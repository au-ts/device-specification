import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register
from reggen.window import Window

from .common import entries, ip, name, new_field_value, reg_value, regs


def oracle_field_value(entry: Register, field: Field):
    if entry.hwext:
        return (
            f"({ip.name}_get_{name(entry)}_{name(field)} st: {field.bits.width()} word)"
        )
    else:
        return f"st.regs.{name(entry)}.{name(field)}"


def oracle_next_field_value(reg: Register, field: Field):
    return f"st'.regs.{name(reg)}.{name(field)}"


def read_case(entry: Register | Window):
    if isinstance(entry, Window):
        # Pass through the offset relative to the start of the whole block, not just
        # this window, since that's closer to how the actual hardware works (except it
        # gets the absolute address, not just the address relative to the block).
        #
        # TODO: is this the right design?
        return rf"""if {hex(entry.offset)} <= offset /\ offset < {hex(entry.offset + entry.size_in_bytes)} then
    INR (SOME (Read ({name(entry)}_read nb offset)), {ip.name}_{name(entry)}_read st nb offset: word32)"""
    else:
        if any(field.hwre for field in entry.fields):
            read_notif = f"SOME (Read {name(entry)}_read)"
        else:
            read_notif = "NONE"
        return f"""if offset = {hex(entry.offset)} then
    INR ({read_notif}, {reg_value(entry, oracle_field_value)}: word32)"""


def write_case(entry: Register | Window):
    prefix = ""
    if isinstance(entry, Window):
        cond = rf"{hex(entry.offset)} <= offset /\ offset < {hex(entry.offset + entry.size_in_bytes)}"
        st_upd = "I"
        write_notif = f"SOME (Write ({name(entry)}_write offset nb wdata))"
    else:
        width = ceil(entry.get_width() / 8)
        cond = rf"offset = {hex(entry.offset)} /\ nb >= {width}"

        writable = any(field.swaccess.allows_write() for field in entry.fields)

        write_notif = "NONE"
        buffered_write_notif = None
        if any(field.hwqe for field in entry.fields):
            # TODO: I don't think this works correctly in the case of ro + hwqe + hwext, but
            # we don't care about that case anyway.
            if entry.hwext:
                write_notif = f"SOME (Write ({name(entry)}_write ({ip.name}_{name(entry)}_decode_write wdata)))"
            else:
                buffered_write_notif = f"SOME {name(entry)}_write"

        if writable and not entry.hwext:
            field_updates = (
                f"{name(field)} := {new_field_value(entry, field, 'wdata', oracle_next_field_value)};"
                for field in entry.fields
                if field.swaccess.allows_write()
            )
            # This gets tacked onto the end of a fresh `i2c_tick`, which always sets
            # `buffered_notif` to NONE, so we shouldn't be overwriting anything here.
            prefix = f"""let
      st_upd = \\st'. st' with <|
        regs := st'.regs with {name(entry)} := st'.regs.{name(entry)} with <|
          {"\n          ".join(field_updates)}
        |>;{"" if buffered_write_notif is None else f"\n      buffered_notif := {buffered_write_notif};"}
      |>
    in
      """
            st_upd = "st_upd"
        else:
            st_upd = "I"

    return rf"""if {cond} then
    {prefix}INR ({st_upd}, {write_notif})"""


read_cases = [read_case(entry) for entry in entries]
write_cases = [write_case(entry) for entry in entries]

# It isn't strictly a failure if we read/write an invalid address, so it'd be
# fine to loosen this to returning all 1s / doing nothing on read / write.
# (Except when devmode_i is set, anyway.)
#
# Undersized writes are always bus errors, though.
read_cases.append("\n    INL FFI_failed")
write_cases.append("\n    INL FFI_failed")


def field_st_upd_assn(reg: Register, field: Field):
    return rf"{name(field)} := if offset = {hex(reg.offset)} then {new_field_value(reg, field, 'wdata', oracle_next_field_value)} else st'.regs.{name(reg)}.{name(field)};"


def reg_st_upd_assn(reg: Register):
    return f"""{name(reg)} := st'.regs.{name(reg)} with <|
        {"\n        ".join(field_st_upd_assn(reg, field) for field in reg.fields if field.swaccess.allows_write())}
      |>;"""


mappings = f"""\
open HolKernel Parse boolLib bossLib;
open BasicProvers;
open alignmentTheory;
open ffiTheory;
open {ip.name}CoreTheory {ip.name}RegsTheory;

val _ = new_theory("{ip.name}Mappings");

Definition {ip.name}_read_def:
  {ip.name}_read (st: {ip.name}_state) (nb: num) (offset: num): ffi_outcome + {ip.name}_hwext_notif option # word32 =
  {"\n  else ".join(read_cases)}
End

Definition {ip.name}_write_def:
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (wdata: word32): ffi_outcome + ({ip.name}_state -> {ip.name}_state) # {ip.name}_hwext_notif option =
  {"\n  else ".join(write_cases)}
End

Theorem {ip.name}_write_st_upd_alt:
  {ip.name}_write st nb offset wdata = INR (st_upd, notif) ==>
  st_upd = \\st'. st' with <|
    regs := st'.regs with <|
        {"\n      ".join(reg_st_upd_assn(reg) for reg in regs if not reg.hwext and any(field.swaccess.allows_write() for field in reg.fields))}
    |>;
    buffered_notif := case offset of
      {"\n    | ".join(f"{hex(reg.offset)} => SOME {name(reg)}_write" for reg in regs if not reg.hwext and any(field.hwqe for field in reg.fields))}
    | _ => st'.buffered_notif;
  |>
Proof
  pure_rewrite_tac [{ip.name}_write_def]
  >> rpt (TOP_CASE_TAC
          >- (fs []
              >> strip_tac
              >> TRY (qpat_x_assum `_ = st_upd` (assume_tac o GSYM))
              >> irule EQ_EXT
              >> simp [{ip.name}_state_component_equality, {ip.name}_regs_component_equality, {", ".join(f"{ip.name}_{name(reg)}_component_equality" for reg in regs if not reg.hwext)}]))
QED

Definition {ip.name}_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  {ip.name}_addrs = {{{"; ".join(f"byte_align {hex(reg.offset)}w" for reg in regs)}}}
End

val _ = export_theory();
"""

with open(sys.argv[2], "w") as f:
    f.write(mappings)
