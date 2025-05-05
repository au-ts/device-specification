from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register

from .common import block, ip, name, new_field_value, reg_value


def oracle_field_value(reg: Register, field: Field):
    if reg.hwext:
        return (
            f"({ip.name}_get_{name(reg)}_{name(field)} st: {field.bits.width()} word)"
        )
    else:
        return f"st.regs.{name(reg)}.{name(field)}"


def oracle_next_field_value(reg: Register, field: Field):
    return f"st'.regs.{name(reg)}.{name(field)}"


def reg_read_case(reg: Register):
    if any(field.hwre for field in reg.fields):
        read_notif = f"SOME (Read {name(reg)}_read)"
    else:
        read_notif = "NONE"
    return f"{hex(reg.offset)} => INR ({read_notif}, {reg_value(reg, oracle_field_value)} : word32)"


def reg_write_case(reg: Register):
    writable = any(field.swaccess.allows_write() for field in reg.fields)

    write_notif = "NONE"
    buffered_write_notif = None
    if any(field.hwqe for field in reg.fields):
        # TODO: I don't think this works correctly in the case of ro + hwqe + hwext, but
        # we don't care about that case anyway.
        if reg.hwext:
            write_notif = f"SOME (Write ({name(reg)}_write ({ip.name}_{name(reg)}_decode_write wdata)))"
        else:
            buffered_write_notif = f"SOME {name(reg)}_write"

    if writable and not reg.hwext:
        field_updates = (
            f"{name(field)} := {new_field_value(reg, field, 'wdata', oracle_next_field_value)};"
            for field in reg.fields
            if field.swaccess.allows_write()
        )
        # This gets tacked onto the end of a fresh `i2c_tick`, which always sets
        # `buffered_notif` to NONE, so we shouldn't be overwriting anything here.
        new_state = f"""st' with <|
          regs := st'.regs with {name(reg)} := st'.regs.{name(reg)} with <|
            {"\n            ".join(field_updates)}
          |>;{"" if buffered_write_notif is None else f"\n          buffered_notif := {buffered_write_notif};"}
        |>"""
    else:
        new_state = "st'"
    width = ceil(reg.get_width() / 8)

    return f"""{hex(reg.offset)} =>
      let
        st_upd = \\st'. {new_state};
      in
        if nb >= {width} then INR (st_upd, {write_notif}) else INL FFI_failed"""


read_cases = [reg_read_case(reg) for reg in block.entries]
write_cases = [reg_write_case(reg) for reg in block.entries]

# It isn't strictly a failure if we read/write an invalid address, so it'd be
# fine to loosen this to returning all 1s / doing nothing on read / write.
# (Except when devmode_i is set, anyway.)
#
# Undersized writes are always bus errors, though.
read_cases.append("_ => INL FFI_failed")
write_cases.append("_ => INL FFI_failed")


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
  {ip.name}_read (st: {ip.name}_state) (nb: num) (offset: num) = case offset of
    {"\n  | ".join(read_cases)}
End

Definition {ip.name}_write_def:
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (wdata: word32) = case offset of
    {"\n  | ".join(write_cases)}
End

Theorem {ip.name}_write_st_upd_alt:
  {ip.name}_write st nb offset wdata = INR (st_upd, notif) ==>
  st_upd = \\st'. st' with <|
    regs := st'.regs with <|
        {"\n      ".join(reg_st_upd_assn(reg) for reg in block.entries if not reg.hwext and any(field.swaccess.allows_write() for field in reg.fields))}
    |>;
    buffered_notif := case offset of
      {"\n    | ".join(f"{hex(reg.offset)} => SOME {name(reg)}_write" for reg in block.entries if not reg.hwext and any(field.hwqe for field in reg.fields))}
    | _ => st'.buffered_notif;
  |>
Proof
  pure_rewrite_tac [{ip.name}_write_def]
  >> rpt (TOP_CASE_TAC
          >- (simp []
              >> strip_tac
              >> irule EQ_EXT
              >> simp [{ip.name}_state_component_equality, {ip.name}_regs_component_equality, {", ".join(f"{ip.name}_{name(reg)}_component_equality" for reg in block.entries if not reg.hwext)}]))
QED

Definition {ip.name}_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  {ip.name}_addrs = {{{"; ".join(f"byte_align {hex(reg.offset)}w" for reg in block.entries)}}}
End

val _ = export_theory();
"""

print(mappings, end="")
