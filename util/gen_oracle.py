import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.ip_block import IpBlock
from reggen.register import Register

ip = IpBlock.from_path(sys.argv[1], [])
# Currently we assume that registers are always 32-bit, so that we can store the
# values being written/read in 32-bit integers.
assert ip.regwidth == 32

# Assume there's only 1 block for now.
(block,) = ip.reg_blocks.values()

read_cases = []
write_cases = []
reg_records = []
reg_decls = []
read_notif_regs = []
write_notif_regs = []
hwext_write_notifs = []

for i, reg in enumerate(block.entries):
    # Assume we don't have to deal with any `MultiReg`s or `Window`s for now.
    assert isinstance(reg, Register)

    reg_name = reg.name.lower()

    field_updates = []
    field_terms = []
    field_decls = []
    for field in reg.fields:
        assert field.swaccess.key in ["ro", "rw", "wo", "rw1c"]

        field_name = field.name.lower()

        get_fn = f"{ip.name}_get_{reg_name}_{field_name}"
        if field.swaccess.allows_read():
            if reg.hwext:
                field_value = f"({get_fn} st: {field.bits.width()} word)"
            else:
                field_value = f"st.regs.{reg_name}.{field_name}"
            field_terms.append(f"(w2w {field_value} << {field.bits.lsb})")

        if field.swaccess.allows_write():
            value = f"w2w (({field.bits.msb} -- {field.bits.lsb}) value)"
            match field.swaccess.key:
                case "rw" | "wo":
                    pass
                case "rw1c":
                    # TODO: not sure whether this makes sense to do in the case of hwext, since the
                    # circuit still just gets the raw value anyway.
                    value = f"{field_value} && ~({value})"
                case other:
                    raise Exception(f"Unreachable: {other}")
            field_updates.append(f"{field_name} := {value};")

        field_decls.append(f"{field_name} : {field.bits.width()} word;")

    write_lets = []
    if len(field_updates) > 0 and (
        not reg.hwext or any(field.hwqe for field in reg.fields)
    ):
        write_lets.append(f"""new_value = <|
          {"\n          ".join(field_updates)}
        |>;""")

    write_notif = "NONE"
    buffered_write_notif = "NONE"
    if any(field.hwqe for field in reg.fields):
        # TODO: I don't think this works correctly in the case of ro + hwqe + hwext, but
        # we don't care about that case anyway.
        if reg.hwext:
            hwext_write_notifs.append(f"{reg_name}_write {reg_name}_fields")
            write_notif = f"SOME (Write ({reg_name}_write new_value))"
        else:
            write_notif_regs.append(reg_name)
            buffered_write_notif = f"SOME {reg_name}_write"

    if len(field_updates) > 0 and not reg.hwext:
        # This gets tacked onto the end of a fresh `i2c_tick`, which always sets
        # `buffered_notif` to NONE, so we shouldn't be overwriting anything here.
        new_state = f"""st' with <|
          regs := st'.regs with {reg_name} := new_value;
          buffered_notif := {buffered_write_notif};
        |>"""
    else:
        new_state = "st'"
    write_lets.append(f"st_upd = \\st'. {new_state};")
    width = ceil(reg.get_width() / 8)
    write_cases.append(
        f"""{hex(reg.offset)} =>
      let
        {"\n        ".join(write_lets)}
      in
        if nb >= {width} then INR (st_upd, {write_notif}) else INL FFI_failed"""
    )

    if any(field.hwre for field in reg.fields):
        read_notif_regs.append(reg_name)
        read_notif = f"SOME (Read {reg_name}_read)"
    else:
        read_notif = "NONE"

    if len(field_terms) == 0:
        field_terms.append("0w")
    read_cases.append(
        f"{hex(reg.offset)} => INR ({read_notif}, {' || '.join(field_terms)} : word32)"
    )

    # We still need this for hwext + hwqe values as the type of the new value to be
    # included in the notification.
    if not reg.hwext or any(field.hwqe for field in reg.fields):
        reg_records.append(f"""\
Datatype:
  {reg_name}_fields = <|
    {"\n    ".join(field_decls)}
  |>
End""")

    if not reg.hwext:
        reg_decls.append(f"{reg_name} : {reg_name}_fields;")

# It isn't strictly a failure if we read/write an invalid address, so it'd be
# fine to loosen this to returning all 1s / doing nothing on read / write.
# (Except when devmode_i is set, anyway.)
#
# Undersized writes are always bus errors, though.
read_cases.append("_ => INL FFI_failed")
write_cases.append("_ => INL FFI_failed")

regs = f"""\
open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory("{ip.name}Regs");

{"\n\n".join(reg_records)}

Datatype:
  {ip.name}_regs = <|
    {"\n    ".join(reg_decls)}
  |>
End

Datatype:
  {ip.name}_hwext_read_notif = {" | ".join(f"{reg}_read" for reg in read_notif_regs)}
End

Datatype:
  {ip.name}_hwext_write_notif = {" | ".join(hwext_write_notifs)}
End

Datatype:
  {ip.name}_hwext_notif = Read {ip.name}_hwext_read_notif | Write {ip.name}_hwext_write_notif
End

Datatype:
  {ip.name}_notif = {" | ".join(f"{reg}_write" for reg in write_notif_regs)}
End

val _ = export_theory();
"""

oracle = f"""\
open HolKernel Parse boolLib bossLib;
open alignmentTheory;
open ffiTheory;
open {ip.name}CoreTheory;

val _ = new_theory("{ip.name}Mappings");

Definition {ip.name}_read_def:
  {ip.name}_read (st: {ip.name}_state) (nb: num) (offset: num) = case offset of
    {"\n  | ".join(read_cases)}
End

Definition {ip.name}_write_def:
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (value: word32) = case offset of
    {"\n  | ".join(write_cases)}
End

Definition {ip.name}_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  {ip.name}_addrs = {{{"; ".join(f"byte_align {hex(reg.offset)}w" for reg in block.entries)}}}
End

val _ = export_theory();
"""

with open(sys.argv[2], "w") as f:
    f.write(regs)

with open(sys.argv[3], "w") as f:
    f.write(oracle)
