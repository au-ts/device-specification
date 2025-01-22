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
                field_value = f"({get_fn} st)"
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
            if not reg.hwext:
                field_updates.append(f"{field_name} := {value};")

        if not reg.hwext:
            field_decls.append(f"{field_name} : {field.bits.width()} word;")

    write_lets = []
    if len(field_updates) != 0:
        # Note: this tacks the write onto the end of the last clock edge.
        write_lets.append(
            f"""st = st with regs := st.regs with {reg_name} := st.regs.{reg_name} with <|
              {"\n              ".join(field_updates)}
            |>;"""
        )
    if any(field.hwqe for field in reg.fields):
        # The hardware doesn't get notified that a register's been written until the
        # cycle after it's already occured, so giving it the state where that's already
        # happened makes sense.
        #
        # That also means that we don't have to pass in the new value, because it's
        # already available in `st`.
        #
        # TODO: return the side effects instead of applying them here, and then pass
        # them to `i2c_tick` to be applied. This is necessary so that we can pass the
        # appropriate register values through to `i2c_core` when verifying the hardware,
        # rather than having them potentially get overwritten here by the side effects.
        #
        # This is also currently wrong because we need to apply the rest of the clock
        # cycle along with these side effects.
        write_lets.append(f"st = {ip.name}_{reg_name}_written st;")

    width = ceil(reg.get_width() / 8)
    if len(write_lets) > 0:
        let = f"""
          let
            {"\n            ".join(write_lets)}
          in
            """
    else:
        let = " "
    write_cases.append(
        f"""{hex(reg.offset)} =>{let}if nb >= {width} then INR st else INL FFI_failed"""
    )

    if any(field.hwre for field in reg.fields):
        new_state = f"{ip.name}_{reg_name}_read st"
    else:
        # If the hardware doesn't have a `re` signal, there's no way for it to tell
        # whether a register's been read, and thus reading can't have any side effects.
        new_state = "st"
    if len(field_terms) == 0:
        field_terms.append("0w")
    read_cases.append(
        f"{hex(reg.offset)} => INR ({new_state}, {' || '.join(field_terms)} : word32)"
    )

    if not reg.hwext:
        reg_records.append(f"""\
Datatype:
  {reg_name}_fields = <|
    {"\n    ".join(field_decls)}
  |>
End""")

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

val _ = export_theory();
"""

oracle = f"""\
open HolKernel Parse boolLib bossLib;
open ffiTheory;
open {ip.name}CoreTheory;

val _ = new_theory("{ip.name}Mappings");

Definition {ip.name}_read_def:
  {ip.name}_read (st: {ip.name}_state) (nb: num) (offset: num) =
    let
      st = apply_fbits st
    in
      case offset of
        {"\n      | ".join(read_cases)}
End

Definition {ip.name}_write_def:
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (value: word32) =
    let
      st = apply_fbits st
    in
      case offset of
        {"\n      | ".join(write_cases)}
End

val _ = export_theory();
"""

with open(sys.argv[2], "w") as f:
    f.write(regs)

with open(sys.argv[3], "w") as f:
    f.write(oracle)
