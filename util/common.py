import sys
from typing import Callable

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.ip_block import IpBlock
from reggen.multi_register import MultiRegister
from reggen.register import Register
from reggen.window import Window

ip = IpBlock.from_path(sys.argv[1], [])
# Currently we assume that registers are always 32-bit, so that we can store the
# values being written/read in 32-bit integers.
assert ip.regwidth == 32

# Assume there's only 1 block for now.
(block,) = ip.reg_blocks.values()
addr_width = block.get_addr_width()
entries: list[Register | Window] = []
for entry in block.entries:
    if isinstance(entry, Register):
        entries.append(entry)
    elif isinstance(entry, MultiRegister):
        entries.extend(entry.regs)
    elif isinstance(entry, Window):
        entries.append(entry)
    else:
        raise NotImplementedError("unsupported entry in memory map")
regs = block.flat_regs
windows = block.windows

# TODO: use bool for single-bit registers instead of word1

# TODO: for all the builtin targets, reggen uses a proper templating system,
# maybe we should do that instead?


def name(x: Register | Field | Window):
    return x.name.lower()


def reg_value(reg: Register, field_value: Callable[[Register, Field], str]):
    field_terms = [
        f"(w2w {field_value(reg, field)} <<~ {field.bits.lsb}w)"
        for field in reg.fields
        if field.swaccess.allows_read()
    ]
    if len(field_terms) == 0:
        field_terms.append("0w")
    return " || ".join(field_terms)


def new_field_value(
    reg: Register,
    field: Field,
    wdata: str,
    field_value: Callable[[Register, Field], str],
):
    value = f"({field.bits.msb} >< {field.bits.lsb}) {wdata}"
    match field.swaccess.key:
        case "rw" | "wo":
            pass
        case "rw1c":
            if not reg.hwext:
                # Note: this is only correct because if the swaccess is rw1c, the field has to
                # be readable.
                value = f"{field_value(reg, field)} && ~({value})"
        case other:
            raise Exception(f"Unsupported or non-writable swaccess: {other}")
    return value
