import itertools

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.register import Register
from reggen.field import Field

from .common import block, ip, name


def field_reg2hw_fields(field: Field):
    fields = []
    if field.hwaccess.allows_read():
        fields.append(f"{name(field)}_q: {field.bits.width()} word;")
    if field.hwqe:
        fields.append(f"{name(field)}_qe: bool;")
    if field.hwre:
        fields.append(f"{name(field)}_re: bool;")
    return fields


def field_needs_reg2hw(field: Field):
    return field.hwaccess.allows_read() or field.hwqe or field.hwre


def field_hw2reg_fields(reg: Register, field: Field):
    fields = [f"{name(field)}_d: {field.bits.width()} word;"]
    if not reg.hwext:
        fields.append(f"{name(field)}_de: bool;")
    return fields


def field_needs_hw2reg(field: Field):
    return field.hwaccess.allows_write()


def reg_reg2hw_def(reg: Register):
    decls = itertools.chain.from_iterable(
        field_reg2hw_fields(field) for field in reg.fields if field_needs_reg2hw(field)
    )
    return f"""\
Datatype:
  {ip.name}_reg2hw_{name(reg)} = <|
    {"\n    ".join(decls)}
  |>
End"""


def reg_needs_reg2hw(reg: Register):
    return any(field_needs_reg2hw(field) for field in reg.fields)


def reg_hw2reg_def(reg: Register):
    decls = itertools.chain.from_iterable(
        field_hw2reg_fields(reg, field)
        for field in reg.fields
        if field_needs_hw2reg(field)
    )
    return f"""\
Datatype:
  {ip.name}_hw2reg_{name(reg)} = <|
    {"\n    ".join(decls)}
  |>
End"""


def reg_needs_hw2reg(reg: Register):
    return any(field_needs_hw2reg(field) for field in reg.fields)


def reg2hw_def():
    decls = (
        f"{name(reg)}: {ip.name}_reg2hw_{name(reg)};"
        for reg in block.entries
        if reg_needs_reg2hw(reg)
    )
    return f"""\
Datatype:
  {ip.name}_reg2hw = <|
    {"\n    ".join(decls)}
  |>
End"""


def hw2reg_def():
    decls = (
        f"{name(reg)}: {ip.name}_hw2reg_{name(reg)};"
        for reg in block.entries
        if reg_needs_hw2reg(reg)
    )
    return f"""\
Datatype:
  {ip.name}_hw2reg = <|
    {"\n    ".join(decls)}
  |>
End"""


regs_comm = f"""\
open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory "{ip.name}RegsComm";

{"\n\n".join(reg_reg2hw_def(reg) for reg in block.entries if reg_needs_reg2hw(reg))}

{reg2hw_def()}

{"\n\n".join(reg_hw2reg_def(reg) for reg in block.entries if reg_needs_hw2reg(reg))}

{hw2reg_def()}

val _ = export_theory ();
"""


print(regs_comm, end="")
