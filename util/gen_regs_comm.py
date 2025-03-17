import itertools

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register
from math import ceil

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


def req_error_case(reg: Register):
    min_bytes = ceil(reg.get_width() / 8)
    return rf"{hex(reg.offset)}w => req.write /\ (({min_bytes - 1} >< 0) req.wstrb: {min_bytes} word) <> {(1 << min_bytes) - 1}w"


def req_error():
    return f"""\
Definition {ip.name}_req_error_def:
  {ip.name}_req_error (req: 7 reg_req) <=>
  req.valid /\\ case req.addr of
    {"\n  | ".join(req_error_case(reg) for reg in block.entries)}
  | _ => T
End"""


def field_notif_rel(reg: Register, field: Field):
    return f"(reg2hw.{name(reg)}.{name(field)}_qe <=> notif = SOME {name(reg)}_write)"


def reg_hwext_notif_rels(reg: Register):
    result = []
    if reg.hwqe:
        result += [
            rf"(!value. notif = SOME (Write ({name(reg)}_write value)) <=> req.addr = {hex(reg.offset)}w /\ req.valid /\ req.write /\ {ip.name}_{name(reg)}_decode_write req.wdata = value)"
        ]
    if reg.hwre:
        result += [
            rf"(notif = SOME (Read {name(reg)}_read) <=> req.addr = {hex(reg.offset)}w /\ req.valid /\ ~req.write)"
        ]
    return result


regs_comm = f"""\
open HolKernel Parse boolLib bossLib;
open wordsTheory;
open wordsLib;
open cheshireCircuitTheory i2cRegsTheory;

val _ = new_theory "{ip.name}RegsComm";

{"\n\n".join(reg_reg2hw_def(reg) for reg in block.entries if reg_needs_reg2hw(reg))}

{reg2hw_def()}

{"\n\n".join(reg_hw2reg_def(reg) for reg in block.entries if reg_needs_hw2reg(reg))}

{hw2reg_def()}

Definition {ip.name}_notif_rel_def:
  {ip.name}_notif_rel (notif: {ip.name}_notif option) (reg2hw: {ip.name}_reg2hw) <=>
  {" /\\\n  ".join(field_notif_rel(reg, field) for reg in block.entries for field in reg.fields if field.hwqe and not reg.hwext)}
End

{req_error()}

Definition {ip.name}_hwext_notif_rel_def:
  {ip.name}_hwext_notif_rel (notif: {ip.name}_hwext_notif option) (req: 7 reg_req) <=>
    ~{ip.name}_req_error req /\\
    {" /\\\n    ".join(term for reg in block.entries for term in reg_hwext_notif_rels(reg) if reg.hwext)}
End

val _ = export_theory ();
"""


print(regs_comm, end="")
