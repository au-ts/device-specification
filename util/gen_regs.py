import sys

from reggen.register import Register

from .common import ip, name, regs


def reg_record(reg: Register):
    return f"""\
Datatype:
  {ip.name}_{name(reg)} = <|
    {"\n    ".join(f"{name(field)}: {field.bits.width()} word;" for field in reg.fields)}
  |>
End"""


def reg_update_record(reg: Register):
    decls = (
        f"{name(field)}: {field.bits.width()} word;"
        for field in reg.fields
        if field.swaccess.allows_write()
    )
    return f"""\
Datatype:
  {ip.name}_{name(reg)}_update = <|
    {"\n    ".join(decls)}
  |>
End"""


def regs_record():
    return f"""\
Datatype:
  {ip.name}_regs = <|
    {"\n    ".join(f"{name(reg)}: {ip.name}_{name(reg)};" for reg in regs if not reg.hwext)}
  |>
End"""


def reg_decode_write(reg: Register):
    updates = (
        f"{name(field)} := ({field.bits.msb} >< {field.bits.lsb}) value;"
        for field in reg.fields
        if field.swaccess.allows_write()
    )
    return f"""\
Definition {ip.name}_{name(reg)}_decode_write_def:
  {ip.name}_{name(reg)}_decode_write (value: word32): {ip.name}_{name(reg)}_update =
  <|
    {"\n    ".join(updates)}
  |>
End"""


if any(
    reg.hwext and (field.hwqe or field.hwre) for reg in regs for field in reg.fields
):
    cases = []
    if any(reg.hwext and field.hwre for reg in regs for field in reg.fields):
        hwext_read_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_read_notif = {" | ".join(f"{(name(reg))}_read" for reg in regs if any(field.hwre for field in reg.fields))}
End

"""
        cases.append(f"Read {ip.name}_hwext_read_notif")
    else:
        hwext_read_notif_decl = ""

    if any(reg.hwext and field.hwqe for reg in regs for field in reg.fields):
        hwext_write_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_write_notif = {" | ".join(f"{(name(reg))}_write {ip.name}_{name(reg)}_update" for reg in regs if any(field.hwqe for field in reg.fields) and reg.hwext)}
End

"""
        cases.append(f"Write {ip.name}_hwext_write_notif")
    else:
        hwext_write_notif_decl = ""

    hwext_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_notif = {" | ".join(cases)}
End"""
else:
    hwext_read_notif_decl = ""
    hwext_write_notif_decl = ""
    hwext_notif_decl = "Type {ip.name}_hwext_notif = ``:unit``"


if any(field.hwqe and not reg.hwext for reg in regs for field in reg.fields):
    notif_decl = f"""\
Datatype:
  {ip.name}_notif = {" | ".join(f"{name(reg)}_write" for reg in regs if any(field.hwqe for field in reg.fields) and not reg.hwext)}
End"""
else:
    notif_decl = f"Type {ip.name}_notif = ``:unit``"

regs = f"""\
open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory("{ip.name}Regs");

(* The fields of all the registers which need to be stored. *)
{"\n\n".join(reg_record(reg) for reg in regs if not reg.hwext)}

{regs_record()}

(* The fields of each register which can be updated on a write. *)
{"\n\n".join(reg_update_record(reg) for reg in regs if any(field.swaccess.allows_write() for field in reg.fields))}

(* Functions which decode all of a register's writable fields from a write request. *)
{"\n\n".join(reg_decode_write(reg) for reg in regs if any(field.swaccess.allows_write() for field in reg.fields))}

{hwext_read_notif_decl}{hwext_write_notif_decl}{hwext_notif_decl}

{notif_decl}

val _ = export_theory();
"""

with open(sys.argv[2], "w") as f:
    f.write(regs)
