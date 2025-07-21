import sys

from reggen.register import Register
from reggen.window import Window

from .common import entries, ip, name, regs


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


cases = []
read_cases = []
write_cases = []

for entry in entries:
    if isinstance(entry, Window):
        read_cases.append(f"{name(entry)}_read num num")
    elif entry.hwext and any(field.hwre for field in entry.fields):
        read_cases.append(f"{name(entry)}_read")

    if isinstance(entry, Window):
        write_cases.append(f"{name(entry)}_write num num word32")
    elif entry.hwext and any(field.hwqe for field in entry.fields):
        write_cases.append(f"{name(entry)}_write {ip.name}_{name(entry)}_update")

if len(read_cases) > 0:
    hwext_read_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_read_notif = {" | ".join(read_cases)}
End

"""
    cases.append(f"Read {ip.name}_hwext_read_notif")
else:
    hwext_read_notif_decl = ""

if len(write_cases) > 0:
    hwext_write_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_write_notif = {" | ".join(write_cases)}
End

"""
    cases.append(f"Write {ip.name}_hwext_write_notif")
else:
    hwext_write_notif_decl = ""

if len(cases) > 0:
    hwext_notif_decl = f"""\
Datatype:
  {ip.name}_hwext_notif = {" | ".join(cases)}
End"""
else:
    hwext_notif_decl = "Type {ip.name}_hwext_notif = ``:unit``"


if any(field.hwqe and not reg.hwext for reg in regs for field in reg.fields):
    notif_decl = f"""\
Datatype:
  {ip.name}_notif = {" | ".join(f"{name(reg)}_write" for reg in regs if any(field.hwqe for field in reg.fields) and not reg.hwext)}
End"""
else:
    notif_decl = f"Type {ip.name}_notif = ``:unit``"

output = f"""\
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
    f.write(output)
