from reggen.register import Register

from .common import block, ip, name


def reg_record(reg: Register):
    return f"""\
Datatype:
  {ip.name}_{name(reg)}_fields = <|
    {"\n    ".join(f"{name(field)}: {field.bits.width()} word;" for field in reg.fields)}
  |>
End"""


def regs_record():
    return f"""\
Datatype:
  {ip.name}_regs = <|
    {"\n    ".join(f"{name(reg)}: {ip.name}_{name(reg)}_fields;" for reg in block.entries if not reg.hwext)}
  |>
End"""


# We still need this for hwext + hwqe values as the type of the new value to be
# included in the notification.
reg_records = (
    reg_record(reg)
    for reg in block.entries
    if not reg.hwext or any(field.hwqe for field in reg.fields)
)

regs = f"""\
open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory("{ip.name}Regs");

{"\n\n".join(reg_records)}

{regs_record()}

Datatype:
  {ip.name}_hwext_read_notif = {" | ".join(f"{(name(reg))}_read" for reg in block.entries if any(field.hwre for field in reg.fields))}
End

Datatype:
  {ip.name}_hwext_write_notif = {" | ".join(f"{(name(reg))}_write {ip.name}_{name(reg)}_fields" for reg in block.entries if any(field.hwqe for field in reg.fields) and reg.hwext)}
End

Datatype:
  {ip.name}_hwext_notif = Read {ip.name}_hwext_read_notif | Write {ip.name}_hwext_write_notif
End

Datatype:
  {ip.name}_notif = {" | ".join(f"{name(reg)}_write" for reg in block.entries if any(field.hwqe for field in reg.fields) and not reg.hwext)}
End

val _ = export_theory();
"""

print(regs, end="")
