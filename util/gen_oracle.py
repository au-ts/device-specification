import itertools
import sys
from math import ceil
from typing import Callable

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.ip_block import IpBlock
from reggen.register import Register
from reggen.field import Field

ip = IpBlock.from_path(sys.argv[1], [])
# Currently we assume that registers are always 32-bit, so that we can store the
# values being written/read in 32-bit integers.
assert ip.regwidth == 32

# Assume there's only 1 block for now.
(block,) = ip.reg_blocks.values()

# TODO: use bool for single-bit registers instead of word1


def name(x):
    return x.name.lower()


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


def reg_value(reg: Register, field_value: Callable[[Register, Field], str]):
    field_terms = [
        f"(w2w {field_value(reg, field)} << {field.bits.lsb})"
        for field in reg.fields
        if field.swaccess.allows_read()
    ]
    if len(field_terms) == 0:
        field_terms.append("0w")
    return " || ".join(field_terms)


def new_field_value(
    reg: Register, field: Field, field_value: Callable[[Register, Field], str]
):
    value = f"({field.bits.msb} >< {field.bits.lsb}) wdata"
    match field.swaccess.key:
        case "rw" | "wo":
            pass
        case "rw1c":
            if not reg.hwext:
                value = f"{field_value(reg, field)} && ~({value})"
        case other:
            raise Exception(f"Unsupported or non-writable swaccess: {other}")
    return value


def oracle_field_value(reg: Register, field: Field):
    if reg.hwext:
        return (
            f"({ip.name}_get_{name(reg)}_{name(field)} st: {field.bits.width()} word)"
        )
    else:
        return f"st.regs.{name(reg)}.{name(field)}"


def hw_field_value(reg: Register, field: Field):
    if reg.hwext:
        return f"s'.hw2reg.{name(reg)}.{name(field)}_d"
    else:
        return f"s.regs.{name(reg)}.{name(field)}"


def rw1c_field_value(reg: Register, field: Field):
    if field.hwaccess.allows_write():
        return f"(if s'.hw2reg.{name(reg)}.{name(field)}_de then s'.hw2reg.{name(reg)}.{name(field)}_d else s.regs.{name(reg)}.{name(field)})"
    else:
        return f"s.regs.{name(reg)}.{name(field)}"


def new_reg_value(reg: Register, field_value: Callable[[Register, Field], str]):
    field_updates = [
        f"{name(field)} := {new_field_value(reg, field, field_value)};"
        for field in reg.fields
        if field.swaccess.allows_write()
    ]
    return f"""<|
          {"\n          ".join(field_updates)}
        |>"""


read_cases = []
write_cases = []
reg_records = []
reg_decls = []
read_notif_regs = []
write_notif_regs = []
hwext_write_notifs = []

for reg in block.entries:
    # Assume we don't have to deal with any `MultiReg`s or `Window`s for now.
    assert isinstance(reg, Register)

    field_decls = [
        f"{name(field)} : {field.bits.width()} word;" for field in reg.fields
    ]
    writable = any(field.swaccess.allows_write() for field in reg.fields)

    write_lets = []
    if writable and (not reg.hwext or any(field.hwqe for field in reg.fields)):
        write_lets.append(f"""new_value = {new_reg_value(reg, oracle_field_value)};""")

    write_notif = "NONE"
    buffered_write_notif = "NONE"
    if any(field.hwqe for field in reg.fields):
        # TODO: I don't think this works correctly in the case of ro + hwqe + hwext, but
        # we don't care about that case anyway.
        if reg.hwext:
            hwext_write_notifs.append(f"{name(reg)}_write {ip.name}_{name(reg)}_fields")
            write_notif = f"SOME (Write ({name(reg)}_write new_value))"
        else:
            write_notif_regs.append(name(reg))
            buffered_write_notif = f"SOME {name(reg)}_write"

    if writable and not reg.hwext:
        # This gets tacked onto the end of a fresh `i2c_tick`, which always sets
        # `buffered_notif` to NONE, so we shouldn't be overwriting anything here.
        new_state = f"""st' with <|
          regs := st'.regs with {name(reg)} := new_value;
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
        read_notif_regs.append(name(reg))
        read_notif = f"SOME (Read {name(reg)}_read)"
    else:
        read_notif = "NONE"

    read_cases.append(
        f"{hex(reg.offset)} => INR ({read_notif}, {reg_value(reg, oracle_field_value)} : word32)"
    )

    # We still need this for hwext + hwqe values as the type of the new value to be
    # included in the notification.
    if not reg.hwext or any(field.hwqe for field in reg.fields):
        reg_records.append(f"""\
Datatype:
  {ip.name}_{name(reg)}_fields = <|
    {"\n    ".join(field_decls)}
  |>
End""")

    if not reg.hwext:
        reg_decls.append(f"{name(reg)} : {ip.name}_{name(reg)}_fields;")

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
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (wdata: word32) = case offset of
    {"\n  | ".join(write_cases)}
End

Definition {ip.name}_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  {ip.name}_addrs = {{{"; ".join(f"byte_align {hex(reg.offset)}w" for reg in block.entries)}}}
End

val _ = export_theory();
"""

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


def reg_top_field_hwext_qe_re_assns(reg: Register, field: Field):
    assns = []
    if field.hwqe:
        # word_bit 1 s'.reg_rsp_o is reg_rsp_o.error.
        assns.append(
            rf"{name(field)}_qe := (addr = {hex(reg.offset)}w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));"
        )
    if field.hwre:
        assns.append(
            rf"{name(field)}_re := (addr = {hex(reg.offset)}w /\ valid /\ ~write /\ ~(word_bit 1 s'.reg_rsp_o));"
        )
    return "\n        ".join(assns)


def reg_top_reg_hwext_qe_re_assn(reg: Register):
    return f"""{name(reg)} := s'.reg2hw.{name(reg)} with <|
        {"\n        ".join(reg_top_field_hwext_qe_re_assns(reg, field) for field in reg.fields)}
      |>;"""


def reg_top_field_hwext_q_assn(reg: Register, field: Field):
    return f"""{name(field)}_q := s'.hw2reg.{name(reg)}.{name(field)}_d;"""


def reg_top_reg_hwext_q_assn(reg: Register):
    return f"""{name(reg)} := s'.reg2hw.{name(reg)} with <|
        {"\n        ".join(reg_top_field_hwext_q_assn(reg, field) for field in reg.fields)}
      |>;"""


def reg_top_field_q_assn(reg: Register, field: Field):
    return f"""{name(field)}_q := s'.regs.{name(reg)}.{name(field)};"""


def reg_top_reg_q_assn(reg: Register):
    # TODO: I think we need to split this up into one `s' = ...` per field if we
    # want the translator to accept it.
    return f"""{name(reg)} := s'.reg2hw.{name(reg)} with <|
        {"\n        ".join(reg_top_field_q_assn(reg, field) for field in reg.fields)}
      |>;"""


def reg_top_field_qe_assn(reg: Register, field: Field):
    return rf"""{name(field)}_qe := (addr = {hex(reg.offset)}w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));"""


def reg_top_reg_qe_assn(reg: Register):
    return rf"""{name(reg)} := s'.reg2hw.{name(reg)} with <|
        {"\n        ".join(reg_top_field_qe_assn(reg, field) for field in reg.fields)}
      |>;"""


def reg_top_field_assn(reg: Register, field: Field):
    if field.hwaccess.allows_write():
        hw_if = f""" if s'.hw2reg.{name(reg)}.{name(field)}_de then
      s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := s'.hw2reg.{name(reg)}.{name(field)}_d
    else
      s'"""
    else:
        hw_if = "\n      s'"

    if field.swaccess.allows_write():
        # field_value is only used in the case of rw1c, so we don't have to worry about
        # rw1c_field_value not making sense in the other cases.
        return rf"""s' = if addr = {hex(reg.offset)}w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := {new_field_value(reg, field, rw1c_field_value)}
    else{hw_if};"""
    else:
        return f"s' ={hw_if};"


def reg_top_error_case(reg: Register):
    min_bytes = ceil(reg.get_width() / 8)
    return rf"{hex(reg.offset)}w => s' with reg_rsp_o := (1 :+ valid /\ write /\ (({min_bytes - 1} >< 0) wstrb: {min_bytes} word) <> {(1 << min_bytes) - 1}w) s'.reg_rsp_o"


def reg_init(reg: Register):
    # We leave add_x_inits to deal with fields that have `resval = None` (meaning `'x`).
    return f"""<|
      {"\n      ".join(f"{name(field)} := {field.resval}w;" for field in reg.fields if field.resval is not None)}
    |>"""


def reg2hw_reg_init(reg: Register):
    return f"""<|
      {"\n      ".join(f"{name(field)}_qe := F;" for field in reg.fields if field.hwqe)}
    |>"""


comms = [
    f'"regs_{name(reg)}_{name(field)}"'
    for reg in block.entries
    for field in reg.fields
    if not reg.hwext
] + [
    f'"reg2hw_{name(reg)}_{name(field)}_qe"'
    for reg in block.entries
    for field in reg.fields
    if field.hwqe and not reg.hwext
]

regs_circuit_lib = f"""
structure {ip.name}RegsCircuitLib =
struct

open wordsLib;
open {ip.name}CircuitStateTheory {ip.name}RegsTheory {ip.name}RegsCommTheory;

(* The translator will only look for processes in the same theory as the
 * top-level `mk_module`, so we just export the bodies of these functions and
 * let `i2cCircuitTheory` make the actual definitions. *)
val {ip.name}_reg_top_comb_1_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;
    write = word_bit 37 fext.reg_req_i;
    wstrb = (4 >< 1) fext.reg_req_i: word4;
    valid = word_bit 0 fext.reg_req_i;

    s' = case addr of
      {"\n    | ".join(reg_top_error_case(reg) for reg in block.entries)}
    | _ => s' with reg_rsp_o := (1 :+ valid) s'.reg_rsp_o;
    s' = s' with reg_rsp_o := (0 :+ T) s'.reg_rsp_o;
  in
    s' with reg2hw := s'.reg2hw with <|
      {"\n      ".join(reg_top_reg_q_assn(reg) for reg in block.entries if not reg.hwext and reg.hwaccess.allows_read())}
      {"\n      ".join(reg_top_reg_hwext_qe_re_assn(reg) for reg in block.entries if reg.hwext and (reg.hwqe or reg.hwre))}
    |>
``

(* TODO: if we ever run into a situation where the `q` signal of a hwext
 * register is being read from by i2c_core, we'll need to add another one of
 * these that runs in between `d` being set and `q` being read. But there
 * doesn't seem to be anything like that right now, and I don't see why there
 * would be. *)
val {ip.name}_reg_top_comb_2_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;

    s' = case addr of
      (* TODO: this won't produce the prettiest Verilog. To do that, we'd need to turn
       * this into a let..in with an assignment for each field of the register, but
       * that would make sharing code with the HOL version more annoying.
       *
       * Alternatively, using @@ would be a lot less ugly than this. *)
      {"\n    | ".join(f"{hex(reg.offset)}w => s' with reg_rsp_o := bit_field_insert 33 2 ({reg_value(reg, hw_field_value)}: word32) s'.reg_rsp_o" for reg in block.entries)}
    | _ => s' with reg_rsp_o := bit_field_insert 33 2 (0xffffffffw: word32) s'.reg_rsp_o
  in
    s' with reg2hw := s'.reg2hw with <|
      {"\n      ".join(reg_top_reg_hwext_q_assn(reg) for reg in block.entries if reg.hwext and reg.hwaccess.allows_read() and reg.hwaccess.allows_write())}
    |>
``

val {ip.name}_reg_top_ff_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;
    write = word_bit 37 fext.reg_req_i;
    wdata = (36 >< 5) fext.reg_req_i: word32;
    valid = word_bit 0 fext.reg_req_i;

    {"\n    ".join(reg_top_field_assn(reg, field) for reg in block.entries for field in reg.fields if not reg.hwext and (field.swaccess.allows_write() or field.hwaccess.allows_write()))}
  in
    s' with reg2hw := s'.reg2hw with <|
      {"\n      ".join(reg_top_reg_qe_assn(reg) for reg in block.entries if not reg.hwext and reg.hwqe)}
    |>
``

val {ip.name}_regs_init_tm = ``
  (<|
    {"\n    ".join(f"{name(reg)} := {reg_init(reg)};" for reg in block.entries if not reg.hwext and any(field.resval is not None for field in reg.fields))}
  |>): i2c_regs
``;

val {ip.name}_reg2hw_init_tm = ``
  (<|
    {"\n    ".join(f"{name(reg)} := {reg2hw_reg_init(reg)};" for reg in block.entries if not reg.hwext and reg.hwqe)}
  |>): i2c_reg2hw
``;

val {ip.name}_reg_comms = [{", ".join(comms)}];

end
"""

with open(sys.argv[2], "w") as f:
    f.write(regs)

with open(sys.argv[3], "w") as f:
    f.write(oracle)

with open(sys.argv[4], "w") as f:
    f.write(regs_comm)

with open(sys.argv[5], "w") as f:
    f.write(regs_circuit_lib)
