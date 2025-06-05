import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register

from .common import block, ip, name, new_field_value, reg_value


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


def reg_top_field_hwext_qe_re_assns(reg: Register, field: Field):
    # TODO: this is probably wrong for ro fields with hwqe/hwre set.
    assns = []
    if field.hwqe:
        # word_bit 1 s'.reg_rsp_o is reg_rsp_o.error.
        assns.append(
            rf"{name(field)}_qe := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));"
        )
    if field.hwre:
        assns.append(
            rf"{name(field)}_re := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ ~s'.write /\ ~(word_bit 1 s'.reg_rsp_o));"
        )
    return assns


def reg_top_reg_hwext_qe_re_assns(reg: Register):
    return (
        f"{name(reg)} := s'.reg2hw.{name(reg)} with {assn}"
        for field in reg.fields
        for assn in reg_top_field_hwext_qe_re_assns(reg, field)
    )


def reg_top_field_hwext_q_assn(field: Field):
    if field.swaccess.allows_write():
        return (
            f"""{name(field)}_q := ({field.bits.msb} >< {field.bits.lsb}) s'.wdata;"""
        )
    else:
        return f"""{name(field)}_q := 0w;"""


def reg_top_reg_hwext_q_assns(reg: Register):
    return (
        f"{name(reg)} := s'.reg2hw.{name(reg)} with {reg_top_field_hwext_q_assn(field)}"
        for field in reg.fields
    )


def reg_top_field_q_assn(reg: Register, field: Field):
    return f"""{name(field)}_q := s.regs.{name(reg)}.{name(field)};"""


def reg_top_reg_q_assns(reg: Register):
    return (
        f"{name(reg)} := s'.reg2hw.{name(reg)} with {reg_top_field_q_assn(reg, field)}"
        for field in reg.fields
    )


def reg_top_field_qe_assn(reg: Register, field: Field):
    # TODO: this is probably wrong for ro fields with hwqe set.
    return rf"""{name(field)}_qe := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));"""


def reg_top_reg_qe_assns(reg: Register):
    return (
        f"{name(reg)} := s'.reg2hw.{name(reg)} with {reg_top_field_qe_assn(reg, field)}"
        for field in reg.fields
    )


def reg_top_field_assn(reg: Register, field: Field):
    # Use the same format in the case of doing nothing as well, so that we can
    # factor it out into `s' with ... := if .. then ... else ...`.
    #
    # TODO: consider turning this into a generalised transformation instead?
    #
    # There'd still need to be the manual step of turning things into
    # `i2c_reg_error` for `comb_1` though.
    #
    # NOTE: if we want to try and turn this back into plain `s'` with some
    # post-processing, we should be able to do so by changing this to `s'.*` and
    # using theorems of the form `rec with field := rec.field = rec`.
    unchanged = f"s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := s.regs.{name(reg)}.{name(field)}"
    if field.hwaccess.allows_write():
        hw_if = f""" if s'.hw2reg.{name(reg)}.{name(field)}_de then
      s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := s'.hw2reg.{name(reg)}.{name(field)}_d
    else
      {unchanged}"""
    else:
        hw_if = f"\n      {unchanged}"

    if field.swaccess.allows_write():
        # field_value is only used in the case of rw1c, so we don't have to worry about
        # rw1c_field_value not making sense in the other cases.
        return rf"""s' = if s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := {new_field_value(reg, field, "s'.wdata", rw1c_field_value)}
    else{hw_if};"""
    else:
        return f"s' ={hw_if};"


def reg_top_error_case(reg: Register):
    min_bytes = ceil(reg.get_width() / 8)
    return rf"{hex(reg.offset)}w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ (({min_bytes - 1} >< 0) s'.wstrb: {min_bytes} word) <> {(1 << min_bytes) - 1}w) s'.reg_rsp_o"


def reg_init(reg: Register):
    # The documentation for `resval` is wrong: fields with a `resval` of None are always reset to 0, not `'x`'.
    return f"""<|
      {"\n      ".join(f"{name(field)} := {field.resval or 0}w;" for field in reg.fields)}
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

regs_circuit_lib = f"""\
structure {ip.name}RegsCircuitLib =
struct

open wordsLib;
open {ip.name}CircuitStateTheory {ip.name}RegsTheory {ip.name}RegsCommTheory;

(* The translator will only look for processes in the same theory as the
 * top-level `mk_module`, so we just export the bodies of these functions and
 * let `i2cCircuitTheory` make the actual definitions. *)
val {ip.name}_reg_top_comb_1_tm = ``
  let
    s' = s' with addr := (reg_req_decode fext.reg_req_i: 7 reg_req).addr;
    s' = s' with write := (reg_req_decode fext.reg_req_i: 7 reg_req).write;
    s' = s' with wdata := (reg_req_decode fext.reg_req_i: 7 reg_req).wdata;
    s' = s' with wstrb := (reg_req_decode fext.reg_req_i: 7 reg_req).wstrb;
    s' = s' with valid := (reg_req_decode fext.reg_req_i: 7 reg_req).valid;

    s' = case s'.addr of
      {"\n    | ".join(reg_top_error_case(reg) for reg in block.entries)}
    | _ => s' with reg_rsp_o := (1 :+ s'.valid) s'.reg_rsp_o;
    s' = s' with reg_rsp_o := (0 :+ T) s'.reg_rsp_o;

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in block.entries for assn in reg_top_reg_q_assns(reg) if not reg.hwext and reg.hwaccess.allows_read())}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in block.entries for assn in reg_top_reg_hwext_q_assns(reg) if reg.hwext and reg.hwaccess.allows_read())}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in block.entries for assn in reg_top_reg_hwext_qe_re_assns(reg) if reg.hwext and (reg.hwqe or reg.hwre))}
  in
    s'
``

val {ip.name}_reg_top_comb_2_tm = ``
  case s'.addr of
    (* TODO: this won't produce the prettiest Verilog. To do that, we'd need to turn
     * this into a let..in with an assignment for each field of the register, but
     * that would make sharing code with the HOL version more annoying.
     *
     * Alternatively, using @@ would be a lot less ugly than this. *)
    {"\n  | ".join(f"{hex(reg.offset)}w => s' with reg_rsp_o := bit_field_insert 33 2 ({reg_value(reg, hw_field_value)}: word32) s'.reg_rsp_o" for reg in block.entries)}
  | _ => s' with reg_rsp_o := bit_field_insert 33 2 (0xffffffffw: word32) s'.reg_rsp_o
``

val {ip.name}_reg_top_ff_tm = ``
  let
    {"\n    ".join(reg_top_field_assn(reg, field) for reg in block.entries for field in reg.fields if not reg.hwext and (field.swaccess.allows_write() or field.hwaccess.allows_write()))}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in block.entries for assn in reg_top_reg_qe_assns(reg) if not reg.hwext and reg.hwqe)}
  in
    s'
``

val {ip.name}_regs_init_tm = ``
  (<|
    {"\n    ".join(f"{name(reg)} := {reg_init(reg)};" for reg in block.entries if not reg.hwext)}
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
    f.write(regs_circuit_lib)
