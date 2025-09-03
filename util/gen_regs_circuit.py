import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register
from reggen.window import Window

from .common import addr_width, ip, name, new_field_value, reg_value, regs, windows


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
        assns.append(
            rf"{name(field)}_qe := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~s'.error);"
        )
    if field.hwre:
        assns.append(
            rf"{name(field)}_re := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ ~s'.write /\ ~s'.error);"
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
    return rf"""{name(field)}_qe := (s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~s'.error);"""


def reg_top_reg_qe_assns(reg: Register):
    return (
        f"{name(reg)} := s'.reg2hw.{name(reg)} with {reg_top_field_qe_assn(reg, field)}"
        for field in reg.fields
    )


def reg_top_window_reg_rsp_o_assn(window: Window):
    return rf"""if {hex(window.offset)}w <=+ s'.addr /\ s'.addr <+ {hex(window.offset + window.size_in_bytes)}w then
    let
      s' = s' with reg_rsp_o := (0 :+ s'.win_buses.rsp.{name(window)}.ready) s'.reg_rsp_o;
      s' = s' with reg_rsp_o := (1 :+ s'.win_buses.rsp.{name(window)}.error) s'.reg_rsp_o;
      s' = s' with reg_rsp_o := bit_field_insert 33 2 s'.win_buses.rsp.{name(window)}.rdata s'.reg_rsp_o;
    in
      s'"""


def reg_top_window_reg_req_win_assn(window: Window):
    return rf"""if {hex(window.offset)}w <=+ s'.addr /\ s'.addr <+ {hex(window.offset + window.size_in_bytes)}w then let
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with addr := (reg_req_decode fext.reg_req_i: 48 reg_req).addr;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with write := (reg_req_decode fext.reg_req_i: 48 reg_req).write;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with wdata := (reg_req_decode fext.reg_req_i: 48 reg_req).wdata;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with wstrb := (reg_req_decode fext.reg_req_i: 48 reg_req).wstrb;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with valid := (reg_req_decode fext.reg_req_i: 48 reg_req).valid;
    in
      s'
    else let
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with addr := (reg_req_decode (0w: 86 word): 48 reg_req).addr;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with write := (reg_req_decode (0w: 86 word): 48 reg_req).write;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with wdata := (reg_req_decode (0w: 86 word): 48 reg_req).wdata;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with wstrb := (reg_req_decode (0w: 86 word): 48 reg_req).wstrb;
      s' = s' with win_buses := s'.win_buses with req := s'.win_buses.req with {name(window)} := s'.win_buses.req.{name(window)} with valid := (reg_req_decode (0w: 86 word): 48 reg_req).valid;
    in
      s'"""


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
        return rf"""s' = if s'.addr = {hex(reg.offset)}w /\ s'.valid /\ s'.write /\ ~s'.error then
      s' with regs := s'.regs with {name(reg)} := s'.regs.{name(reg)} with {name(field)} := {new_field_value(reg, field, "s'.wdata", rw1c_field_value)}
    else{hw_if};"""
    else:
        return f"s' ={hw_if};"


def reg_top_error_case(reg: Register):
    min_bytes = ceil(reg.get_width() / 8)
    return rf"{hex(reg.offset)}w => s' with error := (s'.valid /\ s'.write /\ (({min_bytes - 1} >< 0) s'.wstrb: {min_bytes} word) <> {(1 << min_bytes) - 1}w)"


def reg_init(reg: Register):
    # The documentation for `resval` is wrong: fields with a `resval` of None are always reset to 0, not `'x`'.
    return f"""<|
      {"\n      ".join(f"{name(field)} := {field.resval or 0}w;" for field in reg.fields)}
    |>"""


def regs_init():
    if any(not reg.hwext for reg in regs):
        return f"""\
val {ip.name}_regs_init_tm = ``
  (<|
    {"\n    ".join(f"{name(reg)} := {reg_init(reg)};" for reg in regs if not reg.hwext)}
  |>): {ip.name}_regs
``;"""
    else:
        return f"val {ip.name}_regs_init_tm = ``ARB: {ip.name}_regs``;"


def reg2hw_reg_init(reg: Register):
    return f"""<|
      {"\n      ".join(f"{name(field)}_qe := F;" for field in reg.fields if field.hwqe)}
    |>"""


def reg2hw_init():
    if any(not reg.hwext and reg.hwqe for reg in regs):
        return f"""\
val {ip.name}_reg2hw_init_tm = ``
  (<|
    {"\n    ".join(f"{name(reg)} := {reg2hw_reg_init(reg)};" for reg in regs if not reg.hwext and reg.hwqe)}
  |>): {ip.name}_reg2hw
``;
"""
    else:
        return f"val {ip.name}_reg2hw_init_tm = ``ARB: {ip.name}_reg2hw``;"


comms = [
    f'"regs_{name(reg)}_{name(field)}"'
    for reg in regs
    for field in reg.fields
    if not reg.hwext
] + [
    f'"reg2hw_{name(reg)}_{name(field)}_qe"'
    for reg in regs
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
 * let `{ip.name}CircuitTheory` make the actual definitions. *)
val {ip.name}_reg_top_comb_1_tm = ``
  let
    s' = s' with addr := (reg_req_decode fext.reg_req_i: {addr_width} reg_req).addr;
    s' = s' with write := (reg_req_decode fext.reg_req_i: {addr_width} reg_req).write;
    s' = s' with wdata := (reg_req_decode fext.reg_req_i: {addr_width} reg_req).wdata;
    s' = s' with wstrb := (reg_req_decode fext.reg_req_i: {addr_width} reg_req).wstrb;
    s' = s' with valid := (reg_req_decode fext.reg_req_i: {addr_width} reg_req).valid;

    s' = case s'.addr of
      {"\n    | ".join(reg_top_error_case(reg) for reg in regs)}
    | _ => s' with error := s'.valid;

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in regs for assn in reg_top_reg_q_assns(reg) if not reg.hwext and reg.hwaccess.allows_read())}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in regs for assn in reg_top_reg_hwext_q_assns(reg) if reg.hwext and reg.hwaccess.allows_read())}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in regs for assn in reg_top_reg_hwext_qe_re_assns(reg) if reg.hwext and (reg.hwqe or reg.hwre))}

    {"\n    ".join(f"s' = {reg_top_window_reg_req_win_assn(window)};" for window in windows)}
  in
    s'
``

val {ip.name}_reg_top_comb_2_tm = ``
  {" ".join(reg_top_window_reg_rsp_o_assn(window) + "\n  else" for window in windows)}
    let
      s' = s' with reg_rsp_o := (0 :+ T) s'.reg_rsp_o;
      s' = s' with reg_rsp_o := (1 :+ s'.error) s'.reg_rsp_o;
      s' = case s'.addr of
        (* TODO: this won't produce the prettiest Verilog. To do that, we'd need to turn
         * this into a let..in with an assignment for each field of the register, but
         * that would make sharing code with the HOL version more annoying.
         *
         * Alternatively, using @@ would be a lot less ugly than this. *)
        {"\n      | ".join(f"{hex(reg.offset)}w => s' with reg_rsp_o := bit_field_insert 33 2 ({reg_value(reg, hw_field_value)}: word32) s'.reg_rsp_o" for reg in regs)}
      | _ => s' with reg_rsp_o := bit_field_insert 33 2 (0xffffffffw: word32) s'.reg_rsp_o;
    in
      s'
``

val {ip.name}_reg_top_ff_tm = ``
  let
    {"\n    ".join(reg_top_field_assn(reg, field) for reg in regs for field in reg.fields if not reg.hwext and (field.swaccess.allows_write() or field.hwaccess.allows_write()))}

    {"\n    ".join(f"s' = s' with reg2hw := s'.reg2hw with {assn}" for reg in regs for assn in reg_top_reg_qe_assns(reg) if not reg.hwext and reg.hwqe)}
  in
    s'
``

{regs_init()}

{reg2hw_init()}

val {ip.name}_reg_comms = [{", ".join(comms)}];

end
"""

with open(sys.argv[2], "w") as f:
    f.write(regs_circuit_lib)
