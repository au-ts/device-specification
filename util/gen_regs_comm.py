import itertools
import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register

from .common import addr_width, ip, name, regs, windows


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
        for reg in regs
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
        for reg in regs
        if reg_needs_hw2reg(reg)
    )
    return f"""\
Datatype:
  {ip.name}_hw2reg = <|
    {"\n    ".join(decls)}
  |>
End"""


def win_buses_req_def():
    if len(windows) == 0:
        return f"Type {ip.name}_win_buses_req = ``:unit``;"
    else:
        return f"""\
Datatype:
  {ip.name}_win_buses_req = <|
    {"\n    ".join(f"{name(window)}: 48 reg_req;" for window in windows)}
  |>
End"""


def win_buses_rsp_def():
    if len(windows) == 0:
        return f"Type {ip.name}_win_buses_rsp = ``:unit``;"
    else:
        return f"""\
Datatype:
  {ip.name}_win_buses_rsp = <|
    {"\n    ".join(f"{name(window)}: reg_rsp;" for window in windows)}
  |>
End"""


def req_error_case(reg: Register, alt: bool):
    min_bytes = ceil(reg.get_width() / 8)
    valid = r"req.valid /\ " if alt else ""
    return rf"{hex(reg.offset)}w => {valid}req.write /\ (({min_bytes - 1} >< 0) req.wstrb: {min_bytes} word) <> {(1 << min_bytes) - 1}w"


def req_error():
    return f"""\
Definition {ip.name}_req_error_def:
  {ip.name}_req_error (req: {addr_width} reg_req) <=>
  req.valid /\\ case req.addr of
    {"\n  | ".join(req_error_case(reg, False) for reg in regs)}
  | _ => T
End"""


def req_error_alt():
    return f"""\
Theorem {ip.name}_req_error_alt:
  {ip.name}_req_error (req: {addr_width} reg_req) <=>
  case req.addr of
    {"\n  | ".join(req_error_case(reg, True) for reg in regs)}
  | _ => req.valid
Proof
  simp [{ip.name}_req_error_def]
  >> rpt (IF_CASES_TAC >- simp [])
  >> simp []
QED"""


def win_addr_exp():
    if len(windows) == 0:
        return "F"
    else:
        return " \\/\n  ".join(
            rf"({hex(window.offset)} <= offset /\ offset < {hex(window.offset + window.size_in_bytes)})"
            for window in windows
        )


def field_notif_rel(reg: Register, field: Field):
    return f"(reg2hw.{name(reg)}.{name(field)}_qe <=> notif = SOME {name(reg)}_write)"


def reg_hwext_notif_rels(reg: Register):
    result = []
    if reg.hwqe:
        result += [
            rf"(!value. notif = SOME (Write ({name(reg)}_write value)) <=> req.addr = {hex(reg.offset)}w /\ req.valid /\ req.write /\ ~{ip.name}_req_error req /\ {ip.name}_{name(reg)}_decode_write req.wdata = value)"
        ]
    if reg.hwre:
        result += [
            rf"(notif = SOME (Read {name(reg)}_read) <=> req.addr = {hex(reg.offset)}w /\ req.valid /\ ~req.write /\ ~{ip.name}_req_error req)"
        ]
    return result


def notif_rel_exp():
    if any(field.hwqe and not reg.hwext for reg in regs for field in reg.fields):
        return " /\\\n  ".join(
            field_notif_rel(reg, field)
            for reg in regs
            for field in reg.fields
            if field.hwqe and not reg.hwext
        )
    else:
        return "T"


def hwext_notif_rel_exp():
    if any(reg.hwext for reg in regs):
        return " /\\\n    ".join(
            term for reg in regs for term in reg_hwext_notif_rels(reg) if reg.hwext
        )
    else:
        return "T"


def hw_write_rel_exp():
    if any(
        not reg.hwext and field.hwaccess.allows_write()
        for reg in regs
        for field in reg.fields
    ):
        return " /\\\n  ".join(
            rf"regs'.{name(reg)}.{name(field)} = (if hw2reg.{name(reg)}.{name(field)}_de then hw2reg.{name(reg)}.{name(field)}_d else regs.{name(reg)}.{name(field)})"
            for reg in regs
            for field in reg.fields
            if not reg.hwext and field.hwaccess.allows_write()
        )
    else:
        return "T"


def hwext_read_rel_exp():
    if any(
        reg.hwext and field.swaccess.allows_read()
        for reg in regs
        for field in reg.fields
    ):
        return " /\\\n  ".join(
            f"hw2reg.{name(reg)}.{name(field)}_d = {ip.name}_get_{name(reg)}_{name(field)} st"
            for reg in regs
            for field in reg.fields
            # TODO: why is this an `any`? shouldn't it just be field.swaccess.allows_read?
            if reg.hwext and any(field.swaccess.allows_read() for field in reg.fields)
        )
    else:
        return "T"


def win_notif_rel_exp():
    if len(windows) == 0:
        return "T"
    else:
        # The slicing of `addr` is to stop windows from depending on upper bits of the
        # address which we don't preserve.
        #
        # Note that this is a restriction not enforced by the hardware, since it does
        # preserve those bits. I'd hope that nothing relies on them, though.
        conjuncts = []
        for window in windows:
            conjuncts.append(rf"""(!nb offset.
    cheshire_req_rel (SOME (nb, offset, NONE)) (buses.req.{name(window)} with addr := (({addr_width - 1} >< 0) buses.req.{name(window)}.addr: {addr_width} word))
    /\ buses.rsp.{name(window)}.ready
    <=> notif = SOME (Read ({name(window)}_read nb offset)))""")
            conjuncts.append(rf"""(!nb offset wdata.
    cheshire_req_rel (SOME (nb, offset, SOME wdata)) (buses.req.{name(window)} with addr := (({addr_width - 1} >< 0) buses.req.{name(window)}.addr: {addr_width} word))
    /\ buses.rsp.{name(window)}.ready
    <=> notif = SOME (Write ({name(window)}_write nb offset wdata)))""")
        return " /\\\n  ".join(conjuncts)


def win_read_rel_exp():
    if len(windows) == 0:
        return "T"
    else:
        return " /\\\n  ".join(
            rf"""(!nb offset.
    cheshire_req_rel (SOME (nb, offset, NONE)) (buses.req.{name(window)} with addr := (({addr_width - 1} >< 0) buses.req.{name(window)}.addr: {addr_width} word))
    /\ buses.rsp.{name(window)}.ready
    ==> buses.rsp.{name(window)}.error
    \/ buses.rsp.{name(window)}.rdata = {ip.name}_{name(window)}_read st nb offset)"""
            for window in windows
        )


def win_error_exp():
    if len(windows) == 0:
        return "F"
    else:
        return " \\/\n  ".join(
            rf"buses.req.{name(window)}.valid /\ buses.rsp.{name(window)}.ready /\ buses.rsp.{name(window)}.error"
            for window in windows
        )


# We're also assuming that the window always responds immediately; we shouldn't, but this is the case for SPI and changing this would require rejiggering the way the model works.
def win_ready_exp():
    if len(windows) == 0:
        return "T"
    else:
        return " /\\\n  ".join(
            rf"(buses.req.{name(window)}.valid ==> buses.rsp.{name(window)}.ready)"
            for window in windows
        )


regs_comm = f"""\
open HolKernel Parse boolLib bossLib;
open BasicProvers wordsLib;
open wordsTheory;
open cheshireCircuitTheory cheshireMiscTheory cheshireOracleTheory {ip.name}CoreTheory {ip.name}RegsTheory {ip.name}MappingsTheory;

val _ = new_theory "{ip.name}RegsComm";

{"\n\n".join(reg_reg2hw_def(reg) for reg in regs if reg_needs_reg2hw(reg))}

{reg2hw_def()}

{"\n\n".join(reg_hw2reg_def(reg) for reg in regs if reg_needs_hw2reg(reg))}

{hw2reg_def()}

{win_buses_req_def()}

{win_buses_rsp_def()}

Datatype:
  {ip.name}_win_buses = <|
    req: {ip.name}_win_buses_req;
    rsp: {ip.name}_win_buses_rsp;
  |>
End

Definition {ip.name}_notif_rel_def:
  {ip.name}_notif_rel (notif: {ip.name}_notif option) (reg2hw: {ip.name}_reg2hw) <=>
  {notif_rel_exp()}
End

(* Whether a request is not a valid register access.
 *
 * Note that this also considers window accesses to be errors (in line with
 * `*_reg_top`'s `error` signal). *)
{req_error()}

{req_error_alt()}

(* Whether an address falls within a window. *)
Definition {ip.name}_win_addr_def:
  {ip.name}_win_addr (offset: num) <=>
  {win_addr_exp()}
End

Definition {ip.name}_hwext_notif_rel_def:
  {ip.name}_hwext_notif_rel (notif: {ip.name}_hwext_notif option) (req: {addr_width} reg_req) <=>
    {" /\\\n    ".join(term for reg in regs for term in reg_hwext_notif_rels(reg) if reg.hwext)}
End

Definition {ip.name}_hwext_read_rel_def:
  {ip.name}_hwext_read_rel (st: {ip.name}_state) (hw2reg: {ip.name}_hw2reg) <=>
  (* TODO: we probably shouldn't be including write-only fields in a hwext struct
   * which happens to have other readable fields here? *)
  {hwext_read_rel_exp()}
End

Theorem {ip.name}_hwext_read_rel_fnums:
  {ip.name}_hwext_read_rel (st with fnums := fnums) = {ip.name}_hwext_read_rel st
Proof
  irule EQ_EXT >> simp [{ip.name}_hwext_read_rel_def{"".join(f", {ip.name}_get_{name(reg)}_{name(field)}_def" for reg in regs for field in reg.fields if reg.hwext and field.swaccess.allows_read())}]
QED

Definition {ip.name}_win_notif_rel_def:
  {ip.name}_win_notif_rel (notif: {ip.name}_hwext_notif option) (buses: {ip.name}_win_buses) <=>
  {win_notif_rel_exp()}
End

Definition {ip.name}_win_read_rel_def:
  {ip.name}_win_read_rel (st: {ip.name}_state) (buses: {ip.name}_win_buses) <=>
  {win_read_rel_exp()}
End

Theorem {ip.name}_win_read_rel_fnums:
  {ip.name}_win_read_rel (st with fnums := fnums) = {ip.name}_win_read_rel st
Proof
  irule EQ_EXT >> simp [{ip.name}_win_read_rel_def{"".join(f", {ip.name}_{name(window)}_read_def" for window in windows)}]
QED

(* Whether the transition from `regs` -> `regs'` is in accordance with the
 * instructions in `hw2reg`. *)
Definition {ip.name}_hw_write_rel_def:
  (* hw2reg is from the same clock cycle as `regs`, not `regs'`. *)
  {ip.name}_hw_write_rel (regs: {ip.name}_regs) (regs': {ip.name}_regs) (hw2reg: {ip.name}_hw2reg) <=>
  {hw_write_rel_exp()}
End

Definition {ip.name}_win_error_def:
  {ip.name}_win_error (buses: {ip.name}_win_buses) <=>
  {win_error_exp()}
End

Definition {ip.name}_win_ready_def:
  {ip.name}_win_ready (buses: {ip.name}_win_buses) <=>
  {win_ready_exp()}
End

(* This probably shouldn't go here but I don't want to create a whole new file
 * just for this. *)
Theorem {ip.name}_tick_hwro_unchanged:
  {ip.name}_tick notif st = INR st' ==>
  {" /\\\n  ".join(f"st'.regs.{name(reg)}.{name(field)} = st.regs.{name(reg)}.{name(field)}" for reg in regs for field in reg.fields if not reg.hwext and not field.hwaccess.allows_write())}
Proof
  pure_rewrite_tac [{ip.name}_tick_def]
  >> disch_then (assume_tac o GSYM)
  >> fs []
  >> rpt (pairarg_tac >> fs [])
  >> rpt IF_CASES_TAC
  >> simp []
QED

Theorem nb_wstrb:
  (!i. word_bit i (wstrb: word4) <=> i < nb) /\\ n + 1 = dimindex (:'b) ==>
  (((n >< 0) wstrb: 'b word) = -1w <=> nb > n)
Proof
  rpt strip_tac
  >> full_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [arithmeticTheory.GREATER_DEF, word_bit_def, word_extract_def, WORD_NEG_1_T, w2w, word_bits_def, Cong AND_CONG, arithmeticTheory.LE_LT1]
  >> iff_tac
  >> simp []
QED

val nb_wstrb_insts = [1, 2, 3, 4] |> map (fn bits =>
  let
    val all_ones_val = EVAL (wordsSyntax.mk_wordii (1, bits) |> wordsSyntax.mk_word_2comp);
  in
    nb_wstrb
      |> INST [``n: num`` |-> numSyntax.term_of_int (bits - 1)]
      |> INST_TYPE [``:'b`` |-> fcpSyntax.mk_int_numeric_type bits]
      |> SRULE [all_ones_val]
  end);

Triviality GT_GE1:
  (a: num) > b <=> a >= b + 1
Proof
  decide_tac
QED

Theorem {ip.name}_req_error_{ip.name}_write:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req ==>
  (ISL ({ip.name}_write st nb offset wdata) <=> {ip.name}_req_error req /\\ ~{ip.name}_win_addr offset)
Proof
  simp [cheshire_req_rel_write]
  >> rpt strip_tac
  >> asm_simp_tac std_ss [{ip.name}_write_def, dimword_def, dimindex_{addr_width}, GSYM eq_n2w_iff_w2n_eq]
  >> rpt TOP_CASE_TAC
  >> simp [{ip.name}_win_addr_def, {ip.name}_req_error_def]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> fs [GT_GE1]
QED

Theorem {ip.name}_req_error_{ip.name}_read:
  cheshire_req_rel (SOME (nb, offset, NONE)) req ==>
  (ISL ({ip.name}_read st nb offset) <=> {ip.name}_req_error req /\\ ~{ip.name}_win_addr offset)
Proof
  simp [cheshire_req_rel_read]
  >> rpt strip_tac
  >> simp [{ip.name}_read_def, GSYM eq_n2w_iff_w2n_eq]
  >> rpt IF_CASES_TAC
  >> simp [{ip.name}_win_addr_def, {ip.name}_req_error_def]
QED

Theorem cheshire_req_{ip.name}_req_error:
  cheshire_req_rel req_m req_c ==>
  (ISL (cheshire_req {ip.name}_read {ip.name}_write st req_m) <=> {ip.name}_req_error req_c /\\ ~{ip.name}_win_addr (w2n req_c.addr))
Proof
  rpt strip_tac
  >> simp [cheshire_req_def]
  >> rpt TOP_CASE_TAC
  >- fs [cheshire_req_rel_def, {ip.name}_req_error_def]
  >- fs [ISL_SUM_MAP, cheshire_req_rel_def, {ip.name}_req_error_{ip.name}_read]
  >- fs [ISL_SUM_MAP, cheshire_req_rel_def, {ip.name}_req_error_{ip.name}_write]
QED

Theorem {ip.name}_write_{ip.name}_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req /\\
  {ip.name}_write st nb offset wdata = INR (_, notif) ==>
  {ip.name}_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_write]
  >> pure_rewrite_tac [{ip.name}_write_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> fs [{ip.name}_hwext_notif_rel_def, {ip.name}_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
  >> simp [GSYM eq_n2w_iff_w2n_eq]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> gvs []
QED

Theorem {ip.name}_read_{ip.name}_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, NONE)) req /\\
  {ip.name}_read st nb offset = INR (notif, _) ==>
  {ip.name}_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_read]
  >> pure_rewrite_tac [{ip.name}_read_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> gvs [{ip.name}_hwext_notif_rel_def, {ip.name}_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
QED

Theorem cheshire_req_{ip.name}_hwext_notif_rel:
  cheshire_req_rel req_m req_c /\\
  cheshire_req {ip.name}_read {ip.name}_write st req_m = INR (_, notif, _) ==>
  {ip.name}_hwext_notif_rel notif req_c
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac cheshire_req_INR_cases
  >- fs [cheshire_req_rel_def, {ip.name}_hwext_notif_rel_def, {ip.name}_req_error_def]
  >- (fs [] >> drule_all {ip.name}_read_{ip.name}_hwext_notif_rel >> simp [])
  >- (fs [] >> drule_all {ip.name}_write_{ip.name}_hwext_notif_rel >> simp [])
QED

Theorem {ip.name}_win_addr_{ip.name}_req_error:
  req.valid /\\ {ip.name}_win_addr (w2n req.addr) ==> {ip.name}_req_error req
Proof
  simp [{ip.name}_win_addr_def, {ip.name}_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
QED

val _ = export_theory ();
"""

with open(sys.argv[2], "w") as f:
    f.write(regs_comm)
