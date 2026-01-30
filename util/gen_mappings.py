# TODO: maybe remove the unused st argument from write?

import sys
from math import ceil

# Set PYTHONPATH=${register_interface}/vendor/lowrisc_opentitan/util for these imports to work.
from reggen.field import Field
from reggen.register import Register
from reggen.window import Window

from .common import (
    addr_width,
    entries,
    ip,
    name,
    new_field_value,
    reg_value,
    regs,
    windows,
)


def oracle_field_value(entry: Register, field: Field):
    if entry.hwext:
        return (
            f"({ip.name}_get_{name(entry)}_{name(field)} st: {field.bits.width()} word)"
        )
    else:
        return f"st.regs.{name(entry)}.{name(field)}"


def oracle_next_field_value(reg: Register, field: Field):
    return f"st'.regs.{name(reg)}.{name(field)}"


def read_case(entry: Register | Window):
    if isinstance(entry, Window):
        # Pass through the offset relative to the start of the whole block, not just
        # this window, since that's closer to how the actual hardware works (except it
        # gets the absolute address, not just the address relative to the block).
        #
        # TODO: is this the right design?
        return rf"""if {hex(entry.offset)} <= offset /\ offset < {hex(entry.offset + entry.size_in_bytes)} then
    INR (SOME (Read ({name(entry)}_read nb offset)), {ip.name}_{name(entry)}_read st nb offset: word32)"""
    else:
        if any(field.hwre for field in entry.fields):
            read_notif = f"SOME (Read {name(entry)}_read)"
        else:
            read_notif = "NONE"
        return f"""if offset = {hex(entry.offset)} then
    INR ({read_notif}, {reg_value(entry, oracle_field_value)}: word32)"""


def write_case(entry: Register | Window):
    prefix = ""
    if isinstance(entry, Window):
        cond = rf"{hex(entry.offset)} <= offset /\ offset < {hex(entry.offset + entry.size_in_bytes)}"
        st_upd = "I"
        write_notif = f"SOME (Write ({name(entry)}_write nb offset wdata))"
    else:
        width = ceil(entry.get_width() / 8)
        cond = rf"offset = {hex(entry.offset)} /\ nb >= {width}"

        writable = any(field.swaccess.allows_write() for field in entry.fields)

        write_notif = "NONE"
        buffered_write_notif = None
        if any(field.hwqe for field in entry.fields):
            # TODO: I don't think this works correctly in the case of ro + hwqe + hwext, but
            # we don't care about that case anyway.
            if entry.hwext:
                write_notif = f"SOME (Write ({name(entry)}_write ({ip.name}_{name(entry)}_decode_write wdata)))"
            else:
                buffered_write_notif = f"SOME {name(entry)}_write"

        if writable and not entry.hwext:
            field_updates = (
                f"{name(field)} := {new_field_value(entry, field, 'wdata', oracle_next_field_value)};"
                for field in entry.fields
                if field.swaccess.allows_write()
            )
            # This gets tacked onto the end of a fresh `i2c_tick`, which always sets
            # `buffered_notif` to NONE, so we shouldn't be overwriting anything here.
            prefix = f"""let
      st_upd = \\st'. st' with <|
        regs := st'.regs with {name(entry)} := st'.regs.{name(entry)} with <|
          {"\n          ".join(field_updates)}
        |>;{"" if buffered_write_notif is None else f"\n      buffered_notif := {buffered_write_notif};"}
      |>
    in
      """
            st_upd = "st_upd"
        else:
            st_upd = "I"

    return rf"""if {cond} then
    {prefix}INR ({st_upd}, {write_notif})"""


read_cases = [read_case(entry) for entry in entries]
write_cases = [write_case(entry) for entry in entries]

# It isn't strictly a failure if we read/write an invalid address, so it'd be
# fine to loosen this to returning all 1s / doing nothing on read / write.
# (Except when devmode_i is set, anyway.)
#
# Undersized writes are always bus errors, though.
read_cases.append("\n    INL FFI_failed")
write_cases.append("\n    INL FFI_failed")


def field_st_upd_assn(reg: Register, field: Field):
    return rf"{name(field)} := if offset = {hex(reg.offset)} then {new_field_value(reg, field, 'wdata', oracle_next_field_value)} else st'.regs.{name(reg)}.{name(field)};"


def reg_st_upd_assn(reg: Register):
    return f"""{name(reg)} := st'.regs.{name(reg)} with <|
        {"\n        ".join(field_st_upd_assn(reg, field) for field in reg.fields if field.swaccess.allows_write())}
      |>;"""


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


mappings = f"""\
open HolKernel Parse boolLib bossLib;
open BasicProvers wordsLib;
open alignmentTheory wordsTheory;
open ffiTheory;
open cheshireCircuitTheory cheshireMiscTheory cheshireOracleTheory {ip.name}CoreTheory {ip.name}RegsTheory {ip.name}RegsCommTheory;

val _ = new_theory("{ip.name}Mappings");

Definition {ip.name}_read_def:
  {ip.name}_read (st: {ip.name}_state) (nb: num) (offset: num): ffi_outcome + {ip.name}_hwext_notif option # word32 =
  {"\n  else ".join(read_cases)}
End

Definition {ip.name}_write_def:
  {ip.name}_write (st: {ip.name}_state) (nb: num) (offset: num) (wdata: word32): ffi_outcome + ({ip.name}_state -> {ip.name}_state) # {ip.name}_hwext_notif option =
  {"\n  else ".join(write_cases)}
End

Theorem {ip.name}_write_st_upd_alt:
  {ip.name}_write st nb offset wdata = INR (st_upd, notif) ==>
  st_upd = \\st'. st' with <|
    regs := st'.regs with <|
        {"\n      ".join(reg_st_upd_assn(reg) for reg in regs if not reg.hwext and any(field.swaccess.allows_write() for field in reg.fields))}
    |>;
    buffered_notif := case offset of
      {"\n    | ".join(f"{hex(reg.offset)} => SOME {name(reg)}_write" for reg in regs if not reg.hwext and any(field.hwqe for field in reg.fields))}
    | _ => st'.buffered_notif;
  |>
Proof
  pure_rewrite_tac [{ip.name}_write_def]
  >> rpt (TOP_CASE_TAC
          >- (fs []
              >> strip_tac
              >> TRY (qpat_x_assum `_ = st_upd` (assume_tac o GSYM))
              >> irule EQ_EXT
              >> simp [{ip.name}_state_component_equality, {ip.name}_regs_component_equality, {", ".join(f"{ip.name}_{name(reg)}_component_equality" for reg in regs if not reg.hwext)}]))
QED

Definition {ip.name}_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  {ip.name}_addrs = {{{"; ".join(f"byte_align {hex(reg.offset)}w" for reg in regs)}}}
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

Definition {ip.name}_win_read_rel_def:
  {ip.name}_win_read_rel (st: {ip.name}_state) (buses: {ip.name}_win_buses) <=>
  {win_read_rel_exp()}
End

Theorem {ip.name}_win_read_rel_fnums:
  {ip.name}_win_read_rel (st with fnums := fnums) = {ip.name}_win_read_rel st
Proof
  irule EQ_EXT >> simp [{ip.name}_win_read_rel_def{"".join(f", {ip.name}_{name(window)}_read_def" for window in windows)}]
QED

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

val _ = export_theory();
"""

with open(sys.argv[2], "w") as f:
    f.write(mappings)
