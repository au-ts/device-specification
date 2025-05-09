open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory "cheshireCircuit";

Datatype:
  reg_req = <|
    addr: 'a word;
    write: bool;
    wdata: word32;
    wstrb: word4;
    valid: bool;
  |>
End

Datatype:
  reg_rsp = <|
    rdata: word32;
    error: bool;
    ready: bool;
  |>
End

Definition reg_req_decode_def:
  reg_req_decode (value: 'b word): 'a reg_req = <|
    addr := (37 + dimindex (:'a) >< 38) value;
    write := word_bit 37 value;
    wdata := (36 >< 5) value;
    wstrb := (4 >< 1) value;
    valid := word_bit 0 value;
  |>
End

Definition reg_rsp_decode_def:
  reg_rsp_decode (value: 34 word): reg_rsp = <|
    rdata := (33 >< 2) value;
    error := word_bit 1 value;
    ready := word_bit 0 value;
  |>
End

Definition cheshire_req_rel_def:
  cheshire_req_rel (req_m: (num # num # word32 option) option) (req_c: 'a reg_req) <=>
  req_c.valid = IS_SOME req_m /\
  (!nb offset wdata. req_m = SOME (nb, offset, wdata) ==>
    req_c.write = IS_SOME wdata /\
    offset = w2n req_c.addr /\
    (!i. word_bit i req_c.wstrb <=> i < nb) /\
    (!value. wdata = SOME value ==> req_c.wdata = value))
End

Theorem cheshire_req_rel_read:
  cheshire_req_rel (SOME (nb, offset, NONE)) req_c <=>
  req_c.valid /\ ~req_c.write /\ offset = w2n req_c.addr /\
  (!i. word_bit i req_c.wstrb <=> i < nb)
Proof
  simp [cheshire_req_rel_def]
QED

Theorem cheshire_req_rel_write:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req_c <=>
  req_c.valid /\ req_c.write /\ offset = w2n req_c.addr /\ req_c.wdata = wdata /\
  (!i. word_bit i req_c.wstrb <=> i < nb)
Proof
  simp [cheshire_req_rel_def, CONJ_COMM]
QED

Theorem cheshire_req_rel_valid_write:
  cheshire_req_rel req_m req_c ==>
  ((?nb offset wdata. req_m = SOME (nb, offset, SOME wdata)) <=> req_c.valid /\ req_c.write)
Proof
  simp [cheshire_req_rel_def]
  >> rpt strip_tac
  >> iff_tac
  >- (rpt strip_tac >> fs [])
  >- (simp [optionTheory.IS_SOME_EXISTS]
      >> rpt strip_tac
      >> PairCases_on `x`
      >> fs [optionTheory.IS_SOME_EXISTS])
QED

val _ = export_theory ();
