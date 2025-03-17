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
  reg_rsp_decode (value: 'b word): reg_rsp = <|
    rdata := (33 >< 2) value;
    error := word_bit 1 value;
    ready := word_bit 0 value;
  |>
End

val _ = export_theory ();
