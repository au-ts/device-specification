open HolKernel Parse boolLib bossLib;
open translatorLib;
open cheshireCircuitTheory i2cCircuitStateTheory;
open i2cRegsCircuitLib;

val _ = new_theory "i2cRegsCircuitProof";

Definition i2c_reg_top_comb_1_def:
  i2c_reg_top_comb_1 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_1_tm
End

Definition i2c_reg_top_comb_2_def:
  i2c_reg_top_comb_2 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_2_tm
End

Definition i2c_reg_top_ff_def:
  i2c_reg_top_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_ff_tm
End

val init_tm = add_x_inits ``
  <|
    regs := ^i2c_regs_init_tm;
    reg2hw := ^i2c_reg2hw_init_tm;
  |>
``;

Definition i2c_circuit_init_def:
  i2c_circuit_init fbits = ^init_tm
End

Definition i2c_circuit_def:
  i2c_circuit = mk_module (procs [i2c_reg_top_ff]) (procs [i2c_reg_top_comb_1; i2c_reg_top_comb_2]) i2c_circuit_init
End

Theorem i2c_reg_top_correct:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    oracle_res = if ~req.valid then
      INR (I, NONE, NONE)
    else if req.write then
      SUM_MAP (\(st_upd, notif). (st_upd, notif, NONE)) I (i2c_write st nb (w2n req.addr) req.wdata)
    else
      SUM_MAP (\(notif, rdata). (I, notif, rdata)) I (i2c_read st nb (w2n req.addr));
    rsp = reg_rsp_decode (i2c fext fbits (SUC n)).reg_rsp_o;
  in
  (!proc fext s s'. proc IN set (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.reg_rsp_o = s'.reg_rsp_o)
  /\ (!st fext fbits n notif. i2c_state_rel st (i2c fext fbits n)
    (* TODO: the other way to do this would be to compare notif to
     * (i2c_reg_top_comb_1 (fext n) (i2c fext fbits n) (i2c fext fbits n)).reg2hw;
     * that has the advantage of being closer to what i2c_core actually operates
     * on, but is also uglier.
     *
     * So, we can try switching to that if this way turns out to be annoying. *)
    /\ i2c_hwext_notif_rel notif (reg_req_decode (fext n).reg_req_i)
    ==> ?fnums. i2c_core_state_rel (i2c_tick notif (st with fnums := fnums)) (i2c fext fbits (SUC n)))
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ (!i. word_bit i req.wstrb <=> i < nb)
  ==> rsp.ready
    /\ rsp.error = ISR oracle_res
    /\ (?st_upd notif rdata. oracle_res = INR (st_upd, notif, rdata)
      ==> (?fnums. i2c_state_rel (st_upd (i2c_tick notif (st with fnums := fnums))) (i2c fext fbits (SUC n)))
        /\ (!value. rdata = SOME value ==> rsp.rdata = value))
Proof
QED

val _ = export_theory ();
