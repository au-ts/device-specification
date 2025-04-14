open HolKernel Parse boolLib bossLib;
open translatorLib;
open cheshireCircuitTheory i2cCircuitStateTheory;
open i2cRegsCircuitLib i2cMappingsTheory;

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

Theorem procs_append:
  ∀ps qs fext s s'. procs (ps ++ qs) fext s s' = procs qs fext s (procs ps fext s s')
Proof
  Induct_on `ps`
  >> simp [procs_def]
QED

Theorem procs_unchanged:
  !f ps fext s s'.
  (!p fext s s'. MEM p ps ⇒ f (p fext s s') = f s') ==>
  f (procs ps fext s s') = f s'
Proof
  Induct_on `ps`
  >> simp [procs_def]
QED

Theorem COND_ARG1:
  (if c then f g x else f h x) = f (if c then g else h) x
Proof
  simp [COND_RAND, COND_RATOR]
QED

Theorem COND_ARG1_K:
  (if c then f (K a) x else f (K b) x) = f (K (if c then a else b)) x
Proof
  simp [COND_ARG1, GSYM COND_RAND, GSYM COND_RATOR]
QED

Theorem i2c_reg_top_comb_1_flat = i2c_reg_top_comb_1_def
  |> SRULE [COND_ARG1_K, COND_ARG1]
  |> SRULE [Ntimes LET_THM 5]
  |> SRULE [SRULE [] (GSYM i2c_req_error_alt), SF boolSimps.LET_ss];

Theorem i2c_reg_top_comb_2_flat = SRULE [COND_ARG1_K, COND_ARG1] i2c_reg_top_comb_2_def;

Theorem i2c_reg_top_ff_flat = i2c_reg_top_ff_def
  |> SRULE [COND_ARG1_K]
  |> SRULE [SF boolSimps.LET_ss];

Theorem word_bits_bit_field_insert:
  h < dimindex (:'a) ∧ dimindex (:'b) = h + 1 - l ⇒
  (h -- l) (bit_field_insert h l (v: 'b word) (w: 'a word)) = w2w v
Proof
  rpt strip_tac
  >> asm_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [word_bits_def, bit_field_insert_def, word_modify_def, Cong AND_CONG, w2w]
  >> rpt strip_tac
  >> ‘i < h + 1 − l ⇔ i + l < h + 1’ by (fs [] >> simp [DIMINDEX_GT_0])
  >> simp [arithmeticTheory.LE_LT1]
QED

Theorem word_extract_bit_field_insert:
  h < dimindex (:'a) ∧ dimindex (:'b) = h + 1 - l ⇒
  (h >< l) (bit_field_insert h l (v: 'b word) (w: 'a word)) = v
Proof
  simp [word_extract_def, word_bits_bit_field_insert, w2w_w2w, WORD_ALL_BITS]
QED

Theorem eq_w2n_iff_eq_n2w:
  !(w: 'a word) n. n < dimword (:'a) ==> (n = w2n w <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >> simp []
QED

Theorem w2n_eq_iff_eq_n2w:
  !(w: 'a word) n. n < dimword (:'a) ==> (w2n w = n <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >- (strip_tac
      >> first_x_assum (assume_tac o GSYM)
      >> simp [eq_w2n_iff_eq_n2w])
  >- simp []
QED

Theorem i2c_reg_top_comb_2_i2c_read:
  st.regs = s.regs ∧ i2c_hwext_read_rel st s'.hw2reg ⇒
  (33 >< 2) (i2c_reg_top_comb_2 fext s s').reg_rsp_o =
  case i2c_read st nb (w2n s'.addr) of
    INL _ => 0xFFFFFFFFw
  | INR (_, value) => value
Proof
  simp [i2c_hwext_read_rel_def, i2c_reg_top_comb_2_flat, word_extract_bit_field_insert]
  >> rpt IF_CASES_TAC
  >> simp [i2c_read_def, w2n_eq_iff_eq_n2w]
QED

Theorem mk_circuit_cstep:
  ∀sstep cstep s fext n. ∃s'. mk_circuit sstep cstep s fext n = cstep (fext n) s' s'
Proof
  rpt strip_tac
  >> Cases_on ‘n’
  >- (qexists ‘s’ >> simp [mk_circuit_def])
  >- (qexists ‘(sstep (fext n') (mk_circuit sstep cstep s fext n')
                      (mk_circuit sstep cstep s fext n'))’
      >> simp [mk_circuit_def])
QED

Theorem word_bit_bit_field_insert:
  i < l \/ h < i ==> word_bit i (bit_field_insert h l a b) = word_bit i b
Proof
  asm_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [word_bit_def, bit_field_insert_def, word_modify_def, arithmeticTheory.SUB_LESS_OR_EQ, Cong AND_CONG]
QED

(* For some reason `simp` vehemently refuses to use the original `FCP_APPLY_UPDATE_THM`. *)
Theorem FCP_APPLY_UPDATE_THM_2:
  !(m: 'a['b]) a w b. b < dimindex (:'b) ==> (a :+ w) m ' b = if a = b then w else m ' b
Proof
  assume_tac fcpTheory.FCP_APPLY_UPDATE_THM >> simp []
QED

Theorem ISL_SUM_MAP:
  !f g z. ISL (SUM_MAP f g z) = ISL z
Proof
  Cases_on `z` >> simp []
QED

Theorem nb_wstrb:
  !(wstrb: word4) nb n.
  (!i. word_bit i wstrb <=> i < nb) /\ n + 1 = dimindex (:'b) ==>
  (nb > n <=> ((n >< 0) wstrb: 'b word) = -1w)
Proof
  rpt strip_tac
  >> full_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [arithmeticTheory.GREATER_DEF, word_bit_def, word_extract_def, WORD_NEG_1_T, w2w, word_bits_def, Cong AND_CONG, arithmeticTheory.LE_LT1]
  >> iff_tac
  >> simp []
QED

val all_ones_rewrites = map (fn n => ``-1w: ^(n |> Arbnum.fromInt |> fcpLib.index_type |> ty_antiq) word`` |> EVAL |> GSYM |> Once) [1, 2, 3, 4];

Theorem i2c_req_error_i2c_write:
  !(req: 7 reg_req) st nb.
  req.valid /\ req.write /\ (∀i. word_bit i req.wstrb ⇔ i < nb) ==>
  i2c_req_error req = ISL (i2c_write st nb (w2n req.addr) req.wdata)
Proof
  rpt strip_tac
  >> asm_simp_tac std_ss [i2c_write_def, dimword_def, dimindex_7, w2n_eq_iff_eq_n2w]
  >> rpt TOP_CASE_TAC
  >> (simp [i2c_req_error_def]
      (* We need to re-evaluate this every time so that Once doesn't mark itself as
       * used after the first subgoal and fail to apply these to any of the others. *)
      >> goal_term (fn _ => pure_rewrite_tac (map Once all_ones_rewrites))
      >> dep_rewrite.DEP_REWRITE_TAC [GSYM nb_wstrb]
      >> simp [])
QED

Theorem i2c_req_error_i2c_read:
  !(req: 7 reg_req) st nb.
  req.valid /\ ~req.write ==>
  i2c_req_error req = ISL (i2c_read st nb (w2n req.addr))
Proof
  rpt strip_tac
  >> simp [i2c_read_def, w2n_eq_iff_eq_n2w]
  >> rpt IF_CASES_TAC
  >> simp [i2c_req_error_def]
QED

Theorem i2c_reg_top_rsp_correct:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    oracle_res = if ~req.valid then
      INR (I, NONE, NONE)
    else if req.write then
      SUM_MAP I (\(st_upd, notif). (st_upd, notif, NONE)) (i2c_write st nb (w2n req.addr) req.wdata)
    else
      SUM_MAP I (\(notif, rdata). (I, notif, SOME rdata)) (i2c_read st nb (w2n req.addr));
    rsp = reg_rsp_decode (i2c fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc combs ==>
    let
      s'' = proc fext s s'
    in
      s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ (!i. word_bit i req.wstrb <=> i < nb)
  ==> rsp.ready
    /\ rsp.error = ISL oracle_res
    /\ (!st_upd notif rdata. oracle_res = INR (st_upd, notif, SOME rdata) ==> rsp.rdata = rdata)
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> simp []
  >> rpt strip_tac
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> unabbrev_all_tac
  >> fs [mk_module_def, procs_def, procs_append, reg_rsp_decode_def]
  (* ready *)
  >- (simp [i2c_reg_top_comb_2_flat, word_bit_bit_field_insert]
      >> simp [procs_unchanged, i2c_reg_top_comb_1_flat, word_bit_def, FCP_APPLY_UPDATE_THM_2])
  (* error *)
  >- (simp [i2c_reg_top_comb_2_flat, word_bit_bit_field_insert]
      >> simp [procs_unchanged, i2c_reg_top_comb_1_flat, word_bit_def, FCP_APPLY_UPDATE_THM_2]
      >> rpt IF_CASES_TAC
      >- simp [i2c_req_error_def]
      >- fs [ISL_SUM_MAP, i2c_req_error_i2c_write]
      >- fs [ISL_SUM_MAP, i2c_req_error_i2c_read])
  (* rdata *)
  >- (dep_rewrite.DEP_REWRITE_TAC [i2c_reg_top_comb_2_i2c_read]
      >> `!fext s s'. (i2c_reg_top_comb_1 fext s s').regs = s'.regs` by simp [i2c_reg_top_comb_1_flat]
      >> `!fext s s'. (i2c_reg_top_comb_2 fext s s').regs = s'.regs` by simp [i2c_reg_top_comb_2_flat]
      >> `st.regs = (i2c_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s'))).regs` by fs [i2c_state_rel_def, i2c_core_state_rel_def]
      >> rfs [procs_unchanged]
      >> `!fext s s'. (i2c_reg_top_comb_2 fext s s').hw2reg = s'.hw2reg` by simp [i2c_reg_top_comb_2_flat]
      >> `i2c_hwext_read_rel st (i2c_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s'))).hw2reg` by fs [i2c_state_rel_def, i2c_core_state_rel_def]
      >> rfs []
      >> `(reg_req_decode (fext n).reg_req_i: 7 reg_req).valid` by (spose_not_then assume_tac >> fs [])
      >> `~(reg_req_decode (fext n).reg_req_i: 7 reg_req).write`
         by (spose_not_then assume_tac
             >> Cases_on `i2c_write st nb (w2n (reg_req_decode (fext n).reg_req_i: 7 reg_req).addr) (reg_req_decode (fext n).reg_req_i: 7 reg_req).wdata`
             >> fs [sumTheory.SUM_MAP_def]
             >> Cases_on `y`
             >> fs [])
      >> Cases_on `i2c_read st nb (w2n (reg_req_decode (fext n).reg_req_i: 7 reg_req).addr)`
      >- fs []
      >- (Cases_on `y`
          >> fs []
          >> simp [i2c_reg_top_comb_1_flat]))
QED

Theorem i2c_reg_top_i2c_state_rel_step:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    oracle_res = if ~req.valid then
      INR (I, NONE, NONE)
    else if req.write then
      SUM_MAP I (\(st_upd, notif). (st_upd, notif, NONE)) (i2c_write st nb (w2n req.addr) req.wdata)
    else
      SUM_MAP I (\(notif, rdata). (I, notif, SOME rdata)) (i2c_read st nb (w2n req.addr));
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==> (proc fext s s').reg2hw = s'.reg2hw)
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
  /\ oracle_res = INR (st_upd, notif, rdata)
  ==> ?fnums. i2c_state_rel (st_upd (i2c_tick notif (st with fnums := fnums))) (i2c fext fbits (SUC n))
Proof
  cheat
QED

val _ = export_theory ();
