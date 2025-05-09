open HolKernel Parse boolLib bossLib;
open BasicProvers wordsLib;
open wordsTheory;
open translatorTheory;
open cheshireCircuitTheory cheshireOracleTheory i2cCircuitTheory i2cCircuitStateTheory i2cCoreTheory i2cMappingsTheory i2cRegsTheory i2cRegsCommTheory;

val _ = new_theory "i2cRegsCircuitProof";

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
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req ==>
  ISL (i2c_write st nb offset wdata) = i2c_req_error req
Proof
  simp [cheshire_req_rel_write]
  >> rpt strip_tac
  >> asm_simp_tac std_ss [i2c_write_def, dimword_def, dimindex_7, w2n_eq_iff_eq_n2w]
  >> rpt TOP_CASE_TAC
  >> simp [i2c_req_error_def]
  (* We need to re-evaluate this every time so that Once doesn't mark itself as
   * used after the first subgoal and fail to apply these to any of the others. *)
  >> goal_term (fn _ => pure_rewrite_tac (map Once all_ones_rewrites))
  >> dep_rewrite.DEP_REWRITE_TAC [GSYM nb_wstrb]
  >> simp []
QED

Theorem i2c_req_error_i2c_read:
  cheshire_req_rel (SOME (nb, offset, NONE)) req ==>
  ISL (i2c_read st nb offset) = i2c_req_error req
Proof
  simp [cheshire_req_rel_read]
  >> rpt strip_tac
  >> simp [i2c_read_def, w2n_eq_iff_eq_n2w]
  >> rpt IF_CASES_TAC
  >> simp [i2c_req_error_def]
QED

Theorem cheshire_req_i2c_req_error:
  cheshire_req_rel req_m req_c
  ==> ISL (cheshire_req i2c_read i2c_write st req_m) = i2c_req_error req_c
Proof
  rpt strip_tac
  >> simp [cheshire_req_def]
  >> rpt TOP_CASE_TAC
  >- fs [cheshire_req_rel_def, i2c_req_error_def]
  >- simp [ISL_SUM_MAP, i2c_req_error_i2c_read]
  >- simp [ISL_SUM_MAP, i2c_req_error_i2c_write]
QED

Theorem i2c_reg_top_rsp_ready_error_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    rsp = reg_rsp_decode (i2c fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  ==> rsp.ready /\ rsp.error = i2c_req_error req
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def]
  >> unabbrev_all_tac
  >> simp [procs_append, procs_def, i2c_reg_top_comb_2_flat]
  >> simp [procs_unchanged, i2c_reg_top_comb_1_flat, reg_rsp_decode_def, word_bit_bit_field_insert, word_bit_def, FCP_APPLY_UPDATE_THM_2]
QED

Theorem i2c_reg_top_rsp_ready_error = SRULE [SF boolSimps.LET_ss] i2c_reg_top_rsp_ready_error_inner;

Theorem i2c_reg_top_rsp_correct_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    oracle_res = cheshire_req i2c_read i2c_write st req_m;
    rsp = reg_rsp_decode (i2c fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ cheshire_req_rel req_m req_c
  ==> rsp.ready
    /\ rsp.error = ISL oracle_res
    /\ (!st_upd notif rdata. oracle_res = INR (st_upd, notif, SOME rdata) ==> rsp.rdata = rdata)
Proof
  simp []
  >> qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (i2c_reg_top_comb_1::_)`
  >> rpt strip_tac
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> unabbrev_all_tac
  >> drule_then assume_tac i2c_reg_top_rsp_ready_error
  >> simp []
  (* error *)
  >- simp [cheshire_req_i2c_req_error]
  (* rdata *)
  >- (fs [mk_module_def, procs_def, procs_append, reg_rsp_decode_def]
      >> drule_then strip_assume_tac cheshire_req_INR_cases
      >- fs []
      >- (dep_rewrite.DEP_REWRITE_TAC [i2c_reg_top_comb_2_i2c_read]
          >> `!fext s s'. (i2c_reg_top_comb_1 fext s s').regs = s'.regs` by simp [i2c_reg_top_comb_1_flat]
          >> `!fext s s'. (i2c_reg_top_comb_2 fext s s').regs = s'.regs` by simp [i2c_reg_top_comb_2_flat]
          >> `st.regs = (i2c_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s'))).regs` by fs [i2c_state_rel_def, i2c_core_state_rel_def]
          >> rfs [procs_unchanged]
          >> `!fext s s'. (i2c_reg_top_comb_2 fext s s').hw2reg = s'.hw2reg` by simp [i2c_reg_top_comb_2_flat]
          >> `i2c_hwext_read_rel st (i2c_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s'))).hw2reg` by fs [i2c_state_rel_def, i2c_core_state_rel_def]
          >> gs [cheshire_req_rel_read]
          >> simp [i2c_reg_top_comb_1_flat, cheshire_req_def])
      >- fs [])
QED

Theorem i2c_reg_top_rsp_correct = SRULE [SF boolSimps.LET_ss] i2c_reg_top_rsp_correct_inner;

Theorem i2c_write_i2c_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req /\
  i2c_write st nb offset wdata = INR (_, notif) ==>
  i2c_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_write]
  >> pure_rewrite_tac [i2c_write_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> fs [i2c_hwext_notif_rel_def, i2c_req_error_def, w2n_eq_iff_eq_n2w]
  >> goal_term (fn _ => pure_rewrite_tac (map Once all_ones_rewrites))
  >> dep_rewrite.DEP_REWRITE_TAC [GSYM nb_wstrb]
  >> simp []
  >> first_x_assum (assume_tac o GSYM)
  >> simp []
QED

Theorem i2c_read_i2c_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, NONE)) req /\
  i2c_read st nb offset = INR (notif, _) ==>
  i2c_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_read]
  >> pure_rewrite_tac [i2c_read_def]
  >> rpt TOP_CASE_TAC
  >> fs [i2c_hwext_notif_rel_def, i2c_req_error_def, w2n_eq_iff_eq_n2w]
QED

Theorem i2c_req_fext_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    s' = i2c fext fbits n;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  ==> s'.addr = req.addr /\ s'.write = req.write /\ s'.wdata = req.wdata
    /\ s'.wstrb = req.wstrb /\ s'.valid = req.valid
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def]
  >> unabbrev_all_tac
  >> simp [procs_append, procs_def, i2c_reg_top_comb_2_flat]
  >> simp [procs_unchanged, i2c_reg_top_comb_1_flat]
QED

Theorem i2c_req_fext = SRULE [SF boolSimps.LET_ss] i2c_req_fext_inner;

Theorem i2c_reg_top_i2c_state_rel_step_inner:
  !ffs1 ffs2 combs fext fbits n st req_m st_upd notif rdata.
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  (* Not strictly a requirement, but makes this easier to state (we don't have to
   * add an i2c_reg_top_ff into the i2c_hw_write_rel condition).
   *
   * Besides, blocking synchronous writes are bad practice anyway. (They're forced
   * to be blocking by the fact we reference them as s'.hw2reg - it's an annoying
   * limitation that you have to know whether something's combinationally or
   * synchronously assigned when using it...) *)
  /\ (!proc fext s s'. MEM proc ffs1 ==> (proc fext s s').hw2reg = s'.hw2reg)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req
    in
    i2c_state_rel st (i2c fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
    (* TODO: the other way to do this would be to compare notif to
     * (i2c_reg_top_comb_1 (fext n) (i2c fext fbits n) (i2c fext fbits n)).reg2hw;
     * that has the advantage of being closer to what i2c_core actually operates
     * on, but is also uglier.
     *
     * So, we can try switching to that if this way turns out to be annoying. *)
    /\ i2c_hwext_notif_rel notif req_c
    (* Note: somewhat counterintuitively, this actually shows that
     * i2c_hwext_read_rel is true for the next clock cycle, not this one. *)
    ==> ?fnums. i2c_core_state_rel (st_upd (i2c_tick notif (st with fnums := fnums))) (i2c fext fbits (SUC n))
      (* Note: this is only true because st_upd hasn't run yet, otherwise software
       * might have overwritten some stuff and made this false. *)
      /\ i2c_hw_write_rel (st with fnums := fnums).regs (i2c_tick notif (st with fnums := fnums)).regs
                          (i2c fext fbits n).hw2reg)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
  ==> ?fnums. i2c_state_rel (st_upd (i2c_tick notif (st with fnums := fnums))) (i2c fext fbits (SUC n))
Proof
  simp []
  >> rpt strip_tac

  >> drule_all_then strip_assume_tac i2c_reg_top_rsp_correct
  >> drule_then assume_tac i2c_req_fext
  >> drule_then assume_tac i2c_reg_top_rsp_ready_error

  >> qabbrev_tac `req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req`

  >> `i2c_hwext_notif_rel notif req_c`
     by (drule_then strip_assume_tac cheshire_req_INR_cases
         >- fs [cheshire_req_rel_def, i2c_hwext_notif_rel_def, i2c_req_error_def]
         >- (fs [] >> drule_all i2c_read_i2c_hwext_notif_rel >> simp [])
         >- (fs [] >> drule_all i2c_write_i2c_hwext_notif_rel >> simp []))

  (* We need to do this in all cases so we can pick the value of fnums. *)
  >> fs [Abbr `req_c`]
  >> qpat_x_assum `!st nb fext fbits n st_upd notif rdata. _ ==> ?fnums. _`
       $ drule_all_then strip_assume_tac
  >> qabbrev_tac `req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req`
  >> qexists `fnums`

  >> simp [i2c_state_rel_def]
  >> rpt strip_tac

  (* regs *)
  >- (simp [mk_module_def, mk_circuit_def, procs_def, procs_append, i2c_reg_top_comb_2_flat]
      >> simp [procs_unchanged, i2c_reg_top_comb_1_flat]

      >> drule_then strip_assume_tac cheshire_req_INR_st_upd_cases

      >> simp [GSYM mk_module_def]
      >> qpat_abbrev_tac `i2c = mk_module _ _ _`

      >- (drule_then (fn thm => full_simp_tac pure_ss [thm]) cheshire_req_rel_valid_write
          >> simp [i2c_reg_top_ff_flat, procs_unchanged]
          (* TODO: auto-generate this (probably need to make a new *Lib.sml to put it in...) *)
          >> simp [i2c_regs_component_equality, i2c_intr_state_component_equality, i2c_intr_enable_component_equality, i2c_ctrl_component_equality, i2c_fdata_component_equality, i2c_fifo_ctrl_component_equality, i2c_ovrd_component_equality, i2c_timing0_component_equality, i2c_timing1_component_equality, i2c_timing2_component_equality, i2c_timing3_component_equality, i2c_timing4_component_equality, i2c_timeout_ctrl_component_equality, i2c_target_id_component_equality, i2c_txdata_component_equality, i2c_host_timeout_ctrl_component_equality]
          >> gs [i2c_state_rel_def, i2c_tick_hwro_unchanged, i2c_hw_write_rel_def])
      >- (fs [cheshire_req_rel_write]
          >> drule i2c_write_st_upd_alt
          >> simp [i2c_reg_top_ff_flat, procs_unchanged]
          >> fs [i2c_state_rel_def, i2c_tick_hwro_unchanged, i2c_hw_write_rel_def, reg_rsp_decode_def, w2n_eq_iff_eq_n2w]))
  (* buffered_notif *)
  >- (simp [mk_module_def, mk_circuit_def, procs_def, procs_append, i2c_reg_top_comb_2_flat]
      >> simp [procs_unchanged, i2c_reg_top_comb_1_flat]
      >> simp [i2c_notif_rel_def]
      >> simp [i2c_reg_top_ff_flat, procs_unchanged, GSYM mk_module_def]
      >> fs [reg_rsp_decode_def]

      >> drule_then strip_assume_tac cheshire_req_INR_st_upd_cases

      >- (drule_then (fn thm => full_simp_tac pure_ss [thm]) cheshire_req_rel_valid_write
          >> simp [i2c_tick_buffered_notif_NONE])
      >- (fs [cheshire_req_rel_write]
          >> drule i2c_write_st_upd_alt
          >> simp []
          >> rpt (IF_CASES_TAC >- fs [w2n_eq_iff_eq_n2w])
          >> fs [i2c_tick_buffered_notif_NONE, w2n_eq_iff_eq_n2w]))
QED

Theorem i2c_reg_top_i2c_state_rel_step = SRULE [SF boolSimps.LET_ss] i2c_reg_top_i2c_state_rel_step_inner;

Theorem i2c_read_fnums:
  !st nb offset fnums. i2c_read (st with fnums := fnums) nb offset = i2c_read st nb offset
Proof
  asm_simp_tac std_ss [i2c_read_def]
  >> asm_simp_tac std_ss [i2c_get_status_fmtfull_def, i2c_get_status_rxfull_def, i2c_get_status_fmtempty_def, i2c_get_status_hostidle_def, i2c_get_status_targetidle_def, i2c_get_status_rxempty_def, i2c_get_status_txfull_def, i2c_get_status_acqfull_def, i2c_get_status_txempty_def, i2c_get_status_acqempty_def, i2c_get_rdata_rdata_def, i2c_get_fifo_status_fmtlvl_def, i2c_get_fifo_status_txlvl_def, i2c_get_fifo_status_rxlvl_def, i2c_get_fifo_status_acqlvl_def, i2c_get_val_scl_rx_def, i2c_get_val_sda_rx_def, i2c_get_acqdata_abyte_def, i2c_get_acqdata_signal_def]
  >> asm_simp_tac std_ss [i2c_state_accfupds]
QED

Theorem i2c_write_fnums:
  !st nb offset fnums wdata. i2c_write (st with fnums := fnums) nb offset wdata = i2c_write st nb offset wdata
Proof
  asm_simp_tac std_ss [i2c_write_def, i2c_state_accfupds]
QED

Theorem i2c_cheshire_req_fnums:
  !st valid write nb offset wdata fnums.
  cheshire_req i2c_read i2c_write (st with fnums := fnums) req =
  cheshire_req i2c_read i2c_write st req
Proof
  simp [cheshire_req_def, i2c_read_fnums, i2c_write_fnums]
QED

Theorem i2c_st_upd_unused_fnums:
  !st valid write nb offset wdata st_upd notif rdata st'.
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  unused_fnums_ignored st_upd st'
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac cheshire_req_INR_cases
  >> simp [unused_fnums_ignored_def]
  >> qexists `0`
  >- simp [SF ETA_ss]
  >- simp [SF ETA_ss]
  >- (drule i2c_write_st_upd_alt >> simp [SF ETA_ss])
QED

Theorem OUTR_SUM_MAP:
  !f g z. ISR z ==> OUTR (SUM_MAP f g z) = g (OUTR z)
Proof
  Cases_on `z` >> simp []
QED

Theorem cheshire_run_unused_fnums:
  !reqs st.
  (!st req. MEM req reqs ==> ISR (cheshire_req i2c_read i2c_write st req)) ==>
  unused_fnums_ignored (\st. FST (OUTR (cheshire_run i2c_tick i2c_read i2c_write st reqs))) st
Proof
  Induct_on `reqs`
  >- (simp [unused_fnums_ignored_def]
      >> rpt strip_tac
      >> qexists `0`
      >> simp [cheshire_run_def, SF ETA_ss])
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> `?oracle_res. cheshire_req i2c_read i2c_write st h = INR oracle_res` by simp [GSYM sumExtraTheory.ISR_exists]
      >> `!st'. (?fnums. st' = st with fnums := fnums) ==> cheshire_req i2c_read i2c_write st' h = INR oracle_res`
         by (rpt strip_tac >> simp [i2c_cheshire_req_fnums])
      >> PairCases_on `oracle_res`
      >> simp [Cong unused_fnums_ignored_cong]
      >> `(λst'. FST (OUTR (SUM_MAP I (I ## CONS oracle_res2)
            (cheshire_run i2c_tick i2c_read i2c_write (oracle_res0 (i2c_tick oracle_res1 st')) reqs)))) =
          (λst'. FST (OUTR (SUM_MAP I (I ## CONS oracle_res2)
            (cheshire_run i2c_tick i2c_read i2c_write st' reqs))))
          o oracle_res0
          o i2c_tick oracle_res1` by simp [combinTheory.o_DEF]
      >> simp []
      >> rpt (irule unused_fnums_ignored_comp >> rpt strip_tac)
      >- simp [cheshire_run_cheshire_req_ISR, OUTR_SUM_MAP]
      >- (drule i2c_st_upd_unused_fnums >> simp [])
      >- simp [i2c_tick_unused_fnums])
QED

Theorem i2c_st_upd_fnums_fupd:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  st_upd (st' with fnums := fnums) = st_upd st' with fnums := fnums
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac cheshire_req_INR_cases
  >- simp []
  >- simp []
  >- (drule i2c_write_st_upd_alt >> simp [])
QED

Theorem i2c_st_upd_fnums:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  (st_upd st').fnums = st'.fnums
Proof
  rpt strip_tac
  >> dxrule_then (qspecl_then [`st'`, `st'.fnums`] assume_tac) i2c_st_upd_fnums_fupd
  >> `!st. st with fnums := st.fnums = st` by simp [i2c_state_component_equality]
  >> fs []
  >> last_x_assum (fn thm => simp [Once thm])
QED

Theorem cheshire_run_unused_fnums_2:
  !reqs st.
  (!st req. MEM req reqs ==> ISR (cheshire_req i2c_read i2c_write st req)) ==>
  ?n st' rdatas. !fnums. (!i. i < n ==> fnums i = st.fnums i) ==>
  cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs = INR (st' with fnums := (\i. fnums (i + n)), rdatas)
Proof
  Induct_on `reqs`
  >- (rpt strip_tac
      >> qexistsl [`0`, `st`, `[]`]
      >> simp [cheshire_run_def, SF ETA_ss])
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> `?oracle_res. cheshire_req i2c_read i2c_write st h = INR oracle_res` by simp [GSYM sumExtraTheory.ISR_exists]
      >> PairCases_on `oracle_res`
      >> fs [i2c_cheshire_req_fnums]

      >> qspecl_then [`oracle_res1`, `st`] assume_tac i2c_tick_unused_fnums
      >> fs [unused_fnums_ignored_def]
      >> qrefine `n + m`
      >> simp []
      >> drule_then assume_tac i2c_st_upd_fnums_fupd
      >> simp []
      >> last_x_assum $ qspec_then `oracle_res0 (i2c_tick oracle_res1 st)` strip_assume_tac
      >> qexists `n'`
      >> drule_then assume_tac unused_fnums_ignored_fnums_val_inner
      >> drule_then assume_tac i2c_st_upd_fnums
      >> fs []
      >> qexistsl [`st'`, `oracle_res2::rdatas`]
      >> simp [])
QED

(* If the initial model state lines up with `i2c_circuit_init`, and all the
 * requests in `fext` are valid, then the two states will stay lined up from
 * that point onwards. *)
Theorem i2c_reg_top_correct:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid)
  /\ (!proc fext s s'. MEM proc ffs1 ==> (proc fext s s').hw2reg = s'.hw2reg)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req
    in
    i2c_state_rel st (i2c fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
    /\ i2c_hwext_notif_rel notif req_c
    ==> ?fnums. i2c_core_state_rel (st_upd (i2c_tick notif (st with fnums := fnums))) (i2c fext fbits (SUC n))
      /\ i2c_hw_write_rel (st with fnums := fnums).regs (i2c_tick notif (st with fnums := fnums)).regs
                          (i2c fext fbits n).hw2reg)

  (* We phrase it this way instead of as i2c_circuit_init fbits so that
   * combinational signals are set instead of being random values from fbits. *)
  /\ i2c_state_rel st (i2c fext fbits 0)
  /\ (!i. i < LENGTH reqs ==>
    let
      req = reg_req_decode (fext i).reg_req_i: 7 reg_req;
    in
      ~i2c_req_error req /\ cheshire_req_rel (EL i reqs) req)

  ==> ?fnums. let
      (st', rdatas) = OUTR (cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs)
    in
    i2c_state_rel st' (i2c fext fbits (LENGTH reqs))
    /\ (!i. i < LENGTH reqs ==>
      let
        rsp = reg_rsp_decode (i2c fext fbits i).reg_rsp_o;
      in
        rsp.ready /\ ~rsp.error /\ (!value. EL i rdatas = SOME value ==> rsp.rdata = value))
Proof
  simp []
  >> rpt strip_tac
  >> Induct_on `reqs` using listTheory.SNOC_INDUCT
  >- (drule i2c_reg_top_rsp_ready_error >> fs [cheshire_run_def, i2c_state_rel_fnums])
  >- (rpt strip_tac

      (* Satisfy the assumptions for our inductive hypothesis, which will tell us the
       * `fnums` used by `cheshire_run` up until this point. *)
      >> `!f n. (!i. i < SUC n ==> f i) <=> (!i. i < n ==> f i) /\ f n`
         by (rpt strip_tac
             >> iff_tac
             >- simp []
             >- (rpt strip_tac >> Cases_on `i = n` >> simp []))
      >> fs [listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC]

      (* Show that `cheshire_run = INR _`. *)
      >> `!st req. MEM req reqs ==> ISR (cheshire_req i2c_read i2c_write st req)`
         by (simp [listTheory.MEM_EL]
             >> rpt strip_tac
             >> qpat_x_assum `!i. i < LENGTH reqs ==> _` $ drule_then strip_assume_tac
             >> drule cheshire_req_i2c_req_error
             >> simp [Excl "NOT_ISL_ISR", GSYM sumTheory.NOT_ISL_ISR])
      >> drule_then (qspecl_then [`i2c_tick`, `st with fnums := fnums`] assume_tac) cheshire_run_cheshire_req_ISR
      >> drule_then strip_assume_tac (iffLR sumExtraTheory.ISR_exists)
      >> fs []
      >> pairarg_tac
      >> fs []

      (* Infer from `~i2c_req_error` that `cheshire_req = INR _`, so that it can be
       * used by `drule_all i2c_reg_top_i2c_state_rel_step`. *)
      >> drule_all_then strip_assume_tac i2c_reg_top_rsp_correct
      >> drule_then assume_tac i2c_reg_top_rsp_ready_error
      >> gs []
      >> drule_then (qx_choose_then `oracle_res` assume_tac) (iffLR sumExtraTheory.ISR_exists)
      >> PairCases_on `oracle_res`
      >> drule_all_then strip_assume_tac i2c_reg_top_i2c_state_rel_step

      (* Now we have `fnums'`, the `fnums` needed for the last step to keep things
       * lining up, and we want to use `qexists` with `fnums'` glued onto the end of
       * `fnums`. But first, we need to find out where that end is. *)
      >> `!st req. MEM req reqs ==> ISR (cheshire_req i2c_read i2c_write st req)`
         by (simp [listTheory.MEM_EL]
             >> rpt strip_tac
             >> qpat_x_assum `!i. i < LENGTH reqs ==> _` $ drule_then strip_assume_tac
             >> drule cheshire_req_i2c_req_error
             >> simp [Excl "NOT_ISL_ISR", GSYM sumTheory.NOT_ISL_ISR])
      >> drule_then (qspec_then `st with fnums := fnums` strip_assume_tac) cheshire_run_unused_fnums_2
      >> qexists `\i. if i < n then fnums i else fnums' (i - n)`

      >> first_assum $ qspec_then `\i. if i < n then fnums i else fnums' (i - n)` assume_tac
      (* Instantiate it a second time to prove that st'' = st'. *)
      >> first_x_assum $ qspec_then `fnums` assume_tac
      >> gs [cheshire_run_SNOC, i2c_cheshire_req_fnums]
      >> drule_then assume_tac cheshire_run_LENGTH_rdatas
      >> first_x_assum (assume_tac o GSYM)
      >> fs [i2c_cheshire_req_fnums, SF ETA_ss, listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC])
QED

val _ = export_theory ();
