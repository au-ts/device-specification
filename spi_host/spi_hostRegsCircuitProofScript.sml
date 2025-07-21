open HolKernel Parse boolLib bossLib;
open BasicProvers wordsLib;
open wordsTheory;
open translatorTheory;
open cheshireCircuitTheory cheshireOracleTheory spi_hostCircuitTheory spi_hostCircuitStateTheory spi_hostCoreTheory spi_hostMappingsTheory spi_hostRegsTheory spi_hostRegsCommTheory;

val _ = new_theory "spi_hostRegsCircuitProof";

Theorem procs_append:
  procs (ps ++ qs) fext s s' = procs qs fext s (procs ps fext s s')
Proof
  qid_spec_tac `s'`
  >> Induct_on `ps`
  >> simp [procs_def]
QED

Theorem procs_unchanged:
  (!p fext s s'. MEM p ps ⇒ f (p fext s s') = f s') ==>
  f (procs ps fext s s') = f s'
Proof
  qid_spec_tac `s'`
  >> Induct_on `ps`
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

Theorem spi_host_reg_top_comb_1_flat = spi_host_reg_top_comb_1_def
  |> SRULE [COND_ARG1_K, COND_ARG1]
  |> SRULE [Ntimes LET_THM 5]
  |> SRULE [SRULE [] (GSYM spi_host_req_error_alt), SF boolSimps.LET_ss];

Theorem spi_host_reg_top_comb_2_flat = SRULE [COND_ARG1_K, COND_ARG1] spi_host_reg_top_comb_2_def;

Theorem spi_host_reg_top_ff_flat = spi_host_reg_top_ff_def
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
  n < dimword (:'a) ==> (n = w2n (w: 'a word) <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >> simp []
QED

Theorem w2n_eq_iff_eq_n2w:
  n < dimword (:'a) ==> (w2n (w: 'a word) = n <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >- (strip_tac
      >> first_x_assum (assume_tac o GSYM)
      >> simp [eq_w2n_iff_eq_n2w])
  >- simp []
QED

Theorem spi_host_reg_top_comb_2_spi_host_read:
  st.regs = s.regs ∧ spi_host_hwext_read_rel st s'.hw2reg ⇒
  (33 >< 2) (spi_host_reg_top_comb_2 fext s s').reg_rsp_o =
  case spi_host_read st nb (w2n s'.addr) of
    INL _ => 0xFFFFFFFFw
  | INR (_, value) => value
Proof
  simp [spi_host_hwext_read_rel_def, spi_host_reg_top_comb_2_flat, word_extract_bit_field_insert]
  >> rpt IF_CASES_TAC
  >> simp [spi_host_read_def, w2n_eq_iff_eq_n2w]
QED

Theorem mk_circuit_cstep:
  ∃s'. mk_circuit sstep cstep s fext n = cstep (fext n) s' s'
Proof
  Cases_on ‘n’
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
  b < dimindex (:'b) ==> (a :+ w) (m: 'a['b]) ' b = if a = b then w else m ' b
Proof
  assume_tac fcpTheory.FCP_APPLY_UPDATE_THM >> simp []
QED

Theorem ISL_SUM_MAP:
  ISL (SUM_MAP f g z) = ISL z
Proof
  Cases_on `z` >> simp []
QED

Theorem nb_wstrb:
  (!i. word_bit i (wstrb: word4) <=> i < nb) /\ n + 1 = dimindex (:'b) ==>
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

Theorem spi_host_req_error_spi_host_write:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req ==>
  ISL (spi_host_write st nb offset wdata) = spi_host_req_error req
Proof
  simp [cheshire_req_rel_write]
  >> rpt strip_tac
  >> asm_simp_tac std_ss [spi_host_write_def, dimword_def, dimindex_6, w2n_eq_iff_eq_n2w]
  >> rpt TOP_CASE_TAC
  >> simp [spi_host_req_error_def]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> fs [GT_GE1]
QED

Theorem spi_host_req_error_spi_host_read:
  cheshire_req_rel (SOME (nb, offset, NONE)) req ==>
  ISL (spi_host_read st nb offset) = spi_host_req_error req
Proof
  simp [cheshire_req_rel_read]
  >> rpt strip_tac
  >> simp [spi_host_read_def, w2n_eq_iff_eq_n2w]
  >> rpt IF_CASES_TAC
  >> simp [spi_host_req_error_def]
QED

Theorem cheshire_req_spi_host_req_error:
  cheshire_req_rel req_m req_c
  ==> ISL (cheshire_req spi_host_read spi_host_write st req_m) = spi_host_req_error req_c
Proof
  rpt strip_tac
  >> simp [cheshire_req_def]
  >> rpt TOP_CASE_TAC
  >- fs [cheshire_req_rel_def, spi_host_req_error_def]
  >- simp [ISL_SUM_MAP, spi_host_req_error_spi_host_read]
  >- simp [ISL_SUM_MAP, spi_host_req_error_spi_host_write]
QED

Theorem spi_host_reg_top_rsp_ready_error_inner:
  let
    spi_host = mk_module (procs (ffs1 ++ [spi_host_reg_top_ff] ++ ffs2)) (procs ([spi_host_reg_top_comb_1] ++ combs ++ [spi_host_reg_top_comb_2])) spi_host_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 6 reg_req;
    rsp = reg_rsp_decode (spi_host fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid /\ s''.error = s'.error)
  ==> rsp.ready /\ rsp.error = spi_host_req_error req
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [spi_host_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (spi_host_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def]
  >> unabbrev_all_tac
  >> simp [procs_append, procs_def, spi_host_reg_top_comb_2_flat]
  >> simp [procs_unchanged, spi_host_reg_top_comb_1_flat, reg_rsp_decode_def, word_bit_bit_field_insert, word_bit_def, FCP_APPLY_UPDATE_THM_2]
QED

Theorem spi_host_reg_top_rsp_ready_error = SRULE [SF boolSimps.LET_ss] spi_host_reg_top_rsp_ready_error_inner;

Theorem spi_host_reg_top_rsp_correct_inner:
  let
    spi_host = mk_module (procs (ffs1 ++ [spi_host_reg_top_ff] ++ ffs2)) (procs ([spi_host_reg_top_comb_1] ++ combs ++ [spi_host_reg_top_comb_2])) spi_host_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req;
    oracle_res = cheshire_req spi_host_read spi_host_write st req_m;
    rsp = reg_rsp_decode (spi_host fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid /\ s''.error = s'.error)
  /\ spi_host_state_rel st (spi_host fext fbits n)
  /\ cheshire_req_rel req_m req_c
  ==> rsp.ready
    /\ rsp.error = ISL oracle_res
    /\ (!st_upd notif rdata. oracle_res = INR (st_upd, notif, SOME rdata) ==> rsp.rdata = rdata)
Proof
  simp []
  >> qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (spi_host_reg_top_comb_1::_)`
  >> rpt strip_tac
  >> `?s'. mk_circuit sstep cstep (spi_host_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> unabbrev_all_tac
  >> drule_then assume_tac spi_host_reg_top_rsp_ready_error
  >> simp []
  (* error *)
  >- simp [cheshire_req_spi_host_req_error]
  (* rdata *)
  >- (fs [mk_module_def, procs_def, procs_append, reg_rsp_decode_def]
      >> drule_then strip_assume_tac cheshire_req_INR_cases
      >- fs []
      >- (dep_rewrite.DEP_REWRITE_TAC [spi_host_reg_top_comb_2_spi_host_read]
          >> `!fext s s'. (spi_host_reg_top_comb_1 fext s s').regs = s'.regs` by simp [spi_host_reg_top_comb_1_flat]
          >> `!fext s s'. (spi_host_reg_top_comb_2 fext s s').regs = s'.regs` by simp [spi_host_reg_top_comb_2_flat]
          >> `st.regs = (spi_host_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (spi_host_reg_top_comb_1 (fext n) s' s'))).regs` by fs [spi_host_state_rel_def, spi_host_core_state_rel_def]
          >> rfs [procs_unchanged]
          >> `!fext s s'. (spi_host_reg_top_comb_2 fext s s').hw2reg = s'.hw2reg` by simp [spi_host_reg_top_comb_2_flat]
          >> `spi_host_hwext_read_rel st (spi_host_reg_top_comb_2 (fext n) s' (procs combs (fext n) s' (spi_host_reg_top_comb_1 (fext n) s' s'))).hw2reg` by fs [spi_host_state_rel_def, spi_host_core_state_rel_def]
          >> gs [cheshire_req_rel_read]
          >> simp [spi_host_reg_top_comb_1_flat, cheshire_req_def])
      >- fs [])
QED

Theorem spi_host_reg_top_rsp_correct = SRULE [SF boolSimps.LET_ss] spi_host_reg_top_rsp_correct_inner;

Theorem spi_host_write_spi_host_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req /\
  spi_host_write st nb offset wdata = INR (_, notif) ==>
  spi_host_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_write]
  >> pure_rewrite_tac [spi_host_write_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> fs [spi_host_hwext_notif_rel_def, spi_host_req_error_def, w2n_eq_iff_eq_n2w]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> simp []
  >> first_x_assum (assume_tac o GSYM)
  >> simp []
QED

Theorem spi_host_read_spi_host_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, NONE)) req /\
  spi_host_read st nb offset = INR (notif, _) ==>
  spi_host_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_read]
  >> pure_rewrite_tac [spi_host_read_def]
  >> rpt TOP_CASE_TAC
  >> fs [spi_host_hwext_notif_rel_def, spi_host_req_error_def, w2n_eq_iff_eq_n2w]
QED

Theorem spi_host_parsed_signals_inner:
  let
    spi_host = mk_module (procs (ffs1 ++ [spi_host_reg_top_ff] ++ ffs2)) (procs ([spi_host_reg_top_comb_1] ++ combs ++ [spi_host_reg_top_comb_2])) spi_host_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 6 reg_req;
    s' = spi_host fext fbits n;
    rsp = reg_rsp_decode s'.reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid /\ s''.error = s'.error)
  ==> s'.addr = req.addr /\ s'.write = req.write /\ s'.wdata = req.wdata
    /\ s'.wstrb = req.wstrb /\ s'.valid = req.valid /\ s'.error = rsp.error
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [spi_host_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (spi_host_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def]
  >> unabbrev_all_tac
  >> simp [procs_append, procs_def, spi_host_reg_top_comb_2_flat, reg_rsp_decode_def, word_bit_bit_field_insert]
  >> simp [word_bit_def, FCP_APPLY_UPDATE_THM_2]
  >> simp [procs_unchanged, spi_host_reg_top_comb_1_flat]
QED

Theorem spi_host_parsed_signals = SRULE [SF boolSimps.LET_ss] spi_host_parsed_signals_inner;

Theorem spi_host_reg_top_spi_host_state_rel_step_inner:
  let
    spi_host = mk_module (procs (ffs1 ++ [spi_host_reg_top_ff] ++ ffs2)) (procs ([spi_host_reg_top_comb_1] ++ combs ++ [spi_host_reg_top_comb_2])) spi_host_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid /\ s''.error = s'.error)
  (* Not strictly a requirement, but makes this easier to state (we don't have to
   * add an spi_host_reg_top_ff into the spi_host_hw_write_rel condition).
   *
   * Besides, blocking synchronous writes are bad practice anyway. (They're forced
   * to be blocking by the fact we reference them as s'.hw2reg - it's an annoying
   * limitation that you have to know whether something's combinationally or
   * synchronously assigned when using it...) *)
  /\ (!proc fext s s'. MEM proc ffs1 ==> (proc fext s s').hw2reg = s'.hw2reg)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req
    in
    spi_host_state_rel st (spi_host fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req spi_host_read spi_host_write st req_m = INR (st_upd, notif, rdata)
    (* TODO: the other way to do this would be to compare notif to
     * (spi_host_reg_top_comb_1 (fext n) (spi_host fext fbits n) (spi_host fext fbits n)).reg2hw;
     * that has the advantage of being closer to what spi_host_core actually operates
     * on, but is also uglier.
     *
     * So, we can try switching to that if this way turns out to be annoying. *)
    /\ spi_host_hwext_notif_rel notif req_c
    (* Note: somewhat counterintuitively, this actually shows that
     * spi_host_hwext_read_rel is true for the next clock cycle, not this one. *)
    ==> ?fnums. spi_host_core_state_rel (st_upd (spi_host_tick notif (st with fnums := fnums))) (spi_host fext fbits (SUC n))
      (* Note: this is only true because st_upd hasn't run yet, otherwise software
       * might have overwritten some stuff and made this false. *)
      /\ spi_host_hw_write_rel (st with fnums := fnums).regs (spi_host_tick notif (st with fnums := fnums)).regs
                          (spi_host fext fbits n).hw2reg)
  /\ spi_host_state_rel st (spi_host fext fbits n)
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req spi_host_read spi_host_write st req_m = INR (st_upd, notif, rdata)
  ==> ?fnums. spi_host_state_rel (st_upd (spi_host_tick notif (st with fnums := fnums))) (spi_host fext fbits (SUC n))
Proof
  simp []
  >> rpt strip_tac

  >> drule_all_then strip_assume_tac spi_host_reg_top_rsp_correct
  >> drule_then assume_tac spi_host_parsed_signals
  >> drule_then assume_tac spi_host_reg_top_rsp_ready_error

  >> qabbrev_tac `req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req`

  >> `spi_host_hwext_notif_rel notif req_c`
     by (drule_then strip_assume_tac cheshire_req_INR_cases
         >- fs [cheshire_req_rel_def, spi_host_hwext_notif_rel_def, spi_host_req_error_def]
         >- (fs [] >> drule_all spi_host_read_spi_host_hwext_notif_rel >> simp [])
         >- (fs [] >> drule_all spi_host_write_spi_host_hwext_notif_rel >> simp []))

  (* We need to do this in all cases so we can pick the value of fnums. *)
  >> fs [Abbr `req_c`]
  >> qpat_x_assum `!st nb fext fbits n st_upd notif rdata. _ ==> ?fnums. _`
       $ drule_all_then strip_assume_tac
  >> qabbrev_tac `req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req`
  >> qexists `fnums`

  >> simp [spi_host_state_rel_def]
  >> rpt strip_tac

  (* regs *)
  >- (simp [mk_module_def, mk_circuit_def, procs_def, procs_append, spi_host_reg_top_comb_2_flat]
      >> simp [procs_unchanged, spi_host_reg_top_comb_1_flat]

      >> drule_then strip_assume_tac cheshire_req_INR_st_upd_cases

      >> simp [GSYM mk_module_def]
      >> qpat_abbrev_tac `spi_host = mk_module _ _ _`

      >- (drule_then (fn thm => full_simp_tac pure_ss [thm]) cheshire_req_rel_valid_write
          >> simp [spi_host_reg_top_ff_flat, procs_unchanged]
          (* TODO: auto-generate this (probably need to make a new *Lib.sml to put it in...) *)
          >> simp [spi_host_regs_component_equality, spi_host_intr_state_component_equality, spi_host_intr_enable_component_equality, spi_host_control_component_equality, spi_host_status_component_equality, spi_host_configopts_0_component_equality, spi_host_configopts_1_component_equality, spi_host_configopts_2_component_equality, spi_host_csid_component_equality, spi_host_error_enable_component_equality, spi_host_error_status_component_equality, spi_host_event_enable_component_equality]
          >> gs [spi_host_state_rel_def, spi_host_tick_hwro_unchanged, spi_host_hw_write_rel_def])
      >- (fs [cheshire_req_rel_write]
          >> drule spi_host_write_st_upd_alt
          >> simp [spi_host_reg_top_ff_flat, procs_unchanged]
          >> simp [spi_host_regs_component_equality, spi_host_intr_state_component_equality, spi_host_intr_enable_component_equality, spi_host_control_component_equality, spi_host_status_component_equality, spi_host_configopts_0_component_equality, spi_host_configopts_1_component_equality, spi_host_configopts_2_component_equality, spi_host_csid_component_equality, spi_host_error_enable_component_equality, spi_host_error_status_component_equality, spi_host_event_enable_component_equality]
          >> fs [spi_host_state_rel_def, spi_host_tick_hwro_unchanged, spi_host_hw_write_rel_def, reg_rsp_decode_def, w2n_eq_iff_eq_n2w]))
  (* buffered_notif *)
  >- (simp [mk_module_def, mk_circuit_def, procs_def, procs_append, spi_host_reg_top_comb_2_flat]
      >> simp [procs_unchanged, spi_host_reg_top_comb_1_flat]
      >> simp [spi_host_notif_rel_def]
      >> simp [spi_host_reg_top_ff_flat, procs_unchanged, GSYM mk_module_def]
      >> fs [reg_rsp_decode_def])
QED

Theorem spi_host_reg_top_spi_host_state_rel_step = SRULE [SF boolSimps.LET_ss] spi_host_reg_top_spi_host_state_rel_step_inner;

Theorem spi_host_read_fnums:
  spi_host_read (st with fnums := fnums) nb offset = spi_host_read st nb offset
Proof
  asm_simp_tac std_ss [spi_host_read_def]
  (* >> asm_simp_tac std_ss [spi_host_get_status_fmtfull_def, spi_host_get_status_rxfull_def, spi_host_get_status_fmtempty_def, spi_host_get_status_hostidle_def, spi_host_get_status_targetidle_def, spi_host_get_status_rxempty_def, spi_host_get_status_txfull_def, spi_host_get_status_acqfull_def, spi_host_get_status_txempty_def, spi_host_get_status_acqempty_def, spi_host_get_rdata_rdata_def, spi_host_get_fifo_status_fmtlvl_def, spi_host_get_fifo_status_txlvl_def, spi_host_get_fifo_status_rxlvl_def, spi_host_get_fifo_status_acqlvl_def, spi_host_get_val_scl_rx_def, spi_host_get_val_sda_rx_def, spi_host_get_acqdata_abyte_def, spi_host_get_acqdata_signal_def] *)
  >> asm_simp_tac std_ss [spi_host_state_accfupds]
QED

Theorem spi_host_write_fnums:
  spi_host_write (st with fnums := fnums) nb offset wdata = spi_host_write st nb offset wdata
Proof
  asm_simp_tac std_ss [spi_host_write_def, spi_host_state_accfupds]
QED

Theorem spi_host_cheshire_req_fnums:
  cheshire_req spi_host_read spi_host_write (st with fnums := fnums) req =
  cheshire_req spi_host_read spi_host_write st req
Proof
  simp [cheshire_req_def, spi_host_read_fnums, spi_host_write_fnums]
QED

Theorem OUTR_SUM_MAP:
  ISR z ==> OUTR (SUM_MAP f g z) = g (OUTR z)
Proof
  Cases_on `z` >> simp []
QED

Theorem spi_host_st_upd_fnums_fupd:
  cheshire_req spi_host_read spi_host_write st req = INR (st_upd, notif, rdata) ==>
  st_upd (st' with fnums := fnums) = st_upd st' with fnums := fnums
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac cheshire_req_INR_cases
  >- simp []
  >- simp []
  >- (drule spi_host_write_st_upd_alt >> simp [])
QED

Theorem spi_host_st_upd_fnums:
  cheshire_req spi_host_read spi_host_write st req = INR (st_upd, notif, rdata) ==>
  (st_upd st').fnums = st'.fnums
Proof
  rpt strip_tac
  >> dxrule_then (qspecl_then [`st'`, `st'.fnums`] assume_tac) spi_host_st_upd_fnums_fupd
  >> `!st. st with fnums := st.fnums = st` by simp [spi_host_state_component_equality]
  >> fs []
  >> last_x_assum (fn thm => simp [Once thm])
QED

Theorem cheshire_run_unused_fnums_2:
  (!st req. MEM req reqs ==> ISR (cheshire_req spi_host_read spi_host_write st req)) ==>
  ?n st' rdatas. !fnums. (!i. i < n ==> fnums i = st.fnums i) ==>
  cheshire_run spi_host_tick spi_host_read spi_host_write (st with fnums := fnums) reqs = INR (st' with fnums := (\i. fnums (i + n)), rdatas)
Proof
  qid_spec_tac `st`
  >> Induct_on `reqs`
  >- (rpt strip_tac
      >> qexistsl [`0`, `st`, `[]`]
      >> simp [cheshire_run_def, SF ETA_ss])
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> `?oracle_res. cheshire_req spi_host_read spi_host_write st h = INR oracle_res` by simp [GSYM sumExtraTheory.ISR_exists]
      >> PairCases_on `oracle_res`
      >> fs [spi_host_cheshire_req_fnums]

      >> strip_assume_tac $ Q.INST [`notif` |-> `oracle_res1`] spi_host_tick_unused_fnums
      >> qrefine `n + m`
      >> simp []
      >> drule_then assume_tac spi_host_st_upd_fnums_fupd
      >> simp []
      >> last_x_assum $ qspec_then `oracle_res0 (spi_host_tick oracle_res1 st)` strip_assume_tac
      >> qexists `n'`
      >> drule_then assume_tac unused_fnums_ignored_fnums_val
      >> drule_then assume_tac spi_host_st_upd_fnums
      >> fs []
      >> qexistsl [`st'`, `oracle_res2::rdatas`]
      >> simp [])
QED

(* If the initial model state lines up with `spi_host_circuit_init`, and all the
 * requests in `fext` are valid, then the two states will stay lined up from
 * that point onwards. *)
Theorem spi_host_reg_top_correct:
  let
    spi_host = mk_module (procs (ffs1 ++ [spi_host_reg_top_ff] ++ ffs2)) (procs ([spi_host_reg_top_comb_1] ++ combs ++ [spi_host_reg_top_comb_2])) spi_host_circuit_init
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.addr = s'.addr /\ s''.write = s'.write /\ s''.wdata = s'.wdata
      /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid /\ s''.error = s'.error)
  /\ (!proc fext s s'. MEM proc ffs1 ==> (proc fext s s').hw2reg = s'.hw2reg)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 6 reg_req
    in
    spi_host_state_rel st (spi_host fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req spi_host_read spi_host_write st req_m = INR (st_upd, notif, rdata)
    /\ spi_host_hwext_notif_rel notif req_c
    ==> ?fnums. spi_host_core_state_rel (st_upd (spi_host_tick notif (st with fnums := fnums))) (spi_host fext fbits (SUC n))
      /\ spi_host_hw_write_rel (st with fnums := fnums).regs (spi_host_tick notif (st with fnums := fnums)).regs
                          (spi_host fext fbits n).hw2reg)

  (* We phrase it this way instead of as spi_host_circuit_init fbits so that
   * combinational signals are set instead of being random values from fbits. *)
  /\ spi_host_state_rel st (spi_host fext fbits 0)
  /\ (!i. i < LENGTH reqs ==>
    let
      req = reg_req_decode (fext i).reg_req_i: 6 reg_req;
    in
      ~spi_host_req_error req /\ cheshire_req_rel (EL i reqs) req)

  ==> ?fnums. let
      (st', rdatas) = OUTR (cheshire_run spi_host_tick spi_host_read spi_host_write (st with fnums := fnums) reqs)
    in
    spi_host_state_rel st' (spi_host fext fbits (LENGTH reqs))
    /\ (!i. i < LENGTH reqs ==>
      let
        rsp = reg_rsp_decode (spi_host fext fbits i).reg_rsp_o;
      in
        rsp.ready /\ ~rsp.error /\ (!value. EL i rdatas = SOME value ==> rsp.rdata = value))
Proof
  simp []
  >> rpt strip_tac
  >> Induct_on `reqs` using listTheory.SNOC_INDUCT
  >- (drule spi_host_reg_top_rsp_ready_error >> fs [cheshire_run_def, spi_host_state_rel_fnums])
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
      >> `!st req. MEM req reqs ==> ISR (cheshire_req spi_host_read spi_host_write st req)`
         by (simp [listTheory.MEM_EL]
             >> rpt strip_tac
             >> qpat_x_assum `!i. i < LENGTH reqs ==> _` $ drule_then strip_assume_tac
             >> drule cheshire_req_spi_host_req_error
             >> simp [Excl "NOT_ISL_ISR", GSYM sumTheory.NOT_ISL_ISR])
      >> drule_then (qspecl_then [`spi_host_tick`, `st with fnums := fnums`] assume_tac) cheshire_run_cheshire_req_ISR
      >> drule_then strip_assume_tac (iffLR sumExtraTheory.ISR_exists)
      >> fs []
      >> pairarg_tac
      >> fs []

      (* Infer from `~spi_host_req_error` that `cheshire_req = INR _`, so that it can be
       * used by `drule_all spi_host_reg_top_spi_host_state_rel_step`. *)
      >> drule_all_then strip_assume_tac spi_host_reg_top_rsp_correct
      >> drule_then assume_tac spi_host_reg_top_rsp_ready_error
      >> gs []
      >> drule_then (qx_choose_then `oracle_res` assume_tac) (iffLR sumExtraTheory.ISR_exists)
      >> PairCases_on `oracle_res`
      >> drule_all_then strip_assume_tac spi_host_reg_top_spi_host_state_rel_step

      (* Now we have `fnums'`, the `fnums` needed for the last step to keep things
       * lining up, and we want to use `qexists` with `fnums'` glued onto the end of
       * `fnums`. But first, we need to find out where that end is. *)
      >> `!st req. MEM req reqs ==> ISR (cheshire_req spi_host_read spi_host_write st req)`
         by (simp [listTheory.MEM_EL]
             >> rpt strip_tac
             >> qpat_x_assum `!i. i < LENGTH reqs ==> _` $ drule_then strip_assume_tac
             >> drule cheshire_req_spi_host_req_error
             >> simp [Excl "NOT_ISL_ISR", GSYM sumTheory.NOT_ISL_ISR])
      >> drule_then (qspec_then `st with fnums := fnums` strip_assume_tac) cheshire_run_unused_fnums_2
      >> qexists `\i. if i < n then fnums i else fnums' (i - n)`

      >> first_assum $ qspec_then `\i. if i < n then fnums i else fnums' (i - n)` assume_tac
      (* Instantiate it a second time to prove that st'' = st'. *)
      >> first_x_assum $ qspec_then `fnums` assume_tac
      >> gs [cheshire_run_SNOC, spi_host_cheshire_req_fnums]
      >> drule_then assume_tac cheshire_run_LENGTH_rdatas
      >> first_x_assum (assume_tac o GSYM)
      >> fs [spi_host_cheshire_req_fnums, SF ETA_ss, listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC])
QED

val _ = export_theory ();
