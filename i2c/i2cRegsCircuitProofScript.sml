open HolKernel Parse boolLib bossLib;
open BasicProvers TypeBase combinSyntax wordsLib;
open wordsTheory;
open sumExtraTheory translatorTheory;
open cheshireCircuitTheory cheshireOracleTheory i2cCircuitTheory i2cCircuitStateTheory i2cCoreTheory i2cMappingsTheory i2cRegsTheory i2cRegsCommTheory;

val _ = new_theory "i2cRegsCircuitProof";

(* Peripheral-independent section *)
Theorem i2c_read_fnums:
  i2c_read (st with fnums := fnums) nb offset = i2c_read st nb offset
Proof
  asm_simp_tac std_ss [i2c_read_def]
  >> asm_simp_tac std_ss [i2c_get_status_fmtfull_def, i2c_get_status_rxfull_def, i2c_get_status_fmtempty_def, i2c_get_status_hostidle_def, i2c_get_status_targetidle_def, i2c_get_status_rxempty_def, i2c_get_status_txfull_def, i2c_get_status_acqfull_def, i2c_get_status_txempty_def, i2c_get_status_acqempty_def, i2c_get_rdata_rdata_def, i2c_get_fifo_status_fmtlvl_def, i2c_get_fifo_status_txlvl_def, i2c_get_fifo_status_rxlvl_def, i2c_get_fifo_status_acqlvl_def, i2c_get_val_scl_rx_def, i2c_get_val_sda_rx_def, i2c_get_acqdata_abyte_def, i2c_get_acqdata_signal_def]
  >> asm_simp_tac std_ss [i2c_state_accfupds]
QED

Theorem i2c_write_fnums:
  i2c_write (st with fnums := fnums) nb offset wdata = i2c_write st nb offset wdata
Proof
  asm_simp_tac std_ss [i2c_write_def, i2c_state_accfupds]
QED

Theorem i2c_cheshire_req_fnums:
  cheshire_req i2c_read i2c_write (st with fnums := fnums) req =
  cheshire_req i2c_read i2c_write st req
Proof
  simp [cheshire_req_def, i2c_read_fnums, i2c_write_fnums]
QED

Theorem i2c_read_ISR:
  ISR (i2c_read st nb offset) = ISR (i2c_read st' nb offset)
Proof
  asm_simp_tac std_ss [i2c_read_def]
  >> rpt (IF_CASES_TAC >- asm_simp_tac std_ss [])
  >> asm_simp_tac std_ss []
QED

Theorem i2c_write_ISR:
  ISR (i2c_write st nb offset wdata) = ISR (i2c_write st' nb offset wdata)
Proof
  asm_simp_tac std_ss [i2c_write_def]
  >> rpt (IF_CASES_TAC >- asm_simp_tac std_ss [])
  >> asm_simp_tac std_ss []
QED

Theorem i2c_cheshire_req_ISR:
  ISR (cheshire_req i2c_read i2c_write st req) =
  ISR (cheshire_req i2c_read i2c_write st' req)
Proof
  simp [cheshire_req_def]
  >> ntac 4 CASE_TAC
  >- simp [ISR_SUM_MAP, i2c_read_ISR]
  >- simp [ISR_SUM_MAP, i2c_write_ISR]
QED

Theorem INR_imp_ISR:
  x = INR y ==> ISR x
Proof
  simp []
QED

Theorem i2c_read_unchanged:
  i2c_read st nb offset = INR (notif, rdata) ==>
  ?rdata'. i2c_read st' nb offset = INR (notif, rdata')
Proof
  asm_simp_tac std_ss [i2c_read_def]
  >> rpt (IF_CASES_TAC >- asm_simp_tac std_ss [])
  >> asm_simp_tac std_ss []
QED

Theorem i2c_write_unchanged:
  i2c_write st nb offset wdata = INR (st_upd, notif) ==>
  i2c_write st' nb offset wdata = INR (st_upd, notif)
Proof
  asm_simp_tac std_ss [i2c_write_def]
QED

Theorem i2c_cheshire_req_unchanged:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  ?rdata'.
  cheshire_req i2c_read i2c_write st' req = INR (st_upd, notif, rdata')
Proof
  rpt strip_tac
  >> fs [cheshire_req_def]
  >> rpt CASE_TAC
  (* noop *)
  >- fs []
  (* read *)
  >- (fs []
      >> (Cases_on `i2c_read st q q'` >- fs [])
      >> fs []
      >> pairarg_tac
      >> gvs []
      >> drule_then (qspec_then `st'` strip_assume_tac) i2c_read_unchanged
      >> simp [])
  (* write *)
  >- (fs []
      >> (Cases_on `i2c_write st q q' x` >- fs [])
      >> fs []
      >> pairarg_tac
      >> gvs []
      >> drule_then (qspec_then `st'` assume_tac) i2c_write_unchanged
      >> simp [])
QED

Theorem SUM_MAP_INR:
  SUM_MAP f g x = INR y <=> ?z. x = INR z /\ g z = y
Proof
  Cases_on `x` >> simp []
QED

(* Peripheral-specific section (things that I would put in *CoreTheory if I
 * could, but which depend on things defined later) *)
Theorem i2c_tick_ISR_ctrl_enabletarget:
  st.regs.ctrl.enabletarget = st'.regs.ctrl.enabletarget ==>
  ISR (i2c_tick notif st) = ISR (i2c_tick notif st')
Proof
  Cases_on `st'.regs.ctrl.enabletarget = 1w` >> simp [i2c_tick_def]
QED

Theorem i2c_write_ctrl_enabletarget:
  i2c_write st nb offset wdata = INR (st_upd, notif) /\
  i2c_write st' nb offset wdata = INR (st_upd', notif') /\
  st''.regs.ctrl.enabletarget = st'''.regs.ctrl.enabletarget ==>
  (st_upd st'').regs.ctrl.enabletarget = (st_upd' st''').regs.ctrl.enabletarget
Proof
  rpt strip_tac
  >> rpt (dxrule_then assume_tac i2c_write_st_upd_alt)
  >> simp []
QED

Theorem i2c_cheshire_req_ctrl_enabletarget:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) /\
  cheshire_req i2c_read i2c_write st' req = INR (st_upd', notif', rdata') /\
  st''.regs.ctrl.enabletarget = st'''.regs.ctrl.enabletarget ==>
  (st_upd st'').regs.ctrl.enabletarget = (st_upd' st''').regs.ctrl.enabletarget
Proof
  simp [cheshire_req_def]
  >> rpt CASE_TAC
  >- simp []
  >- (rpt strip_tac
      >> fs [SUM_MAP_INR]
      >> rpt (pairarg_tac >> gvs []))
  >- (rpt strip_tac
      >> fs [SUM_MAP_INR]
      >> rpt (pairarg_tac >> gvs [])
      >> irule i2c_write_ctrl_enabletarget
      >> simp []
      >> rpt (goal_assum $ drule_at Any))
QED

Theorem i2c_cheshire_run_ISR_fnums:
  ISR (cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs) =
  ISR (cheshire_run i2c_tick i2c_read i2c_write st reqs)
Proof
  goal_term (fn tm =>
    `^tm /\ (ISR (cheshire_run i2c_tick i2c_read i2c_write st reqs) ==>
    (FST (OUTR (cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs))).regs.ctrl.enabletarget
    = (FST (OUTR (cheshire_run i2c_tick i2c_read i2c_write st reqs))).regs.ctrl.enabletarget)`
    suffices_by simp [])
  >> qid_spec_tac `st`
  >> qid_spec_tac `fnums`
  >> Induct_on `reqs` using listTheory.SNOC_INDUCT
  >- simp [cheshire_run_def]
  >- (rpt gen_tac
      >> conj_asm1_tac
      >- (iff_tac
          >> rpt strip_tac
          >> fs [cheshire_run_ISR_SNOC]

          (* Apply the inductive hypothesis to prove that the other cheshire_run is also INR *)
          >> qpat_assum `cheshire_run _ _ _ _ _ = INR _` (fn thm => assume_tac (MATCH_MP INR_imp_ISR thm))
          >| [
            last_assum (fn thm => drule_then assume_tac (iffLR (cj 1 thm))),
            last_assum (fn thm => drule_then (qspec_then `fnums` assume_tac) (iffRL (cj 1 thm)))
          ]
          >> dxrule_then strip_assume_tac (iffLR ISR_exists)
          >> PairCases_on `x'`
          >> simp []

          (* Obtain the other st_upd, notif and rdata *)
          >> drule_then (qspec_then `x'0` strip_assume_tac) i2c_cheshire_req_unchanged
          >> simp []

          (* Apply the inductive hypothesis to prove that the other i2c_tick is also INR *)
          >> last_x_assum $ qspecl_then [`fnums`, `st`] strip_assume_tac
          >> rfs []
          >> drule_then assume_tac i2c_tick_ISR_ctrl_enabletarget
          >> fs [])
      >- (first_x_assum (assume_tac o iffRL)
          >> rpt strip_tac
          >> last_x_assum (fn thm => fs [ISR_exists] >> qspecl_then [`fnums`, `st`] strip_assume_tac thm)
          >> rfs [cheshire_run_SNOC, sum_bind_INR]
          >> rpt (pairarg_tac >> gvs [sum_bind_INR])
          >> irule i2c_cheshire_req_ctrl_enabletarget
          >> ntac 2 $ dxrule_then (fn thm => simp [thm]) i2c_tick_hwro_unchanged
          >> qexistsl [`notif'`, `notif`, `rdata'`, `rdata`, `x`, `st'³'`, `st'`]
          >> simp []))
QED

(* Peripheral-independent section *)
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

Triviality COND_2RAND:
  !f b x y z w.
  f (if b then x else z) (if b then y else w) =
  (if b then f x y else f z w)
Proof
  Cases_on `b` >> simp []
QED

Triviality COND_2RAND_K:
  !f b x y z w.
  f (K (if b then x else z)) (if b then y else w) =
  (if b then f (K x) y else f (K z) w)
Proof
  Cases_on `b` >> simp []
QED

(* A version of TypeBase.fields_of which uses the concrete input type rather
 * than the generalised one. *)
fun fields_of_concrete (rty: hol_type) = map (fn (name, {accessor, fupd, ty}) => let
  val accessor' = inst (match_type (accessor |> type_of |> dom_rng |> fst) rty) accessor;
  val fupd' = inst (match_type (fupd |> type_of |> dom_rng |> snd) (rty --> rty)) fupd;
  val ty' = accessor' |> type_of |> dom_rng |> snd;
in
  (name, {accessor = accessor', fupd = fupd', ty = ty'})
end) (fields_of rty)

fun prove_identity_fupds (rty: hol_type) = let
  val fields = fields_of_concrete rty;
  val accessors = accessors_of rty;
  val updates = updates_of rty;
  val nchotomy = nchotomy_of rty;
in
  LIST_CONJ (map (fn ((_, {accessor, fupd, ty}), accessor_thm, update_thm) =>
    prove (``!r. ^fupd (K (^accessor r)) r = r``,
      gen_tac
      >> qspec_then `r` strip_assume_tac nchotomy
      >> first_x_assum (fn thm => pure_rewrite_tac [thm, accessor_thm, update_thm, combinTheory.K_THM])
      >> REFL_TAC)
  ) (Portable.zip3 (fields, accessors, updates)))
end

fun FORCE_FUPD_CONV ({accessor, fupd, ...}: rcd_fieldinfo) (tm: term) = let
  val (f, _) = strip_comb tm;
in
  if term_eq f fupd then
    raise UNCHANGED
  else
    prove (``^tm = ^fupd (K (^accessor ^tm)) ^tm``, pure_rewrite_tac [prove_identity_fupds (type_of tm)] >> REFL_TAC)
end

fun COND_RECORD_CONV tm = DEPTH_CONV (fn tm =>
  if is_cond tm andalso TypeBase.is_record_type (type_of tm) then let
    val fields = type_of tm |> fields_of_concrete;
    val (cond, thn, els) = dest_cond tm;
    val (thn_f, thn_args) = strip_comb thn;
    val (els_f, els_args) = strip_comb els;
    val info = get_first (fn (_, info as {fupd, ...}) =>
      if term_eq thn_f fupd orelse term_eq els_f fupd then
        SOME info
      else
        NONE
    ) fields;
  in case info of
      SOME (info as {fupd, ...}) =>
        (LAND_CONV (QCONV (FORCE_FUPD_CONV info))
        THENC RAND_CONV (QCONV (FORCE_FUPD_CONV info))
        THENC (if (not $ term_eq thn_f fupd orelse is_K_1 (el 1 thn_args))
          andalso (not $ term_eq els_f fupd orelse is_K_1 (el 1 els_args))
        then
          PURE_ONCE_REWRITE_CONV [GSYM COND_2RAND_K]
        else
          PURE_ONCE_REWRITE_CONV [GSYM COND_2RAND])
        (* Make sure the new ifs we've just generated are covered too. *)
        THENC (LAND_CONV COND_RECORD_CONV)
        THENC (RAND_CONV COND_RECORD_CONV)) tm
    | NONE => raise UNCHANGED
  end else
    raise UNCHANGED) tm

Triviality COND_reg_req_decode:
  (if c then f (reg_req_decode x) else f (reg_req_decode y)) = f (reg_req_decode (if c then x else y))
Proof
  simp [COND_RAND]
QED

Theorem i2c_reg_top_comb_1_flat = i2c_reg_top_comb_1_def
  |> CONV_RULE (DEPTH_CONV (fn tm => if is_cond tm then SCONV [SF boolSimps.LET_ss] tm else ALL_CONV tm))
  |> CONV_RULE COND_RECORD_CONV
  |> SRULE [COND_reg_req_decode]
  |> SRULE [Ntimes LET_THM 2, SRULE [] (GSYM i2c_req_error_alt)]
  |> SRULE [WORD_LO, WORD_LS, GSYM i2c_win_addr_def, GSYM COND_reg_req_decode, Q.ISPEC `0w: 86 word` reg_req_decode_def]
  |> CONV_RULE (DEPTH_CONV (fn tm => if is_comb tm andalso same_const (fst (dest_comb tm)) ``i2c_req_error`` andalso is_record (snd (dest_comb tm)) then SCONV [i2c_req_error_def] tm else ALL_CONV tm))
  |> SRULE [SF boolSimps.LET_ss];

Theorem i2c_reg_top_comb_2_flat = i2c_reg_top_comb_2_def
  |> SRULE [SF boolSimps.LET_ss, COND_ARG1_K]
  |> SRULE [Q.ISPEC `bit_field_insert 33 2` (GSYM COND_2RAND), Q.ISPEC `$:+ n` (GSYM COND_2RAND)];

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

Theorem eq_w2n_iff_eq_n2w:
  n < dimword (:'a) ==> (n = w2n (w: 'a word) <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >> simp []
QED

Theorem eq_n2w_iff_w2n_eq:
  n < dimword (:'a) ==> (w = n2w n <=> w2n (w: 'a word) = n)
Proof
  rpt strip_tac
  >> iff_tac
  >- simp []
  >- (strip_tac
      >> first_x_assum (assume_tac o GSYM)
      >> simp [eq_w2n_iff_eq_n2w])
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

Theorem i2c_basic_signals_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    s' = i2c fext fbits n;
    rsp = reg_rsp_decode s'.reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  ==> s'.raw_addr = req.addr
    /\ s'.addr = (if i2c_win_addr (w2n req.addr) then 0w else req.addr)
    /\ s'.write = (~i2c_win_addr (w2n req.addr) /\ req.write)
    /\ s'.wstrb = (if i2c_win_addr (w2n req.addr) then 0w else req.wstrb)
    /\ s'.wdata = (if i2c_win_addr (w2n req.addr) then 0w else req.wdata)
    /\ s'.valid = (~i2c_win_addr (w2n req.addr) /\ req.valid)
    /\ s'.error = (~i2c_win_addr (w2n req.addr) /\ i2c_req_error req)
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def]
  >> unabbrev_all_tac
  >> simp [procs_append, procs_def, i2c_reg_top_comb_2_flat, reg_rsp_decode_def, word_bit_bit_field_insert]
  >> simp [word_bit_def, FCP_APPLY_UPDATE_THM_2]
  >> simp [procs_unchanged, i2c_reg_top_comb_1_flat]
  >> simp [i2c_win_addr_def]
QED

Theorem i2c_basic_signals = SRULE [SF boolSimps.LET_ss] i2c_basic_signals_inner;

Theorem i2c_reg_top_i2c_read_inner:
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
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ cheshire_req_rel (SOME (nb, offset, NONE)) req
  /\ ~rsp.error
  ==> ?notif. i2c_read st nb offset = INR (notif, rsp.rdata)
Proof
  simp []
  >> rpt strip_tac
  >> drule_all_then (qspecl_then [`n`, `fext`, `fbits`] strip_assume_tac) i2c_basic_signals
  >> `!fext s s'. (\x. x.win_buses.req) (procs combs fext s s') = (\x. x.win_buses.req) s'` by (irule procs_unchanged >> simp [])
  >> fs []
  >> qmatch_goalsub_abbrev_tac `mk_module sstep cstep`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> unabbrev_all_tac
  >> fs [mk_module_def, procs_def, procs_append, i2c_state_rel_def, i2c_core_state_rel_def, i2c_hwext_read_rel_def, i2c_win_read_rel_def, i2c_win_ready_def]
  >> first_x_assum kall_tac
  >> qpat_x_assum `i2c_notif_rel _ _` kall_tac
  >> rpt (qpat_x_assum `!nb offset. _` $ qspecl_then [`nb`, `offset`] assume_tac)
  >> gvs [cheshire_req_rel_def]
  >> gs [i2c_reg_top_comb_2_flat, procs_unchanged, reg_rsp_decode_def, word_extract_bit_field_insert, word_bit_bit_field_insert]
  >> fs [word_bit_def, FCP_APPLY_UPDATE_THM_2]
  >> qabbrev_tac `s'' = procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s')`
  >> gs [i2c_reg_top_comb_1_flat]
  >> qmatch_goalsub_abbrev_tac `req.addr`
  >> rpt (IF_CASES_TAC
          >- (gs [i2c_win_addr_def, WORD_LS, WORD_LO, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
              >> simp [i2c_read_def, Excl "w2n_eq_0"]
              >> rfs [Abbr `req`, reg_req_decode_def, WORD_EXTRACT_COMP_THM]))
  >> full_simp_tac std_ss [i2c_win_addr_def, WORD_LS, WORD_LO, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0", dimword_def, dimindex_7, bool_case_eq, w2n_n2w]
  >> asm_simp_tac std_ss [i2c_read_def, Excl "w2n_eq_0"]
  >> full_simp_tac std_ss [i2c_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0", dimword_def, dimindex_7]
QED

Theorem i2c_reg_top_i2c_read = SRULE [SF boolSimps.LET_ss] i2c_reg_top_i2c_read_inner;

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

Theorem i2c_req_error_i2c_write:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req ==>
  (ISL (i2c_write st nb offset wdata) <=> i2c_req_error req /\ ~i2c_win_addr offset)
Proof
  simp [cheshire_req_rel_write]
  >> rpt strip_tac
  >> asm_simp_tac std_ss [i2c_write_def, dimword_def, dimindex_7, GSYM eq_n2w_iff_w2n_eq]
  >> rpt TOP_CASE_TAC
  >> simp [i2c_win_addr_def, i2c_req_error_def]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> fs [GT_GE1]
QED

Theorem i2c_req_error_i2c_read:
  cheshire_req_rel (SOME (nb, offset, NONE)) req ==>
  (ISL (i2c_read st nb offset) <=> i2c_req_error req /\ ~i2c_win_addr offset)
Proof
  simp [cheshire_req_rel_read]
  >> rpt strip_tac
  >> simp [i2c_read_def, GSYM eq_n2w_iff_w2n_eq]
  >> rpt IF_CASES_TAC
  >> simp [i2c_win_addr_def, i2c_req_error_def]
QED

Theorem cheshire_req_i2c_req_error:
  cheshire_req_rel req_m req_c ==>
  (ISL (cheshire_req i2c_read i2c_write st req_m) <=> i2c_req_error req_c /\ ~i2c_win_addr (w2n req_c.addr))
Proof
  rpt strip_tac
  >> simp [cheshire_req_def]
  >> rpt TOP_CASE_TAC
  >- fs [cheshire_req_rel_def, i2c_req_error_def]
  >- fs [ISL_SUM_MAP, cheshire_req_rel_def, i2c_req_error_i2c_read]
  >- fs [ISL_SUM_MAP, cheshire_req_rel_def, i2c_req_error_i2c_write]
QED

Theorem i2c_win_addr_i2c_req_error:
  req.valid /\ i2c_win_addr (w2n req.addr) ==> i2c_req_error req
Proof
  simp [i2c_win_addr_def, i2c_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
QED

Theorem i2c_reg_top_rsp_ready_inner:
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
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  /\ i2c_win_ready (i2c fext fbits n).win_buses
  /\ req.valid
  ==> rsp.ready
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def, reg_req_decode_def, reg_rsp_decode_def, i2c_win_ready_def]
  >> unabbrev_all_tac
  >> rpt strip_tac
  >> `!fext s s'. (\x. x.win_buses.req) (procs combs fext s s') = (\x. x.win_buses.req) s'` by (irule procs_unchanged >> simp [])
  >> fs [procs_append, procs_def, i2c_reg_top_comb_2_flat, word_bit_bit_field_insert]
  >> fs [word_bit_def, FCP_APPLY_UPDATE_THM_2, procs_unchanged]
  >> qpat_abbrev_tac `s'' = procs combs _ _ _`
  >> fs [i2c_reg_top_comb_1_flat, reg_req_decode_def, word_bit_def, WORD_LO, WORD_LS]
QED

Theorem i2c_reg_top_rsp_ready = SRULE [SF boolSimps.LET_ss] i2c_reg_top_rsp_ready_inner;

Theorem i2c_reg_top_rsp_error_inner:
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
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  /\ req.valid
  /\ rsp.ready
  ==> (rsp.error <=> i2c_req_error req /\ ~i2c_win_addr (w2n req.addr) \/ i2c_win_error (i2c fext fbits n).win_buses)
Proof
  qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (_ ++ [i2c_reg_top_comb_2])`
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> simp [mk_module_def, reg_req_decode_def, reg_rsp_decode_def, i2c_win_addr_def, i2c_win_error_def]
  >> unabbrev_all_tac
  >> rpt strip_tac
  >> `!fext s s'. (\x. x.win_buses.req) (procs combs fext s s') = (\x. x.win_buses.req) s'` by (irule procs_unchanged >> simp [])
  >> fs [procs_append, procs_def, i2c_reg_top_comb_2_flat, word_bit_bit_field_insert]
  >> gs [word_bit_def, FCP_APPLY_UPDATE_THM_2, procs_unchanged]
  >> qabbrev_tac `s'' = procs combs (fext n) s' (i2c_reg_top_comb_1 (fext n) s' s')`
  >> fs [i2c_reg_top_comb_1_flat, reg_req_decode_def, word_bit_def, i2c_win_addr_def, WORD_LO, WORD_LS]
  >> rpt IF_CASES_TAC
  >> gs [i2c_req_error_def]
QED

Theorem i2c_reg_top_rsp_error = SRULE [SF boolSimps.LET_ss] i2c_reg_top_rsp_error_inner;

Theorem i2c_write_i2c_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, SOME wdata)) req /\
  i2c_write st nb offset wdata = INR (_, notif) ==>
  i2c_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_write]
  >> pure_rewrite_tac [i2c_write_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> fs [i2c_hwext_notif_rel_def, i2c_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
  >> simp [GSYM eq_n2w_iff_w2n_eq]
  >> dep_rewrite.DEP_REWRITE_TAC nb_wstrb_insts
  >> gvs []
QED

Theorem i2c_read_i2c_hwext_notif_rel:
  cheshire_req_rel (SOME (nb, offset, NONE)) req /\
  i2c_read st nb offset = INR (notif, _) ==>
  i2c_hwext_notif_rel notif req
Proof
  simp [cheshire_req_rel_read]
  >> pure_rewrite_tac [i2c_read_def]
  >> rpt TOP_CASE_TAC
  >> rpt strip_tac
  >> gvs [i2c_hwext_notif_rel_def, i2c_req_error_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0"]
QED

Theorem cheshire_req_i2c_hwext_notif_rel:
  cheshire_req_rel req_m req_c /\
  cheshire_req i2c_read i2c_write st req_m = INR (_, notif, _) ==>
  i2c_hwext_notif_rel notif req_c
Proof
  rpt strip_tac
  >> drule_then strip_assume_tac cheshire_req_INR_cases
  >- fs [cheshire_req_rel_def, i2c_hwext_notif_rel_def, i2c_req_error_def]
  >- (fs [] >> drule_all i2c_read_i2c_hwext_notif_rel >> simp [])
  >- (fs [] >> drule_all i2c_write_i2c_hwext_notif_rel >> simp [])
QED

Theorem i2c_reg_top_rsp_correct_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
    rsp = reg_rsp_decode (i2c fext fbits n).reg_rsp_o;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req
    in
    i2c_state_rel st (i2c fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
    /\ ISR (i2c_tick notif st)
    (* TODO: the other way to do this would be to compare notif to
     * (i2c_reg_top_comb_1 (fext n) (i2c fext fbits n) (i2c fext fbits n)).reg2hw;
     * that has the advantage of being closer to what i2c_core actually operates
     * on, but is also uglier.
     *
     * So, we can try switching to that if this way turns out to be annoying. *)
    /\ i2c_hwext_notif_rel notif req_c
    (* Note: somewhat counterintuitively, this actually shows that
     * i2c_hwext_read_rel is true for the next clock cycle, not this one. *)
    ==> ?fnums. i2c_core_state_rel (st_upd (OUTR (i2c_tick notif (st with fnums := fnums)))) (i2c fext fbits (SUC n))
      (* Note: this is only true because st_upd hasn't run yet, otherwise software
       * might have overwritten some stuff and made this false. *)
      /\ i2c_hw_write_rel (st with fnums := fnums).regs (OUTR (i2c_tick notif (st with fnums := fnums))).regs
                          (i2c fext fbits n).hw2reg
      /\ ~i2c_win_error (i2c fext fbits n).win_buses)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
  /\ req_c.valid
  /\ rsp.ready
  ==> (rsp.error ==> ISL (i2c_tick notif st))
    /\ (!value. ~rsp.error /\ rdata = SOME value ==> rsp.rdata = value)
Proof
  simp []
  >> qpat_abbrev_tac `sstep = procs (_ ++ ffs2)`
  >> qpat_abbrev_tac `cstep = procs (i2c_reg_top_comb_1::_)`
  >> rpt strip_tac
  >> `?s'. mk_circuit sstep cstep (i2c_circuit_init fbits) fext n = cstep (fext n) s' s'` by irule mk_circuit_cstep
  >> unabbrev_all_tac
  (* error *)
  >- (drule_all_then strip_assume_tac (iffLR i2c_reg_top_rsp_error)
      >- (drule_all_then (qspec_then `st` assume_tac) (iffRL cheshire_req_i2c_req_error)
          >> rfs [])
      >- (drule_all_then assume_tac cheshire_req_i2c_hwext_notif_rel
          >> spose_not_then (assume_tac o SRULE [])
          >> qpat_x_assum `∀st req_m fext fbits n st_upd notif rdata. _` $ drule_all_then strip_assume_tac))
  (* rdata *)
  >- (drule_then strip_assume_tac cheshire_req_INR_cases
      >- fs []
      >- (gvs []
          >> drule_all_then strip_assume_tac i2c_reg_top_i2c_read
          >> gvs [])
      >- fs [])
QED

Theorem i2c_reg_top_rsp_correct = SRULE [SF boolSimps.LET_ss] i2c_reg_top_rsp_correct_inner;

Theorem i2c_reg_top_i2c_state_rel_step_inner:
  let
    i2c = mk_module (procs (ffs1 ++ [i2c_reg_top_ff] ++ ffs2)) (procs ([i2c_reg_top_comb_1] ++ combs ++ [i2c_reg_top_comb_2])) i2c_circuit_init;
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  (!proc fext s s'. MEM proc (ffs1 ++ ffs2 ++ combs) ==>
    let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw /\ s''.regs = s'.regs /\ s''.reg_rsp_o = s'.reg_rsp_o
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
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
    /\ ISR (i2c_tick notif st)
    /\ i2c_hwext_notif_rel notif req_c
    ==> ?fnums. i2c_core_state_rel (st_upd (OUTR (i2c_tick notif (st with fnums := fnums)))) (i2c fext fbits (SUC n))
      /\ i2c_hw_write_rel (st with fnums := fnums).regs (OUTR (i2c_tick notif (st with fnums := fnums))).regs
                          (i2c fext fbits n).hw2reg
      /\ ~i2c_win_error (i2c fext fbits n).win_buses)
  /\ i2c_state_rel st (i2c fext fbits n)
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
  /\ ISR (i2c_tick notif st)
  ==> ?fnums. i2c_state_rel (st_upd (OUTR (i2c_tick notif (st with fnums := fnums)))) (i2c fext fbits (SUC n))
Proof
  simp []
  >> rpt strip_tac

  >> drule_then (qspecl_then [`n`, `fext`, `fbits`] strip_assume_tac) i2c_basic_signals
  >> drule_all_then assume_tac cheshire_req_i2c_hwext_notif_rel

  (* We need to do this in all cases so we can pick the value of fnums. *)
  >> qpat_assum `!st req_m fext fbits n st_upd notif rdata. _ ==> ?fnums. _`
       $ drule_all_then strip_assume_tac
  >> qexists `fnums`

  >> `?st'. i2c_tick notif (st with fnums := fnums) = INR st'`
     by (irule (iffLR ISR_exists) >> simp [i2c_tick_ISR_fnums])

  >> qmatch_asmsub_abbrev_tac `(req_c: 'a reg_req).addr`
  >> `~i2c_win_addr (w2n req_c.addr) ==> ~i2c_req_error req_c`
     by (`~ISL (cheshire_req i2c_read i2c_write st req_m)` by simp []
         >> drule_then (fn thm => full_simp_tac bool_ss [thm]) cheshire_req_i2c_req_error)
  >> fs [Abbr `req_c`]

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
          >> gs [i2c_state_rel_def, i2c_hw_write_rel_def]
          >> drule_then strip_assume_tac i2c_tick_hwro_unchanged
          >> simp [])
      >- (gvs [cheshire_req_rel_write, i2c_win_addr_def]
          >> drule i2c_write_st_upd_alt
          (* TODO: I think the reason this doesn't work for SPI might be that
           * procs_unchanged isn't applying properly or something? *)
          >> simp [i2c_reg_top_ff_flat, procs_unchanged]
          >> fs [i2c_state_rel_def, i2c_hw_write_rel_def, reg_rsp_decode_def, eq_n2w_iff_w2n_eq, Excl "w2n_eq_0", Cong AND_CONG]
          >> drule_then strip_assume_tac i2c_tick_hwro_unchanged
          >> simp []))
  (* buffered_notif *)
  >- (simp [mk_module_def, mk_circuit_def, procs_def, procs_append, i2c_reg_top_comb_2_flat]
      >> simp [procs_unchanged, i2c_reg_top_comb_1_flat]
      >> simp [i2c_notif_rel_def]
      >> simp [i2c_reg_top_ff_flat, procs_unchanged, GSYM mk_module_def]
      >> fs [reg_rsp_decode_def]

      (* Avoid the >- operators complaining if the goal was already solved. *)
      >> (drule_then strip_assume_tac cheshire_req_INR_st_upd_cases
          >- (drule_then (fn thm => full_simp_tac pure_ss [thm]) cheshire_req_rel_valid_write
              >> drule_then assume_tac i2c_tick_buffered_notif_NONE
              >> fs [])
          >- (fs [cheshire_req_rel_write]
              >> drule i2c_write_st_upd_alt
              >> simp []
              >> rpt (IF_CASES_TAC >- fs [GSYM eq_n2w_iff_w2n_eq, i2c_win_addr_def])
              >> drule_then assume_tac i2c_tick_buffered_notif_NONE
              >> fs [GSYM eq_n2w_iff_w2n_eq])))
QED

Theorem i2c_reg_top_i2c_state_rel_step = SRULE [SF boolSimps.LET_ss] i2c_reg_top_i2c_state_rel_step_inner;

Theorem OUTR_SUM_MAP:
  ISR z ==> OUTR (SUM_MAP f g z) = g (OUTR z)
Proof
  Cases_on `z` >> simp []
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

Theorem cheshire_run_unused_fnums:
  cheshire_run i2c_tick i2c_read i2c_write st reqs = INR (st', rdatas) ==>
  ?n. !fnums. (!i. i < n ==> fnums i = st.fnums i) ==>
  cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs = INR (st' with fnums := (\i. fnums (i + n)), rdatas)
Proof
  qid_spec_tac `st`
  >> qid_spec_tac `st'`
  >> qid_spec_tac `rdatas`
  >> Induct_on `reqs`
  >- (rpt strip_tac
      >> qexists `0`
      >> fs [cheshire_run_def, SF ETA_ss])
  >- (rpt strip_tac
      >> fs [cheshire_run_INR_CONS, i2c_cheshire_req_fnums]

      >> strip_assume_tac i2c_tick_unused_fnums
      >> qrefine `n + m`
      >> rfs []

      >> drule_then assume_tac i2c_st_upd_fnums_fupd
      >> simp []
      >> last_x_assum $ drule_then strip_assume_tac
      >> qexists `n'`
      >> drule_then assume_tac i2c_st_upd_fnums
      >> fs []
      >> `st''.fnums = (\i. st.fnums (i + n))`
         by (qpat_x_assum `!fnums. _ ==> i2c_tick _ _ = _` $ qspec_then `st.fnums` assume_tac
             >> `st with fnums := st.fnums = st` by simp [i2c_state_component_equality]
             >> fs []
             >> qpat_x_assum `_ = st''` (fn thm => simp [Once (GSYM thm)]))
      >> fs [])
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
      /\ s''.raw_addr = s'.raw_addr /\ s''.addr = s'.addr /\ s''.write = s'.write
      /\ s''.wdata = s'.wdata /\ s''.wstrb = s'.wstrb /\ s''.valid = s'.valid
      /\ s''.error = s'.error /\ s''.win_buses.req = s'.win_buses.req)
  /\ (!proc fext s s'. MEM proc ffs1 ==> (proc fext s s').hw2reg = s'.hw2reg)
  /\ (!st req_m fext fbits n st_upd notif rdata.
    let
      req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req
    in
    i2c_state_rel st (i2c fext fbits n)
    /\ cheshire_req_rel req_m req_c
    /\ cheshire_req i2c_read i2c_write st req_m = INR (st_upd, notif, rdata)
    /\ ISR (i2c_tick notif st)
    /\ i2c_hwext_notif_rel notif req_c
    ==> ?fnums. i2c_core_state_rel (st_upd (OUTR (i2c_tick notif (st with fnums := fnums)))) (i2c fext fbits (SUC n))
      /\ i2c_hw_write_rel (st with fnums := fnums).regs (OUTR (i2c_tick notif (st with fnums := fnums))).regs
                          (i2c fext fbits n).hw2reg
      /\ ~i2c_win_error (i2c fext fbits n).win_buses)

  (* We phrase it this way instead of as i2c_circuit_init fbits so that
   * combinational signals are set instead of being random values from fbits. *)
  /\ i2c_state_rel st (i2c fext fbits 0)
  /\ (!i. i < LENGTH reqs ==>
    cheshire_req_rel (EL i reqs) (reg_req_decode (fext i).reg_req_i: 7 reg_req))
  /\ ISR (cheshire_run i2c_tick i2c_read i2c_write st reqs)

  ==> ?fnums. let
      (st', rdatas) = OUTR (cheshire_run i2c_tick i2c_read i2c_write (st with fnums := fnums) reqs)
    in
    i2c_state_rel st' (i2c fext fbits (LENGTH reqs))
    /\ (!i. i < LENGTH reqs ==>
      let
        rsp = reg_rsp_decode (i2c fext fbits i).reg_rsp_o;
      in
        (IS_SOME (EL i reqs) ==> rsp.ready /\ ~rsp.error)
        /\ (!value. EL i rdatas = SOME value ==> rsp.rdata = value))
Proof
  simp []
  >> rpt strip_tac
  >> (Induct_on `reqs` using listTheory.SNOC_INDUCT
      >- fs [cheshire_run_def, i2c_state_rel_fnums])
  >> rpt strip_tac

  (* Satisfy the assumptions for our inductive hypothesis, which will tell us the
   * `fnums` used by `cheshire_run` up until this point. *)
  >> `!f n. (!i. i < SUC n ==> f i) <=> (!i. i < n ==> f i) /\ f n`
     by (rpt strip_tac
         >> iff_tac
         >- simp []
         >- (rpt strip_tac >> Cases_on `i = n` >> simp []))
  >> drule_then assume_tac (iffRL i2c_cheshire_run_ISR_fnums)
  >> gs [listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC, cheshire_run_ISR_SNOC, INR_imp_ISR]
  >> pairarg_tac
  >> fs []

  (* Then find `fnums'`, the fnums which need to follow `fnums` for the last step
   * to keep things lining up. *)
  >> qpat_x_assum `!fnums. ?st' rdatas st_upd notif rdata. _` $ qspec_then `fnums` strip_assume_tac
  >> gvs []
  >> drule_all_then strip_assume_tac i2c_reg_top_i2c_state_rel_step

  (* Now we want to use `qexists` with `fnums'` glued onto the end of `fnums`; but
   * first, we need to find out where that end is. *)
  >> drule_then strip_assume_tac cheshire_run_unused_fnums
  >> fs []
  >> qexists `\i. if i < n then fnums i else fnums' (i - n)`

  (* Obtain the values of `st'` and `rdatas`. *)
  >> simp [cheshire_run_SNOC, sum_bind_def, i2c_cheshire_req_fnums, ETA_THM]
  >> `?st. i2c_tick notif' (st'' with fnums := fnums') = INR st` by simp [GSYM ISR_exists, i2c_tick_ISR_fnums]
  >> simp [sum_bind_def]

  (* Now that we've actually got all the values we're working with, we can prove
   * the goal. *)
  (* st -> st'' -> st_upd' st'³' *)
  >> qpat_x_assum `!fnums'. _ => cheshire_run _ _ _ _ _ = INR _` $ qspec_then `\i. if i < n then fnums i else fnums' (i - n)` assume_tac
  >> fs []

  >> drule_then (assume_tac o GSYM) cheshire_run_LENGTH_rdatas
  >> gs [listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC]

  >> qabbrev_tac `req = reg_req_decode (fext (LENGTH rdatas')).reg_req_i: 7 reg_req`
  >> qmatch_goalsub_abbrev_tac `rsp.ready`
  >> conj_tac
  >> rpt (FIRST [disch_tac, gen_tac])
  >| [
    `req.valid` by fs [Abbr `req`, cheshire_req_rel_def],
    `req.valid` by (drule_then strip_assume_tac cheshire_req_INR_cases
                    >> gvs [Abbr `req`, cheshire_req_rel_def])
  ]
  >> `rsp.ready`
      by (fs [Abbr `rsp`]
          >> drule_then irule i2c_reg_top_rsp_ready
          >> fs [i2c_state_rel_def, i2c_core_state_rel_def])
  >> unabbrev_all_tac
  >> drule_all_then strip_assume_tac i2c_reg_top_rsp_correct
  >> qmatch_asmsub_abbrev_tac `rsp.error`
  >> `~rsp.error`
      by (rpt strip_tac
          >> fs [GSYM sumTheory.NOT_ISR_ISL, Excl "NOT_ISR_ISL"])
  >> simp []
QED

val asm1_simp = BETA_RULE o REWRITE_RULE [combinTheory.C_THM, listTheory.EVERY_MEM] o GEN_ALL

val ff_asm1' = ff_asm1 |> asm1_simp
val comb_asm1' = comb_asm1 |> asm1_simp

Theorem asm1:
∀proc fext s s'.
  MEM proc (i2c_core_ffs1 ++ [] ++ i2c_core_combs) ⇒
  (let
     s'' = proc fext s s'
   in
     s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧
     s''.reg_rsp_o = s'.reg_rsp_o ∧ s''.addr = s'.addr ∧
     (s''.write ⇔ s'.write) ∧ s''.wdata = s'.wdata ∧
     s''.wstrb = s'.wstrb ∧ (s''.valid ⇔ s'.valid))
Proof
  ASSUME_TAC ff_asm1'
  >> ASSUME_TAC comb_asm1'
  >> rpt GEN_TAC
  >> REWRITE_TAC [rich_listTheory.IS_EL_APPEND, listTheory.MEM]
  >> STRIP_TAC
  >> FIRST_X_ASSUM (fn th1 => FIRST_ASSUM (fn th2 => MATCH_MP th2 th1 |> REWRITE_RULE [LET_THM] |> BETA_RULE |> ASSUME_TAC))
  >> rw [LET_THM]
QED

Theorem asm2:
∀proc fext s s'. MEM proc i2c_core_ffs1 ⇒ (proc fext s s').hw2reg = s'.hw2reg
Proof
  rw [ff_asm2 |> asm1_simp]
QED

val _ = type_abbrev(
  "proc_ty",
  “:(i2c_circuit_ext_state -> i2c_circuit_state -> i2c_circuit_state -> i2c_circuit_state) list”);

val i2c_reg_top_correct' = i2c_reg_top_correct
             |> INST [“combs:proc_ty” |-> “i2c_core_combs” ,
                      “ffs2:proc_ty” |-> “[]:proc_ty” ,
                      “ffs1:proc_ty” |-> “i2c_core_ffs1”]
             |> REWRITE_RULE [GSYM i2c_circuit_def, Ntimes LET_THM 1]
             |> BETA_RULE
             |> IMP_CANON
             |> hd

(* this is the theorem ‘i2c_reg_top_correct’ with the first two assumptions
   being discharged, targetted specifically for ‘i2c_circuit’ *)
val i2c_reg_top_correct_inst =
  MATCH_MP (MATCH_MP i2c_reg_top_correct' asm1) asm2

val _ = export_theory ();
