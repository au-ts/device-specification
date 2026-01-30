open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorLib;
open shallowFlattenLib i2cRegsCircuitLib;
open cheshireCircuitTheory i2cCircuitStateTheory;

val _ = new_theory "i2cCircuit";

Definition i2c_reg_top_comb_1_def:
  i2c_reg_top_comb_1 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_1_tm
End

Definition i2c_reg_top_comb_2_def:
  i2c_reg_top_comb_2 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_2_tm
End

Definition i2c_reg_top_ff_def:
  i2c_reg_top_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_ff_tm
End

Theorem i2c_reg_top_comb_1_trans = SIMP_RULE (pure_ss ++ ARITH_ss) [reg_req_decode_def, reg_req_accfupds, combinTheory.K_THM, dimindex_7, dimindex_48, WORD_EXTRACT_ZERO2, word_bit_0] i2c_reg_top_comb_1_def;

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

(* Section --- I2C Core *)

Definition i2c_core_target_loopback_comb_def:
  i2c_core_target_loopback_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with target_loopback := (word_bit 0 s.regs.ctrl.enabletarget ∧ word_bit 0 s.regs.ctrl.llpbk)
End

Definition i2c_core_start_det_comb_def:
  i2c_core_start_det_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with start_det := (word_bit 0 s.regs.ctrl.enabletarget /\ s.scl_i_q /\ s.scl_sync /\ s.sda_i_q /\ ~s.sda_sync)
End

Definition i2c_core_stop_det_comb_def:
  i2c_core_stop_det_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with stop_det := (word_bit 0 s.regs.ctrl.enabletarget /\ s.scl_i_q /\ s.scl_sync /\ ~s.sda_i_q /\ s.sda_sync)
End

Definition i2c_core_address_match_comb_def:
  i2c_core_address_match_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with address_match := 
  ((((7 >< 1) s.input_byte) && s.regs.target_id.mask0 = s.regs.target_id.address0) ∨
  (((7 >< 1) s.input_byte) && s.regs.target_id.mask1 = s.regs.target_id.address1))
End

Definition i2c_core_target_idle_comb_def:
  i2c_core_target_idle_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  (* All the target states come at the end, and the target mode is idle as long as
   * we aren't in any of those.
   *
   * Even though it can't happen in reality, the original circuit returns 1 in the
   * case of an invalid state, which we need to match for equivalence checking to
   * pass. *)
  s' with target_idle := (s.fsm_state <+ acquireStart ∨ stretchAcqFull <+ s.fsm_state)
End

Definition i2c_core_host_idle_comb_def:
  i2c_core_host_idle_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with host_idle := (s.fsm_state = idle \/ acquireStart <=+ s.fsm_state)
End

(* Direct translation from @{file "i2cCoreCiruitLib.sml"} *)
Definition fmt_fifo_reset_def:
  fmt_fifo_reset (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with reset := ((s.regs.fifo_ctrl.fmtrst = 1w) ∧ s.reg2hw.fifo_ctrl.fmtrst_qe)
End

Definition fmt_fifo_rready_def:
  fmt_fifo_rready (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rready := (s.fsm_state = popFmtFifo)
End

Definition fmt_fifo_empty_def:
  fmt_fifo_empty (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with empty := (s.fmt_fifo.rptr = s.fmt_fifo.wptr)
End

Definition fmt_fifo_rdata_def:
  fmt_fifo_rdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rdata :=
  if s'.fmt_fifo.empty then 0w else s.fmt_fifo_regfile $ (5 >< 0) s.fmt_fifo.rptr
End

Definition fmt_fifo_rvalid_def:
  fmt_fifo_rvalid (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rvalid := ¬s'.fmt_fifo.empty
End

Definition fmt_fifo_incr_rptr_def:
  fmt_fifo_incr_rptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with incr_rptr := (s'.fmt_fifo.rvalid ∧ s'.fmt_fifo.rready ∧ ¬s.under_rst)
End

Definition fmt_fifo_counter_rptr_wrap_def:
  fmt_fifo_counter_rptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter := s'.fmt_fifo.counter with rptr_wrap :=
  (s'.fmt_fifo.incr_rptr ∧ (5 >< 0) s.fmt_fifo.rptr = 63w : 6 word)
End

Definition fmt_fifo_counter_rptr_wrap_cnt_def:
  fmt_fifo_counter_rptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter := s'.fmt_fifo.counter with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.fmt_fifo.rptr then (64w : 7 word) else 0w
End

Definition fmt_fifo_rptr_ff_def:
  fmt_fifo_rptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.fmt_fifo.reset then
    s' with fmt_fifo := s'.fmt_fifo with rptr := 0w
  else if s'.fmt_fifo.counter.rptr_wrap then
    s' with fmt_fifo := s'.fmt_fifo with rptr := s'.fmt_fifo.counter.rptr_wrap_cnt
  else if s'.fmt_fifo.incr_rptr then
    s' with fmt_fifo := s'.fmt_fifo with rptr := s.fmt_fifo.rptr + 1w
  else
    s' with fmt_fifo := s'.fmt_fifo with rptr := s.fmt_fifo.rptr
End

Definition fmt_fifo_wvalid_def:
  fmt_fifo_wvalid (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
   s' with fmt_fifo := s'.fmt_fifo with wvalid :=
   (s.reg2hw.fdata.fbyte_qe ∧ s.reg2hw.fdata.start_qe ∧ s.reg2hw.fdata.stop_qe ∧ s.reg2hw.fdata.read_qe ∧ s.reg2hw.fdata.rcont_qe ∧ s.reg2hw.fdata.nakok_qe)
End

Definition fmt_fifo_full_def:
  fmt_fifo_full (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with full :=
  ( word_bit 6 s.fmt_fifo.wptr ≠ word_bit 6 s.fmt_fifo.rptr
    ∧ (5 >< 0) s.fmt_fifo.wptr : 6 word = (5 >< 0) s.fmt_fifo.rptr : 6 word)
End

Definition fmt_fifo_wready_def:
  fmt_fifo_wready (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with wready := (~s'.fmt_fifo.full /\ ~s.under_rst)
End

Definition fmt_fifo_incr_wptr_def:
  fmt_fifo_incr_wptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with incr_wptr := (s'.fmt_fifo.wvalid ∧ s'.fmt_fifo.wready ∧ ¬s.under_rst)
End

Definition fmt_fifo_wdata_def:
  fmt_fifo_wdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with wdata :=
  (w2w s.regs.fdata.nakok <<~ 12w)
  || (w2w s.regs.fdata.rcont <<~ 11w)
  || (w2w s.regs.fdata.read <<~ 10w)
  || (w2w s.regs.fdata.stop <<~ 9w)
  || (w2w s.regs.fdata.start <<~ 8w)
  ||  w2w s.regs.fdata.fbyte
End

Definition fmt_fifo_regfile_ff_def:
  fmt_fifo_regfile_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.fmt_fifo.incr_wptr
  then s' with fmt_fifo_regfile := ((5 >< 0) s.fmt_fifo.wptr =+ s'.fmt_fifo.wdata) s'.fmt_fifo_regfile
  else s'
End

Definition fmt_fifo_counter_wptr_wrap_def:
  fmt_fifo_counter_wptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter := s'.fmt_fifo.counter with wptr_wrap :=
  (s'.fmt_fifo.incr_wptr ∧ (5 >< 0) s.fmt_fifo.wptr = 63w : 6 word)
End

Definition fmt_fifo_counter_wptr_wrap_cnt_def:
  fmt_fifo_counter_wptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter := s'.fmt_fifo.counter with wptr_wrap_cnt :=
  if ¬ (word_bit 6 s.fmt_fifo.wptr) then 64w else 0w
End

Definition fmt_fifo_wptr_ff_def:
  fmt_fifo_wptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.fmt_fifo.reset then
    s' with fmt_fifo := s'.fmt_fifo with wptr := 0w
  else if s'.fmt_fifo.counter.wptr_wrap then
    s' with fmt_fifo := s'.fmt_fifo with wptr := s'.fmt_fifo.counter.wptr_wrap_cnt
  else if s'.fmt_fifo.incr_wptr then
    s' with fmt_fifo := s'.fmt_fifo with wptr := s.fmt_fifo.wptr + 1w
  else
    s' with fmt_fifo := s'.fmt_fifo with wptr := s.fmt_fifo.wptr
End

Definition i2c_core_delay_comb_def:
  i2c_core_delay_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  let
    s' = s' with delay := s'.delay with setup_start := w2w s.regs.timing1.t_r + w2w s.regs.timing2.tsu_sta ;
    s' = s' with delay := s'.delay with hold_start  := w2w s.regs.timing1.t_f + w2w s.regs.timing2.thd_sta ;
    s' = s' with delay := s'.delay with setup_data  := w2w s.regs.timing1.t_r + w2w s.regs.timing3.tsu_dat ;
    s' = s' with delay := s'.delay with clock_start := w2w s.regs.timing3.thd_dat ;
    s' = s' with delay := s'.delay with clock_low   := w2w s.regs.timing0.tlow - w2w s.regs.timing3.thd_dat;
    s' = s' with delay := s'.delay with clock_pulse := w2w s.regs.timing1.t_r + w2w s.regs.timing0.thigh + w2w s.regs.timing1.t_f ;
    s' = s' with delay := s'.delay with hold_bit    := w2w s.regs.timing1.t_f + w2w s.regs.timing3.thd_dat ;
    s' = s' with delay := s'.delay with clock_stop  := w2w s.regs.timing1.t_f + w2w s.regs.timing0.tlow - w2w s.regs.timing3.thd_dat ;
    s' = s' with delay := s'.delay with setup_stop  := w2w s.regs.timing1.t_r + w2w s.regs.timing4.tsu_sto ;
    s' = s' with delay := s'.delay with hold_stop   := w2w s.regs.timing1.t_r + w2w s.regs.timing4.t_buf - w2w s.regs.timing2.tsu_sta ;
  in
    s'
End

Definition i2c_core_log_start_comb_def:
  i2c_core_log_start_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  s' with log_start := (s.fsm_state = setupStart ∧ s.counter = 1w)
End

Definition i2c_core_log_stop_comb_def:
  i2c_core_log_stop_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  s' with log_stop := (s.fsm_state = setupStop ∧ s.counter = 1w)
End

Definition fmt_fifo_flag_start_before_def:
  fmt_fifo_flag_start_before (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with start_before :=
  (s'.fmt_fifo.rvalid ∧ word_bit 8 s'.fmt_fifo.rdata)
End

Definition fmt_fifo_flag_stop_after_def:
  fmt_fifo_flag_stop_after (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with stop_after :=
  (s'.fmt_fifo.rvalid ∧ word_bit 9 s'.fmt_fifo.rdata)
End

Definition fmt_fifo_flag_read_bytes_def:
  fmt_fifo_flag_read_bytes (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with read_bytes :=
  (s'.fmt_fifo.rvalid ∧ word_bit 10 s'.fmt_fifo.rdata)
End

Definition fmt_fifo_flag_read_continue_def:
  fmt_fifo_flag_read_continue (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with read_continue :=
  (s'.fmt_fifo.rvalid ∧ word_bit 11 s'.fmt_fifo.rdata)
End

Definition fmt_fifo_flag_nak_ok_def:
  fmt_fifo_flag_nak_ok (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with nak_ok :=
  (s'.fmt_fifo.rvalid ∧ word_bit 12 s'.fmt_fifo.rdata)
End

Definition i2c_core_tx_fifo_empty_comb_def:
  i2c_core_tx_fifo_empty_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with empty := (s.tx_fifo.rptr = s.tx_fifo.wptr)
End

Definition i2c_core_tx_fifo_rdata_comb_def:
  i2c_core_tx_fifo_rdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with rdata :=
  if s'.tx_fifo.empty then 0w else s.tx_fifo_regfile $ (5 >< 0) s.tx_fifo.rptr
End

Definition i2c_core_tx_fifo_rvalid_comb_def:
  i2c_core_tx_fifo_rvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with rvalid := ~s'.tx_fifo.empty
End

Definition i2c_core_tx_fifo_full_comb_def:
  i2c_core_tx_fifo_full_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with full :=
  ((word_bit 6 s.tx_fifo.wptr ≠ word_bit 6 s.tx_fifo.rptr) ∧
   ((5 >< 0) s.tx_fifo.wptr : 6 word = (5 >< 0) s.tx_fifo.rptr : 6 word))
End

Definition i2c_core_tx_fifo_wready_comb_def:
  i2c_core_tx_fifo_wready_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with wready := (~s'.tx_fifo.full /\ ~s.under_rst)
End

Definition i2c_core_tx_fifo_depth_comb_def:
  i2c_core_tx_fifo_depth_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.tx_fifo.full then
    s' with tx_fifo := s'.tx_fifo with depth := 64w
  else if word_bit 6 s.tx_fifo.wptr = word_bit 6 s.tx_fifo.rptr then
    s' with tx_fifo := s'.tx_fifo with depth :=
    ((w2w ((5 >< 0) s.tx_fifo.wptr : 6 word)) - (w2w ((5 >< 0) s.tx_fifo.rptr : 6 word)))
  else
    s' with tx_fifo := s'.tx_fifo with depth :=
    64w - w2w ((5 >< 0) s.tx_fifo.rptr : 6 word) + w2w ((5 >< 0) s.tx_fifo.wptr :  6 word)
End

Definition i2c_core_acq_fifo_empty_comb_def:
  i2c_core_acq_fifo_empty_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with empty := (s.acq_fifo.rptr = s.acq_fifo.wptr)
End

Definition i2c_core_acq_fifo_rdata_comb_def:
  i2c_core_acq_fifo_rdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with rdata :=
  if s'.acq_fifo.empty then 0w else s.acq_fifo_regfile $ (5 >< 0) s.acq_fifo.rptr
End

Definition i2c_core_acq_fifo_rvalid_comb_def:
  i2c_core_acq_fifo_rvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with rvalid := ~s'.acq_fifo.empty
End

Definition i2c_core_acq_fifo_full_comb_def:
  i2c_core_acq_fifo_full_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with full :=
  ((word_bit 6 s.acq_fifo.wptr ≠ word_bit 6 s.acq_fifo.rptr) ∧
   ((5 >< 0) s.acq_fifo.wptr : 6 word = (5 >< 0) s.acq_fifo.rptr : 6 word))
End

Definition i2c_core_acq_fifo_wready_comb_def:
  i2c_core_acq_fifo_wready_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with wready := (~s'.acq_fifo.full /\ ~s.under_rst)
End

Definition i2c_core_acq_fifo_depth_comb_def:
  i2c_core_acq_fifo_depth_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.acq_fifo.full then
    s' with acq_fifo := s'.acq_fifo with depth := 64w
  else if word_bit 6 s.acq_fifo.wptr = word_bit 6 s.acq_fifo.rptr then
    s' with acq_fifo := s'.acq_fifo with depth :=
    ((w2w ((5 >< 0) s.acq_fifo.wptr : 6 word)) - (w2w ((5 >< 0) s.acq_fifo.rptr : 6 word)))
  else
    s' with acq_fifo := s'.acq_fifo with depth :=
    64w - w2w ((5 >< 0) s.acq_fifo.rptr : 6 word) + w2w ((5 >< 0) s.acq_fifo.wptr :  6 word)
End

Definition i2c_core_acq_fifo_2free_comb_def:
  i2c_core_acq_fifo_2free_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo_2free := (1w <+ 64w - s'.acq_fifo.depth)
End

Definition i2c_core_tx_fifo_reset_comb_def:
  i2c_core_tx_fifo_reset_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with reset :=
  (word_bit 0 s.regs.fifo_ctrl.txrst ∧ s.reg2hw.fifo_ctrl.txrst_qe)
End

Definition i2c_core_tx_fifo_rready_comb_def:
  i2c_core_tx_fifo_rready_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with rready := (s.fsm_state = transmitAckPulse ∧ ~s.scl_sync)
End

Definition i2c_core_tx_fifo_wvalid_comb_def:
  i2c_core_tx_fifo_wvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with wvalid :=
  if s'.target_loopback then
    s'.acq_fifo.rvalid ∧ word_bit 0 s.regs.ctrl.enabletarget ∧ ((9 >< 8) s'.acq_fifo.rdata: 2 word) = 0w
  else
    s.reg2hw.txdata.txdata_qe
End

Definition i2c_core_tx_fifo_wdata_comb_def:
  i2c_core_tx_fifo_wdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with wdata :=
  if s'.target_loopback then
    (7 >< 0) s'.acq_fifo.rdata
  else
    s.regs.txdata.txdata
End

Definition i2c_core_tx_fifo_incr_rptr_comb_def:
  i2c_core_tx_fifo_incr_rptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with incr_rptr := (s'.tx_fifo.rvalid ∧ s'.tx_fifo.rready ∧ ¬s.under_rst)
End

Definition i2c_core_tx_fifo_counter_rptr_wrap_comb_def:
  i2c_core_tx_fifo_counter_rptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with counter := s'.tx_fifo.counter with rptr_wrap :=
  (s'.tx_fifo.incr_rptr ∧ (5 >< 0) s.tx_fifo.rptr = 63w : 6 word)
End

Definition i2c_core_tx_fifo_counter_rptr_wrap_cnt_comb_def:
  i2c_core_tx_fifo_counter_rptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with counter := s'.tx_fifo.counter with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.tx_fifo.rptr then (64w : 7 word) else 0w
End

Definition i2c_core_tx_fifo_rptr_ff_def:
  i2c_core_tx_fifo_rptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.tx_fifo.reset then
    s' with tx_fifo := s'.tx_fifo with rptr := 0w
  else if s'.tx_fifo.counter.rptr_wrap then
    s' with tx_fifo := s'.tx_fifo with rptr := s'.tx_fifo.counter.rptr_wrap_cnt
  else if s'.tx_fifo.incr_rptr then
    s' with tx_fifo := s'.tx_fifo with rptr := s.tx_fifo.rptr + 1w
  else
    s' with tx_fifo := s'.tx_fifo with rptr := s.tx_fifo.rptr
End

Definition i2c_core_tx_fifo_incr_wptr_comb_def:
  i2c_core_tx_fifo_incr_wptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with incr_wptr := (s'.tx_fifo.wvalid ∧ s'.tx_fifo.wready ∧ ¬s.under_rst)
End

Definition i2c_core_tx_fifo_regfile_def:
  i2c_core_tx_fifo_regfile (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.tx_fifo.incr_wptr
  then s' with tx_fifo_regfile := ((5 >< 0) s.tx_fifo.wptr =+ s'.tx_fifo.wdata) s'.tx_fifo_regfile
  else s'
End

Definition i2c_core_tx_fifo_counter_wptr_wrap_comb_def:
  i2c_core_tx_fifo_counter_wptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with counter := s'.tx_fifo.counter with wptr_wrap :=
  (s'.tx_fifo.incr_wptr ∧ (5 >< 0) s.tx_fifo.wptr = 63w : 6 word)
End

Definition i2c_core_tx_fifo_counter_wptr_wrap_cnt_comb_def:
  i2c_core_tx_fifo_counter_wptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with tx_fifo := s'.tx_fifo with counter := s'.tx_fifo.counter with wptr_wrap_cnt :=
  if ¬word_bit 6 s.tx_fifo.wptr then 64w else 0w
End

Definition i2c_core_tx_fifo_wptr_ff_def:
  i2c_core_tx_fifo_wptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.tx_fifo.reset then
    s' with tx_fifo := s'.tx_fifo with wptr := 0w
  else if s'.tx_fifo.counter.wptr_wrap then
    s' with tx_fifo := s'.tx_fifo with wptr := s'.tx_fifo.counter.wptr_wrap_cnt
  else if s'.tx_fifo.incr_wptr then
    s' with tx_fifo := s'.tx_fifo with wptr := s.tx_fifo.wptr + 1w
  else
    s' with tx_fifo := s'.tx_fifo with wptr := s.tx_fifo.wptr
End

Definition i2c_core_acq_fifo_reset_comb_def:
  i2c_core_acq_fifo_reset_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with reset :=
  (word_bit 0 s.regs.fifo_ctrl.acqrst ∧ s.reg2hw.fifo_ctrl.acqrst_qe)
End

Definition i2c_core_acq_fifo_rready_comb_def:
  i2c_core_acq_fifo_rready_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with rready :=
  ((s'.reg2hw.acqdata.abyte_re ∧ s'.reg2hw.acqdata.signal_re)
  ∨ (s'.target_loopback ∧ (s'.tx_fifo.wready ∨ ((9 >< 8) s'.acq_fifo.rdata: 2 word) ≠ 0w)))
End

Definition i2c_core_acq_fifo_wvalid_comb_def:
  i2c_core_acq_fifo_wvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.start_det ∨ s'.stop_det then
    s' with acq_fifo := s'.acq_fifo with wvalid := ¬s'.target_idle
  else if (s.fsm_state = addrAckHold ∨ s.fsm_state = acquireAckHold) ∧ s.counter = 1w ∨ s.fsm_state = stretchAddr ∨ s.fsm_state = stretchAcqFull then
    s' with acq_fifo := s'.acq_fifo with wvalid := s'.acq_fifo_2free
  else
    s' with acq_fifo := s'.acq_fifo with wvalid := F
End

Definition i2c_core_acq_fifo_wdata_comb_def:
  i2c_core_acq_fifo_wdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.start_det then
    s' with acq_fifo := s'.acq_fifo with wdata := (3w : word2) @@ s.input_byte
  else if s'.stop_det then
    s' with acq_fifo := s'.acq_fifo with wdata := (2w : word2) @@ s.input_byte
  else if s.fsm_state = addrAckHold ∧ s.counter = 1w ∨ s.fsm_state = stretchAddr then
    s' with acq_fifo := s'.acq_fifo with wdata := (1w : word2) @@ s.input_byte
  else if s.fsm_state = acquireAckHold ∧ s.counter = 1w ∨ s.fsm_state = stretchAcqFull then
    s' with acq_fifo := s'.acq_fifo with wdata := (0w : word2) @@ s.input_byte
  else
    s' with acq_fifo := s'.acq_fifo with wdata := 0w
End

Definition i2c_core_acq_fifo_incr_rptr_comb_def:
  i2c_core_acq_fifo_incr_rptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with incr_rptr := (s'.acq_fifo.rvalid ∧ s'.acq_fifo.rready ∧ ¬s.under_rst)
End

Definition i2c_core_acq_fifo_counter_rptr_wrap_comb_def:
  i2c_core_acq_fifo_counter_rptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with counter := s'.acq_fifo.counter with rptr_wrap :=
  (s'.acq_fifo.incr_rptr ∧ (5 >< 0) s.acq_fifo.rptr = 63w : 6 word)
End

Definition i2c_core_acq_fifo_counter_rptr_wrap_cnt_comb_def:
  i2c_core_acq_fifo_counter_rptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with counter := s'.acq_fifo.counter with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.acq_fifo.rptr then (64w : 7 word) else 0w
End

Definition i2c_core_acq_fifo_rptr_ff_def:
  i2c_core_acq_fifo_rptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.acq_fifo.reset then
    s' with acq_fifo := s'.acq_fifo with rptr := 0w
  else if s'.acq_fifo.counter.rptr_wrap then
    s' with acq_fifo := s'.acq_fifo with rptr := s'.acq_fifo.counter.rptr_wrap_cnt
  else if s'.acq_fifo.incr_rptr then
    s' with acq_fifo := s'.acq_fifo with rptr := s.acq_fifo.rptr + 1w
  else
    s' with acq_fifo := s'.acq_fifo with rptr := s.acq_fifo.rptr
End

Definition i2c_core_acq_fifo_incr_wptr_comb_def:
  i2c_core_acq_fifo_incr_wptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with incr_wptr := (s'.acq_fifo.wvalid ∧ s'.acq_fifo.wready ∧ ¬s.under_rst)
End

Definition i2c_core_acq_fifo_regfile_def:
  i2c_core_acq_fifo_regfile (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.acq_fifo.incr_wptr
  then s' with acq_fifo_regfile := ((5 >< 0) s.acq_fifo.wptr =+ s'.acq_fifo.wdata) s'.acq_fifo_regfile
  else s'
End

Definition i2c_core_acq_fifo_counter_wptr_wrap_comb_def:
  i2c_core_acq_fifo_counter_wptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with counter := s'.acq_fifo.counter with wptr_wrap :=
  (s'.acq_fifo.incr_wptr ∧ (5 >< 0) s.acq_fifo.wptr = 63w : 6 word)
End

Definition i2c_core_acq_fifo_counter_wptr_wrap_cnt_comb_def:
  i2c_core_acq_fifo_counter_wptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with acq_fifo := s'.acq_fifo with counter := s'.acq_fifo.counter with wptr_wrap_cnt :=
  if ¬word_bit 6 s.acq_fifo.wptr then 64w else 0w
End

Definition i2c_core_acq_fifo_wptr_ff_def:
  i2c_core_acq_fifo_wptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.acq_fifo.reset then
    s' with acq_fifo := s'.acq_fifo with wptr := 0w
  else if s'.acq_fifo.counter.wptr_wrap then
    s' with acq_fifo := s'.acq_fifo with wptr := s'.acq_fifo.counter.wptr_wrap_cnt
  else if s'.acq_fifo.incr_wptr then
    s' with acq_fifo := s'.acq_fifo with wptr := s.acq_fifo.wptr + 1w
  else
    s' with acq_fifo := s'.acq_fifo with wptr := s.acq_fifo.wptr
End

Definition i2c_core_stretch_tx_comb_def:
  i2c_core_stretch_tx_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with stretch_tx := (¬s'.tx_fifo.rvalid ∨ 1w <+ s'.acq_fifo.depth)
End

Definition i2c_core_load_tcount_comb_def:
  i2c_core_load_tcount_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with load_tcount := (
    setupStart <=+ s.fsm_state ∧ s.fsm_state <=+ hostHoldBitAck ∧ s.counter = 1w
    ∨ s.fsm_state = active
    ∨ s.fsm_state = popFmtFifo
    ∨ s.fsm_state = addrRead ∧ s.bit_idx = 8w ∧ s'.address_match
    ∨ (s.fsm_state = addrAckPulse ∨ s.fsm_state = transmitPulse ∨ s.fsm_state = acquireAckPulse)
      ∧ ¬s.scl_sync
    ∨ (s.fsm_state = transmitWait ∨ s.fsm_state = stretchTx) ∧ ¬s'.stretch_tx
    ∨ s.fsm_state = transmitHold ∧ s.counter = 1w ∧ s.bit_idx ≠ 8w
    ∨ s.fsm_state = acquireByte ∧ s.bit_idx = 8w
    )
End

Definition fmt_byte_def:
  fmt_byte (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_byte :=
  if s'.fmt_fifo.rvalid then (7 >< 0) s'.fmt_fifo.rdata else 0w
End

Definition req_restart_def:
  req_restart (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with req_restart := ( ¬s'.fmt_flag.read_bytes ∧  s'.fmt_flag.start_before
                           ∧  s.fsm_state = active ∧  s.trans_started )
End

Definition bit_clr_def:
  bit_clr (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with bit_clr := ( (s.fsm_state = holdBit ∨ s.fsm_state = readHoldBit)
                       ∧  s.counter = 1w ∧ s.bit_index = 0w )
End

Definition bit_decr_def:
  bit_decr (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with bit_decr := ((s.fsm_state = holdBit ∨ s.fsm_state = readHoldBit)
                       ∧ s.counter = 1w ∧ s.bit_index ≠ 0w )
End

Definition i2c_core_stretch_en_comb_def:
  i2c_core_stretch_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with stretch_en := (s.fsm_state = clockPulse ∨  s.fsm_state = clockPulseAck
                         ∨  s.fsm_state = readClockPulse ∨  s.fsm_state = hostClockPulseAck)
End

Definition i2c_core_scl_d_comb_def:
  i2c_core_scl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_d := ¬( s.fsm_state = clockStart
                      ∨ s.fsm_state = clockLow
                      ∨ s.fsm_state = holdBit
                      ∨ s.fsm_state = clockLowAck
                      ∨ s.fsm_state = holdDevAck
                      ∨ s.fsm_state = readClockLow
                      ∨ s.fsm_state = readHoldBit
                      ∨ s.fsm_state = hostClockLowAck
                      ∨ s.fsm_state = hostHoldBitAck
                      ∨ s.fsm_state = clockStop
                      ∨ s.fsm_state = active ∧ (¬s'.fmt_flag.start_before ∨ s.trans_started)
                      ∨ s.fsm_state = popFmtFifo ∧ ¬s'.fmt_flag.stop_after
                      ∨ s.fsm_state = stretchAddr
                      ∨ s.fsm_state = stretchTx
                      ∨ s.fsm_state = stretchTxSetup
                      ∨ s.fsm_state = stretchAcqFull)
End

Definition i2c_core_sda_d_comb_def:
  i2c_core_sda_d_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with sda_d := ¬(
    s.fsm_state = holdStart
    ∨ s.fsm_state = clockStart
    (* The translator doesn't support indexing into regular words with
     * non-constants, so we have to use bitshifts. *)
    ∨ (s.fsm_state = clockLow ∨ s.fsm_state = clockPulse ∨ s.fsm_state = holdBit)
      ∧ (w2w (s'.fmt_byte >>>~ w2w s.bit_index): 1 word) = 0w
    ∨ (s.fsm_state = hostClockLowAck ∨ s.fsm_state = hostClockPulseAck ∨ s.fsm_state = hostHoldBitAck)
      ∧ (s'.fmt_flag.read_continue ∨ s.byte_index ≠ 1w)
    ∨ s.fsm_state = clockStop
    ∨ s.fsm_state = setupStop
    ∨ s.fsm_state = addrAckSetup
    ∨ s.fsm_state = addrAckPulse
    ∨ s.fsm_state = addrAckHold
    ∨ (s.fsm_state = transmitSetup ∨ s.fsm_state = stretchTxSetup)
      ∧ (w2w (s'.tx_fifo.rdata >>>~ (7w - w2w (w2w s.bit_idx: 3 word))): 1 word) = 0w
    ∨ (s.fsm_state = transmitPulse ∨ s.fsm_state = transmitHold) ∧ ¬s.sda_q
    ∨ s.fsm_state = acquireAckSetup
    ∨ s.fsm_state = acquireAckPulse
    ∨ s.fsm_state = acquireAckHold)
End

Definition i2c_core_scl_o_comb_def:
  i2c_core_scl_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_o := if s.regs.ovrd.txovrden = 1w then word_bit 0 s.regs.ovrd.sclval else s.scl_q
End

Definition i2c_core_sda_o_comb_def:
  i2c_core_sda_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with sda_o := if s.regs.ovrd.txovrden = 1w then word_bit 0 s.regs.ovrd.sdaval else s.sda_q
End

Definition i2c_core_cio_scl_o_comb_def:
  i2c_core_cio_scl_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with cio_scl_o := F
End

Definition i2c_core_cio_sda_o_comb_def:
  i2c_core_cio_sda_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with cio_sda_o := F
End

Definition i2c_core_cio_scl_en_o_comb_def:
  i2c_core_cio_scl_en_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with cio_scl_en_o := ¬s'.scl_o
End

Definition i2c_core_cio_sda_en_o_comb_def:
  i2c_core_cio_sda_en_o_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with cio_sda_en_o := ¬s'.sda_o
End

Definition i2c_core_next_scl_rx_val_comb_def:
  i2c_core_next_scl_rx_val_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if fext.cio_scl_i then
    s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w) || 1w
  else
    s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w)
End

Definition i2c_core_byte_clr_comb_def:
  i2c_core_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_clr := (s.fsm_state = active ∧ s'.fmt_flag.read_bytes)
End

Definition i2c_core_byte_decr_comb_def:
  i2c_core_byte_decr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_decr := (s.fsm_state = hostHoldBitAck ∧ s.counter = 1w ∧ s.byte_index ≠ 1w)
End

Definition i2c_core_byte_num_comb_def:
  i2c_core_byte_num_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if ¬s'.fmt_flag.read_bytes then s' with byte_num := 0w
  else if s'.fmt_byte = 0w then s' with byte_num := 256w
  else s' with byte_num := w2w s'.fmt_byte
End

Definition i2c_core_next_byte_index_comb_def:
  i2c_core_next_byte_index_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.byte_clr then s' with next_byte_index := s'.byte_num
  else if s'.byte_decr then s' with next_byte_index := s.byte_index - 1w
  else s' with next_byte_index := s.byte_index
End

Definition fifo_depth_def:
  fifo_depth (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.fmt_fifo.full then
    s' with fmt_fifo := s'.fmt_fifo with depth := 64w
  else if word_bit 6 s.fmt_fifo.wptr = word_bit 6 s.fmt_fifo.rptr then
    s' with fmt_fifo := s'.fmt_fifo with depth :=
    ((w2w ((5 >< 0) s.fmt_fifo.wptr : 6 word)) - (w2w ((5 >< 0) s.fmt_fifo.rptr : 6 word)))
  else
    s' with fmt_fifo := s'.fmt_fifo with depth :=
    64w - w2w ((5 >< 0) s.fmt_fifo.rptr : 6 word) + w2w ((5 >< 0) s.fmt_fifo.wptr :  6 word)
End

(* FIXME: fix the name *)        
Definition counter_gt_one_comb_def:
  counter_gt_one_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with cnt_gt_one := (s.counter ≠ 1w)
End

Definition i2c_core_next_state_def:
  i2c_core_next_state (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  let
    s' = case s.fsm_state of
      idle              => if s.regs.ctrl.enablehost = 1w ∧ s'.fmt_fifo.rvalid
                           then s' with next_state := active
                           else s' with next_state := idle
    | active            => if s'.fmt_flag.read_bytes then
                             s' with next_state := readClockLow
                           else if s'.fmt_flag.start_before ∧ ¬s.trans_started then
                             s' with next_state := setupStart
                           else
                             s' with next_state := clockLow

    | readClockLow      => if s'.cnt_gt_one then s' with next_state := readClockLow
                           else s' with next_state := readClockPulse

    | readClockPulse    => if s'.cnt_gt_one then s' with next_state := readClockPulse
                           else s' with next_state := readHoldBit

                           | readHoldBit       => if s'.cnt_gt_one then
                           s' with next_state := readHoldBit
                           else if s.bit_index = 0w then
                             s' with next_state := hostClockLowAck
                           else
                             s' with next_state := readClockLow

    | hostClockLowAck   => if s'.cnt_gt_one then s' with next_state := hostClockLowAck
                           else s' with next_state := hostClockPulseAck

    | hostClockPulseAck => if s'.cnt_gt_one then s' with next_state := hostClockPulseAck
                           else s' with next_state := hostHoldBitAck

    | hostHoldBitAck    => if s'.cnt_gt_one then
                             s' with next_state := hostHoldBitAck
                           else if s.byte_index = 1w ∧ s'.fmt_flag.stop_after then
                             s' with next_state := clockStop
                           else if s.byte_index = 1w ∧ ¬s'.fmt_flag.stop_after then
                             s' with next_state := popFmtFifo
                           else
                             s' with next_state := readClockLow

    | clockStop         => if s'.cnt_gt_one then s' with next_state := clockStop
                           else s' with next_state := setupStop

    | setupStop         => if s'.cnt_gt_one then s' with next_state := setupStop
                           else s' with next_state := holdStop

    | holdStop          => if s'.cnt_gt_one then s' with next_state := holdStop
                           else if s.regs.ctrl.enablehost = 0w then s' with next_state := idle
                           else s' with next_state := popFmtFifo

    | setupStart        => if s'.cnt_gt_one then s' with next_state := setupStart
                           else s' with next_state := holdStart

    | holdStart         => if s'.cnt_gt_one then s' with next_state := holdStart
                           else s' with next_state := clockStart

    | clockStart        => if s'.cnt_gt_one then s' with next_state := clockStart
                           else s' with next_state := clockLow

    | clockLow          => if s'.cnt_gt_one then s' with next_state := clockLow
                           else if s.pend_restart then s' with next_state := setupStart
                           else s' with next_state := clockPulse

    | clockPulse        => if s'.cnt_gt_one then s' with next_state := clockPulse
                           else s' with next_state := holdBit

    | holdBit           => if s'.cnt_gt_one then s' with next_state := holdBit
                           else if s.bit_index = 0w then s' with next_state := clockLowAck
                           else s' with next_state := clockLow

    | clockLowAck       => if s'.cnt_gt_one then s' with next_state := clockLowAck
                           else s' with next_state := clockPulseAck

    | clockPulseAck     => if s'.cnt_gt_one then s' with next_state := clockPulseAck
                           else s' with next_state := holdDevAck

    | holdDevAck        => if s'.cnt_gt_one then
                             s' with next_state := holdDevAck
                           else if s'.fmt_flag.stop_after then
                             s' with next_state := clockStop
                           else
                             s' with next_state := popFmtFifo

    | popFmtFifo        => if s.regs.ctrl.enablehost = 0w then s' with next_state := clockStop
                           else if s'.fmt_fifo.depth = 1w then s' with next_state := idle
                           else s' with next_state := active

    | acquireStart      => if s.scl_i_q /\ ~s.scl_sync then
                             s' with next_state := addrRead
                           else
                             s' with next_state := acquireStart

    | addrRead          => if s.bit_idx ≠ 8w then
                             s' with next_state := addrRead
                           else if s'.address_match then
                             s' with next_state := addrAckWait
                           else
                             s' with next_state := idle

    | addrAckWait       => if s.counter = 1w ∧ ~s.scl_sync then
                             s' with next_state := addrAckSetup
                           else
                             s' with next_state := addrAckWait

    | addrAckSetup      => if s.scl_sync then
                             s' with next_state := addrAckPulse
                           else
                             s' with next_state := addrAckSetup

    | addrAckPulse      => if ~s.scl_sync then
                             s' with next_state := addrAckHold
                           else
                             s' with next_state := addrAckPulse

    | addrAckHold       => if s.counter ≠ 1w then
                             s' with next_state := addrAckHold
                           else if ~s'.acq_fifo_2free then
                             s' with next_state := stretchAddr
                           else if s.rw_bit then
                             s' with next_state := transmitWait
                           else
                             s' with next_state := acquireByte

    | transmitWait      => if s'.stretch_tx then
                             s' with next_state := stretchTx
                           else
                             s' with next_state := transmitSetup

    | transmitSetup     => if s.scl_sync then
                             s' with next_state := transmitPulse
                           else
                             s' with next_state := transmitSetup

    | transmitPulse     => if ¬s.scl_sync then
                             s' with next_state := transmitHold
                           else
                             s' with next_state := transmitPulse

    | transmitHold      => if s.counter ≠ 1w then
                             s' with next_state := transmitHold
                           else if s.bit_idx = 8w then
                             s' with next_state := transmitAck
                           else
                             s' with next_state := transmitSetup

    | transmitAck       => if s.scl_sync then
                             s' with next_state := transmitAckPulse
                           else
                             s' with next_state := transmitAck

    | transmitAckPulse  => if s.scl_sync then
                             s' with next_state := transmitAckPulse
                           else if s.host_ack then
                             s' with next_state := transmitWait
                           else
                             s' with next_state := waitForStop

    | waitForStop       => s' with next_state := waitForStop

    | acquireByte       => if s.bit_idx = 8w then
                             s' with next_state := acquireAckWait
                           else
                             s' with next_state := acquireByte

    | acquireAckWait    => if s.counter = 1w ∧ ¬s.scl_sync then
                             s' with next_state := acquireAckSetup
                           else
                             s' with next_state := acquireAckWait

    | acquireAckSetup   => if s.scl_sync then
                             s' with next_state := acquireAckPulse
                           else
                             s' with next_state := acquireAckSetup

    | acquireAckPulse   => if ¬s.scl_sync then
                             s' with next_state := acquireAckHold
                           else
                             s' with next_state := acquireAckPulse

    | acquireAckHold    => if s.counter ≠ 1w then
                             s' with next_state := acquireAckHold
                           else if s'.acq_fifo_2free then
                             s' with next_state := acquireByte
                           else
                             s' with next_state := stretchAcqFull

    | stretchAddr       => if ¬s'.acq_fifo_2free then
                             s' with next_state := stretchAddr
                           else if s.rw_bit then
                             s' with next_state := stretchTx
                           else
                             s' with next_state := acquireByte

    | stretchTx         => if ¬s'.stretch_tx then
                             s' with next_state := stretchTxSetup
                           else
                             s' with next_state := stretchTx

    | stretchTxSetup    => if s.counter = 1w then
                             s' with next_state := transmitSetup
                           else
                             s' with next_state := stretchTxSetup

    | stretchAcqFull    => if s'.acq_fifo_2free then
                             s' with next_state := acquireByte
                           else
                             s' with next_state := stretchAcqFull

    | _ => s' with next_state := idle
  in
    if ~s'.target_idle /\ s.regs.ctrl.enabletarget = 0w then
      s' with next_state := idle
    else if s'.start_det then
      s' with next_state := acquireStart
    else if s'.stop_det then
      s' with next_state := idle
    else
      s'
End

Definition i2c_core_next_delay_comb_def:
  i2c_core_next_delay_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  case s.fsm_state of
  | setupStart        => s' with next_delay := s'.delay.hold_start
  | holdStart         => s' with next_delay := s'.delay.clock_start
  | clockStart        => s' with next_delay := s'.delay.clock_low
  | clockLow          => s' with next_delay := if s.pend_restart then s'.delay.setup_start else s'.delay.clock_pulse
  | clockPulse        => s' with next_delay := s'.delay.hold_bit
  | holdBit           => s' with next_delay := s'.delay.clock_low
  | clockLowAck       => s' with next_delay := s'.delay.clock_pulse
  | clockPulseAck     => s' with next_delay := s'.delay.hold_bit
  | holdDevAck        => s' with next_delay := if s'.fmt_flag.stop_after then s'.delay.clock_stop else 1w
  | readClockLow      => s' with next_delay := s'.delay.clock_pulse
  | readClockPulse    => s' with next_delay := s'.delay.hold_bit
  | readHoldBit       => s' with next_delay := s'.delay.clock_low
  | hostClockLowAck   => s' with next_delay := s'.delay.clock_pulse
  | hostClockPulseAck => s' with next_delay := s'.delay.hold_bit
  | hostHoldBitAck    =>
      if s.byte_index ≠ 1w then
        s' with next_delay := s'.delay.clock_low
      else if s'.fmt_flag.stop_after then
        s' with next_delay := s'.delay.clock_stop
      else
        s' with next_delay := 1w
  | clockStop         => s' with next_delay := s'.delay.setup_stop
  | setupStop         => s' with next_delay := s'.delay.hold_stop
  | holdStop          => s' with next_delay := 1w
  | active            =>
      if s'.fmt_flag.read_bytes ∨ ¬s'.fmt_flag.start_before ∨ s.trans_started then
        s' with next_delay := s'.delay.clock_low
      else
        s' with next_delay := s'.delay.setup_start
  | popFmtFifo        => s' with next_delay := if s.regs.ctrl.enablehost = 0w then s'.delay.clock_stop else 1w
  | addrRead          => s' with next_delay := s'.delay.clock_start
  | addrAckPulse      => s' with next_delay := s'.delay.clock_start
  | transmitWait      => s' with next_delay := s'.delay.clock_start
  | transmitPulse     => s' with next_delay := s'.delay.clock_start
  | transmitHold      => s' with next_delay := s'.delay.clock_start
  | acquireByte       => s' with next_delay := s'.delay.clock_start
  | acquireAckPulse   => s' with next_delay := s'.delay.clock_start
  | stretchTx         => s' with next_delay := s'.delay.setup_data
  | _                 => s' with next_delay := 1w
End

Definition i2c_core_next_counter_def:
  i2c_core_next_counter (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.load_tcount then s' with next_counter := s'.next_delay
  else if s.stretch_idle_cnt = 0w ∨ s.regs.ctrl.enabletarget = 1w then s' with next_counter := s.counter - 1w
  else s' with next_counter := s.counter
End

Definition i2c_core_read_byte_clr_comb_def:
  i2c_core_read_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with read_byte_clr := (s.fsm_state = readHoldBit ∧ s.counter = 1w ∧ s.bit_index = 0w)
End

Definition i2c_core_input_byte_clr_comb_def:
  i2c_core_input_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with input_byte_clr := (s.fsm_state = acquireStart ∧ s.scl_i_q ∧ ¬s.scl_sync)
End

Definition i2c_core_shift_data_en_comb_def:
  i2c_core_shift_data_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with shift_data_en := (s.fsm_state = readClockPulse ∧ s.counter = 1w)
End

Definition i2c_core_next_sda_rx_val_comb_def:
  i2c_core_next_sda_rx_val_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if fext.cio_sda_i then
    s' with next_sda_rx_val := (w2w s.sda_rx_val <<~ 1w) || 1w
  else
    s' with next_sda_rx_val := (w2w s.sda_rx_val <<~ 1w)
End

Definition i2c_core_next_read_byte_comb_def:
  i2c_core_next_read_byte_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.read_byte_clr then s' with next_read_byte := 0w
  else if s'.shift_data_en ∧ s.sda_sync then
    s' with next_read_byte := (w2w s.read_byte <<~ 1w) || 1w
  else if s'.shift_data_en ∧ ¬s.sda_sync then
    s' with next_read_byte := (w2w s.read_byte <<~ 1w)
  else
    s' with next_read_byte := s.read_byte
End

Definition i2c_core_rx_fifo_reset_comb_def:
  i2c_core_rx_fifo_reset_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with reset :=
  (word_bit 0 s.regs.fifo_ctrl.rxrst ∧ s.reg2hw.fifo_ctrl.rxrst_qe)
End

Definition i2c_core_rx_fifo_rready_comb_def:
  i2c_core_rx_fifo_rready_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with rready := s'.reg2hw.rdata.rdata_re
End

Definition i2c_core_rx_fifo_empty_comb_def:
  i2c_core_rx_fifo_empty_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with empty := (s.rx_fifo.rptr = s.rx_fifo.wptr)
End

Definition i2c_core_rx_fifo_rdata_comb_def:
  i2c_core_rx_fifo_rdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with rdata :=
  if s'.rx_fifo.empty then 0w else s.rx_fifo_regfile $ (5 >< 0) s.rx_fifo.rptr
End

Definition i2c_core_rx_fifo_rvalid_comb_def:
  i2c_core_rx_fifo_rvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with rvalid := ~s'.rx_fifo.empty
End

Definition i2c_core_rx_fifo_incr_rptr_comb_def:
  i2c_core_rx_fifo_incr_rptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with incr_rptr := (s'.rx_fifo.rvalid ∧ s'.rx_fifo.rready ∧ ¬s.under_rst)
End

Definition i2c_core_rx_fifo_counter_rptr_wrap_comb_def:
  i2c_core_rx_fifo_counter_rptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with rptr_wrap :=
  (s'.rx_fifo.incr_rptr ∧ (5 >< 0) s.rx_fifo.rptr = 63w : 6 word)
End

Definition i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def:
  i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.rx_fifo.rptr then (64w : 7 word) else 0w
End

Definition i2c_core_rx_fifo_rptr_ff_def:
  i2c_core_rx_fifo_rptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.rx_fifo.reset then
    s' with rx_fifo := s'.rx_fifo with rptr := 0w
  else if s'.rx_fifo.counter.rptr_wrap then
    s' with rx_fifo := s'.rx_fifo with rptr := s'.rx_fifo.counter.rptr_wrap_cnt
  else if s'.rx_fifo.incr_rptr then
    s' with rx_fifo := s'.rx_fifo with rptr := s.rx_fifo.rptr + 1w
  else
    s' with rx_fifo := s'.rx_fifo with rptr := s.rx_fifo.rptr    
End

Definition i2c_core_rx_fifo_wvalid_comb_def:
  i2c_core_rx_fifo_wvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with wvalid :=
  (s.fsm_state = readHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w)
End

Definition i2c_core_rx_fifo_wdata_comb_def:
  i2c_core_rx_fifo_wdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s.fsm_state = readHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w then
    s' with rx_fifo := s'.rx_fifo with wdata := s.read_byte
  else
    s' with rx_fifo := s'.rx_fifo with wdata := 0w
End

Definition i2c_core_rx_fifo_full_comb_def:
  i2c_core_rx_fifo_full_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with full :=
  ((word_bit 6 s.rx_fifo.wptr ≠ word_bit 6 s.rx_fifo.rptr) ∧
   ((5 >< 0) s.rx_fifo.wptr : 6 word = (5 >< 0) s.rx_fifo.rptr : 6 word))
End

Definition i2c_core_rx_fifo_wready_comb_def:
  i2c_core_rx_fifo_wready_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with wready := (~s'.rx_fifo.full /\ ~s.under_rst)
End

Definition i2c_core_rx_fifo_depth_comb_def:
  i2c_core_rx_fifo_depth_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.rx_fifo.full then
    s' with rx_fifo := s'.rx_fifo with depth := 64w
  else if word_bit 6 s.rx_fifo.wptr = word_bit 6 s.rx_fifo.rptr then
    s' with rx_fifo := s'.rx_fifo with depth :=
    ((w2w ((5 >< 0) s.rx_fifo.wptr : 6 word)) - (w2w ((5 >< 0) s.rx_fifo.rptr : 6 word)))
  else
    s' with rx_fifo := s'.rx_fifo with depth :=
    64w - w2w ((5 >< 0) s.rx_fifo.rptr : 6 word) + w2w ((5 >< 0) s.rx_fifo.wptr :  6 word)
End

Definition i2c_core_rx_fifo_incr_wptr_comb_def:
  i2c_core_rx_fifo_incr_wptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with incr_wptr := (s'.rx_fifo.wvalid ∧ s'.rx_fifo.wready ∧ ¬s.under_rst)
End

Definition i2c_core_rx_fifo_regfile_def:
  i2c_core_rx_fifo_regfile (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.rx_fifo.incr_wptr
  then s' with rx_fifo_regfile := ((5 >< 0) s.rx_fifo.wptr =+ s'.rx_fifo.wdata) s'.rx_fifo_regfile
  else s'
End

Definition i2c_core_rx_fifo_counter_wptr_wrap_comb_def:
  i2c_core_rx_fifo_counter_wptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with wptr_wrap :=
  (s'.rx_fifo.incr_wptr ∧ (5 >< 0) s.rx_fifo.wptr = 63w : 6 word)
End

Definition i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def:
  i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with wptr_wrap_cnt :=
  if ¬word_bit 6 s.rx_fifo.wptr then 64w else 0w
End

Definition i2c_core_rx_fifo_wptr_ff_def:
  i2c_core_rx_fifo_wptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.rx_fifo.reset then
    s' with rx_fifo := s'.rx_fifo with wptr := 0w
  else if s'.rx_fifo.counter.wptr_wrap then
    s' with rx_fifo := s'.rx_fifo with wptr := s'.rx_fifo.counter.wptr_wrap_cnt
  else if s'.rx_fifo.incr_wptr then
    s' with rx_fifo := s'.rx_fifo with wptr := s.rx_fifo.wptr + 1w
  else
    s' with rx_fifo := s'.rx_fifo with wptr := s.rx_fifo.wptr
End

Definition i2c_core_fmt_threshold_d_comb_def:
  i2c_core_fmt_threshold_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  case s.regs.fifo_ctrl.fmtilvl of
  | 0w => s' with fmt_threshold_d := (s'.fmt_fifo.depth <=+ 1w)
  | 1w => s' with fmt_threshold_d := (s'.fmt_fifo.depth <=+ 4w)
  | 2w => s' with fmt_threshold_d := (s'.fmt_fifo.depth <=+ 8w)
  | _ => s' with fmt_threshold_d := (s'.fmt_fifo.depth <=+ 16w)
End

Definition i2c_core_fmt_threshold_q_ff_def:
  i2c_core_fmt_threshold_q_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_threshold_q := s'.fmt_threshold_d
End

Definition i2c_core_rx_threshold_d_comb_def:
  i2c_core_rx_threshold_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  case s.regs.fifo_ctrl.rxilvl of
  | 0w => s' with rx_threshold_d := (1w <=+ s'.rx_fifo.depth)
  | 1w => s' with rx_threshold_d := (4w <=+ s'.rx_fifo.depth)
  | 2w => s' with rx_threshold_d := (8w <=+ s'.rx_fifo.depth)
  | 3w => s' with rx_threshold_d := (16w <=+ s'.rx_fifo.depth)
  | 4w => s' with rx_threshold_d := (30w <=+ s'.rx_fifo.depth)
  | _ => s' with rx_threshold_d := F
End

Definition i2c_core_rx_threshold_q_ff_def:
  i2c_core_rx_threshold_q_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_threshold_q := s'.rx_threshold_d
End

Definition i2c_core_en_sda_interf_det_comb_def:
  i2c_core_en_sda_interf_det_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with en_sda_interf_det :=
  ((s.fsm_state = clockLow ∨ s.fsm_state = clockPulse ∨ s.fsm_state = hostClockLowAck ∨ s.fsm_state = hostClockPulseAck)
    ∨ (s.fsm_state = holdBit ∨ s.fsm_state = hostHoldBitAck ∨ s.fsm_state = holdStop) ∧ s.counter ≠ 1w)
End

Definition i2c_core_sda_rise_cnt_ff_def:
  i2c_core_sda_rise_cnt_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if ¬s'.en_sda_interf_det then
    s' with sda_rise_cnt := 0w
  else if s.sda_rise_cnt <+ w2w s.regs.timing1.t_r + 2w then
    s' with sda_rise_cnt := s.sda_rise_cnt + 1w
  else
    s'
End

Definition i2c_core_expect_stop_comb_def:
  i2c_core_expect_stop_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with expect_stop := (s.fsm_state = waitForStop)
End

(*
Datatype:
  i2c_hw2reg_intr_state = <|
    fmt_threshold_d: 1 word;
    fmt_threshold_de: bool;
    rx_threshold_d: 1 word;
    rx_threshold_de: bool;
    fmt_overflow_d: 1 word;
    fmt_overflow_de: bool;
    rx_overflow_d: 1 word;
    rx_overflow_de: bool;
    nak_d: 1 word;
    nak_de: bool;
    scl_interference_d: 1 word;
    scl_interference_de: bool;
    sda_interference_d: 1 word;
    sda_interference_de: bool;
    stretch_timeout_d: 1 word;
    stretch_timeout_de: bool;
    sda_unstable_d: 1 word;
    sda_unstable_de: bool;
    cmd_complete_d: 1 word;
    cmd_complete_de: bool;
    tx_stretch_d: 1 word;
    tx_stretch_de: bool;
    tx_overflow_d: 1 word;
    tx_overflow_de: bool;
    acq_full_d: 1 word;
    acq_full_de: bool;
    unexp_stop_d: 1 word;
    unexp_stop_de: bool;
    host_timeout_d: 1 word;
    host_timeout_de: bool;
  |>
End
*)

Definition i2c_core_event_fmt_threshold_comb_def:
  i2c_core_event_fmt_threshold_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_fmt_threshold := (s'.fmt_threshold_d ∧ ¬s.fmt_threshold_q)
End

Definition i2c_core_event_rx_threshold_comb_def:
  i2c_core_event_rx_threshold_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_rx_threshold := (s'.rx_threshold_d ∧ ¬s.rx_threshold_q)
End

Definition i2c_core_event_fmt_overflow_comb_def:
  i2c_core_event_fmt_overflow_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_fmt_overflow := (s'.fmt_fifo.wvalid ∧ ¬s'.fmt_fifo.wready)
End

Definition i2c_core_event_rx_overflow_comb_def:
  i2c_core_event_rx_overflow_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_rx_overflow := (s'.rx_fifo.wvalid ∧ ¬s'.rx_fifo.wready)
End

Definition i2c_core_event_nak_comb_def:
  i2c_core_event_nak_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_nak := (s.fsm_state = clockPulseAck ∧ ¬s'.fmt_flag.nak_ok ∧ s.sda_sync)
End

Definition i2c_core_event_scl_interference_comb_def:
  i2c_core_event_scl_interference_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_scl_interference :=
    ((s.fsm_state = clockPulse ∨ s.fsm_state = clockPulseAck ∨ s.fsm_state = readClockPulse ∨ s.fsm_state = hostClockPulseAck)
      ∧ s.scl_i_q ∧ ¬s.scl_sync)
End

Definition i2c_core_event_sda_interference_comb_def:
  i2c_core_event_sda_interference_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_sda_interference :=
    (s'.host_idle ∧ s.regs.ctrl.enablehost = 1w ∧ ¬s.sda_sync
      ∨ s.sda_rise_cnt = w2w s.regs.timing1.t_r + 2w ∧ s.sda_q ∧ ¬s.sda_sync)
End

Definition i2c_core_event_stretch_timeout_comb_def:
  i2c_core_event_stretch_timeout_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_stretch_timeout := (s'.stretch_en ∧ s.regs.timeout_ctrl.val <+ ((30 >< 0) s.stretch_idle_cnt) ∧ word_bit 0 s.regs.timeout_ctrl.en)
End

Definition i2c_core_event_sda_unstable_comb_def:
  i2c_core_event_sda_unstable_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_sda_unstable :=
  ((s.fsm_state = clockPulse ∨ s.fsm_state = clockPulseAck ∨ s.fsm_state = readClockPulse ∨ s.fsm_state = hostClockPulseAck) ∧ s.sda_i_q ≠ s.sda_sync)
End

Definition i2c_core_event_cmd_complete_comb_def:
  i2c_core_event_cmd_complete_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.start_det ∨ s'.stop_det then
    s' with event_cmd_complete := ¬s'.target_idle
  else
    s' with event_cmd_complete := (s.fsm_state = holdStop ∨ s.fsm_state = setupStart ∧ s'.log_start ∧ s.pend_restart)
End

Definition i2c_core_event_tx_stretch_comb_def:
  i2c_core_event_tx_stretch_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_tx_stretch := (s.fsm_state = stretchTx ∧ s'.stretch_tx)
End

Definition i2c_core_event_tx_overflow_comb_def:
  i2c_core_event_tx_overflow_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_tx_overflow := (s'.tx_fifo.wvalid ∧ ¬s'.tx_fifo.wready)
End

Definition i2c_core_event_acq_full_comb_def:
  i2c_core_event_acq_full_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_acq_full := ¬s'.acq_fifo_2free
End

Definition i2c_core_event_unexp_stop_comb_def:
  i2c_core_event_unexp_stop_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_unexp_stop := (¬s'.target_idle ∧ s.rw_bit ∧ s'.stop_det ∧ ¬s'.expect_stop)
End

Definition i2c_core_event_host_timeout_comb_def:
  i2c_core_event_host_timeout_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with event_host_timeout := (¬s'.target_idle ∧ s.regs.host_timeout_ctrl.host_timeout_ctrl <+ s.stretch_idle_cnt)
End

Definition i2c_core_hw2reg_intr_state_fmt_threshold_de_comb_def:
  i2c_core_hw2reg_intr_state_fmt_threshold_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with fmt_threshold_de :=
  (s'.event_fmt_threshold ∨ s'.reg2hw.intr_test.fmt_threshold_qe ∧ word_bit 0 s'.reg2hw.intr_test.fmt_threshold_q)
End

Definition i2c_core_hw2reg_intr_state_fmt_threshold_d_comb_def:
  i2c_core_hw2reg_intr_state_fmt_threshold_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with fmt_threshold_d :=
  (* Strictly speaking, we could just set these to 1, since their value only
   * matters when `de` is true anyway. But doing it this way makes equivalence
   * checking a little easier, since we can just assert that the `d`s are always
   * equal. *)
  if s'.hw2reg.intr_state.fmt_threshold_de ∨ word_bit 0 s'.reg2hw.intr_state.fmt_threshold_q then 1w else 0w
End

Definition i2c_core_intr_fmt_threshold_o_ff_def:
  i2c_core_intr_fmt_threshold_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_fmt_threshold_o := (word_bit 0 s.regs.intr_state.fmt_threshold ∧ word_bit 0 s.regs.intr_enable.fmt_threshold)
End

Definition i2c_core_hw2reg_intr_state_rx_threshold_de_comb_def:
  i2c_core_hw2reg_intr_state_rx_threshold_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with rx_threshold_de :=
  (s'.event_rx_threshold ∨ s'.reg2hw.intr_test.rx_threshold_qe ∧ word_bit 0 s'.reg2hw.intr_test.rx_threshold_q)
End

Definition i2c_core_hw2reg_intr_state_rx_threshold_d_comb_def:
  i2c_core_hw2reg_intr_state_rx_threshold_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with rx_threshold_d :=
  if s'.hw2reg.intr_state.rx_threshold_de ∨ word_bit 0 s'.reg2hw.intr_state.rx_threshold_q then 1w else 0w
End

Definition i2c_core_intr_rx_threshold_o_ff_def:
  i2c_core_intr_rx_threshold_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_rx_threshold_o := (word_bit 0 s.regs.intr_state.rx_threshold ∧ word_bit 0 s.regs.intr_enable.rx_threshold)
End

Definition i2c_core_hw2reg_intr_state_fmt_overflow_de_comb_def:
  i2c_core_hw2reg_intr_state_fmt_overflow_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with fmt_overflow_de :=
  (s'.event_fmt_overflow ∨ s'.reg2hw.intr_test.fmt_overflow_qe ∧ word_bit 0 s'.reg2hw.intr_test.fmt_overflow_q)
End

Definition i2c_core_hw2reg_intr_state_fmt_overflow_d_comb_def:
  i2c_core_hw2reg_intr_state_fmt_overflow_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with fmt_overflow_d :=
  if s'.hw2reg.intr_state.fmt_overflow_de ∨ word_bit 0 s'.reg2hw.intr_state.fmt_overflow_q then 1w else 0w
End

Definition i2c_core_intr_fmt_overflow_o_ff_def:
  i2c_core_intr_fmt_overflow_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_fmt_overflow_o := (word_bit 0 s.regs.intr_state.fmt_overflow ∧ word_bit 0 s.regs.intr_enable.fmt_overflow)
End

Definition i2c_core_hw2reg_intr_state_rx_overflow_de_comb_def:
  i2c_core_hw2reg_intr_state_rx_overflow_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with rx_overflow_de :=
  (s'.event_rx_overflow ∨ s'.reg2hw.intr_test.rx_overflow_qe ∧ word_bit 0 s'.reg2hw.intr_test.rx_overflow_q)
End

Definition i2c_core_hw2reg_intr_state_rx_overflow_d_comb_def:
  i2c_core_hw2reg_intr_state_rx_overflow_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with rx_overflow_d :=
  if s'.hw2reg.intr_state.rx_overflow_de ∨ word_bit 0 s'.reg2hw.intr_state.rx_overflow_q then 1w else 0w
End

Definition i2c_core_intr_rx_overflow_o_ff_def:
  i2c_core_intr_rx_overflow_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_rx_overflow_o := (word_bit 0 s.regs.intr_state.rx_overflow ∧ word_bit 0 s.regs.intr_enable.rx_overflow)
End

Definition i2c_core_hw2reg_intr_state_nak_de_comb_def:
  i2c_core_hw2reg_intr_state_nak_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_de :=
  (s'.event_nak ∨ s'.reg2hw.intr_test.nak_qe ∧ word_bit 0 s'.reg2hw.intr_test.nak_q)
End

Definition i2c_core_hw2reg_intr_state_nak_d_comb_def:
  i2c_core_hw2reg_intr_state_nak_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_d :=
  if s'.hw2reg.intr_state.nak_de ∨ word_bit 0 s'.reg2hw.intr_state.nak_q then 1w else 0w
End

Definition i2c_core_intr_nak_o_ff_def:
  i2c_core_intr_nak_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_nak_o := (word_bit 0 s.regs.intr_state.nak ∧ word_bit 0 s.regs.intr_enable.nak)
End

Definition i2c_core_hw2reg_intr_state_scl_interference_de_comb_def:
  i2c_core_hw2reg_intr_state_scl_interference_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with scl_interference_de :=
  (s'.event_scl_interference ∨ s'.reg2hw.intr_test.scl_interference_qe ∧ word_bit 0 s'.reg2hw.intr_test.scl_interference_q)
End

Definition i2c_core_hw2reg_intr_state_scl_interference_d_comb_def:
  i2c_core_hw2reg_intr_state_scl_interference_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with scl_interference_d :=
  if s'.hw2reg.intr_state.scl_interference_de ∨ word_bit 0 s'.reg2hw.intr_state.scl_interference_q then 1w else 0w
End

Definition i2c_core_intr_scl_interference_o_ff_def:
  i2c_core_intr_scl_interference_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_scl_interference_o := (word_bit 0 s.regs.intr_state.scl_interference ∧ word_bit 0 s.regs.intr_enable.scl_interference)
End

Definition i2c_core_hw2reg_intr_state_sda_interference_de_comb_def:
  i2c_core_hw2reg_intr_state_sda_interference_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with sda_interference_de :=
  (s'.event_sda_interference ∨ s'.reg2hw.intr_test.sda_interference_qe ∧ word_bit 0 s'.reg2hw.intr_test.sda_interference_q)
End

Definition i2c_core_hw2reg_intr_state_sda_interference_d_comb_def:
  i2c_core_hw2reg_intr_state_sda_interference_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with sda_interference_d :=
  if s'.hw2reg.intr_state.sda_interference_de ∨ word_bit 0 s'.reg2hw.intr_state.sda_interference_q then 1w else 0w
End

Definition i2c_core_intr_sda_interference_o_ff_def:
  i2c_core_intr_sda_interference_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_sda_interference_o := (word_bit 0 s.regs.intr_state.sda_interference ∧ word_bit 0 s.regs.intr_enable.sda_interference)
End

Definition i2c_core_hw2reg_intr_state_stretch_timeout_de_comb_def:
  i2c_core_hw2reg_intr_state_stretch_timeout_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with stretch_timeout_de :=
  (s'.event_stretch_timeout ∨ s'.reg2hw.intr_test.stretch_timeout_qe ∧ word_bit 0 s'.reg2hw.intr_test.stretch_timeout_q)
End

Definition i2c_core_hw2reg_intr_state_stretch_timeout_d_comb_def:
  i2c_core_hw2reg_intr_state_stretch_timeout_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with stretch_timeout_d :=
  if s'.hw2reg.intr_state.stretch_timeout_de ∨ word_bit 0 s'.reg2hw.intr_state.stretch_timeout_q then 1w else 0w
End

Definition i2c_core_intr_stretch_timeout_o_ff_def:
  i2c_core_intr_stretch_timeout_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_stretch_timeout_o := (word_bit 0 s.regs.intr_state.stretch_timeout ∧ word_bit 0 s.regs.intr_enable.stretch_timeout)
End

Definition i2c_core_hw2reg_intr_state_sda_unstable_de_comb_def:
  i2c_core_hw2reg_intr_state_sda_unstable_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with sda_unstable_de :=
  (s'.event_sda_unstable ∨ s'.reg2hw.intr_test.sda_unstable_qe ∧ word_bit 0 s'.reg2hw.intr_test.sda_unstable_q)
End

Definition i2c_core_hw2reg_intr_state_sda_unstable_d_comb_def:
  i2c_core_hw2reg_intr_state_sda_unstable_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with sda_unstable_d :=
  if s'.hw2reg.intr_state.sda_unstable_de ∨ word_bit 0 s'.reg2hw.intr_state.sda_unstable_q then 1w else 0w
End

Definition i2c_core_intr_sda_unstable_o_ff_def:
  i2c_core_intr_sda_unstable_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_sda_unstable_o := (word_bit 0 s.regs.intr_state.sda_unstable ∧ word_bit 0 s.regs.intr_enable.sda_unstable)
End

Definition i2c_core_hw2reg_intr_state_cmd_complete_de_comb_def:
  i2c_core_hw2reg_intr_state_cmd_complete_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_de :=
  (s'.event_cmd_complete ∨ s'.reg2hw.intr_test.cmd_complete_qe ∧ word_bit 0 s'.reg2hw.intr_test.cmd_complete_q)
End

Definition i2c_core_hw2reg_intr_state_cmd_complete_d_comb_def:
  i2c_core_hw2reg_intr_state_cmd_complete_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_d :=
  if s'.hw2reg.intr_state.cmd_complete_de ∨ word_bit 0 s'.reg2hw.intr_state.cmd_complete_q then 1w else 0w
End

Definition i2c_core_intr_cmd_complete_o_ff_def:
  i2c_core_intr_cmd_complete_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_cmd_complete_o := (word_bit 0 s.regs.intr_state.cmd_complete ∧ word_bit 0 s.regs.intr_enable.cmd_complete)
End

Definition i2c_core_test_tx_stretch_ff_def:
  i2c_core_test_tx_stretch_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.reg2hw.intr_test.tx_stretch_qe then
    s' with test_tx_stretch := word_bit 0 s'.reg2hw.intr_test.tx_stretch_q
  else
    s'
End

Definition i2c_core_hw2reg_intr_state_tx_stretch_de_comb_def:
  i2c_core_hw2reg_intr_state_tx_stretch_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with tx_stretch_de := T
End

Definition i2c_core_hw2reg_intr_state_tx_stretch_d_comb_def:
  i2c_core_hw2reg_intr_state_tx_stretch_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with tx_stretch_d :=
  if s'.event_tx_stretch ∨ s.test_tx_stretch then 1w else 0w
End

Definition i2c_core_intr_tx_stretch_o_ff_def:
  i2c_core_intr_tx_stretch_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_tx_stretch_o := ((s'.event_tx_stretch ∨ s.test_tx_stretch) ∧ word_bit 0 s.regs.intr_enable.tx_stretch)
End

Definition i2c_core_hw2reg_intr_state_tx_overflow_de_comb_def:
  i2c_core_hw2reg_intr_state_tx_overflow_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with tx_overflow_de :=
  (s'.event_tx_overflow ∨ s'.reg2hw.intr_test.tx_overflow_qe ∧ word_bit 0 s'.reg2hw.intr_test.tx_overflow_q)
End

Definition i2c_core_hw2reg_intr_state_tx_overflow_d_comb_def:
  i2c_core_hw2reg_intr_state_tx_overflow_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with tx_overflow_d :=
  if s'.hw2reg.intr_state.tx_overflow_de ∨ word_bit 0 s'.reg2hw.intr_state.tx_overflow_q then 1w else 0w
End

Definition i2c_core_intr_tx_overflow_o_ff_def:
  i2c_core_intr_tx_overflow_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_tx_overflow_o := (word_bit 0 s.regs.intr_state.tx_overflow ∧ word_bit 0 s.regs.intr_enable.tx_overflow)
End

Definition i2c_core_test_acq_full_ff_def:
  i2c_core_test_acq_full_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.reg2hw.intr_test.acq_full_qe then
    s' with test_acq_full := word_bit 0 s'.reg2hw.intr_test.acq_full_q
  else
    s'
End

Definition i2c_core_hw2reg_intr_state_acq_full_de_comb_def:
  i2c_core_hw2reg_intr_state_acq_full_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with acq_full_de := T
End

Definition i2c_core_hw2reg_intr_state_acq_full_d_comb_def:
  i2c_core_hw2reg_intr_state_acq_full_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with acq_full_d :=
  if s'.event_acq_full ∨ s.test_acq_full then 1w else 0w
End

Definition i2c_core_intr_acq_full_o_ff_def:
  i2c_core_intr_acq_full_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_acq_full_o := ((s'.event_acq_full ∨ s.test_acq_full) ∧ word_bit 0 s.regs.intr_enable.acq_full)
End

Definition i2c_core_hw2reg_intr_state_unexp_stop_de_comb_def:
  i2c_core_hw2reg_intr_state_unexp_stop_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with unexp_stop_de :=
  (s'.event_unexp_stop ∨ s'.reg2hw.intr_test.unexp_stop_qe ∧ word_bit 0 s'.reg2hw.intr_test.unexp_stop_q)
End

Definition i2c_core_hw2reg_intr_state_unexp_stop_d_comb_def:
  i2c_core_hw2reg_intr_state_unexp_stop_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with unexp_stop_d :=
  if s'.hw2reg.intr_state.unexp_stop_de ∨ word_bit 0 s'.reg2hw.intr_state.unexp_stop_q then 1w else 0w
End

Definition i2c_core_intr_unexp_stop_o_ff_def:
  i2c_core_intr_unexp_stop_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_unexp_stop_o := (word_bit 0 s.regs.intr_state.unexp_stop ∧ word_bit 0 s.regs.intr_enable.unexp_stop)
End

Definition i2c_core_hw2reg_intr_state_host_timeout_de_comb_def:
  i2c_core_hw2reg_intr_state_host_timeout_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with host_timeout_de :=
  (s'.event_host_timeout ∨ s'.reg2hw.intr_test.host_timeout_qe ∧ word_bit 0 s'.reg2hw.intr_test.host_timeout_q)
End

Definition i2c_core_hw2reg_intr_state_host_timeout_d_comb_def:
  i2c_core_hw2reg_intr_state_host_timeout_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with host_timeout_d :=
  if s'.hw2reg.intr_state.host_timeout_de ∨ word_bit 0 s'.reg2hw.intr_state.host_timeout_q then 1w else 0w
End

Definition i2c_core_intr_host_timeout_o_ff_def:
  i2c_core_intr_host_timeout_o_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with intr_host_timeout_o := (word_bit 0 s.regs.intr_state.host_timeout ∧ word_bit 0 s.regs.intr_enable.host_timeout)
End

Definition i2c_core_next_stretch_idle_cnt_def:
  i2c_core_next_stretch_idle_cnt (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.stretch_en ∧ s'.scl_d ∧ ¬s.scl_sync ∨ ¬s'.target_idle ∧ ¬s'.event_host_timeout ∧ s.scl_sync
  then s' with next_stretch_idle_cnt := s.stretch_idle_cnt + 1w
  else s' with next_stretch_idle_cnt := 0w
End

Definition next_pend_restart_comb_def:
  next_pend_restart_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s.pend_restart ∧ s.regs.ctrl.enablehost = 0w then s' with next_pend_restart := F
  else if s'.req_restart then s' with next_pend_restart := T
  else if s'.log_start then s' with next_pend_restart := F
  else s' with next_pend_restart := s.pend_restart
End

Definition next_trans_started_comb_def:
  next_trans_started_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s.trans_started ∧ s.regs.ctrl.enablehost = 0w then s' with next_trans_started := F
  else if s'.log_start then s' with next_trans_started := T
  else if s'.log_stop then s' with next_trans_started := F
  else s' with next_trans_started := s.trans_started
End

Definition next_bit_index_comb_def:
  next_bit_index_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.bit_clr then s' with next_bit_index := 7w
  else if s'.bit_decr then s' with next_bit_index := s.bit_index - 1w
  else s' with next_bit_index := s.bit_index
End

(*
Datatype:
  i2c_hw2reg_status = <|
    fmtfull_d: 1 word;
    rxfull_d: 1 word;
    fmtempty_d: 1 word;
    hostidle_d: 1 word;
    targetidle_d: 1 word;
    rxempty_d: 1 word;
    txfull_d: 1 word;
    acqfull_d: 1 word;
    txempty_d: 1 word;
    acqempty_d: 1 word;
  |>
End

Datatype:
  i2c_hw2reg_rdata = <|
    rdata_d: 8 word;
  |>
End

Datatype:
  i2c_hw2reg_fifo_status = <|
    fmtlvl_d: 7 word;
    txlvl_d: 7 word;
    rxlvl_d: 7 word;
    acqlvl_d: 7 word;
  |>
End

Datatype:
  i2c_hw2reg_val = <|
    scl_rx_d: 16 word;
    sda_rx_d: 16 word;
  |>
End

Datatype:
  i2c_hw2reg_acqdata = <|
    abyte_d: 8 word;
    signal_d: 2 word;
  |>
End
*)

Definition i2c_core_status_fmtfull_d_comb_def:
  i2c_core_status_fmtfull_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with fmtfull_d := if s'.fmt_fifo.wready then 0w else 1w
End

Definition i2c_core_status_rxfull_d_comb_def:
  i2c_core_status_rxfull_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with rxfull_d := if s'.rx_fifo.wready then 0w else 1w
End

Definition i2c_core_status_fmtempty_d_comb_def:
  i2c_core_status_fmtempty_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with fmtempty_d := if s'.fmt_fifo.rvalid then 0w else 1w
End

Definition i2c_core_status_hostidle_d_comb_def:
  i2c_core_status_hostidle_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with hostidle_d := if s'.host_idle then 1w else 0w
End

Definition i2c_core_status_targetidle_d_comb_def:
  i2c_core_status_targetidle_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with targetidle_d := if s'.target_idle then 1w else 0w
End

Definition i2c_core_status_rxempty_d_comb_def:
  i2c_core_status_rxempty_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with rxempty_d := if s'.rx_fifo.rvalid then 0w else 1w
End

Definition i2c_core_rdata_rdata_d_comb_def:
  i2c_core_rdata_rdata_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with rdata := s'.hw2reg.rdata with rdata_d := s'.rx_fifo.rdata
End

Definition i2c_core_fifo_status_fmtlvl_d_comb_def:
  i2c_core_fifo_status_fmtlvl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with fifo_status := s'.hw2reg.fifo_status with fmtlvl_d := s'.fmt_fifo.depth
End

Definition i2c_core_fifo_status_rxlvl_d_comb_def:
  i2c_core_fifo_status_rxlvl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with fifo_status := s'.hw2reg.fifo_status with rxlvl_d := s'.rx_fifo.depth
End

Definition i2c_core_val_scl_rx_d_comb_def:
  i2c_core_val_scl_rx_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with val := s'.hw2reg.val with scl_rx_d := s.scl_rx_val
End

Definition i2c_core_val_sda_rx_d_comb_def:
  i2c_core_val_sda_rx_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with val := s'.hw2reg.val with sda_rx_d := s.sda_rx_val
End

Definition i2c_core_status_txfull_d_comb_def:
  i2c_core_status_txfull_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with txfull_d := if s'.tx_fifo.wready then 0w else 1w
End

Definition i2c_core_status_acqfull_d_comb_def:
  i2c_core_status_acqfull_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with acqfull_d := if s'.acq_fifo_2free then 0w else 1w
End

Definition i2c_core_status_txempty_d_comb_def:
  i2c_core_status_txempty_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with txempty_d := if s'.tx_fifo.rvalid then 0w else 1w
End

Definition i2c_core_status_acqempty_d_comb_def:
  i2c_core_status_acqempty_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with status := s'.hw2reg.status with acqempty_d := if s'.acq_fifo.rvalid then 0w else 1w
End

Definition i2c_core_fifo_status_txlvl_d_comb_def:
  i2c_core_fifo_status_txlvl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with fifo_status := s'.hw2reg.fifo_status with txlvl_d := s'.tx_fifo.depth
End

Definition i2c_core_fifo_status_acqlvl_d_comb_def:
  i2c_core_fifo_status_acqlvl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with fifo_status := s'.hw2reg.fifo_status with acqlvl_d := s'.acq_fifo.depth
End

Definition i2c_core_acqdata_abyte_d_comb_def:
  i2c_core_acqdata_abyte_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with acqdata := s'.hw2reg.acqdata with abyte_d := (7 >< 0) s'.acq_fifo.rdata
End

Definition i2c_core_acqdata_signal_d_comb_def:
  i2c_core_acqdata_signal_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with acqdata := s'.hw2reg.acqdata with signal_d := (9 >< 8) s'.acq_fifo.rdata
End

Definition i2c_core_sync_ff_def:
  i2c_core_sync_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  let
    s' = s' with scl_buf := fext.cio_scl_i;
    s' = s' with sda_buf := fext.cio_sda_i;
    s' = s' with scl_sync := s.scl_buf;
    s' = s' with sda_sync := s.sda_buf;
  in
    s'
End

Definition i2c_core_scl_q_ff_def:
  i2c_core_scl_q_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_q := s'.scl_d
End

Definition i2c_core_sda_q_ff_def:
  i2c_core_sda_q_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with sda_q := s'.sda_d
End

Definition i2c_core_ff_def:
  i2c_core_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fsm_state := s'.next_state
End

Definition i2c_core_counter_ff_def:
  i2c_core_counter_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with counter := s'.next_counter
End

Definition i2c_core_stretch_idle_cnt_ff_def:
  i2c_core_stretch_idle_cnt_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with stretch_idle_cnt := s'.next_stretch_idle_cnt
End

Definition bit_index_ff_def:
  bit_index_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with bit_index := s'.next_bit_index
End

Definition i2c_core_bit_idx_ff_def:
  i2c_core_bit_idx_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.start_det then
    s' with bit_idx := 0w
  else if s.scl_i_q ∧ ¬s.scl_sync then
    if s'.input_byte_clr ∨ s.bit_idx = 8w then
      s' with bit_idx := 0w
    else
      s' with bit_idx := s.bit_idx + 1w
  else
    s'
End

Definition pend_restart_ff_def:
  pend_restart_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with pend_restart := s'.next_pend_restart
End

Definition trans_started_ff_def:
  trans_started_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with trans_started := s'.next_trans_started
End
        

Definition byte_index_ff_def:
  byte_index_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_index := s'.next_byte_index
End

Definition read_byte_ff_def:
  read_byte_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with read_byte := s'.next_read_byte
End

Definition i2c_core_input_byte_ff_def:
  i2c_core_input_byte_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.input_byte_clr then
    s' with input_byte := 0w
  else if ¬s.scl_i_q ∧ s.scl_sync ∧ s.bit_idx ≠ 8w then
    s' with input_byte := ((6 >< 0) s.input_byte: 7 word) @@ (if s.sda_sync then 1w else 0w: word1)
  else
    s'
End
        
Definition scl_rx_val_ff_def:
  scl_rx_val_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_rx_val := s'.next_scl_rx_val
End

Definition sda_rx_val_ff_def:
  sda_rx_val_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with sda_rx_val := s'.next_sda_rx_val
End

Definition scl_i_q_ff_def:
  scl_i_q_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_i_q := s.scl_sync
End

Definition sda_i_q_ff_def:
  sda_i_q_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with sda_i_q := s.sda_sync
End

Definition i2c_core_under_rst_ff_def:
  i2c_core_under_rst_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with under_rst := F
End

Definition i2c_core_rw_bit_ff_def:
  i2c_core_rw_bit_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s.bit_idx = 8w ∧ s'.address_match ∧ s.fsm_state = addrRead then
    s' with rw_bit := word_bit 0 s.input_byte
  else
    s'
End

Definition i2c_core_host_ack_ff_def:
  i2c_core_host_ack_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if ¬s.scl_i_q ∧ s.scl_sync ∧ s.bit_idx = 8w then
    s' with host_ack := ¬s.sda_sync
  else
    s'
End
        
val init_tm = add_x_inits ``
  <|
    intr_fmt_threshold_o := F;
    intr_rx_threshold_o := F;
    intr_fmt_overflow_o := F;
    intr_rx_overflow_o := F;
    intr_nak_o := F;
    intr_scl_interference_o := F;
    intr_sda_interference_o := F;
    intr_stretch_timeout_o := F;
    intr_sda_unstable_o := F;
    intr_cmd_complete_o := F;
    intr_tx_stretch_o := F;
    intr_tx_overflow_o := F;
    intr_acq_full_o := F;
    intr_unexp_stop_o := F;
    intr_host_timeout_o := F;
    regs := ^i2c_regs_init_tm;
    reg2hw := ^i2c_reg2hw_init_tm;
    scl_buf := T;
    sda_buf := T;
    scl_sync := T;
    sda_sync := T;
    fsm_state := idle;
    counter := 0xfffffw;
    byte_index := 0w;
    bit_index := 7w;
    pend_restart := F;
    trans_started := F;
    scl_rx_val := 0w;
    stretch_idle_cnt := 0w;
    scl_q := T;
    sda_q := T;
    sda_rx_val := 0w;
    read_byte := 0w;
    sda_rise_cnt := 0w;
    under_rst := T;
    fmt_fifo := <|
      rptr := 0w;
      wptr := 0w;
    |>;
    rx_fifo := <|
      rptr := 0w;
      wptr := 0w;
    |>;
    tx_fifo := <|
      rptr := 0w;
      wptr := 0w;
    |>;
    acq_fifo := <|
      rptr := 0w;
      wptr := 0w;
    |>;
    fmt_threshold_q := T;
    rx_threshold_q := F;
    scl_i_q := T;
    sda_i_q := T;
    input_byte := 0w;
    bit_idx := 0w;
    rw_bit := F;
    host_ack := F;
    test_tx_stretch := F;
    test_acq_full := F;
  |>
``;

Definition i2c_circuit_init_def:
  i2c_circuit_init fbits = ^init_tm
End

Definition i2c_core_ffs1_def:
  i2c_core_ffs1 = [
    fmt_fifo_rptr_ff; fmt_fifo_regfile_ff; fmt_fifo_wptr_ff;
    i2c_core_tx_fifo_rptr_ff; i2c_core_tx_fifo_regfile; i2c_core_tx_fifo_wptr_ff;
    i2c_core_acq_fifo_rptr_ff; i2c_core_acq_fifo_regfile; i2c_core_acq_fifo_wptr_ff;
    i2c_core_rx_fifo_rptr_ff; i2c_core_rx_fifo_regfile; i2c_core_rx_fifo_wptr_ff;
    i2c_core_fmt_threshold_q_ff; i2c_core_rx_threshold_q_ff;
    i2c_core_sda_rise_cnt_ff; i2c_core_intr_fmt_threshold_o_ff;
    i2c_core_intr_rx_threshold_o_ff; i2c_core_intr_fmt_overflow_o_ff;
    i2c_core_intr_rx_overflow_o_ff; i2c_core_intr_nak_o_ff;
    i2c_core_intr_scl_interference_o_ff; i2c_core_intr_sda_interference_o_ff;
    i2c_core_intr_stretch_timeout_o_ff; i2c_core_intr_sda_unstable_o_ff;
    i2c_core_intr_cmd_complete_o_ff; i2c_core_test_tx_stretch_ff;
    i2c_core_intr_tx_stretch_o_ff; i2c_core_intr_tx_overflow_o_ff;
    i2c_core_test_acq_full_ff; i2c_core_intr_acq_full_o_ff;
    i2c_core_intr_unexp_stop_o_ff; i2c_core_intr_host_timeout_o_ff;
    i2c_core_sync_ff; i2c_core_scl_q_ff; i2c_core_sda_q_ff; i2c_core_ff;
    i2c_core_counter_ff; i2c_core_stretch_idle_cnt_ff; bit_index_ff;
    i2c_core_bit_idx_ff; pend_restart_ff; trans_started_ff; byte_index_ff;
    read_byte_ff; i2c_core_input_byte_ff; scl_rx_val_ff; sda_rx_val_ff; scl_i_q_ff;
    sda_i_q_ff; i2c_core_under_rst_ff; i2c_core_rw_bit_ff; i2c_core_host_ack_ff
  ]
End

Definition i2c_core_combs_def:
  i2c_core_combs = [
    i2c_core_target_loopback_comb; i2c_core_start_det_comb; i2c_core_stop_det_comb;
    i2c_core_address_match_comb; i2c_core_target_idle_comb; i2c_core_host_idle_comb;
    fmt_fifo_reset; fmt_fifo_rready; fmt_fifo_empty; fmt_fifo_rdata;
    fmt_fifo_rvalid; fmt_fifo_incr_rptr; fmt_fifo_counter_rptr_wrap;
    fmt_fifo_counter_rptr_wrap_cnt; fmt_fifo_wvalid; fmt_fifo_full; fmt_fifo_wready;
    fmt_fifo_incr_wptr; fmt_fifo_wdata; fmt_fifo_counter_wptr_wrap;
    fmt_fifo_counter_wptr_wrap_cnt; i2c_core_delay_comb; i2c_core_log_start_comb;
    i2c_core_log_stop_comb; fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after;
    fmt_fifo_flag_read_bytes; fmt_fifo_flag_read_continue; fmt_fifo_flag_nak_ok;
    i2c_core_tx_fifo_empty_comb; i2c_core_tx_fifo_rdata_comb;
    i2c_core_tx_fifo_rvalid_comb; i2c_core_tx_fifo_full_comb;
    i2c_core_tx_fifo_wready_comb; i2c_core_tx_fifo_depth_comb;
    i2c_core_acq_fifo_empty_comb; i2c_core_acq_fifo_rdata_comb;
    i2c_core_acq_fifo_rvalid_comb; i2c_core_acq_fifo_full_comb;
    i2c_core_acq_fifo_wready_comb; i2c_core_acq_fifo_depth_comb;
    i2c_core_acq_fifo_2free_comb; i2c_core_tx_fifo_reset_comb;
    i2c_core_tx_fifo_rready_comb; i2c_core_tx_fifo_wvalid_comb;
    i2c_core_tx_fifo_wdata_comb; i2c_core_tx_fifo_incr_rptr_comb;
    i2c_core_tx_fifo_counter_rptr_wrap_comb;
    i2c_core_tx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_tx_fifo_incr_wptr_comb;
    i2c_core_tx_fifo_counter_wptr_wrap_comb;
    i2c_core_tx_fifo_counter_wptr_wrap_cnt_comb; i2c_core_acq_fifo_reset_comb;
    i2c_core_acq_fifo_rready_comb; i2c_core_acq_fifo_wvalid_comb;
    i2c_core_acq_fifo_wdata_comb; i2c_core_acq_fifo_incr_rptr_comb;
    i2c_core_acq_fifo_counter_rptr_wrap_comb;
    i2c_core_acq_fifo_counter_rptr_wrap_cnt_comb; i2c_core_acq_fifo_incr_wptr_comb;
    i2c_core_acq_fifo_counter_wptr_wrap_comb;
    i2c_core_acq_fifo_counter_wptr_wrap_cnt_comb; i2c_core_stretch_tx_comb;
    i2c_core_load_tcount_comb; fmt_byte; req_restart; bit_clr; bit_decr;
    i2c_core_stretch_en_comb; i2c_core_scl_d_comb; i2c_core_sda_d_comb;
    i2c_core_scl_o_comb; i2c_core_sda_o_comb; i2c_core_cio_scl_o_comb;
    i2c_core_cio_sda_o_comb; i2c_core_cio_scl_en_o_comb; i2c_core_cio_sda_en_o_comb;
    i2c_core_next_scl_rx_val_comb; i2c_core_byte_clr_comb; i2c_core_byte_decr_comb;
    i2c_core_byte_num_comb; i2c_core_next_byte_index_comb; fifo_depth;
    counter_gt_one_comb; i2c_core_next_state; i2c_core_next_delay_comb;
    i2c_core_next_counter; i2c_core_read_byte_clr_comb;
    i2c_core_input_byte_clr_comb; i2c_core_shift_data_en_comb;
    i2c_core_next_sda_rx_val_comb; i2c_core_next_read_byte_comb;
    i2c_core_rx_fifo_reset_comb; i2c_core_rx_fifo_rready_comb;
    i2c_core_rx_fifo_empty_comb; i2c_core_rx_fifo_rdata_comb;
    i2c_core_rx_fifo_rvalid_comb; i2c_core_rx_fifo_incr_rptr_comb;
    i2c_core_rx_fifo_counter_rptr_wrap_comb;
    i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_rx_fifo_wvalid_comb;
    i2c_core_rx_fifo_wdata_comb; i2c_core_rx_fifo_full_comb;
    i2c_core_rx_fifo_wready_comb; i2c_core_rx_fifo_depth_comb;
    i2c_core_rx_fifo_incr_wptr_comb; i2c_core_rx_fifo_counter_wptr_wrap_comb;
    i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb; i2c_core_fmt_threshold_d_comb;
    i2c_core_rx_threshold_d_comb; i2c_core_en_sda_interf_det_comb;
    i2c_core_expect_stop_comb; i2c_core_event_fmt_threshold_comb;
    i2c_core_event_rx_threshold_comb; i2c_core_event_fmt_overflow_comb;
    i2c_core_event_rx_overflow_comb; i2c_core_event_nak_comb;
    i2c_core_event_scl_interference_comb; i2c_core_event_sda_interference_comb;
    i2c_core_event_stretch_timeout_comb; i2c_core_event_sda_unstable_comb;
    i2c_core_event_cmd_complete_comb; i2c_core_event_tx_stretch_comb;
    i2c_core_event_tx_overflow_comb; i2c_core_event_acq_full_comb;
    i2c_core_event_unexp_stop_comb; i2c_core_event_host_timeout_comb;
    i2c_core_hw2reg_intr_state_fmt_threshold_de_comb;
    i2c_core_hw2reg_intr_state_fmt_threshold_d_comb;
    i2c_core_hw2reg_intr_state_rx_threshold_de_comb;
    i2c_core_hw2reg_intr_state_rx_threshold_d_comb;
    i2c_core_hw2reg_intr_state_fmt_overflow_de_comb;
    i2c_core_hw2reg_intr_state_fmt_overflow_d_comb;
    i2c_core_hw2reg_intr_state_rx_overflow_de_comb;
    i2c_core_hw2reg_intr_state_rx_overflow_d_comb;
    i2c_core_hw2reg_intr_state_nak_de_comb; i2c_core_hw2reg_intr_state_nak_d_comb;
    i2c_core_hw2reg_intr_state_scl_interference_de_comb;
    i2c_core_hw2reg_intr_state_scl_interference_d_comb;
    i2c_core_hw2reg_intr_state_sda_interference_de_comb;
    i2c_core_hw2reg_intr_state_sda_interference_d_comb;
    i2c_core_hw2reg_intr_state_stretch_timeout_de_comb;
    i2c_core_hw2reg_intr_state_stretch_timeout_d_comb;
    i2c_core_hw2reg_intr_state_sda_unstable_de_comb;
    i2c_core_hw2reg_intr_state_sda_unstable_d_comb;
    i2c_core_hw2reg_intr_state_cmd_complete_de_comb;
    i2c_core_hw2reg_intr_state_cmd_complete_d_comb;
    i2c_core_hw2reg_intr_state_tx_stretch_de_comb;
    i2c_core_hw2reg_intr_state_tx_stretch_d_comb;
    i2c_core_hw2reg_intr_state_tx_overflow_de_comb;
    i2c_core_hw2reg_intr_state_tx_overflow_d_comb;
    i2c_core_hw2reg_intr_state_acq_full_de_comb;
    i2c_core_hw2reg_intr_state_acq_full_d_comb;
    i2c_core_hw2reg_intr_state_unexp_stop_de_comb;
    i2c_core_hw2reg_intr_state_unexp_stop_d_comb;
    i2c_core_hw2reg_intr_state_host_timeout_de_comb;
    i2c_core_hw2reg_intr_state_host_timeout_d_comb; i2c_core_next_stretch_idle_cnt;
    next_pend_restart_comb; next_trans_started_comb; next_bit_index_comb;
    i2c_core_status_fmtfull_d_comb; i2c_core_status_rxfull_d_comb;
    i2c_core_status_fmtempty_d_comb; i2c_core_status_hostidle_d_comb;
    i2c_core_status_targetidle_d_comb; i2c_core_status_rxempty_d_comb;
    i2c_core_rdata_rdata_d_comb; i2c_core_fifo_status_fmtlvl_d_comb;
    i2c_core_fifo_status_rxlvl_d_comb; i2c_core_val_scl_rx_d_comb;
    i2c_core_val_sda_rx_d_comb; i2c_core_status_txfull_d_comb;
    i2c_core_status_acqfull_d_comb; i2c_core_status_txempty_d_comb;
    i2c_core_status_acqempty_d_comb; i2c_core_fifo_status_txlvl_d_comb;
    i2c_core_fifo_status_acqlvl_d_comb; i2c_core_acqdata_abyte_d_comb;
    i2c_core_acqdata_signal_d_comb
  ]
End

Definition i2c_circuit_def:
  i2c_circuit = mk_module
                (procs (i2c_core_ffs1 ++ [i2c_reg_top_ff] ++ []))
                (procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]))
                i2c_circuit_init
End

Theorem ff_asm1:
  flip EVERY i2c_core_ffs1
       (λproc.
          let
            s'' = proc fext s s'
          in
            s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧ s''.reg_rsp_o = s'.reg_rsp_o
            ∧ s''.raw_addr = s'.raw_addr ∧ s''.addr = s'.addr ∧ s''.write = s'.write
            ∧ s''.wdata = s'.wdata ∧ s''.wstrb = s'.wstrb ∧ s''.valid = s'.valid
            ∧ s''.error = s'.error ∧ s''.win_buses.req = s'.win_buses.req)
Proof
  LET_ELIM_TAC
  >> rw [i2c_core_ffs1_def]
  >> rw [Abbr ‘s''’, fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, fmt_fifo_wptr_ff_def,
         i2c_core_tx_fifo_rptr_ff_def, i2c_core_tx_fifo_regfile_def,
         i2c_core_tx_fifo_wptr_ff_def, i2c_core_acq_fifo_rptr_ff_def,
         i2c_core_acq_fifo_regfile_def, i2c_core_acq_fifo_wptr_ff_def,
         i2c_core_rx_fifo_rptr_ff_def, i2c_core_rx_fifo_regfile_def,
         i2c_core_rx_fifo_wptr_ff_def, i2c_core_fmt_threshold_q_ff_def,
         i2c_core_rx_threshold_q_ff_def, i2c_core_sda_rise_cnt_ff_def,
         i2c_core_intr_fmt_threshold_o_ff_def, i2c_core_intr_rx_threshold_o_ff_def,
         i2c_core_intr_fmt_overflow_o_ff_def, i2c_core_intr_rx_overflow_o_ff_def,
         i2c_core_intr_nak_o_ff_def, i2c_core_intr_scl_interference_o_ff_def,
         i2c_core_intr_sda_interference_o_ff_def, i2c_core_intr_stretch_timeout_o_ff_def,
         i2c_core_intr_sda_unstable_o_ff_def, i2c_core_intr_cmd_complete_o_ff_def,
         i2c_core_test_tx_stretch_ff_def, i2c_core_intr_tx_stretch_o_ff_def,
         i2c_core_intr_tx_overflow_o_ff_def, i2c_core_test_acq_full_ff_def,
         i2c_core_intr_acq_full_o_ff_def, i2c_core_intr_unexp_stop_o_ff_def,
         i2c_core_intr_host_timeout_o_ff_def, i2c_core_sync_ff_def,
         i2c_core_scl_q_ff_def, i2c_core_sda_q_ff_def, i2c_core_ff_def,
         i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def, bit_index_ff_def,
         i2c_core_bit_idx_ff_def, pend_restart_ff_def, trans_started_ff_def,
         byte_index_ff_def, read_byte_ff_def, i2c_core_input_byte_ff_def,
         scl_rx_val_ff_def, sda_rx_val_ff_def, scl_i_q_ff_def, sda_i_q_ff_def,
         i2c_core_under_rst_ff_def, i2c_core_rw_bit_ff_def, i2c_core_host_ack_ff_def]
QED

Theorem ff_asm2:
  EVERY (λproc. (proc fext s s').hw2reg = s'.hw2reg) i2c_core_ffs1
Proof
  rw [i2c_core_ffs1_def]
  >> rw [fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, fmt_fifo_wptr_ff_def,
         i2c_core_tx_fifo_rptr_ff_def, i2c_core_tx_fifo_regfile_def,
         i2c_core_tx_fifo_wptr_ff_def, i2c_core_acq_fifo_rptr_ff_def,
         i2c_core_acq_fifo_regfile_def, i2c_core_acq_fifo_wptr_ff_def,
         i2c_core_rx_fifo_rptr_ff_def, i2c_core_rx_fifo_regfile_def,
         i2c_core_rx_fifo_wptr_ff_def, i2c_core_fmt_threshold_q_ff_def,
         i2c_core_rx_threshold_q_ff_def, i2c_core_sda_rise_cnt_ff_def,
         i2c_core_intr_fmt_threshold_o_ff_def, i2c_core_intr_rx_threshold_o_ff_def,
         i2c_core_intr_fmt_overflow_o_ff_def, i2c_core_intr_rx_overflow_o_ff_def,
         i2c_core_intr_nak_o_ff_def, i2c_core_intr_scl_interference_o_ff_def,
         i2c_core_intr_sda_interference_o_ff_def, i2c_core_intr_stretch_timeout_o_ff_def,
         i2c_core_intr_sda_unstable_o_ff_def, i2c_core_intr_cmd_complete_o_ff_def,
         i2c_core_test_tx_stretch_ff_def, i2c_core_intr_tx_stretch_o_ff_def,
         i2c_core_intr_tx_overflow_o_ff_def, i2c_core_test_acq_full_ff_def,
         i2c_core_intr_acq_full_o_ff_def, i2c_core_intr_unexp_stop_o_ff_def,
         i2c_core_intr_host_timeout_o_ff_def, i2c_core_sync_ff_def,
         i2c_core_scl_q_ff_def, i2c_core_sda_q_ff_def, i2c_core_ff_def,
         i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def, bit_index_ff_def,
         i2c_core_bit_idx_ff_def, pend_restart_ff_def, trans_started_ff_def,
         byte_index_ff_def, read_byte_ff_def, i2c_core_input_byte_ff_def,
         scl_rx_val_ff_def, sda_rx_val_ff_def, scl_i_q_ff_def, sda_i_q_ff_def,
         i2c_core_under_rst_ff_def, i2c_core_rw_bit_ff_def, i2c_core_host_ack_ff_def]
QED

Theorem comb_asm1:
  flip EVERY i2c_core_combs
       (λproc.
          let
            s'' = proc fext s s'
          in
            s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧ s''.reg_rsp_o = s'.reg_rsp_o
            ∧ s''.raw_addr = s'.raw_addr ∧ s''.addr = s'.addr ∧ s''.write = s'.write
            ∧ s''.wdata = s'.wdata ∧ s''.wstrb = s'.wstrb ∧ s''.valid = s'.valid
            ∧ s''.error = s'.error ∧ s''.win_buses.req = s'.win_buses.req)
Proof
  LET_ELIM_TAC
  >> rw [i2c_core_combs_def]
  >> rw [Abbr ‘s''’, i2c_core_target_loopback_comb_def, i2c_core_start_det_comb_def,
         i2c_core_stop_det_comb_def, i2c_core_address_match_comb_def,
         i2c_core_target_idle_comb_def, i2c_core_host_idle_comb_def, fmt_fifo_reset_def,
         fmt_fifo_rready_def, fmt_fifo_empty_def, fmt_fifo_rdata_def,
         fmt_fifo_rvalid_def, fmt_fifo_incr_rptr_def, fmt_fifo_counter_rptr_wrap_def,
         fmt_fifo_counter_rptr_wrap_cnt_def, fmt_fifo_wvalid_def, fmt_fifo_full_def,
         fmt_fifo_wready_def, fmt_fifo_incr_wptr_def, fmt_fifo_wdata_def,
         fmt_fifo_counter_wptr_wrap_def, fmt_fifo_counter_wptr_wrap_cnt_def,
         i2c_core_delay_comb_def, i2c_core_log_start_comb_def,
         i2c_core_log_stop_comb_def, fmt_fifo_flag_start_before_def,
         fmt_fifo_flag_stop_after_def, fmt_fifo_flag_read_bytes_def,
         fmt_fifo_flag_read_continue_def, fmt_fifo_flag_nak_ok_def,
         i2c_core_tx_fifo_empty_comb_def, i2c_core_tx_fifo_rdata_comb_def,
         i2c_core_tx_fifo_rvalid_comb_def, i2c_core_tx_fifo_full_comb_def,
         i2c_core_tx_fifo_wready_comb_def, i2c_core_tx_fifo_depth_comb_def,
         i2c_core_acq_fifo_empty_comb_def, i2c_core_acq_fifo_rdata_comb_def,
         i2c_core_acq_fifo_rvalid_comb_def, i2c_core_acq_fifo_full_comb_def,
         i2c_core_acq_fifo_wready_comb_def, i2c_core_acq_fifo_depth_comb_def,
         i2c_core_acq_fifo_2free_comb_def, i2c_core_tx_fifo_reset_comb_def,
         i2c_core_tx_fifo_rready_comb_def, i2c_core_tx_fifo_wvalid_comb_def,
         i2c_core_tx_fifo_wdata_comb_def, i2c_core_tx_fifo_incr_rptr_comb_def,
         i2c_core_tx_fifo_counter_rptr_wrap_comb_def,
         i2c_core_tx_fifo_counter_rptr_wrap_cnt_comb_def,
         i2c_core_tx_fifo_incr_wptr_comb_def,
         i2c_core_tx_fifo_counter_wptr_wrap_comb_def,
         i2c_core_tx_fifo_counter_wptr_wrap_cnt_comb_def,
         i2c_core_acq_fifo_reset_comb_def, i2c_core_acq_fifo_rready_comb_def,
         i2c_core_acq_fifo_wvalid_comb_def, i2c_core_acq_fifo_wdata_comb_def,
         i2c_core_acq_fifo_incr_rptr_comb_def,
         i2c_core_acq_fifo_counter_rptr_wrap_comb_def,
         i2c_core_acq_fifo_counter_rptr_wrap_cnt_comb_def,
         i2c_core_acq_fifo_incr_wptr_comb_def,
         i2c_core_acq_fifo_counter_wptr_wrap_comb_def,
         i2c_core_acq_fifo_counter_wptr_wrap_cnt_comb_def, i2c_core_stretch_tx_comb_def,
         i2c_core_load_tcount_comb_def, fmt_byte_def, req_restart_def, bit_clr_def,
         bit_decr_def, i2c_core_stretch_en_comb_def, i2c_core_scl_d_comb_def,
         i2c_core_sda_d_comb_def, i2c_core_scl_o_comb_def, i2c_core_sda_o_comb_def,
         i2c_core_cio_scl_o_comb_def, i2c_core_cio_sda_o_comb_def,
         i2c_core_cio_scl_en_o_comb_def, i2c_core_cio_sda_en_o_comb_def,
         i2c_core_next_scl_rx_val_comb_def, i2c_core_byte_clr_comb_def,
         i2c_core_byte_decr_comb_def, i2c_core_byte_num_comb_def,
         i2c_core_next_byte_index_comb_def, fifo_depth_def, counter_gt_one_comb_def,
         i2c_core_next_state_def, i2c_core_next_delay_comb_def,
         i2c_core_next_counter_def, i2c_core_read_byte_clr_comb_def,
         i2c_core_input_byte_clr_comb_def, i2c_core_shift_data_en_comb_def,
         i2c_core_next_sda_rx_val_comb_def, i2c_core_next_read_byte_comb_def,
         i2c_core_rx_fifo_reset_comb_def, i2c_core_rx_fifo_rready_comb_def,
         i2c_core_rx_fifo_empty_comb_def, i2c_core_rx_fifo_rdata_comb_def,
         i2c_core_rx_fifo_rvalid_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def,
         i2c_core_rx_fifo_counter_rptr_wrap_comb_def,
         i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def,
         i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_wdata_comb_def,
         i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_wready_comb_def,
         i2c_core_rx_fifo_depth_comb_def, i2c_core_rx_fifo_incr_wptr_comb_def,
         i2c_core_rx_fifo_counter_wptr_wrap_comb_def,
         i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def,
         i2c_core_fmt_threshold_d_comb_def, i2c_core_rx_threshold_d_comb_def,
         i2c_core_en_sda_interf_det_comb_def, i2c_core_expect_stop_comb_def,
         i2c_core_event_fmt_threshold_comb_def, i2c_core_event_rx_threshold_comb_def,
         i2c_core_event_fmt_overflow_comb_def, i2c_core_event_rx_overflow_comb_def,
         i2c_core_event_nak_comb_def, i2c_core_event_scl_interference_comb_def,
         i2c_core_event_sda_interference_comb_def,
         i2c_core_event_stretch_timeout_comb_def, i2c_core_event_sda_unstable_comb_def,
         i2c_core_event_cmd_complete_comb_def, i2c_core_event_tx_stretch_comb_def,
         i2c_core_event_tx_overflow_comb_def, i2c_core_event_acq_full_comb_def,
         i2c_core_event_unexp_stop_comb_def, i2c_core_event_host_timeout_comb_def,
         i2c_core_hw2reg_intr_state_fmt_threshold_de_comb_def,
         i2c_core_hw2reg_intr_state_fmt_threshold_d_comb_def,
         i2c_core_hw2reg_intr_state_rx_threshold_de_comb_def,
         i2c_core_hw2reg_intr_state_rx_threshold_d_comb_def,
         i2c_core_hw2reg_intr_state_fmt_overflow_de_comb_def,
         i2c_core_hw2reg_intr_state_fmt_overflow_d_comb_def,
         i2c_core_hw2reg_intr_state_rx_overflow_de_comb_def,
         i2c_core_hw2reg_intr_state_rx_overflow_d_comb_def,
         i2c_core_hw2reg_intr_state_nak_de_comb_def,
         i2c_core_hw2reg_intr_state_nak_d_comb_def,
         i2c_core_hw2reg_intr_state_scl_interference_de_comb_def,
         i2c_core_hw2reg_intr_state_scl_interference_d_comb_def,
         i2c_core_hw2reg_intr_state_sda_interference_de_comb_def,
         i2c_core_hw2reg_intr_state_sda_interference_d_comb_def,
         i2c_core_hw2reg_intr_state_stretch_timeout_de_comb_def,
         i2c_core_hw2reg_intr_state_stretch_timeout_d_comb_def,
         i2c_core_hw2reg_intr_state_sda_unstable_de_comb_def,
         i2c_core_hw2reg_intr_state_sda_unstable_d_comb_def,
         i2c_core_hw2reg_intr_state_cmd_complete_de_comb_def,
         i2c_core_hw2reg_intr_state_cmd_complete_d_comb_def,
         i2c_core_hw2reg_intr_state_tx_stretch_de_comb_def,
         i2c_core_hw2reg_intr_state_tx_stretch_d_comb_def,
         i2c_core_hw2reg_intr_state_tx_overflow_de_comb_def,
         i2c_core_hw2reg_intr_state_tx_overflow_d_comb_def,
         i2c_core_hw2reg_intr_state_acq_full_de_comb_def,
         i2c_core_hw2reg_intr_state_acq_full_d_comb_def,
         i2c_core_hw2reg_intr_state_unexp_stop_de_comb_def,
         i2c_core_hw2reg_intr_state_unexp_stop_d_comb_def,
         i2c_core_hw2reg_intr_state_host_timeout_de_comb_def,
         i2c_core_hw2reg_intr_state_host_timeout_d_comb_def,
         i2c_core_next_stretch_idle_cnt_def, next_pend_restart_comb_def,
         next_trans_started_comb_def, next_bit_index_comb_def,
         i2c_core_status_fmtfull_d_comb_def, i2c_core_status_rxfull_d_comb_def,
         i2c_core_status_fmtempty_d_comb_def, i2c_core_status_hostidle_d_comb_def,
         i2c_core_status_targetidle_d_comb_def, i2c_core_status_rxempty_d_comb_def,
         i2c_core_rdata_rdata_d_comb_def, i2c_core_fifo_status_fmtlvl_d_comb_def,
         i2c_core_fifo_status_rxlvl_d_comb_def, i2c_core_val_scl_rx_d_comb_def,
         i2c_core_val_sda_rx_d_comb_def, i2c_core_status_txfull_d_comb_def,
         i2c_core_status_acqfull_d_comb_def, i2c_core_status_txempty_d_comb_def,
         i2c_core_status_acqempty_d_comb_def, i2c_core_fifo_status_txlvl_d_comb_def,
         i2c_core_fifo_status_acqlvl_d_comb_def, i2c_core_acqdata_abyte_d_comb_def,
         i2c_core_acqdata_signal_d_comb_def]
QED

val _ = export_theory ();
