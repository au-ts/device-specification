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

(* Direct translation from @{file "i2cCoreCiruitLib.sml"} *)
Definition fmt_fifo_reset_def:
  fmt_fifo_reset (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = 
  s' with fmt_fifo := s'.fmt_fifo with reset := ((s'.reg2hw.fifo_ctrl.fmtrst_q = 1w) ∧ s.reg2hw.fifo_ctrl.fmtrst_qe)
End

Definition fmt_fifo_rdata_def:
  fmt_fifo_rdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rdata := s.fmt_fifo_regfile $ (5 >< 0) s.fmt_fifo.rptr
End

Definition fmt_fifo_rready_def:
  fmt_fifo_rready (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rready := (s.fsm_state = popFmtFifo)
End

Definition fmt_fifo_empty_def:
  fmt_fifo_empty (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with empty := (s.fmt_fifo.rptr = s.fmt_fifo.wptr)
End

Definition fmt_fifo_incr_rptr_def:
  fmt_fifo_incr_rptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with incr_rptr := (¬s'.fmt_fifo.empty ∧ s'.fmt_fifo.rready)
End

Definition fmt_fifo_counter_rptr_wrap_def:
  fmt_fifo_counter_rptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with rptr_wrap :=
  (s'.fmt_fifo.incr_rptr ∧ (5 >< 0) s.fmt_fifo.rptr = 63w : 6 word)
End

Definition fmt_fifo_counter_rptr_wrap_cnt_def:
  fmt_fifo_counter_rptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.fmt_fifo.rptr then (64w : 7 word) else 0w
End

Definition fmt_fifo_rptr_ff_def:
  fmt_fifo_rptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.fmt_fifo.reset then
    s' with fmt_fifo := s'.fmt_fifo with rptr := 0w
  else if s'.fmt_fifo.counter2.rptr_wrap then
    s' with fmt_fifo := s'.fmt_fifo with rptr := s'.fmt_fifo.counter2.rptr_wrap_cnt
  else
    s' with fmt_fifo := s'.fmt_fifo with rptr := s.fmt_fifo.rptr + 1w
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

Definition fmt_fifo_incr_wptr_def:
  fmt_fifo_incr_wptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with incr_wptr := (¬s'.fmt_fifo.full ∧ s'.fmt_fifo.wvalid)
End

Definition fmt_fifo_wdata_def:
  fmt_fifo_wdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with wdata :=
  (w2w s'.reg2hw.fdata.nakok_q <<~ 12w)
  || (w2w s'.reg2hw.fdata.rcont_q <<~ 11w)
  || (w2w s'.reg2hw.fdata.read_q <<~ 10w)
  || (w2w s'.reg2hw.fdata.stop_q <<~ 9w)
  || (w2w s'.reg2hw.fdata.start_q <<~ 8w)
  ||  w2w s'.reg2hw.fdata.fbyte_q
End

Definition fmt_fifo_regfile_ff_def:
  fmt_fifo_regfile_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  let
    wptr = (5 >< 0) s.fmt_fifo.wptr;
  in
    if s'.fmt_fifo.incr_wptr
    then s' with fmt_fifo_regfile := (wptr =+ s'.fmt_fifo.wdata) s'.fmt_fifo_regfile
    else s'
End

Definition fmt_fifo_counter_wptr_wrap_def:
  fmt_fifo_counter_wptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with wptr_wrap :=
  (s'.fmt_fifo.incr_wptr ∧ (5 >< 0) s.fmt_fifo.wptr = 63w : 6 word)
End

Definition fmt_fifo_counter_wptr_wrap_cnt_def:
  fmt_fifo_counter_wptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with wptr_wrap_cnt :=
  if ¬ (word_bit 6 s.fmt_fifo.wptr) then 64w else 0w
End

Definition fmt_fifo_wptr_ff_def:
  fmt_fifo_wptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.fmt_fifo.reset then
    s' with fmt_fifo := s'.fmt_fifo with wptr := 0w
  else if s'.fmt_fifo.counter2.wptr_wrap then
    s' with fmt_fifo := s'.fmt_fifo with wptr := s'.fmt_fifo.counter2.wptr_wrap_cnt
  else
    s' with fmt_fifo := s'.fmt_fifo with wptr := s.fmt_fifo.wptr + 1w
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

Definition i2c_core_curr_delay_comb_def:
  i2c_core_curr_delay_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  case s.fsm_state of
    recReadClockLow      => s' with curr_delay := s'.delay.clock_low
  | recReadClockPulse    => s' with curr_delay := s'.delay.clock_pulse
  | recReadHoldBit       => s' with curr_delay := s'.delay.hold_bit
  | recHostClockLowAck   => s' with curr_delay := s'.delay.clock_low
  | recHostClockPulseAck => s' with curr_delay := s'.delay.clock_pulse
  | recHostHoldBitAck    => s' with curr_delay := s'.delay.hold_bit
  | stopClockStop        => s' with curr_delay := s'.delay.clock_stop
  | stopSetupStop        => s' with curr_delay := s'.delay.setup_stop
  | stopHoldStop         => s' with curr_delay := s'.delay.hold_stop
  | startSetupStart      => s' with curr_delay := s'.delay.setup_start
  | startHoldStart       => s' with curr_delay := s'.delay.hold_start
  | startClockStart      => s' with curr_delay := s'.delay.clock_start
  | transClockLow        => s' with curr_delay := s'.delay.clock_low
  | transClockPulse      => s' with curr_delay := s'.delay.clock_pulse
  | transHoldBit         => s' with curr_delay := s'.delay.hold_bit
  | transClockLowAck     => s' with curr_delay := s'.delay.clock_low
  | transClockPulseAck   => s' with curr_delay := s'.delay.clock_pulse
  | transHoldDevAck      => s' with curr_delay := s'.delay.hold_bit
  | _                    => s' with curr_delay := 0w
End

Definition i2c_core_load_tcount_comb_def:
  i2c_core_load_tcount_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with load_tcount := (s.fsm_state ≠ idle ∧ s.counter = 1w ∨ s.fsm_state = popFmtFifo)
End

Definition i2c_core_log_start_comb_def:
  i2c_core_log_start_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  s' with log_start := (s.fsm_state = startSetupStart ∧ s.counter = 1w)
End

Definition i2c_core_log_stop_comb_def:
  i2c_core_log_stop_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  s' with log_stop := (s.fsm_state = stopClockStop ∧ s.counter = 1w)
End

Definition fmt_fifo_rvalid_def:
  fmt_fifo_rvalid (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_fifo := s'.fmt_fifo with rvalid := ¬s'.fmt_fifo.empty
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

Definition fmt_fifo_flag_nak_ok_def:
  fmt_fifo_flag_nak_ok (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with fmt_flag := s'.fmt_flag with nak_ok :=
  (s'.fmt_fifo.rvalid ∧ word_bit 12 s'.fmt_fifo.rdata)
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
  s' with bit_clr := ( (s.fsm_state = transHoldBit ∨ s.fsm_state = recReadHoldBit)
                       ∧  s.counter = 1w ∧ s.bit_index = 0w )
End

Definition bit_decr_def:
  bit_decr (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with bit_decr := ((s.fsm_state = transHoldBit ∨ s.fsm_state = recReadHoldBit)
                       ∧ s.counter = 1w ∧ s.bit_index ≠ 0w )
End

Definition i2c_core_stretch_en_comb_def:
  i2c_core_stretch_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with stretch_en := (s.fsm_state = transClockPulse ∨  s.fsm_state = transClockPulseAck
                         ∨  s.fsm_state = recReadClockPulse ∨  s.fsm_state = recHostClockPulseAck)
End

Definition i2c_core_scl_d_comb_def:
  i2c_core_scl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with scl_d := ¬( s.fsm_state = startClockStart
                      ∨ s.fsm_state = transClockLow
                      ∨ s.fsm_state = transHoldBit
                      ∨ s.fsm_state = transClockLowAck
                      ∨ s.fsm_state = transHoldDevAck
                      ∨ s.fsm_state = recReadClockLow
                      ∨ s.fsm_state = recReadHoldBit
                      ∨ s.fsm_state = recHostClockLowAck
                      ∨ s.fsm_state = recHostHoldBitAck
                      ∨ s.fsm_state = recHostHoldBitAck
                      ∨ s.fsm_state = stopClockStop
                      ∨ s.fsm_state = active ∧ (¬s'.fmt_flag.start_before ∨ s.trans_started)
                      ∨ s.fsm_state = popFmtFifo ∧ ¬s'.fmt_flag.stop_after)
End

Definition i2c_core_next_scl_rx_val_comb_def:
  i2c_core_next_scl_rx_val_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if fext.cio_scl_i then
    s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w) || 1w
  else
    s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w)
End

Definition i2c_core_next_stretch_idle_cnt_def:
  i2c_core_next_stretch_idle_cnt (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.stretch_en ∧ s'.scl_d ∧ ¬fext.cio_scl_i
  then s' with next_stretch_idle_cnt := s.stretch_idle_cnt + 1w
  else s' with next_stretch_idle_cnt := 0w
End

Definition i2c_core_next_counter_def:
  i2c_core_next_counter (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s'.load_tcount then s' with next_counter := s'.curr_delay
  else if s.stretch_idle_cnt = 0w then s' with next_counter := s.counter - 1w
  else s' with next_counter := s.counter
End

Definition i2c_core_byte_clr_comb_def:
  i2c_core_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_clr := (s.fsm_state = active ∧ s'.fmt_flag.read_bytes)
End

Definition i2c_core_byte_decr_comb_def:
  i2c_core_byte_decr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_decr := (s.fsm_state = recHostHoldBitAck ∧ s.counter = 1w ∧ s.byte_index ≠ 1w)
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

Definition counter_gt_one_comb_def:
  counter_gt_one_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  s' with cnt_gt_one := (1w <+ s.counter)
End

Definition i2c_core_next_state_def:
  i2c_core_next_state (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  case s.fsm_state of
    idle                 => if s.regs.ctrl.enablehost = 1w ∧ s'.fmt_fifo.rvalid
                            then s' with next_state := active
                            else s' with next_state := idle
  | active               => if s'.fmt_flag.read_bytes then
                              s' with next_state := recReadClockLow
                            else if s'.fmt_flag.start_before ∧ ¬s.trans_started then
                              s' with next_state := startSetupStart
                            else
                              s' with next_state := transClockLow

  | recReadClockLow      => if s'.cnt_gt_one then s' with next_state := recReadClockLow
                            else s' with next_state := recReadClockPulse

  | recReadClockPulse    => if s'.cnt_gt_one then s' with next_state := recReadClockPulse
                            else s' with next_state := recReadHoldBit

  | recReadHoldBit       => if s'.cnt_gt_one then
                              s' with next_state := recReadHoldBit
                            else if s.bit_index = 0w then
                              s' with next_state := recHostClockLowAck
                            else
                              s' with next_state := recReadClockLow

  | recHostClockLowAck   => if s'.cnt_gt_one then s' with next_state := recHostClockLowAck
                            else s' with next_state := recHostClockPulseAck

  | recHostClockPulseAck => if s'.cnt_gt_one then s' with next_state := recHostClockPulseAck
                            else s' with next_state := recHostHoldBitAck

  | recHostHoldBitAck    => if s'.cnt_gt_one then
                              s' with next_state := recHostHoldBitAck
                            else if s.byte_index = 1w ∧ s'.fmt_flag.stop_after then
                              s' with next_state := stopClockStop
                            else if s.byte_index = 1w ∧ ¬s'.fmt_flag.stop_after then
                              s' with next_state := popFmtFifo
                            else
                              s' with next_state := recReadClockLow

  | stopClockStop        => if s'.cnt_gt_one then s' with next_state := stopClockStop
                            else s' with next_state := stopSetupStop

  | stopSetupStop        => if s'.cnt_gt_one then s' with next_state := stopSetupStop
                            else s' with next_state := stopHoldStop

  | stopHoldStop         => if s'.cnt_gt_one then s' with next_state := stopHoldStop
                            else if s.regs.ctrl.enablehost = 0w then s' with next_state := idle
                            else s' with next_state := popFmtFifo

  | startSetupStart      => if s'.cnt_gt_one then s' with next_state := startSetupStart
                            else s' with next_state := startHoldStart

  | startHoldStart       => if s'.cnt_gt_one then s' with next_state := startHoldStart
                            else s' with next_state := startClockStart

  | startClockStart      => if s'.cnt_gt_one then s' with next_state := startClockStart
                            else s' with next_state := transClockLow

  | transClockLow        => if s'.cnt_gt_one then s' with next_state := transClockLow
                            else if s.pend_restart then s' with next_state := startSetupStart
                            else s' with next_state := transClockPulse

  | transClockPulse      => if s'.cnt_gt_one then s' with next_state := transClockPulse
                            else s' with next_state := transHoldBit

  | transHoldBit         => if s'.cnt_gt_one then s' with next_state := transHoldBit
                            else if s.bit_index = 0w then s' with next_state := transClockLowAck
                            else s' with next_state := transClockLow

  | transClockLowAck     => if s'.cnt_gt_one then s' with next_state := transClockLowAck
                            else s' with next_state := transClockPulseAck
                                                       
  | transClockPulseAck   => if s'.cnt_gt_one then s' with next_state := transClockPulseAck
                            else s' with next_state := transHoldDevAck

  | transHoldDevAck      => if s'.cnt_gt_one then
                              s' with next_state := transHoldDevAck
                            else if s'.fmt_flag.stop_after then
                              s' with next_state := stopClockStop
                            else
                              s' with next_state := popFmtFifo

  | popFmtFifo           => if s.regs.ctrl.enablehost = 0w then s' with next_state := stopClockStop
                            else if s'.fmt_fifo.depth = 1w then s' with next_state := idle
                            else s' with next_state := active

  | _ => s' with next_state := idle
End

Definition i2c_core_read_byte_clr_comb_def:
  i2c_core_read_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with read_byte_clr := (s.fsm_state = recReadHoldBit ∧ s.counter = 1w ∧ s.bit_index = 0w)
End

Definition i2c_core_shift_data_en_comb_def:
  i2c_core_shift_data_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with shift_data_en := (s.fsm_state = recReadClockPulse ∧ s.counter = 1w)
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
  else if s'.shift_data_en ∧ fext.cio_sda_i then
    s' with next_read_byte := (w2w s.read_byte <<~ 1w) || 1w
  else if s'.shift_data_en ∧ ¬fext.cio_sda_i then
    s' with next_read_byte := (w2w s.read_byte <<~ 1w)
  else
    s' with next_read_byte := s.read_byte
End

Definition i2c_core_rx_fifo_reset_comb_def:
  i2c_core_rx_fifo_reset_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with reset :=
  (word_bit 0 s'.reg2hw.fifo_ctrl.rxrst_q ∧ s.reg2hw.fifo_ctrl.rxrst_qe)
End

Definition i2c_core_rx_fifo_rdata_comb_def:
  i2c_core_rx_fifo_rdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with rdata := s.rx_fifo_regfile $ (5 >< 0) s.rx_fifo.rptr
End

Definition i2c_core_rx_fifo_rready_comb_def:
  i2c_core_rx_fifo_rready_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with rready := s'.reg2hw.rdata.rdata_re
End

Definition i2c_core_rx_fifo_empty_comb_def:
  i2c_core_rx_fifo_empty_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with empty := (s.rx_fifo.rptr = s.rx_fifo.wptr)
End

Definition i2c_core_rx_fifo_incr_rptr_comb_def:
  i2c_core_rx_fifo_incr_rptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with incr_rptr := (¬s'.rx_fifo.empty ∧ s'.rx_fifo.rready)
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
  else
    s' with rx_fifo := s'.rx_fifo with rptr := s.rx_fifo.rptr + 1w
End

Definition i2c_core_rx_fifo_wvalid_comb_def:
  i2c_core_rx_fifo_wvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with wvalid :=
  (s.fsm_state = recReadHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w)
End

Definition i2c_core_rx_fifo_wdata_comb_def:
  i2c_core_rx_fifo_wdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  if s.fsm_state = recReadHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w then
    s' with rx_fifo := s'.rx_fifo with wdata := s.read_byte
  else
    s' with rx_fifo := s'.rx_fifo with wdata := 0w
End

Definition i2c_core_rx_fifo_full_comb_def:
  i2c_core_rx_fifo_full_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with full :=
  ((word_bit 5 s.rx_fifo.wptr ≠ word_bit 5 s.rx_fifo.rptr) ∧
   ((5 >< 0) s.rx_fifo.wptr : 6 word = (5 >< 0) s.rx_fifo.rptr : 6 word))
End

Definition i2c_core_rx_fifo_incr_wptr_comb_def:
  i2c_core_rx_fifo_incr_wptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with rx_fifo := s'.rx_fifo with incr_wptr := (¬s'.rx_fifo.full ∧ s'.rx_fifo.wvalid)
End

Definition i2c_core_rx_fifo_regfile_def:
  i2c_core_rx_fifo_regfile (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  let
    wptr = (5 >< 0) s.rx_fifo.wptr;
  in
    if s'.rx_fifo.incr_wptr
    then s' with rx_fifo_regfile := (wptr =+ s'.rx_fifo.wdata) s'.rx_fifo_regfile
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
  else
    s' with rx_fifo := s'.rx_fifo with wptr := s.rx_fifo.wptr + 1w
End

Definition hw2reg_intr_state_nak_de_comb_def:
  hw2reg_intr_state_nak_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_de :=
  (s.fsm_state = transClockPulseAck ∧ ¬s'.fmt_flag.nak_ok ∧ fext.cio_sda_i)
End

Definition hw2reg_intr_state_nak_d_comb_def:
  hw2reg_intr_state_nak_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_d :=
  n2w $ bool_to_bit
      ( s.fsm_state = transClockPulseAck ∧ ¬s'.fmt_flag.nak_ok ∧ fext.cio_sda_i
        ∨ word_bit 0 s'.reg2hw.intr_state.nak_q)
End

Definition next_intr_nak_comb_def:
  next_intr_nak_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with next_intr_nak_o := (word_bit 0 s'.reg2hw.intr_state.nak_q ∧ word_bit 0 s'.reg2hw.intr_enable.nak_q)
End

Definition hw2reg_intr_state_cmd_complete_de_comb_def:
  hw2reg_intr_state_cmd_complete_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_de :=
  (s.fsm_state = stopHoldStop ∨ s.fsm_state = startSetupStart ∧ s'.log_start ∧ s.pend_restart)
End

Definition hw2reg_intr_state_cmd_complete_d_comb_def:
  hw2reg_intr_state_cmd_complete_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_d :=
  if ( s.fsm_state = stopHoldStop ∨ s.fsm_state = startSetupStart ∧ s'.log_start ∧ s.pend_restart
       ∨ word_bit 0 s'.reg2hw.intr_state.cmd_complete_q ) then 1w else 0w
End

Definition next_intr_cmd_complete_comb_def:
  next_intr_cmd_complete_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with next_intr_cmd_complete_o := (word_bit 0 s'.reg2hw.intr_state.cmd_complete_q ∧ word_bit 0 s'.reg2hw.intr_enable.cmd_complete_q)
End

Definition next_pend_restart_comb_def:
  next_pend_restart_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s.pend_restart ∧ s.regs.ctrl.enablehost = 0w ∨ s'.log_start then s' with next_pend_restart := F
  else if s'.req_restart then s' with next_pend_restart := T
  else s' with next_pend_restart := s.pend_restart
End

Definition next_trans_started_comb_def:
  next_trans_started_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s.trans_started ∧ s.regs.ctrl.enablehost = 0w ∨ s'.log_stop then s' with next_trans_started := F
  else if s'.log_start then s' with next_trans_started := T
  else s' with next_trans_started := s.trans_started
End

Definition next_bit_index_comb_def:
  next_bit_index_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  if s'.bit_clr then s' with next_bit_index := 7w
  else if s'.bit_decr then s' with next_bit_index := s.bit_index - 1w
  else s' with next_bit_index := s.bit_index
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

Definition pend_restart_ff_def:
  pend_restart_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with pend_restart := s'.next_pend_restart
End

Definition byte_index_ff_def:
  byte_index_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  s' with byte_index := s'.next_byte_index
End

val init_tm = add_x_inits ``
  <|
    regs := ^i2c_regs_init_tm;
    reg2hw := ^i2c_reg2hw_init_tm;
    fmt_fifo_regfile := K 0w;
    rx_fifo_regfile := K 0w;
  |>
``;

Definition i2c_circuit_init_def:
  i2c_circuit_init fbits = ^init_tm
End

Definition i2c_core_ffs1_def:
  i2c_core_ffs1 = [i2c_core_counter_ff; i2c_core_stretch_idle_cnt_ff; fmt_fifo_rptr_ff;
                   fmt_fifo_regfile_ff; i2c_core_rx_fifo_wptr_ff; fmt_fifo_wptr_ff; bit_index_ff;
                   pend_restart_ff; byte_index_ff; i2c_core_rx_fifo_rptr_ff; i2c_core_rx_fifo_regfile;
                   i2c_core_ff]
End

(* with dependency taken into account *)        
Definition i2c_core_combs_def:
  i2c_core_combs = [
    fmt_fifo_reset; fmt_fifo_rdata; fmt_fifo_rready; fmt_fifo_empty;
    fmt_fifo_incr_rptr; fmt_fifo_counter_rptr_wrap;
    fmt_fifo_counter_rptr_wrap_cnt; fmt_fifo_wvalid; fmt_fifo_full;
    fmt_fifo_incr_wptr; fmt_fifo_wdata; fmt_fifo_counter_wptr_wrap;
    fmt_fifo_counter_wptr_wrap_cnt; i2c_core_delay_comb;
    i2c_core_curr_delay_comb; i2c_core_load_tcount_comb;
    i2c_core_log_start_comb; i2c_core_log_stop_comb; fmt_fifo_rvalid;
    fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after;
    fmt_fifo_flag_read_bytes; fmt_fifo_flag_nak_ok; fmt_byte; req_restart;
    bit_clr; bit_decr; i2c_core_stretch_en_comb; i2c_core_scl_d_comb;
    i2c_core_next_scl_rx_val_comb; i2c_core_next_stretch_idle_cnt;
    i2c_core_next_counter; i2c_core_byte_clr_comb; i2c_core_byte_decr_comb;
    i2c_core_byte_num_comb; i2c_core_next_byte_index_comb; fifo_depth;
    counter_gt_one_comb; i2c_core_next_state; i2c_core_read_byte_clr_comb;
    i2c_core_shift_data_en_comb; i2c_core_next_sda_rx_val_comb;
    i2c_core_rx_fifo_reset_comb; i2c_core_rx_fifo_rdata_comb;
    i2c_core_rx_fifo_rready_comb; i2c_core_rx_fifo_empty_comb;
    i2c_core_rx_fifo_incr_rptr_comb; i2c_core_rx_fifo_counter_rptr_wrap_comb;
    i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb;
    i2c_core_rx_fifo_wvalid_comb; i2c_core_rx_fifo_wdata_comb;
    i2c_core_rx_fifo_full_comb; i2c_core_rx_fifo_incr_wptr_comb;
    i2c_core_rx_fifo_counter_wptr_wrap_comb;
    i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb;
    hw2reg_intr_state_nak_de_comb; next_intr_nak_comb;
    hw2reg_intr_state_cmd_complete_de_comb;
    hw2reg_intr_state_cmd_complete_d_comb; next_pend_restart_comb;
    next_trans_started_comb]                 
End
        

(* basis --- successfully generated the deeply embedded *)
(*
Definition i2c_core_combs_def:
  i2c_core_combs = [i2c_core_rx_fifo_counter_wptr_wrap_comb; i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb;
                    i2c_core_delay_comb; i2c_core_curr_delay_comb; i2c_core_load_tcount_comb;
                    i2c_core_stretch_en_comb; i2c_core_scl_d_comb; i2c_core_next_stretch_idle_cnt;
                    i2c_core_next_counter; i2c_core_next_state; fmt_fifo_reset; counter_gt_one_comb;
                    fmt_fifo_rdata; fmt_fifo_rready; fmt_fifo_empty;
                    fmt_fifo_counter_rptr_wrap; fmt_fifo_counter_rptr_wrap_cnt;
                    fmt_fifo_wvalid; fmt_fifo_full; fmt_fifo_incr_wptr; fmt_fifo_wdata;
                    fmt_fifo_counter_wptr_wrap;
                    fmt_fifo_counter_wptr_wrap_cnt; i2c_core_log_start_comb; i2c_core_log_stop_comb;
                    fmt_fifo_rvalid;
                    fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after; fmt_fifo_flag_read_bytes; fmt_byte;
                    req_restart; bit_clr; bit_decr; i2c_core_next_scl_rx_val_comb; i2c_core_byte_clr_comb;
                    i2c_core_byte_num_comb; i2c_core_next_byte_index_comb; fifo_depth;
                    i2c_core_read_byte_clr_comb;
                    i2c_core_shift_data_en_comb; i2c_core_next_sda_rx_val_comb; i2c_core_next_read_byte_comb;
                    i2c_core_rx_fifo_reset_comb; i2c_core_rx_fifo_rdata_comb; i2c_core_rx_fifo_rready_comb;
                    i2c_core_rx_fifo_empty_comb; i2c_core_rx_fifo_incr_rptr_comb;
                    i2c_core_rx_fifo_counter_rptr_wrap_comb;
                    i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_rx_fifo_wvalid_comb;
                    i2c_core_rx_fifo_wdata_comb;
                    i2c_core_rx_fifo_full_comb; i2c_core_rx_fifo_incr_wptr_comb;
                    hw2reg_intr_state_nak_de_comb; next_intr_nak_comb;
                    hw2reg_intr_state_cmd_complete_de_comb; hw2reg_intr_state_cmd_complete_d_comb;
                    next_intr_cmd_complete_comb;
                    next_pend_restart_comb; next_trans_started_comb; next_bit_index_comb]
End
*)

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
  >> rw [Abbr ‘s''’, i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def,
         fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
         bit_index_ff_def, pend_restart_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
         i2c_core_rx_fifo_regfile_def, i2c_core_ff_def]
QED

Theorem ff_asm2:
  EVERY (λproc. (proc fext s s').hw2reg = s'.hw2reg) i2c_core_ffs1
Proof
  rw [i2c_core_ffs1_def, i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def,
         fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
         bit_index_ff_def, pend_restart_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
         i2c_core_rx_fifo_regfile_def, i2c_core_ff_def]
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
  >> rw [Abbr ‘s''’, i2c_core_rx_fifo_counter_wptr_wrap_comb_def, i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def,
         i2c_core_delay_comb_def, i2c_core_curr_delay_comb_def, i2c_core_load_tcount_comb_def,
         i2c_core_stretch_en_comb_def, i2c_core_scl_d_comb_def, i2c_core_next_stretch_idle_cnt_def,
         i2c_core_next_counter_def, i2c_core_next_state_def, fmt_fifo_reset_def, counter_gt_one_comb_def,
         fmt_fifo_rdata_def, fmt_fifo_rready_def, fmt_fifo_empty_def,
         fmt_fifo_counter_rptr_wrap_def, fmt_fifo_counter_rptr_wrap_cnt_def,
         fmt_fifo_wvalid_def, fmt_fifo_full_def, fmt_fifo_incr_wptr_def, fmt_fifo_wdata_def, fmt_fifo_counter_wptr_wrap_def,
         fmt_fifo_counter_wptr_wrap_cnt_def, i2c_core_log_start_comb_def, i2c_core_log_stop_comb_def, fmt_fifo_rvalid_def,
         fmt_fifo_flag_start_before_def, fmt_fifo_flag_stop_after_def, fmt_fifo_flag_read_bytes_def, fmt_byte_def,
         req_restart_def, bit_clr_def, bit_decr_def, i2c_core_next_scl_rx_val_comb_def, i2c_core_byte_clr_comb_def,
         i2c_core_byte_num_comb_def, i2c_core_next_byte_index_comb_def, fifo_depth_def, i2c_core_read_byte_clr_comb_def,
         i2c_core_shift_data_en_comb_def, i2c_core_next_sda_rx_val_comb_def, i2c_core_next_read_byte_comb_def,
         i2c_core_rx_fifo_reset_comb_def, i2c_core_rx_fifo_rdata_comb_def, i2c_core_rx_fifo_rready_comb_def,
         i2c_core_rx_fifo_empty_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_comb_def,
         i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def, i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_wdata_comb_def,
         i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_incr_wptr_comb_def,
         hw2reg_intr_state_nak_de_comb_def, next_intr_nak_comb_def,
         hw2reg_intr_state_cmd_complete_de_comb_def, hw2reg_intr_state_cmd_complete_d_comb_def, next_intr_cmd_complete_comb_def,
         next_pend_restart_comb_def, next_trans_started_comb_def, next_bit_index_comb_def,
         i2c_core_byte_decr_comb_def, fmt_fifo_flag_nak_ok_def, fmt_fifo_incr_rptr_def
        ]
QED

val _ = export_theory ();
