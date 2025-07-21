structure i2cCoreCircuitLib =
struct

open wordsLib;
open i2cCircuitStateTheory i2cRegsTheory i2cRegsCommTheory;
open i2cCoreTheory;

Overload idle = “0w : 5 word”;
Overload active = “1w : 5 word”;
Overload recReadClockLow = “2w : 5 word”;
Overload recReadClockPulse = “3w : 5 word”;
Overload recReadHoldBit = “4w : 5 word”;
Overload recHostClockLowAck = “5w : 5 word”;
Overload recHostClockPulseAck = “6w : 5 word”;
Overload recHostHoldBitAck = “7w : 5 word”;
Overload stopClockStop = “8w : 5 word”;
Overload stopSetupStop = “9w : 5 word”;
Overload stopHoldStop = “10w : 5 word”;
Overload startSetupStart = “11w : 5 word”;
Overload startHoldStart = “12w : 5 word”;
Overload startClockStart = “13w : 5 word”;
Overload transClockLow = “14w : 5 word”;
Overload transClockPulse = “15w : 5 word”;
Overload transHoldBit = “16w : 5 word”;
Overload transClockLowAck = “17w : 5 word”;
Overload transClockPulseAck = “18w : 5 word”;
Overload transHoldDevAck = “19w : 5 word”;
Overload popFmtFifo = “20w : 5 word”;

(* soft reset *)
val fmt_fifo_reset_tm = “
 s' with fmt_fifo := s'.fmt_fifo with reset := ((s'.reg2hw.fifo_ctrl.fmtrst_q = 1w) ∧ s.reg2hw.fifo_ctrl.fmtrst_qe)
”;

(* Reading register file via read pointer *)
val fmt_fifo_rdata_tm = “
 s' with fmt_fifo := s'.fmt_fifo with rdata := s.fmt_fifo_regfile $ (5 >< 0) s.fmt_fifo.rptr
”;

(* Section --- Updating read pointer *)
val fmt_fifo_rready_tm = “
 s' with fmt_fifo := s'.fmt_fifo with rready := (s.fsm_state = popFmtFifo)
”;

val fmt_fifo_empty_tm = “
 s' with fmt_fifo := s'.fmt_fifo with empty := (s.fmt_fifo.rptr = s.fmt_fifo.wptr)
”;

val fmt_fifo_incr_rptr_tm = “
 s' with fmt_fifo := s'.fmt_fifo with incr_rptr := (¬s'.fmt_fifo.empty ∧ s'.fmt_fifo.rready)
”;

val fmt_fifo_counter_rptr_wrap_tm = “
 s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with rptr_wrap :=
   (s'.fmt_fifo.incr_rptr ∧ (5 >< 0) s.fmt_fifo.rptr = 63w : 6 word)
”;

val fmt_fifo_counter_rptr_wrap_cnt_tm = “
 s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.fmt_fifo.rptr then (64w : 7 word) else 0w
”;

val fmt_fifo_rptr_tm = “
 if s'.fmt_fifo.reset then
   s' with fmt_fifo := s'.fmt_fifo with rptr := 0w
 else if s'.fmt_fifo.counter2.rptr_wrap then
   s' with fmt_fifo := s'.fmt_fifo with rptr := s'.fmt_fifo.counter2.rptr_wrap_cnt
 else
   s' with fmt_fifo := s'.fmt_fifo with rptr := s.fmt_fifo.rptr + 1w
”;

(* Updating register file via write pointer *)
val fmt_fifo_wvalid_tm = “
   s' with fmt_fifo := s'.fmt_fifo with wvalid :=
   (s.reg2hw.fdata.fbyte_qe ∧ s.reg2hw.fdata.start_qe ∧ s.reg2hw.fdata.stop_qe ∧ s.reg2hw.fdata.read_qe ∧ s.reg2hw.fdata.rcont_qe ∧ s.reg2hw.fdata.nakok_qe)
”;

val fmt_fifo_full_tm = “
 s' with fmt_fifo := s'.fmt_fifo with full :=
 ( word_bit 6 s.fmt_fifo.wptr ≠ word_bit 6 s.fmt_fifo.rptr
 ∧ (5 >< 0) s.fmt_fifo.wptr : 6 word = (5 >< 0) s.fmt_fifo.rptr : 6 word)
”;

val fmt_fifo_incr_wptr_tm = “
 s' with fmt_fifo := s'.fmt_fifo with incr_wptr := (¬s'.fmt_fifo.full ∧ s'.fmt_fifo.wvalid)
”;

val fmt_fifo_wdata_tm = “
   s' with fmt_fifo := s'.fmt_fifo with wdata :=
           	      (w2w s'.reg2hw.fdata.nakok_q <<~ 12w)
                   || (w2w s'.reg2hw.fdata.rcont_q <<~ 11w)
                   || (w2w s'.reg2hw.fdata.read_q <<~ 10w)
                   || (w2w s'.reg2hw.fdata.stop_q <<~ 9w)
                   || (w2w s'.reg2hw.fdata.start_q <<~ 8w)
                   ||  w2w s'.reg2hw.fdata.fbyte_q
”;

val fmt_fifo_regfile_tm = “
 let
   wptr = (5 >< 0) s.fmt_fifo.wptr;
 in
   if s'.fmt_fifo.incr_wptr
   then s' with fmt_fifo_regfile := (wptr =+ s'.fmt_fifo.wdata) s'.fmt_fifo_regfile
   else s'
”;

(* Section --- updating the write pointer *)
val fmt_fifo_counter_wptr_wrap_tm = “
 s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with wptr_wrap :=
   (s'.fmt_fifo.incr_wptr ∧ (5 >< 0) s.fmt_fifo.wptr = 63w : 6 word)
”;

val fmt_fifo_counter_wptr_wrap_cnt_tm = “
 s' with fmt_fifo := s'.fmt_fifo with counter2 := s'.fmt_fifo.counter2 with wptr_wrap_cnt :=
    if ¬ (word_bit 6 s.fmt_fifo.wptr) then 64w else 0w
”;

val fmt_fifo_wptr_tm = “
 if s'.fmt_fifo.reset then
   s' with fmt_fifo := s'.fmt_fifo with wptr := 0w
 else if s'.fmt_fifo.counter2.wptr_wrap then
   s' with fmt_fifo := s'.fmt_fifo with wptr := s'.fmt_fifo.counter2.wptr_wrap_cnt
 else
   s' with fmt_fifo := s'.fmt_fifo with wptr := s.fmt_fifo.wptr + 1w
”;

(* section --- Finite State Machine *)
val delay_tm = “
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
”;

val curr_delay_tm = “
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
”;

val load_tcount_tm = “
 s' with load_tcount := (s.fsm_state ≠ idle ∧ s.counter = 1w ∨ s.fsm_state = popFmtFifo)
”;

val log_start_tm = “
 s' with log_start := (s.fsm_state = startSetupStart ∧ s.counter = 1w)
”;

val log_stop_tm = “
 s' with log_stop := (s.fsm_state = stopClockStop ∧ s.counter = 1w)
”;

(* section --- FMT flags *)
val fmt_fifo_rvalid_tm = “
 s' with fmt_fifo := s'.fmt_fifo with rvalid := ¬s'.fmt_fifo.empty
”;

val fmt_fifo_flag_start_before_tm = “
 s' with fmt_flag := s'.fmt_flag with start_before :=
  (s'.fmt_fifo.rvalid ∧ word_bit 8 s'.fmt_fifo.rdata)
”;

val fmt_fifo_flag_stop_after_tm = “
 s' with fmt_flag := s'.fmt_flag with stop_after :=
 (s'.fmt_fifo.rvalid ∧ word_bit 9 s'.fmt_fifo.rdata)
”;

val fmt_fifo_flag_read_bytes_tm = “
 s' with fmt_flag := s'.fmt_flag with read_bytes :=
 (s'.fmt_fifo.rvalid ∧ word_bit 10 s'.fmt_fifo.rdata)
”;

val fmt_byte_tm = “
 s' with fmt_byte :=
 if s'.fmt_fifo.rvalid then (7 >< 0) s'.fmt_fifo.rdata else 0w
”;

val fmt_fifo_flag_nak_ok_tm = “
 s' with fmt_flag := s'.fmt_flag with nak_ok := word_bit 12 s'.fmt_fifo.rdata
”;

val req_restart_tm = “
 s' with req_restart := ( ¬s'.fmt_flag.read_bytes
                        ∧  s'.fmt_flag.start_before
                        ∧  s.fsm_state = active
                        ∧  s.trans_started )
”;

val bit_clr_tm = “
 s' with bit_clr := ( (s.fsm_state = transHoldBit ∨ s.fsm_state = recReadHoldBit)
                    ∧  s.counter = 1w ∧ s.bit_index = 0w )
”;

val bit_decr_tm = “
 s' with bit_decr := ((s.fsm_state = transHoldBit ∨ s.fsm_state = recReadHoldBit)
                     ∧ s.counter = 1w ∧ s.bit_index ≠ 0w )
”;

val stretch_en_tm = “
 s' with stretch_en := (s.fsm_state = transClockPulse
                     ∨  s.fsm_state = transClockPulseAck
                     ∨  s.fsm_state = recReadClockPulse
                     ∨  s.fsm_state = recHostClockPulseAck)
”;

val scl_d_tm = “
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
”;

val next_scl_rx_val_tm = “
 if fext.cio_scl_i then
   s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w) || 1w
 else
   s' with next_scl_rx_val := (w2w s.scl_rx_val <<~ 1w)
”

val next_stretch_idle_cnt_tm = “
 if s'.stretch_en ∧ s'.scl_d ∧ ¬fext.cio_scl_i
 then s' with next_stretch_idle_cnt := s.stretch_idle_cnt + 1w
 else s' with next_stretch_idle_cnt := 0w
”;

val next_counter_tm = “
 if s'.load_tcount then s' with next_counter := s'.curr_delay
 else if s.stretch_idle_cnt = 0w then s' with next_counter := s.counter - 1w
 else s' with next_counter := s.counter
”;

val byte_clr_tm = “
 s' with byte_clr := (s.fsm_state = active ∧ s'.fmt_flag.read_bytes)
”

val byte_decr_tm= “
 s' with byte_decr := (s.fsm_state = recHostHoldBitAck ∧ s.counter = 1w ∧ s.byte_index ≠ 1w)
”

val byte_num_tm = “
 if s'.fmt_flag.read_bytes then s' with byte_num := 0w
 else if s'.fmt_byte = 0w then s' with byte_num := 256w
 else s' with byte_num := w2w s'.fmt_byte
”

val next_byte_index_tm = “
 if s'.byte_clr then s' with next_byte_index := s'.byte_num
 else if s'.byte_decr then s' with next_byte_index := s.byte_index - 1w
 else s' with next_byte_index := s.byte_index
”;

val fifo_depth_tm = “
     if s'.fmt_fifo.full then
       s' with fmt_fifo := s'.fmt_fifo with depth := 64w
     else if word_bit 6 s.fmt_fifo.wptr = word_bit 6 s.fmt_fifo.rptr then
       s' with fmt_fifo := s'.fmt_fifo with depth := ((w2w ((5 >< 0) s.fmt_fifo.wptr : 6 word)) - (w2w ((5 >< 0) s.fmt_fifo.rptr : 6 word)))
     else
       s' with fmt_fifo := s'.fmt_fifo with depth := 64w - w2w ((5 >< 0) s.fmt_fifo.rptr : 6 word) + w2w ((5 >< 0) s.fmt_fifo.wptr :  6 word)
”;

val counter_gt_one_tm = “
 s' with cnt_gt_one := (1w <+ s.counter)
”;

val next_state_tm = “
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
”;

val read_byte_clr_tm = “
 s' with read_byte_clr := (s.fsm_state = recReadHoldBit ∧ s.counter = 1w ∧ s.bit_index = 0w)
”;

val shift_data_en_tm = “
 s' with shift_data_en := (s.fsm_state = recReadClockPulse ∧ s.counter = 1w)
”;

val next_sda_rx_val_tm = “
 if fext.cio_sda_i then
   s' with next_sda_rx_val := (w2w s.sda_rx_val <<~ 1w) || 1w
 else
   s' with next_sda_rx_val := (w2w s.sda_rx_val <<~ 1w)
”;

val next_read_byte_tm = “
 if s'.read_byte_clr then s' with next_read_byte := 0w
 else if s'.shift_data_en ∧ fext.cio_sda_i then
   s' with next_read_byte := (w2w s.read_byte <<~ 1w) || 1w
 else if s'.shift_data_en ∧ ¬fext.cio_sda_i then
   s' with next_read_byte := (w2w s.read_byte <<~ 1w)
 else
   s' with next_read_byte := s.read_byte
”;

(* Section RX FIFO *)
val rx_fifo_reset_tm = “
 s' with rx_fifo := s'.rx_fifo with reset :=
 (word_bit 0 s'.reg2hw.fifo_ctrl.rxrst_q ∧ s.reg2hw.fifo_ctrl.rxrst_qe)
”;

val rx_fifo_rdata_tm = “
 s' with rx_fifo := s'.rx_fifo with rdata := s.rx_fifo_regfile $ (5 >< 0) s.rx_fifo.rptr
”;

val rx_fifo_rready_tm = “
 s' with rx_fifo := s'.rx_fifo with rready := s'.reg2hw.rdata.rdata_re
”;

val rx_fifo_empty_tm = “
 s' with rx_fifo := s'.rx_fifo with empty := (s.rx_fifo.rptr = s.rx_fifo.wptr)
”;

val rx_fifo_incr_rptr_tm = “
 s' with rx_fifo := s'.rx_fifo with incr_rptr := (¬s'.rx_fifo.empty ∧ s'.rx_fifo.rready)
”;

val rx_fifo_counter_rptr_wrap_tm = “
 s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with rptr_wrap :=
   (s'.rx_fifo.incr_rptr ∧ (5 >< 0) s.rx_fifo.rptr = 63w : 6 word)
”;

val rx_fifo_counter_rptr_wrap_cnt_tm = “
 s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with rptr_wrap_cnt :=
  if ¬ word_bit 6 s.rx_fifo.rptr then (64w : 7 word) else 0w
”;

val rx_fifo_rptr_tm = “
 if s'.rx_fifo.reset then
   s' with rx_fifo := s'.rx_fifo with rptr := 0w
 else if s'.rx_fifo.counter.rptr_wrap then
   s' with rx_fifo := s'.rx_fifo with rptr := s'.rx_fifo.counter.rptr_wrap_cnt
 else
   s' with rx_fifo := s'.rx_fifo with rptr := s.rx_fifo.rptr + 1w
”;

val rx_fifo_wvalid_tm = “
 s' with rx_fifo := s'.rx_fifo with wvalid :=
 (s.fsm_state = recReadHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w)
”;

val rx_fifo_wdata_tm = “
 if s.fsm_state = recReadHoldBit ∧ s.bit_index = 0w ∧ s.counter = 1w then
   s' with rx_fifo := s'.rx_fifo with wdata := s.read_byte
 else
   s' with rx_fifo := s'.rx_fifo with wdata := 0w
”;

val rx_fifo_full_tm = “
 s' with rx_fifo := s'.rx_fifo with full :=
   ((word_bit 5 s.rx_fifo.wptr ≠ word_bit 5 s.rx_fifo.rptr) ∧
   ((5 >< 0) s.rx_fifo.wptr : 6 word = (5 >< 0) s.rx_fifo.rptr : 6 word))
”;

val rx_fifo_incr_wptr_tm = “
 s' with rx_fifo := s'.rx_fifo with incr_wptr := (¬s'.rx_fifo.full ∧ s'.rx_fifo.wvalid)
”;

val rx_fifo_regfile_tm = “
 let
   wptr: word6 = (5 >< 0) s.rx_fifo.wptr;
   wptr: word8 = w2w wptr;
   wptr: word6 = w2w wptr;
 in
   if s'.rx_fifo.incr_wptr
   then s' with rx_fifo_regfile := (wptr =+ s'.rx_fifo.wdata) s'.rx_fifo_regfile
   else s'
”;

val rx_fifo_counter_wptr_wrap_tm = “
 s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with wptr_wrap :=
   (s'.rx_fifo.incr_wptr ∧ (5 >< 0) s.rx_fifo.wptr = 63w : 6 word)
”;

val rx_fifo_counter_wptr_wrap_cnt_tm = “
 s' with rx_fifo := s'.rx_fifo with counter := s'.rx_fifo.counter with wptr_wrap_cnt :=
  if ¬word_bit 6 s.rx_fifo.wptr then 64w else 0w
”;

val rx_fifo_wptr_tm = “
 if s'.rx_fifo.reset then
   s' with rx_fifo := s'.rx_fifo with wptr := 0w
 else if s'.rx_fifo.counter.wptr_wrap then
   s' with rx_fifo := s'.rx_fifo with wptr := s'.rx_fifo.counter.wptr_wrap_cnt
 else
   s' with rx_fifo := s'.rx_fifo with wptr := s.rx_fifo.wptr + 1w
”;

val hw2reg_intr_state_nak_de_tm = “
 s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_de :=
 (s.fsm_state = transClockPulseAck ∧ ¬s'.fmt_flag.nak_ok ∧ fext.cio_sda_i)
”;

val hw2reg_intr_state_nak_d_tm = “
 s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with nak_d :=
 n2w $ bool_to_bit
     ( s.fsm_state = transClockPulseAck ∧ ¬s'.fmt_flag.nak_ok ∧ fext.cio_sda_i
     ∨ word_bit 0 s'.reg2hw.intr_state.nak_q)
”;

val next_intr_nak_o_tm = “
 s' with next_intr_nak_o := (word_bit 0 s'.reg2hw.intr_state.nak_q ∧ word_bit 0 s'.reg2hw.intr_enable.nak_q)
”

val hw2reg_intr_state_cmd_complete_de_tm = “
 s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_de :=
 (s.fsm_state = stopHoldStop ∨ s.fsm_state = startSetupStart ∧ s'.log_start ∧ s.pend_restart)
”;

val hw2reg_intr_state_cmd_complete_d_tm = “
 s' with hw2reg := s'.hw2reg with intr_state := s'.hw2reg.intr_state with cmd_complete_d :=
 if ( s.fsm_state = stopHoldStop ∨ s.fsm_state = startSetupStart ∧ s'.log_start ∧ s.pend_restart
 ∨ word_bit 0 s'.reg2hw.intr_state.cmd_complete_q ) then 1w else 0w
”

val next_intr_cmd_complete_o_tm = “
 s' with next_intr_cmd_complete_o := (word_bit 0 s'.reg2hw.intr_state.cmd_complete_q ∧ word_bit 0 s'.reg2hw.intr_enable.cmd_complete_q)
”;

val next_pend_restart_tm = “
 if s.pend_restart ∧ s.regs.ctrl.enablehost = 0w ∨ s'.log_start then s' with next_pend_restart := F
 else if s'.req_restart then s' with next_pend_restart := T
 else s' with next_pend_restart := s.pend_restart
”;

val next_trans_started_tm = “
 if s.trans_started ∧ s.regs.ctrl.enablehost = 0w ∨ s'.log_stop then s' with next_trans_started := F
 else if s'.log_start then s' with next_trans_started := T
 else s' with next_trans_started := s.trans_started
”;

val next_bit_index_tm = “
 if s'.bit_clr then s' with next_bit_index := 7w
 else if s'.bit_decr then s' with next_bit_index := s.bit_index - 1w
 else s' with next_bit_index := s.bit_index
”;

val i2c_core_ff_tm = “
  s' with fsm_state := s'.next_state
”;

val i2c_core_counter_ff_tm = “
  s' with counter := s'.next_counter
”;

val i2c_core_stretch_idle_cnt_ff_tm = “
  s' with stretch_idle_cnt := s'.next_stretch_idle_cnt
”;

val bit_index_ff_tm = “
  s' with bit_index := s'.next_bit_index
”;

val pend_restart_ff_tm = “
  s' with pend_restart := s'.next_pend_restart
”;

val byte_index_ff_tm = “
  s' with byte_index := s'.next_byte_index
”;

end
