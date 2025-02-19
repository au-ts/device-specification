
structure i2cRegsCircuitLib =
struct

open wordsLib;
open i2cCircuitStateTheory i2cRegsTheory i2cRegsCommTheory;

(* The translator will only look for processes in the same theory as the
 * top-level `mk_module`, so we just export the bodies of these functions and
 * let `i2cCircuitTheory` make the actual definitions. *)
val i2c_reg_top_comb_1_tm = ``
  let
    s' = s' with addr := (69 >< 38) fext.reg_req_i;
    s' = s' with write := word_bit 37 fext.reg_req_i;
    s' = s' with wdata := (36 >< 5) fext.reg_req_i;
    s' = s' with wstrb := (4 >< 1) fext.reg_req_i;
    s' = s' with valid := word_bit 0 fext.reg_req_i;

    s' = case s'.addr of
      0x0w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x4w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x8w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0xcw => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((0 >< 0) s'.wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x10w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((0 >< 0) s'.wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x14w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x18w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((0 >< 0) s'.wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x1cw => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x20w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x24w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x28w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((0 >< 0) s'.wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x2cw => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x30w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x34w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x38w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x3cw => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x40w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x44w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x48w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x4cw => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((1 >< 0) s'.wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x50w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((0 >< 0) s'.wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x54w => s' with reg_rsp_o := (1 :+ s'.valid /\ s'.write /\ ((3 >< 0) s'.wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | _ => s' with reg_rsp_o := (1 :+ s'.valid) s'.reg_rsp_o;
    s' = s' with reg_rsp_o := (0 :+ T) s'.reg_rsp_o;

    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with fmt_threshold_q := s.regs.intr_state.fmt_threshold;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with rx_threshold_q := s.regs.intr_state.rx_threshold;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with fmt_overflow_q := s.regs.intr_state.fmt_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with rx_overflow_q := s.regs.intr_state.rx_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with nak_q := s.regs.intr_state.nak;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with scl_interference_q := s.regs.intr_state.scl_interference;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with sda_interference_q := s.regs.intr_state.sda_interference;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with stretch_timeout_q := s.regs.intr_state.stretch_timeout;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with sda_unstable_q := s.regs.intr_state.sda_unstable;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with cmd_complete_q := s.regs.intr_state.cmd_complete;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with tx_stretch_q := s.regs.intr_state.tx_stretch;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with tx_overflow_q := s.regs.intr_state.tx_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with acq_full_q := s.regs.intr_state.acq_full;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with unexp_stop_q := s.regs.intr_state.unexp_stop;
    s' = s' with reg2hw := s'.reg2hw with intr_state := s'.reg2hw.intr_state with host_timeout_q := s.regs.intr_state.host_timeout;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with fmt_threshold_q := s.regs.intr_enable.fmt_threshold;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with rx_threshold_q := s.regs.intr_enable.rx_threshold;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with fmt_overflow_q := s.regs.intr_enable.fmt_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with rx_overflow_q := s.regs.intr_enable.rx_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with nak_q := s.regs.intr_enable.nak;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with scl_interference_q := s.regs.intr_enable.scl_interference;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with sda_interference_q := s.regs.intr_enable.sda_interference;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with stretch_timeout_q := s.regs.intr_enable.stretch_timeout;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with sda_unstable_q := s.regs.intr_enable.sda_unstable;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with cmd_complete_q := s.regs.intr_enable.cmd_complete;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with tx_stretch_q := s.regs.intr_enable.tx_stretch;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with tx_overflow_q := s.regs.intr_enable.tx_overflow;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with acq_full_q := s.regs.intr_enable.acq_full;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with unexp_stop_q := s.regs.intr_enable.unexp_stop;
    s' = s' with reg2hw := s'.reg2hw with intr_enable := s'.reg2hw.intr_enable with host_timeout_q := s.regs.intr_enable.host_timeout;
    s' = s' with reg2hw := s'.reg2hw with ctrl := s'.reg2hw.ctrl with enablehost_q := s.regs.ctrl.enablehost;
    s' = s' with reg2hw := s'.reg2hw with ctrl := s'.reg2hw.ctrl with enabletarget_q := s.regs.ctrl.enabletarget;
    s' = s' with reg2hw := s'.reg2hw with ctrl := s'.reg2hw.ctrl with llpbk_q := s.regs.ctrl.llpbk;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with fbyte_q := s.regs.fdata.fbyte;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with start_q := s.regs.fdata.start;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with stop_q := s.regs.fdata.stop;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with read_q := s.regs.fdata.read;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with rcont_q := s.regs.fdata.rcont;
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with nakok_q := s.regs.fdata.nakok;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with rxrst_q := s.regs.fifo_ctrl.rxrst;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with fmtrst_q := s.regs.fifo_ctrl.fmtrst;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with rxilvl_q := s.regs.fifo_ctrl.rxilvl;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with fmtilvl_q := s.regs.fifo_ctrl.fmtilvl;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with acqrst_q := s.regs.fifo_ctrl.acqrst;
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with txrst_q := s.regs.fifo_ctrl.txrst;
    s' = s' with reg2hw := s'.reg2hw with ovrd := s'.reg2hw.ovrd with txovrden_q := s.regs.ovrd.txovrden;
    s' = s' with reg2hw := s'.reg2hw with ovrd := s'.reg2hw.ovrd with sclval_q := s.regs.ovrd.sclval;
    s' = s' with reg2hw := s'.reg2hw with ovrd := s'.reg2hw.ovrd with sdaval_q := s.regs.ovrd.sdaval;
    s' = s' with reg2hw := s'.reg2hw with timing0 := s'.reg2hw.timing0 with thigh_q := s.regs.timing0.thigh;
    s' = s' with reg2hw := s'.reg2hw with timing0 := s'.reg2hw.timing0 with tlow_q := s.regs.timing0.tlow;
    s' = s' with reg2hw := s'.reg2hw with timing1 := s'.reg2hw.timing1 with t_r_q := s.regs.timing1.t_r;
    s' = s' with reg2hw := s'.reg2hw with timing1 := s'.reg2hw.timing1 with t_f_q := s.regs.timing1.t_f;
    s' = s' with reg2hw := s'.reg2hw with timing2 := s'.reg2hw.timing2 with tsu_sta_q := s.regs.timing2.tsu_sta;
    s' = s' with reg2hw := s'.reg2hw with timing2 := s'.reg2hw.timing2 with thd_sta_q := s.regs.timing2.thd_sta;
    s' = s' with reg2hw := s'.reg2hw with timing3 := s'.reg2hw.timing3 with tsu_dat_q := s.regs.timing3.tsu_dat;
    s' = s' with reg2hw := s'.reg2hw with timing3 := s'.reg2hw.timing3 with thd_dat_q := s.regs.timing3.thd_dat;
    s' = s' with reg2hw := s'.reg2hw with timing4 := s'.reg2hw.timing4 with tsu_sto_q := s.regs.timing4.tsu_sto;
    s' = s' with reg2hw := s'.reg2hw with timing4 := s'.reg2hw.timing4 with t_buf_q := s.regs.timing4.t_buf;
    s' = s' with reg2hw := s'.reg2hw with timeout_ctrl := s'.reg2hw.timeout_ctrl with val_q := s.regs.timeout_ctrl.val;
    s' = s' with reg2hw := s'.reg2hw with timeout_ctrl := s'.reg2hw.timeout_ctrl with en_q := s.regs.timeout_ctrl.en;
    s' = s' with reg2hw := s'.reg2hw with target_id := s'.reg2hw.target_id with address0_q := s.regs.target_id.address0;
    s' = s' with reg2hw := s'.reg2hw with target_id := s'.reg2hw.target_id with mask0_q := s.regs.target_id.mask0;
    s' = s' with reg2hw := s'.reg2hw with target_id := s'.reg2hw.target_id with address1_q := s.regs.target_id.address1;
    s' = s' with reg2hw := s'.reg2hw with target_id := s'.reg2hw.target_id with mask1_q := s.regs.target_id.mask1;
    s' = s' with reg2hw := s'.reg2hw with txdata := s'.reg2hw.txdata with txdata_q := s.regs.txdata.txdata;
    s' = s' with reg2hw := s'.reg2hw with host_timeout_ctrl := s'.reg2hw.host_timeout_ctrl with host_timeout_ctrl_q := s.regs.host_timeout_ctrl.host_timeout_ctrl;

    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with fmt_threshold_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with rx_threshold_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with fmt_overflow_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with rx_overflow_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with nak_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with scl_interference_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with sda_interference_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with stretch_timeout_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with sda_unstable_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with cmd_complete_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with tx_stretch_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with tx_overflow_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with acq_full_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with unexp_stop_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with intr_test := s'.reg2hw.intr_test with host_timeout_qe := (s'.addr = 0x8w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with alert_test := s'.reg2hw.alert_test with fatal_fault_qe := (s'.addr = 0xcw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with rdata := s'.reg2hw.rdata with rdata_re := (s'.addr = 0x18w /\ s'.valid /\ ~s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with acqdata := s'.reg2hw.acqdata with abyte_re := (s'.addr = 0x4cw /\ s'.valid /\ ~s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with acqdata := s'.reg2hw.acqdata with signal_re := (s'.addr = 0x4cw /\ s'.valid /\ ~s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
  in
    s'
``

(* TODO: if we ever run into a situation where the `q` signal of a hwext
 * register is being read from by i2c_core, we'll need to add another one of
 * these that runs in between `d` being set and `q` being read. But there
 * doesn't seem to be anything like that right now, and I don't see why there
 * would be. *)
val i2c_reg_top_comb_2_tm = ``
  let
    s' = case s'.addr of
      (* TODO: this won't produce the prettiest Verilog. To do that, we'd need to turn
       * this into a let..in with an assignment for each field of the register, but
       * that would make sharing code with the HOL version more annoying.
       *
       * Alternatively, using @@ would be a lot less ugly than this. *)
      0x0w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.intr_state.fmt_threshold <<~ 0w) || (w2w s.regs.intr_state.rx_threshold <<~ 1w) || (w2w s.regs.intr_state.fmt_overflow <<~ 2w) || (w2w s.regs.intr_state.rx_overflow <<~ 3w) || (w2w s.regs.intr_state.nak <<~ 4w) || (w2w s.regs.intr_state.scl_interference <<~ 5w) || (w2w s.regs.intr_state.sda_interference <<~ 6w) || (w2w s.regs.intr_state.stretch_timeout <<~ 7w) || (w2w s.regs.intr_state.sda_unstable <<~ 8w) || (w2w s.regs.intr_state.cmd_complete <<~ 9w) || (w2w s.regs.intr_state.tx_stretch <<~ 10w) || (w2w s.regs.intr_state.tx_overflow <<~ 11w) || (w2w s.regs.intr_state.acq_full <<~ 12w) || (w2w s.regs.intr_state.unexp_stop <<~ 13w) || (w2w s.regs.intr_state.host_timeout <<~ 14w): word32) s'.reg_rsp_o
    | 0x4w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.intr_enable.fmt_threshold <<~ 0w) || (w2w s.regs.intr_enable.rx_threshold <<~ 1w) || (w2w s.regs.intr_enable.fmt_overflow <<~ 2w) || (w2w s.regs.intr_enable.rx_overflow <<~ 3w) || (w2w s.regs.intr_enable.nak <<~ 4w) || (w2w s.regs.intr_enable.scl_interference <<~ 5w) || (w2w s.regs.intr_enable.sda_interference <<~ 6w) || (w2w s.regs.intr_enable.stretch_timeout <<~ 7w) || (w2w s.regs.intr_enable.sda_unstable <<~ 8w) || (w2w s.regs.intr_enable.cmd_complete <<~ 9w) || (w2w s.regs.intr_enable.tx_stretch <<~ 10w) || (w2w s.regs.intr_enable.tx_overflow <<~ 11w) || (w2w s.regs.intr_enable.acq_full <<~ 12w) || (w2w s.regs.intr_enable.unexp_stop <<~ 13w) || (w2w s.regs.intr_enable.host_timeout <<~ 14w): word32) s'.reg_rsp_o
    | 0x8w => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0xcw => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x10w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.ctrl.enablehost <<~ 0w) || (w2w s.regs.ctrl.enabletarget <<~ 1w) || (w2w s.regs.ctrl.llpbk <<~ 2w): word32) s'.reg_rsp_o
    | 0x14w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.status.fmtfull_d <<~ 0w) || (w2w s'.hw2reg.status.rxfull_d <<~ 1w) || (w2w s'.hw2reg.status.fmtempty_d <<~ 2w) || (w2w s'.hw2reg.status.hostidle_d <<~ 3w) || (w2w s'.hw2reg.status.targetidle_d <<~ 4w) || (w2w s'.hw2reg.status.rxempty_d <<~ 5w) || (w2w s'.hw2reg.status.txfull_d <<~ 6w) || (w2w s'.hw2reg.status.acqfull_d <<~ 7w) || (w2w s'.hw2reg.status.txempty_d <<~ 8w) || (w2w s'.hw2reg.status.acqempty_d <<~ 9w): word32) s'.reg_rsp_o
    | 0x18w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.rdata.rdata_d <<~ 0w): word32) s'.reg_rsp_o
    | 0x1cw => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x20w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.fifo_ctrl.rxilvl <<~ 2w) || (w2w s.regs.fifo_ctrl.fmtilvl <<~ 5w): word32) s'.reg_rsp_o
    | 0x24w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.fifo_status.fmtlvl_d <<~ 0w) || (w2w s'.hw2reg.fifo_status.txlvl_d <<~ 8w) || (w2w s'.hw2reg.fifo_status.rxlvl_d <<~ 16w) || (w2w s'.hw2reg.fifo_status.acqlvl_d <<~ 24w): word32) s'.reg_rsp_o
    | 0x28w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.ovrd.txovrden <<~ 0w) || (w2w s.regs.ovrd.sclval <<~ 1w) || (w2w s.regs.ovrd.sdaval <<~ 2w): word32) s'.reg_rsp_o
    | 0x2cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.val.scl_rx_d <<~ 0w) || (w2w s'.hw2reg.val.sda_rx_d <<~ 16w): word32) s'.reg_rsp_o
    | 0x30w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing0.thigh <<~ 0w) || (w2w s.regs.timing0.tlow <<~ 16w): word32) s'.reg_rsp_o
    | 0x34w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing1.t_r <<~ 0w) || (w2w s.regs.timing1.t_f <<~ 16w): word32) s'.reg_rsp_o
    | 0x38w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing2.tsu_sta <<~ 0w) || (w2w s.regs.timing2.thd_sta <<~ 16w): word32) s'.reg_rsp_o
    | 0x3cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing3.tsu_dat <<~ 0w) || (w2w s.regs.timing3.thd_dat <<~ 16w): word32) s'.reg_rsp_o
    | 0x40w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing4.tsu_sto <<~ 0w) || (w2w s.regs.timing4.t_buf <<~ 16w): word32) s'.reg_rsp_o
    | 0x44w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timeout_ctrl.val <<~ 0w) || (w2w s.regs.timeout_ctrl.en <<~ 31w): word32) s'.reg_rsp_o
    | 0x48w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.target_id.address0 <<~ 0w) || (w2w s.regs.target_id.mask0 <<~ 7w) || (w2w s.regs.target_id.address1 <<~ 14w) || (w2w s.regs.target_id.mask1 <<~ 21w): word32) s'.reg_rsp_o
    | 0x4cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.acqdata.abyte_d <<~ 0w) || (w2w s'.hw2reg.acqdata.signal_d <<~ 8w): word32) s'.reg_rsp_o
    | 0x50w => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x54w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.host_timeout_ctrl.host_timeout_ctrl <<~ 0w): word32) s'.reg_rsp_o
    | _ => s' with reg_rsp_o := bit_field_insert 33 2 (0xffffffffw: word32) s'.reg_rsp_o;

    s' = s' with reg2hw := s'.reg2hw with rdata := s'.reg2hw.rdata with rdata_q := s'.hw2reg.rdata.rdata_d;
    s' = s' with reg2hw := s'.reg2hw with acqdata := s'.reg2hw.acqdata with abyte_q := s'.hw2reg.acqdata.abyte_d;
    s' = s' with reg2hw := s'.reg2hw with acqdata := s'.reg2hw.acqdata with signal_q := s'.hw2reg.acqdata.signal_d;
  in
    s'
``

val i2c_reg_top_ff_tm = ``
  let
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_threshold := (if s'.hw2reg.intr_state.fmt_threshold_de then s'.hw2reg.intr_state.fmt_threshold_d else s.regs.intr_state.fmt_threshold) && ~((0 >< 0) s'.wdata)
    else if s'.hw2reg.intr_state.fmt_threshold_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_threshold := s'.hw2reg.intr_state.fmt_threshold_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_threshold := (if s'.hw2reg.intr_state.rx_threshold_de then s'.hw2reg.intr_state.rx_threshold_d else s.regs.intr_state.rx_threshold) && ~((1 >< 1) s'.wdata)
    else if s'.hw2reg.intr_state.rx_threshold_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_threshold := s'.hw2reg.intr_state.rx_threshold_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_overflow := (if s'.hw2reg.intr_state.fmt_overflow_de then s'.hw2reg.intr_state.fmt_overflow_d else s.regs.intr_state.fmt_overflow) && ~((2 >< 2) s'.wdata)
    else if s'.hw2reg.intr_state.fmt_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_overflow := s'.hw2reg.intr_state.fmt_overflow_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_overflow := (if s'.hw2reg.intr_state.rx_overflow_de then s'.hw2reg.intr_state.rx_overflow_d else s.regs.intr_state.rx_overflow) && ~((3 >< 3) s'.wdata)
    else if s'.hw2reg.intr_state.rx_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_overflow := s'.hw2reg.intr_state.rx_overflow_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with nak := (if s'.hw2reg.intr_state.nak_de then s'.hw2reg.intr_state.nak_d else s.regs.intr_state.nak) && ~((4 >< 4) s'.wdata)
    else if s'.hw2reg.intr_state.nak_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with nak := s'.hw2reg.intr_state.nak_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with scl_interference := (if s'.hw2reg.intr_state.scl_interference_de then s'.hw2reg.intr_state.scl_interference_d else s.regs.intr_state.scl_interference) && ~((5 >< 5) s'.wdata)
    else if s'.hw2reg.intr_state.scl_interference_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with scl_interference := s'.hw2reg.intr_state.scl_interference_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_interference := (if s'.hw2reg.intr_state.sda_interference_de then s'.hw2reg.intr_state.sda_interference_d else s.regs.intr_state.sda_interference) && ~((6 >< 6) s'.wdata)
    else if s'.hw2reg.intr_state.sda_interference_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_interference := s'.hw2reg.intr_state.sda_interference_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with stretch_timeout := (if s'.hw2reg.intr_state.stretch_timeout_de then s'.hw2reg.intr_state.stretch_timeout_d else s.regs.intr_state.stretch_timeout) && ~((7 >< 7) s'.wdata)
    else if s'.hw2reg.intr_state.stretch_timeout_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with stretch_timeout := s'.hw2reg.intr_state.stretch_timeout_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_unstable := (if s'.hw2reg.intr_state.sda_unstable_de then s'.hw2reg.intr_state.sda_unstable_d else s.regs.intr_state.sda_unstable) && ~((8 >< 8) s'.wdata)
    else if s'.hw2reg.intr_state.sda_unstable_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_unstable := s'.hw2reg.intr_state.sda_unstable_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with cmd_complete := (if s'.hw2reg.intr_state.cmd_complete_de then s'.hw2reg.intr_state.cmd_complete_d else s.regs.intr_state.cmd_complete) && ~((9 >< 9) s'.wdata)
    else if s'.hw2reg.intr_state.cmd_complete_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with cmd_complete := s'.hw2reg.intr_state.cmd_complete_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_stretch := (if s'.hw2reg.intr_state.tx_stretch_de then s'.hw2reg.intr_state.tx_stretch_d else s.regs.intr_state.tx_stretch) && ~((10 >< 10) s'.wdata)
    else if s'.hw2reg.intr_state.tx_stretch_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_stretch := s'.hw2reg.intr_state.tx_stretch_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_overflow := (if s'.hw2reg.intr_state.tx_overflow_de then s'.hw2reg.intr_state.tx_overflow_d else s.regs.intr_state.tx_overflow) && ~((11 >< 11) s'.wdata)
    else if s'.hw2reg.intr_state.tx_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_overflow := s'.hw2reg.intr_state.tx_overflow_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with acq_full := (if s'.hw2reg.intr_state.acq_full_de then s'.hw2reg.intr_state.acq_full_d else s.regs.intr_state.acq_full) && ~((12 >< 12) s'.wdata)
    else if s'.hw2reg.intr_state.acq_full_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with acq_full := s'.hw2reg.intr_state.acq_full_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with unexp_stop := (if s'.hw2reg.intr_state.unexp_stop_de then s'.hw2reg.intr_state.unexp_stop_d else s.regs.intr_state.unexp_stop) && ~((13 >< 13) s'.wdata)
    else if s'.hw2reg.intr_state.unexp_stop_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with unexp_stop := s'.hw2reg.intr_state.unexp_stop_d
    else
      s';
    s' = if s'.addr = 0x0w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with host_timeout := (if s'.hw2reg.intr_state.host_timeout_de then s'.hw2reg.intr_state.host_timeout_d else s.regs.intr_state.host_timeout) && ~((14 >< 14) s'.wdata)
    else if s'.hw2reg.intr_state.host_timeout_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with host_timeout := s'.hw2reg.intr_state.host_timeout_d
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with fmt_threshold := (0 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with rx_threshold := (1 >< 1) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with fmt_overflow := (2 >< 2) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with rx_overflow := (3 >< 3) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with nak := (4 >< 4) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with scl_interference := (5 >< 5) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with sda_interference := (6 >< 6) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with stretch_timeout := (7 >< 7) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with sda_unstable := (8 >< 8) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with cmd_complete := (9 >< 9) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with tx_stretch := (10 >< 10) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with tx_overflow := (11 >< 11) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with acq_full := (12 >< 12) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with unexp_stop := (13 >< 13) s'.wdata
    else
      s';
    s' = if s'.addr = 0x4w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with host_timeout := (14 >< 14) s'.wdata
    else
      s';
    s' = if s'.addr = 0x10w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with enablehost := (0 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x10w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with enabletarget := (1 >< 1) s'.wdata
    else
      s';
    s' = if s'.addr = 0x10w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with llpbk := (2 >< 2) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with fbyte := (7 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with start := (8 >< 8) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with stop := (9 >< 9) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with read := (10 >< 10) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with rcont := (11 >< 11) s'.wdata
    else
      s';
    s' = if s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with nakok := (12 >< 12) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with rxrst := (0 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with fmtrst := (1 >< 1) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with rxilvl := (4 >< 2) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with fmtilvl := (6 >< 5) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with acqrst := (7 >< 7) s'.wdata
    else
      s';
    s' = if s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with txrst := (8 >< 8) s'.wdata
    else
      s';
    s' = if s'.addr = 0x28w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with txovrden := (0 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x28w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with sclval := (1 >< 1) s'.wdata
    else
      s';
    s' = if s'.addr = 0x28w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with sdaval := (2 >< 2) s'.wdata
    else
      s';
    s' = if s'.addr = 0x30w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing0 := s'.regs.timing0 with thigh := (15 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x30w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing0 := s'.regs.timing0 with tlow := (31 >< 16) s'.wdata
    else
      s';
    s' = if s'.addr = 0x34w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing1 := s'.regs.timing1 with t_r := (15 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x34w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing1 := s'.regs.timing1 with t_f := (31 >< 16) s'.wdata
    else
      s';
    s' = if s'.addr = 0x38w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing2 := s'.regs.timing2 with tsu_sta := (15 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x38w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing2 := s'.regs.timing2 with thd_sta := (31 >< 16) s'.wdata
    else
      s';
    s' = if s'.addr = 0x3cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing3 := s'.regs.timing3 with tsu_dat := (15 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x3cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing3 := s'.regs.timing3 with thd_dat := (31 >< 16) s'.wdata
    else
      s';
    s' = if s'.addr = 0x40w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing4 := s'.regs.timing4 with tsu_sto := (15 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x40w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing4 := s'.regs.timing4 with t_buf := (31 >< 16) s'.wdata
    else
      s';
    s' = if s'.addr = 0x44w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timeout_ctrl := s'.regs.timeout_ctrl with val := (30 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x44w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timeout_ctrl := s'.regs.timeout_ctrl with en := (31 >< 31) s'.wdata
    else
      s';
    s' = if s'.addr = 0x48w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with address0 := (6 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x48w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with mask0 := (13 >< 7) s'.wdata
    else
      s';
    s' = if s'.addr = 0x48w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with address1 := (20 >< 14) s'.wdata
    else
      s';
    s' = if s'.addr = 0x48w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with mask1 := (27 >< 21) s'.wdata
    else
      s';
    s' = if s'.addr = 0x50w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with txdata := s'.regs.txdata with txdata := (7 >< 0) s'.wdata
    else
      s';
    s' = if s'.addr = 0x54w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with host_timeout_ctrl := s'.regs.host_timeout_ctrl with host_timeout_ctrl := (31 >< 0) s'.wdata
    else
      s';

    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with fbyte_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with start_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with stop_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with read_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with rcont_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fdata := s'.reg2hw.fdata with nakok_qe := (s'.addr = 0x1cw /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with rxrst_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with fmtrst_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with rxilvl_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with fmtilvl_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with acqrst_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with fifo_ctrl := s'.reg2hw.fifo_ctrl with txrst_qe := (s'.addr = 0x20w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
    s' = s' with reg2hw := s'.reg2hw with txdata := s'.reg2hw.txdata with txdata_qe := (s'.addr = 0x50w /\ s'.valid /\ s'.write /\ ~(word_bit 1 s'.reg_rsp_o));
  in
    s'
``

val i2c_regs_init_tm = ``
  (<|
    intr_state := <|
      fmt_threshold := 0w;
      rx_threshold := 0w;
      fmt_overflow := 0w;
      rx_overflow := 0w;
      nak := 0w;
      scl_interference := 0w;
      sda_interference := 0w;
      stretch_timeout := 0w;
      sda_unstable := 0w;
      cmd_complete := 0w;
      tx_stretch := 0w;
      tx_overflow := 0w;
      acq_full := 0w;
      unexp_stop := 0w;
      host_timeout := 0w;
    |>;
    intr_enable := <|
      fmt_threshold := 0w;
      rx_threshold := 0w;
      fmt_overflow := 0w;
      rx_overflow := 0w;
      nak := 0w;
      scl_interference := 0w;
      sda_interference := 0w;
      stretch_timeout := 0w;
      sda_unstable := 0w;
      cmd_complete := 0w;
      tx_stretch := 0w;
      tx_overflow := 0w;
      acq_full := 0w;
      unexp_stop := 0w;
      host_timeout := 0w;
    |>;
    ctrl := <|
      enablehost := 0w;
      enabletarget := 0w;
      llpbk := 0w;
    |>;
  |>): i2c_regs
``;

val i2c_reg2hw_init_tm = ``
  (<|
    fdata := <|
      fbyte_qe := F;
      start_qe := F;
      stop_qe := F;
      read_qe := F;
      rcont_qe := F;
      nakok_qe := F;
    |>;
    fifo_ctrl := <|
      rxrst_qe := F;
      fmtrst_qe := F;
      rxilvl_qe := F;
      fmtilvl_qe := F;
      acqrst_qe := F;
      txrst_qe := F;
    |>;
    txdata := <|
      txdata_qe := F;
    |>;
  |>): i2c_reg2hw
``;

val i2c_reg_comms = ["regs_intr_state_fmt_threshold", "regs_intr_state_rx_threshold", "regs_intr_state_fmt_overflow", "regs_intr_state_rx_overflow", "regs_intr_state_nak", "regs_intr_state_scl_interference", "regs_intr_state_sda_interference", "regs_intr_state_stretch_timeout", "regs_intr_state_sda_unstable", "regs_intr_state_cmd_complete", "regs_intr_state_tx_stretch", "regs_intr_state_tx_overflow", "regs_intr_state_acq_full", "regs_intr_state_unexp_stop", "regs_intr_state_host_timeout", "regs_intr_enable_fmt_threshold", "regs_intr_enable_rx_threshold", "regs_intr_enable_fmt_overflow", "regs_intr_enable_rx_overflow", "regs_intr_enable_nak", "regs_intr_enable_scl_interference", "regs_intr_enable_sda_interference", "regs_intr_enable_stretch_timeout", "regs_intr_enable_sda_unstable", "regs_intr_enable_cmd_complete", "regs_intr_enable_tx_stretch", "regs_intr_enable_tx_overflow", "regs_intr_enable_acq_full", "regs_intr_enable_unexp_stop", "regs_intr_enable_host_timeout", "regs_ctrl_enablehost", "regs_ctrl_enabletarget", "regs_ctrl_llpbk", "regs_fdata_fbyte", "regs_fdata_start", "regs_fdata_stop", "regs_fdata_read", "regs_fdata_rcont", "regs_fdata_nakok", "regs_fifo_ctrl_rxrst", "regs_fifo_ctrl_fmtrst", "regs_fifo_ctrl_rxilvl", "regs_fifo_ctrl_fmtilvl", "regs_fifo_ctrl_acqrst", "regs_fifo_ctrl_txrst", "regs_ovrd_txovrden", "regs_ovrd_sclval", "regs_ovrd_sdaval", "regs_timing0_thigh", "regs_timing0_tlow", "regs_timing1_t_r", "regs_timing1_t_f", "regs_timing2_tsu_sta", "regs_timing2_thd_sta", "regs_timing3_tsu_dat", "regs_timing3_thd_dat", "regs_timing4_tsu_sto", "regs_timing4_t_buf", "regs_timeout_ctrl_val", "regs_timeout_ctrl_en", "regs_target_id_address0", "regs_target_id_mask0", "regs_target_id_address1", "regs_target_id_mask1", "regs_txdata_txdata", "regs_host_timeout_ctrl_host_timeout_ctrl", "reg2hw_fdata_fbyte_qe", "reg2hw_fdata_start_qe", "reg2hw_fdata_stop_qe", "reg2hw_fdata_read_qe", "reg2hw_fdata_rcont_qe", "reg2hw_fdata_nakok_qe", "reg2hw_fifo_ctrl_rxrst_qe", "reg2hw_fifo_ctrl_fmtrst_qe", "reg2hw_fifo_ctrl_rxilvl_qe", "reg2hw_fifo_ctrl_fmtilvl_qe", "reg2hw_fifo_ctrl_acqrst_qe", "reg2hw_fifo_ctrl_txrst_qe", "reg2hw_txdata_txdata_qe"];

end
