
structure i2cRegsCircuitLib =
struct

open wordsLib;
open i2cCircuitStateTheory i2cRegsTheory i2cRegsCommTheory;

(* The translator will only look for processes in the same theory as the
 * top-level `mk_module`, so we just export the bodies of these functions and
 * let `i2cCircuitTheory` make the actual definitions. *)
val i2c_reg_top_comb_1_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;
    write = word_bit 37 fext.reg_req_i;
    wstrb = (4 >< 1) fext.reg_req_i: word4;
    valid = word_bit 0 fext.reg_req_i;

    s' = case addr of
      0x0w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x4w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x8w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0xcw => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((0 >< 0) wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x10w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((0 >< 0) wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x14w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x18w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((0 >< 0) wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x1cw => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x20w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x24w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x28w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((0 >< 0) wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x2cw => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x30w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x34w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x38w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x3cw => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x40w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x44w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x48w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | 0x4cw => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((1 >< 0) wstrb: 2 word) <> 3w) s'.reg_rsp_o
    | 0x50w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((0 >< 0) wstrb: 1 word) <> 1w) s'.reg_rsp_o
    | 0x54w => s' with reg_rsp_o := (1 :+ valid /\ write /\ ((3 >< 0) wstrb: 4 word) <> 15w) s'.reg_rsp_o
    | _ => s' with reg_rsp_o := (1 :+ valid) s'.reg_rsp_o;
    s' = s' with reg_rsp_o := (0 :+ T) s'.reg_rsp_o;
  in
    s' with reg2hw := s'.reg2hw with <|
      intr_state := s'.reg2hw.intr_state with <|
        fmt_threshold_q := s'.regs.intr_state.fmt_threshold;
        rx_threshold_q := s'.regs.intr_state.rx_threshold;
        fmt_overflow_q := s'.regs.intr_state.fmt_overflow;
        rx_overflow_q := s'.regs.intr_state.rx_overflow;
        nak_q := s'.regs.intr_state.nak;
        scl_interference_q := s'.regs.intr_state.scl_interference;
        sda_interference_q := s'.regs.intr_state.sda_interference;
        stretch_timeout_q := s'.regs.intr_state.stretch_timeout;
        sda_unstable_q := s'.regs.intr_state.sda_unstable;
        cmd_complete_q := s'.regs.intr_state.cmd_complete;
        tx_stretch_q := s'.regs.intr_state.tx_stretch;
        tx_overflow_q := s'.regs.intr_state.tx_overflow;
        acq_full_q := s'.regs.intr_state.acq_full;
        unexp_stop_q := s'.regs.intr_state.unexp_stop;
        host_timeout_q := s'.regs.intr_state.host_timeout;
      |>;
      intr_enable := s'.reg2hw.intr_enable with <|
        fmt_threshold_q := s'.regs.intr_enable.fmt_threshold;
        rx_threshold_q := s'.regs.intr_enable.rx_threshold;
        fmt_overflow_q := s'.regs.intr_enable.fmt_overflow;
        rx_overflow_q := s'.regs.intr_enable.rx_overflow;
        nak_q := s'.regs.intr_enable.nak;
        scl_interference_q := s'.regs.intr_enable.scl_interference;
        sda_interference_q := s'.regs.intr_enable.sda_interference;
        stretch_timeout_q := s'.regs.intr_enable.stretch_timeout;
        sda_unstable_q := s'.regs.intr_enable.sda_unstable;
        cmd_complete_q := s'.regs.intr_enable.cmd_complete;
        tx_stretch_q := s'.regs.intr_enable.tx_stretch;
        tx_overflow_q := s'.regs.intr_enable.tx_overflow;
        acq_full_q := s'.regs.intr_enable.acq_full;
        unexp_stop_q := s'.regs.intr_enable.unexp_stop;
        host_timeout_q := s'.regs.intr_enable.host_timeout;
      |>;
      ctrl := s'.reg2hw.ctrl with <|
        enablehost_q := s'.regs.ctrl.enablehost;
        enabletarget_q := s'.regs.ctrl.enabletarget;
        llpbk_q := s'.regs.ctrl.llpbk;
      |>;
      fdata := s'.reg2hw.fdata with <|
        fbyte_q := s'.regs.fdata.fbyte;
        start_q := s'.regs.fdata.start;
        stop_q := s'.regs.fdata.stop;
        read_q := s'.regs.fdata.read;
        rcont_q := s'.regs.fdata.rcont;
        nakok_q := s'.regs.fdata.nakok;
      |>;
      fifo_ctrl := s'.reg2hw.fifo_ctrl with <|
        rxrst_q := s'.regs.fifo_ctrl.rxrst;
        fmtrst_q := s'.regs.fifo_ctrl.fmtrst;
        rxilvl_q := s'.regs.fifo_ctrl.rxilvl;
        fmtilvl_q := s'.regs.fifo_ctrl.fmtilvl;
        acqrst_q := s'.regs.fifo_ctrl.acqrst;
        txrst_q := s'.regs.fifo_ctrl.txrst;
      |>;
      ovrd := s'.reg2hw.ovrd with <|
        txovrden_q := s'.regs.ovrd.txovrden;
        sclval_q := s'.regs.ovrd.sclval;
        sdaval_q := s'.regs.ovrd.sdaval;
      |>;
      timing0 := s'.reg2hw.timing0 with <|
        thigh_q := s'.regs.timing0.thigh;
        tlow_q := s'.regs.timing0.tlow;
      |>;
      timing1 := s'.reg2hw.timing1 with <|
        t_r_q := s'.regs.timing1.t_r;
        t_f_q := s'.regs.timing1.t_f;
      |>;
      timing2 := s'.reg2hw.timing2 with <|
        tsu_sta_q := s'.regs.timing2.tsu_sta;
        thd_sta_q := s'.regs.timing2.thd_sta;
      |>;
      timing3 := s'.reg2hw.timing3 with <|
        tsu_dat_q := s'.regs.timing3.tsu_dat;
        thd_dat_q := s'.regs.timing3.thd_dat;
      |>;
      timing4 := s'.reg2hw.timing4 with <|
        tsu_sto_q := s'.regs.timing4.tsu_sto;
        t_buf_q := s'.regs.timing4.t_buf;
      |>;
      timeout_ctrl := s'.reg2hw.timeout_ctrl with <|
        val_q := s'.regs.timeout_ctrl.val;
        en_q := s'.regs.timeout_ctrl.en;
      |>;
      target_id := s'.reg2hw.target_id with <|
        address0_q := s'.regs.target_id.address0;
        mask0_q := s'.regs.target_id.mask0;
        address1_q := s'.regs.target_id.address1;
        mask1_q := s'.regs.target_id.mask1;
      |>;
      txdata := s'.reg2hw.txdata with <|
        txdata_q := s'.regs.txdata.txdata;
      |>;
      host_timeout_ctrl := s'.reg2hw.host_timeout_ctrl with <|
        host_timeout_ctrl_q := s'.regs.host_timeout_ctrl.host_timeout_ctrl;
      |>;
      intr_test := s'.reg2hw.intr_test with <|
        fmt_threshold_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        rx_threshold_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        fmt_overflow_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        rx_overflow_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        nak_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        scl_interference_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        sda_interference_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        stretch_timeout_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        sda_unstable_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        cmd_complete_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        tx_stretch_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        tx_overflow_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        acq_full_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        unexp_stop_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        host_timeout_qe := (addr = 0x8w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
      alert_test := s'.reg2hw.alert_test with <|
        fatal_fault_qe := (addr = 0xcw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
      rdata := s'.reg2hw.rdata with <|
        rdata_re := (addr = 0x18w /\ valid /\ ~write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
      acqdata := s'.reg2hw.acqdata with <|
        abyte_re := (addr = 0x4cw /\ valid /\ ~write /\ ~(word_bit 1 s'.reg_rsp_o));
        signal_re := (addr = 0x4cw /\ valid /\ ~write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
    |>
``

(* TODO: if we ever run into a situation where the `q` signal of a hwext
 * register is being read from by i2c_core, we'll need to add another one of
 * these that runs in between `d` being set and `q` being read. But there
 * doesn't seem to be anything like that right now, and I don't see why there
 * would be. *)
val i2c_reg_top_comb_2_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;

    s' = case addr of
      (* TODO: this won't produce the prettiest Verilog. To do that, we'd need to turn this into a let..in with an assignment for each field of the register, but that would make sharing code with the HOL version more annoying.
       * Alternatively, using @@ would be a lot less ugly than this. *)
      0x0w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.intr_state.fmt_threshold << 0) || (w2w s.regs.intr_state.rx_threshold << 1) || (w2w s.regs.intr_state.fmt_overflow << 2) || (w2w s.regs.intr_state.rx_overflow << 3) || (w2w s.regs.intr_state.nak << 4) || (w2w s.regs.intr_state.scl_interference << 5) || (w2w s.regs.intr_state.sda_interference << 6) || (w2w s.regs.intr_state.stretch_timeout << 7) || (w2w s.regs.intr_state.sda_unstable << 8) || (w2w s.regs.intr_state.cmd_complete << 9) || (w2w s.regs.intr_state.tx_stretch << 10) || (w2w s.regs.intr_state.tx_overflow << 11) || (w2w s.regs.intr_state.acq_full << 12) || (w2w s.regs.intr_state.unexp_stop << 13) || (w2w s.regs.intr_state.host_timeout << 14): word32) s'.reg_rsp_o
    | 0x4w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.intr_enable.fmt_threshold << 0) || (w2w s.regs.intr_enable.rx_threshold << 1) || (w2w s.regs.intr_enable.fmt_overflow << 2) || (w2w s.regs.intr_enable.rx_overflow << 3) || (w2w s.regs.intr_enable.nak << 4) || (w2w s.regs.intr_enable.scl_interference << 5) || (w2w s.regs.intr_enable.sda_interference << 6) || (w2w s.regs.intr_enable.stretch_timeout << 7) || (w2w s.regs.intr_enable.sda_unstable << 8) || (w2w s.regs.intr_enable.cmd_complete << 9) || (w2w s.regs.intr_enable.tx_stretch << 10) || (w2w s.regs.intr_enable.tx_overflow << 11) || (w2w s.regs.intr_enable.acq_full << 12) || (w2w s.regs.intr_enable.unexp_stop << 13) || (w2w s.regs.intr_enable.host_timeout << 14): word32) s'.reg_rsp_o
    | 0x8w => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0xcw => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x10w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.ctrl.enablehost << 0) || (w2w s.regs.ctrl.enabletarget << 1) || (w2w s.regs.ctrl.llpbk << 2): word32) s'.reg_rsp_o
    | 0x14w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.status.fmtfull_d << 0) || (w2w s'.hw2reg.status.rxfull_d << 1) || (w2w s'.hw2reg.status.fmtempty_d << 2) || (w2w s'.hw2reg.status.hostidle_d << 3) || (w2w s'.hw2reg.status.targetidle_d << 4) || (w2w s'.hw2reg.status.rxempty_d << 5) || (w2w s'.hw2reg.status.txfull_d << 6) || (w2w s'.hw2reg.status.acqfull_d << 7) || (w2w s'.hw2reg.status.txempty_d << 8) || (w2w s'.hw2reg.status.acqempty_d << 9): word32) s'.reg_rsp_o
    | 0x18w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.rdata.rdata_d << 0): word32) s'.reg_rsp_o
    | 0x1cw => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x20w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.fifo_ctrl.rxilvl << 2) || (w2w s.regs.fifo_ctrl.fmtilvl << 5): word32) s'.reg_rsp_o
    | 0x24w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.fifo_status.fmtlvl_d << 0) || (w2w s'.hw2reg.fifo_status.txlvl_d << 8) || (w2w s'.hw2reg.fifo_status.rxlvl_d << 16) || (w2w s'.hw2reg.fifo_status.acqlvl_d << 24): word32) s'.reg_rsp_o
    | 0x28w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.ovrd.txovrden << 0) || (w2w s.regs.ovrd.sclval << 1) || (w2w s.regs.ovrd.sdaval << 2): word32) s'.reg_rsp_o
    | 0x2cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.val.scl_rx_d << 0) || (w2w s'.hw2reg.val.sda_rx_d << 16): word32) s'.reg_rsp_o
    | 0x30w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing0.thigh << 0) || (w2w s.regs.timing0.tlow << 16): word32) s'.reg_rsp_o
    | 0x34w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing1.t_r << 0) || (w2w s.regs.timing1.t_f << 16): word32) s'.reg_rsp_o
    | 0x38w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing2.tsu_sta << 0) || (w2w s.regs.timing2.thd_sta << 16): word32) s'.reg_rsp_o
    | 0x3cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing3.tsu_dat << 0) || (w2w s.regs.timing3.thd_dat << 16): word32) s'.reg_rsp_o
    | 0x40w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timing4.tsu_sto << 0) || (w2w s.regs.timing4.t_buf << 16): word32) s'.reg_rsp_o
    | 0x44w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.timeout_ctrl.val << 0) || (w2w s.regs.timeout_ctrl.en << 31): word32) s'.reg_rsp_o
    | 0x48w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.target_id.address0 << 0) || (w2w s.regs.target_id.mask0 << 7) || (w2w s.regs.target_id.address1 << 14) || (w2w s.regs.target_id.mask1 << 21): word32) s'.reg_rsp_o
    | 0x4cw => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s'.hw2reg.acqdata.abyte_d << 0) || (w2w s'.hw2reg.acqdata.signal_d << 8): word32) s'.reg_rsp_o
    | 0x50w => s' with reg_rsp_o := bit_field_insert 33 2 (0w: word32) s'.reg_rsp_o
    | 0x54w => s' with reg_rsp_o := bit_field_insert 33 2 ((w2w s.regs.host_timeout_ctrl.host_timeout_ctrl << 0): word32) s'.reg_rsp_o
    | _ => s' with reg_rsp_o := bit_field_insert 33 2 (0xffffffffw: word32) s'.reg_rsp_o
  in
    s' with reg2hw := s'.reg2hw with <|
      rdata := s'.reg2hw.rdata with <|
        rdata_q := s'.hw2reg.rdata.rdata_d;
      |>;
      acqdata := s'.reg2hw.acqdata with <|
        abyte_q := s'.hw2reg.acqdata.abyte_d;
        signal_q := s'.hw2reg.acqdata.signal_d;
      |>;
    |>
``

val i2c_reg_top_ff_tm = ``
  let
    addr = (69 >< 38) fext.reg_req_i: word32;
    write = word_bit 37 fext.reg_req_i;
    wdata = (36 >< 5) fext.reg_req_i: word32;
    valid = word_bit 0 fext.reg_req_i;

    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_threshold := (if s'.hw2reg.intr_state.fmt_threshold_de then s'.hw2reg.intr_state.fmt_threshold_d else s.regs.intr_state.fmt_threshold) && ~((0 >< 0) wdata)
    else if s'.hw2reg.intr_state.fmt_threshold_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_threshold := s'.hw2reg.intr_state.fmt_threshold_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_threshold := (if s'.hw2reg.intr_state.rx_threshold_de then s'.hw2reg.intr_state.rx_threshold_d else s.regs.intr_state.rx_threshold) && ~((1 >< 1) wdata)
    else if s'.hw2reg.intr_state.rx_threshold_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_threshold := s'.hw2reg.intr_state.rx_threshold_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_overflow := (if s'.hw2reg.intr_state.fmt_overflow_de then s'.hw2reg.intr_state.fmt_overflow_d else s.regs.intr_state.fmt_overflow) && ~((2 >< 2) wdata)
    else if s'.hw2reg.intr_state.fmt_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with fmt_overflow := s'.hw2reg.intr_state.fmt_overflow_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_overflow := (if s'.hw2reg.intr_state.rx_overflow_de then s'.hw2reg.intr_state.rx_overflow_d else s.regs.intr_state.rx_overflow) && ~((3 >< 3) wdata)
    else if s'.hw2reg.intr_state.rx_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with rx_overflow := s'.hw2reg.intr_state.rx_overflow_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with nak := (if s'.hw2reg.intr_state.nak_de then s'.hw2reg.intr_state.nak_d else s.regs.intr_state.nak) && ~((4 >< 4) wdata)
    else if s'.hw2reg.intr_state.nak_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with nak := s'.hw2reg.intr_state.nak_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with scl_interference := (if s'.hw2reg.intr_state.scl_interference_de then s'.hw2reg.intr_state.scl_interference_d else s.regs.intr_state.scl_interference) && ~((5 >< 5) wdata)
    else if s'.hw2reg.intr_state.scl_interference_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with scl_interference := s'.hw2reg.intr_state.scl_interference_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_interference := (if s'.hw2reg.intr_state.sda_interference_de then s'.hw2reg.intr_state.sda_interference_d else s.regs.intr_state.sda_interference) && ~((6 >< 6) wdata)
    else if s'.hw2reg.intr_state.sda_interference_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_interference := s'.hw2reg.intr_state.sda_interference_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with stretch_timeout := (if s'.hw2reg.intr_state.stretch_timeout_de then s'.hw2reg.intr_state.stretch_timeout_d else s.regs.intr_state.stretch_timeout) && ~((7 >< 7) wdata)
    else if s'.hw2reg.intr_state.stretch_timeout_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with stretch_timeout := s'.hw2reg.intr_state.stretch_timeout_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_unstable := (if s'.hw2reg.intr_state.sda_unstable_de then s'.hw2reg.intr_state.sda_unstable_d else s.regs.intr_state.sda_unstable) && ~((8 >< 8) wdata)
    else if s'.hw2reg.intr_state.sda_unstable_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with sda_unstable := s'.hw2reg.intr_state.sda_unstable_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with cmd_complete := (if s'.hw2reg.intr_state.cmd_complete_de then s'.hw2reg.intr_state.cmd_complete_d else s.regs.intr_state.cmd_complete) && ~((9 >< 9) wdata)
    else if s'.hw2reg.intr_state.cmd_complete_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with cmd_complete := s'.hw2reg.intr_state.cmd_complete_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_stretch := (if s'.hw2reg.intr_state.tx_stretch_de then s'.hw2reg.intr_state.tx_stretch_d else s.regs.intr_state.tx_stretch) && ~((10 >< 10) wdata)
    else if s'.hw2reg.intr_state.tx_stretch_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_stretch := s'.hw2reg.intr_state.tx_stretch_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_overflow := (if s'.hw2reg.intr_state.tx_overflow_de then s'.hw2reg.intr_state.tx_overflow_d else s.regs.intr_state.tx_overflow) && ~((11 >< 11) wdata)
    else if s'.hw2reg.intr_state.tx_overflow_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with tx_overflow := s'.hw2reg.intr_state.tx_overflow_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with acq_full := (if s'.hw2reg.intr_state.acq_full_de then s'.hw2reg.intr_state.acq_full_d else s.regs.intr_state.acq_full) && ~((12 >< 12) wdata)
    else if s'.hw2reg.intr_state.acq_full_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with acq_full := s'.hw2reg.intr_state.acq_full_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with unexp_stop := (if s'.hw2reg.intr_state.unexp_stop_de then s'.hw2reg.intr_state.unexp_stop_d else s.regs.intr_state.unexp_stop) && ~((13 >< 13) wdata)
    else if s'.hw2reg.intr_state.unexp_stop_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with unexp_stop := s'.hw2reg.intr_state.unexp_stop_d
    else
      s';
    s' = if addr = 0x0w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with host_timeout := (if s'.hw2reg.intr_state.host_timeout_de then s'.hw2reg.intr_state.host_timeout_d else s.regs.intr_state.host_timeout) && ~((14 >< 14) wdata)
    else if s'.hw2reg.intr_state.host_timeout_de then
      s' with regs := s'.regs with intr_state := s'.regs.intr_state with host_timeout := s'.hw2reg.intr_state.host_timeout_d
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with fmt_threshold := (0 >< 0) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with rx_threshold := (1 >< 1) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with fmt_overflow := (2 >< 2) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with rx_overflow := (3 >< 3) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with nak := (4 >< 4) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with scl_interference := (5 >< 5) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with sda_interference := (6 >< 6) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with stretch_timeout := (7 >< 7) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with sda_unstable := (8 >< 8) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with cmd_complete := (9 >< 9) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with tx_stretch := (10 >< 10) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with tx_overflow := (11 >< 11) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with acq_full := (12 >< 12) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with unexp_stop := (13 >< 13) wdata
    else
      s';
    s' = if addr = 0x4w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with intr_enable := s'.regs.intr_enable with host_timeout := (14 >< 14) wdata
    else
      s';
    s' = if addr = 0x10w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with enablehost := (0 >< 0) wdata
    else
      s';
    s' = if addr = 0x10w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with enabletarget := (1 >< 1) wdata
    else
      s';
    s' = if addr = 0x10w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ctrl := s'.regs.ctrl with llpbk := (2 >< 2) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with fbyte := (7 >< 0) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with start := (8 >< 8) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with stop := (9 >< 9) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with read := (10 >< 10) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with rcont := (11 >< 11) wdata
    else
      s';
    s' = if addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fdata := s'.regs.fdata with nakok := (12 >< 12) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with rxrst := (0 >< 0) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with fmtrst := (1 >< 1) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with rxilvl := (4 >< 2) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with fmtilvl := (6 >< 5) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with acqrst := (7 >< 7) wdata
    else
      s';
    s' = if addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with fifo_ctrl := s'.regs.fifo_ctrl with txrst := (8 >< 8) wdata
    else
      s';
    s' = if addr = 0x28w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with txovrden := (0 >< 0) wdata
    else
      s';
    s' = if addr = 0x28w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with sclval := (1 >< 1) wdata
    else
      s';
    s' = if addr = 0x28w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with ovrd := s'.regs.ovrd with sdaval := (2 >< 2) wdata
    else
      s';
    s' = if addr = 0x30w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing0 := s'.regs.timing0 with thigh := (15 >< 0) wdata
    else
      s';
    s' = if addr = 0x30w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing0 := s'.regs.timing0 with tlow := (31 >< 16) wdata
    else
      s';
    s' = if addr = 0x34w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing1 := s'.regs.timing1 with t_r := (15 >< 0) wdata
    else
      s';
    s' = if addr = 0x34w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing1 := s'.regs.timing1 with t_f := (31 >< 16) wdata
    else
      s';
    s' = if addr = 0x38w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing2 := s'.regs.timing2 with tsu_sta := (15 >< 0) wdata
    else
      s';
    s' = if addr = 0x38w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing2 := s'.regs.timing2 with thd_sta := (31 >< 16) wdata
    else
      s';
    s' = if addr = 0x3cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing3 := s'.regs.timing3 with tsu_dat := (15 >< 0) wdata
    else
      s';
    s' = if addr = 0x3cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing3 := s'.regs.timing3 with thd_dat := (31 >< 16) wdata
    else
      s';
    s' = if addr = 0x40w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing4 := s'.regs.timing4 with tsu_sto := (15 >< 0) wdata
    else
      s';
    s' = if addr = 0x40w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timing4 := s'.regs.timing4 with t_buf := (31 >< 16) wdata
    else
      s';
    s' = if addr = 0x44w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timeout_ctrl := s'.regs.timeout_ctrl with val := (30 >< 0) wdata
    else
      s';
    s' = if addr = 0x44w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with timeout_ctrl := s'.regs.timeout_ctrl with en := (31 >< 31) wdata
    else
      s';
    s' = if addr = 0x48w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with address0 := (6 >< 0) wdata
    else
      s';
    s' = if addr = 0x48w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with mask0 := (13 >< 7) wdata
    else
      s';
    s' = if addr = 0x48w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with address1 := (20 >< 14) wdata
    else
      s';
    s' = if addr = 0x48w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with target_id := s'.regs.target_id with mask1 := (27 >< 21) wdata
    else
      s';
    s' = if addr = 0x50w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with txdata := s'.regs.txdata with txdata := (7 >< 0) wdata
    else
      s';
    s' = if addr = 0x54w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o) then
      s' with regs := s'.regs with host_timeout_ctrl := s'.regs.host_timeout_ctrl with host_timeout_ctrl := (31 >< 0) wdata
    else
      s';
  in
    s' with reg2hw := s'.reg2hw with <|
      fdata := s'.reg2hw.fdata with <|
        fbyte_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        start_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        stop_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        read_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        rcont_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        nakok_qe := (addr = 0x1cw /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
      fifo_ctrl := s'.reg2hw.fifo_ctrl with <|
        rxrst_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        fmtrst_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        rxilvl_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        fmtilvl_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        acqrst_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
        txrst_qe := (addr = 0x20w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
      txdata := s'.reg2hw.txdata with <|
        txdata_qe := (addr = 0x50w /\ valid /\ write /\ ~(word_bit 1 s'.reg_rsp_o));
      |>;
    |>
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
