open HolKernel Parse boolLib bossLib;
open i2cCoreTheory i2cRegsTheory i2cRegsCommTheory;

val _ = new_theory "i2cCircuitState";

Datatype:
  i2c_circuit_ext_state = <|
    (* 48-bit (DefaultCfg.AddrWidth) addr + 32-bit data + 4-bit strobe + 2 bits of write/valid *)
    reg_req_i: 86 word;

    cio_scl_i: bool;
    cio_sda_i: bool;
  |>
End

Datatype:
  i2c_delay = <|
    setup_start: 20 word;
    hold_start: 20 word;
    setup_data: 20 word;
    clock_start: 20 word;
    clock_low: 20 word;
    clock_pulse: 20 word;
    hold_bit: 20 word;
    clock_stop: 20 word;
    setup_stop: 20 word;
    hold_stop: 20 word;
  |>
End

Datatype:
  counter = <|
    wptr_wrap : bool ;
    wptr_wrap_cnt : 7 word;
    rptr_wrap : bool;
    rptr_wrap_cnt : 7 word;
  |>
End

Datatype:
  fmt_flag = <|
    start_before : bool;
    stop_after : bool;
    read_bytes : bool;
    nak_ok : bool;
  |>
End

Datatype:
  fifo = <|
    reset   : bool;
    wvalid  : bool;
    wready  : bool;
    wdata   : 'a word;
    depth   : 7 word;
    rvalid  : bool;
    rready  : bool;
    rdata   : 'a word;
    rptr    : 7 word;
    wptr    : 7 word;
    incr_wptr : bool;
    incr_rptr : bool;
    empty   : bool;
    full    : bool;
    counter : counter;
  |>
End

Datatype:
  i2c_circuit_state = <|
    (* 32-bit data + 2 bits of error/ready *)
    reg_rsp_o: 34 word;

    cio_scl_o: bool;
    cio_scl_en_o: bool;
    cio_sda_o: bool;
    cio_sda_en_o: bool;

    intr_fmt_threshold_o: bool;
    intr_rx_threshold_o: bool;
    intr_fmt_overflow_o: bool;
    intr_rx_overflow_o: bool;
    intr_nak_o: bool;
    intr_scl_interference_o: bool;
    intr_sda_interference_o: bool;
    intr_stretch_timeout_o: bool;
    intr_sda_unstable_o: bool;
    intr_cmd_complete_o: bool;
    intr_tx_stretch_o: bool;
    intr_tx_overflow_o: bool;
    intr_acq_full_o: bool;
    intr_unexp_stop_o: bool;
    intr_host_timeout_o: bool;

    (* The storage for the values of all our memory-mapped I/O registers.
     *
     * We can't just assign to `reg2hw.*.*.q` directly because for hwo registers,
     * there are no such signals. (There aren't actually any instances of non-hwext
     * hwo registers in Cheshire I2C, though.) *)
    regs: i2c_regs;

    (* Wires for communication between i2cCircuitTheory and i2cRegsCircuitLib (the
     * same as the ones in real hardware). *)
    reg2hw: i2c_reg2hw;
    hw2reg: i2c_hw2reg;
    win_buses: i2c_win_buses;

    (* The decoded fields of `reg_req_i`. *)
    raw_addr: word7;
    addr: word7;
    write: bool;
    wdata: word32;
    wstrb: word4;
    valid: bool;
    (* `reg_rsp_o.error`, if it's being determined by us and not by a window. *)
    error: bool;

    (* required for i2c_core *)
    target_loopback: bool;
    scl_buf: bool;
    sda_buf: bool;
    scl_sync: bool;
    sda_sync: bool;
    fsm_state : 6 word;
    next_state : 6 word;
    counter : 20 word;
    next_counter : 20 word;
    byte_index : 9 word;
    next_byte_index : 9 word;
    next_bit_index : 3 word;
    bit_index : 3 word;
    next_pend_restart: bool;
    pend_restart : bool;
    next_trans_started: bool;
    trans_started : bool;
    req_restart : bool;
    bit_clr : bool;
    bit_decr : bool;
    delay : i2c_delay;
    curr_delay : 20 word;
    load_tcount : bool;
    log_start : bool;
    log_stop : bool;
    scl_rx_val : 16 word;
    next_scl_rx_val : 16 word;
    stretch_idle_cnt : 32 word;
    next_stretch_idle_cnt : 32 word;
    stretch_en : bool;
    scl_d : bool;
    byte_clr : bool;
    byte_decr : bool;
    byte_num :  9 word;
    next_sda_rx_val : 16 word;
    sda_rx_val : 16 word;
    read_byte_clr : bool;
    shift_data_en : bool;
    next_read_byte : 8 word;
    read_byte : 8 word;
    fmt_flag : fmt_flag;
    fmt_byte : 8 word;
    next_intr_nak_o : bool;
    next_intr_cmd_complete_o : bool;
    under_rst : bool;
    fmt_fifo : 13 fifo;
    rx_fifo : 8 fifo;
    tx_fifo : 8 fifo;
    acq_fifo : 10 fifo;
    cnt_gt_one: bool;
    fmt_threshold_q : 1 word;
    fmt_threshold_d : 1 word;
    rx_threshold_q : 1 word;
    rx_threshold_d : 1 word;
    scl_i_q : bool;
    sda_i_q : bool;
    fmt_fifo_regfile : 6 word -> 13 word;
    rx_fifo_regfile : 6 word -> 8 word;
    tx_fifo_regfile : 6 word -> 8 word;
    acq_fifo_regfile : 6 word -> 10 word;
    start_det : bool;
    stop_det : bool;
    address_match: bool;
    input_byte: 8 word;
    input_byte_clr: bool;
    stretch_tx: bool;
    bit_idx: 4 word;
    rw_bit: bool;
    host_ack: bool;
    host_idle: bool;
    target_idle: bool;

    (* event_fmt_threshold: bool; *)
    (* event_rx_threshold: bool; *)
    (* event_fmt_overflow: bool; *)
    (* event_rx_overflow: bool; *)
    (* event_nak: bool; *)
    (* event_scl_interference: bool; *)
    (* event_sda_interference: bool; *)
    event_stretch_timeout: bool;
    (* event_sda_unstable: bool; *)
    (* event_cmd_complete: bool; *)
    (* event_tx_stretch: bool; *)
    (* event_tx_overflow: bool; *)
    (* event_unexp_stop: bool; *)
    event_host_timeout: bool;
  |>
End

Overload idle = “0w : 6 word”;
Overload active = “1w : 6 word”;
Overload popFmtFifo = “2w : 6 word”;
Overload setupStart = “3w : 6 word”;
Overload holdStart = “4w : 6 word”;
Overload clockStart = “5w : 6 word”;
Overload setupStop = “6w : 6 word”;
Overload holdStop = “7w : 6 word”;
Overload clockStop = “8w : 6 word”;
Overload clockLow = “9w : 6 word”;
Overload clockPulse = “10w : 6 word”;
Overload holdBit = “11w : 6 word”;
Overload clockLowAck = “12w : 6 word”;
Overload clockPulseAck = “13w : 6 word”;
Overload holdDevAck = “14w : 6 word”;
Overload readClockLow = “15w : 6 word”;
Overload readClockPulse = “16w : 6 word”;
Overload readHoldBit = “17w : 6 word”;
Overload hostClockLowAck = “18w : 6 word”;
Overload hostClockPulseAck = “19w : 6 word”;
Overload hostHoldBitAck = “20w : 6 word”;
Overload acquireStart = “21w : 6 word”;
Overload addrRead = “22w : 6 word”;
Overload addrAckWait = “23w : 6 word”;
Overload addrAckSetup = “24w : 6 word”;
Overload addrAckPulse = “25w : 6 word”;
Overload addrAckHold = “26w : 6 word”;
Overload transmitWait = “27w : 6 word”;
Overload transmitSetup = “28w : 6 word”;
Overload transmitPulse = “29w : 6 word”;
Overload transmitHold = “30w : 6 word”;
Overload transmitAck = “31w : 6 word”;
Overload transmitAckPulse = “32w : 6 word”;
Overload waitForStop = “33w : 6 word”;
Overload acquireByte = “34w : 6 word”;
Overload acquireAckWait = “35w : 6 word”;
Overload acquireAckSetup = “36w : 6 word”;
Overload acquireAckPulse = “37w : 6 word”;
Overload acquireAckHold = “38w : 6 word”;
Overload stretchAddr = “39w : 6 word”;
Overload stretchTx = “40w : 6 word”;
Overload stretchTxSetup = “41w : 6 word”;
Overload stretchAcqFull = “42w : 6 word”;

Definition encode_fsm_def:
  encode_fsm (machine: fsmState) =
  case machine of
    Idle => idle
  | Active => active
  | Transmitting ClockLow => clockLow
  | Transmitting ClockPulse => clockPulse
  | Transmitting HoldBit => holdBit
  | Transmitting ClockLowAck => clockLowAck
  | Transmitting ClockPulseAck => clockPulseAck
  | Transmitting HoldDevAck => holdDevAck
  | Receiving ReadClockLow => readClockLow
  | Receiving ReadClockPulse => readClockPulse
  | Receiving ReadHoldBit => readHoldBit
  | Receiving HostClockLowAck => hostClockLowAck
  | Receiving HostClockPulseAck => hostClockPulseAck
  | Receiving HostHoldBitAck => hostHoldBitAck
  | Starting SetupStart => setupStart
  | Starting HoldStart => holdStart
  | Starting ClockStart => clockStart
  | Stopping ClockStop => clockStop
  | Stopping SetupStop => setupStop
  | Stopping HoldStop => holdStop
  | PopFmtFifo => popFmtFifo
End

Definition fifo_rel_def:
  (fifo_rel [] (circuit : 'a word -> 'b) (rptr : 'c word) wptr ⇔ rptr = wptr)
∧ (fifo_rel (w :: ws) circuit rptr wptr ⇔
     ((word_bit (dimindex(:'c) - 1) rptr = word_bit (dimindex(:'c) - 1) wptr) ⇒ wptr >+ rptr)
   ∧ ((word_bit (dimindex(:'c) - 1) rptr ≠ word_bit (dimindex(:'c) - 1) wptr) ⇒
      ((dimindex(:'a) - 1 >< 0) wptr : 'a word) <=+ ((dimindex(:'a) - 1 >< 0) rptr :'a word))
   ∧ (circuit $ ((dimindex(:'a) - 1 >< 0) rptr : 'a word) = w)
   ∧ fifo_rel ws circuit (rptr + 1w) wptr)
End

Definition core_sim_rel_def:
  core_sim_rel (machine : i2c_state) (circuit: i2c_circuit_state) =
  ( fifo_rel machine.rx_fifo circuit.rx_fifo_regfile circuit.rx_fifo.rptr circuit.rx_fifo.wptr
  ∧ fifo_rel machine.fmt_fifo circuit.fmt_fifo_regfile circuit.fmt_fifo.rptr circuit.fmt_fifo.wptr
  ∧ encode_fsm (machine.fsm_state) = circuit.fsm_state
  ∧ machine.counter = circuit.counter
  ∧ machine.pend_restart = circuit.pend_restart
  ∧ machine.trans_started = circuit.trans_started
  ∧ machine.bit_index = circuit.bit_index
  ∧ machine.stretch_idle_cnt = circuit.stretch_idle_cnt
  ∧ machine.byte_index = circuit.byte_index
  ∧ machine.read_byte = circuit.read_byte
  ∧ machine.scl_rx_val = circuit.scl_rx_val
  ∧ machine.sda_rx_val = circuit.sda_rx_val
  ∧ machine.regs = circuit.regs
  )
End

Definition i2c_core_state_rel_def:

  (* mstate = model state, cstate = circuit state *)
  i2c_core_state_rel (mstate: i2c_state) (cstate: i2c_circuit_state) <=>
    i2c_hwext_read_rel mstate cstate.hw2reg /\
    i2c_win_read_rel mstate cstate.win_buses /\
    (* We shouldn't really be assuming this: it's true for I2C and SPI, but in
     * general it should be perfectly fine for an access to take more than 1 cycle
     * to complete.
     *
     * Right now, though, the structure of our model assumes that an access will
     * never take more than one cycle, and I don't want to deal with fixing that
     * just yet; besides, much of the work of fixing this would go towards Cheshire-
     * specific code, when I don't think it's likely that we're going to find a
     * Cheshire peripheral which doesn't respond immediately. *)
    i2c_win_ready cstate.win_buses /\
    core_sim_rel mstate cstate
End

Definition i2c_state_rel_def:
  i2c_state_rel (mstate: i2c_state) (cstate: i2c_circuit_state) <=>
    mstate.regs = cstate.regs /\
    i2c_notif_rel mstate.buffered_notif cstate.reg2hw /\
    i2c_core_state_rel mstate cstate
End

Theorem i2c_state_rel_fnums:
  i2c_state_rel (st with fnums := fnums) = i2c_state_rel st
Proof
  irule EQ_EXT
  >> simp [i2c_state_rel_def, i2c_notif_rel_def, i2c_core_state_rel_def, i2c_hwext_read_rel_def, i2c_win_read_rel_def, core_sim_rel_def]
  >> simp [i2c_get_status_fmtfull_def, i2c_get_status_rxfull_def, i2c_get_status_fmtempty_def, i2c_get_status_hostidle_def, i2c_get_status_targetidle_def, i2c_get_status_rxempty_def, i2c_get_status_txfull_def, i2c_get_status_acqfull_def, i2c_get_status_txempty_def, i2c_get_status_acqempty_def, i2c_get_rdata_rdata_def, i2c_get_fifo_status_fmtlvl_def, i2c_get_fifo_status_txlvl_def, i2c_get_fifo_status_rxlvl_def, i2c_get_fifo_status_acqlvl_def, i2c_get_val_scl_rx_def, i2c_get_val_sda_rx_def, i2c_get_acqdata_abyte_def, i2c_get_acqdata_signal_def]
QED

val _ = export_theory ();
