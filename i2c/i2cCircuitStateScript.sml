open HolKernel Parse boolLib bossLib;
open i2cRegsTheory i2cRegsCommTheory;

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
    read_continue : bool;
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
    next_delay : 20 word;
    load_tcount : bool;
    log_start : bool;
    log_stop : bool;
    scl_rx_val : 16 word;
    next_scl_rx_val : 16 word;
    stretch_idle_cnt : 32 word;
    next_stretch_idle_cnt : 32 word;
    stretch_en : bool;
    scl_d : bool;
    sda_d : bool;
    scl_q : bool;
    sda_q : bool;
    scl_o : bool;
    sda_o : bool;
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
    en_sda_interf_det: bool;
    sda_rise_cnt: 17 word;
    under_rst : bool;
    fmt_fifo : 13 fifo;
    rx_fifo : 8 fifo;
    tx_fifo : 8 fifo;
    acq_fifo : 10 fifo;
    cnt_gt_one: bool;
    fmt_threshold_q : bool;
    fmt_threshold_d : bool;
    rx_threshold_q : bool;
    rx_threshold_d : bool;
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
    expect_stop: bool;
    (* Whether acq_fifo has _two_ free slots (as opposed to one free slot for
     * acq_fifo.wready). *)
    acq_fifo_2free: bool;

    event_fmt_threshold: bool;
    event_rx_threshold: bool;
    event_fmt_overflow: bool;
    event_rx_overflow: bool;
    event_nak: bool;
    event_scl_interference: bool;
    event_sda_interference: bool;
    event_stretch_timeout: bool;
    event_sda_unstable: bool;
    event_cmd_complete: bool;
    (* Interrupts with `IntrT = "Status"` need this extra field. *)
    test_tx_stretch: bool;
    event_tx_stretch: bool;
    event_tx_overflow: bool;
    test_acq_full: bool;
    event_acq_full: bool;
    event_unexp_stop: bool;
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

val _ = export_theory ();
