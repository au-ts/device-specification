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

(*
* This record is basically the same with the record `counter` above.
* This is a hack to circumvent the limitation of the translator framework.
*
* The problem is that creating an identifier for a signal structured in a record
* only look up to one level only. Hence if the record `fifo` and `fifo2` each
* has the field `counter`, the name of the signal `wptr_wrap_cnt` (member of the
* record `counter`) would be `counter_wptr_wrap_cnt` and one cannot distinguish
* whether it belongs to `fifo` or `fifo2` anymore.
*)

Datatype:
  counter2 = <|
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
  fifo2 = <|
    reset   : bool;
    wvalid  : bool;
    wready  : bool;
    wdata   : 13 word;
    depth   : 7 word;
    rvalid  : bool;
    rready  : bool;
    rdata   : 13 word;
    rptr    : 7 word;
    wptr    : 7 word;
    incr_wptr : bool;
    incr_rptr : bool;
    empty   : bool;
    full    : bool;
    counter2: counter2;
  |>
End

Datatype:
  fifo = <|
    reset   : bool;
    wvalid  : bool;
    wready  : bool;
    wdata   : 8 word;
    depth   : 7 word;
    rvalid  : bool;
    rready  : bool;
    rdata   : 8 word;
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
    fsm_state : 5 word;
    next_state : 5 word;
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
    fmt_fifo : fifo2;
    rx_fifo : fifo;
    cnt_gt_one: bool;
    fmt_fifo_regfile : 6 word -> 13 word;
    rx_fifo_regfile : 6 word -> 8 word;
  |>
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
    i2c_win_ready cstate.win_buses
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
  >> simp [i2c_state_rel_def, i2c_notif_rel_def, i2c_core_state_rel_def, i2c_hwext_read_rel_def, i2c_win_read_rel_def]
  >> simp [i2c_get_status_fmtfull_def, i2c_get_status_rxfull_def, i2c_get_status_fmtempty_def, i2c_get_status_hostidle_def, i2c_get_status_targetidle_def, i2c_get_status_rxempty_def, i2c_get_status_txfull_def, i2c_get_status_acqfull_def, i2c_get_status_txempty_def, i2c_get_status_acqempty_def, i2c_get_rdata_rdata_def, i2c_get_fifo_status_fmtlvl_def, i2c_get_fifo_status_txlvl_def, i2c_get_fifo_status_rxlvl_def, i2c_get_fifo_status_acqlvl_def, i2c_get_val_scl_rx_def, i2c_get_val_sda_rx_def, i2c_get_acqdata_abyte_def, i2c_get_acqdata_signal_def]
QED

val _ = export_theory ();
