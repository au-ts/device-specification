open HolKernel Parse boolLib bossLib;
open wordsTheory;
open wordsLib;
open cheshireCircuitTheory i2cRegsTheory;

val _ = new_theory "i2cRegsComm";

Datatype:
  i2c_reg2hw_intr_state = <|
    fmt_threshold_q: 1 word;
    rx_threshold_q: 1 word;
    fmt_overflow_q: 1 word;
    rx_overflow_q: 1 word;
    nak_q: 1 word;
    scl_interference_q: 1 word;
    sda_interference_q: 1 word;
    stretch_timeout_q: 1 word;
    sda_unstable_q: 1 word;
    cmd_complete_q: 1 word;
    tx_stretch_q: 1 word;
    tx_overflow_q: 1 word;
    acq_full_q: 1 word;
    unexp_stop_q: 1 word;
    host_timeout_q: 1 word;
  |>
End

Datatype:
  i2c_reg2hw_intr_enable = <|
    fmt_threshold_q: 1 word;
    rx_threshold_q: 1 word;
    fmt_overflow_q: 1 word;
    rx_overflow_q: 1 word;
    nak_q: 1 word;
    scl_interference_q: 1 word;
    sda_interference_q: 1 word;
    stretch_timeout_q: 1 word;
    sda_unstable_q: 1 word;
    cmd_complete_q: 1 word;
    tx_stretch_q: 1 word;
    tx_overflow_q: 1 word;
    acq_full_q: 1 word;
    unexp_stop_q: 1 word;
    host_timeout_q: 1 word;
  |>
End

Datatype:
  i2c_reg2hw_intr_test = <|
    fmt_threshold_q: 1 word;
    fmt_threshold_qe: bool;
    rx_threshold_q: 1 word;
    rx_threshold_qe: bool;
    fmt_overflow_q: 1 word;
    fmt_overflow_qe: bool;
    rx_overflow_q: 1 word;
    rx_overflow_qe: bool;
    nak_q: 1 word;
    nak_qe: bool;
    scl_interference_q: 1 word;
    scl_interference_qe: bool;
    sda_interference_q: 1 word;
    sda_interference_qe: bool;
    stretch_timeout_q: 1 word;
    stretch_timeout_qe: bool;
    sda_unstable_q: 1 word;
    sda_unstable_qe: bool;
    cmd_complete_q: 1 word;
    cmd_complete_qe: bool;
    tx_stretch_q: 1 word;
    tx_stretch_qe: bool;
    tx_overflow_q: 1 word;
    tx_overflow_qe: bool;
    acq_full_q: 1 word;
    acq_full_qe: bool;
    unexp_stop_q: 1 word;
    unexp_stop_qe: bool;
    host_timeout_q: 1 word;
    host_timeout_qe: bool;
  |>
End

Datatype:
  i2c_reg2hw_alert_test = <|
    fatal_fault_q: 1 word;
    fatal_fault_qe: bool;
  |>
End

Datatype:
  i2c_reg2hw_ctrl = <|
    enablehost_q: 1 word;
    enabletarget_q: 1 word;
    llpbk_q: 1 word;
  |>
End

Datatype:
  i2c_reg2hw_rdata = <|
    rdata_q: 8 word;
    rdata_re: bool;
  |>
End

Datatype:
  i2c_reg2hw_fdata = <|
    fbyte_q: 8 word;
    fbyte_qe: bool;
    start_q: 1 word;
    start_qe: bool;
    stop_q: 1 word;
    stop_qe: bool;
    read_q: 1 word;
    read_qe: bool;
    rcont_q: 1 word;
    rcont_qe: bool;
    nakok_q: 1 word;
    nakok_qe: bool;
  |>
End

Datatype:
  i2c_reg2hw_fifo_ctrl = <|
    rxrst_q: 1 word;
    rxrst_qe: bool;
    fmtrst_q: 1 word;
    fmtrst_qe: bool;
    rxilvl_q: 3 word;
    rxilvl_qe: bool;
    fmtilvl_q: 2 word;
    fmtilvl_qe: bool;
    acqrst_q: 1 word;
    acqrst_qe: bool;
    txrst_q: 1 word;
    txrst_qe: bool;
  |>
End

Datatype:
  i2c_reg2hw_ovrd = <|
    txovrden_q: 1 word;
    sclval_q: 1 word;
    sdaval_q: 1 word;
  |>
End

Datatype:
  i2c_reg2hw_timing0 = <|
    thigh_q: 16 word;
    tlow_q: 16 word;
  |>
End

Datatype:
  i2c_reg2hw_timing1 = <|
    t_r_q: 16 word;
    t_f_q: 16 word;
  |>
End

Datatype:
  i2c_reg2hw_timing2 = <|
    tsu_sta_q: 16 word;
    thd_sta_q: 16 word;
  |>
End

Datatype:
  i2c_reg2hw_timing3 = <|
    tsu_dat_q: 16 word;
    thd_dat_q: 16 word;
  |>
End

Datatype:
  i2c_reg2hw_timing4 = <|
    tsu_sto_q: 16 word;
    t_buf_q: 16 word;
  |>
End

Datatype:
  i2c_reg2hw_timeout_ctrl = <|
    val_q: 31 word;
    en_q: 1 word;
  |>
End

Datatype:
  i2c_reg2hw_target_id = <|
    address0_q: 7 word;
    mask0_q: 7 word;
    address1_q: 7 word;
    mask1_q: 7 word;
  |>
End

Datatype:
  i2c_reg2hw_acqdata = <|
    abyte_q: 8 word;
    abyte_re: bool;
    signal_q: 2 word;
    signal_re: bool;
  |>
End

Datatype:
  i2c_reg2hw_txdata = <|
    txdata_q: 8 word;
    txdata_qe: bool;
  |>
End

Datatype:
  i2c_reg2hw_host_timeout_ctrl = <|
    host_timeout_ctrl_q: 32 word;
  |>
End

Datatype:
  i2c_reg2hw = <|
    intr_state: i2c_reg2hw_intr_state;
    intr_enable: i2c_reg2hw_intr_enable;
    intr_test: i2c_reg2hw_intr_test;
    alert_test: i2c_reg2hw_alert_test;
    ctrl: i2c_reg2hw_ctrl;
    rdata: i2c_reg2hw_rdata;
    fdata: i2c_reg2hw_fdata;
    fifo_ctrl: i2c_reg2hw_fifo_ctrl;
    ovrd: i2c_reg2hw_ovrd;
    timing0: i2c_reg2hw_timing0;
    timing1: i2c_reg2hw_timing1;
    timing2: i2c_reg2hw_timing2;
    timing3: i2c_reg2hw_timing3;
    timing4: i2c_reg2hw_timing4;
    timeout_ctrl: i2c_reg2hw_timeout_ctrl;
    target_id: i2c_reg2hw_target_id;
    acqdata: i2c_reg2hw_acqdata;
    txdata: i2c_reg2hw_txdata;
    host_timeout_ctrl: i2c_reg2hw_host_timeout_ctrl;
  |>
End

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

Datatype:
  i2c_hw2reg = <|
    intr_state: i2c_hw2reg_intr_state;
    status: i2c_hw2reg_status;
    rdata: i2c_hw2reg_rdata;
    fifo_status: i2c_hw2reg_fifo_status;
    val: i2c_hw2reg_val;
    acqdata: i2c_hw2reg_acqdata;
  |>
End

Definition i2c_notif_rel_def:
  i2c_notif_rel (notif: i2c_notif option) (reg2hw: i2c_reg2hw) <=>
  (reg2hw.fdata.fbyte_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fdata.start_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fdata.stop_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fdata.read_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fdata.rcont_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fdata.nakok_qe <=> notif = SOME fdata_write) /\
  (reg2hw.fifo_ctrl.rxrst_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.fifo_ctrl.fmtrst_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.fifo_ctrl.rxilvl_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.fifo_ctrl.fmtilvl_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.fifo_ctrl.acqrst_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.fifo_ctrl.txrst_qe <=> notif = SOME fifo_ctrl_write) /\
  (reg2hw.txdata.txdata_qe <=> notif = SOME txdata_write)
End

Definition i2c_req_error_def:
  i2c_req_error (req: 7 reg_req) <=>
  req.valid /\ case req.addr of
    0x0w => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x4w => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x8w => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0xcw => req.write /\ ((0 >< 0) req.wstrb: 1 word) <> 1w
  | 0x10w => req.write /\ ((0 >< 0) req.wstrb: 1 word) <> 1w
  | 0x14w => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x18w => req.write /\ ((0 >< 0) req.wstrb: 1 word) <> 1w
  | 0x1cw => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x20w => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x24w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x28w => req.write /\ ((0 >< 0) req.wstrb: 1 word) <> 1w
  | 0x2cw => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x30w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x34w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x38w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x3cw => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x40w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x44w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x48w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | 0x4cw => req.write /\ ((1 >< 0) req.wstrb: 2 word) <> 3w
  | 0x50w => req.write /\ ((0 >< 0) req.wstrb: 1 word) <> 1w
  | 0x54w => req.write /\ ((3 >< 0) req.wstrb: 4 word) <> 15w
  | _ => T
End

Definition i2c_hwext_notif_rel_def:
  i2c_hwext_notif_rel (notif: i2c_hwext_notif option) (req: 7 reg_req) <=>
    ~i2c_req_error req /\
    (!value. notif = SOME (Write (intr_test_write value)) <=> req.addr = 0x8w /\ req.valid /\ req.write /\ i2c_intr_test_decode_write req.wdata = value) /\
    (!value. notif = SOME (Write (alert_test_write value)) <=> req.addr = 0xcw /\ req.valid /\ req.write /\ i2c_alert_test_decode_write req.wdata = value) /\
    (notif = SOME (Read rdata_read) <=> req.addr = 0x18w /\ req.valid /\ ~req.write) /\
    (notif = SOME (Read acqdata_read) <=> req.addr = 0x4cw /\ req.valid /\ ~req.write)
End

val _ = export_theory ();
