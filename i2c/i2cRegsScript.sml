open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory("i2cRegs");

Datatype:
  i2c_intr_state_fields = <|
    fmt_threshold : 1 word;
    rx_threshold : 1 word;
    fmt_overflow : 1 word;
    rx_overflow : 1 word;
    nak : 1 word;
    scl_interference : 1 word;
    sda_interference : 1 word;
    stretch_timeout : 1 word;
    sda_unstable : 1 word;
    cmd_complete : 1 word;
    tx_stretch : 1 word;
    tx_overflow : 1 word;
    acq_full : 1 word;
    unexp_stop : 1 word;
    host_timeout : 1 word;
  |>
End

Datatype:
  i2c_intr_enable_fields = <|
    fmt_threshold : 1 word;
    rx_threshold : 1 word;
    fmt_overflow : 1 word;
    rx_overflow : 1 word;
    nak : 1 word;
    scl_interference : 1 word;
    sda_interference : 1 word;
    stretch_timeout : 1 word;
    sda_unstable : 1 word;
    cmd_complete : 1 word;
    tx_stretch : 1 word;
    tx_overflow : 1 word;
    acq_full : 1 word;
    unexp_stop : 1 word;
    host_timeout : 1 word;
  |>
End

Datatype:
  i2c_intr_test_fields = <|
    fmt_threshold : 1 word;
    rx_threshold : 1 word;
    fmt_overflow : 1 word;
    rx_overflow : 1 word;
    nak : 1 word;
    scl_interference : 1 word;
    sda_interference : 1 word;
    stretch_timeout : 1 word;
    sda_unstable : 1 word;
    cmd_complete : 1 word;
    tx_stretch : 1 word;
    tx_overflow : 1 word;
    acq_full : 1 word;
    unexp_stop : 1 word;
    host_timeout : 1 word;
  |>
End

Datatype:
  i2c_alert_test_fields = <|
    fatal_fault : 1 word;
  |>
End

Datatype:
  i2c_ctrl_fields = <|
    enablehost : 1 word;
    enabletarget : 1 word;
    llpbk : 1 word;
  |>
End

Datatype:
  i2c_fdata_fields = <|
    fbyte : 8 word;
    start : 1 word;
    stop : 1 word;
    read : 1 word;
    rcont : 1 word;
    nakok : 1 word;
  |>
End

Datatype:
  i2c_fifo_ctrl_fields = <|
    rxrst : 1 word;
    fmtrst : 1 word;
    rxilvl : 3 word;
    fmtilvl : 2 word;
    acqrst : 1 word;
    txrst : 1 word;
  |>
End

Datatype:
  i2c_ovrd_fields = <|
    txovrden : 1 word;
    sclval : 1 word;
    sdaval : 1 word;
  |>
End

Datatype:
  i2c_timing0_fields = <|
    thigh : 16 word;
    tlow : 16 word;
  |>
End

Datatype:
  i2c_timing1_fields = <|
    t_r : 16 word;
    t_f : 16 word;
  |>
End

Datatype:
  i2c_timing2_fields = <|
    tsu_sta : 16 word;
    thd_sta : 16 word;
  |>
End

Datatype:
  i2c_timing3_fields = <|
    tsu_dat : 16 word;
    thd_dat : 16 word;
  |>
End

Datatype:
  i2c_timing4_fields = <|
    tsu_sto : 16 word;
    t_buf : 16 word;
  |>
End

Datatype:
  i2c_timeout_ctrl_fields = <|
    val : 31 word;
    en : 1 word;
  |>
End

Datatype:
  i2c_target_id_fields = <|
    address0 : 7 word;
    mask0 : 7 word;
    address1 : 7 word;
    mask1 : 7 word;
  |>
End

Datatype:
  i2c_txdata_fields = <|
    txdata : 8 word;
  |>
End

Datatype:
  i2c_host_timeout_ctrl_fields = <|
    host_timeout_ctrl : 32 word;
  |>
End

Datatype:
  i2c_regs = <|
    intr_state : i2c_intr_state_fields;
    intr_enable : i2c_intr_enable_fields;
    ctrl : i2c_ctrl_fields;
    fdata : i2c_fdata_fields;
    fifo_ctrl : i2c_fifo_ctrl_fields;
    ovrd : i2c_ovrd_fields;
    timing0 : i2c_timing0_fields;
    timing1 : i2c_timing1_fields;
    timing2 : i2c_timing2_fields;
    timing3 : i2c_timing3_fields;
    timing4 : i2c_timing4_fields;
    timeout_ctrl : i2c_timeout_ctrl_fields;
    target_id : i2c_target_id_fields;
    txdata : i2c_txdata_fields;
    host_timeout_ctrl : i2c_host_timeout_ctrl_fields;
  |>
End

Datatype:
  i2c_hwext_read_notif = rdata_read | acqdata_read
End

Datatype:
  i2c_hwext_write_notif = intr_test_write i2c_intr_test_fields | alert_test_write i2c_alert_test_fields
End

Datatype:
  i2c_hwext_notif = Read i2c_hwext_read_notif | Write i2c_hwext_write_notif
End

Datatype:
  i2c_notif = fdata_write | fifo_ctrl_write | txdata_write
End

val _ = export_theory();
