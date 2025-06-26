open HolKernel Parse boolLib bossLib;
open spi_hostCoreTheory spi_hostRegsTheory spi_hostRegsCommTheory;

val _ = new_theory "spi_hostCircuitState";

Datatype:
  spi_host_circuit_ext_state = <|
    (* 48-bit (DefaultCfg.AddrWidth) addr + 32-bit data + 4-bit strobe + 2 bits of write/valid *)
    reg_req_i: 86 word;

    cio_scl_i: bool;
    cio_sda_i: bool;
  |>
End

Datatype:
  spi_host_circuit_state = <|
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
     * hwo registers in Cheshire spi_host, though.) *)
    regs: spi_host_regs;

    (* Wires for communication between spi_hostCircuitTheory and spi_hostRegsCircuitLib (the
     * same as the ones in real hardware). *)
    reg2hw: spi_host_reg2hw;
    hw2reg: spi_host_hw2reg;

    (* The decoded fields of `reg_req_i`. *)
    addr: word6;
    write: bool;
    wdata: word32;
    wstrb: word4;
    valid: bool;
  |>
End

Definition spi_host_core_state_rel_def:
  (* mstate = model state, cstate = circuit state *)
  spi_host_core_state_rel (mstate: spi_host_state) (cstate: spi_host_circuit_state) =
    spi_host_hwext_read_rel mstate cstate.hw2reg
End

Definition spi_host_state_rel_def:
  spi_host_state_rel (mstate: spi_host_state) (cstate: spi_host_circuit_state) <=>
    mstate.regs = cstate.regs /\
    spi_host_notif_rel mstate.buffered_notif cstate.reg2hw /\
    spi_host_core_state_rel mstate cstate
End

Theorem spi_host_state_rel_fnums:
  spi_host_state_rel (st with fnums := fnums) = spi_host_state_rel st
Proof
  irule EQ_EXT
  >> simp [spi_host_state_rel_def, spi_host_notif_rel_def, spi_host_core_state_rel_def, spi_host_hwext_read_rel_def]
QED

val _ = export_theory ();
