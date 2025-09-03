open HolKernel Parse boolLib bossLib;
open spi_hostCoreTheory spi_hostRegsTheory spi_hostRegsCommTheory;

val _ = new_theory "spi_hostCircuitState";

Datatype:
  spi_host_circuit_ext_state = <|
    (* 40-bit (DefaultCfg.AddrWidth) addr + 32-bit data + 4-bit strobe + 2 bits of write/valid *)
    reg_req_i: 78 word;

    cio_sd_i: 4 word;
  |>
End

Datatype:
  spi_host_circuit_state = <|
    (* 32-bit data + 2 bits of error/ready *)
    reg_rsp_o: 34 word;

    cio_sck_o: bool;
    cio_sck_en_o: bool;
    cio_csb_o: 1 word; (*We may want to expand these for additional CSBs *)
    cio_csb_en_o: 1 word;

    cio_sd_o: 4 word; (*We are only using 2 bits but hardware as 4, to support Quad SPI *)
    cio_sd_en_o: 4 word;

    intr_error_o: bool;
    intr_spi_event_o: bool;


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
    win_buses: spi_host_win_buses;

    (* The decoded fields of `reg_req_i`. *)
    addr: word6;
    write: bool;
    wdata: word32;
    wstrb: word4;
    valid: bool;
    (* `reg_rsp_o.error`, if it's being determined by us and not by a window. *)
    error: bool;
  |>
End

Definition spi_host_core_state_rel_def:
  (* mstate = model state, cstate = circuit state *)
  spi_host_core_state_rel (mstate: spi_host_state) (cstate: spi_host_circuit_state) <=>
    spi_host_hwext_read_rel mstate cstate.hw2reg /\
    spi_host_win_read_rel mstate cstate.win_buses /\
    (* We shouldn't really be assuming this: it's true for I2C and SPI, but in
     * general it should be perfectly fine for an access to take more than 1 cycle
     * to complete.
     *
     * Right now, though, the structure of our model assumes that an access will
     * never take more than one cycle, and I don't want to deal with fixing that
     * just yet; besides, much of the work of fixing this would go towards Cheshire-
     * specific code, when I don't think it's likely that we're going to find a
     * Cheshire peripheral which doesn't respond immediately. *)
    spi_host_win_ready cstate.win_buses
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
  >> simp [spi_host_state_rel_def, spi_host_notif_rel_def, spi_host_core_state_rel_def, spi_host_hwext_read_rel_def, spi_host_win_read_rel_def]
  >> simp [spi_host_rxdata_read_def, spi_host_txdata_read_def]
QED

val _ = export_theory ();
