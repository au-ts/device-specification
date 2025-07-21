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
    reg_req_win_rxdata: 48 reg_req;
    reg_req_win_txdata: 48 reg_req;
    reg_rsp_win_rxdata: reg_rsp;
    reg_rsp_win_txdata: reg_rsp;

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
