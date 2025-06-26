open HolKernel Parse boolLib bossLib;
open translatorLib verilogPrintLib;
open spi_hostRegsCircuitLib;
open spi_hostCircuitTheory;

val _ = new_theory "spi_hostCircuitCompile";

local
  val outputs = [
    "reg_rsp_o",

    "cio_scl_o",
    "cio_scl_en_o",
    "cio_sda_o",
    "cio_sda_en_o",

    "intr_fmt_threshold_o",
    "intr_rx_threshold_o",
    "intr_fmt_overflow_o",
    "intr_rx_overflow_o",
    "intr_nak_o",
    "intr_scl_interference_o",
    "intr_sda_interference_o",
    "intr_stretch_timeout_o",
    "intr_sda_unstable_o",
    "intr_cmd_complete_o",
    "intr_tx_stretch_o",
    "intr_tx_overflow_o",
    "intr_acq_full_o",
    "intr_unexp_stop_o",
    "intr_host_timeout_o"
  ];
  val comms = spi_host_reg_comms @ [];
in
  val tstate = init_translator spi_host_circuit_def [] comms;
  val trans_thm = module2hardware tstate spi_host_circuit_def [] outputs comms;
end

val verilogstr =
  definition "spi_host_circuit_v_def"
  |> REWRITE_RULE [definition "spi_host_circuit_v_seqs_def", definition "spi_host_circuit_v_combs_def", definition "spi_host_circuit_v_decls_def"]
  |> concl
  |> rhs
  |> verilog_print "spi_host_circuit" "clk_i" (SOME "rst_ni");

val f = TextIO.openOut "spi_host_circuit.sv";
val _ = output (f, verilogstr);

val _ = export_theory ();
