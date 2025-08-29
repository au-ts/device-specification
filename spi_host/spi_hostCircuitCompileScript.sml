open HolKernel Parse boolLib bossLib;
open translatorLib verilogPrintLib;
open spi_hostRegsCircuitLib;
open spi_hostCircuitTheory;

val _ = new_theory "spi_hostCircuitCompile";

local
  val outputs = [
    "reg_rsp_o",

    "cio_csk_o",
    "cio_csk_en_o",
    "cio_csb_o",
    "cio_csb_en_o",
    "cio_sd_o",
    "cio_sd_en_o",

    "intr_error_o",
    "int_spi_event_o"
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
