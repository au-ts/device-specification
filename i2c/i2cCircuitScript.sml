open HolKernel Parse boolLib bossLib;
open translatorLib verilogPrintLib;
open i2cRegsCircuitLib;
open cheshireCircuitTheory i2cCircuitStateTheory;

val _ = new_theory "i2cCircuit";

Definition i2c_reg_top_comb_1_def:
  i2c_reg_top_comb_1 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_1_tm
End

Definition i2c_reg_top_comb_2_def:
  i2c_reg_top_comb_2 (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_comb_2_tm
End

Definition i2c_reg_top_ff_def:
  i2c_reg_top_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^i2c_reg_top_ff_tm
End

Theorem i2c_reg_top_comb_1_trans = SIMP_RULE (pure_ss ++ ARITH_ss) [reg_req_decode_def, reg_req_accfupds, combinTheory.K_THM, dimindex_7] i2c_reg_top_comb_1_def;

val init_tm = add_x_inits ``
  <|
    regs := ^i2c_regs_init_tm;
    reg2hw := ^i2c_reg2hw_init_tm;
  |>
``;

Definition i2c_circuit_init_def:
  i2c_circuit_init fbits = ^init_tm
End

Definition i2c_circuit_def:
  i2c_circuit = mk_module (procs [i2c_reg_top_ff]) (procs [i2c_reg_top_comb_1; i2c_reg_top_comb_2]) i2c_circuit_init
End

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
  val comms = i2c_reg_comms @ [];
in
  val tstate = init_translator i2c_circuit_def [] comms;
  val trans_thm = module2hardware tstate i2c_circuit_def [] outputs comms;
end

val verilogstr =
  definition "i2c_circuit_v_def"
  |> REWRITE_RULE [definition "i2c_circuit_v_seqs_def", definition "i2c_circuit_v_combs_def", definition "i2c_circuit_v_decls_def"]
  |> concl
  |> rhs
  |> verilog_print "i2c_circuit" "clk_i" (SOME "rst_ni");

val f = TextIO.openOut "i2c_circuit.sv";
val _ = output (f, verilogstr);

val _ = export_theory ();
