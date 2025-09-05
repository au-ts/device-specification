open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorLib;
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

Theorem i2c_reg_top_comb_1_trans = SIMP_RULE (pure_ss ++ ARITH_ss) [reg_req_decode_def, reg_req_accfupds, combinTheory.K_THM, dimindex_7, dimindex_48] i2c_reg_top_comb_1_def;

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

val _ = export_theory ();
