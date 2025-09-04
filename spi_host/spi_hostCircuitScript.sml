open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorLib;
open spi_hostRegsCircuitLib;
open cheshireCircuitTheory spi_hostCircuitStateTheory;

val _ = new_theory "spi_hostCircuit";

Definition spi_host_reg_top_comb_1_def:
  spi_host_reg_top_comb_1 (fext: spi_host_circuit_ext_state) (s: spi_host_circuit_state) (s': spi_host_circuit_state) = ^spi_host_reg_top_comb_1_tm
End

Definition spi_host_reg_top_comb_2_def:
  spi_host_reg_top_comb_2 (fext: spi_host_circuit_ext_state) (s: spi_host_circuit_state) (s': spi_host_circuit_state) = ^spi_host_reg_top_comb_2_tm
End

Definition spi_host_reg_top_ff_def:
  spi_host_reg_top_ff (fext: spi_host_circuit_ext_state) (s: spi_host_circuit_state) (s': spi_host_circuit_state) = ^spi_host_reg_top_ff_tm
End

Theorem spi_host_reg_top_comb_1_trans = SIMP_RULE (pure_ss ++ ARITH_ss) [reg_req_decode_def, reg_req_accfupds, combinTheory.K_THM, dimindex_6, dimindex_48, WORD_EXTRACT_ZERO2, word_bit_0] spi_host_reg_top_comb_1_def;

val init_tm = add_x_inits ``
  <|
    regs := ^spi_host_regs_init_tm;
    reg2hw := ^spi_host_reg2hw_init_tm;
    (* TODO: these should be 'x too, but add_x_inits doesn't like reg_req *)
    win_buses := <|
      req := <|
        rxdata := <| addr := 0w; |>;
        txdata := <| addr := 0w; |>;
      |>
    |>
  |>
``;

Definition spi_host_circuit_init_def:
  spi_host_circuit_init fbits = ^init_tm
End

Definition spi_host_circuit_def:
  spi_host_circuit = mk_module (procs [spi_host_reg_top_ff]) (procs [spi_host_reg_top_comb_1; spi_host_reg_top_comb_2]) spi_host_circuit_init
End

val _ = export_theory ();
