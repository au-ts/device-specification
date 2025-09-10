open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorLib;
open shallowFlattenLib spi_hostRegsCircuitLib;
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

Theorem COND_ARG1:
  (if c then f g x else f h x) = f (if c then g else h) x
Proof
  simp [COND_RAND, COND_RATOR]
QED

Theorem COND_ARG1_K:
  (if c then f (K a) x else f (K b) x) = f (K (if c then a else b)) x
Proof
  simp [COND_ARG1, GSYM COND_RAND, GSYM COND_RATOR]
QED

Triviality COND_reg_req_decode:
  (if c then f (reg_req_decode x) else f (reg_req_decode y)) = f (reg_req_decode (if c then x else y))
Proof
  simp [COND_RAND]
QED

Theorem spi_host_reg_top_comb_1_flat = spi_host_reg_top_comb_1_def
  |> CONV_RULE (DEPTH_CONV (fn tm => if is_cond tm then SCONV [SF boolSimps.LET_ss] tm else ALL_CONV tm))
  |> CONV_RULE COND_RECORD_CONV
  |> SRULE [COND_reg_req_decode]
  |> SRULE [Ntimes LET_THM 2, SRULE [] (GSYM spi_host_req_error_alt)]
  |> SRULE [WORD_LO, WORD_LS, GSYM spi_host_win_addr_def, GSYM COND_reg_req_decode, Q.ISPEC `0w: 86 word` reg_req_decode_def]
  |> CONV_RULE (DEPTH_CONV (fn tm => if is_comb tm andalso same_const (fst (dest_comb tm)) ``spi_host_req_error`` andalso is_record (snd (dest_comb tm)) then SCONV [spi_host_req_error_def] tm else ALL_CONV tm))
  |> SRULE [SF boolSimps.LET_ss];

Theorem spi_host_reg_top_comb_2_flat = spi_host_reg_top_comb_2_def
  |> SRULE [SF boolSimps.LET_ss, COND_ARG1_K]
  |> SRULE [Q.ISPEC `bit_field_insert 33 2` (GSYM COND_2RAND), Q.ISPEC `$:+ n` (GSYM COND_2RAND)];

Theorem spi_host_reg_top_ff_flat = spi_host_reg_top_ff_def
  |> SRULE [COND_ARG1_K]
  |> SRULE [SF boolSimps.LET_ss];

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
