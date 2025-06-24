open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorLib;
open i2cRegsCircuitLib i2cCoreCircuitLib;
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

Theorem i2c_reg_top_comb_1_trans = SIMP_RULE (pure_ss ++ ARITH_ss) [reg_req_decode_def, reg_req_accfupds, combinTheory.K_THM, dimindex_7, dimindex_48, WORD_EXTRACT_ZERO2, word_bit_0] i2c_reg_top_comb_1_def;

(* Section --- I2C Core *)

(* Direct translation from @{file "i2cCoreCiruitLib.sml"} *)
Definition fmt_fifo_reset_def:
  fmt_fifo_reset (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_reset_tm
End

Definition fmt_fifo_rdata_def:
  fmt_fifo_rdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_rdata_tm
End

Definition fmt_fifo_rready_def:
  fmt_fifo_rready (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_rready_tm
End

Definition fmt_fifo_empty_def:
  fmt_fifo_empty (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_empty_tm
End

Definition fmt_fifo_incr_rptr_def:
  fmt_fifo_incr_rptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_incr_rptr_tm
End

Definition fmt_fifo_counter_rptr_wrap_def:
  fmt_fifo_counter_rptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_counter_rptr_wrap_tm
End

Definition fmt_fifo_counter_rptr_wrap_cnt_def:
  fmt_fifo_counter_rptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_counter_rptr_wrap_cnt_tm
End

Definition fmt_fifo_rptr_ff_def:
  fmt_fifo_rptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_rptr_tm
End

Definition fmt_fifo_wvalid_def:
  fmt_fifo_wvalid (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_wvalid_tm
End

Definition fmt_fifo_full_def:
  fmt_fifo_full (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_full_tm
End

Definition fmt_fifo_incr_wptr_def:
  fmt_fifo_incr_wptr (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_incr_wptr_tm
End

Definition fmt_fifo_wdata_def:
  fmt_fifo_wdata (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_wdata_tm
End

Definition fmt_fifo_regfile_ff_def:
  fmt_fifo_regfile_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_regfile_tm
End

Definition fmt_fifo_counter_wptr_wrap_def:
  fmt_fifo_counter_wptr_wrap (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_counter_wptr_wrap_tm
End

Definition fmt_fifo_counter_wptr_wrap_cnt_def:
  fmt_fifo_counter_wptr_wrap_cnt (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_counter_wptr_wrap_cnt_tm
End

Definition fmt_fifo_wptr_ff_def:
  fmt_fifo_wptr_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_wptr_tm
End

Definition i2c_core_delay_comb_def:
  i2c_core_delay_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^delay_tm
End

Definition i2c_core_curr_delay_comb_def:
  i2c_core_curr_delay_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^curr_delay_tm
End

Definition i2c_core_load_tcount_comb_def:
  i2c_core_load_tcount_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^load_tcount_tm
End

Definition i2c_core_log_start_comb_def:
  i2c_core_log_start_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  ^log_start_tm
End

Definition i2c_core_log_stop_comb_def:
  i2c_core_log_stop_comb (fext : i2c_circuit_ext_state) (s : i2c_circuit_state) (s' : i2c_circuit_state) =
  ^log_stop_tm
End

Definition fmt_fifo_rvalid_def:
  fmt_fifo_rvalid (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_rvalid_tm
End

Definition fmt_fifo_flag_start_before_def:
  fmt_fifo_flag_start_before (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_flag_start_before_tm
End

Definition fmt_fifo_flag_stop_after_def:
  fmt_fifo_flag_stop_after (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_flag_stop_after_tm
End

Definition fmt_fifo_flag_read_bytes_def:
  fmt_fifo_flag_read_bytes (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_fifo_flag_read_bytes_tm
End

Definition fmt_byte_def:
  fmt_byte (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^fmt_byte_tm
End

Definition req_restart_def:
  req_restart (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^req_restart_tm
End

Definition bit_clr_def:
  bit_clr (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^bit_clr_tm
End

Definition bit_decr_def:
  bit_decr (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^bit_decr_tm
End

Definition i2c_core_stretch_en_comb_def:
  i2c_core_stretch_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^stretch_en_tm
End

Definition stretch_en_def:
  stretch_en (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^stretch_en_tm
End

Definition i2c_core_scl_d_comb_def:
  i2c_core_scl_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^scl_d_tm
End

Definition i2c_core_next_scl_rx_val_comb_def:
  i2c_core_next_scl_rx_val_comb (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) = ^next_scl_rx_val_tm
End

Definition i2c_core_next_stretch_idle_cnt_def:
  i2c_core_next_stretch_idle_cnt (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_stretch_idle_cnt_tm
End

Definition i2c_core_next_counter_def:
  i2c_core_next_counter (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_counter_tm
End

Definition i2c_core_byte_clr_comb_def:
  i2c_core_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^byte_clr_tm
End

Definition i2c_core_byte_decr_comb_def:
  i2c_core_byte_decr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^byte_decr_tm
End

Definition i2c_core_byte_num_comb_def:
  i2c_core_byte_num_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^byte_num_tm
End

Definition i2c_core_next_byte_index_comb_def:
  i2c_core_next_byte_index_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_byte_index_tm
End

Definition fifo_depth_def:
  fifo_depth (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  ^fifo_depth_tm
End

Definition counter_gt_one_comb_def:
  counter_gt_one_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  ^counter_gt_one_tm
End

Definition i2c_core_next_state_def:
  i2c_core_next_state (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_state_tm
End

Definition i2c_core_read_byte_clr_comb_def:
  i2c_core_read_byte_clr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^read_byte_clr_tm
End

Definition i2c_core_shift_data_en_comb_def:
  i2c_core_shift_data_en_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^shift_data_en_tm
End

Definition i2c_core_next_sda_rx_val_comb_def:
  i2c_core_next_sda_rx_val_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_sda_rx_val_tm
End

Definition i2c_core_next_read_byte_comb_def:
  i2c_core_next_read_byte_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_read_byte_tm
End

Definition i2c_core_rx_fifo_reset_comb_def:
  i2c_core_rx_fifo_reset_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_reset_tm
End

Definition i2c_core_rx_fifo_rdata_comb_def:
  i2c_core_rx_fifo_rdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_rdata_tm
End

Definition i2c_core_rx_fifo_rready_comb_def:
  i2c_core_rx_fifo_rready_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_rready_tm
End

Definition i2c_core_rx_fifo_empty_comb_def:
  i2c_core_rx_fifo_empty_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_empty_tm
End

Definition i2c_core_rx_fifo_incr_rptr_comb_def:
  i2c_core_rx_fifo_incr_rptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_incr_rptr_tm
End

Definition i2c_core_rx_fifo_counter_rptr_wrap_comb_def:
  i2c_core_rx_fifo_counter_rptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_counter_rptr_wrap_tm
End

Definition i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def:
  i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_counter_rptr_wrap_cnt_tm
End

Definition i2c_core_rx_fifo_rptr_ff_def:
  i2c_core_rx_fifo_rptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_counter_rptr_wrap_cnt_tm
End

Definition i2c_core_rx_fifo_wvalid_comb_def:
  i2c_core_rx_fifo_wvalid_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_wvalid_tm
End

Definition i2c_core_rx_fifo_wdata_comb_def:
  i2c_core_rx_fifo_wdata_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_wdata_tm
End

Definition i2c_core_rx_fifo_full_comb_def:
  i2c_core_rx_fifo_full_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_full_tm
End

Definition i2c_core_rx_fifo_incr_wptr_comb_def:
  i2c_core_rx_fifo_incr_wptr_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_incr_wptr_tm
End

Definition i2c_core_rx_fifo_regfile_def:
  i2c_core_rx_fifo_regfile (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_regfile_tm
End

Definition i2c_core_rx_fifo_counter_wptr_wrap_comb_def:
  i2c_core_rx_fifo_counter_wptr_wrap_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_counter_wptr_wrap_tm
End

Definition i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def:
  i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_counter_wptr_wrap_cnt_tm
End

Definition i2c_core_rx_fifo_wptr_ff_def:
  i2c_core_rx_fifo_wptr_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^rx_fifo_wptr_tm
End

Definition hw2reg_intr_state_nak_de_comb_def:
  hw2reg_intr_state_nak_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^hw2reg_intr_state_nak_de_tm
End

Definition hw2reg_intr_state_nak_d_comb_def:
  hw2reg_intr_state_nak_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^hw2reg_intr_state_nak_d_tm
End

Definition next_intr_nak_comb_def:
  next_intr_nak_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_intr_nak_o_tm
End

Definition hw2reg_intr_state_cmd_complete_de_comb_def:
  hw2reg_intr_state_cmd_complete_de_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^hw2reg_intr_state_cmd_complete_de_tm
End

Definition hw2reg_intr_state_cmd_complete_d_comb_def:
  hw2reg_intr_state_cmd_complete_d_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^hw2reg_intr_state_cmd_complete_d_tm
End

Definition next_intr_cmd_complete_comb_def:
  next_intr_cmd_complete_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^next_intr_cmd_complete_o_tm
End

Definition next_pend_restart_comb_def:
  next_pend_restart_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  ^next_pend_restart_tm
End

Definition next_trans_started_comb_def:
  next_trans_started_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  ^next_trans_started_tm
End

Definition next_bit_index_comb_def:
  next_bit_index_comb (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s':i2c_circuit_state) =
  ^next_bit_index_tm
End

Definition i2c_core_ff_def:
  i2c_core_ff (fext : i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^i2c_core_ff_tm
End

Definition i2c_core_counter_ff_def:
  i2c_core_counter_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^i2c_core_counter_ff_tm
End

Definition i2c_core_stretch_idle_cnt_ff_def:
  i2c_core_stretch_idle_cnt_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^i2c_core_stretch_idle_cnt_ff_tm
End

Definition bit_index_ff_def:
  bit_index_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^bit_index_ff_tm
End

Definition pend_restart_ff_def:
  pend_restart_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^pend_restart_ff_tm
End

Definition byte_index_ff_def:
  byte_index_ff (fext: i2c_circuit_ext_state) (s: i2c_circuit_state) (s': i2c_circuit_state) =
  ^byte_index_ff_tm
End

val init_tm = add_x_inits ``
  <|
    regs := ^i2c_regs_init_tm;
    reg2hw := ^i2c_reg2hw_init_tm;
    fmt_fifo_regfile := K 0w;
    rx_fifo_regfile := K 0w;
  |>
``;

Definition i2c_circuit_init_def:
  i2c_circuit_init fbits = ^init_tm
End

Definition i2c_core_ffs1_def:
  i2c_core_ffs1 = [i2c_core_counter_ff; i2c_core_stretch_idle_cnt_ff; fmt_fifo_rptr_ff;
                   fmt_fifo_regfile_ff; i2c_core_rx_fifo_wptr_ff; fmt_fifo_wptr_ff; bit_index_ff; pend_restart_ff;
                   byte_index_ff; i2c_core_rx_fifo_rptr_ff; i2c_core_rx_fifo_regfile; i2c_core_ff]
End

Definition i2c_core_combs_def:
  i2c_core_combs = [i2c_core_rx_fifo_counter_wptr_wrap_comb; i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb;
                    i2c_core_delay_comb; i2c_core_curr_delay_comb; i2c_core_load_tcount_comb;
                    i2c_core_stretch_en_comb; i2c_core_scl_d_comb; i2c_core_next_stretch_idle_cnt;
                    i2c_core_next_counter; i2c_core_next_state; fmt_fifo_reset; counter_gt_one_comb;
                    fmt_fifo_rdata; fmt_fifo_rready; fmt_fifo_empty;
                    fmt_fifo_counter_rptr_wrap; fmt_fifo_counter_rptr_wrap_cnt;
                    fmt_fifo_wvalid; fmt_fifo_full; fmt_fifo_incr_wptr; fmt_fifo_wdata; fmt_fifo_counter_wptr_wrap;
                    fmt_fifo_counter_wptr_wrap_cnt; i2c_core_log_start_comb; i2c_core_log_stop_comb; fmt_fifo_rvalid;
                    fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after; fmt_fifo_flag_read_bytes; fmt_byte;
                    req_restart; bit_clr; bit_decr; i2c_core_next_scl_rx_val_comb; i2c_core_byte_clr_comb;
                    i2c_core_byte_num_comb; i2c_core_next_byte_index_comb; fifo_depth; i2c_core_read_byte_clr_comb;
                    i2c_core_shift_data_en_comb; i2c_core_next_sda_rx_val_comb; i2c_core_next_read_byte_comb;
                    i2c_core_rx_fifo_reset_comb; i2c_core_rx_fifo_rdata_comb; i2c_core_rx_fifo_rready_comb;
                    i2c_core_rx_fifo_empty_comb; i2c_core_rx_fifo_incr_rptr_comb; i2c_core_rx_fifo_counter_rptr_wrap_comb;
                    i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_rx_fifo_wvalid_comb; i2c_core_rx_fifo_wdata_comb;
                    i2c_core_rx_fifo_full_comb; i2c_core_rx_fifo_incr_wptr_comb;
                    hw2reg_intr_state_nak_de_comb; next_intr_nak_comb;
                    hw2reg_intr_state_cmd_complete_de_comb; hw2reg_intr_state_cmd_complete_d_comb; next_intr_cmd_complete_comb;
                    next_pend_restart_comb; next_trans_started_comb; next_bit_index_comb]
End

Definition i2c_circuit_def:
  i2c_circuit = mk_module
                (procs (i2c_core_ffs1 ++ [i2c_reg_top_ff] ++ []))
                (procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]))
                i2c_circuit_init
End

Theorem ff_asm1:
  flip EVERY i2c_core_ffs1
       (λproc.
          let
            s'' = proc fext s s'
          in
            s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧ s''.reg_rsp_o = s'.reg_rsp_o
            ∧ s''.addr = s'.addr ∧ s''.write = s'.write ∧ s''.wdata = s'.wdata
            ∧ s''.wstrb = s'.wstrb ∧ s''.valid = s'.valid)
Proof
  LET_ELIM_TAC
  >> rw [i2c_core_ffs1_def]
  >> rw [Abbr ‘s''’, i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def,
         fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
         bit_index_ff_def, pend_restart_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
         i2c_core_rx_fifo_regfile_def, i2c_core_ff_def]
QED

Theorem ff_asm2:
  EVERY (λproc. (proc fext s s').hw2reg = s'.hw2reg) i2c_core_ffs1
Proof
  rw [i2c_core_ffs1_def, i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def,
         fmt_fifo_rptr_ff_def, fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
         bit_index_ff_def, pend_restart_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
         i2c_core_rx_fifo_regfile_def, i2c_core_ff_def]
QED

Theorem comb_asm1:
  flip EVERY i2c_core_combs
       (λproc.
          let
            s'' = proc fext s s'
          in
            s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧ s''.reg_rsp_o = s'.reg_rsp_o
            ∧ s''.addr = s'.addr ∧ s''.write = s'.write ∧ s''.wdata = s'.wdata
            ∧ s''.wstrb = s'.wstrb ∧ s''.valid = s'.valid)
Proof
  LET_ELIM_TAC
  >> rw [i2c_core_combs_def]
  >> rw [Abbr ‘s''’, i2c_core_rx_fifo_counter_wptr_wrap_comb_def, i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def,
         i2c_core_delay_comb_def, i2c_core_curr_delay_comb_def, i2c_core_load_tcount_comb_def,
         i2c_core_stretch_en_comb_def, i2c_core_scl_d_comb_def, i2c_core_next_stretch_idle_cnt_def,
         i2c_core_next_counter_def, i2c_core_next_state_def, fmt_fifo_reset_def, counter_gt_one_comb_def,
         fmt_fifo_rdata_def, fmt_fifo_rready_def, fmt_fifo_empty_def,
         fmt_fifo_counter_rptr_wrap_def, fmt_fifo_counter_rptr_wrap_cnt_def,
         fmt_fifo_wvalid_def, fmt_fifo_full_def, fmt_fifo_incr_wptr_def, fmt_fifo_wdata_def, fmt_fifo_counter_wptr_wrap_def,
         fmt_fifo_counter_wptr_wrap_cnt_def, i2c_core_log_start_comb_def, i2c_core_log_stop_comb_def, fmt_fifo_rvalid_def,
         fmt_fifo_flag_start_before_def, fmt_fifo_flag_stop_after_def, fmt_fifo_flag_read_bytes_def, fmt_byte_def,
         req_restart_def, bit_clr_def, bit_decr_def, i2c_core_next_scl_rx_val_comb_def, i2c_core_byte_clr_comb_def,
         i2c_core_byte_num_comb_def, i2c_core_next_byte_index_comb_def, fifo_depth_def, i2c_core_read_byte_clr_comb_def,
         i2c_core_shift_data_en_comb_def, i2c_core_next_sda_rx_val_comb_def, i2c_core_next_read_byte_comb_def,
         i2c_core_rx_fifo_reset_comb_def, i2c_core_rx_fifo_rdata_comb_def, i2c_core_rx_fifo_rready_comb_def,
         i2c_core_rx_fifo_empty_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_comb_def,
         i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def, i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_wdata_comb_def,
         i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_incr_wptr_comb_def,
         hw2reg_intr_state_nak_de_comb_def, next_intr_nak_comb_def,
         hw2reg_intr_state_cmd_complete_de_comb_def, hw2reg_intr_state_cmd_complete_d_comb_def, next_intr_cmd_complete_comb_def,
         next_pend_restart_comb_def, next_trans_started_comb_def, next_bit_index_comb_def]
QED

val _ = export_theory ();
