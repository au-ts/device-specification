open HolKernel Parse boolLib bossLib;
open translatorLib verilogPrintLib;
open i2cRegsCircuitLib;
open i2cCircuitTheory;

val _ = new_theory "i2cCircuitCompile";

Theorem i2c_circuit_alt_def:
i2c_circuit =
     mk_module
       (procs
        ([fmt_fifo_rptr_ff; fmt_fifo_regfile_ff; fmt_fifo_wptr_ff;
          i2c_core_tx_fifo_rptr_ff; i2c_core_tx_fifo_regfile; i2c_core_tx_fifo_wptr_ff;
          i2c_core_acq_fifo_rptr_ff; i2c_core_acq_fifo_regfile; i2c_core_acq_fifo_wptr_ff;
          i2c_core_rx_fifo_rptr_ff; i2c_core_rx_fifo_regfile; i2c_core_rx_fifo_wptr_ff;
          i2c_core_fmt_threshold_q_ff; i2c_core_rx_threshold_q_ff;
          i2c_core_sda_rise_cnt_ff; i2c_core_intr_fmt_threshold_o_ff;
          i2c_core_intr_rx_threshold_o_ff; i2c_core_intr_fmt_overflow_o_ff;
          i2c_core_intr_rx_overflow_o_ff; i2c_core_intr_nak_o_ff;
          i2c_core_intr_scl_interference_o_ff; i2c_core_intr_sda_interference_o_ff;
          i2c_core_intr_stretch_timeout_o_ff; i2c_core_intr_sda_unstable_o_ff;
          i2c_core_intr_cmd_complete_o_ff; i2c_core_test_tx_stretch_ff;
          i2c_core_intr_tx_stretch_o_ff; i2c_core_intr_tx_overflow_o_ff;
          i2c_core_test_acq_full_ff; i2c_core_intr_acq_full_o_ff;
          i2c_core_intr_unexp_stop_o_ff; i2c_core_intr_host_timeout_o_ff;
          i2c_core_sync_ff; i2c_core_scl_q_ff; i2c_core_sda_q_ff; i2c_core_ff;
          i2c_core_counter_ff; i2c_core_stretch_idle_cnt_ff; bit_index_ff;
          i2c_core_bit_idx_ff; pend_restart_ff; trans_started_ff; byte_index_ff;
          read_byte_ff; i2c_core_input_byte_ff; scl_rx_val_ff; sda_rx_val_ff; scl_i_q_ff;
          sda_i_q_ff; i2c_core_under_rst_ff; i2c_core_rw_bit_ff; i2c_core_host_ack_ff; i2c_reg_top_ff]))
       (procs
        ([i2c_reg_top_comb_1;
          i2c_core_target_loopback_comb; i2c_core_start_det_comb; i2c_core_stop_det_comb;
          i2c_core_address_match_comb; i2c_core_target_idle_comb; i2c_core_host_idle_comb;
          fmt_fifo_reset; fmt_fifo_rdata; fmt_fifo_rready; fmt_fifo_empty;
          fmt_fifo_incr_rptr; fmt_fifo_counter_rptr_wrap; fmt_fifo_counter_rptr_wrap_cnt;
          fmt_fifo_wvalid; fmt_fifo_full; fmt_fifo_wready; fmt_fifo_incr_wptr;
          fmt_fifo_wdata; fmt_fifo_counter_wptr_wrap; fmt_fifo_counter_wptr_wrap_cnt;
          i2c_core_delay_comb; i2c_core_curr_delay_comb; i2c_core_load_tcount_comb;
          i2c_core_log_start_comb; i2c_core_log_stop_comb; fmt_fifo_rvalid;
          fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after; fmt_fifo_flag_read_bytes;
          fmt_fifo_flag_read_continue; fmt_fifo_flag_nak_ok; i2c_core_tx_fifo_rdata_comb;
          i2c_core_tx_fifo_empty_comb; i2c_core_tx_fifo_rvalid_comb;
          i2c_core_tx_fifo_full_comb; i2c_core_tx_fifo_wready_comb;
          i2c_core_tx_fifo_depth_comb; i2c_core_acq_fifo_rdata_comb;
          i2c_core_acq_fifo_empty_comb; i2c_core_acq_fifo_rvalid_comb;
          i2c_core_acq_fifo_full_comb; i2c_core_acq_fifo_wready_comb;
          i2c_core_acq_fifo_depth_comb; i2c_core_tx_fifo_reset_comb;
          i2c_core_tx_fifo_rready_comb; i2c_core_tx_fifo_wvalid_comb;
          i2c_core_tx_fifo_wdata_comb; i2c_core_tx_fifo_incr_rptr_comb;
          i2c_core_tx_fifo_counter_rptr_wrap_comb;
          i2c_core_tx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_tx_fifo_incr_wptr_comb;
          i2c_core_tx_fifo_counter_wptr_wrap_comb;
          i2c_core_tx_fifo_counter_wptr_wrap_cnt_comb; i2c_core_acq_fifo_reset_comb;
          i2c_core_acq_fifo_rready_comb; i2c_core_acq_fifo_wvalid_comb;
          i2c_core_acq_fifo_wdata_comb; i2c_core_acq_fifo_incr_rptr_comb;
          i2c_core_acq_fifo_counter_rptr_wrap_comb;
          i2c_core_acq_fifo_counter_rptr_wrap_cnt_comb; i2c_core_acq_fifo_incr_wptr_comb;
          i2c_core_acq_fifo_counter_wptr_wrap_comb;
          i2c_core_acq_fifo_counter_wptr_wrap_cnt_comb; i2c_core_stretch_tx_comb;
          fmt_byte; req_restart; bit_clr; bit_decr; i2c_core_stretch_en_comb;
          i2c_core_scl_d_comb; i2c_core_sda_d_comb; i2c_core_scl_o_comb;
          i2c_core_sda_o_comb; i2c_core_cio_scl_o_comb; i2c_core_cio_sda_o_comb;
          i2c_core_cio_scl_en_o_comb; i2c_core_cio_sda_en_o_comb;
          i2c_core_next_scl_rx_val_comb; i2c_core_next_counter; i2c_core_byte_clr_comb;
          i2c_core_byte_decr_comb; i2c_core_byte_num_comb; i2c_core_next_byte_index_comb;
          fifo_depth; counter_gt_one_comb; i2c_core_next_state;
          i2c_core_read_byte_clr_comb; i2c_core_input_byte_clr_comb;
          i2c_core_shift_data_en_comb; i2c_core_next_sda_rx_val_comb;
          i2c_core_next_read_byte_comb; i2c_core_rx_fifo_reset_comb;
          i2c_core_rx_fifo_rdata_comb; i2c_core_rx_fifo_rready_comb;
          i2c_core_rx_fifo_empty_comb; i2c_core_rx_fifo_rvalid_comb;
          i2c_core_rx_fifo_incr_rptr_comb; i2c_core_rx_fifo_counter_rptr_wrap_comb;
          i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb; i2c_core_rx_fifo_wvalid_comb;
          i2c_core_rx_fifo_wdata_comb; i2c_core_rx_fifo_full_comb;
          i2c_core_rx_fifo_wready_comb; i2c_core_rx_fifo_depth_comb;
          i2c_core_rx_fifo_incr_wptr_comb; i2c_core_rx_fifo_counter_wptr_wrap_comb;
          i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb; i2c_core_fmt_threshold_d_comb;
          i2c_core_rx_threshold_d_comb; i2c_core_en_sda_interf_det_comb;
          i2c_core_expect_stop_comb; i2c_core_event_fmt_threshold_comb;
          i2c_core_event_rx_threshold_comb; i2c_core_event_fmt_overflow_comb;
          i2c_core_event_rx_overflow_comb; i2c_core_event_nak_comb;
          i2c_core_event_scl_interference_comb; i2c_core_event_sda_interference_comb;
          i2c_core_event_stretch_timeout_comb; i2c_core_event_sda_unstable_comb;
          i2c_core_event_cmd_complete_comb; i2c_core_event_tx_stretch_comb;
          i2c_core_event_tx_overflow_comb; i2c_core_event_acq_full_comb;
          i2c_core_event_unexp_stop_comb; i2c_core_event_host_timeout_comb;
          i2c_core_hw2reg_intr_state_fmt_threshold_de_comb;
          i2c_core_hw2reg_intr_state_fmt_threshold_d_comb;
          i2c_core_hw2reg_intr_state_rx_threshold_de_comb;
          i2c_core_hw2reg_intr_state_rx_threshold_d_comb;
          i2c_core_hw2reg_intr_state_fmt_overflow_de_comb;
          i2c_core_hw2reg_intr_state_fmt_overflow_d_comb;
          i2c_core_hw2reg_intr_state_rx_overflow_de_comb;
          i2c_core_hw2reg_intr_state_rx_overflow_d_comb;
          i2c_core_hw2reg_intr_state_nak_de_comb; i2c_core_hw2reg_intr_state_nak_d_comb;
          i2c_core_hw2reg_intr_state_scl_interference_de_comb;
          i2c_core_hw2reg_intr_state_scl_interference_d_comb;
          i2c_core_hw2reg_intr_state_sda_interference_de_comb;
          i2c_core_hw2reg_intr_state_sda_interference_d_comb;
          i2c_core_hw2reg_intr_state_stretch_timeout_de_comb;
          i2c_core_hw2reg_intr_state_stretch_timeout_d_comb;
          i2c_core_hw2reg_intr_state_sda_unstable_de_comb;
          i2c_core_hw2reg_intr_state_sda_unstable_d_comb;
          i2c_core_hw2reg_intr_state_cmd_complete_de_comb;
          i2c_core_hw2reg_intr_state_cmd_complete_d_comb;
          i2c_core_hw2reg_intr_state_tx_stretch_de_comb;
          i2c_core_hw2reg_intr_state_tx_stretch_d_comb;
          i2c_core_hw2reg_intr_state_tx_overflow_de_comb;
          i2c_core_hw2reg_intr_state_tx_overflow_d_comb;
          i2c_core_hw2reg_intr_state_acq_full_de_comb;
          i2c_core_hw2reg_intr_state_acq_full_d_comb;
          i2c_core_hw2reg_intr_state_unexp_stop_de_comb;
          i2c_core_hw2reg_intr_state_unexp_stop_d_comb;
          i2c_core_hw2reg_intr_state_host_timeout_de_comb;
          i2c_core_hw2reg_intr_state_host_timeout_d_comb; i2c_core_next_stretch_idle_cnt;
          next_pend_restart_comb; next_trans_started_comb; next_bit_index_comb;
          i2c_core_status_fmtfull_d_comb; i2c_core_status_rxfull_d_comb;
          i2c_core_status_fmtempty_d_comb; i2c_core_status_hostidle_d_comb;
          i2c_core_status_targetidle_d_comb; i2c_core_status_rxempty_d_comb;
          i2c_core_rdata_rdata_d_comb; i2c_core_fifo_status_fmtlvl_d_comb;
          i2c_core_fifo_status_rxlvl_d_comb; i2c_core_val_scl_rx_d_comb;
          i2c_core_val_sda_rx_d_comb; i2c_core_status_txfull_d_comb;
          i2c_core_status_acqfull_d_comb; i2c_core_status_txempty_d_comb;
          i2c_core_status_acqempty_d_comb; i2c_core_fifo_status_txlvl_d_comb;
          i2c_core_fifo_status_acqlvl_d_comb; i2c_core_acqdata_abyte_d_comb;
          i2c_core_acqdata_signal_d_comb;
          i2c_reg_top_comb_2]))
       i2c_circuit_init
Proof
  rw [i2c_circuit_def, i2c_core_ffs1_def, i2c_core_combs_def]
QED
    
    
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
  val comms = i2c_reg_comms @ ["fsm_state", "counter", "stretch_idle_cnt", "under_rst", "fmt_fifo_rptr", "fmt_fifo_wptr", "fmt_fifo_regfile",
                             "rx_fifo_regfile", "rx_fifo_rptr", "rx_fifo_wptr", "tx_fifo_regfile", "tx_fifo_rptr", "tx_fifo_wptr",
                             "acq_fifo_regfile", "acq_fifo_rptr", "acq_fifo_wptr", "bit_index", "pend_restart", "byte_index", "trans_started",
                             "read_byte", "sda_rx_val", "scl_rx_val", "scl_buf", "sda_buf", "scl_sync", "sda_sync", "input_byte", "bit_idx",
                             "rw_bit", "host_ack", "scl_i_q", "sda_i_q", "fmt_threshold_q", "rx_threshold_q", "sda_rise_cnt", "scl_q",
                             "sda_q", "test_tx_stretch", "test_acq_full"]

in
  val tstate = init_translator i2c_circuit_alt_def [] comms;
  val trans_thm = module2hardware tstate i2c_circuit_alt_def [] outputs comms;
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
