open HolKernel Parse boolLib bossLib;
open translatorLib verilogPrintLib;
open i2cRegsCircuitLib;
open i2cCircuitTheory;

val _ = new_theory "i2cCircuitCompile";

Theorem i2c_circuit_alt_def:
i2c_circuit =
     mk_module
       (procs
          ([i2c_core_counter_ff; i2c_core_stretch_idle_cnt_ff;
            fmt_fifo_rptr_ff; fmt_fifo_regfile_ff; i2c_core_rx_fifo_wptr_ff;
            fmt_fifo_wptr_ff; bit_index_ff; pend_restart_ff; byte_index_ff;
            i2c_core_rx_fifo_rptr_ff; i2c_core_rx_fifo_regfile; i2c_core_ff;
            i2c_reg_top_ff]))
       (procs
          ([i2c_reg_top_comb_1; i2c_core_rx_fifo_counter_wptr_wrap_comb;
            i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb; i2c_core_delay_comb;
            i2c_core_curr_delay_comb; i2c_core_load_tcount_comb;
            i2c_core_stretch_en_comb; i2c_core_scl_d_comb;
            i2c_core_next_stretch_idle_cnt; i2c_core_next_counter;
            i2c_core_next_state; fmt_fifo_reset; counter_gt_one_comb;
            fmt_fifo_rdata; fmt_fifo_rready; fmt_fifo_empty;
            fmt_fifo_counter_rptr_wrap; fmt_fifo_counter_rptr_wrap_cnt;
            fmt_fifo_wvalid; fmt_fifo_full; fmt_fifo_incr_wptr;
            fmt_fifo_wdata; fmt_fifo_counter_wptr_wrap;
            fmt_fifo_counter_wptr_wrap_cnt; i2c_core_log_start_comb;
            i2c_core_log_stop_comb; fmt_fifo_rvalid;
            fmt_fifo_flag_start_before; fmt_fifo_flag_stop_after;
            fmt_fifo_flag_read_bytes; fmt_byte; req_restart; bit_clr;
            bit_decr; i2c_core_next_scl_rx_val_comb; i2c_core_byte_clr_comb;
            i2c_core_byte_num_comb; i2c_core_next_byte_index_comb;
            fifo_depth; i2c_core_read_byte_clr_comb;
            i2c_core_shift_data_en_comb; i2c_core_next_sda_rx_val_comb;
            i2c_core_next_read_byte_comb; i2c_core_rx_fifo_reset_comb;
            i2c_core_rx_fifo_rdata_comb; i2c_core_rx_fifo_rready_comb;
            i2c_core_rx_fifo_empty_comb; i2c_core_rx_fifo_incr_rptr_comb;
            i2c_core_rx_fifo_counter_rptr_wrap_comb;
            i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb;
            i2c_core_rx_fifo_wvalid_comb; i2c_core_rx_fifo_wdata_comb;
            i2c_core_rx_fifo_full_comb; i2c_core_rx_fifo_incr_wptr_comb;
            hw2reg_intr_state_nak_de_comb; next_intr_nak_comb;
            hw2reg_intr_state_cmd_complete_de_comb;
            hw2reg_intr_state_cmd_complete_d_comb;
            next_intr_cmd_complete_comb; next_pend_restart_comb;
            next_trans_started_comb; next_bit_index_comb;
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
  val comms = i2c_reg_comms @ [];
  val comms = i2c_reg_comms @ ["fsm_state", "counter", "stretch_idle_cnt", "fmt_fifo_rptr", "fmt_fifo_wptr", "fmt_fifo_regfile",
                             "rx_fifo_regfile", "rx_fifo_rptr", "rx_fifo_wptr", "bit_index", "pend_restart", "byte_index", "trans_started",
                             "read_byte", "sda_rx_val", "scl_rx_val"]

in
  val tstate = init_translator i2c_circuit_alt_def [] comms;
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
