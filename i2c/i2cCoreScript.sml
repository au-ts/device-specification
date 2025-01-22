open HolKernel Parse boolLib bossLib;
open i2cRegsTheory;

val _ = new_theory("i2cCore");

Datatype:
  i2c_state = <|
    (* An infinite stream of non-deterministic bits used to determine what in the
    * hardware's state has changed since the last shared memory access.
    *
    * Having a version of this for each peripheral is a bit silly, but should allow
    * proving theorems about each of them independently. *)
    fbits : num -> bool;
    regs: i2c_regs;
  |>
End

(* Stubs *)
Definition i2c_get_status_fmtfull_def:
  i2c_get_status_fmtfull (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_rxfull_def:
  i2c_get_status_rxfull (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_fmtempty_def:
  i2c_get_status_fmtempty (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_hostidle_def:
  i2c_get_status_hostidle (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_targetidle_def:
  i2c_get_status_targetidle (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_rxempty_def:
  i2c_get_status_rxempty (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_txfull_def:
  i2c_get_status_txfull (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_acqfull_def:
  i2c_get_status_acqfull (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_txempty_def:
  i2c_get_status_txempty (st: i2c_state) = 0w : word1
End

Definition i2c_get_status_acqempty_def:
  i2c_get_status_acqempty (st: i2c_state) = 0w : word1
End

Definition i2c_get_rdata_rdata_def:
  i2c_get_rdata_rdata (st: i2c_state) = 0w : word8
End

Definition i2c_get_fifo_status_fmtlvl_def:
  i2c_get_fifo_status_fmtlvl (st: i2c_state) = 0w : word7
End

Definition i2c_get_fifo_status_txlvl_def:
  i2c_get_fifo_status_txlvl (st: i2c_state) = 0w : word7
End

Definition i2c_get_fifo_status_rxlvl_def:
  i2c_get_fifo_status_rxlvl (st: i2c_state) = 0w : word7
End

Definition i2c_get_fifo_status_acqlvl_def:
  i2c_get_fifo_status_acqlvl (st: i2c_state) = 0w : word7
End

Definition i2c_get_val_scl_rx_def:
  i2c_get_val_scl_rx (st: i2c_state) = 0w : word16
End

Definition i2c_get_val_sda_rx_def:
  i2c_get_val_sda_rx (st: i2c_state) = 0w : word16
End

Definition i2c_get_acqdata_abyte_def:
  i2c_get_acqdata_abyte (st: i2c_state) = 0w : word8
End

Definition i2c_get_acqdata_signal_def:
  i2c_get_acqdata_signal (st: i2c_state) = 0w : word2
End


Definition i2c_rdata_read_def:
  i2c_rdata_read (st: i2c_state) = st
End

Definition i2c_acqdata_read_def:
  i2c_acqdata_read (st: i2c_state) = st
End


Definition i2c_intr_test_written_def:
  i2c_intr_test_written (st: i2c_state) = st
End

Definition i2c_alert_test_written_def:
  i2c_alert_test_written (st: i2c_state) = st
End

Definition i2c_fdata_written_def:
  i2c_fdata_written (st: i2c_state) = st
End

Definition i2c_fifo_ctrl_written_def:
  i2c_fifo_ctrl_written (st: i2c_state) = st
End

Definition i2c_txdata_written_def:
  i2c_txdata_written (st: i2c_state) = st
End


(* Simulates an unknown amount of time passing, using `st.fbits` both to
 * determine the amount of time elapsed and what external events or
 * non-deterministic behaviour (i.e., behaviour we didn't bother modelling)
 * happened during that time. *)
Definition apply_fbits_def:
  apply_fbits (st: i2c_state) = st
End

val _ = export_theory();
