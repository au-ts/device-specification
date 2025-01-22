open HolKernel Parse boolLib bossLib;
open i2cRegsTheory;

val _ = new_theory("i2cCore");

Datatype:
  i2c_state = <|
    (* An infinite stream of non-deterministic numbers used to determine what in the
     * hardware's state has changed since the last shared memory access.
     *
     * This is inspired by `CakeML/hardware`'s `fbits`; we use `num`s instead of
     * bits because with bits, it's tricky to define how they're interpreted to
     * produce the number of ticks that pass between each read/write. My initial
     * idea was to interpret each bit as 'should we keep going', and thus end up
     * using the number of leading ones as the number of ticks; however, if `fbits`
     * was all 1s, that would cause `apply_fbits` not to terminate. With `num`s, we
     * can just take the first `num` from the list and use that as the number of
     * ticks.
     *
     * Having a version of this for each peripheral is a bit silly, but should allow
     * proving theorems about each of them independently. *)
    fnums : num -> num;
    regs: i2c_regs;
    (* Although there can only be one regbus transaction per clock cycle, because
     * non-`hwext` transactions only issue notifications on the next clock cycle,
     * whereas `hwext` transactions issue notifications immediately, you can end up
     * with two notifications on the same clock cycle if you have a non-`hwext`
     * transaction immediately followed by a `hwext` transaction. *)
    buffered_notif: i2c_notif option;
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


(* Simulates one clock cycle of the I2C core.
 *
 * Register reads/writes are handled externally, with new values simply being
 * made available in `st`. If the hardware has a `qe`/`re` signal to detect
 * interactions with a register, a notification is provided that that's occured.
 * For regular registers, this occurs on the clock cycle after the I/O actually
 * occurs, but for `hwext` registers it occurs on the same clock cycle. *)
Definition i2c_tick_def:
  i2c_tick (hwext_notif: i2c_hwext_notif option) (st: i2c_state) =
    let
      notif = st.buffered_notif;
      st' = st with buffered_notif := NONE;
    in
      st'
End

(* Simulates an unknown amount of time passing, using `st.fnums` to determine
 * the amount of time elapsed. *)
Definition apply_fbits_def:
  apply_fbits (st: i2c_state) =
    let
      ticks = st.fnums 0;
      st' = st with fnums := st.fnums o SUC;
    in
      FUNPOW (i2c_tick NONE) ticks st'
End

val _ = export_theory();
