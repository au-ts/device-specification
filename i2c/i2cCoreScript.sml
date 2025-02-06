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
    regs : i2c_regs;
    (* Although there can only be one regbus transaction per clock cycle, because
     * non-`hwext` transactions only issue notifications on the next clock cycle,
     * whereas `hwext` transactions issue notifications immediately, you can end up
     * with two notifications on the same clock cycle if you have a non-`hwext`
     * transaction immediately followed by a `hwext` transaction. *)
    buffered_notif : i2c_notif option;

    (* Maximum length: 64 *)
    rx_fifo : word8 list;
  |>
End


(* Stubs *)
Definition i2c_get_status_fmtfull_def:
  i2c_get_status_fmtfull (st: i2c_state) = 0w
End

Definition i2c_get_status_rxfull_def:
  i2c_get_status_rxfull (st: i2c_state) = if LENGTH st.rx_fifo >= 64 then 1w else 0w
End

Definition i2c_get_status_fmtempty_def:
  i2c_get_status_fmtempty (st: i2c_state) = 0w
End

Definition i2c_get_status_hostidle_def:
  i2c_get_status_hostidle (st: i2c_state) = 0w
End

Definition i2c_get_status_targetidle_def:
  i2c_get_status_targetidle (st: i2c_state) = 0w
End

Definition i2c_get_status_rxempty_def:
  i2c_get_status_rxempty (st: i2c_state) = if NULL st.rx_fifo then 1w else 0w
End

Definition i2c_get_status_txfull_def:
  i2c_get_status_txfull (st: i2c_state) = 0w
End

Definition i2c_get_status_acqfull_def:
  i2c_get_status_acqfull (st: i2c_state) = 0w
End

Definition i2c_get_status_txempty_def:
  i2c_get_status_txempty (st: i2c_state) = 0w
End

Definition i2c_get_status_acqempty_def:
  i2c_get_status_acqempty (st: i2c_state) = 0w
End

Definition i2c_get_rdata_rdata_def:
  (* `OutputZeroIfEmpty` is set to 1, so we can rely on it always being 0 in that
   * case rather than having to use `fnums`. *)
  i2c_get_rdata_rdata (st: i2c_state) = if NULL st.rx_fifo then 0w else HD st.rx_fifo
End

Definition i2c_get_fifo_status_fmtlvl_def:
  i2c_get_fifo_status_fmtlvl (st: i2c_state) = 0w
End

Definition i2c_get_fifo_status_txlvl_def:
  i2c_get_fifo_status_txlvl (st: i2c_state) = 0w
End

Definition i2c_get_fifo_status_rxlvl_def:
  i2c_get_fifo_status_rxlvl (st: i2c_state) = n2w (LENGTH st.rx_fifo)
End

Definition i2c_get_fifo_status_acqlvl_def:
  i2c_get_fifo_status_acqlvl (st: i2c_state) = 0w
End

Definition i2c_get_val_scl_rx_def:
  i2c_get_val_scl_rx (st: i2c_state) = 0w
End

Definition i2c_get_val_sda_rx_def:
  i2c_get_val_sda_rx (st: i2c_state) = 0w
End

Definition i2c_get_acqdata_abyte_def:
  i2c_get_acqdata_abyte (st: i2c_state) = 0w
End

Definition i2c_get_acqdata_signal_def:
  i2c_get_acqdata_signal (st: i2c_state) = 0w
End


Definition i2c_eat_fnum:
  i2c_eat_fnum st = (st with fnums := st.fnums o SUC, st.fnums 0)
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
      fnums = st.fnums;

      (* `Pass` is set to 0, which means that a value cannot be removed from the FIFO
       * on the same clock cycle that it is inserted, and so this needs to go first so
       * that it can't see any newly-inserted values. *)
      rx_fifo' = if hwext_notif = SOME (Read rdata_read) /\ ~NULL st.rx_fifo then TL st.rx_fifo else st.rx_fifo;
      (* The FIFO can't insert into a spot that was freed in the same clock cycle, so
       * we need to use `st.rx_fifo` rather than `rx_fifo'`. *)
      rx_fifo'' = if fnums 0 <> 0 /\ LENGTH st.rx_fifo < 64 then SNOC (n2w (fnums 1)) rx_fifo' else rx_fifo';
      fnums = \n. fnums (n + 2);
    in
      <|
        fnums := fnums;
        buffered_notif := NONE;
        rx_fifo := rx_fifo'';
      |>
End

val _ = export_theory();
