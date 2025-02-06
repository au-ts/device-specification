open HolKernel Parse boolLib bossLib;
open sharedMemoryOracleTheory;

val _ = new_theory "cheshireOracle";

(* Simulates an unknown amount of time passing, using `fnums` to determine the
 * amount of time elapsed. *)
Definition cheshire_wait_def:
  cheshire_wait eat_fnum tick st =
  let
    (st', ticks) = eat_fnum st
  in
    FUNPOW (tick NONE) ticks st'
End

Definition cheshire_oracle_read_def:
  cheshire_oracle_read
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> 'ffi)
    (read: 'ffi -> num -> num -> ffi_outcome + 'notif option # word32)
    (st: 'ffi) (nb: num) (addr: num) =
  let
    st' = cheshire_wait eat_fnum tick st;
  in
    if nb > 4 then
      INL FFI_failed
    else
      case read st' nb addr of
        INL outcome => INL outcome
      | INR (notif, value) => INR (tick notif st', w2n value)
End

Definition cheshire_oracle_write_def:
  cheshire_oracle_write
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> 'ffi)
    (write: 'ffi -> num -> num -> word32 -> ffi_outcome + ('ffi -> 'ffi) # 'notif option)
    (st: 'ffi) (nb: num) (addr: num) (value: num) =
  let
    st' = cheshire_wait eat_fnum tick st;
  in
    if nb > 4 then
      INL FFI_failed
    else
      case write st' nb addr (n2w value) of
        INL outcome => INL outcome
      | INR (st_upd, notif) => INR (st_upd (tick notif st'))
End

Definition cheshire_oracle_def:
  cheshire_oracle (:'a)
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> 'ffi)
    (read: 'ffi -> num -> num -> ffi_outcome + 'notif option # word32)
    (write: 'ffi -> num -> num -> word32 -> ffi_outcome + ('ffi -> 'ffi) # 'notif option) =
  sh_mem_oracle (:'a)
    (cheshire_oracle_read eat_fnum tick read)
    (cheshire_oracle_write eat_fnum tick write)
End

val _ = export_theory ();
