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

(* Performs either a device memory read, write, or no-op from a Cheshire
 * peripheral model. *)
Definition cheshire_req_def:
  cheshire_req
    (read_fn: 'ffi -> num -> num -> ffi_outcome + 'notif option # word32)
    (write_fn: 'ffi -> num -> num -> word32 -> ffi_outcome + ('ffi -> 'ffi) # 'notif option)
    (st: 'ffi) (valid: bool) (write: bool) (nb: num) (offset: num) (wdata: word32) =
  if ~valid then
    INR (I, NONE, NONE)
  else if write then
    SUM_MAP I (\(st_upd, notif). (st_upd, notif, NONE)) (write_fn st nb offset wdata)
  else
    SUM_MAP I (\(notif, rdata). (I, notif, SOME rdata)) (read_fn st nb offset)
End

Theorem cheshire_req_INR_cases:
  cheshire_req read_fn write_fn st valid write nb offset wdata = INR (st_upd, notif, rdata) ==>
  (~valid /\ st_upd = I /\ notif = NONE /\ rdata = NONE) \/
  (valid /\ ~write /\ st_upd = I /\ (?value. rdata = SOME value /\ read_fn st nb offset = INR (notif, value))) \/
  (valid /\ write /\ rdata = NONE /\ write_fn st nb offset wdata = INR (st_upd, notif))
Proof
  Cases_on `valid`
  >- (Cases_on `write`
      >- (Cases_on `write_fn st nb offset wdata`
          >- simp [cheshire_req_def]
          >- (Cases_on `y` >> simp [cheshire_req_def]))
      >- (Cases_on `read_fn st nb offset`
          >- simp [cheshire_req_def]
          >- (Cases_on `y` >> simp [cheshire_req_def])))
  >- simp [cheshire_req_def]
QED

Theorem cheshire_req_INR_st_upd_cases:
  cheshire_req read_fn write_fn st valid write nb offset wdata = INR (st_upd, notif, rdata) ==>
  (~(valid /\ write) /\ st_upd = I) \/
  (valid /\ write /\ write_fn st nb offset wdata = INR (st_upd, notif))
Proof
  rpt strip_tac
  >> dxrule cheshire_req_INR_cases
  >> rpt strip_tac
  >> simp []
QED

val _ = export_theory ();
