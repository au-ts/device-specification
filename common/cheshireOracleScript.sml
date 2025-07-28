open HolKernel Parse boolLib bossLib;
open BasicProvers;
open sumExtraTheory;
open sharedMemoryOracleTheory;

val _ = new_theory "cheshireOracle";

(* Simulates an unknown amount of time passing, using `fnums` to determine the
 * amount of time elapsed. *)
Definition cheshire_wait_def:
  cheshire_wait eat_fnum tick st =
  let
    (st', ticks) = eat_fnum st
  in
    sum_funpowM (tick NONE) ticks st'
End

Definition cheshire_oracle_read_def:
  cheshire_oracle_read
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> ffi_outcome + 'ffi)
    (read: 'ffi -> num -> num -> ffi_outcome + 'notif option # word32)
    (st: 'ffi) (nb: num) (addr: num) =
  do
    sum_check (nb > 4) FFI_failed;
    st <- cheshire_wait eat_fnum tick st;
    (notif, value) <- read st nb addr;
    st <- tick notif st;
    INR (st, w2n value)
  od
End

Definition cheshire_oracle_write_def:
  cheshire_oracle_write
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> ffi_outcome + 'ffi)
    (write: 'ffi -> num -> num -> word32 -> ffi_outcome + ('ffi -> 'ffi) # 'notif option)
    (st: 'ffi) (nb: num) (addr: num) (value: num) =
  do
    sum_check (nb > 4) FFI_failed;
    st <- cheshire_wait eat_fnum tick st;
    (st_upd, notif) <- write st nb addr (n2w value);
    st <- tick notif st;
    INR (st_upd st)
  od
End

Definition cheshire_oracle_def:
  cheshire_oracle (:'a)
    (eat_fnum: 'ffi -> 'ffi # num)
    (tick: 'notif option -> 'ffi -> ffi_outcome + 'ffi)
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
    (st: 'ffi) (req: (num # num # word32 option) option) =
  case req of
    NONE => INR (I, NONE, NONE)
  | SOME (nb, offset, SOME wdata) => SUM_MAP I (\(st_upd, notif). (st_upd, notif, NONE)) (write_fn st nb offset wdata)
  | SOME (nb, offset, NONE) => SUM_MAP I (\(notif, rdata). (I, notif, SOME rdata)) (read_fn st nb offset)
End

Theorem cheshire_req_INR_cases:
  cheshire_req read_fn write_fn st req = INR (st_upd, notif, rdata) ==>
  (req = NONE /\ st_upd = I /\ notif = NONE /\ rdata = NONE) \/
  (?nb offset value. req = SOME (nb, offset, NONE) /\ st_upd = I /\ rdata = SOME value /\ read_fn st nb offset = INR (notif, value)) \/
  (?nb offset wdata. req = SOME (nb, offset, (SOME wdata)) /\ rdata = NONE /\ write_fn st nb offset wdata = INR (st_upd, notif))
Proof
  simp [cheshire_req_def]
  >> rpt TOP_CASE_TAC
  >- (Cases_on `read_fn st q q'`
      >- simp []
      >- (Cases_on `y` >> simp []))
  >- (Cases_on `write_fn st q q' x`
      >- simp []
      >- (Cases_on `y` >> simp []))
QED

Theorem cheshire_req_INR_st_upd_cases:
  cheshire_req read_fn write_fn st req = INR (st_upd, notif, rdata) ==>
  (~(?nb offset wdata. req = SOME (nb, offset, SOME wdata)) /\ st_upd = I) \/
  (?nb offset wdata. req = SOME (nb, offset, SOME wdata) /\ write_fn st nb offset wdata = INR (st_upd, notif))
Proof
  rpt strip_tac
  >> dxrule_then strip_assume_tac cheshire_req_INR_cases
  >> simp []
QED

Definition cheshire_run_def:
  (cheshire_run tick_fn read_fn write_fn st [] = INR (st, [])) /\
  (cheshire_run tick_fn read_fn write_fn st (req::reqs) = do
    (st_upd, notif, rdata) <- cheshire_req read_fn write_fn st req;
    st <- tick_fn notif st;
    (st, rdatas) <- cheshire_run tick_fn read_fn write_fn (st_upd st) reqs;
    INR (st, rdata::rdatas)
  od)
End

Theorem ISR_SUM_MAP:
  ISR (SUM_MAP f g z) = ISR z
Proof
  Cases_on `z` >> simp []
QED

Theorem cheshire_run_cheshire_req_ISR:
  (!st req. MEM req reqs ==> ?st_upd notif rdata.
    cheshire_req read_fn write_fn st req = INR (st_upd, notif, rdata) /\
    ISR (tick_fn notif st)) ==>
  ISR (cheshire_run tick_fn read_fn write_fn st reqs)
Proof
  qid_spec_tac `st`
  >> Induct_on `reqs`
  >- simp [cheshire_run_def]
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> first_assum (qspecl_then [`st`, `h`] assume_tac)
      >> fs [sum_bind_def, ISR_exists]
      >> last_x_assum (qspec_then `st_upd x'` strip_assume_tac)
      >> simp [sum_bind_def]
      >> PairCases_on `x''`
      >> simp [])
QED

Theorem sum_bind_assoc:
  sum_bind (sum_bind x f) g = sum_bind x (\y. sum_bind (f y) g)
Proof
  Cases_on `x` >> simp [sum_bind_def]
QED

(*
We want to normalise this:

do
  a <- do
    (b, c) <- d;
    e b c
  od;
  f a
od

into:

do
  (b, c) <- d
  a <- e b c
  f a
od

However, plain `sum_bind_assoc` gets stuck here:

do
  y <- d;
  a <- (λ(b,c). e b c) y;
  f a
od

We should be able to use ETA_THM; but internally, it looks like this:

sum_bind d (\y. do
  a <- (λ(b,c). e b c) y;
  f a
od)

This theorem converts that into this:

sum_bind d (\y. (λ(b,c) do
  a <- e b c;
  f a
od) y)

at which point ETA_THM can be applied.
*)
Theorem sum_bind_uncurry:
  sum_bind (UNCURRY f x) g = UNCURRY (\a b. sum_bind (f a b) g) x
Proof
  pairarg_tac >> simp []
QED

Theorem cheshire_run_SNOC:
  cheshire_run tick_fn read_fn write_fn st (SNOC req reqs) =
  do
    (st, rdatas) <- cheshire_run tick_fn read_fn write_fn st reqs;
    (st_upd, notif, rdata) <- cheshire_req read_fn write_fn st req;
    st <- tick_fn notif st;
    INR (st_upd st, SNOC rdata rdatas)
  od
Proof
  qid_spec_tac `st`
  >> Induct_on `reqs`
  >- simp [cheshire_run_def, sum_bind_def]
  >- (simp [cheshire_run_def, sum_bind_assoc, sum_bind_uncurry]
      (* For some reason this doesn't work with `simp`. *)
      >> pure_rewrite_tac [ETA_THM]
      >> simp [sum_bind_def])
QED

Theorem sum_bind_INR:
  sum_bind x f = INR z ==> ?y. x = INR y /\ f y = INR z
Proof
  Cases_on `x` >> simp [sum_bind_def]
QED

Theorem cheshire_run_LENGTH_rdatas:
  cheshire_run tick_fn read_fn write_fn st reqs = INR (st', rdatas) ==>
  LENGTH rdatas = LENGTH reqs
Proof
  qid_spec_tac `st`
  >> qid_spec_tac `st'`
  >> qid_spec_tac `rdatas`
  >> Induct_on `reqs`
  >- simp [cheshire_run_def]
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> dxrule_then strip_assume_tac sum_bind_INR
      >> pairarg_tac
      >> fs []
      >> dxrule_then strip_assume_tac sum_bind_INR
      >> fs []
      >> dxrule_then strip_assume_tac sum_bind_INR
      >> pairarg_tac
      >> fs []
      >> qpat_x_assum `_::_ = _` (assume_tac o GSYM)
      >> simp []
      >> last_x_assum (qspecl_then [`rdatas'`, `st'`, `st_upd y'`] assume_tac)
      >> simp [])
QED

val _ = export_theory ();
