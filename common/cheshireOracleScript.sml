open HolKernel Parse boolLib bossLib;
open BasicProvers;
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
  (cheshire_run tick_fn read_fn write_fn st (req::reqs) =
    case cheshire_req read_fn write_fn st req of
      INL x => INL x
    | INR (st_upd, notif, rdata) => SUM_MAP I (I ## (CONS rdata))
        (cheshire_run tick_fn read_fn write_fn (st_upd (tick_fn notif st)) reqs))
End

Theorem ISR_SUM_MAP:
  !f g z. ISR (SUM_MAP f g z) = ISR z
Proof
  Cases_on `z` >> simp []
QED

Theorem cheshire_run_cheshire_req_ISR:
  !st reqs.
  (!st req. MEM req reqs ==> ISR (cheshire_req read_fn write_fn st req)) ==>
  ISR (cheshire_run tick_fn read_fn write_fn st reqs)
Proof
  Induct_on `reqs`
  >- simp [cheshire_run_def]
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> `?oracle_res. cheshire_req read_fn write_fn st h = INR oracle_res` by simp [GSYM sumExtraTheory.ISR_exists]
      >> PairCases_on `oracle_res`
      >> simp [ISR_SUM_MAP])
QED

Theorem cheshire_run_SNOC:
  !tick_fn read_fn write_fn st req reqs.
  cheshire_run tick_fn read_fn write_fn st (SNOC req reqs) =
  case cheshire_run tick_fn read_fn write_fn st reqs of
    INL x => INL x
  | INR (st', rdatas) =>
    case cheshire_req read_fn write_fn st' req of
      INL x => INL x
    | INR (st_upd, notif, rdata) => INR (st_upd (tick_fn notif st'), SNOC rdata rdatas)
Proof
  Induct_on `reqs`
  >- simp [cheshire_run_def]
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> Cases_on `cheshire_req read_fn write_fn st h`
      >- simp []
      >- (PairCases_on `y`
          >> Cases_on `cheshire_run tick_fn read_fn write_fn (y0 (tick_fn y1 st)) reqs`
          >- simp []
          >- (PairCases_on `y`
              >> Cases_on `cheshire_req read_fn write_fn y0' req`
              >- simp []
              >- (PairCases_on `y` >> simp []))))
QED

Theorem cheshire_run_LENGTH_rdatas:
  !tick_fn read_fn write_fn st reqs st' rdatas.
  cheshire_run tick_fn read_fn write_fn st reqs = INR (st', rdatas) ==>
  LENGTH rdatas = LENGTH reqs
Proof
  Induct_on `reqs`
  >- simp [cheshire_run_def]
  >- (simp [cheshire_run_def]
      >> rpt strip_tac
      >> Cases_on `cheshire_req read_fn write_fn st h`
      >- fs []
      >- (PairCases_on `y`
          >> Cases_on `cheshire_run tick_fn read_fn write_fn (y0 (tick_fn y1 st)) reqs`
          >- fs []
          >- (PairCases_on `y`
              >> fs []
              >> qpat_x_assum `_ = rdatas` (assume_tac o GSYM)
              >> simp []
              >> last_x_assum $ drule_then assume_tac
              >> simp [])))
QED

val _ = export_theory ();
