open HolKernel Parse boolLib bossLib;
open wordsLib;
open arithmeticTheory;
open ffiTheory panSemTheory;
open byteExtraTheory;

val _ = new_theory "sharedMemoryOracle";

Definition interp_nb_def:
  (* nb = 0 represents the word size of the processor. *)
  interp_nb (:'a) nb = if nb = 0 then dimindex (:'a) DIV 8 else nb
End

Definition sh_mem_oracle_def:
  (* 'a is the word size of the processor. *)
  sh_mem_oracle (:'a)
    (read: 'ffi -> num -> num -> ffi_outcome + 'ffi # num)
    (write: 'ffi -> num -> num -> num -> ffi_outcome + 'ffi)
    (s: ffiname) (st: 'ffi) (conf: word8 list) (bytes: word8 list) =
    let
      nb = HD conf;
      nb' = interp_nb (:'a) (w2n nb);
      addr_offset = case s of
        SharedMem MappedRead => 0
      | SharedMem MappedWrite => nb'
      | _ => 0; (* We'll return an error later on. *)
      (* The F means little-endian: little-endian is used to encode shared-memory I/O regardless of the processor's endianness. *)
      addr = word_of_bytes F 0w (DROP addr_offset bytes): 'a word;
    in
      case s of
        SharedMem MappedRead =>
          (case read st nb' (w2n addr) of
            INL outcome => Oracle_final outcome
          | INR (st', value) => Oracle_return st' (word_to_bytes ((8 * nb' - 1 -- 0) (n2w value: 'a word)) F))
      | SharedMem MappedWrite =>
          let
            value = word_of_bytes F 0w (TAKE addr_offset bytes): 'a word;
          in
            (case write st nb' (w2n addr) (w2n value) of
              INL outcome => Oracle_final outcome
            | INR st' => Oracle_return st' (GENLIST (K 0w) (LENGTH bytes)))
      | _ => Oracle_final FFI_failed
End

Theorem sh_mem_oracle_read_Oracle_return:
  sh_mem_oracle (:'a) read write (SharedMem MappedRead) st [nb] (word_to_bytes (addr: 'a word) F) = Oracle_return st' bytes'
  /\ 8 <= dimindex (:'a)
  /\ divides 8 (dimindex (:'a))
  ==> ?value. read st (interp_nb (:'a) (w2n nb)) (w2n addr) = INR (st', value)
              /\ bytes' = word_to_bytes ((8 * interp_nb (:'a) (w2n nb) - 1 -- 0) (n2w value: 'a word)) F
Proof
  strip_tac
     (* sh_mem_oracle needs to be in the goal for CASE_TAC to apply to it. *)
  >> last_x_assum mp_tac
  >> simp [sh_mem_oracle_def, word_to_bytes_word_of_bytes_le]
  >> rpt CASE_TAC
QED

Theorem sh_mem_oracle_read_Oracle_final:
  8 <= dimindex (:'a)
  /\ divides 8 (dimindex (:'a))
  ==> (sh_mem_oracle (:'a) read write (SharedMem MappedRead) st [nb] (word_to_bytes (addr: 'a word) F) = Oracle_final outcome
     <=> read st (interp_nb (:'a) (w2n nb)) (w2n addr) = INL outcome)
Proof
  strip_tac
  >> simp [sh_mem_oracle_def, word_to_bytes_word_of_bytes_le]
  >> iff_tac
  >- rpt CASE_TAC
  >- simp []
QED

Theorem sh_mem_load_sh_mem_oracle:
  s.ffi.oracle = sh_mem_oracle (:'a) read write
  /\ (if nb = 0 then addr else byte_align addr) IN s.sh_memaddrs
  /\ 32 <= dimindex (:'a)
  /\ divides 8 (dimindex (:'a))
  /\ nb <= 4
  ==> sh_mem_load v (addr: 'a word) nb s =
    let
      nm = SharedMem MappedRead;
      conf = [n2w nb];
      bytes = word_to_bytes addr F;
      nb' = interp_nb (:'a) nb;
    in
      case read s.ffi.ffi_state nb' (w2n addr) of
        (* TODO: this should probably be constrained to 'a result inside CakeML, not here. *)
        INL outcome => (SOME (FinalFFI (Final_event nm conf bytes outcome): 'a result), empty_locals s)
      | INR (st', value) =>
          let
            value' = (8 * nb' - 1 -- 0) (n2w value);
            bytes' = word_to_bytes value' F;
          in (
            NONE,
            (set_var v (ValWord value') s) with ffi := s.ffi with <|
              ffi_state := st';
              io_events := s.ffi.io_events ++ [IO_event nm conf (ZIP (bytes, bytes'))];
            |>
          )
Proof
  simp [sh_mem_load_def, call_FFI_def]
  >> Cases_on ‘nb = 0’
  >> simp []
  >> (CASE_TAC
      >- (drule sh_mem_oracle_read_Oracle_return
          >> rpt strip_tac
          >> ‘32 DIV 8 <= dimindex (:'a) DIV 8’ by simp [DIV_LE_MONOTONE]
          >> fs []
          >> ‘1 <= interp_nb (:'a) nb’ by simp [interp_nb_def]
          >> rfs [word_to_bytes_length, word_to_bytes_word_of_bytes_le])
      >- (strip_tac
          >> fs [sh_mem_oracle_read_Oracle_final]))
QED

Definition offset_oracle_read_def:
  offset_oracle_read (base: num) read st nb addr =
  if addr < base then
    INL FFI_failed
  else
    read st nb (addr - base)
End

Definition offset_oracle_write_def:
  offset_oracle_write (base: num) write st nb addr value =
  if addr < base then
    INL FFI_failed
  else
    write st nb (addr - base) value
End

Definition offset_oracle_def:
  offset_oracle (:'a) base read write =
  sh_mem_oracle (:'a) (offset_oracle_read base read) (offset_oracle_write base write)
End

Definition offset_addrs_def:
  offset_addrs (base: 'a word) (addrs: 'a word set) = IMAGE (\addr. base + addr) addrs
End

val _ = export_theory ();
