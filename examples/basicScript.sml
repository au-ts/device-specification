open HolKernel Parse boolLib bossLib;
open dep_rewrite;
open alignmentTheory arithmeticTheory bitTheory dividesTheory finite_mapTheory listTheory wordsTheory;
open wordsLib;
open ffiTheory panLangTheory panPropsTheory panSemTheory;
(* panHoareLib is just for `parse_pancake_file`. *)
(* panPtreeConversionTheory is a dependency of panHoareLib that isn't getting picked up properly. *)
open panPtreeConversionTheory panHoareLib;
open cheshireOracleTheory i2cTheory i2cCoreTheory i2cMappingsTheory sharedMemoryOracleTheory;

val _ = new_theory "basic";

val (ast, _) = parse_pancake_file "basic.pnk";

Definition the_code_def:
  the_code = FEMPTY |++ (MAP (I ## SND) (^ast))
End

Theorem FLOOKUP_read_byte = EVAL ``FLOOKUP the_code «read_byte»``;

Theorem read_byte_result:
  the_code SUBMAP s.code
  /\ offset_addrs 0x03003000w i2c_addrs SUBSET s.sh_memaddrs
  /\ s.ffi.oracle = offset_oracle (:64) 0x03003000 i2c_oracle_read i2c_oracle_write
  /\ 0 < s.clock
  ==>
    let
      prog = Call NONE (Label «read_byte») [];
      (st', value) = OUTR (i2c_oracle_read s.ffi.ffi_state 1 0x18);
      value' = n2w value;
      ev = IO_event (SharedMem MappedRead) [1w] (ZIP (word_to_bytes (0x03003018w: word64) F, word_to_bytes value' F));
    in
      evaluate (prog, s) = (
        SOME (Return (ValWord value')),
        empty_locals (s with <|
          clock := s.clock - 1;
          ffi := s.ffi with <|
            ffi_state := st';
            io_events := s.ffi.io_events ++ [ev];
          |>;
        |>)
      )
Proof
  strip_tac
  >> assume_tac FLOOKUP_read_byte
  >> drule_all FLOOKUP_SUBMAP
  >> fs [evaluate_def, eval_def, lookup_code_def, FUPDATE_LIST, FLOOKUP_UPDATE, offset_oracle_def, nb_op_def, offset_addrs_def, i2c_addrs_def, byte_align_def, align_def, dec_clock_def]
  >> ‘(s with
         <|locals := FEMPTY |+ («val», ValWord 0w);
           clock := s.clock - 1|>).ffi.oracle =
      sh_mem_oracle (:64) (offset_oracle_read 0x03003000 i2c_oracle_read) (offset_oracle_write 0x03003000 i2c_oracle_write)’ by simp []
  >> drule_then (qspecl_then [‘«val»’, ‘1’, ‘0x3003018w’] assume_tac) sh_mem_load_sh_mem_oracle
  >> rfs [byte_align_def, align_def, dimindex_64, DIVIDES_MOD_0, offset_oracle_read_def, i2c_oracle_read_def, cheshire_oracle_read_def, i2c_read_def, interp_nb_def, set_var_def, FLOOKUP_UPDATE, shape_of_def, size_of_shape_def, w2n_w2w, GSYM w2w_def, word_bits_w2w, empty_locals_def, WORD_ALL_BITS]
QED

Theorem cheshire_wait_rx_fifo:
  !st.
  let
    st' = cheshire_wait i2c_eat_fnum i2c_tick st
  in
    ?bytes. st'.rx_fifo = st.rx_fifo ++ bytes
Proof
  strip_tac
  >> simp [cheshire_wait_def, i2c_eat_fnum]
  >> ‘(\st'. ?bytes. st'.rx_fifo = st.rx_fifo ++ bytes) (FUNPOW (i2c_tick NONE) (st.fnums 0) (st with fnums := st.fnums o SUC))’ suffices_by simp []
  >> irule FUNPOW_invariant
  >> rw []
  >> rw [i2c_tick_def]
QED

Theorem read_byte_correct:
  the_code SUBMAP s.code
  /\ offset_addrs 0x03003000w i2c_addrs SUBSET s.sh_memaddrs
  /\ s.ffi.oracle = offset_oracle (:64) 0x03003000 i2c_oracle_read i2c_oracle_write
  /\ 0 < s.clock
  ==>
  ?bytes.
    let
      prog = Call NONE (Label «read_byte») [];
      st = s.ffi.ffi_state;
      (res, t) = evaluate (prog, s);
      st' = t.ffi.ffi_state;
      rx_fifo' = st.rx_fifo ++ bytes;
    in
      res = SOME (Return (ValWord (if NULL rx_fifo' then 0w else w2w (HD rx_fifo'))))
      /\ ?bytes'. st'.rx_fifo = (if NULL rx_fifo' then rx_fifo' else TL rx_fifo') ++ bytes'
Proof
  strip_tac
  >> drule_all read_byte_result
  >> strip_tac
  >> rfs [i2c_oracle_read_def, cheshire_oracle_read_def, i2c_read_def, w2n_w2w]
  >> rfs [GSYM w2w_def, i2c_get_rdata_rdata_def, empty_locals_def, cheshire_wait_rx_fifo, i2c_tick_def]
  >> qspec_then ‘s.ffi.ffi_state’ assume_tac cheshire_wait_rx_fifo
  >> fs []
  >> qrefine ‘bytes’
  >> qspec_then ‘w2w: word8 -> word64’ assume_tac COND_RAND
  >> rw []
  >> metis_tac []
QED

val _ = export_theory ();
