(* A formal model of Cheshire/OpenTitan's I2C peripheral. *)

open HolKernel Parse boolLib bossLib;
open byteTheory;
open ffiTheory;
open i2cMappingsTheory;

val _ = new_theory("i2c");

Definition region_start_def:
  region_start = 0x03003000 : num
End

Definition region_end_def:
  region_end = 0x03004000 : num
End

Definition i2c_oracle_def:
  (* 'a is the word size of the processor. *)
  i2c_oracle (:'a) (s: ffiname) (st: i2c_state) [(nb: word8)] (bytes: word8 list) =
    let
      (* nb = 0 represents the word size of the processor. *)
      nb' = if nb = 0w then w2n (bytes_in_word : 'a word) else w2n nb;
      addr_offset = case s of
        SharedMem MappedRead => 0
      | SharedMem MappedWrite => nb'
      | _ => 0; (* We'll return an error later on. *)
      (* The F means little-endian; nothing else in CakeML bothers handling big-endian
       * systems, so I won't here either. *)
      addr_word = word_of_bytes F 0w (DROP addr_offset bytes) : 'a word;
      addr = w2n addr_word;
      st' = apply_fbits st;
    in
      (* TODO: I'm pretty sure 64-bit reads get split up into two 32-bit reads, but no
       * sane driver should be using 64-bit accesses on 32-bit registers anyway.
       *
       * If we do implement it, we should use `fnums` to reorder the reads
       * non-deterministically (use each number as an index into the list of remaining
       * options?), and use `apply_fbits` to simulate an arbitrary delay between
       * reads. *)
      if addr < region_start \/ addr >= region_end \/ nb' > 4 then
        Oracle_final FFI_failed
      else
        case s of
          SharedMem MappedRead =>
            (case i2c_read st' nb' (addr - region_start) of
              INL outcome => Oracle_final outcome
            | INR (notif, value) => Oracle_return (i2c_tick notif st') (TAKE nb' (word_to_bytes value F)))
        | SharedMem MappedWrite =>
            let
              value = word_of_bytes F 0w (TAKE addr_offset bytes)
            in
              (case i2c_write st' nb' (addr - region_start) value of
                INL outcome => Oracle_final outcome
                (* Register writes from software take priority over ones from software, so
                 * applying `st_upd` after `i2c_tick` is correct. *)
              | INR (st_upd, notif) => Oracle_return (st_upd (i2c_tick notif st')) [])
        | _ => Oracle_final FFI_failed
End

val _ = export_theory();
