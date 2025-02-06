(* A formal model of Cheshire/OpenTitan's I2C peripheral. *)

open HolKernel Parse boolLib bossLib;
open byteTheory;
open ffiTheory;
open i2cMappingsTheory cheshireOracleTheory;

val _ = new_theory("i2c");

Definition i2c_oracle_read_def:
  i2c_oracle_read = cheshire_oracle_read i2c_eat_fnum i2c_tick i2c_read
End

Definition i2c_oracle_write_def:
  i2c_oracle_write = cheshire_oracle_write i2c_eat_fnum i2c_tick i2c_write
End

Definition i2c_oracle_def:
  (* 'a is the word size of the processor. *)
  i2c_oracle (:'a) = cheshire_oracle (:'a) i2c_eat_fnum i2c_tick i2c_read i2c_write
End

val _ = export_theory();
