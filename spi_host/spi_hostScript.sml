(* A formal model of Cheshire/OpenTitan's spi_host peripheral. *)

open HolKernel Parse boolLib bossLib;
open byteTheory;
open ffiTheory;
open spi_hostMappingsTheory cheshireOracleTheory;

val _ = new_theory("spi_host");

Definition spi_host_oracle_read_def:
  spi_host_oracle_read = cheshire_oracle_read spi_host_eat_fnum spi_host_tick spi_host_read
End

Definition spi_host_oracle_write_def:
  spi_host_oracle_write = cheshire_oracle_write spi_host_eat_fnum spi_host_tick spi_host_write
End

Definition spi_host_oracle_def:
  (* 'a is the word size of the processor. *)
  spi_host_oracle (:'a) = cheshire_oracle (:'a) spi_host_eat_fnum spi_host_tick spi_host_read spi_host_write
End

val _ = export_theory();
