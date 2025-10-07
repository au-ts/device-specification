open HolKernel Parse boolLib bossLib;
open i2cCircuitTheory i2cCoreCircuitProofTheory i2cRegsCircuitProofTheory;

val _ = new_theory "i2cCircuitProof";

val asm1_simp = BETA_RULE o REWRITE_RULE [combinTheory.C_THM, listTheory.EVERY_MEM] o GEN_ALL

val ff_asm1' = ff_asm1 |> asm1_simp
val comb_asm1' = comb_asm1 |> asm1_simp

Theorem asm1:
∀proc fext s s'.
  MEM proc (i2c_core_ffs1 ++ [] ++ i2c_core_combs) ⇒
  (let
      s'' = proc fext s s'
    in
      s''.reg2hw = s'.reg2hw ∧ s''.regs = s'.regs ∧
      s''.reg_rsp_o = s'.reg_rsp_o ∧ s''.raw_addr = s'.raw_addr ∧
      s''.addr = s'.addr ∧ (s''.write ⇔ s'.write) ∧
      s''.wdata = s'.wdata ∧ s''.wstrb = s'.wstrb ∧
      (s''.valid ⇔ s'.valid) ∧ (s''.error ⇔ s'.error) ∧
      s''.win_buses.req = s'.win_buses.req)
Proof
  ASSUME_TAC ff_asm1'
  >> ASSUME_TAC comb_asm1'
  >> rpt GEN_TAC
  >> REWRITE_TAC [rich_listTheory.IS_EL_APPEND, listTheory.MEM]
  >> STRIP_TAC
  >> FIRST_X_ASSUM (fn th1 => FIRST_ASSUM (fn th2 => MATCH_MP th2 th1 |> REWRITE_RULE [LET_THM] |> BETA_RULE |> ASSUME_TAC))
  >> rw [LET_THM]
QED

Theorem asm2:
∀proc fext s s'. MEM proc i2c_core_ffs1 ⇒ (proc fext s s').hw2reg = s'.hw2reg
Proof
  rw [ff_asm2 |> asm1_simp]
QED

val _ = type_abbrev(
  "proc_ty",
  “:(i2c_circuit_ext_state -> i2c_circuit_state -> i2c_circuit_state -> i2c_circuit_state) list”);

val i2c_reg_top_correct' = i2c_reg_top_correct
             |> INST [“combs:proc_ty” |-> “i2c_core_combs” ,
                      “ffs2:proc_ty” |-> “[]:proc_ty” ,
                      “ffs1:proc_ty” |-> “i2c_core_ffs1”]
             |> REWRITE_RULE [GSYM i2c_circuit_def, Ntimes LET_THM 1]
             |> BETA_RULE
             |> IMP_CANON
             |> hd

(* this is the theorem ‘i2c_reg_top_correct’ with the first two assumptions
   being discharged, targetted specifically for ‘i2c_circuit’ *)
Theorem i2c_correct =
  MATCH_MP (MATCH_MP (MATCH_MP i2c_reg_top_correct' asm1) asm2) i2c_core_correct

val _ = export_theory ();
