open HolKernel Parse boolLib bossLib;
open wordsTheory;
open translatorTheory;

val _ = new_theory "cheshireMisc";

Theorem INR_imp_ISR:
  x = INR y ==> ISR x
Proof
  simp []
QED

Theorem SUM_MAP_INR:
  SUM_MAP f g x = INR y <=> ?z. x = INR z /\ g z = y
Proof
  Cases_on `x` >> simp []
QED

Theorem ISL_SUM_MAP:
  ISL (SUM_MAP f g z) = ISL z
Proof
  Cases_on `z` >> simp []
QED

Theorem OUTR_SUM_MAP:
  ISR z ==> OUTR (SUM_MAP f g z) = g (OUTR z)
Proof
  Cases_on `z` >> simp []
QED

Theorem procs_append:
  procs (ps ++ qs) fext s s' = procs qs fext s (procs ps fext s s')
Proof
  qid_spec_tac `s'`
  >> Induct_on `ps`
  >> simp [procs_def]
QED

Theorem procs_unchanged:
  (!p fext s s'. MEM p ps ⇒ f (p fext s s') = f s') ==>
  f (procs ps fext s s') = f s'
Proof
  qid_spec_tac `s'`
  >> Induct_on `ps`
  >> simp [procs_def]
QED

Theorem word_bits_bit_field_insert:
  h < dimindex (:'a) ∧ dimindex (:'b) = h + 1 - l ⇒
  (h -- l) (bit_field_insert h l (v: 'b word) (w: 'a word)) = w2w v
Proof
  rpt strip_tac
  >> asm_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [word_bits_def, bit_field_insert_def, word_modify_def, Cong AND_CONG, w2w]
  >> rpt strip_tac
  >> ‘i < h + 1 − l ⇔ i + l < h + 1’ by (fs [] >> simp [DIMINDEX_GT_0])
  >> simp [arithmeticTheory.LE_LT1]
QED

Theorem word_extract_bit_field_insert:
  h < dimindex (:'a) ∧ dimindex (:'b) = h + 1 - l ⇒
  (h >< l) (bit_field_insert h l (v: 'b word) (w: 'a word)) = v
Proof
  simp [word_extract_def, word_bits_bit_field_insert, w2w_w2w, WORD_ALL_BITS]
QED

Theorem word_bit_bit_field_insert:
  i < l \/ h < i ==> word_bit i (bit_field_insert h l a b) = word_bit i b
Proof
  asm_simp_tac (boss_ss () ++ fcpLib.FCP_ss) [word_bit_def, bit_field_insert_def, word_modify_def, arithmeticTheory.SUB_LESS_OR_EQ, Cong AND_CONG]
QED

(* For some reason `simp` vehemently refuses to use the original `FCP_APPLY_UPDATE_THM`. *)
Theorem FCP_APPLY_UPDATE_THM_2:
  b < dimindex (:'b) ==> (a :+ w) (m: 'a['b]) ' b = if a = b then w else m ' b
Proof
  assume_tac fcpTheory.FCP_APPLY_UPDATE_THM >> simp []
QED

Theorem eq_w2n_iff_eq_n2w:
  n < dimword (:'a) ==> (n = w2n (w: 'a word) <=> w = n2w n)
Proof
  rpt strip_tac
  >> iff_tac
  >> simp []
QED

Theorem eq_n2w_iff_w2n_eq:
  n < dimword (:'a) ==> (w = n2w n <=> w2n (w: 'a word) = n)
Proof
  rpt strip_tac
  >> iff_tac
  >- simp []
  >- (strip_tac
      >> first_x_assum (assume_tac o GSYM)
      >> simp [eq_w2n_iff_eq_n2w])
QED

Theorem mk_circuit_cstep:
  ∃s'. mk_circuit sstep cstep s fext n = cstep (fext n) s' s'
Proof
  Cases_on ‘n’
  >- (qexists ‘s’ >> simp [mk_circuit_def])
  >- (qexists ‘(sstep (fext n') (mk_circuit sstep cstep s fext n')
                      (mk_circuit sstep cstep s fext n'))’
      >> simp [mk_circuit_def])
QED

val _ = export_theory ();
