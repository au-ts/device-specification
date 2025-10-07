open BasicProvers;
open translatorLib;
open shallowFlattenLib;
open cheshireMiscTheory;
open cheshireOracleTheory;
open i2cCircuitTheory;
open dep_rewrite;
open i2cCoreTheory;
open i2cMappingsTheory;
open i2cCircuitStateTheory;
open i2cRegsCommTheory;

val _ = new_theory "i2cCoreCircuitProof"

Theorem word_bit_UINT_MAXw:
  word_bit (dimindex (:'a) - 1) (UINT_MAXw : 'a word)
Proof
  blastLib.BBLAST_TAC
  >> conj_tac
  >- ( rw [fcpTheory.DIMINDEX_GE_1] )
  >> ‘dimindex (:'a) - 1 < dimindex (:'a)’ by ( MP_TAC fcpTheory.DIMINDEX_GE_1 THEN decide_tac)
  >> drule wordsTheory.WORD_NEG_1_T
  >> disch_then ACCEPT_TAC
QED

Theorem word_bit_eq_GT:
  (word_bit (dimindex (:'a) - 1) x ⇔ word_bit (dimindex (:'a) - 1) (x + 1w)) ⇒ (x : 'a word) + 1w >+ x
Proof
  strip_tac
  >> rewrite_tac [wordsTheory.WORD_HIGHER, wordsTheory.WORD_LO]
  >> ‘w2n (x + 1w) = w2n x + 1’ suffices_by ( simp [] )
  >> ‘x ≠ UINT_MAXw : 'a word’ suffices_by ( rw [wordsTheory.w2n_plus1])
  >> spose_not_then assume_tac
  >> ‘word_bit (dimindex (:'a) - 1) x’ by ( metis_tac [word_bit_UINT_MAXw])
  >> ‘(UINT_MAXw : 'a word) + 1w = 0w’ by ( blastLib.BBLAST_TAC)
  >> ‘(x + 1w) = 0w’ by ( fs [] )
  >> ‘¬word_bit (dimindex (:'a) - 1) (x + 1w)’ by ( metis_tac [wordsTheory.word_bit_0])
  >> metis_tac []
QED

Theorem word_msb_1:
  1 < dimindex (:α) ⇒ ¬word_bit (dimindex (:α) - 1) (1w: α word)
Proof
  simp [wordsTheory.word_bit_n2w]
QED

Theorem fifo_rel_not_null:
  fifo_rel ws (circuit : 'a word -> 'b) (rptr: 'c word) wptr ∧ ¬ NULL ws ⇒ rptr ≠ wptr
Proof
  Induct_on ‘ws’ >- ( rw [fifo_rel_def] )
  >> NTAC 2 strip_tac
  >> ASM_CASES_TAC “word_bit (dimindex(:'c) - 1) (rptr: 'c word) = word_bit (dimindex(:'c) - 1) (wptr: 'c word)”
  >- (
  ‘wptr >+ rptr’ by (
    qpat_x_assum ‘fifo_rel (_ :: _) _ _ _’ mp_tac
    THEN rw [fifo_rel_def] )
  >> fs [wordsTheory.WORD_HIGHER]
  >> drule wordsTheory.WORD_LOWER_NOT_EQ
  >> disch_then ACCEPT_TAC )
  >- (
  spose_not_then (assume_tac o REWRITE_RULE [GSYM wordsTheory.WORD_EQ])
  >> ‘0 < dimindex (:'c)’ by (irule wordsTheory.DIMINDEX_GT_0 )
  >> ‘dimindex (:'c) - 1 < dimindex(:'c)’ by decide_tac
  >> fs []
  )
QED

Theorem n2w_length_fifo:
  fifo_rel ws (circuit: 6 word -> 'a) (rptr:7 word) (wptr:7 word) ⇒
  n2w $ LENGTH ws = if (word_bit 6 wptr ≠ word_bit 6 rptr) ∧ ((5 >< 0) wptr :word6 = (5 >< 0) rptr :word6) then 64w : word7
                    else if word_bit 6 wptr = word_bit 6 rptr then -1w * ((5 >< 0) rptr : word7) + ((5 >< 0) wptr : word7)
                    else -1w * ((5 >< 0) rptr : word7) + (((5 >< 0) wptr : word7) + 64w)
Proof
  qid_spec_tac ‘rptr’
  >> Induct_on ‘ws’ >- ( rw [fifo_rel_def] )
  >> rpt strip_tac
  >> ‘fifo_rel ws circuit (rptr + 1w) wptr’ by ( fs [fifo_rel_def ])
  >> first_x_assum drule
  >> disch_then assume_tac
  >> IF_CASES_TAC
  >- (
  ASM_CASES_TAC “rptr: 7 word = 63w”
  >- (
    ‘rptr + 1w = 64w’ by ( asm_rewrite_tac [] THEN EVAL_TAC)
    THEN ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by ( rw [] )
    THEN ‘(5 >< 0) (rptr + 1w) : 7 word = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘n2w $ LENGTH ws = (5 >< 0) wptr : 7 word’ by (
      asm_rewrite_tac []
      >> EVAL_TAC
      >> rw [wordsTheory.WORD_ADD_0] )
    THEN ‘(5 >< 0) wptr : 7 word = (5 >< 0) rptr : 7 word’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
    THEN ‘n2w $ LENGTH ws = 63w : 7 word’ by (
      qpat_x_assum ‘n2w $ LENGTH ws = if _ then _ else _’ mp_tac
      >> asm_rewrite_tac []
      >> blastLib.BBLAST_TAC )
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN EVAL_TAC )
  >> ASM_CASES_TAC “rptr: 7 word = 127w”
  >- (
    ‘rptr + 1w = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC)
    THEN ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by ( rw [] )
    THEN ‘(5 >< 0) (rptr + 1w) : 7 word = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘n2w $ LENGTH ws = (5 >< 0) wptr : 7 word’ by (
      asm_rewrite_tac []
      >> EVAL_TAC
      >> rw [wordsTheory.WORD_ADD_0] )
    THEN ‘(5 >< 0) wptr : 7 word = (5 >< 0) rptr : 7 word’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
    THEN ‘(5 >< 0) rptr : 7 word = 63w’ by ( fs [] THEN EVAL_TAC)
    THEN ‘n2w $ LENGTH ws = 63w : 7 word’  by ( fs [] )
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN EVAL_TAC )
  >> ‘word_bit 6 (rptr + 1w) = word_bit 6 rptr’ by (rpt $ qpat_x_assum ‘rptr ≠ _’ mp_tac THEN blastLib.BBLAST_TAC)
  >> ‘word_bit 6 wptr ≠ word_bit 6 (rptr + 1w)’ by ( fs [] )
  >> ‘((5 >< 0) wptr : 6 word) ≠ ((5 >< 0) (rptr + (1w : 7 word)) : 6 word)’ by (
    qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
  >> ‘(n2w (LENGTH ws) :word7) =
      ((5 >< 0) (wptr :word7) :word7) + -(1w :word7) * ((5 >< 0) ((rptr :word7) + (1w :word7)) :word7) + (64w :word7)’
    by ( fs [] )
  >> ‘((5 >< 0) (wptr :word7) :word7) = ((5 >< 0) rptr : word7)’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC)
  >> ‘((5 >< 0) (wptr :word7) :word7) + -(1w :word7) * ((5 >< 0) ((rptr :word7) + (1w :word7)) :word7) + (64w :word7) = (63w: word7)’ by (
    rpt $ qpat_x_assum ‘rptr ≠ _’ mp_tac
    THEN simp [SF WORD_ss, SF WORD_ARITH_EQ_ss, SF WORD_EXTRACT_ss]
    THEN asm_rewrite_tac []
    THEN blastLib.BBLAST_TAC )
  >> asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
  >> EVAL_TAC )
  >> IF_CASES_TAC
  >- (
  ‘wptr >+ rptr’ by (
    qpat_x_assum ‘fifo_rel (_ :: _) _ _ _’ mp_tac
    THEN rewrite_tac [fifo_rel_def]
    THEN EVAL_TAC
    THEN rw [] )
  >> ‘rptr + 1w <+ wptr ∨ rptr + 1w = wptr’ by (first_x_assum mp_tac THEN blastLib.BBLAST_TAC)
  >- (
    ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (NTAC 3 $ first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
    THEN qpat_x_assum ‘n2w $ LENGTH ws = _’ mp_tac
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN disch_then (fn th => REWRITE_TAC [th])
    THEN NTAC 4 $ first_x_assum mp_tac
    THEN simp [SF WORD_ARITH_ss, SF WORD_EXTRACT_ss, SF WORD_ss]
    THEN blastLib.BBLAST_TAC )
  >- (
    ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (NTAC 3 $ first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
    THEN qpat_x_assum ‘n2w $ LENGTH ws = _’ mp_tac
    THEN qpat_x_assum ‘rptr + 1w = wptr’ mp_tac
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN disch_then assume_tac
    THEN disch_then (fn th => REWRITE_TAC [th])
    THEN NTAC 4 $ first_x_assum mp_tac
    THEN simp [SF WORD_ARITH_ss, SF WORD_EXTRACT_ss, SF WORD_ss]
    THEN blastLib.BBLAST_TAC ) )
  >> ‘(5 >< 0) wptr :word6 <=+ (5 >< 0) rptr : word6’ by (
    qpat_x_assum ‘fifo_rel (_ :: _) _ _ _’ mp_tac
    THEN rewrite_tac [fifo_rel_def]
    THEN EVAL_TAC
    THEN rw [] )
  >> ASM_CASES_TAC “(5 >< 0) (rptr: word7) = 63w: word6”
  >- (
  ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by (first_x_assum mp_tac >> blastLib.BBLAST_TAC)
  THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (
    rpt $ qpat_x_assum ‘word_bit _ _ ≠ word_bit _ _’ mp_tac >> blastLib.BBLAST_TAC)
  THEN qpat_x_assum ‘n2w $ LENGTH ws = _’ mp_tac
  THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
  THEN disch_then (fn th => REWRITE_TAC [th])
  THEN qpat_x_assum ‘_ = 63w : word6’ mp_tac
  THEN blastLib.BBLAST_TAC )
  >> ‘word_bit 6 rptr = word_bit 6 (rptr + 1w)’ by (first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
  >> ‘word_bit 6 wptr ≠ word_bit 6 (rptr + 1w)’ by ( fs [] )
  >> ‘(5 >< 0) wptr : word6 ≠ (5 >< 0) (rptr + 1w) : word6’ by (
    qpat_x_assum ‘_ <=+ _’ mp_tac
    THEN qpat_x_assum ‘_ ≠ 63w : word6’ mp_tac
    THEN blastLib.BBLAST_TAC )
  >> qpat_x_assum ‘n2w $ LENGTH ws = _’ mp_tac
  >> asm_rewrite_tac [wordsTheory.n2w_SUC, listTheory.LENGTH]
  >> disch_then (fn th => REWRITE_TAC [th])
  >> qpat_x_assum ‘_ ≠ 63w : word6’ mp_tac
  >> blastLib.BBLAST_TAC
QED

Theorem length_fifo:
  fifo_rel ws (circuit: 6 word -> 'a) (rptr:7 word) (wptr:7 word) ⇒
  LENGTH ws = if (word_bit 6 wptr ≠ word_bit 6 rptr) ∧ ((5 >< 0) wptr :word6 = (5 >< 0) rptr :word6) then w2n (64w : word7)
              else if word_bit 6 wptr = word_bit 6 rptr then w2n (-1w * ((5 >< 0) rptr : word7) + ((5 >< 0) wptr : word7))
              else w2n (-1w * ((5 >< 0) rptr : word7) + (((5 >< 0) wptr : word7) + 64w))
Proof
  qid_spec_tac ‘rptr’
  >> Induct_on ‘ws’ >- ( rw [fifo_rel_def] )
  >> rpt strip_tac
  >> ‘fifo_rel ws circuit (rptr + 1w) wptr’ by ( fs [fifo_rel_def ])
  >> first_x_assum drule
  >> disch_then assume_tac
  >> IF_CASES_TAC
  >- (
  ASM_CASES_TAC “rptr: 7 word = 63w”
  >- (
    ‘rptr + 1w = 64w’ by ( asm_rewrite_tac [] THEN EVAL_TAC)
    THEN ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by ( rw [] )
    THEN ‘(5 >< 0) (rptr + 1w) : 7 word = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘LENGTH ws = w2n ((5 >< 0) wptr : 7 word)’ by (
      asm_rewrite_tac []
      >> EVAL_TAC
      >> rw [wordsTheory.WORD_ADD_0] )
    THEN ‘(5 >< 0) wptr : 7 word = (5 >< 0) rptr : 7 word’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
    THEN ‘LENGTH ws = w2n (63w : 7 word)’ by (
      qpat_x_assum ‘LENGTH ws = if _ then _ else _’ mp_tac
      >> asm_rewrite_tac []
      >> EVAL_TAC )
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN EVAL_TAC )
  >> ASM_CASES_TAC “rptr: 7 word = 127w”
  >- (
    ‘rptr + 1w = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC)
    THEN ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by ( rw [] )
    THEN ‘(5 >< 0) (rptr + 1w) : 7 word = 0w’ by ( asm_rewrite_tac [] THEN EVAL_TAC )
    THEN ‘LENGTH ws = w2n $ (5 >< 0) wptr : 7 word’ by (
      asm_rewrite_tac []
      >> EVAL_TAC
      >> rw [wordsTheory.WORD_ADD_0] )
    THEN ‘(5 >< 0) wptr : 7 word = (5 >< 0) rptr : 7 word’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
    THEN ‘(5 >< 0) rptr : 7 word = 63w’ by ( fs [] THEN EVAL_TAC)
    THEN ‘LENGTH ws = w2n $ 63w : 7 word’  by ( fs [] )
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
    THEN EVAL_TAC )
  >> ‘word_bit 6 (rptr + 1w) = word_bit 6 rptr’ by (rpt $ qpat_x_assum ‘rptr ≠ _’ mp_tac THEN blastLib.BBLAST_TAC)
  >> ‘word_bit 6 wptr ≠ word_bit 6 (rptr + 1w)’ by ( fs [] )
  >> ‘((5 >< 0) wptr : 6 word) ≠ ((5 >< 0) (rptr + (1w : 7 word)) : 6 word)’ by (
    qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC )
  >> ‘LENGTH ws =
      w2n $ ((5 >< 0) (wptr :word7) :word7) + -(1w :word7) * ((5 >< 0) ((rptr :word7) + (1w :word7)) :word7) + (64w :word7)’
    by ( fs [] )
  >> ‘((5 >< 0) (wptr :word7) :word7) = ((5 >< 0) rptr : word7)’ by ( qpat_x_assum ‘_ ∧ _’ mp_tac THEN blastLib.BBLAST_TAC)
  >> ‘((5 >< 0) (wptr :word7) :word7) + -(1w :word7) * ((5 >< 0) ((rptr :word7) + (1w :word7)) :word7) + (64w :word7) = (63w: word7)’ by (
    rpt $ qpat_x_assum ‘rptr ≠ _’ mp_tac
    THEN simp [SF WORD_ss, SF WORD_ARITH_EQ_ss, SF WORD_EXTRACT_ss]
    THEN asm_rewrite_tac []
    THEN blastLib.BBLAST_TAC )
  >> asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC]
  >> EVAL_TAC )
  >> IF_CASES_TAC
  >- (
  ‘wptr >+ rptr’ by (
    qpat_x_assum ‘fifo_rel (_ :: _) _ _ _’ mp_tac
    THEN rewrite_tac [fifo_rel_def]
    THEN EVAL_TAC
    THEN rw [] )
  >> ‘rptr + 1w <+ wptr ∨ rptr + 1w = wptr’ by (first_x_assum mp_tac THEN blastLib.BBLAST_TAC)
  >- (
    ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (NTAC 3 $ first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
    THEN qpat_x_assum ‘LENGTH ws = _’ mp_tac
    THEN asm_rewrite_tac [listTheory.LENGTH, wordsTheory.n2w_SUC, arithmeticTheory.ADD1]
    THEN disch_then (fn th => REWRITE_TAC [th, wordsTheory.w2n_plus1])
    THEN ‘-(1w :word7) * (((5 :num) >< (0 :num)) ((rptr :word7) + (1w :word7)) :word7) +
          (((5 :num) >< (0 :num)) (wptr :word7) :word7) ≠ (UINT_MAXw :word7)’ by (
      NTAC 4 $ first_x_assum mp_tac >> blastLib.BBLAST_TAC)
    THEN asm_rewrite_tac [wordsTheory.w2n_11]
    THEN NTAC 5 $ first_x_assum mp_tac
    THEN simp [SF WORD_ARITH_ss, SF WORD_EXTRACT_ss, SF WORD_ss]
    THEN blastLib.BBLAST_TAC)
  >- (
    ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (NTAC 3 $ first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
    THEN qpat_x_assum ‘LENGTH ws = _’ mp_tac
    THEN qpat_x_assum ‘rptr + 1w = wptr’ mp_tac
    THEN asm_rewrite_tac [listTheory.LENGTH, arithmeticTheory.ADD1]
    THEN disch_then assume_tac
    THEN disch_then (fn th => REWRITE_TAC [th, wordsTheory.w2n_plus1])
    THEN ‘-(1w :word7) * (((5 :num) >< (0 :num)) ((rptr :word7) + (1w :word7)) :word7) +
          (((5 :num) >< (0 :num)) (wptr :word7) :word7) ≠ (UINT_MAXw :word7)’ by (
      NTAC 4 $ first_x_assum mp_tac >> blastLib.BBLAST_TAC)
    THEN asm_rewrite_tac [wordsTheory.w2n_11]
    THEN NTAC 4 $ first_x_assum mp_tac
    THEN simp [SF WORD_ARITH_ss, SF WORD_EXTRACT_ss, SF WORD_ss]
    THEN blastLib.BBLAST_TAC ) )
  >> ‘(5 >< 0) wptr :word6 <=+ (5 >< 0) rptr : word6’ by (
    qpat_x_assum ‘fifo_rel (_ :: _) _ _ _’ mp_tac
    THEN rewrite_tac [fifo_rel_def]
    THEN EVAL_TAC
    THEN rw [] )
  >> ASM_CASES_TAC “(5 >< 0) (rptr: word7) = 63w: word6”
  >- (
  ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ by (first_x_assum mp_tac >> blastLib.BBLAST_TAC)
  THEN ‘word_bit 6 wptr = word_bit 6 (rptr + 1w)’ by (
    rpt $ qpat_x_assum ‘word_bit _ _ ≠ word_bit _ _’ mp_tac >> blastLib.BBLAST_TAC)
  THEN qpat_x_assum ‘LENGTH ws = _’ mp_tac
  THEN asm_rewrite_tac [listTheory.LENGTH, arithmeticTheory.ADD1]
  THEN disch_then (fn th => REWRITE_TAC [th, wordsTheory.w2n_plus1])
  THEN ‘-(1w :word7) * (((5 :num) >< (0 :num)) ((rptr :word7) + (1w :word7)) :word7) +
        (((5 :num) >< (0 :num)) (wptr :word7) :word7) ≠ (UINT_MAXw :word7)’ by (
    NTAC 4 $ first_x_assum mp_tac >> blastLib.BBLAST_TAC)
  THEN asm_rewrite_tac [wordsTheory.w2n_11]
  THEN qpat_x_assum ‘_ = 63w : word6’ mp_tac
  THEN blastLib.BBLAST_TAC )
  >> ‘word_bit 6 rptr = word_bit 6 (rptr + 1w)’ by (first_x_assum mp_tac THEN blastLib.BBLAST_TAC )
  >> ‘word_bit 6 wptr ≠ word_bit 6 (rptr + 1w)’ by ( fs [] )
  >> ‘(5 >< 0) wptr : word6 ≠ (5 >< 0) (rptr + 1w) : word6’ by (
    qpat_x_assum ‘_ <=+ _’ mp_tac
    THEN qpat_x_assum ‘_ ≠ 63w : word6’ mp_tac
    THEN blastLib.BBLAST_TAC )
  >> qpat_x_assum ‘LENGTH ws = _’ mp_tac
  >> asm_rewrite_tac [arithmeticTheory.ADD1, listTheory.LENGTH]
  >> disch_then (fn th => REWRITE_TAC [th, wordsTheory.w2n_plus1])
  >> ‘-(1w :word7) *
       (((5 :num) >< (0 :num)) ((rptr :word7) + (1w :word7)) :word7) +
      ((((5 :num) >< (0 :num)) (wptr :word7) :word7) + (64w :word7)) ≠
                                                                     (UINT_MAXw :word7)’ by (
    NTAC 5 $ first_x_assum mp_tac >> blastLib.BBLAST_TAC)
  >> asm_rewrite_tac [wordsTheory.w2n_11]
  >> qpat_x_assum ‘_ ≠ 63w : word6’ mp_tac
  >> blastLib.BBLAST_TAC
QED

Theorem word_bit_add_64w:
  (((x : 7 word) + 64w) ' 0 = x ' 0)
  ∧ (((x : 7 word) + 64w) ' 1 = x ' 1)
  ∧ (((x : 7 word) + 64w) ' 2 = x ' 2)
  ∧ (((x : 7 word) + 64w) ' 3 = x ' 3)
  ∧ (((x : 7 word) + 64w) ' 4 = x ' 4)
  ∧ (((x : 7 word) + 64w) ' 5 = x ' 5)
Proof
  blastLib.BBLAST_TAC
QED

(* FIXME: generalise the bitwidth *)        
Theorem length_fifo_max:
  fifo_rel ws (circuit : 6 word -> α) (rptr: 7 word) wptr ⇒ LENGTH ws ≤ 2 ** 6
Proof
  rpt strip_tac
  >> drule length_fifo
  >> disch_then (fn th => REWRITE_TAC [th])
  >> IF_CASES_TAC >- ( EVAL_TAC )
  >> ASM_CASES_TAC “ws : α list = []”
  >- (
  ‘rptr = wptr’ by ( fs [fifo_rel_def])
  >> first_x_assum mp_tac >> blastLib.BBLAST_TAC )
  >> IF_CASES_TAC
  >- (
  ‘w2n $ ((5 >< 0) wptr : 7 word) - ((5 >< 0) rptr : 7 word) ≤ 2 ** 6’
     suffices_by ( simp [SF WORD_ARITH_EQ_ss])
  THEN ‘(5 >< 0) (rptr: 7 word) : 7 word <=+ (5 >< 0) (wptr : 7 word) : 7 word’ by (
    ‘ws = HD ws :: TL ws’ by ( metis_tac [listTheory.LIST_NOT_NIL])
    >> ‘fifo_rel (HD ws :: TL ws) circuit rptr wptr’ by ( metis_tac [] )
    >> fs [fifo_rel_def]
    >> ‘wptr >+ rptr’ by ( fs [] )
    >> first_x_assum mp_tac
    >> qpat_x_assum ‘_ ⇔ _’ mp_tac
    >> blastLib.BBLAST_TAC)
  THEN drule wordsTheory.word_sub_w2n
  THEN disch_then (fn th => REWRITE_TAC [th])
  THEN ‘w2n ((5 >< 0) wptr : 7 word) ≤ 2 ** 6 + w2n ((5 >< 0) rptr : 7 word)’ suffices_by (simp [SF WORD_ARITH_ss])
  THEN ‘2 ** 6 ≤ 2 ** 6 + w2n ((5 >< 0) rptr : 7 word)’ suffices_by (
    assume_tac
    $ SPEC “wptr: 7 word” $ SPEC “0:num” $ SPEC “5:num” $ INST_TYPE [“:α” |-> “:7”, “:β” |-> “:7”]
    wordsTheory.WORD_EXTRACT_LT
    >> first_x_assum mp_tac >> EVAL_TAC >> decide_tac)
  THEN decide_tac)
  >> ‘ws = HD ws :: TL ws’ by ( metis_tac [listTheory.LIST_NOT_NIL])
  >> ‘fifo_rel (HD ws :: TL ws) circuit rptr wptr’ by ( metis_tac [])
  >> fs [fifo_rel_def]
  >> ‘word_bit 6 rptr ≠ word_bit 6 wptr’ by ( rw [] )
  >> first_x_assum drule
  >> disch_tac
  >> ‘w2n ((((5 >< 0) wptr : 7 word) + 64w) - (5 >< 0) rptr : 7 word) ≤ 64’ suffices_by (
    simp [SF WORD_ARITH_EQ_ss])
  >> ‘((5 >< 0) rptr : 7 word) <=+ ((5 >< 0) wptr : 7 word) + 64w’ by (
    blastLib.BBLAST_TAC)
  >> drule wordsTheory.word_sub_w2n
  >> disch_then (fn th => REWRITE_TAC [th])
  >> ‘w2n (((5 >< 0) wptr: 7 word) + 64w) ≤ w2n ((5 >< 0) rptr : 7 word) +64 ’ suffices_by (
    blastLib.BBLAST_TAC)
  >> ‘w2n (((5 >< 0) wptr: 7 word) + 64w) = w2n ((5 >< 0) wptr : 7 word) + 64’ by (
    rewrite_tac [wordsTheory.w2n_def]
    >> EVAL_TAC
    >> rewrite_tac [word_bit_add_64w, GSYM arithmeticTheory.ADD_ASSOC, arithmeticTheory.EQ_ADD_LCANCEL]
    >> blastLib.BBLAST_TAC
    >> EVAL_TAC)
  >> asm_rewrite_tac []
  >> ‘w2n ((5 >< 0) wptr : 7 word) <= w2n ((5 >< 0) rptr : 7 word)’ suffices_by (decide_tac)
  >> rewrite_tac [GSYM wordsTheory.WORD_LS]
  >> qpat_x_assum ‘(5 >< 0) wptr : 6 word <=+ (5 >< 0) rptr : 6 word’ mp_tac
  >> blastLib.BBLAST_TAC
QED

(* FIXME: generalise the bit-width *)        
Theorem fifo_rel_append:
  ∀rptr. fifo_rel (xs ++ ys) (circuit: 6 word -> β) (rptr: 7 word) wptr ⇒
         ∃cptr. fifo_rel xs circuit rptr cptr ∧ fifo_rel ys circuit cptr wptr
Proof
  Induct_on ‘xs’
  >- ( rw [fifo_rel_def, listTheory.APPEND] )
  >> rpt strip_tac
  >> drule length_fifo_max 
  >> disch_tac
  >> fs [fifo_rel_def]
  >> first_x_assum drule
  >> disch_then CHOOSE_TAC
  >> EXISTS_TAC “cptr: 7 word”
  >> ASM_CASES_TAC “xs = [] : 'b list”
  >- (
  ‘cptr = rptr + 1w’ by ( fs [fifo_rel_def] )
  THEN ‘((word_bit (6 :num) (rptr :word7) ⇔ word_bit (6 :num) (cptr :word7)) ⇒ cptr >₊ rptr)’ by (
    asm_rewrite_tac []
    >> assume_tac $ INST [“x: 7 word” |-> “rptr : 7 word”] $ INST_TYPE [“:α” |-> “:7”] word_bit_eq_GT
    >> first_x_assum mp_tac
    >> EVAL_TAC)
  THEN ‘((word_bit (6 :num) rptr ⇎ word_bit (6 :num) cptr) ⇒
         (((5 :num) >< (0 :num)) cptr :word6) <=+ (((5 :num) >< (0 :num)) rptr :word6))’ by (
    asm_rewrite_tac []
    >> simp [SF WORD_EXTRACT_ss]
    >> blastLib.BBLAST_TAC)
  THEN asm_rewrite_tac [])
  >> qsuff_tac ‘((word_bit 6 rptr ⇔ word_bit 6 cptr) ⇒ cptr >₊ rptr)
                ∧ (((word_bit 6 rptr ⇎ word_bit 6 cptr) ⇒ (5 >< 0) cptr : 6 word <=+ (5 >< 0) rptr : 6 word))’
  >- ( rw [] )
  >>  conj_tac
  >> ‘xs = HD xs :: TL xs’ by ( metis_tac [quantHeuristicsTheory.HD_TL_EQ_1])
  >> qpat_assum ‘fifo_rel xs _ _ _ ∧ _’ (fn th => first_assum (fn th2 => STRIP_ASSUME_TAC $ ONCE_REWRITE_RULE [th2] th))
  >> fs [fifo_rel_def]
  >> disch_tac
  >- (
  ASM_CASES_TAC “word_bit 6 ((rptr : 7 word) + 1w) ⇔ word_bit 6 (rptr : 7 word) ”
  >- (
    ‘word_bit 6 (rptr + 1w) ⇔ word_bit 6 cptr’ by ( fs [] )
    THEN first_x_assum drule
    THEN qpat_x_assum ‘word_bit _ (rptr + 1w) ⇔ word_bit _ rptr’ mp_tac
    THEN blastLib.BBLAST_TAC)
  >> ‘rptr = 63w ∨ rptr = 127w’ by (
    qpat_x_assum ‘word_bit 6 (rptr + 1w) ≠ word_bit 6 rptr’ mp_tac
    THEN blastLib.BBLAST_TAC )
  >> ‘word_bit 6 (rptr + 1w) ≠ word_bit 6 cptr’ by ( metis_tac [] )
  >> first_x_assum drule
  >> disch_tac
  >> ‘((5 >< 0) cptr : 6 word) = (5 >< 0) (rptr + 1w)’ by (
    NTAC 3 $ first_x_assum mp_tac >> blastLib.BBLAST_TAC)
  >> qpat_x_assum ‘fifo_rel xs _ _ _’ assume_tac
  >> drule length_fifo
  >> simp [])
  >- (
  ASM_CASES_TAC “word_bit 6 (rptr : 7 word) ⇔ word_bit 6 ((rptr : 7 word) + 1w)”
  >- (
    ‘word_bit 6 (rptr + 1w) ≠ word_bit 6 cptr’ by ( fs [] )
    THEN first_x_assum drule
    THEN ‘((5 >< 0) cptr : 6 word) ≠ ((5 >< 0) (rptr + 1w) : 6 word)’ suffices_by (
      blastLib.BBLAST_TAC)
    THEN spose_not_then assume_tac
    THEN qpat_x_assum ‘fifo_rel xs _ _ _’ assume_tac
    THEN drule length_fifo
    THEN simp [])
  >> ‘cptr >+ rptr + 1w’ by ( metis_tac [] ) 
  >> ‘(5 >< 0) rptr : 6 word = 63w’ by (
    qpat_x_assum ‘word_bit 6 rptr ≠ word_bit 6 (rptr + 1w)’ mp_tac
    THEN blastLib.BBLAST_TAC)
  >> pop_assum mp_tac
  >> blastLib.BBLAST_TAC)
QED

(* TODO: generalise the bit width *)     
Theorem word_helper:
  w2n (((5 >< 0) (wptr : 7 word) : 7 word) + 64w) = w2n ((5 >< 0) (wptr : 7 word) : 7 word) + 64
Proof
  rewrite_tac [wordsTheory.w2n_def]
  >> EVAL_TAC
  >> rewrite_tac [word_bit_add_64w, GSYM arithmeticTheory.ADD_ASSOC, arithmeticTheory.EQ_ADD_LCANCEL]
  >> blastLib.BBLAST_TAC
  >> EVAL_TAC  
QED

Theorem fifo_rel_append_if:
  ∀rptr .
    fifo_rel (xs : α list) (circuit :6 word -> 'a) (rptr :7 word) cptr
    ∧ fifo_rel ys circuit cptr wptr
    ∧ LENGTH xs + LENGTH ys ≤ 2 ** 6
    ⇒ fifo_rel (xs ++ ys) circuit rptr wptr
Proof
  Induct_on ‘xs’ >- (rw [fifo_rel_def])
  >> rpt strip_tac
  >> rw [listTheory.APPEND, fifo_rel_def]
  >- (
  ASM_CASES_TAC “(ys : α list) = []”  >- ( fs [fifo_rel_def] )
  >> ASM_CASES_TAC “word_bit 6 (cptr : 7 word) ⇔
                      word_bit 6 (wptr : 7 word)”
  >- (
    ‘∃y ys'. ys = y :: ys'’ by ( metis_tac [listTheory.LIST_NOT_NIL])
    >> ‘wptr >+ cptr’ by (fs [fifo_rel_def])
    >> ASM_CASES_TAC “word_bit 6 (cptr: 7 word) ⇔ word_bit 6 (rptr: 7 word)”
    >- (
      ‘cptr >+ rptr’ by ( fs [fifo_rel_def])
      >> first_x_assum mp_tac
      >> qpat_x_assum ‘_ >+ _’ mp_tac
      >> rewrite_tac [wordsTheory.WORD_HIGHER]
      >> metis_tac [wordsTheory.WORD_LOWER_TRANS])
    >> ‘F’ by ( metis_tac [length_fifo]))
  >> ‘∃y ys'. ys = y :: ys'’ by ( metis_tac [listTheory.LIST_NOT_NIL])
  >> ‘((5 >< 0) wptr : 6 word) <=+ ((5 >< 0) cptr : 6 word)’
    by ( fs [fifo_rel_def] )
  >> ‘word_bit 6 (rptr : 7 word) ≠ word_bit 6 (cptr : 7 word)’
    by (metis_tac [])
  >> ‘((5 >< 0) cptr : 6 word) ≠ ((5 >< 0) rptr : 6 word)’ by (
    spose_not_then assume_tac
    >> qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ assume_tac
    >> drule length_fifo
    >> disch_then (fn th =>
                     ‘LENGTH (h :: xs) = w2n (64w: 7 word)’ by (metis_tac [th]))
    >> ‘1 ≤ LENGTH (ys)’ by ( fs [])
    >> NTAC 2 $ pop_assum mp_tac
    >> qpat_x_assum ‘_ + _ ≤ 2 ** 6’ mp_tac
    >> EVAL_TAC
    >> decide_tac)
  >> ‘((5 >< 0) cptr : 6 word) <=+ ((5 >< 0) rptr : 6 word)’ by (fs [fifo_rel_def])
  >> ‘((5 >< 0) wptr : 6 word) ≠ ((5 >< 0) cptr : 6 word)’ by (
    spose_not_then assume_tac
    >> drule length_fifo
    >> disch_tac
    >> ‘LENGTH ys = w2n (64w : 7 word)’ by (metis_tac [])
    >> ‘1 + LENGTH xs + w2n (64w: 7 word) ≤ 2 ** 6’
      by (fs [])
    >> pop_assum mp_tac
    >> EVAL_TAC
    >> decide_tac )
  >> ‘LENGTH (h :: xs) ≤ (w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word))’ by (
    drule length_fifo
    >> disch_then (fn th => ‘LENGTH ys = w2n (((5 >< 0) wptr : 7 word) + 64w - ((5 >< 0) cptr : 7 word))’
                     by ( simp [th, SF WORD_ss, SF WORD_ARITH_EQ_ss]))
    >> ‘LENGTH (h :: xs) + w2n (((5 >< 0) wptr : 7 word) + 64w - ((5 >< 0) cptr : 7 word)) ≤ 2 ** 6’
      by ( fs [])
    >> ‘¬ (LENGTH (h :: xs) ≤ 0)’ by ( simp [listTheory.LENGTH])
    >> ‘LENGTH (h :: xs) ≤ 2 ** 6 - w2n (((5 >< 0) wptr : 7 word) + 64w - ((5 >< 0) cptr : 7 word))’
      by ( metis_tac [arithmeticTheory.SUB_LEFT_LESS_EQ])
    >> ‘((5 >< 0) cptr : 7 word) <=+ ((5 >< 0) wptr : 7 word) + 64w’ by (blastLib.BBLAST_TAC)
    >> drule wordsTheory.word_sub_w2n
    >> disch_then (fn th => qpat_x_assum ‘_ ≤ _ - _’ (ASSUME_TAC o REWRITE_RULE [th]))
    >> ‘w2n ((5 >< 0) cptr : 7 word) <= w2n (((5 >< 0) wptr : 7 word) + 64w)’ by ( fs [wordsTheory.WORD_LS])
    >> drule arithmeticTheory.SUB_SUB
    >> disch_then (fn th => qpat_x_assum ‘_ ≤ _ - _’ (ASSUME_TAC o REWRITE_RULE [th]))
    >> pop_assum (ASSUME_TAC o REWRITE_RULE [word_helper, arithmeticTheory.SUB_PLUS])
    >> ‘2 ** 6 + w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word) − 64 =
        w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word)’ by (EVAL_TAC >> decide_tac)
    >> pop_assum (fn th => qpat_x_assum ‘_ ≤ _ ’ (ACCEPT_TAC o REWRITE_RULE [th])))
  >> ‘LENGTH (h :: xs) > (w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word))’ by (
    qpat_x_assum ‘fifo_rel (h :: xs) _ _ _ ’ assume_tac
    >> drule length_fifo
    >> disch_then (fn th => ‘LENGTH (h :: xs) = w2n ((-1w:7 word) * ((5 >< 0) rptr : 7 word) + ((5 >< 0) cptr : 7 word) + 64w)’ by (fs [th]))
    >> ‘LENGTH (h::xs) = w2n (((5 >< 0) cptr : 7 word) + 64w - ((5 >< 0) rptr : 7 word))’ by (
      pop_assum mp_tac >> blastLib.BBLAST_TAC)
    >> ‘((5 >< 0) rptr : 7 word) <=+ ((5 >< 0) cptr : 7 word) + 64w’ by (blastLib.BBLAST_TAC)
    >> drule wordsTheory.word_sub_w2n
    >> disch_then (fn th => qpat_x_assum ‘LENGTH (h :: xs) = _’ (ASSUME_TAC o REWRITE_RULE [th, word_helper]))
    >> ‘w2n ((5 >< 0) cptr : 7 word) =
        w2n (((5 >< 0) wptr : 7 word) + (((5 >< 0) cptr : 7 word) - ((5 >< 0) wptr : 7 word)))’ by (blastLib.BBLAST_TAC)
    >> ‘¬ word_msb ((((5 >< 0) cptr : 7 word) - ((5 >< 0) wptr : 7 word))) ∧ ¬ word_msb ((5 >< 0) wptr : 7 word)’ by (
      qpat_assum ‘(5 >< 0) wptr <=+ (5 >< 0) cptr’ mp_tac >> blastLib.BBLAST_TAC)
    >> dxrule wordsTheory.w2n_add
    >> disch_then dxrule
    >> disch_then (fn th => pop_assum (ASSUME_TAC o REWRITE_RULE [th]))
    >> pop_assum (fn th => pop_assum (ASSUME_TAC o REWRITE_RULE [th]))
    >> ‘w2n (((5 >< 0) cptr : 7 word) - ((5 >< 0) wptr : 7 word)) = w2n ((5 >< 0) cptr : 7 word) -
                                                                    w2n ((5 >< 0) wptr : 7 word)’
      by (  irule wordsTheory.word_sub_w2n
            >> qpat_x_assum ‘(5 >< 0) wptr <=+ (5 >< 0) cptr’ mp_tac
            >> blastLib.BBLAST_TAC)
    >> pop_assum (fn th => pop_assum (ASSUME_TAC o REWRITE_RULE [th]))
    >> ‘w2n ((5 >< 0) rptr : 7 word) ≤ 64’ by (
      ‘64 = w2n (64w : 7 word)’ by (EVAL_TAC)
      >> once_asm_rewrite_tac []
      >> irule $ iffLR wordsTheory.WORD_LS
      >> blastLib.BBLAST_TAC)
    >> drule arithmeticTheory.LESS_EQ_ADD_SUB
    >> disch_then (fn th => qpat_x_assum ‘LENGTH (h :: xs) = _’ (ASSUME_TAC o REWRITE_RULE [th]))
    >> ‘w2n ((5 >< 0) rptr : 7 word) < 64’ by (
      ‘64:num = 2 ** (SUC 5 - 0)’ by EVAL_TAC
      >> once_asm_rewrite_tac []
      >> irule wordsTheory.WORD_EXTRACT_LT)
    >> ‘0 < 64 - w2n ((5 >< 0) rptr : 7 word)’ by ( pop_assum mp_tac >> DECIDE_TAC )
    >> ‘0 < w2n ((5 >< 0) wptr : 7 word) + (64 − w2n ((5 >< 0) rptr : 7 word))’ by (
      pop_assum mp_tac >> DECIDE_TAC)
    >> ‘LENGTH (h :: xs) > (w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word))’ by (
      qpat_x_assum ‘LENGTH (h :: xs) = _’ mp_tac
      >> pop_assum mp_tac
      >> DECIDE_TAC))
  >> DECIDE_TAC)
  >- (
  ASM_CASES_TAC “(ys : α list) = []”
  >- ( ‘cptr = wptr’ by ( fs [fifo_rel_def] ) THEN fs [fifo_rel_def] )
  >> ‘∃y ys'. ys = y :: ys'’ by ( metis_tac [listTheory.LIST_NOT_NIL])
  >> ‘fifo_rel (y :: ys') circuit cptr wptr’ by ( fs [] )
  >> pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def])
  >> ASM_CASES_TAC “word_bit (dimindex (:7) - 1) (cptr : 7 word) ⇔ word_bit (dimindex (:7) - 1) (wptr : 7 word)”
  >- (
    first_x_assum drule
    >> disch_tac
    >> ‘word_bit (dimindex (:7) - 1) rptr ≠ word_bit (dimindex (:7) - 1) cptr’ by ( fs [] )
    >> qpat_assum ‘fifo_rel (h :: xs) _ _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def])
    >> first_x_assum drule
    >> disch_tac
    >> ‘LENGTH ys = w2n ((5 >< 0) wptr : 7 word) - w2n ((5 >< 0) cptr : 7 word)’ by (
      qpat_x_assum ‘fifo_rel ys _ _ _’ assume_tac
      THEN drule length_fifo
      THEN ‘word_bit 6 wptr ⇔ word_bit 6 cptr’ by ( fs [] )
      THEN asm_rewrite_tac [] 
      THEN ‘w2n (-1w * ((5 >< 0) cptr: 7 word) + ((5 >< 0) wptr : 7 word)) = w2n (((5 >< 0) wptr : 7 word) - ((5 >< 0) cptr : 7 word))’
        by (blastLib.BBLAST_TAC)
      THEN pop_assum (fn th => asm_rewrite_tac [th])
      THEN DEP_REWRITE_TAC [wordsTheory.word_sub_w2n]
      THEN qpat_x_assum ‘wptr >+ cptr’ mp_tac
      THEN pop_assum mp_tac
      THEN blastLib.BBLAST_TAC)
    >> ‘((5 >< 0) rptr : 7 word) ≠ ((5 >< 0) cptr : 7 word)’ by (
      spose_not_then assume_tac
      THEN ‘word_bit 6 rptr ≠ word_bit 6 cptr’ by ( fs [] )
      THEN qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ assume_tac
      THEN drule length_fifo
      THEN disch_tac
      THEN ‘LENGTH (h :: xs) = w2n (64w : 7 word)’ by ( fs  [] )
      THEN ‘w2n (64w: 7 word) + LENGTH ys ≤ 2 ** 6’ by ( fs [] )
      THEN ‘LENGTH ys = 0’ by (pop_assum mp_tac >> EVAL_TAC >> DECIDE_TAC)
      THEN ‘F’ by ( fs [] ))
    >> ‘LENGTH (h :: xs) = w2n (((5 >< 0) cptr : 7 word)) + 64 - w2n ((5 >< 0) rptr : 7 word)’
      by (
      qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ assume_tac
      THEN drule length_fifo
      THEN ‘word_bit 6 cptr ≠ word_bit 6 rptr’ by ( fs [] )
      THEN ‘((5 >< 0) cptr : 6 word) ≠ ((5 >< 0) rptr : 6 word)’ by (
        qpat_x_assum ‘(5 >< 0) rptr ≠ (5 >< 0) cptr’ mp_tac >> blastLib.BBLAST_TAC )
      THEN asm_rewrite_tac []
      THEN ‘w2n ((-1w: 7 word) * ((5 >< 0) rptr : 7 word) + (((5 >< 0) cptr : 7 word) + 64w)) =
            w2n ((((5 >< 0) cptr : 7 word) + 64w) - ((5 >< 0) rptr : 7 word))’
        by ( blastLib.BBLAST_TAC )
      THEN pop_assum (fn th => REWRITE_TAC [th])
      THEN ‘w2n (((5 >< 0) cptr : 7 word) + 64w − ((5 >< 0) rptr : 7 word)) =
            w2n (((5 >< 0) cptr : 7 word) + 64w) − w2n ((5 >< 0) rptr : 7 word)’ suffices_by ( simp [word_helper] )
      THEN DEP_REWRITE_TAC [wordsTheory.word_sub_w2n]
      THEN blastLib.BBLAST_TAC)
    >> ‘LENGTH ys ≤ 64 - LENGTH (h :: xs)’ by (
      qpat_x_assum ‘_ + _ ≤ 2 ** 6’ mp_tac THEN EVAL_TAC THEN decide_tac)
    >> pop_assum mp_tac
    >> qpat_assum ‘LENGTH (h :: xs) = _’ (fn th => REWRITE_TAC [th])
    >> ‘w2n ((5 >< 0) rptr : 7 word) ≤ (w2n ((5 >< 0) cptr : 7 word) + 64)’ by (
      rewrite_tac [GSYM word_helper, GSYM wordsTheory.WORD_LS]
      THEN blastLib.BBLAST_TAC )
    >> dxrule arithmeticTheory.SUB_SUB
    >> disch_then (fn th => REWRITE_TAC [th])
    >> ‘64 + w2n ((5 >< 0) rptr: 7 word) − (w2n ((5 >< 0) cptr: 7 word) + 64) =
        w2n ((5 >< 0) rptr : 7 word) - w2n ((5 >< 0) cptr : 7 word)’ by (
      rewrite_tac [SPEC “w2n ((5 >< 0) (cptr : 7 word) : 7 word)” arithmeticTheory.ADD_COMM]
      THEN rewrite_tac [arithmeticTheory.SUB_PLUS]
      THEN rewrite_tac [SPEC “w2n ((5 >< 0) (rptr : 7 word) : 7 word)” $ SPEC “64:num” arithmeticTheory.ADD_COMM]
      THEN ‘64:num ≤ 64:num’ by decide_tac
      THEN drule arithmeticTheory.LESS_EQ_ADD_SUB
      THEN disch_then (fn th => REWRITE_TAC [th])
      THEN EVAL_TAC)
    >> pop_assum (fn th => REWRITE_TAC [th])
    >> qpat_assum ‘LENGTH ys = _’ (fn th => REWRITE_TAC [th])
    >> REWRITE_TAC [arithmeticTheory.LE_SUB_RCANCEL, GSYM wordsTheory.WORD_LS]
    >> qpat_assum ‘wptr >+ cptr’ mp_tac
    >> qpat_assum ‘word_bit _ cptr ⇔ word_bit _ wptr’ mp_tac
    >> blastLib.BBLAST_TAC)
  >> ‘((dimindex (:6) − 1 >< 0) wptr : 6 word) ≤₊ ((dimindex (:6) − 1 >< 0) cptr : 6 word)’ by (
    first_x_assum drule >> simp [] )
  >> ‘word_bit (dimindex (:7) - 1) rptr ⇔ word_bit (dimindex (:7) - 1) cptr’ by (
    qpat_assum ‘word_bit _ cptr ≠ word_bit _ wptr’ mp_tac
    THEN qpat_assum ‘word_bit _ rptr ≠ word_bit _ wptr’ mp_tac
    THEN EVAL_TAC
    THEN metis_tac [])
  >> ‘((5 >< 0) wptr : 6 word) ≠ ((5 >< 0) cptr : 6 word)’ by (
    spose_not_then assume_tac
    THEN qpat_x_assum ‘fifo_rel ys _ _ _’ assume_tac
    THEN drule length_fifo
    THEN ‘word_bit 6 wptr ≠ word_bit 6 cptr’ by (
      qpat_x_assum ‘word_bit _ cptr ≠ word_bit _ wptr’ mp_tac >> EVAL_TAC >> simp [] )
    THEN disch_then (fn th => ‘LENGTH ys = w2n (64w: 7 word)’ by (simp [th]))
    THEN fs [])
  >> ‘LENGTH ys = 64 + w2n (((5 >< 0) wptr : 7 word)) − w2n ((5 >< 0) cptr : 7 word)’
    by (
    qpat_x_assum ‘fifo_rel ys _ _ _’ assume_tac        
    THEN drule length_fifo
    THEN ‘word_bit 6 wptr ≠ word_bit 6 cptr’ by (
      qpat_x_assum ‘word_bit _ cptr ≠ word_bit _ wptr’ mp_tac >> EVAL_TAC >> simp [] )
    THEN disch_then (fn th => ‘LENGTH ys = w2n (-1w * ((5 >< 0) cptr : 7 word) + (((5 >< 0) wptr : 7 word) + 64w))’ by (
                      simp [th]))
    THEN ‘w2n (-1w * ((5 >< 0) cptr : 7 word) + (((5 >< 0) wptr : 7 word) + 64w)) =
          w2n ((((5 >< 0) wptr : 7 word) + 64w) - ((5 >< 0) cptr : 7 word))’
      by (blastLib.BBLAST_TAC)
    THEN pop_assum (fn th => ‘LENGTH ys = w2n ((((5 >< 0) wptr : 7 word) + 64w) - ((5 >< 0) cptr : 7 word))’ by (fs [th]))
    THEN ‘((5 >< 0) cptr : 7 word) <=+ ((5 >< 0) wptr : 7 word) + 64w’ by ( blastLib.BBLAST_TAC )
    THEN dxrule wordsTheory.word_sub_w2n
    THEN fs [word_helper])
  >> ‘LENGTH (h :: xs) ≤ 64 - LENGTH ys’ by (
    qpat_x_assum ‘LENGTH _ + LENGTH _ ≤ 2 ** 6’ mp_tac >> EVAL_TAC >> decide_tac)
  >> ‘LENGTH (h :: xs) ≤ w2n ((5 >< 0) cptr : 7 word) - w2n ((5 >< 0) wptr : 7 word)’ by (
    qpat_x_assum ‘LENGTH (h :: xs) ≤ 64 - _’ mp_tac
    THEN qpat_x_assum ‘LENGTH ys = _’ (fn th => REWRITE_TAC [th])
    THEN ‘w2n ((5 >< 0) cptr : 7 word) ≤ 64 + w2n ((5 >< 0) wptr : 7 word)’ by (
      once_rewrite_tac [arithmeticTheory.ADD_COMM]
      >> rewrite_tac [GSYM word_helper, GSYM wordsTheory.WORD_LS]
      >>blastLib.BBLAST_TAC)
    THEN drule arithmeticTheory.SUB_SUB
    THEN disch_then (fn th => REWRITE_TAC [th, arithmeticTheory.SUB_PLUS])
    THEN decide_tac)
  >> ‘LENGTH (h :: xs) = w2n ((5 >< 0) cptr : 7 word) - w2n ((5 >< 0) rptr : 7 word)’ by (
    qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ assume_tac
    >> drule length_fifo
    >> ‘word_bit 6 cptr ⇔ word_bit 6 rptr’ by ( fs [] )
    >> ‘w2n (-1w * ((5 >< 0) rptr : 7 word) + ((5 >< 0) cptr : 7 word)) =
        w2n (((5 >< 0) cptr : 7 word) - ((5 >< 0) rptr : 7 word))’ by (blastLib.BBLAST_TAC)
    >> asm_rewrite_tac []
    >> DEP_REWRITE_TAC [wordsTheory.word_sub_w2n]
    >> qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def])
    >> first_x_assum drule
    >> qpat_x_assum ‘word_bit _ rptr ⇔ word_bit _ cptr’ mp_tac
    >> EVAL_TAC
    >> blastLib.BBLAST_TAC)
  >> ‘w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) rptr : 7 word) ≤ w2n ((5 >< 0) cptr : 7 word) − w2n ((5 >< 0) wptr : 7 word)’
    by ( fs [] )
  >> pop_assum (ASSUME_TAC o REWRITE_RULE [arithmeticTheory.LE_SUB_LCANCEL, GSYM wordsTheory.WORD_LS])
  >> ‘¬ (((5 >< 0) cptr : 7 word) ≤₊ ((5 >< 0) rptr : 7 word))’ by (
    qpat_assum ‘fifo_rel (h :: xs) _ _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def])
    >> first_x_assum drule
    >> qpat_x_assum ‘word_bit _ rptr ⇔ word_bit _ cptr’ mp_tac
    >> EVAL_TAC >> blastLib.BBLAST_TAC)
  >> fs []
  >> qpat_x_assum ‘_ <=+ _’ mp_tac
  >> blastLib.BBLAST_TAC)
  >- (
  qpat_x_assum ‘fifo_rel (h :: xs) _ _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def])
  >> qpat_x_assum ‘circuit _ = h’ mp_tac
  >> EVAL_TAC )
  >> first_assum irule
  >> ‘LENGTH xs + LENGTH ys ≤ 2 ** 6’ by (
    qpat_x_assum ‘LENGTH _ + LENGTH _ ≤ 2 ** 6’ mp_tac
    >> rewrite_tac [listTheory.LENGTH]                        
    >> decide_tac)
  >> fs [fifo_rel_def]                                                
QED
 
val core_init_tm = add_x_inits “<|fmt_fifo_regfile := K 0w; rx_fifo_regfile := K 0w; |>”

Definition core_init_def:
  core_init fbits = ^core_init_tm
End

Theorem i2c_combs_flat =
        ``procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s'``
          |> SCONV [i2c_core_combs_def, procs_def]
          |> SRULE [i2c_reg_top_comb_1_flat]
          |> (fn thm => foldl (fn (rule, thm) => SRULE [rule |> CONV_RULE COND_RECORD_CONV |> SRULE [SF boolSimps.LET_ss]] thm) thm
                              [fmt_fifo_reset_def, fmt_fifo_rdata_def, fmt_fifo_rready_def, fmt_fifo_empty_def,
                               fmt_fifo_incr_rptr_def, fmt_fifo_counter_rptr_wrap_def,
                               fmt_fifo_counter_rptr_wrap_cnt_def, fmt_fifo_wvalid_def, fmt_fifo_full_def,
                               fmt_fifo_incr_wptr_def, fmt_fifo_wdata_def, fmt_fifo_counter_wptr_wrap_def,
                               fmt_fifo_counter_wptr_wrap_cnt_def, i2c_core_delay_comb_def,
                               i2c_core_curr_delay_comb_def, i2c_core_load_tcount_comb_def,
                               i2c_core_log_start_comb_def, i2c_core_log_stop_comb_def, fmt_fifo_rvalid_def,
                               fmt_fifo_flag_start_before_def, fmt_fifo_flag_stop_after_def,
                               fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_nak_ok_def, fmt_byte_def, req_restart_def,
                               bit_clr_def, bit_decr_def, i2c_core_stretch_en_comb_def, i2c_core_scl_d_comb_def,
                               i2c_core_next_scl_rx_val_comb_def, i2c_core_next_stretch_idle_cnt_def,
                               i2c_core_next_counter_def, i2c_core_byte_clr_comb_def, i2c_core_byte_decr_comb_def,
                               i2c_core_byte_num_comb_def, i2c_core_next_byte_index_comb_def, fifo_depth_def,
                               counter_gt_one_comb_def, i2c_core_next_state_def, i2c_core_read_byte_clr_comb_def,
                               i2c_core_shift_data_en_comb_def, i2c_core_next_sda_rx_val_comb_def,
                               i2c_core_rx_fifo_reset_comb_def, i2c_core_rx_fifo_rdata_comb_def,
                               i2c_core_rx_fifo_rready_comb_def, i2c_core_rx_fifo_empty_comb_def,
                               i2c_core_rx_fifo_incr_rptr_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_comb_def,
                               i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def,
                               i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_wdata_comb_def,
                               i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_incr_wptr_comb_def,
                               i2c_core_rx_fifo_counter_wptr_wrap_comb_def,
                               i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def,
                               hw2reg_intr_state_nak_de_comb_def, next_intr_nak_comb_def,
                               hw2reg_intr_state_nak_d_comb_def,
                               hw2reg_intr_state_cmd_complete_de_comb_def,
                               hw2reg_intr_state_cmd_complete_d_comb_def, next_pend_restart_comb_def,
                               next_trans_started_comb_def, next_bit_index_comb_def, i2c_core_next_read_byte_comb_def])
          |> SRULE [i2c_reg_top_comb_2_flat];

Theorem i2c_ffs_flat =
        ``procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) fext s s'``
          |> SCONV [i2c_core_ffs1_def, procs_def]
          |> (fn thm => foldl (fn (rule, thm) => SRULE [rule |> CONV_RULE COND_RECORD_CONV |> SRULE [SF boolSimps.LET_ss]] thm) thm
                              [i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def, fmt_fifo_rptr_ff_def,
                               fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
                               bit_index_ff_def, pend_restart_ff_def, trans_started_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
                               i2c_core_rx_fifo_regfile_def, i2c_core_ff_def, read_byte_ff_def, scl_rx_val_ff_def, sda_rx_val_ff_def, scl_i_q_ff_def ])
          |> SRULE [i2c_reg_top_ff_flat];

Theorem core_sim_rel_combs:
  core_sim_rel mstate (procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s') ⇔ core_sim_rel mstate s'
Proof
  simp [core_sim_rel_def, i2c_combs_flat]
QED

(* Definition fnum_witness_def:
  (fnum_witness fext (0:num) = bool_to_bit fext.cio_scl_i)
  ∧ (fnum_witness fext (1:num) = bool_to_bit fext.cio_sda_i)
End
 *)

Definition fnum_witness'_def:
  (fnum_witness' cstate fext (0:num) = bool_to_bit fext.cio_scl_i)
  ∧ (fnum_witness' cstate fext (1:num) = bool_to_bit fext.cio_sda_i)
  ∧ (fnum_witness' cstate fext (2:num) = w2n (
       (if cstate.hw2reg.intr_state.fmt_threshold_de then
          cstate.hw2reg.intr_state.fmt_threshold_d
        else cstate.regs.intr_state.fmt_threshold)))
  ∧ (fnum_witness' cstate fext (3:num) = w2n (
       if cstate.hw2reg.intr_state.rx_threshold_de then
         cstate.hw2reg.intr_state.rx_threshold_d
       else cstate.regs.intr_state.rx_threshold))
  ∧ (fnum_witness' cstate fext (4:num) = w2n (
       if cstate.hw2reg.intr_state.fmt_overflow_de then
         cstate.hw2reg.intr_state.fmt_overflow_d
       else cstate.regs.intr_state.fmt_overflow))
  ∧ (fnum_witness' cstate fext (5:num) = w2n (
       if cstate.hw2reg.intr_state.rx_overflow_de then
         cstate.hw2reg.intr_state.rx_overflow_d
       else cstate.regs.intr_state.rx_overflow))
  ∧ (fnum_witness' cstate fext (6:num) = w2n (
       if cstate.hw2reg.intr_state.scl_interference_de then
         cstate.hw2reg.intr_state.scl_interference_d
       else cstate.regs.intr_state.scl_interference))
  ∧ (fnum_witness' cstate fext (7:num) = w2n (
       if cstate.hw2reg.intr_state.sda_interference_de then
         cstate.hw2reg.intr_state.sda_interference_d
       else cstate.regs.intr_state.sda_interference))
  ∧ (fnum_witness' cstate fext (8:num) = w2n (
       if cstate.hw2reg.intr_state.stretch_timeout_de then
         cstate.hw2reg.intr_state.stretch_timeout_d
       else cstate.regs.intr_state.stretch_timeout))
  ∧ (fnum_witness' cstate fext (9:num) = w2n (
       if cstate.hw2reg.intr_state.sda_unstable_de then
         cstate.hw2reg.intr_state.sda_unstable_d
       else cstate.regs.intr_state.sda_unstable))
  ∧ (fnum_witness' cstate fext (10:num) = w2n (
       if cstate.hw2reg.intr_state.tx_stretch_de then
         cstate.hw2reg.intr_state.tx_stretch_d
       else cstate.regs.intr_state.tx_stretch))
  ∧ (fnum_witness' cstate fext (11:num) = w2n (
       if cstate.hw2reg.intr_state.tx_overflow_de then
         cstate.hw2reg.intr_state.tx_overflow_d
       else cstate.regs.intr_state.tx_overflow))
  ∧ (fnum_witness' cstate fext (12:num) = w2n (
       if cstate.hw2reg.intr_state.acq_full_de then
         cstate.hw2reg.intr_state.acq_full_d
       else cstate.regs.intr_state.acq_full))
  ∧ (fnum_witness' cstate fext (13:num) = w2n (
       if cstate.hw2reg.intr_state.unexp_stop_de then
         cstate.hw2reg.intr_state.unexp_stop_d
       else cstate.regs.intr_state.unexp_stop))
  ∧ (fnum_witness' cstate fext (14:num) = w2n (
       if cstate.hw2reg.intr_state.host_timeout_de then
         cstate.hw2reg.intr_state.host_timeout_d
       else cstate.regs.intr_state.host_timeout))
End
        

Theorem i2c_tick_fsm_state:
  i2c_tick notif mstate = INR mstate' ==>
  mstate'.fsm_state =
  (case mstate.fsm_state of
     Idle =>
       if mstate.regs.ctrl.enablehost = 1w ∧ ¬NULL mstate.fmt_fifo then
         Active
       else Idle
   | Active =>
       if ¬NULL mstate.fmt_fifo ∧ word_bit 10 (HD mstate.fmt_fifo) then
         Receiving ReadClockLow
       else if
       (¬NULL mstate.fmt_fifo ∧ word_bit 8 (HD mstate.fmt_fifo)) ∧
       ¬mstate.trans_started
       then
         Starting SetupStart
       else Transmitting ClockLow
   | Transmitting ClockLow =>
       if mstate.counter ≠ 1w then Transmitting ClockLow
       else if mstate.pend_restart then Starting SetupStart
       else Transmitting ClockPulse
   | Transmitting ClockPulse =>
       if mstate.counter ≠ 1w then Transmitting ClockPulse
       else Transmitting HoldBit
   | Transmitting HoldBit =>
       if mstate.counter ≠ 1w then Transmitting HoldBit
       else if mstate.bit_index = 0w then Transmitting ClockLowAck
       else Transmitting ClockLow
   | Transmitting ClockLowAck =>
       if mstate.counter ≠ 1w then Transmitting ClockLowAck
       else Transmitting ClockPulseAck
   | Transmitting ClockPulseAck =>
       if mstate.counter ≠ 1w then Transmitting ClockPulseAck
       else Transmitting HoldDevAck
   | Transmitting HoldDevAck =>
       if mstate.counter ≠ 1w then Transmitting HoldDevAck
       else if ¬NULL mstate.fmt_fifo ∧ word_bit 9 (HD mstate.fmt_fifo) then
         Stopping ClockStop
       else PopFmtFifo
   | Receiving ReadClockLow =>
       if mstate.counter ≠ 1w then Receiving ReadClockLow
       else Receiving ReadClockPulse
   | Receiving ReadClockPulse =>
       if mstate.counter ≠ 1w then Receiving ReadClockPulse
       else Receiving ReadHoldBit
   | Receiving ReadHoldBit =>
       if mstate.counter ≠ 1w then Receiving ReadHoldBit
       else if mstate.bit_index = 0w then Receiving HostClockLowAck
       else Receiving ReadClockLow
   | Receiving HostClockLowAck =>
       if mstate.counter ≠ 1w then Receiving HostClockLowAck
       else Receiving HostClockPulseAck
   | Receiving HostClockPulseAck =>
       if mstate.counter ≠ 1w then Receiving HostClockPulseAck
       else Receiving HostHoldBitAck
   | Receiving HostHoldBitAck =>
       if mstate.counter ≠ 1w then Receiving HostHoldBitAck
       else if
       mstate.byte_index = 1w ∧ ¬NULL mstate.fmt_fifo ∧
       word_bit 9 (HD mstate.fmt_fifo)
       then
         Stopping ClockStop
       else if
       mstate.byte_index = 1w ∧
       (NULL mstate.fmt_fifo ∨ ¬word_bit 9 (HD mstate.fmt_fifo))
       then
         PopFmtFifo
       else Receiving ReadClockLow
   | Starting SetupStart =>
       if mstate.counter ≠ 1w then Starting SetupStart else Starting HoldStart
   | Starting HoldStart =>
       if mstate.counter ≠ 1w then Starting HoldStart else Starting ClockStart
   | Starting ClockStart =>
       if mstate.counter ≠ 1w then Starting ClockStart
       else Transmitting ClockLow
   | Stopping ClockStop =>
       if mstate.counter ≠ 1w then Stopping ClockStop else Stopping SetupStop
   | Stopping SetupStop =>
       if mstate.counter ≠ 1w then Stopping SetupStop else Stopping HoldStop
   | Stopping HoldStop =>
       if mstate.counter ≠ 1w then Stopping HoldStop
       else if mstate.regs.ctrl.enablehost = 0w then Idle
       else PopFmtFifo
   | PopFmtFifo =>
       if mstate.regs.ctrl.enablehost = 0w then Stopping ClockStop
       else if LENGTH mstate.fmt_fifo = 1 then Idle
       else Active)                    
Proof
  simp [i2c_tick_def]
QED

Theorem cheshire_req_unchanged:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  (st_upd st').rx_fifo = st'.rx_fifo /\
  (st_upd st').fmt_fifo = st'.fmt_fifo /\
  (st_upd st').fsm_state = st'.fsm_state /\
  (st_upd st').counter = st'.counter /\
  (st_upd st').pend_restart = st'.pend_restart /\
  (st_upd st').trans_started = st'.trans_started /\
  (st_upd st').bit_index = st'.bit_index /\
  (st_upd st').stretch_idle_cnt = st'.stretch_idle_cnt /\
  (st_upd st').byte_index = st'.byte_index /\
  (st_upd st').read_byte = st'.read_byte /\
  (st_upd st').read_byte_clr = st'.read_byte_clr /\
  (st_upd st').shift_data_en = st'.shift_data_en /\
  (st_upd st').scl_rx_val = st'.scl_rx_val /\
  (st_upd st').sda_rx_val = st'.sda_rx_val
Proof
  disch_tac
  >> dxrule_then strip_assume_tac cheshire_req_INR_cases
  >- simp []
  >- simp []
  >- dxrule_then (fn thm => simp [thm]) i2c_write_st_upd_alt
QED

Theorem if_equality:
  (Q1 = Q2 ∧ R1 = R2) ⇒ (if P then Q1 else R1) = (if P then Q2 else R2)
Proof
  rw []
QED

(*        
Theorem next_state_i2c_core_combs_further = SCONV [i2c_combs_flat] ``(Procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s').next_state``
*)

Theorem encode_fsm_next_state:
  encode_fsm (fsmState_CASE x v v1 f f1 f2 f3 v2) =
  fsmState_CASE x
                (encode_fsm v) 
                (encode_fsm v1)
                (λx. encode_fsm $ f x)
                (λx. encode_fsm $ f1 x)
                (λx. encode_fsm $ f2 x)
                (λx. encode_fsm $ f3 x)
                (encode_fsm v2)
Proof
  Induct_on ‘x’ >> rw [fsmState_case_def]
QED

Theorem encode_fsm_ite:
  encode_fsm (if P then Q else R) = if P then encode_fsm Q else encode_fsm R
Proof
  rw [boolTheory.COND_RAND]
QED

Theorem encode_fsm_txState:
  encode_fsm (txState_CASE x v0 v1 v2 v3 v4 v5) =
  txState_CASE x
               (encode_fsm v0)
               (encode_fsm v1)
               (encode_fsm v2)
               (encode_fsm v3)
               (encode_fsm v4)
               (encode_fsm v5)
Proof
  Induct_on ‘x’ >> rw [txState_case_def]
QED

Theorem encode_fsm_rxState:
  encode_fsm (rxState_CASE x v0 v1 v2 v3 v4 v5) =
  rxState_CASE x
               (encode_fsm v0)
               (encode_fsm v1)
               (encode_fsm v2)
               (encode_fsm v3)
               (encode_fsm v4)
               (encode_fsm v5)
Proof
  Induct_on ‘x’ >> rw [txState_case_def]
QED

Theorem encode_fsm_stopState:
  encode_fsm (stopState_CASE x v0 v1 v2) =
  stopState_CASE x
                 (encode_fsm v0)
                 (encode_fsm v1)
                 (encode_fsm v2)
Proof
  Induct_on ‘x’ >> rw [stopState_case_def]
QED

Theorem encode_fsm_startState:
  encode_fsm (startState_CASE x v0 v1 v2) =
  startState_CASE x
                  (encode_fsm v0)
                  (encode_fsm v1)
                  (encode_fsm v2)
Proof
  Induct_on ‘x’ >> rw [startState_case_def]
QED

Theorem i2c_core_combs_fsm_state:
  (procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s').fsm_state = s'.fsm_state
Proof
  simp [i2c_core_combs_def, procs_def, i2c_combs_flat]
QED

Theorem fifo_rel_null:
  fifo_rel ws circuit rptr wptr ⇒ (NULL ws ⇔ rptr = wptr)
Proof
  Induct_on ‘ws’ >- rw [fifo_rel_def]
  >> rpt strip_tac
  >> drule fifo_rel_not_null
  >> rw []
QED

Theorem fifo_rel_not_null_HD:
  fifo_rel ws (circuit : 'a word -> 'b) rptr wptr ∧ ¬ NULL ws ⇒ HD ws = circuit $ (dimindex (:'a) - 1 >< 0) rptr : 'a word
Proof
  Induct_on ‘ws’
  >> rw [fifo_rel_def]
QED

Theorem i2c_tick_rx_fifo:
  i2c_tick notif mstate = INR mstate' ==>
  mstate'.rx_fifo =
  (let
     rx_fifo =
     if mstate.fsm_state = Receiving ReadHoldBit
        ∧ mstate'.fsm_state = Receiving HostClockLowAck ∧ LENGTH mstate.rx_fifo < 64
     then
       (if notif = SOME (Read rdata_read) ∧ ¬NULL mstate.rx_fifo
        then TL mstate.rx_fifo
        else mstate.rx_fifo) ⧺ [mstate.read_byte]
     else if notif = SOME (Read rdata_read) ∧ ¬NULL mstate.rx_fifo
     then TL mstate.rx_fifo
     else mstate.rx_fifo             
   in
     if mstate.buffered_notif = SOME fifo_ctrl_write ∧ mstate.regs.fifo_ctrl.rxrst = 1w
     then []
     else rx_fifo)
Proof
  simp [i2c_tick_def, fsmState_case_def]
QED

Theorem i2c_tick_fmt_fifo:
  i2c_tick notif mstate = INR mstate' ==>
  mstate'.fmt_fifo =
  (if
  mstate.buffered_notif = SOME fifo_ctrl_write ∧
  mstate.regs.fifo_ctrl.fmtrst = 1w
  then
    []
  else if
  mstate.buffered_notif = SOME fdata_write ∧ LENGTH mstate.fmt_fifo < 64
  then
    SNOC
    (w2w mstate.regs.fdata.fbyte ‖ w2w mstate.regs.fdata.nakok ≪ 12 ‖
         w2w mstate.regs.fdata.rcont ≪ 11 ‖ w2w mstate.regs.fdata.read ≪ 10 ‖
         w2w mstate.regs.fdata.start ≪ 8 ‖ w2w mstate.regs.fdata.stop ≪ 9)
    (if mstate.fsm_state = PopFmtFifo ∧ ¬NULL mstate.fmt_fifo then
       TL mstate.fmt_fifo
     else mstate.fmt_fifo)
  else if mstate.fsm_state = PopFmtFifo ∧ ¬NULL mstate.fmt_fifo then
    TL mstate.fmt_fifo
  else mstate.fmt_fifo)                   
Proof
  simp [i2c_tick_def, fsmState_case_def]
QED

Theorem i2c_tick_counter:
  i2c_tick notif mstate = INR mstate' ==>
  mstate'.counter =
   (if
      mstate.fsm_state ≠ Idle ∧ mstate.counter = 1w ∨
      mstate.fsm_state = PopFmtFifo
    then
      case mstate.fsm_state of
        Idle => 0w
      | Active => 0w
      | Transmitting ClockLow =>
        w2w mstate.regs.timing0.tlow + -1w * w2w mstate.regs.timing3.thd_dat
      | Transmitting ClockPulse =>
        w2w mstate.regs.timing0.thigh + w2w mstate.regs.timing1.t_f +
        w2w mstate.regs.timing1.t_r
      | Transmitting HoldBit =>
        w2w mstate.regs.timing1.t_f + w2w mstate.regs.timing3.thd_dat
      | Transmitting ClockLowAck =>
        w2w mstate.regs.timing0.tlow + -1w * w2w mstate.regs.timing3.thd_dat
      | Transmitting ClockPulseAck =>
        w2w mstate.regs.timing0.thigh + w2w mstate.regs.timing1.t_f +
        w2w mstate.regs.timing1.t_r
      | Transmitting HoldDevAck =>
        w2w mstate.regs.timing1.t_f + w2w mstate.regs.timing3.thd_dat
      | Receiving ReadClockLow =>
        w2w mstate.regs.timing0.tlow + -1w * w2w mstate.regs.timing3.thd_dat
      | Receiving ReadClockPulse =>
        w2w mstate.regs.timing0.thigh + w2w mstate.regs.timing1.t_f +
        w2w mstate.regs.timing1.t_r
      | Receiving ReadHoldBit =>
        w2w mstate.regs.timing1.t_f + w2w mstate.regs.timing3.thd_dat
      | Receiving HostClockLowAck =>
        w2w mstate.regs.timing0.tlow + -1w * w2w mstate.regs.timing3.thd_dat
      | Receiving HostClockPulseAck =>
        w2w mstate.regs.timing0.thigh + w2w mstate.regs.timing1.t_f +
        w2w mstate.regs.timing1.t_r
      | Receiving HostHoldBitAck =>
        w2w mstate.regs.timing1.t_f + w2w mstate.regs.timing3.thd_dat
      | Starting SetupStart =>
        w2w mstate.regs.timing1.t_r + w2w mstate.regs.timing2.tsu_sta
      | Starting HoldStart =>
        w2w mstate.regs.timing1.t_f + w2w mstate.regs.timing2.thd_sta
      | Starting ClockStart => w2w mstate.regs.timing3.thd_dat
      | Stopping ClockStop =>
        w2w mstate.regs.timing0.tlow + w2w mstate.regs.timing1.t_f +
        -1w * w2w mstate.regs.timing3.thd_dat
      | Stopping SetupStop =>
        w2w mstate.regs.timing1.t_r + w2w mstate.regs.timing4.tsu_sto
      | Stopping HoldStop =>
        w2w mstate.regs.timing1.t_r + -1w * w2w mstate.regs.timing2.tsu_sta +
        w2w mstate.regs.timing4.t_buf
      | PopFmtFifo => 0w
    else if mstate.stretch_idle_cnt = 0w then mstate.counter + -1w
    else mstate.counter)                  
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_pend_restart:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.pend_restart ⇔
  ((mstate.regs.ctrl.enablehost = 0w ⇒ ¬mstate.pend_restart) ∧
   (mstate.fsm_state = Starting SetupStart ⇒ mstate.counter ≠ 1w)) ∧
  ((NULL mstate.fmt_fifo ∨ ¬word_bit 10 (HD mstate.fmt_fifo)) ∧
   (¬NULL mstate.fmt_fifo ∧ word_bit 8 (HD mstate.fmt_fifo)) ∧
   mstate.fsm_state = Active ∧ mstate.trans_started ∨ mstate.pend_restart))   
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_trans_started:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.trans_started ⇔
     ((mstate.regs.ctrl.enablehost = 0w ⇒ ¬mstate.trans_started) ∧
      (mstate.fsm_state = Stopping ClockStop ⇒ mstate.counter ≠ 1w)) ∧
     (mstate.fsm_state = Starting SetupStart ∧ mstate.counter = 1w ∨
      mstate.trans_started))
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_regs_intr_state:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.regs.intr_state =
   <|fmt_threshold := n2w (mstate.fnums 2);
     rx_threshold := n2w (mstate.fnums 3);
     fmt_overflow := n2w (mstate.fnums 4);
     rx_overflow := n2w (mstate.fnums 5);
     nak :=
       if
         mstate.fsm_state = Transmitting ClockPulseAck ∧
         (NULL mstate.fmt_fifo ∨ ¬word_bit 12 (HD mstate.fmt_fifo)) ∧
         word_bit 0 (n2w (mstate.fnums 1): 1 word)
       then
         1w
       else mstate.regs.intr_state.nak;
     scl_interference := n2w (mstate.fnums 6);
     sda_interference := n2w (mstate.fnums 7);
     stretch_timeout := n2w (mstate.fnums 8);
     sda_unstable := n2w (mstate.fnums 9);
     cmd_complete :=
       if
         mstate.fsm_state = Stopping HoldStop ∨
         mstate.fsm_state = Starting SetupStart ∧
         (mstate.fsm_state = Starting SetupStart ∧ mstate.counter = 1w) ∧
         mstate.pend_restart
       then
         1w
       else mstate.regs.intr_state.cmd_complete;
     tx_stretch := n2w (mstate.fnums 10);
     tx_overflow := n2w (mstate.fnums 11); acq_full := n2w (mstate.fnums 12);
     unexp_stop := n2w (mstate.fnums 13);
     host_timeout := n2w (mstate.fnums 14)|> )
Proof
  simp [i2c_tick_def]
QED
        

Theorem i2c_tick_bit_index:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.bit_index =
   (if
   (mstate.fsm_state = Transmitting HoldBit ∨
    mstate.fsm_state = Receiving ReadHoldBit) ∧ mstate.counter = 1w ∧
   mstate.bit_index = 0w
   then
     7w
   else if
   (mstate.fsm_state = Transmitting HoldBit ∨
    mstate.fsm_state = Receiving ReadHoldBit) ∧ mstate.counter = 1w ∧
   mstate.bit_index ≠ 0w
   then
     mstate.bit_index + -1w
   else mstate.bit_index))
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_stretch_idle_cnt:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.stretch_idle_cnt =
   (if
   (mstate.fsm_state = Transmitting ClockPulse ∨
    mstate.fsm_state = Transmitting ClockPulseAck ∨
    mstate.fsm_state = Receiving ReadClockPulse ∨
    mstate.fsm_state = Receiving HostClockPulseAck) ∧
   (mstate.fsm_state ≠ Starting ClockStart ∧
    mstate.fsm_state ≠ Transmitting ClockLow ∧
    mstate.fsm_state ≠ Transmitting HoldBit ∧
    mstate.fsm_state ≠ Transmitting ClockLowAck ∧
    mstate.fsm_state ≠ Transmitting HoldDevAck ∧
    mstate.fsm_state ≠ Receiving ReadClockLow ∧
    mstate.fsm_state ≠ Receiving ReadHoldBit ∧
    mstate.fsm_state ≠ Receiving HostClockLowAck ∧
    mstate.fsm_state ≠ Receiving HostHoldBitAck ∧
    mstate.fsm_state ≠ Receiving HostHoldBitAck ∧
    mstate.fsm_state ≠ Stopping ClockStop ∧
    (mstate.fsm_state = Active ⇒
     ¬NULL mstate.fmt_fifo ∧ word_bit 8 (HD mstate.fmt_fifo)) ∧
    (mstate.fsm_state = Active ⇒ ¬mstate.trans_started) ∧
    (mstate.fsm_state = PopFmtFifo ⇒
     ¬NULL mstate.fmt_fifo ∧ word_bit 9 (HD mstate.fmt_fifo))) ∧
   ¬word_bit 0 (n2w (mstate.fnums 0) : 1 word)
   then
     mstate.stretch_idle_cnt + 1w
   else 0w))
Proof
  simp [i2c_tick_def]
QED


Theorem i2c_tick_read_byte:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.read_byte =
   (if
   mstate.fsm_state = Receiving ReadHoldBit ∧ mstate.counter = 1w ∧
   mstate.bit_index = 0w
   then
     0w
   else if
   mstate.fsm_state = Receiving ReadClockPulse ∧ mstate.counter = 1w
   then
     ((6 >< 0) mstate.read_byte: 7 word) @@ (n2w (mstate.fnums 1) : 1 word)
   else mstate.read_byte))
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_scl_rx_val:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.scl_rx_val = ((14 >< 0) mstate.scl_rx_val : 15 word) @@ (n2w (mstate.fnums 0) : 1 word))
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_sda_rx_val:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.sda_rx_val = ((14 >< 0) mstate.sda_rx_val : 15 word) @@ (n2w (mstate.fnums 1) : 1 word))
Proof
  simp [i2c_tick_def]
QED

Theorem i2c_tick_byte_index:
  i2c_tick notif mstate = INR mstate' ==>
  (mstate'.byte_index =
   (if
   mstate.fsm_state = Active ∧ ¬NULL mstate.fmt_fifo ∧
   word_bit 10 (HD mstate.fmt_fifo)
   then
     if ((7 >< 0) (HD mstate.fmt_fifo): 8 word) = 0w then 256w
     else w2w ((7 >< 0) (HD mstate.fmt_fifo): 8 word)
   else if
   mstate.fsm_state = Receiving HostHoldBitAck ∧ mstate.counter = 1w ∧
   mstate.byte_index ≠ 1w
   then
     mstate.byte_index + -1w
   else mstate.byte_index))
Proof
  simp [i2c_tick_def]
QED
        
Theorem mstate_with_fnums:
  ((mstate with fnums := fnums).rx_fifo = mstate.rx_fifo)
∧ ((mstate with fnums := fnums).fsm_state = mstate.fsm_state)
Proof
  simp []
QED

Theorem i2c_circuit_cstep:
  ?s. i2c_circuit fext fbits n = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext n) s s
Proof
  simp [i2c_circuit_def, mk_module_def] >> irule mk_circuit_cstep
QED

Theorem incr_ptr_simplified:
  let
    cstate = i2c_circuit fext fbits n;
  in
    ((if cstate.rx_fifo.counter.rptr_wrap
     then cstate.rx_fifo.counter.rptr_wrap_cnt
     else (cstate.rx_fifo.rptr + 1w))
    =
    cstate.rx_fifo.rptr + 1w)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> REVERSE IF_CASES_TAC
  >- ( simp [] )
  >> qpat_x_assum ‘cstate.rx_fifo.counter.rptr_wrap’ mp_tac
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> rpt strip_tac
  >> qpat_x_assum ‘_ = 63w’ mp_tac
  >> IF_CASES_TAC
  >> (ntac 2 $ pop_assum mp_tac >> blastLib.BBLAST_TAC)
QED

Theorem fmt_incr_rptr_simplified:
  let
    cstate = i2c_circuit fext fbits n;
  in
    ((if cstate.fmt_fifo.counter2.rptr_wrap
     then cstate.fmt_fifo.counter2.rptr_wrap_cnt
     else (cstate.fmt_fifo.rptr + 1w))
    =
    cstate.fmt_fifo.rptr + 1w)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> REVERSE IF_CASES_TAC
  >- ( simp [] )
  >> qpat_x_assum ‘cstate.fmt_fifo.counter2.rptr_wrap’ mp_tac
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> rpt strip_tac
  >> qpat_x_assum ‘_ = 63w’ mp_tac
  >> IF_CASES_TAC
  >> (ntac 2 $ pop_assum mp_tac >> blastLib.BBLAST_TAC)
QED

Theorem incr_wptr_simplified:
  let
    cstate = i2c_circuit fext fbits n;
  in
    ((if cstate.rx_fifo.counter.wptr_wrap
     then cstate.rx_fifo.counter.wptr_wrap_cnt
     else (cstate.rx_fifo.wptr + 1w))
    =
    cstate.rx_fifo.wptr + 1w)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> REVERSE IF_CASES_TAC
  >- ( simp [] )
  >> qpat_x_assum ‘cstate.rx_fifo.counter.wptr_wrap’ mp_tac
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> rpt strip_tac
  >> qpat_x_assum ‘_ = 63w’ mp_tac
  >> IF_CASES_TAC
  >> (ntac 2 $ pop_assum mp_tac >> blastLib.BBLAST_TAC)
QED

Theorem fmt_incr_wptr_simplified:
  let
    cstate = i2c_circuit fext fbits n;
  in
    ((if cstate.fmt_fifo.counter2.wptr_wrap
     then cstate.fmt_fifo.counter2.wptr_wrap_cnt
     else (cstate.fmt_fifo.wptr + 1w))
    =
    cstate.fmt_fifo.wptr + 1w)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> REVERSE IF_CASES_TAC
  >- ( simp [] )
  >> qpat_x_assum ‘cstate.fmt_fifo.counter2.wptr_wrap’ mp_tac
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> rpt strip_tac
  >> qpat_x_assum ‘_ = 63w’ mp_tac
  >> IF_CASES_TAC
  >> (ntac 2 $ pop_assum mp_tac >> blastLib.BBLAST_TAC)
QED

Theorem core_sim_rel_relates_seq_only:
  ∀s.
    (i2c_circuit fext fbits n =
         procs
           ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2])
           (fext n) s s)
    ∧ core_sim_rel mstate $ i2c_circuit fext fbits n
    ⇒  ( (encode_fsm mstate.fsm_state  = s.fsm_state)
       ∧ (mstate.bit_index = s.bit_index)
       ∧ (mstate.counter = s.counter)
       ∧ (mstate.regs = s.regs)
       )
Proof
  rpt strip_tac
  >> ‘(i2c_circuit fext fbits n).fsm_state = s.fsm_state
      ∧ (i2c_circuit fext fbits n).bit_index = s.bit_index
      ∧ (i2c_circuit fext fbits n).counter = s.counter
      ∧ (i2c_circuit fext fbits n).regs = s.regs’ by (
    asm_rewrite_tac [] >> simp [i2c_combs_flat])
  >> fs [core_sim_rel_def]
QED
        
Theorem rx_fifo_wvalid_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    core_sim_rel mstate cstate
    ∧ mstate.fsm_state = Receiving ReadHoldBit
    ∧ mstate.bit_index = 0w
    ∧ mstate.counter = 1w
    ⇒ cstate.rx_fifo.wvalid
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> drule core_sim_rel_relates_seq_only
  >> ‘core_sim_rel mstate (i2c_circuit fext fbits n)’ by ( simp [Abbr ‘cstate’])
  >> disch_then drule
  >> simp [Abbr ‘cstate’, i2c_combs_flat, encode_fsm_def]
QED

Theorem incr_wptr_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    LENGTH mstate.rx_fifo < 64
    ∧ core_sim_rel mstate cstate
    ∧ mstate.fsm_state = Receiving ReadHoldBit
    ∧ mstate.bit_index = 0w
    ∧ mstate.counter = 1w
    ⇒ cstate.rx_fifo.incr_wptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> drule_all core_sim_rel_relates_seq_only
  >> ‘(((5 >< 0) s.rx_fifo.wptr : 6 word) = ((5 >< 0) s.rx_fifo.rptr : 6 word)⇒
                 (word_bit 6 s.rx_fifo.wptr ⇔ word_bit 6 s.rx_fifo.rptr))’
    suffices_by (simp [encode_fsm_def])
  >> qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o REWRITE_RULE [core_sim_rel_def])
  >> pop_assum mp_tac
  >> asm_rewrite_tac []
  >> simp [i2c_combs_flat]
  >> disch_tac                
  >> ASM_CASES_TAC “mstate.rx_fifo : word8 list = []”
  >- (
     ‘s.rx_fifo.rptr = s.rx_fifo.wptr’ by ( fs [fifo_rel_def])
     >> pop_assum mp_tac >> blastLib.BBLAST_TAC)
  >> spose_not_then strip_assume_tac
  >> drule length_fifo
  >> simp []
QED

(* FIXME : THIS PROOF CAN BE SHORTENED BY USING THE THEOREM length_fifo_max *)        
Theorem not_incr_wptr:
  let
    cstate = i2c_circuit fext fbits n;
  in
    core_sim_rel mstate cstate
    ∧ ¬(LENGTH mstate.rx_fifo < 64
        ∧ mstate.fsm_state = Receiving ReadHoldBit
        ∧ mstate.bit_index = 0w
        ∧ mstate.counter = 1w)
    ⇒ ¬ cstate.rx_fifo.incr_wptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> drule_all core_sim_rel_relates_seq_only
  >> rpt $ disch_then STRIP_ASSUME_TAC
  >> ‘mstate.fsm_state = Receiving ReadHoldBit’ by (
    Cases_on ‘mstate.fsm_state’
    >> TRY $ Cases_on ‘t’
    >> TRY $ Cases_on ‘r’
    >> TRY $ Cases_on ‘s'’
    >> fs [encode_fsm_def])
  >> ‘mstate.bit_index = 0w ∧ mstate.counter = 1w’ by ( fs [])
  >> ‘¬ (LENGTH mstate.rx_fifo < 64)’ by ( fs [])
  >> ‘LENGTH mstate.rx_fifo >= 64’ by ( decide_tac )
  >> qpat_x_assum ‘core_sim_rel _ _’ (assume_tac o CONJUNCT1 o REWRITE_RULE [core_sim_rel_def])
  >> once_rewrite_tac [boolTheory.CONJ_SYM]
  >> spose_not_then strip_assume_tac
  >> drule length_fifo
  >> IF_CASES_TAC
  >- (
     ntac 2 $ pop_assum mp_tac
     >> simp [i2c_combs_flat]
     >> rpt strip_tac
     >> first_x_assum drule
     >> metis_tac [])
  >> IF_CASES_TAC
  >- (
     simp [i2c_combs_flat, SF WORD_ARITH_EQ_ss]
     >> ‘-1w * ((5 >< 0) s.rx_fifo.rptr : 7 word) + ((5 >< 0) s.rx_fifo.wptr: 7 word) =
         ((5 >< 0) s.rx_fifo.wptr: 7 word) - ((5 >< 0) s.rx_fifo.rptr : 7 word)’
         by ( simp [SF WORD_ARITH_EQ_ss])
     >> pop_assum (fn th => REWRITE_TAC [th])
     >> ‘0w ≤ ((5 >< 0) s.rx_fifo.wptr: 7 word) - ((5 >< 0) s.rx_fifo.rptr : 7 word) ∧
         ((5 >< 0) s.rx_fifo.wptr: 7 word) - ((5 >< 0) s.rx_fifo.rptr : 7 word) <= ((5 >< 0) s.rx_fifo.wptr: 7 word)’ by (
       irule wordsTheory.WORD_SUB_LE
       >> REVERSE conj_tac
       >- ( blastLib.BBLAST_TAC )                
       >> ‘mstate.rx_fifo ≠ []’ by (
         irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
       >> dxrule $ iffLR listTheory.LIST_NOT_NIL
       >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))          
       >> gvs [fifo_rel_def, i2c_combs_flat]
       >> qpat_x_assum ‘_ >+ _’ mp_tac
       >> qpat_x_assum ‘word_bit _ _ ⇔ word_bit _ _’ mp_tac
       >> blastLib.BBLAST_TAC)
     >> ‘w2n (((5 >< 0) s.rx_fifo.wptr: 7 word) - ((5 >< 0) s.rx_fifo.rptr : 7 word)) ≤ w2n ((5 >< 0) s.rx_fifo.wptr: 7 word)’ by (
       irule $ iffLR wordsTheory.WORD_LS
       >> ntac 2 $ pop_assum mp_tac
       >> blastLib.BBLAST_TAC)
     >> ‘w2n ((5 >< 0) s.rx_fifo.wptr: 7 word) ≤ w2n (INT_MAXw : 7 word)’ by (
       irule $ iffLR wordsTheory.WORD_LS
       >> blastLib.BBLAST_TAC)
     >> ‘w2n (((5 >< 0) s.rx_fifo.wptr: 7 word) - ((5 >< 0) s.rx_fifo.rptr : 7 word)) ≤ w2n (INT_MAXw : 7 word)’ by (decide_tac)
     >> pop_assum mp_tac
     >> qpat_x_assum ‘LENGTH _ >= 64’ mp_tac
     >> EVAL_TAC
     >> decide_tac)
  >> ‘(-1w * ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr: 7 word) + (((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.wptr : 7 word) + 64w)) =
      (((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.wptr : 7 word) + 64w) - ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr : 7 word)’ by (
      simp [SF WORD_ARITH_EQ_ss])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘w2n ((((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.wptr : 7 word) + 64w) - ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr : 7 word)) = w2n (((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.wptr : 7 word) + 64w) - w2n ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr : 7 word)’ by (
    irule wordsTheory.word_sub_w2n
    >> blastLib.BBLAST_TAC)
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> rewrite_tac [word_helper]
  >> once_rewrite_tac [arithmeticTheory.ADD_SYM]
  >> DEP_REWRITE_TAC [GSYM arithmeticTheory.SUB_SUB]
  >> conj_tac
  >- (
  irule $ iffLR wordsTheory.WORD_LS
  >> ‘mstate.rx_fifo ≠ []’ by (
    irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
  >> dxrule $ iffLR listTheory.LIST_NOT_NIL
  >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))
  >> pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def, EVAL “dimindex (:7) - 1”, EVAL “dimindex (:6) - 1”])
  >> qpat_x_assum ‘word_bit 6 (i2c_circuit fext fbits n).rx_fifo.wptr ⇎ word_bit 6 (i2c_circuit fext fbits n).rx_fifo.rptr’ (fn th =>
     ‘word_bit 6 (i2c_circuit fext fbits n).rx_fifo.rptr ⇎ word_bit 6 (i2c_circuit fext fbits n).rx_fifo.wptr’ by (simp [th]))
  >> first_x_assum drule                            
  >> blastLib.BBLAST_TAC
  )
  >> ‘64 - (w2n ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr: 7 word) − w2n ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.wptr: 7 word)) < 64’ suffices_by decide_tac
  >> irule arithmeticTheory.SUB_LESS
  >> REVERSE $ CONJ_TAC                                             
  >- (
  irule arithmeticTheory.LESS_EQ_TRANS
  >> EXISTS_TAC “w2n ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr: 7 word)”
  >> CONJ_TAC >- ( simp [arithmeticTheory.SUB_LESS_EQ] )
  >> ‘w2n ((5 >< 0) (i2c_circuit fext fbits n).rx_fifo.rptr: 7 word) ≤ 63’ suffices_by decide_tac
  >> ‘63 = w2n (INT_MAXw : 7 word)’ by EVAL_TAC
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> irule $ iffLR wordsTheory.WORD_LS
  >> blastLib.BBLAST_TAC              
  )
  >> irule $ iffLR arithmeticTheory.SUB_LESS_0
  >> irule $ iffLR wordsTheory.WORD_LO
  >> ‘mstate.rx_fifo ≠ []’ by (
    irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
  >> dxrule $ iffLR listTheory.LIST_NOT_NIL
  >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))
  >> pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def, EVAL “dimindex (:7) - 1”, EVAL “dimindex (:6) - 1”])
  >> qpat_x_assum ‘word_bit 6 (i2c_circuit fext fbits n).rx_fifo.wptr ⇎ word_bit 6 (i2c_circuit fext fbits n).rx_fifo.rptr’ (fn th =>
     ‘word_bit 6 (i2c_circuit fext fbits n).rx_fifo.rptr ⇎ word_bit 6 (i2c_circuit fext fbits n).rx_fifo.wptr’ by (simp [th]))
  >> first_x_assum drule                            
  >> gvs [i2c_combs_flat]
  >> qpat_x_assum ‘(_ >< _) _ ≠ _’mp_tac
  >> blastLib.BBLAST_TAC
QED

Theorem fmt_not_incr_wptr:
  let
    cstate = i2c_circuit fext fbits n;
  in
    core_sim_rel mstate cstate
    ∧ i2c_notif_rel mstate.buffered_notif cstate.reg2hw
    ∧ (¬ (LENGTH mstate.fmt_fifo < 64) ∨ mstate.buffered_notif ≠ SOME fdata_write)
    ==> ¬ cstate.fmt_fifo.incr_wptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >- (
  qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [core_sim_rel_def])
  >> drule length_fifo_max
  >> disch_then $ ASSUME_TAC o REWRITE_RULE [EVAL “(2:num) ** (6:num)”]
  >> ‘LENGTH mstate.fmt_fifo = 64’ by (decide_tac)
  >> DISJ1_TAC
  >> drule length_fifo
  >> IF_CASES_TAC
  >- (
     ntac 2 $ pop_assum mp_tac
     >> simp [i2c_combs_flat]
     >> rpt strip_tac
     >> first_x_assum drule
     >> metis_tac [])
  >> IF_CASES_TAC
  >- (
     simp [i2c_combs_flat, SF WORD_ARITH_EQ_ss]
     >> ‘-1w * ((5 >< 0) s.fmt_fifo.rptr : 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word) =
         ((5 >< 0) s.fmt_fifo.wptr: 7 word) - ((5 >< 0) s.fmt_fifo.rptr : 7 word)’
         by ( simp [SF WORD_ARITH_EQ_ss])
     >> pop_assum (fn th => REWRITE_TAC [th])
     >> ‘0w ≤ ((5 >< 0) s.fmt_fifo.wptr: 7 word) - ((5 >< 0) s.fmt_fifo.rptr : 7 word) ∧
         ((5 >< 0) s.fmt_fifo.wptr: 7 word) - ((5 >< 0) s.fmt_fifo.rptr : 7 word) <= ((5 >< 0) s.fmt_fifo.wptr: 7 word)’ by (
       irule wordsTheory.WORD_SUB_LE
       >> REVERSE conj_tac
       >- ( blastLib.BBLAST_TAC )                
       >> ‘mstate.fmt_fifo ≠ []’ by (
         irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
       >> dxrule $ iffLR listTheory.LIST_NOT_NIL
       >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))          
       >> gvs [fifo_rel_def, i2c_combs_flat]
       >> qpat_x_assum ‘_ >+ _’ mp_tac
       >> qpat_x_assum ‘word_bit _ _ ⇔ word_bit _ _’ mp_tac
       >> blastLib.BBLAST_TAC)
     >> ‘w2n (((5 >< 0) s.fmt_fifo.wptr: 7 word) - ((5 >< 0) s.fmt_fifo.rptr : 7 word)) ≤ w2n ((5 >< 0) s.fmt_fifo.wptr: 7 word)’ by (
       irule $ iffLR wordsTheory.WORD_LS
       >> ntac 2 $ pop_assum mp_tac
       >> blastLib.BBLAST_TAC)
     >> ‘w2n ((5 >< 0) s.fmt_fifo.wptr: 7 word) ≤ w2n (INT_MAXw : 7 word)’ by (
       irule $ iffLR wordsTheory.WORD_LS
       >> blastLib.BBLAST_TAC)
     >> ‘w2n (((5 >< 0) s.fmt_fifo.wptr: 7 word) - ((5 >< 0) s.fmt_fifo.rptr : 7 word)) ≤ w2n (INT_MAXw : 7 word)’ by (decide_tac)
     >> disch_tac
     >> spose_not_then (fn _ => ALL_TAC)
     >> ntac 3 $ pop_assum mp_tac
     >> REWRITE_TAC [EVAL “w2n (INT_MAXw: 7 word)”]
     >> decide_tac)
  >> ‘(-1w * ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr: 7 word) + (((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.wptr : 7 word) + 64w)) =
      (((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.wptr : 7 word) + 64w) - ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr : 7 word)’ by (
      simp [SF WORD_ARITH_EQ_ss])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘w2n ((((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.wptr : 7 word) + 64w) - ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr : 7 word)) = w2n (((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.wptr : 7 word) + 64w) - w2n ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr : 7 word)’ by (
    irule wordsTheory.word_sub_w2n
    >> blastLib.BBLAST_TAC)
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> rewrite_tac [word_helper]
  >> once_rewrite_tac [arithmeticTheory.ADD_SYM]
  >> DEP_REWRITE_TAC [GSYM arithmeticTheory.SUB_SUB]
  >> conj_tac
  >- (
  irule $ iffLR wordsTheory.WORD_LS
  >> ‘mstate.fmt_fifo ≠ []’ by (
    irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
  >> dxrule $ iffLR listTheory.LIST_NOT_NIL
  >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))
  >> pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def, EVAL “dimindex (:7) - 1”, EVAL “dimindex (:6) - 1”])
  >> qpat_x_assum ‘word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.wptr ⇎ word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.rptr’ (fn th =>
     ‘word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.rptr ⇎ word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.wptr’ by (simp [th]))
  >> first_x_assum drule                            
  >> blastLib.BBLAST_TAC
    )
  >> disch_tac
  >> spose_not_then (fn _ => ALL_TAC)
  >> pop_assum mp_tac
  >> ‘64 - (w2n ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr: 7 word) − w2n ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.wptr: 7 word)) < 64’ suffices_by decide_tac
  >> irule arithmeticTheory.SUB_LESS
  >> REVERSE $ CONJ_TAC                                             
  >- (
  irule arithmeticTheory.LESS_EQ_TRANS
  >> EXISTS_TAC “w2n ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr: 7 word)”
  >> CONJ_TAC >- ( simp [arithmeticTheory.SUB_LESS_EQ] )
  >> ‘w2n ((5 >< 0) (i2c_circuit fext fbits n).fmt_fifo.rptr: 7 word) ≤ 63’ suffices_by decide_tac
  >> ‘63 = w2n (INT_MAXw : 7 word)’ by EVAL_TAC
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> irule $ iffLR wordsTheory.WORD_LS
  >> blastLib.BBLAST_TAC              
  )
  >> irule $ iffLR arithmeticTheory.SUB_LESS_0
  >> irule $ iffLR wordsTheory.WORD_LO
  >> ‘mstate.fmt_fifo ≠ []’ by (
    irule $ iffRL listTheory.NOT_NIL_EQ_LENGTH_NOT_0 >> decide_tac)
  >> dxrule $ iffLR listTheory.LIST_NOT_NIL
  >> disch_then (fn th => qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))
  >> pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [fifo_rel_def, EVAL “dimindex (:7) - 1”, EVAL “dimindex (:6) - 1”])
  >> qpat_x_assum ‘word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.wptr ⇎ word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.rptr’ (fn th =>
     ‘word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.rptr ⇎ word_bit 6 (i2c_circuit fext fbits n).fmt_fifo.wptr’ by (simp [th]))
  >> first_x_assum drule                            
  >> gvs [i2c_combs_flat]
  >> qpat_x_assum ‘(_ >< _) _ ≠ _’mp_tac
  >> blastLib.BBLAST_TAC
  )
  >> DISJ2_TAC
  >> gvs [i2c_notif_rel_def, i2c_combs_flat]
QED

        
Theorem incr_ptr_related:
  let
    cstate = i2c_circuit fext fbits n;
    req_c = reg_req_decode (fext n).reg_req_i
  in
    ¬ NULL mstate.rx_fifo
    ∧ core_sim_rel mstate cstate
    ∧ i2c_hwext_notif_rel notif req_c                         
    ∧ notif = SOME (Read rdata_read)
    ==> cstate.rx_fifo.incr_rptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> ‘s.rx_fifo.rptr ≠ s.rx_fifo.wptr’ by (
    ‘mstate.rx_fifo ≠ []’ by (fs [rich_listTheory.NULL_EQ_NIL])
    >> pop_assum (assume_tac o REWRITE_RULE [listTheory.LIST_NOT_NIL])
    >> qpat_assum ‘i2c_circuit fext fbits n = _’ (fn th =>
       qpat_x_assum ‘core_sim_rel _ _’ (assume_tac o REWRITE_RULE [th]))
    >> pop_assum (assume_tac o CONJUNCT1 o REWRITE_RULE [core_sim_rel_def])
    >> qpat_x_assum ‘mstate.rx_fifo = _’ (fn th =>
         qpat_x_assum ‘fifo_rel _ _ _ _’ (assume_tac o ONCE_REWRITE_RULE [th]))
    >> fs [fifo_rel_def, i2c_combs_flat]
    >> qpat_x_assum ‘_ ⇒ _ >+ _’ mp_tac
    >> qpat_x_assum ‘_ ⇒ _ <=+ _’ mp_tac
    >> blastLib.BBLAST_TAC)
  >> fs [i2c_hwext_notif_rel_def]
QED

Theorem fmt_incr_rptr_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    ¬ NULL mstate.fmt_fifo
    ∧ core_sim_rel mstate cstate
    ∧ mstate.fsm_state = PopFmtFifo
    ==> cstate.fmt_fifo.incr_rptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> ‘s.fsm_state = 20w’ by (
    qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [core_sim_rel_def])
    >> gvs [i2c_combs_flat, encode_fsm_def])
  >> ‘s.fmt_fifo.rptr ≠ s.fmt_fifo.wptr’ suffices_by ( simp [] )
  >> ‘mstate.fmt_fifo = HD mstate.fmt_fifo :: TL mstate.fmt_fifo’ by (
    metis_tac [listTheory.LIST_NOT_NIL, rich_listTheory.NULL_EQ_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> pop_assum mp_tac
  >> once_asm_rewrite_tac []
  >> simp [i2c_combs_flat, fifo_rel_def]
  >> disch_then STRIP_ASSUME_TAC
  >> ASM_CASES_TAC “(word_bit 6 s.fmt_fifo.rptr ⇔ word_bit 6 s.fmt_fifo.wptr)”
  >> first_x_assum drule
  >> pop_assum mp_tac
  >> blastLib.BBLAST_TAC
QED
        
Theorem fmt_incr_wptr_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    LENGTH mstate.fmt_fifo < 64 
    ∧ core_sim_rel mstate cstate
    ∧ i2c_notif_rel mstate.buffered_notif cstate.reg2hw
    ∧ mstate.buffered_notif = SOME fdata_write
    ==> cstate.fmt_fifo.incr_wptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> ‘s.reg2hw.fdata.fbyte_qe ∧ s.reg2hw.fdata.start_qe ∧
      s.reg2hw.fdata.stop_qe ∧ s.reg2hw.fdata.read_qe ∧
      s.reg2hw.fdata.rcont_qe ∧ s.reg2hw.fdata.nakok_qe’ by (
    gvs [i2c_combs_flat, i2c_notif_rel_def])
  >> ‘((5 >< 0) s.fmt_fifo.wptr : 6 word) = ((5 >< 0) s.fmt_fifo.rptr: 6 word) ⇒
       (word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr)’
    suffices_by (simp [])
  >> ASM_CASES_TAC “mstate.fmt_fifo = []”                      
  >- (
  qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> gvs [fifo_rel_def, i2c_combs_flat]
  )
  >> qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> ‘mstate.fmt_fifo = HD mstate.fmt_fifo :: TL mstate.fmt_fifo’ by ( metis_tac [listTheory.LIST_NOT_NIL])
  >> qpat_assum ‘fifo_rel _ _ _ _ ’ mp_tac
  >> qpat_x_assum ‘mstate.fmt_fifo = _’ (fn th => once_rewrite_tac [th])
  >> simp [fifo_rel_def, i2c_combs_flat]
  >> disch_then STRIP_ASSUME_TAC
  >> disch_tac
  >> spose_not_then (ASSUME_TAC o GSYM)
  >> rev_drule length_fifo
  >> simp [i2c_combs_flat]        
QED

Theorem no_incr_rptr:
  let
    cstate = i2c_circuit fext fbits n;
    req_c = reg_req_decode (fext n).reg_req_i
  in
      core_sim_rel mstate cstate
    ∧ i2c_hwext_notif_rel notif req_c                         
    ∧ ¬ (notif = SOME (Read rdata_read) ∧ ¬ NULL mstate.rx_fifo)
    ⇒ ¬cstate.rx_fifo.incr_rptr
Proof
  LET_ELIM_TAC
  >> qpat_x_assum ‘¬ _’ (assume_tac o SRULE [SF boolSimps.BOOL_ss])
  >> ASM_CASES_TAC “notif = SOME (Read rdata_read)”                  
  >| [‘mstate.rx_fifo = []’ by (fs [rich_listTheory.NULL_EQ_NIL])
      >> ‘cstate.rx_fifo.rptr = cstate.rx_fifo.wptr’ by (
        fs [core_sim_rel_def, fifo_rel_def])
      , ALL_TAC]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> fs [Abbr ‘cstate’, i2c_combs_flat, i2c_hwext_notif_rel_def]
QED

Theorem fmt_no_incr_rptr:
  let
    cstate = i2c_circuit fext fbits n;
  in
    core_sim_rel mstate cstate ∧ (NULL mstate.fmt_fifo ∨ mstate.fsm_state ≠ PopFmtFifo)
    ==> ¬ cstate.fmt_fifo.incr_rptr
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >- (
  ‘mstate.fmt_fifo = []’ by ( fs [rich_listTheory.NULL_EQ_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> gvs [fifo_rel_def, i2c_combs_flat]
  )
  >> disch_tac
  >> qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [core_sim_rel_def])
  >> ‘encode_fsm mstate.fsm_state = s.fsm_state’ by ( fs [i2c_combs_flat])
  >> Cases_on ‘mstate.fsm_state’
  >> TRY $ Cases_on ‘t’
  >> TRY $ Cases_on ‘r’
  >> TRY $ Cases_on ‘s'’
  >> gvs [encode_fsm_def]
QED

Theorem reset_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    i2c_notif_rel mstate.buffered_notif cstate.reg2hw
    ∧ mstate.regs = cstate.regs
    ⇒ (((mstate.buffered_notif = SOME fifo_ctrl_write) ∧ mstate.regs.fifo_ctrl.rxrst = 1w)
       ⇔ cstate.rx_fifo.reset)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> ‘cstate.rx_fifo.reset ⇔ word_bit 0 s.regs.fifo_ctrl.rxrst ∧ s.reg2hw.fifo_ctrl.rxrst_qe’ by (
    simp [Abbr ‘cstate’, i2c_combs_flat])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘(mstate.buffered_notif = SOME fifo_ctrl_write ⇔ s.reg2hw.fifo_ctrl.rxrst_qe )
      ∧ ((mstate.regs.fifo_ctrl.rxrst = 1w) ⇔ word_bit 0 s.regs.fifo_ctrl.rxrst )’ suffices_by (metis_tac [])
  >> conj_tac
  >- (
     ‘cstate.reg2hw.fifo_ctrl.rxrst_qe = s.reg2hw.fifo_ctrl.rxrst_qe’ by (simp [Abbr ‘cstate’, i2c_combs_flat])
     >> qpat_x_assum ‘i2c_notif_rel _ _’ (ASSUME_TAC o REWRITE_RULE [i2cRegsCommTheory.i2c_notif_rel_def])
     >> fs [])
  >> ‘cstate.regs.fifo_ctrl.rxrst = s.regs.fifo_ctrl.rxrst’ by (simp [Abbr ‘cstate’, i2c_combs_flat])
  >> simp [SF WORD_EXTRACT_ss]       
QED

Theorem fmt_reset_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    i2c_notif_rel mstate.buffered_notif cstate.reg2hw
    ∧ mstate.regs = cstate.regs
    ⇒ (((mstate.buffered_notif = SOME fifo_ctrl_write) ∧ mstate.regs.fifo_ctrl.fmtrst = 1w)
       ⇔ cstate.fmt_fifo.reset)
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> ‘cstate.fmt_fifo.reset ⇔ cstate.regs.fifo_ctrl.fmtrst = 1w ∧ s.reg2hw.fifo_ctrl.fmtrst_qe’ by (
    simp [Abbr ‘cstate’, i2c_combs_flat, SF WORD_EXTRACT_ss])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘(mstate.buffered_notif = SOME fifo_ctrl_write ⇔ s.reg2hw.fifo_ctrl.fmtrst_qe)’ suffices_by (metis_tac [])
  >> ‘cstate.reg2hw.fifo_ctrl.fmtrst_qe = s.reg2hw.fifo_ctrl.fmtrst_qe’ by (simp [Abbr ‘cstate’, i2c_combs_flat])
  >> qpat_x_assum ‘i2c_notif_rel _ _’ (ASSUME_TAC o REWRITE_RULE [i2cRegsCommTheory.i2c_notif_rel_def])
  >> fs []
QED
        
Theorem read_byte_related:
  let
    cstate = i2c_circuit fext fbits n;
  in
    core_sim_rel mstate cstate
    ∧ mstate.fsm_state = Receiving ReadHoldBit
    ∧ mstate.bit_index = 0w
    ∧ mstate.counter = 1w
    ⇒ cstate.rx_fifo.wdata = mstate.read_byte
Proof
  LET_ELIM_TAC
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [Abbr ‘cstate’, i2c_combs_flat]
  >> drule_all core_sim_rel_relates_seq_only
  >> fs [core_sim_rel_def, encode_fsm_def, i2c_combs_flat]  
QED

Theorem fifo_rel_wptr_updated:
  ∀rptr .
    fifo_rel ws (circuit : 6 word -> β) (rptr : 7 word) wptr
    ∧ ((word_bit 6 rptr ≠ word_bit 6 wptr) ⇒ ((5 >< 0) (rptr : 7 word) : 6 word) ≠ ((5 >< 0) (wptr : 7 word) : 6 word))
    ⇒ fifo_rel ws (circuit ⦇((5 >< 0) wptr : 6 word) ↦ data ⦈) rptr wptr
Proof
  Induct_on ‘ws’
  >-( simp [fifo_rel_def] )
  >> ntac 2 strip_tac 
  >> disch_then (fn th => assume_tac th >> STRIP_ASSUME_TAC $ REWRITE_RULE [fifo_rel_def] th)
  >> first_x_assum drule
  >> ASM_CASES_TAC “(word_bit 6 (rptr + 1w) ≠ word_bit 6 wptr) ⇒ ((5 >< 0) ((rptr : 7 word) + 1w) : 6 word) ≠ ((5 >< 0) (wptr : 7 word) : 6 word)”
  >- (
     disch_then drule
     >> ASM_CASES_TAC “word_bit 6 $ (rptr : 7 word) ≠ word_bit 6 (wptr : 7 word)”
     >- ( first_x_assum drule
          >> qpat_x_assum ‘circuit _ = h’ mp_tac
          >> simp [fifo_rel_def, combinTheory.UPDATE_APPLY] )
     >> ‘word_bit 6 rptr = word_bit 6 wptr’ by (fs [])
     >> ‘(5 >< 0) rptr : 6 word ≠ (5 >< 0) wptr : 6 word’ by (
        spose_not_then assume_tac
        >> ‘dimindex (:7) - 1 = 6’ by EVAL_TAC
        >> fs []
        >> qpat_x_assum ‘word_bit 6 rptr ⇔ word_bit 6 wptr’ mp_tac
        >> qpat_x_assum ‘(5 >< 0) rptr = (5 >< 0) wptr’ mp_tac 
        >> qpat_x_assum ‘wptr >+ rptr’ mp_tac
        >> blastLib.BBLAST_TAC)
     >> qpat_x_assum ‘circuit _ = h’ mp_tac
     >> simp [fifo_rel_def, combinTheory.UPDATE_APPLY])
  >> fs []
  >> drule length_fifo
  >> disch_then (fn th => ‘LENGTH ws = w2n (64w : 7 word)’ by ( fs [th] ))
  >> rev_drule length_fifo_max
  >> qpat_x_assum ‘LENGTH ws = w2n (64w : 7 word)’ mp_tac
  >> simp [listTheory.LENGTH]
QED
        
Theorem fifo_rel_tail:
  fifo_rel ws (circuit : 6 word -> β) (rptr : 7 word) wptr
  ∧ ws ≠ []
  ∧ ((word_bit 6 rptr ≠ word_bit 6 wptr) ⇒ ((5 >< 0) (rptr : 7 word) : 6 word) ≠ ((5 >< 0) (wptr : 7 word) : 6 word))
  ⇒ fifo_rel (TL ws) (circuit ⦇((5 >< 0) wptr : 6 word) ↦ data ⦈) (rptr + 1w) wptr
Proof
  rpt strip_tac
  >> drule $ iffLR listTheory.LIST_NOT_NIL
  >> disch_then (fn th => ‘fifo_rel (HD ws :: TL ws) circuit rptr wptr’ by ( metis_tac [th]))
  >> drule_all fifo_rel_wptr_updated
  >> simp [fifo_rel_def]
QED

Theorem encode_fsm_injective:
  encode_fsm a = encode_fsm b ⇒ a = b
Proof
  spose_not_then STRIP_ASSUME_TAC
  >> Cases_on ‘a’
  >> TRY $ Cases_on ‘t’
  >> TRY $ Cases_on ‘r’
  >> TRY $ Cases_on ‘s'’
  >> (
  Cases_on ‘b’
  >> TRY $ Cases_on ‘t’
  >> TRY $ Cases_on ‘r’
  >> TRY $ Cases_on ‘s’
  >> TRY $ Cases_on ‘s'’
  >> fs [encode_fsm_def]     
  )
QED

Theorem encode_fsm_circuit:
  core_sim_rel mstate $ i2c_circuit fext fbits n
  ⇒ (mstate.fsm_state = a ⇔ (i2c_circuit fext fbits n).fsm_state = encode_fsm a)
Proof
  rewrite_tac [core_sim_rel_def]
  >> rpt strip_tac
  >> iff_tac
  >- (
  disch_then assume_tac
  >> (hardwareMiscTheory.f_equals1
       |> INST_TYPE [“:α” |-> “:fsmState”, “:β” |-> “:5 word”]
       |> SPEC “encode_fsm”
       |> drule)
  >> simp []                
  )
  >> qpat_x_assum ‘encode_fsm _ = _’ (ASSUME_TAC o GSYM)
  >> simp [encode_fsm_injective]
QED

Theorem i2c_core_circuit_simulate_encode_fsm:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ encode_fsm (st_upd mstate').fsm_state = cstate'.fsm_state
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘encode_fsm (st_upd mstate').fsm_state = cstate1_seq.fsm_state’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_fsm_state
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’,
           encode_fsm_next_state, encode_fsm_ite, encode_fsm_txState, encode_fsm_rxState,
           encode_fsm_startState, encode_fsm_stopState]
  >> strip_assume_tac i2c_circuit_cstep
  >> Cases_on ‘mstate.fsm_state’ THEN rewrite_tac [fsmState_case_def]
  >~ [‘Idle’]
  >- (
  ‘s.fsm_state = 0w’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
  >> ‘NULL mstate.fmt_fifo ⇔ s.fmt_fifo.rptr = s.fmt_fifo.wptr’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN drule fifo_rel_null
    THEN rw [])
  >> simp [i2c_combs_flat, encode_fsm_def])
  >~ [‘Active’]
  >- (
  ‘s.fsm_state = active’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
  >> ‘NULL mstate.fmt_fifo ⇔ s.fmt_fifo.rptr = s.fmt_fifo.wptr’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN drule fifo_rel_null
    THEN rw [])
  >> ASM_CASES_TAC “NULL mstate.fmt_fifo”
  >- (
    qpat_x_assum ‘i2c_circuit fext fbits n = _’ (fn th => REWRITE_TAC [th])
    >> fs [i2c_combs_flat, encode_fsm_def])
  >> ‘HD mstate.fmt_fifo = s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr :word6)’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN drule fifo_rel_not_null_HD
    THEN disch_then drule
    THEN EVAL_TAC )
  >> ‘mstate.trans_started = s.trans_started’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rw [core_sim_rel_def] )
  >> qpat_assum ‘i2c_circuit fext fbits n = _’ (fn th => REWRITE_TAC [th])
  >> simp [i2c_combs_flat]
  >> fs [encode_fsm_def] )
  >~ [‘Transmitting’]
  >- (
  BETA_TAC
  >> Cases_on ‘t’ THEN simp [txState_case_def]
  >- (
    ‘s.fsm_state = transClockLow’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.pend_restart = s.pend_restart)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER])
  >- (
    ‘s.fsm_state = transClockPulse’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.pend_restart = s.pend_restart)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = transHoldBit’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)
        ∧ (mstate.pend_restart = s.pend_restart)
        ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = transClockLowAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)
        ∧ (mstate.pend_restart = s.pend_restart)
        ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = transClockPulseAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)
        ∧ (mstate.pend_restart = s.pend_restart)
        ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = transHoldDevAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)
        ∧ (mstate.pend_restart = s.pend_restart)
        ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> ‘NULL mstate.fmt_fifo ⇔ s.fmt_fifo.rptr = s.fmt_fifo.wptr’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN drule fifo_rel_null
      THEN DISCH_THEN ACCEPT_TAC)
    >> ASM_CASES_TAC “NULL mstate.fmt_fifo”
    >- (
      simp [i2c_combs_flat]
      >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER])
    >> ‘HD mstate.fmt_fifo = s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr :word6)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN drule fifo_rel_not_null_HD
      THEN disch_then drule
      THEN EVAL_TAC )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
  >~ [‘Receiving’]
  >- (
  BETA_TAC
  >> Cases_on ‘r’ THEN simp [rxState_case_def]
  >- (
    ‘s.fsm_state = recReadClockLow’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = recReadClockPulse’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = recReadHoldBit’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = recHostClockLowAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = recHostClockPulseAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.bit_index = s.bit_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = recHostHoldBitAck’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)
        ∧ (mstate.bit_index = s.bit_index)
        ∧ (mstate.byte_index = s.byte_index)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> ‘NULL mstate.fmt_fifo ⇔ s.fmt_fifo.rptr = s.fmt_fifo.wptr’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN drule fifo_rel_null
      THEN DISCH_THEN ACCEPT_TAC)
    >> ASM_CASES_TAC “NULL mstate.fmt_fifo”
    >- (simp [i2c_combs_flat] >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
    >> ‘HD mstate.fmt_fifo = s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr :word6)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN drule fifo_rel_not_null_HD
      THEN disch_then drule
      THEN EVAL_TAC )
    >> simp [i2c_combs_flat]                                                                                                
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
  >~ [‘Starting’]  
  >- (
  BETA_TAC
  >> Cases_on ‘s'’ THEN simp [startState_case_def]
  >- (
    ‘s.fsm_state = startSetupStart’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = startHoldStart’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = startClockStart’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
  >~ [‘Stopping’]
  >- (
  BETA_TAC
  >> Cases_on ‘s'’ THEN simp [stopState_case_def]
  >- (
    ‘s.fsm_state = stopClockStop’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = stopSetupStop’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] )
  >- (
    ‘s.fsm_state = stopHoldStop’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
    >> ‘(mstate.counter = s.counter) ∧ (mstate.regs = s.regs)’ by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac
      THEN qpat_x_assum `mstate.regs = (i2c_circuit fext fbits n).regs` kall_tac
      THEN simp [core_sim_rel_combs]
      THEN rewrite_tac [core_sim_rel_def]
      THEN rpt strip_tac
      THEN rw [] )
    >> simp [i2c_combs_flat]
    >>  fs [encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
  >~ [‘PopFmtFifo’]
  >- (
  ‘s.fsm_state = popFmtFifo’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_def, i2c_core_combs_fsm_state, encode_fsm_def] )
  >> ‘(mstate.regs = s.regs)’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN qpat_x_assum `mstate.regs = (i2c_circuit fext fbits n).regs` kall_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN rw [] )
  >> ‘NULL mstate.fmt_fifo ⇔ s.fmt_fifo.rptr = s.fmt_fifo.wptr’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN drule fifo_rel_null
    THEN DISCH_THEN ACCEPT_TAC)
  >> ‘fifo_rel mstate.fmt_fifo s.fmt_fifo_regfile s.fmt_fifo.rptr s.fmt_fifo.wptr’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    THEN simp [core_sim_rel_combs]
    THEN rewrite_tac [core_sim_rel_def]
    THEN rpt strip_tac
    THEN drule fifo_rel_null
    THEN DISCH_THEN ACCEPT_TAC)
  >> drule length_fifo
  >> disch_then (fn th => REWRITE_TAC [th])
  >> simp [i2c_combs_flat]
  >> fs [encode_fsm_def, wordsTheory.WORD_HIGHER]                           
  >> ‘dimindex(:6) = (5:num) + (1:num) - (0:num)’ by EVAL_TAC
                                                     
  >> drule wordsTheory.EXTEND_EXTRACT
  >> disch_then (ASSUME_TAC o GSYM)
                
  >> irule if_equality
  >> conj_tac THEN1 ( rw [] )
  >> irule boolTheory.COND_CONG
  >> conj_tac
  >- (
    rw []
    >> simp [SF WORD_ss, SF WORD_EXTRACT_ss, SF WORD_ARITH_ss]
    >> ‘1 = w2n (1w: word7)’ by EVAL_TAC
    >> first_x_assum (fn th => ONCE_REWRITE_TAC [th])
    >> rewrite_tac [wordsTheory.w2n_11, wordsTheory.n2w_w2n] )
  >> conj_tac THEN ( rw [])
  ) (* popFmtInfo *)
QED

Theorem i2c_core_circuit_simulate_fifo_rel_rx:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ fifo_rel (st_upd mstate').rx_fifo cstate'.rx_fifo_regfile cstate'.rx_fifo.rptr cstate'.rx_fifo.wptr
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘fifo_rel (st_upd mstate').rx_fifo cstate1_seq.rx_fifo_regfile cstate1_seq.rx_fifo.rptr cstate1_seq.rx_fifo.wptr’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_rx_fifo
  >> simp []
  >> rpt IF_CASES_TAC
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
      
  >> ‘cstate.rx_fifo.reset’ by (
    simp [Abbr ‘cstate’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> ‘word_bit 0 s.regs.fifo_ctrl.rxrst’ by (
      qpat_x_assum ‘(i2c_circuit fext fbits n).regs.fifo_ctrl.rxrst = 1w’ mp_tac
      THEN simp [i2c_combs_flat])
    >> ‘s.reg2hw.fifo_ctrl.rxrst_qe’ by (
      qpat_x_assum ‘i2c_notif_rel _ _’ mp_tac
      THEN simp [i2c_notif_rel_def, i2c_combs_flat])
    >> qpat_assum ‘i2c_circuit_step fext fbit n = _’ (fn th => REWRITE_TAC [th])
    >> simp [i2c_combs_flat])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, fifo_rel_def])
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> irule fifo_rel_append_if
  >> conj_tac
  >- (
    ‘LENGTH mstate.rx_fifo < 64’ by ( metis_tac [] )
    >> ‘mstate.rx_fifo ≠ []’ by (
      spose_not_then assume_tac
      >> drule $ iffRL rich_listTheory.NULL_EQ_NIL
      >> disch_then (fn th => fs [th]))
    >> qpat_x_assum ‘LENGTH _ < 64’ mp_tac
    >> drule rich_listTheory.LENGTH_TL_LT
    >> simp [listTheory.LENGTH])
  >> EXISTS_TAC “cstate.rx_fifo.wptr : 7 word”
  >> ‘¬cstate.rx_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.rx_fifo.incr_rptr’ by (
    drule $ SRULE [SF boolSimps.LET_ss] incr_ptr_related
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> rpt $ disch_then drule
    >> disch_then irule
    >> fs [])
  >> ‘cstate.rx_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] incr_wptr_related
    >> EXISTS_TAC “mstate: i2c_state”
    >> ‘mstate.counter = 1w ∧ mstate.bit_index = 0w’ suffices_by ( simp [] )
    >> drule i2c_tick_fsm_state
    >> rw [])
  >> asm_rewrite_tac []
  >> ‘i2c_circuit fext fbits n = cstate’ by (simp [Abbr ‘cstate’])
  >> pop_assum (fn th => REWRITE_TAC [SRULE [th, SF boolSimps.LET_ss] incr_ptr_simplified,
                                      SRULE [th, SF boolSimps.LET_ss] incr_wptr_simplified] )
  >> ‘LENGTH mstate.rx_fifo < 64’ by (metis_tac [])
  >> ‘fifo_rel mstate.rx_fifo cstate.rx_fifo_regfile cstate.rx_fifo.rptr cstate.rx_fifo.wptr’
    by (fs [core_sim_rel_def])
  >> ‘¬ NULL mstate.rx_fifo’ by (metis_tac [])
  >> conj_tac
  >- (
    irule fifo_rel_tail           
    >> ‘(word_bit 6 cstate.rx_fifo.rptr ⇎ word_bit 6 cstate.rx_fifo.wptr) ⇒ ((5 >< 0) cstate.rx_fifo.rptr : 6 word) ≠ ((5 >< 0) cstate.rx_fifo.wptr: 6 word)’ by (
      spose_not_then strip_assume_tac
      >> drule length_fifo
      >> simp [])
    >> fs [listTheory.NULL_EQ])
  >> ‘cstate.rx_fifo.wdata = mstate.read_byte’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] read_byte_related
    >> ‘mstate.counter = 1w ∧ mstate.bit_index = 0w’ suffices_by ( simp [] )
    >> drule i2c_tick_fsm_state
    >> rw [])
  >> simp [fifo_rel_def]
  >> blastLib.BBLAST_TAC)
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬cstate.rx_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.rx_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] incr_wptr_related
    >> EXISTS_TAC “mstate: i2c_state”
    >> ‘mstate.counter = 1w ∧ mstate.bit_index = 0w’ suffices_by ( simp [] )
    >> drule i2c_tick_fsm_state
    >> rw [])
  >> ‘ ¬cstate.rx_fifo.incr_rptr’ by (
    simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> drule $ SRULE [SF boolSimps.LET_ss] no_incr_rptr
    >> rpt $ disch_then drule
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.rx_fifo.counter.rptr_wrap’ by (
    simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> ‘notif ≠ SOME (Read rdata_read) ∨ NULL mstate.rx_fifo’ by (fs [])
    >- ( fs [i2c_hwext_notif_rel_def] )                                
    >> ‘mstate.rx_fifo = []’ by ( fs [rich_listTheory.NULL_EQ_NIL])
    >> ‘s.rx_fifo.rptr = s.rx_fifo.wptr’  by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac 
      >> simp [core_sim_rel_def, fifo_rel_def, i2c_combs_flat])
    >> simp [])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> ‘i2c_circuit fext fbits n = cstate’ by (simp [Abbr ‘cstate’])
  >> pop_assum (fn th => REWRITE_TAC [SRULE [th, SF boolSimps.LET_ss] incr_wptr_simplified] )
  >> irule fifo_rel_append_if
  >> conj_tac
  >- (qpat_x_assum ‘LENGTH _ < 64’ mp_tac >> EVAL_TAC >> decide_tac)                
  >> EXISTS_TAC “cstate.rx_fifo.wptr : 7 word”
  >> conj_tac
  >- (
    irule fifo_rel_wptr_updated
    >> fs [core_sim_rel_def]
    >> disch_tac
    >> spose_not_then assume_tac
    >> rev_drule length_fifo
    >> qpat_x_assum ‘LENGTH _ < 64 ’ mp_tac
    >> simp [])
  >> ‘cstate.rx_fifo.wdata = mstate.read_byte’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] read_byte_related
    >> ‘mstate.counter = 1w ∧ mstate.bit_index = 0w’ suffices_by ( simp [] )
    >> drule i2c_tick_fsm_state
    >> rw [])
  >> simp [fifo_rel_def]
  >> blastLib.BBLAST_TAC )
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬cstate.rx_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.rx_fifo.incr_rptr’ by (
    drule $ SRULE [SF boolSimps.LET_ss] incr_ptr_related
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> rpt $ disch_then drule
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.rx_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] not_incr_wptr
    >> EXISTS_TAC “mstate: i2c_state”                
    >> ‘mstate.bit_index = 0w ∧ mstate.counter = 1w ∧ mstate.fsm_state = Receiving ReadHoldBit ⇒ 
        mstate'.fsm_state = Receiving HostClockLowAck’ suffices_by (rw [] >> fs [])
    >> drule i2c_tick_fsm_state
    >> simp [])
  >> ‘¬ cstate.rx_fifo.counter.wptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.rx_fifo.incr_wptr’ mp_tac
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> metis_tac [])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> ‘fifo_rel (TL mstate.rx_fifo) cstate.rx_fifo_regfile (cstate.rx_fifo.rptr + 1w) cstate.rx_fifo.wptr’ suffices_by (simp [Abbr ‘cstate’, SRULE [SF boolSimps.LET_ss] incr_ptr_simplified])
  >> ‘mstate.rx_fifo = HD mstate.rx_fifo :: TL mstate.rx_fifo’ by (
    metis_tac [listTheory.LIST_NOT_NIL, rich_listTheory.NULL_DEF])
  >> qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [core_sim_rel_def])
  >> qpat_x_assum ‘fifo_rel mstate.rx_fifo _ _ _’ mp_tac
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def])
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬ cstate.rx_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] not_incr_wptr
    >> EXISTS_TAC “mstate: i2c_state”                
    >> ‘mstate.bit_index = 0w ∧ mstate.counter = 1w ∧ mstate.fsm_state = Receiving ReadHoldBit ⇒ 
        mstate'.fsm_state = Receiving HostClockLowAck’ suffices_by (rw [] >> fs [])
    >> drule i2c_tick_fsm_state
    >> simp [])
  >> ‘¬cstate.rx_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘ ¬cstate.rx_fifo.incr_rptr’ by (
    simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> drule $ SRULE [SF boolSimps.LET_ss] no_incr_rptr
    >> rpt $ disch_then drule
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.rx_fifo.counter.wptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.rx_fifo.incr_wptr’ mp_tac
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> metis_tac [])
  >> ‘¬ cstate.rx_fifo.counter.rptr_wrap’ by (
    simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> ‘notif ≠ SOME (Read rdata_read) ∨ NULL mstate.rx_fifo’ by (fs [])
    >- ( fs [i2c_hwext_notif_rel_def] )                                
    >> ‘mstate.rx_fifo = []’ by ( fs [rich_listTheory.NULL_EQ_NIL])
    >> ‘s.rx_fifo.rptr = s.rx_fifo.wptr’  by (
      qpat_x_assum ‘core_sim_rel _ _’ mp_tac 
      >> simp [core_sim_rel_def, fifo_rel_def, i2c_combs_flat])
    >> simp [])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> fs [core_sim_rel_def])
QED

(*FIXME: this is a duplicate of the proof above. Can we abstract both proofs?*)
Theorem i2c_core_circuit_simulate_fifo_rel_fmt:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ fifo_rel (st_upd mstate').fmt_fifo cstate'.fmt_fifo_regfile cstate'.fmt_fifo.rptr cstate'.fmt_fifo.wptr
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘fifo_rel (st_upd mstate').fmt_fifo cstate1_seq.fmt_fifo_regfile cstate1_seq.fmt_fifo.rptr cstate1_seq.fmt_fifo.wptr’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_fmt_fifo
  >> simp []
  >> rpt IF_CASES_TAC
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘cstate.fmt_fifo.reset’ by (
    simp [Abbr ‘cstate’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> ‘s.regs.fifo_ctrl.fmtrst = 1w’ by (
      qpat_x_assum ‘(i2c_circuit fext fbits n).regs.fifo_ctrl.fmtrst = 1w’ mp_tac
      THEN simp [i2c_combs_flat])
    >> ‘s.reg2hw.fifo_ctrl.fmtrst_qe’ by (
      qpat_x_assum ‘i2c_notif_rel _ _’ mp_tac
      THEN simp [i2c_notif_rel_def, i2c_combs_flat])
    >> qpat_assum ‘i2c_circuit_step fext fbit n = _’ (fn th => REWRITE_TAC [th])
    >> simp [i2c_combs_flat])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, fifo_rel_def])
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> ‘(SNOC  (w2w cstate.regs.fdata.fbyte ‖
                  w2w cstate.regs.fdata.nakok ≪ 12 ‖
                  w2w cstate.regs.fdata.rcont ≪ 11 ‖
                  w2w cstate.regs.fdata.read ≪ 10 ‖
                  w2w cstate.regs.fdata.start ≪ 8 ‖
                  w2w cstate.regs.fdata.stop ≪ 9) (TL mstate.fmt_fifo)) =
      TL mstate.fmt_fifo ++ [(w2w cstate.regs.fdata.fbyte ‖
                                  w2w cstate.regs.fdata.nakok ≪ 12 ‖
                                  w2w cstate.regs.fdata.rcont ≪ 11 ‖
                                  w2w cstate.regs.fdata.read ≪ 10 ‖
                                  w2w cstate.regs.fdata.start ≪ 8 ‖
                                  w2w cstate.regs.fdata.stop ≪ 9)]’ by (simp [])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> irule fifo_rel_append_if
  >> conj_tac
  >- (
    ‘LENGTH $ TL mstate.fmt_fifo < 64’ suffices_by ( simp [] THEN decide_tac )
    >> irule arithmeticTheory.LET_TRANS
    >> EXISTS_TAC “LENGTH mstate.fmt_fifo”
    >> conj_tac >- (simp [])
    >> simp [listTheory.LENGTH_TL_LE] 
    )
  >> EXISTS_TAC “cstate.fmt_fifo.wptr : 7 word”
  >> ‘¬cstate.fmt_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.fmt_fifo.incr_rptr’ by (
    drule $ SRULE [SF boolSimps.LET_ss] fmt_incr_rptr_related
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.fmt_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] fmt_incr_wptr_related
    >> EXISTS_TAC “mstate: i2c_state”
    >> simp [])
  >> asm_rewrite_tac []
  >> ‘i2c_circuit fext fbits n = cstate’ by (simp [Abbr ‘cstate’])
  >> pop_assum (fn th => REWRITE_TAC [SRULE [th, SF boolSimps.LET_ss] fmt_incr_rptr_simplified,
                                      SRULE [th, SF boolSimps.LET_ss] fmt_incr_wptr_simplified] )
  >> ‘fifo_rel mstate.fmt_fifo cstate.fmt_fifo_regfile cstate.fmt_fifo.rptr cstate.fmt_fifo.wptr’
    by (fs [core_sim_rel_def])
  >> conj_tac
  >- (
    irule fifo_rel_tail           
    >> ‘(word_bit 6 cstate.fmt_fifo.rptr ⇎ word_bit 6 cstate.fmt_fifo.wptr) ⇒ ((5 >< 0) cstate.fmt_fifo.rptr : 6 word) ≠ ((5 >< 0) cstate.fmt_fifo.wptr: 6 word)’ by (
      spose_not_then strip_assume_tac
      >> drule length_fifo
      >> simp [])
    >> fs [listTheory.NULL_EQ])
  >> ‘cstate.fmt_fifo.wdata = (w2w cstate.regs.fdata.fbyte ‖
                                   w2w cstate.regs.fdata.nakok ≪ 12 ‖
                                   w2w cstate.regs.fdata.rcont ≪ 11 ‖
                                   w2w cstate.regs.fdata.read ≪ 10 ‖
                                   w2w cstate.regs.fdata.start ≪ 8 ‖
                                   w2w cstate.regs.fdata.stop ≪ 9)’ by (
    simp [Abbr ‘cstate’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> simp [i2c_combs_flat])
  >> simp [fifo_rel_def]
  >> blastLib.BBLAST_TAC)           
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬cstate.fmt_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.fmt_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] fmt_incr_wptr_related
    >> EXISTS_TAC “mstate: i2c_state”
    >> rw [])
  >> ‘ ¬cstate.fmt_fifo.incr_rptr’ by (
    simp [Abbr ‘cstate’]
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_no_incr_rptr
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.fmt_fifo.counter2.rptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.fmt_fifo.incr_rptr’ mp_tac
    >> simp [Abbr ‘cstate’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    )
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> ‘i2c_circuit fext fbits n = cstate’ by (simp [Abbr ‘cstate’])
  >> pop_assum (fn th => REWRITE_TAC [SRULE [th, SF boolSimps.LET_ss] fmt_incr_wptr_simplified] )
  >> ‘(SNOC  (w2w cstate.regs.fdata.fbyte ‖
                  w2w cstate.regs.fdata.nakok ≪ 12 ‖
                  w2w cstate.regs.fdata.rcont ≪ 11 ‖
                  w2w cstate.regs.fdata.read ≪ 10 ‖
                  w2w cstate.regs.fdata.start ≪ 8 ‖
                  w2w cstate.regs.fdata.stop ≪ 9) (mstate.fmt_fifo)) =
      mstate.fmt_fifo ++ [(w2w cstate.regs.fdata.fbyte ‖
                               w2w cstate.regs.fdata.nakok ≪ 12 ‖
                               w2w cstate.regs.fdata.rcont ≪ 11 ‖
                               w2w cstate.regs.fdata.read ≪ 10 ‖
                               w2w cstate.regs.fdata.start ≪ 8 ‖
                               w2w cstate.regs.fdata.stop ≪ 9)]’ by (simp [])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> irule fifo_rel_append_if
  >> conj_tac
  >- (qpat_x_assum ‘LENGTH _ < 64’ mp_tac >> EVAL_TAC >> decide_tac)                
  >> EXISTS_TAC “cstate.fmt_fifo.wptr : 7 word”
  >> conj_tac
  >- (
    irule fifo_rel_wptr_updated
    >> fs [core_sim_rel_def]
    >> disch_tac
    >> spose_not_then assume_tac
    >> drule length_fifo
    >> qpat_x_assum ‘LENGTH _ < 64 ’ mp_tac
    >> simp [])
  >> ‘cstate.fmt_fifo.wdata = (w2w cstate.regs.fdata.fbyte ‖
                                   w2w cstate.regs.fdata.nakok ≪ 12 ‖
                                   w2w cstate.regs.fdata.rcont ≪ 11 ‖
                                   w2w cstate.regs.fdata.read ≪ 10 ‖
                                   w2w cstate.regs.fdata.start ≪ 8 ‖
                                   w2w cstate.regs.fdata.stop ≪ 9)’ by (
    simp [Abbr ‘cstate’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> simp [i2c_combs_flat])
  >> simp [fifo_rel_def]
  >> blastLib.BBLAST_TAC )
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬cstate.fmt_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘cstate.fmt_fifo.incr_rptr’ by (
    drule $ SRULE [SF boolSimps.LET_ss] fmt_incr_rptr_related
    >> simp [Abbr ‘cstate’]
    >> rpt $ disch_then drule
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.fmt_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] fmt_not_incr_wptr
    >> EXISTS_TAC “mstate: i2c_state”
    >> metis_tac [])
  >> ‘¬ cstate.fmt_fifo.counter2.wptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.fmt_fifo.incr_wptr’ mp_tac
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> metis_tac [])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> ‘fifo_rel (TL mstate.fmt_fifo) cstate.fmt_fifo_regfile (cstate.fmt_fifo.rptr + 1w) cstate.fmt_fifo.wptr’
    suffices_by (simp [Abbr ‘cstate’, SRULE [SF boolSimps.LET_ss] fmt_incr_rptr_simplified])
  >> ‘mstate.fmt_fifo = HD mstate.fmt_fifo :: TL mstate.fmt_fifo’ by (
    metis_tac [listTheory.LIST_NOT_NIL, rich_listTheory.NULL_DEF])
  >> qpat_x_assum ‘core_sim_rel _ _’ (STRIP_ASSUME_TAC o REWRITE_RULE [core_sim_rel_def])
  >> qpat_x_assum ‘fifo_rel mstate.fmt_fifo _ _ _’ mp_tac
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def])
  >- (
  rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
  >> ‘¬ cstate.fmt_fifo.incr_wptr’ by (
    simp [Abbr ‘cstate’]
    >> irule $ SRULE [SF boolSimps.LET_ss] fmt_not_incr_wptr
    >> EXISTS_TAC “mstate: i2c_state”
    >> metis_tac [])
  >> ‘¬cstate.fmt_fifo.reset’ by (
    ‘i2c_notif_rel mstate.buffered_notif (i2c_circuit fext fbits n).reg2hw’ by ( simp [Abbr ‘cstate’])
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_reset_related
    >> ‘mstate.regs = (i2c_circuit fext fbits n).regs’ by (simp [Abbr ‘cstate’])
    >> disch_then drule              
    >> simp [Abbr ‘cstate’])
  >> ‘ ¬cstate.fmt_fifo.incr_rptr’ by (
    simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> drule $ SRULE [SF boolSimps.LET_ss] fmt_no_incr_rptr
    >> disch_then irule
    >> fs [])
  >> ‘¬ cstate.fmt_fifo.counter2.wptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.fmt_fifo.incr_wptr’ mp_tac
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep
    >> metis_tac [])
  >> ‘¬ cstate.fmt_fifo.counter2.rptr_wrap’ by (
    qpat_x_assum ‘¬ cstate.fmt_fifo.incr_rptr’ mp_tac
    >> simp [Abbr ‘cstate’]
    >> qx_choose_then ‘s’ (fn th => simp [th, i2c_combs_flat] >> assume_tac th) i2c_circuit_cstep)
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat ]
  >> fs [core_sim_rel_def])
QED

Theorem i2c_core_circuit_simulate_counter:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').counter = cstate'.counter
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').counter = cstate1_seq.counter’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_counter
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat]
  >> drule encode_fsm_circuit                
  >> disch_then (fn th => qpat_assum ‘i2c_circuit fext fbits n = _ ’ (fn th2 =>
    ASSUME_TAC $ SRULE [th2, i2c_combs_flat] th))
  >> pop_assum (fn th => REWRITE_TAC [th, encode_fsm_def, fsmState_case_def])
  >> ‘mstate.counter = s.counter’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def,i2c_combs_flat])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> irule if_equality
  >> ‘mstate.stretch_idle_cnt = s.stretch_idle_cnt’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def,i2c_combs_flat])
  >> Cases_on ‘mstate.fsm_state’
  >> TRY $ Cases_on ‘t’
  >> TRY $ Cases_on ‘r’
  >> TRY $ Cases_on ‘s'’
  >> simp [encode_fsm_def]
  >> drule encode_fsm_circuit
  >> disch_then (fn th => drule $ iffLR th)
  >> simp [i2c_combs_flat, encode_fsm_def]
QED

Theorem i2c_core_circuit_simulate_pend_restart:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').pend_restart = cstate'.pend_restart
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').pend_restart = cstate1_seq.pend_restart’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_pend_restart
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat]
  >> ‘mstate.pend_restart ⇔ s.pend_restart’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘mstate.counter = s.counter’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘mstate.trans_started ⇔ s.trans_started’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
      suffices_by (metis_tac [])
  >> conj_tac
  >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac
    >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat]                
      )
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat]
QED         

Theorem i2c_core_circuit_simulate_trans_started:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').trans_started = cstate'.trans_started
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').trans_started = cstate1_seq.trans_started’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_trans_started
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat]
  >> ‘mstate.counter = s.counter ∧ mstate.trans_started = s.trans_started’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
QED

Theorem i2c_core_circuit_simulate_bit_index:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').bit_index = cstate'.bit_index
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').bit_index = cstate1_seq.bit_index’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_bit_index
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat]
  >> ‘mstate.counter = s.counter ∧ mstate.bit_index = s.bit_index’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
QED

Theorem i2c_core_circuit_simulate_stretch_idle_cnt:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').stretch_idle_cnt = cstate'.stretch_idle_cnt
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').stretch_idle_cnt = cstate1_seq.stretch_idle_cnt’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_stretch_idle_cnt
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> ‘mstate.trans_started = s.trans_started ∧ mstate.stretch_idle_cnt = s.stretch_idle_cnt’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> ‘word_bit 0 (n2w (bool_to_bit (fext n).cio_scl_i) : 1 word) = (fext n).cio_scl_i’ by (
    rewrite_tac [arithmeticTheory.bool_to_bit_def]
    >> IF_CASES_TAC
    >> blastLib.BBLAST_TAC)
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> qsuff_tac ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
  >- (
    strip_tac
    >> ‘(¬NULL mstate.fmt_fifo ∧ word_bit 8 (HD mstate.fmt_fifo)) ⇔
       (s.fmt_fifo.rptr ≠ s.fmt_fifo.wptr ∧
        word_bit 8 (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr)))’ by ( metis_tac [] )
    >> ‘(¬NULL mstate.fmt_fifo ∧ word_bit 9 (HD mstate.fmt_fifo)) ⇔
       (s.fmt_fifo.rptr ≠ s.fmt_fifo.wptr ∧
        word_bit 9 (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr)))’ by ( metis_tac [] )
    >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
    >> irule boolTheory.COND_CONG
    >> metis_tac [])
  >> conj_tac
  >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac
    >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat]                
      )
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat]        
QED

Theorem i2c_core_circuit_simulate_byte_index:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').byte_index = cstate'.byte_index
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').byte_index = cstate1_seq.byte_index’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_byte_index
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> ‘mstate.counter = s.counter ∧ mstate.byte_index = s.byte_index’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> qsuff_tac ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
  >- (
    strip_tac
    >> ‘(¬NULL mstate.fmt_fifo ∧ word_bit 10 (HD mstate.fmt_fifo)) ⇔
       (s.fmt_fifo.rptr ≠ s.fmt_fifo.wptr ∧
        word_bit 10 (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr)))’ by ( metis_tac [] )
    >> metis_tac [])
  >> conj_tac
  >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac
    >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat]                
      )
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat]        
QED

Theorem i2c_core_circuit_simulate_read_byte:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').read_byte = cstate'.read_byte
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').read_byte = cstate1_seq.read_byte’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_read_byte
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> ‘mstate.bit_index = s.bit_index ∧ mstate.counter = s.counter ∧ mstate.read_byte = s.read_byte’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> NTAC 3 $ POP_ASSUM (fn th => REWRITE_TAC [th])
  >> irule if_equality
  >> conj_tac >- (simp [] )
  >> IF_CASES_TAC
  >- (
    rewrite_tac [arithmeticTheory.bool_to_bit_def]
    >> simp []
    >> IF_CASES_TAC
    >> simp [] >> blastLib.BBLAST_TAC)
  >> simp []
QED

Theorem i2c_core_circuit_simulate_scl_rx_val:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').scl_rx_val = cstate'.scl_rx_val
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').scl_rx_val = cstate1_seq.scl_rx_val’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_scl_rx_val
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> ‘mstate.scl_rx_val = s.scl_rx_val’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> POP_ASSUM (fn th => REWRITE_TAC [th, arithmeticTheory.bool_to_bit_def])
  >> IF_CASES_TAC
  >> simp []
  >> blastLib.BBLAST_TAC                
QED        

Theorem i2c_core_circuit_simulate_sda_rx_val:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').sda_rx_val = cstate'.sda_rx_val
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').sda_rx_val = cstate1_seq.sda_rx_val’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >>   drule_then assume_tac cheshire_req_unchanged
  >> drule_then assume_tac i2c_tick_sda_rx_val
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> ‘mstate.sda_rx_val = s.sda_rx_val’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> POP_ASSUM (fn th => REWRITE_TAC [th, arithmeticTheory.bool_to_bit_def])
  >> IF_CASES_TAC
  >> simp []
  >> blastLib.BBLAST_TAC                
QED

Theorem i2c_core_circuit_simulate_regs:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  ∧ cheshire_req_rel req_m req_c
  ∧ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  ∧ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  ∧ i2c_hwext_notif_rel notif req_c
  ⇒ (st_upd mstate').regs = cstate'.regs
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘(st_upd mstate').regs = cstate1_seq.regs’
    suffices_by (simp [Abbr ‘cstate'’, i2c_combs_flat])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >> Cases_on ‘req_m’
  >- (
  fs [cheshire_req_def, i2c_tick_def]
  >> ‘¬ (i2c_circuit fext fbits n).valid’ by (
    fs [cheshireCircuitTheory.cheshire_req_rel_def]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> simp [Abbr ‘cstate’, i2c_combs_flat]                        
    )
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> simp [i2cRegsTheory.i2c_regs_component_equality]
  >> REVERSE conj_tac
  >- (
    simp [i2cRegsTheory.i2c_intr_enable_component_equality,
          i2cRegsTheory.i2c_ctrl_component_equality,
          i2cRegsTheory.i2c_fdata_component_equality,
          i2cRegsTheory.i2c_fifo_ctrl_component_equality,
          i2cRegsTheory.i2c_ovrd_component_equality,
          i2cRegsTheory.i2c_timing0_component_equality,
          i2cRegsTheory.i2c_timing1_component_equality,
          i2cRegsTheory.i2c_timing2_component_equality,
          i2cRegsTheory.i2c_timing3_component_equality,
          i2cRegsTheory.i2c_timing4_component_equality,
          i2cRegsTheory.i2c_timeout_ctrl_component_equality,
          i2cRegsTheory.i2c_target_id_component_equality,
          i2cRegsTheory.i2c_txdata_component_equality,
          i2cRegsTheory.i2c_host_timeout_ctrl_component_equality
         ])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> ‘mstate.counter = s.counter ∧ mstate.pend_restart = s.pend_restart’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> simp [arithmeticTheory.bool_to_bit_def]
  >> ‘s.regs.intr_state.cmd_complete ‖ 1w = 1w ∧ s.regs.intr_state.nak ‖ 1w = 1w’ by (blastLib.BBLAST_TAC)
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> qsuff_tac
     ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
  >- (
    disch_tac
    >> rw []
    >> gvs []
    )
  >> conj_tac
  >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac
    >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat]                
      )
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat])
  >> Cases_on ‘x’
  >> Cases_on ‘r’
  >> Cases_on ‘r'’                
  >> gvs [cheshire_req_def, i2c_tick_def]
  >- (
  ‘st_upd = I’ by (
    qpat_x_assum ‘SUM_MAP _ _ _ = _’ mp_tac
    >> Cases_on ‘i2c_read mstate q q'’
    >- (simp [sumTheory.SUM_MAP_def])        
    >> Cases_on ‘y’
    >> simp [sumTheory.SUM_MAP_def])
  >> pop_assum (fn th => REWRITE_TAC [th, combinTheory.I_THM])
  >> ‘¬ (i2c_circuit fext fbits n).write’ by (
    gvs [cheshireCircuitTheory.cheshire_req_rel_def]
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> simp [i2c_combs_flat])
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> simp [i2cRegsTheory.i2c_regs_component_equality]
  >> REVERSE conj_tac
  >- (
    simp [i2cRegsTheory.i2c_intr_enable_component_equality,
          i2cRegsTheory.i2c_ctrl_component_equality,
          i2cRegsTheory.i2c_fdata_component_equality,
          i2cRegsTheory.i2c_fifo_ctrl_component_equality,
          i2cRegsTheory.i2c_ovrd_component_equality,
          i2cRegsTheory.i2c_timing0_component_equality,
          i2cRegsTheory.i2c_timing1_component_equality,
          i2cRegsTheory.i2c_timing2_component_equality,
          i2cRegsTheory.i2c_timing3_component_equality,
          i2cRegsTheory.i2c_timing4_component_equality,
          i2cRegsTheory.i2c_timeout_ctrl_component_equality,
          i2cRegsTheory.i2c_target_id_component_equality,
          i2cRegsTheory.i2c_txdata_component_equality,
          i2cRegsTheory.i2c_host_timeout_ctrl_component_equality
         ])
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def])
  >> ‘mstate.counter = s.counter ∧ mstate.pend_restart = s.pend_restart’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> simp [arithmeticTheory.bool_to_bit_def]
  >> ‘s.regs.intr_state.cmd_complete ‖ 1w = 1w ∧ s.regs.intr_state.nak ‖ 1w = 1w’ by (blastLib.BBLAST_TAC)
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> qsuff_tac
     ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
  >- (
    disch_tac
    >> rw []
    >> gvs []
    )
  >> conj_tac
  >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac
    >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat]                
      )
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat])
  >> ‘i2c_write mstate q q' x = INR (st_upd, notif)’ by (
    qpat_x_assum ‘SUM_MAP _ _ _ = _’ mp_tac
    >> Cases_on ‘i2c_write mstate q q' x’
    >- ( simp [] )
    >> Cases_on ‘y’
    >> simp [sumTheory.SUM_MAP_def]
    )
  >> drule i2cMappingsTheory.i2c_write_st_upd_alt
  >> disch_then (fn th => REWRITE_TAC [th])
  >> ‘ (i2c_circuit fext fbits n).valid ∧
       (i2c_circuit fext fbits n).write ’ by (
    gvs [cheshireCircuitTheory.cheshire_req_rel_def]
    >> simp [Abbr ‘cstate’, Abbr ‘req_c’]
    >> CHOOSE_TAC i2c_circuit_cstep
    >> simp [i2c_combs_flat]
    )
  >> ‘¬(i2c_circuit fext fbits n).error’ by (
    CHOOSE_TAC i2c_circuit_cstep
    >> simp [i2c_combs_flat]
    >> `~ISL (i2c_write mstate q q' x)` by simp []
    >> drule_then (fn thm => full_simp_tac pure_ss [thm]) i2c_req_error_i2c_write
    (* since i2c doesn't use windows, we can ignore this *)
    >> fs [i2c_win_addr_def]
    )
  >> simp [Abbr ‘cstate1_seq’, i2c_ffs_flat, Abbr ‘cstate’]
  >> CHOOSE_TAC i2c_circuit_cstep
  >> simp [i2c_combs_flat, fnum_witness'_def]
  >> ‘∀w. req_c.addr = w <=> q' = w2n w ’ by (
    strip_tac
    >> gvs [cheshireCircuitTheory.cheshire_req_rel_def])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> ‘x = req_c.wdata’ by (gvs [cheshireCircuitTheory.cheshire_req_rel_def])
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> EVAL_TAC
  >> drule encode_fsm_circuit
  >> disch_then (fn th => simp [th, i2c_combs_flat, encode_fsm_def, arithmeticTheory.bool_to_bit_def])
  >> ‘s.regs.intr_state.cmd_complete ‖ 1w = 1w ∧ s.regs.intr_state.nak ‖ 1w = 1w’ by (
    blastLib.BBLAST_TAC)
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> ‘mstate.counter = s.counter ∧ mstate.pend_restart = s.pend_restart’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> NTAC 2 $ pop_assum (fn th => REWRITE_TAC [th])
  >> ‘BIT 0 (if (fext n).cio_sda_i then 1 else 0) = (fext n).cio_sda_i’ by (
    rw []
    )
  >> pop_assum (fn th => REWRITE_TAC [th])
  >> qsuff_tac
     ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==> HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
  >- (
  disch_tac
  >> rw []
  >> gvs []
  )
  >> conj_tac
  >- (
  qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> iff_tac
  >- (
    disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
    >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
    >> simp [fifo_rel_def, i2c_combs_flat]                
    )
  >> drule length_fifo
  >> simp [i2c_combs_flat]
  >> rpt strip_tac
  >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
    qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
    >> blastLib.BBLAST_TAC)
  >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
    qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
    >> blastLib.BBLAST_TAC)
  >> ‘LENGTH mstate.fmt_fifo = 0’ by (
    qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
    >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
    >> EVAL_TAC)
  >> pop_assum mp_tac
  >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat]  
QED
        
Theorem i2c_core_circuit_simulate:
  let
    cstate = i2c_circuit fext fbits n;
    cstate' = i2c_circuit fext fbits (SUC n);
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req;
  in
  i2c_state_rel mstate cstate
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  /\ i2c_tick notif (mstate with fnums := fnum_witness' cstate (fext n)) = INR mstate'
  /\ i2c_hwext_notif_rel notif req_c
  ==> core_sim_rel (st_upd mstate') cstate'
Proof
  LET_ELIM_TAC
  >> rewrite_tac [core_sim_rel_def]
  >> rpt conj_tac
  >> simp [Abbr ‘cstate'’, Abbr ‘req_c’, Abbr ‘cstate’]
  >| map (drule o SRULE [SF boolSimps.LET_ss])
         [ i2c_core_circuit_simulate_fifo_rel_rx,
           i2c_core_circuit_simulate_fifo_rel_fmt,
           i2c_core_circuit_simulate_encode_fsm,
           i2c_core_circuit_simulate_counter,
           i2c_core_circuit_simulate_pend_restart,
           i2c_core_circuit_simulate_trans_started,
           i2c_core_circuit_simulate_bit_index,
           i2c_core_circuit_simulate_stretch_idle_cnt,
           i2c_core_circuit_simulate_byte_index,
           i2c_core_circuit_simulate_read_byte,
           i2c_core_circuit_simulate_scl_rx_val,
           i2c_core_circuit_simulate_sda_rx_val,
           i2c_core_circuit_simulate_regs]
  >> rpt $ disch_then drule
  >> simp []
QED

Theorem i2c_core_correct:
  !mstate req_m fext fbits n st_upd notif rdata.
  let
    req_c = reg_req_decode (fext n).reg_req_i: 7 reg_req
  in
  i2c_state_rel mstate (i2c_circuit fext fbits n)
  /\ cheshire_req_rel req_m req_c
  /\ cheshire_req i2c_read i2c_write mstate req_m = INR (st_upd, notif, rdata)
  /\ ISR (i2c_tick notif mstate)
  /\ i2c_hwext_notif_rel notif req_c
  ==> ?fnums. i2c_core_state_rel (st_upd (OUTR (i2c_tick notif (mstate with fnums := fnums)))) (i2c_circuit fext fbits (SUC n))
    /\ i2c_hw_write_rel (mstate with fnums := fnums).regs (OUTR (i2c_tick notif (mstate with fnums := fnums))).regs
                        (i2c_circuit fext fbits n).hw2reg
    /\ ~i2c_win_error (i2c_circuit fext fbits n).win_buses
Proof
  simp []
  >> rpt strip_tac
  >> qexists `fnum_witness' (i2c_circuit fext fbits n) (fext n)`
  >> `?mstate'. i2c_tick notif (mstate with fnums := fnum_witness' (i2c_circuit fext fbits n) (fext n)) = INR mstate'`
     by (simp [GSYM ISR_exists, i2c_tick_ISR_fnums])
  >> simp [i2c_core_state_rel_def]
  >> rpt strip_tac

  (* i2c_hwext_read_rel *)
  >- cheat
  (* i2c_win_read_rel *)
  >- simp [i2c_win_read_rel_def]
  (* i2c_win_ready *)
  >- simp [i2c_win_ready_def]
  (* core_sim_rel *)
  >- drule_all_then irule $ SRULE [SF boolSimps.LET_ss] i2c_core_circuit_simulate
  (* i2c_hw_write_rel *)
  >- (
  rewrite_tac [i2c_hw_write_rel_def]
  >> drule i2c_tick_regs_intr_state
  >> disch_tac
  >> CHOOSE_TAC i2c_circuit_cstep
  >> ‘mstate.regs = s.regs’ by (
    fs [i2c_state_rel_def, i2c_combs_flat])
  >> ‘s.regs.intr_state.cmd_complete ‖ 1w = 1w ∧ s.regs.intr_state.nak ‖ 1w = 1w’ by (
    blastLib.BBLAST_TAC)
  >> ‘core_sim_rel mstate (i2c_circuit fext fbits n)’ by (
    fs [i2c_state_rel_def, i2c_core_state_rel_def])
  >> drule encode_fsm_circuit
  >> disch_tac
  >> ‘mstate.counter = s.counter ∧ mstate.pend_restart = s.pend_restart’ by (
    qpat_x_assum ‘core_sim_rel _ _’ mp_tac
    >> simp [core_sim_rel_def, i2c_combs_flat])
  >> simp [i2c_combs_flat, fnum_witness'_def, arithmeticTheory.bool_to_bit_def, encode_fsm_def]
  >> ‘(NULL mstate.fmt_fifo ⇔ (s.fmt_fifo.rptr = s.fmt_fifo.wptr))
      ∧ (¬ NULL mstate.fmt_fifo ==>
         HD mstate.fmt_fifo = (s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr : 6 word)))’
    suffices_by (disch_tac >> rw [] >> gvs [])
  >> conj_tac >- (
    qpat_x_assum ‘core_sim_rel _ _’ (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
    >> iff_tac >- (
      disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ])
      >> qpat_x_assum ‘fifo_rel _ _ _ _’ mp_tac
      >> simp [fifo_rel_def, i2c_combs_flat])
    >> drule length_fifo
    >> simp [i2c_combs_flat]
    >> rpt strip_tac
    >> ‘word_bit 6 s.fmt_fifo.wptr ⇔ word_bit 6 s.fmt_fifo.rptr’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘(-1w * ((5 >< 0) s.fmt_fifo.rptr: 7 word) + ((5 >< 0) s.fmt_fifo.wptr: 7 word)) = 0w’ by (
      qpat_x_assum ‘s.fmt_fifo.rptr = s.fmt_fifo.wptr’ mp_tac
      >> blastLib.BBLAST_TAC)
    >> ‘LENGTH mstate.fmt_fifo = 0’ by (
      qpat_x_assum ‘LENGTH mstate.fmt_fifo = _’ mp_tac
      >> ntac 2 $ pop_assum (fn th => REWRITE_TAC [th])
      >> EVAL_TAC)
    >> pop_assum mp_tac
    >> simp [listTheory.NULL_LENGTH])
  >> disch_then (ASSUME_TAC o REWRITE_RULE [listTheory.NULL_EQ, listTheory.LIST_NOT_NIL])
  >> qpat_x_assum ‘core_sim_rel _ _’ (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [core_sim_rel_def])
  >> once_asm_rewrite_tac []
  >> simp [fifo_rel_def, i2c_combs_flat])
  (* i2c_win_error *)
  >- ( fs [i2c_win_error_def])
QED

val _ = export_theory ();
 
