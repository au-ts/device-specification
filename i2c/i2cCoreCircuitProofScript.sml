open BasicProvers;
open translatorLib;
open shallowFlattenLib;
open cheshireOracleTheory;
open i2cCircuitTheory;
open dep_rewrite;
open i2cCoreTheory;
open i2cMappingsTheory;
open i2cCircuitStateTheory;
 
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

Theorem i2c_combs_flat = ``procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s'``
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
            hw2reg_intr_state_cmd_complete_de_comb_def,
            hw2reg_intr_state_cmd_complete_d_comb_def, next_pend_restart_comb_def,
            next_trans_started_comb_def])
  |> SRULE [i2c_reg_top_comb_2_flat];

Theorem i2c_ffs_flat = ``procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) fext s s'``
  |> SCONV [i2c_core_ffs1_def, procs_def]
  |> (fn thm => foldl (fn (rule, thm) => SRULE [rule |> CONV_RULE COND_RECORD_CONV |> SRULE [SF boolSimps.LET_ss]] thm) thm
           [i2c_core_counter_ff_def, i2c_core_stretch_idle_cnt_ff_def, fmt_fifo_rptr_ff_def,
            fmt_fifo_regfile_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_wptr_ff_def,
            bit_index_ff_def, pend_restart_ff_def, byte_index_ff_def, i2c_core_rx_fifo_rptr_ff_def,
            i2c_core_rx_fifo_regfile_def, i2c_core_ff_def])
  |> SRULE [i2c_reg_top_ff_flat];

Theorem core_sim_rel_combs:
  core_sim_rel mstate (procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s') ⇔ core_sim_rel mstate s'
Proof
  simp [core_sim_rel_def, i2c_combs_flat]
QED

Definition fnum_witness_def:
  (fnum_witness fext (0:num) = bool_to_bit fext.cio_scl_i)
∧ (fnum_witness fext (1:num) = bool_to_bit fext.cio_sda_i)
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
       if ¬NULL mstate.fmt_fifo ∧ word_bit 10 (HD mstate.fmt_fifo) then Receiving ReadClockLow
       else if
       (¬NULL mstate.fmt_fifo ∧ word_bit 8 (HD mstate.fmt_fifo)) ∧
       ¬mstate.trans_started
       then
         Starting SetupStart
       else Transmitting ClockLow
   | Transmitting ClockLow =>
       if mstate.counter >+ 1w then Transmitting ClockLow
       else if mstate.pend_restart then Starting SetupStart
       else Transmitting ClockPulse
   | Transmitting ClockPulse =>
       if mstate.counter >+ 1w then Transmitting ClockPulse
       else Transmitting HoldBit
   | Transmitting HoldBit =>
       if mstate.counter >+ 1w then Transmitting HoldBit
       else if mstate.bit_index = 0w then Transmitting ClockLowAck
       else Transmitting ClockLow
   | Transmitting ClockLowAck =>
       if mstate.counter >+ 1w then Transmitting ClockLowAck
       else Transmitting ClockPulseAck
   | Transmitting ClockPulseAck =>
       if mstate.counter >+ 1w then Transmitting ClockPulseAck
       else Transmitting HoldDevAck
   | Transmitting HoldDevAck =>
       if mstate.counter >+ 1w then Transmitting HoldDevAck
       else if ¬ NULL mstate.fmt_fifo ∧ word_bit 9 (HD mstate.fmt_fifo) then Stopping ClockStop
       else PopFmtFifo
   | Receiving ReadClockLow =>
       if mstate.counter >+ 1w then Receiving ReadClockLow
       else Receiving ReadClockPulse
   | Receiving ReadClockPulse =>
       if mstate.counter >+ 1w then Receiving ReadClockPulse
       else Receiving ReadHoldBit
   | Receiving ReadHoldBit =>
       if mstate.counter >+ 1w then Receiving ReadHoldBit
       else if mstate.bit_index = 0w then Receiving HostClockLowAck
       else Receiving ReadClockLow
   | Receiving HostClockLowAck =>
       if mstate.counter >+ 1w then Receiving HostClockLowAck
       else Receiving HostClockPulseAck
   | Receiving HostClockPulseAck =>
       if mstate.counter >+ 1w then Receiving HostClockPulseAck
       else Receiving HostHoldBitAck
   | Receiving HostHoldBitAck =>
       if mstate.counter >+ 1w then Receiving HostHoldBitAck
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
       if mstate.counter >+ 1w then Starting SetupStart else Starting HoldStart
   | Starting HoldStart =>
       if mstate.counter >+ 1w then Starting HoldStart else Starting ClockStart
   | Starting ClockStart =>
       if mstate.counter >+ 1w then Starting ClockStart
       else Transmitting ClockLow
   | Stopping ClockStop =>
       if mstate.counter >+ 1w then Stopping ClockStop else Stopping SetupStop
   | Stopping SetupStop =>
       if mstate.counter >+ 1w then Stopping SetupStop else Stopping HoldStop
   | Stopping HoldStop =>
       if mstate.counter >+ 1w then Stopping HoldStop
       else if mstate.regs.ctrl.enablehost = 0w then Idle
       else PopFmtFifo
   | PopFmtFifo =>
       if mstate.regs.ctrl.enablehost = 0w then Stopping ClockStop
       else if (LENGTH mstate.fmt_fifo = 1) then Idle
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

Theorem next_state_i2c_core_combs_further = SCONV [i2c_combs_flat] ``(procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s').next_state``

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
        (if
           mstate.fsm_state = Receiving ReadHoldBit ∧
           mstate'.fsm_state = Receiving HostClockLowAck ∧
           LENGTH mstate.rx_fifo < 64
         then
           (if notif = SOME (Read rdata_read) ∧ ¬NULL mstate.rx_fifo then
              TL mstate.rx_fifo
            else mstate.rx_fifo) ⧺ [mstate.read_byte]
         else if notif = SOME (Read rdata_read) ∧ ¬NULL mstate.rx_fifo then
           TL mstate.rx_fifo
         else mstate.rx_fifo)            
Proof
  simp [i2c_tick_def]
QED

Theorem mstate_with_fnums:
  ((mstate with fnums := fnums).rx_fifo = mstate.rx_fifo)
∧ ((mstate with fnums := fnums).fsm_state = mstate.fsm_state)
Proof
  simp []
QED

(* TODO: put into CakeML/hardware? (at the very least, stop making copies) *)
Theorem mk_circuit_cstep:
  ∃s'. mk_circuit sstep cstep s fext n = cstep (fext n) s' s'
Proof
  Cases_on ‘n’
  >- (qexists ‘s’ >> simp [mk_circuit_def])
  >- (qexists ‘(sstep (fext n') (mk_circuit sstep cstep s fext n')
                      (mk_circuit sstep cstep s fext n'))’
      >> simp [mk_circuit_def])
QED

Theorem i2c_circuit_cstep:
  ?s. i2c_circuit fext fbits n = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext n) s s
Proof
  simp [i2c_circuit_def, mk_module_def] >> irule mk_circuit_cstep
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
  /\ i2c_tick notif (mstate with fnums := fnum_witness (fext n)) = INR mstate'
  /\ i2c_hwext_notif_rel notif req_c
  ==> core_sim_rel (st_upd mstate') cstate'
Proof
  LET_ELIM_TAC
  >> qabbrev_tac ‘cstate1_seq = procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) (fext n) cstate cstate’
  >> ‘cstate' = procs ([i2c_reg_top_comb_1] ++ i2c_core_combs ++ [i2c_reg_top_comb_2]) (fext (SUC n)) cstate1_seq cstate1_seq’
    by fs [Abbr ‘cstate'’, i2c_circuit_def, mk_module_def, mk_circuit_def, Abbr ‘cstate1_seq’]
  >> ‘core_sim_rel (st_upd mstate') cstate1_seq’
    suffices_by (rw [Abbr ‘cstate'’, core_sim_rel_combs])
  >> fs [i2c_state_rel_def, i2c_core_state_rel_def]
  >> rw [core_sim_rel_def]
  >~ [‘encode_fsm’]
  >- (
     drule_then assume_tac cheshire_req_unchanged
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
        >- ( fs [next_state_i2c_core_combs_further, encode_fsm_def] )
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
        >> fs [next_state_i2c_core_combs_further, encode_fsm_def] )
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
           >> fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER])
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
           >> fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >> fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >> fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >> fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >- ( fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
           >> ‘HD mstate.fmt_fifo = s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr :word6)’ by (
              qpat_x_assum ‘core_sim_rel _ _’ mp_tac
              THEN simp [core_sim_rel_combs]
              THEN rewrite_tac [core_sim_rel_def]
              THEN rpt strip_tac
              THEN drule fifo_rel_not_null_HD
              THEN disch_then drule
              THEN EVAL_TAC )
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >- ( fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
           >> ‘HD mstate.fmt_fifo = s.fmt_fifo_regfile ((5 >< 0) s.fmt_fifo.rptr :word6)’ by (
              qpat_x_assum ‘core_sim_rel _ _’ mp_tac
              THEN simp [core_sim_rel_combs]
              THEN rewrite_tac [core_sim_rel_def]
              THEN rpt strip_tac
              THEN drule fifo_rel_not_null_HD
              THEN disch_then drule
              THEN EVAL_TAC )
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] )
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
           >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER] ) )
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
        >>  fs [next_state_i2c_core_combs_further, encode_fsm_def, wordsTheory.WORD_HIGHER]
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
  ) (* encode_fsm *)
  >- (
     drule_then assume_tac cheshire_req_unchanged
     >> drule_then assume_tac i2c_tick_rx_fifo
     >> simp []
     >> rpt IF_CASES_TAC
     >- (
        rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
        >> simp [Abbr ‘cstate1_seq’,i2c_core_ffs1_rx_fifo, cstate_rx_fifo_regfile, cstate_rx_fifo_rptr, cstate_rx_fifo_wptr]
        >> irule fifo_rel_append_if
        >> conj_tac
        >- (
           qpat_x_assum ‘LENGTH _ < 64’ mp_tac
           >> ‘mstate.rx_fifo ≠ []’ by ( fs [rich_listTheory.NULL_EQ_NIL] )
           >> drule rich_listTheory.LENGTH_TL_LT
           >> simp [listTheory.LENGTH])
        >> EXISTS_TAC “cstate.rx_fifo.wptr : 7 word”
        >> conj_tac
        >- (



      )
    )
  ) (* fifo_rel rx_fifo *)
  >- (
    cheat
  ) (* fifo_rel fmt_fifo*)     
  >- (
    cheat 
  ) (* counter *)
  >- (
    cheat
  ) (* pend_restart *)
  >- (
    cheat
  ) (* trans_started *)
  >- (
    cheat
  ) (* bit_index *)
  >- (
    cheat
  ) (* stretch_idle_cnt *)
  >- (
    cheat
  ) (* byte_index *)
  >- (
    cheat
  ) (* read_byte *)
  >- (
    cheat
  ) (* scl_rx_val *)
  >- (
    cheat
  ) (* sda_rx_val *)
  >- (
    cheat
  ) (* regs *)
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
  >> qexists `fnum_witness (fext n)`
  >> `?mstate'. i2c_tick notif (mstate with fnums := fnum_witness (fext n)) = INR mstate'`
     by (simp [GSYM ISR_exists, i2c_tick_ISR_fnums])
  >> simp [i2c_core_state_rel_def]
  >> rpt strip_tac

  (* i2c_hwext_read_rel *)
  >- cheat
  (* i2c_win_read_rel *)
  >- cheat
  (* i2c_win_ready *)
  >- cheat
  (* core_sim_rel *)
  >- drule_all_then irule $ SRULE [SF boolSimps.LET_ss] i2c_core_circuit_simulate
  (* i2c_hw_write_rel *)
  >- cheat
  (* i2c_win_error *)
  >- cheat
QED

val _ = export_theory ();
