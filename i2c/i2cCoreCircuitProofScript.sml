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

(*        
Theorem word_bit_eq_GT:
  (x : 'a word) + 1w >+ x ∧ 1 < dimindex (:α) 
  ⇒ (word_bit (dimindex (:'a) - 1) x ⇔
       word_bit (dimindex (:'a) - 1) (x + 1w))
Proof
  once_rewrite_tac [wordsTheory.WORD_ADD_COMM]
  >> rewrite_tac [wordsTheory.WORD_HIGHER, WORD_ADD_RIGHT_LO2]
  >> rpt $ strip_tac
  >- (
     ‘1w + x = 1w’ by ( rw [] ) 
     THEN asm_rewrite_tac [wordsTheory.word_bit_0]
     THEN drule word_msb_1
     THEN simp [SF WORD_ss, SF WORD_BIT_EQ_ss])
  >- (
  )
QED
        

Theorem word_msb_differs:
  word_bit (dimindex (:α) - 1) x ≠ word_bit (dimindex (:α) - 1) ((x : α word) + 1w) ⇒
  x = UINT_MAXw ∨ x = INT_MAXw
Proof
  print_match [] “word_bit _ (_ + _)”
QED

Theorem fifo_rel_append:
  dimindex (:γ) < dimindex (:α) ⇒
  ∀rptr. fifo_rel (xs ++ ys) (circuit: γ word -> β) (rptr: α word) wptr ⇒
           ∃cptr. fifo_rel xs circuit rptr cptr ∧ fifo_rel ys circuit cptr wptr
Proof
  >> strip_tac
  >> Induct_on ‘xs’ >- (rw [fifo_rel_def, listTheory.APPEND] )
  >> rpt strip_tac
  >> fs [fifo_rel_def]
  >> first_x_assum drule
  >> disch_then CHOOSE_TAC
  >> EXISTS_TAC “cptr: 'a word”
  >> ASM_CASES_TAC “xs = [] : 'b list”
  >- (
     ‘cptr = rptr + 1w’ by ( fs [fifo_rel_def] )
     THEN ‘((word_bit (dimindex (:α) − (1 :num)) rptr ⇎ word_bit (dimindex (:α) − (1 :num)) cptr) ⇒
          ((dimindex (:γ) − (1 :num) >< (0 :num)) cptr :γ word) <₊ ((dimindex (:γ) − (1 :num) >< (0 :num)) rptr :γ word))’
       suffices_by ( metis_tac [word_bit_eq_GT])
     THEN strip_tac
     THEN ‘((dimindex (:γ) - 1 >< 0) (rptr + 1w) : γ word) = ((dimindex (:γ) - 1 >< 0) rptr : γ word) + (((dimindex (:γ) - 1 >< 0) (1w : α word)) : γ word)’
          by (irule WORD_EXTRACT_OVER_ADD >> simp [])
     THEN asm_rewrite_tac []
        
sprint_match [] “_ + x <+ x”        
  )
   
  
QED
*)
        

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
  >> ‘(5 >< 0) wptr :word6 <+ (5 >< 0) rptr : word6’ by (
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
     qpat_x_assum ‘_ <+ _’ mp_tac
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
  >> ‘(5 >< 0) wptr :word6 <+ (5 >< 0) rptr : word6’ by (
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
     qpat_x_assum ‘_ <+ _’ mp_tac
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

val core_init_tm = add_x_inits “<|fmt_fifo_regfile := K 0w; rx_fifo_regfile := K 0w; |>”

Definition core_init_def:
  core_init fbits = ^core_init_tm
End
 
Theorem core_sim_rel_comb:
  (core_sim_rel mstate (next_bit_index_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_byte fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (next_trans_started_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_rvalid fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (next_pend_restart_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (next_intr_cmd_complete_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (hw2reg_intr_state_cmd_complete_d_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (hw2reg_intr_state_cmd_complete_de_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (next_intr_nak_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (hw2reg_intr_state_nak_de_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_incr_wptr_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_full_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_wdata_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_wvalid_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_counter_rptr_wrap_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_incr_rptr_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_empty_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_rready_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_rdata_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_reset_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_read_byte_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_sda_rx_val_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fifo_depth fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_byte_clr_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_byte_decr_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_scl_rx_val_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (bit_decr fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (bit_clr fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (req_restart fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_flag_stop_after fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_flag_start_before fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_flag_read_bytes fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_flag_nak_ok fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_log_stop_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_log_start_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_counter_wptr_wrap_cnt fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_counter_wptr_wrap fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_wdata fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_incr_wptr fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_incr_rptr fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_full fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_wvalid fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_counter_rptr_wrap_cnt fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_counter_rptr_wrap fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_counter_rptr_wrap fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_empty fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_rready fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (counter_gt_one_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_reset fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (fmt_fifo_rdata fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_counter fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_stretch_idle_cnt fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_scl_d_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_stretch_en_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_load_tcount_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_curr_delay_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_delay_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_rx_fifo_counter_wptr_wrap_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_state fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_next_byte_index_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_shift_data_en_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_read_byte_clr_comb fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_core_byte_num_comb fext s s') ⇔ core_sim_rel mstate s')
Proof
  rw [next_bit_index_comb_def, next_trans_started_comb_def, next_pend_restart_comb_def, next_intr_cmd_complete_comb_def,
      hw2reg_intr_state_cmd_complete_d_comb_def, hw2reg_intr_state_cmd_complete_de_comb_def, next_intr_nak_comb_def,
      hw2reg_intr_state_nak_de_comb_def, i2c_core_rx_fifo_incr_wptr_comb_def, i2c_core_rx_fifo_full_comb_def,
      i2c_core_rx_fifo_wdata_comb_def, i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def,
      i2c_core_rx_fifo_counter_rptr_wrap_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def, i2c_core_rx_fifo_empty_comb_def,
      i2c_core_rx_fifo_rready_comb_def, i2c_core_rx_fifo_rdata_comb_def, i2c_core_rx_fifo_reset_comb_def,
      i2c_core_next_read_byte_comb_def, i2c_core_next_sda_rx_val_comb_def, fifo_depth_def,
      i2c_core_byte_clr_comb_def, i2c_core_next_scl_rx_val_comb_def, bit_decr_def,
      bit_clr_def, req_restart_def, fmt_fifo_flag_stop_after_def, fmt_fifo_flag_start_before_def, i2c_core_log_stop_comb_def,
      i2c_core_log_start_comb_def, fmt_fifo_counter_wptr_wrap_cnt_def, fmt_fifo_counter_wptr_wrap_def, fmt_fifo_wdata_def,
      fmt_fifo_incr_wptr_def, fmt_fifo_full_def, fmt_fifo_wvalid_def, fmt_fifo_counter_rptr_wrap_cnt_def,
      fmt_fifo_counter_rptr_wrap_def, fmt_fifo_empty_def, fmt_fifo_rready_def, counter_gt_one_comb_def, fmt_fifo_reset_def,
      i2c_core_next_counter_def, i2c_core_next_stretch_idle_cnt_def, i2c_core_scl_d_comb_def, i2c_core_stretch_en_comb_def,
      i2c_core_load_tcount_comb_def, i2c_core_curr_delay_comb_def, i2c_core_delay_comb_def,
      i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def, i2c_core_rx_fifo_counter_wptr_wrap_comb_def, fmt_fifo_rdata_def,
      fmt_fifo_incr_rptr_def, fmt_fifo_rvalid_def, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_nak_ok_def, fmt_byte_def,
      i2c_core_byte_decr_comb_def, i2c_core_byte_num_comb_def, i2c_core_next_state_def, i2c_core_read_byte_clr_comb_def,
      i2c_core_next_byte_index_comb_def, i2c_core_shift_data_en_comb_def, i2c_core_read_byte_clr_comb_def
      , core_sim_rel_def]
QED

Theorem core_sim_rel_i2c_reg_top_comb:
  (core_sim_rel mstate (i2c_reg_top_comb_1 fext s s') ⇔ core_sim_rel mstate s')
  ∧ (core_sim_rel mstate (i2c_reg_top_comb_2 fext s s') ⇔ core_sim_rel mstate s')
Proof
  simp [core_sim_rel_def, i2c_reg_top_comb_1_flat, i2c_reg_top_comb_2_flat]
QED

Theorem next_state_disjoint:
  ((i2c_core_next_state fext s s').curr_delay = s'.curr_delay)
  ∧ ((i2c_core_next_state fext s s').load_tcount = s'.load_tcount)
  ∧ ((i2c_core_next_state fext s s').stretch_en = s'.stretch_en)
  ∧ ((i2c_core_next_state fext s s').scl_d = s'.scl_d)
  ∧ ((i2c_core_next_state fext s s').fmt_flag = s'.fmt_flag)
  ∧ ((i2c_core_next_state fext s s').delay = s'.delay)
  ∧ ((i2c_core_next_state fext s s').fmt_byte = s'.fmt_byte)
  ∧ ((i2c_core_next_state fext s s').byte_clr = s'.byte_clr)
  ∧ ((i2c_core_next_state fext s s').byte_decr = s'.byte_decr)
  ∧ ((i2c_core_next_state fext s s').byte_num = s'.byte_num)
  ∧ ((i2c_core_next_state fext s s').fmt_fifo = s'.fmt_fifo)
  
  ∧ ((i2c_core_curr_delay_comb fext s s').fmt_flag = s'.fmt_flag)
  ∧ ((i2c_core_curr_delay_comb fext s s').fmt_fifo = s'.fmt_fifo)
  ∧ ((i2c_core_curr_delay_comb fext s s').fmt_byte = s'.fmt_byte)
  ∧ ((i2c_core_curr_delay_comb fext s s').byte_clr = s'.byte_clr)
  ∧ ((i2c_core_curr_delay_comb fext s s').byte_decr = s'.byte_decr)
  ∧ ((i2c_core_curr_delay_comb fext s s').byte_num = s'.byte_num)
                               
  ∧ ((i2c_core_delay_comb fext s s').fmt_flag = s'.fmt_flag)
  ∧ ((i2c_core_delay_comb fext s s').fmt_fifo = s'.fmt_fifo)
Proof
  rw [i2c_core_next_state_def, i2c_core_curr_delay_comb_def, i2c_core_delay_comb_def]
QED

Theorem fupd_ite:
  (next_counter_fupd (K f1) (if P then Q else R) = if P then next_counter_fupd (K f1) Q else next_counter_fupd (K f1) R)
∧ (next_stretch_idle_cnt_fupd (K f2) (if P then Q else R) = if P then next_stretch_idle_cnt_fupd (K f2) Q else next_stretch_idle_cnt_fupd (K f2) R)
∧ (scl_d_fupd (K f3) (if P then Q else R) = if P then scl_d_fupd (K f3) Q else scl_d_fupd (K f3) R)
∧ (stretch_en_fupd (K f4) (if P then Q else R) = if P then stretch_en_fupd (K f4) Q else stretch_en_fupd (K f4) R)
∧ (load_tcount_fupd (K f5) (if P then Q else R) = if P then load_tcount_fupd (K f5) Q else load_tcount_fupd (K f5) R)
∧ (curr_delay_fupd (K f6) (if P then Q else R) = if P then curr_delay_fupd (K f6) Q else curr_delay_fupd (K f6) R)
∧ (delay_fupd (K f7) (if P then Q else R) = if P then delay_fupd (K f7) Q else delay_fupd (K f7) R)
∧ (rx_fifo_fupd (K f8) (if P then Q else R) = if P then rx_fifo_fupd (K f8) Q else rx_fifo_fupd (K f8) R)
∧ (wptr_wrap_cnt_fupd (K f9) (if P then (Q1:counter) else R1) = if P then wptr_wrap_cnt_fupd (K f9) Q1 else wptr_wrap_cnt_fupd (K f9) R1)
∧ (wptr_wrap_cnt_fupd (K f10) (if P then (Q2:counter2) else R2) = if P then wptr_wrap_cnt_fupd (K f10) Q2 else wptr_wrap_cnt_fupd (K f10) R2)
∧ (fifo_counter_fupd (K f11) (if P then (Q3:fifo) else R3) = if P then fifo_counter_fupd (K f11) Q3 else fifo_counter_fupd (K f11) R3)
∧ (byte_num_fupd (K f12) (if P then Q else R) = if P then byte_num_fupd (K f12) Q else byte_num_fupd (K f12) R)
∧ (next_byte_index_fupd (K f13) (if P then Q else R) = if P then next_byte_index_fupd (K f13) Q else next_byte_index_fupd (K f13) R)
∧ (wdata_fupd (K f14) (if P then Q3 else R3) = if P then wdata_fupd (K f14) Q3 else wdata_fupd (K f14) R3)
∧ (read_byte_clr_fupd (K f15) (if P then Q else R) = if P then read_byte_clr_fupd (K f15) Q else read_byte_clr_fupd (K f15) R)
∧ (shift_data_en_fupd (K f16) (if P then Q else R) = if P then shift_data_en_fupd (K f16) Q else shift_data_en_fupd (K f16) R)
∧ (byte_decr_fupd (K f17) (if P then Q else R) = if P then byte_decr_fupd (K f17) Q else byte_decr_fupd (K f17) R)
∧ (byte_clr_fupd (K f18) (if P then Q else R) = if P then byte_clr_fupd (K f18) Q else byte_clr_fupd (K f18) R)
∧ (cnt_gt_one_fupd (K f19) (if P then Q else R) = if P then cnt_gt_one_fupd (K f19) Q else cnt_gt_one_fupd (K f19) R)
∧ (next_scl_rx_val_fupd (K f20) (if P then Q else R) = if P then next_scl_rx_val_fupd (K f20) Q else next_scl_rx_val_fupd (K f20) R)
∧ (bit_decr_fupd (K f21) (if P then Q else R) = if P then bit_decr_fupd (K f21) Q else bit_decr_fupd (K f21) R)
∧ (bit_clr_fupd (K f22) (if P then Q else R) = if P then bit_clr_fupd (K f22) Q else bit_clr_fupd (K f22) R)
∧ (req_restart_fupd (K f23) (if P then Q else R) = if P then req_restart_fupd (K f23) Q else req_restart_fupd (K f23) R)
∧ (fmt_byte_fupd (K f24) (if P then Q else R) = if P then fmt_byte_fupd (K f24) Q else fmt_byte_fupd (K f24) R)
∧ (fmt_flag_fupd (K f25) (if P then Q else R) = if P then fmt_flag_fupd (K f25) Q else fmt_flag_fupd (K f25) R)
∧ (log_stop_fupd (K f26) (if P then Q else R) = if P then log_stop_fupd (K f26) Q else log_stop_fupd (K f26) R)
∧ (log_start_fupd (K f27) (if P then Q else R) = if P then log_start_fupd (K f27) Q else log_start_fupd (K f27) R)
∧ (next_state_fupd (K f28) (if P then Q else R) = if P then next_state_fupd (K f28) Q else next_state_fupd (K f28) R)
∧ (fmt_fifo_fupd (K f29) (if P then Q else R) = if P then fmt_fifo_fupd (K f29) Q else fmt_fifo_fupd (K f29) R)
Proof
  rw [] 
QED

Theorem ite_rec_sel:
  ((if P then Q else R).fmt_flag = if P then Q.fmt_flag else R.fmt_flag)
∧ ((if P then Q else R).fmt_byte = if P then Q.fmt_byte else R.fmt_byte)
∧ ((if P then Q else R).byte_clr = if P then Q.byte_clr else R.byte_clr)
∧ ((if P then Q else R).byte_decr = if P then Q.byte_decr else R.byte_decr)
∧ ((if P then Q else R).log_start = if P then Q.log_start else R.log_start)
∧ ((if P then Q else R).log_stop = if P then Q.log_stop else R.log_stop)
∧ ((if P then Q else R).stretch_en = if P then Q.stretch_en else R.stretch_en)
∧ ((if P then Q else R).scl_d = if P then Q.scl_d else R.scl_d)
∧ ((if P then Q else R).next_state = if P then Q.next_state else R.next_state)
∧ ((if P then Q else R).next_byte_index = if P then Q.next_byte_index else R.next_byte_index)
∧ ((if P then Q else R).fmt_fifo = if P then Q.fmt_fifo else R.fmt_fifo)
∧ ((if P then Q else R).fmt_fifo.depth = if P then Q.fmt_fifo.depth else R.fmt_fifo.depth)
∧ ((if P then Q2 else R2).depth = if P then Q2.depth else R2.depth)
∧ ((if P then (Q3:fifo2) else (R3:fifo2)).depth = if P then Q3.depth else R3.depth)
∧ ((if P then Q else R).rx_fifo_regfile = if P then Q.rx_fifo_regfile else R.rx_fifo_regfile)
∧ ((if P then Q else R).rx_fifo = if P then Q.rx_fifo else R.rx_fifo)
∧ ((if P then Q3 else R3).rptr = if P then Q3.rptr else R3.rptr)
∧ ((if P then Q3 else R3).wptr = if P then Q3.wptr else R3.wptr)
∧ ((if P then Q2 else R2).rptr = if P then Q2.rptr else R2.rptr)
∧ ((if P then Q2 else R2).wptr = if P then Q2.wptr else R2.wptr)
Proof
  rw []
QED
        
Theorem core_sim_rel_combs:
  core_sim_rel mstate (procs (i2c_reg_top_comb_1::(i2c_core_combs ++ [i2c_reg_top_comb_2])) fext s s') ⇔ core_sim_rel mstate s'
Proof
  simp [i2c_core_combs_def, procs_def, core_sim_rel_comb, core_sim_rel_i2c_reg_top_comb]
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

Theorem next_state_access:
  ((i2c_core_rx_fifo_regfile fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_rptr_ff fext s s').next_state = s'.next_state)
  ∧ ((byte_index_ff fext s s').next_state = s'.next_state)
  ∧ ((pend_restart_ff fext s s').next_state = s'.next_state)
  ∧ ((bit_index_ff fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_wptr_ff fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_wptr_ff fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_regfile_ff fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_rptr_ff fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_stretch_idle_cnt_ff fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_counter_ff fext s s').next_state = s'.next_state)
Proof
  rw [i2c_core_rx_fifo_regfile_def, i2c_core_rx_fifo_rptr_ff_def, byte_index_ff_def,
      pend_restart_ff_def, bit_index_ff_def, fmt_fifo_wptr_ff_def, i2c_core_rx_fifo_wptr_ff_def,
      fmt_fifo_regfile_ff_def, fmt_fifo_rptr_ff_def, i2c_core_stretch_idle_cnt_ff_def,
      i2c_core_counter_ff_def]
QED
 
Theorem cstate_fsm_state:
  (procs (i2c_core_ffs1 ++ [i2c_reg_top_ff]) fext cstate cstate).fsm_state = cstate.next_state
Proof
  simp [i2c_core_ffs1_def, procs_def, i2c_core_ff_def, i2c_reg_top_ff_flat, next_state_access]
QED

Theorem cheshire_req_fsm_state:
  cheshire_req i2c_read i2c_write st req = INR (st_upd, notif, rdata) ==>
  (st_upd st').fsm_state = st'.fsm_state
Proof
  rpt strip_tac
  >> dxrule_then strip_assume_tac cheshire_req_INR_cases
  >- simp []
  >- simp []
  >- dxrule_then (fn thm => simp [thm]) i2c_write_st_upd_alt
QED

Theorem next_state_comb_access:
  ((next_trans_started_comb fext s s').next_state = s'.next_state)
  ∧ ((next_pend_restart_comb fext s s').next_state = s'.next_state)
  ∧ ((hw2reg_intr_state_cmd_complete_d_comb fext s s').next_state = s'.next_state)
  ∧ ((hw2reg_intr_state_cmd_complete_de_comb fext s s').next_state = s'.next_state)
  ∧ ((next_intr_nak_comb fext s s').next_state = s'.next_state)
  ∧ ((hw2reg_intr_state_nak_de_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_counter_wptr_wrap_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_incr_wptr_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_full_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_wdata_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_wvalid_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_counter_rptr_wrap_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_incr_rptr_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_empty_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_rready_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_rdata_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_rx_fifo_reset_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_next_sda_rx_val_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_shift_data_en_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_read_byte_clr_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_next_byte_index_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_byte_num_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_byte_decr_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_byte_clr_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_next_counter fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_next_stretch_idle_cnt fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_next_scl_rx_val_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_scl_d_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_stretch_en_comb fext s s').next_state = s'.next_state)
  ∧ ((bit_decr fext s s').next_state = s'.next_state)
  ∧ ((bit_clr fext s s').next_state = s'.next_state)
  ∧ ((req_restart fext s s').next_state = s'.next_state)
  ∧ ((fmt_byte fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_flag_nak_ok fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_log_stop_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_log_start_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_load_tcount_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_curr_delay_comb fext s s').next_state = s'.next_state)
  ∧ ((i2c_core_delay_comb fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_counter_wptr_wrap_cnt fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_counter_wptr_wrap fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_wdata fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_incr_wptr fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_full fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_wvalid fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_counter_rptr_wrap_cnt fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_counter_rptr_wrap fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_incr_rptr fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_rready fext s s').next_state = s'.next_state)
  ∧ ((fmt_fifo_reset fext s s').next_state = s'.next_state)
Proof
  rw [next_trans_started_comb_def, next_pend_restart_comb_def, hw2reg_intr_state_cmd_complete_d_comb_def,
      hw2reg_intr_state_cmd_complete_de_comb_def, next_intr_nak_comb_def, hw2reg_intr_state_nak_de_comb_def,
      i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def, i2c_core_rx_fifo_counter_wptr_wrap_comb_def,
      i2c_core_rx_fifo_incr_wptr_comb_def, i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_wdata_comb_def,
      i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def,
      i2c_core_rx_fifo_counter_rptr_wrap_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def,
      i2c_core_rx_fifo_empty_comb_def, i2c_core_rx_fifo_rready_comb_def, i2c_core_rx_fifo_rdata_comb_def,
      i2c_core_rx_fifo_reset_comb_def, i2c_core_next_sda_rx_val_comb_def, i2c_core_shift_data_en_comb_def,
      i2c_core_read_byte_clr_comb_def, i2c_core_next_byte_index_comb_def, i2c_core_byte_num_comb_def,
      i2c_core_byte_decr_comb_def, i2c_core_byte_clr_comb_def, i2c_core_next_counter_def,
      i2c_core_next_stretch_idle_cnt_def, i2c_core_next_scl_rx_val_comb_def, i2c_core_scl_d_comb_def,
      i2c_core_stretch_en_comb_def, bit_decr_def, bit_clr_def, req_restart_def, fmt_byte_def,
      fmt_fifo_flag_nak_ok_def, i2c_core_log_stop_comb_def, i2c_core_log_start_comb_def,
      i2c_core_load_tcount_comb_def, i2c_core_curr_delay_comb_def, i2c_core_delay_comb_def,
      fmt_fifo_counter_wptr_wrap_cnt_def, fmt_fifo_counter_wptr_wrap_def, fmt_fifo_wdata_def,
      fmt_fifo_incr_wptr_def, fmt_fifo_full_def, fmt_fifo_wvalid_def, fmt_fifo_counter_rptr_wrap_cnt_def,
      fmt_fifo_counter_rptr_wrap_def, fmt_fifo_incr_rptr_def, fmt_fifo_rready_def, fmt_fifo_reset_def
      ]
QED

Theorem if_equality:
  (Q1 = Q2 ∧ R1 = R2) ⇒ (if P then Q1 else R1) = (if P then Q2 else R2)
Proof
  rw []
QED

(* takes longer time to prove *)        
Theorem next_state_commute_curr_delay_comb:
(i2c_core_next_state fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ i2c_core_next_state fext s s')
Proof
  rewrite_tac [i2c_core_curr_delay_comb_def, i2c_core_next_state_def] >> rw [fupd_ite] >> fs []
QED
        

Theorem commute_with_next_state:
  (i2c_core_next_state fext s $ i2c_core_next_byte_index_comb fext s s' = i2c_core_next_byte_index_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_next_byte_index_comb fext s s' = i2c_core_next_byte_index_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_next_byte_index_comb fext s s' = i2c_core_next_byte_index_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_byte_num_comb fext s s' = i2c_core_byte_num_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_byte_num_comb fext s s' = i2c_core_byte_num_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_byte_num_comb fext s s' = i2c_core_byte_num_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_byte_decr_comb fext s s' = i2c_core_byte_decr_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_byte_decr_comb fext s s' = i2c_core_byte_decr_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_byte_decr_comb fext s s' = i2c_core_byte_decr_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_byte_clr_comb fext s s' = i2c_core_byte_clr_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_byte_clr_comb fext s s' = i2c_core_byte_clr_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_byte_clr_comb fext s s' = i2c_core_byte_clr_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_next_counter fext s s' = i2c_core_next_counter fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_next_counter fext s s' = i2c_core_next_counter fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_next_counter fext s s' = i2c_core_next_counter fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_next_stretch_idle_cnt fext s s' = i2c_core_next_stretch_idle_cnt fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_next_stretch_idle_cnt fext s s' = i2c_core_next_stretch_idle_cnt fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_next_stretch_idle_cnt fext s s' = i2c_core_next_stretch_idle_cnt fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_next_scl_rx_val_comb fext s s' = i2c_core_next_scl_rx_val_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_next_scl_rx_val_comb fext s s' = i2c_core_next_scl_rx_val_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_next_scl_rx_val_comb fext s s' = i2c_core_next_scl_rx_val_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_scl_d_comb fext s s' = i2c_core_scl_d_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_scl_d_comb fext s s' = i2c_core_scl_d_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_scl_d_comb fext s s' = i2c_core_scl_d_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_stretch_en_comb fext s s' = i2c_core_stretch_en_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_stretch_en_comb fext s s' = i2c_core_stretch_en_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_stretch_en_comb fext s s' = i2c_core_stretch_en_comb fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ bit_decr fext s s' = bit_decr fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ bit_decr fext s s' = bit_decr fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ bit_decr fext s s' = bit_decr fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ bit_clr fext s s' = bit_clr fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ bit_clr fext s s' = bit_clr fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ bit_clr fext s s' = bit_clr fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ req_restart fext s s' = req_restart fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ req_restart fext s s' = req_restart fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ req_restart fext s s' = req_restart fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ fmt_byte fext s s' = fmt_byte fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_byte fext s s' = fmt_byte fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_byte fext s s' = fmt_byte fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_flag_nak_ok fext s s' = fmt_fifo_flag_nak_ok fext s $ fifo_depth fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ i2c_core_log_stop_comb fext s s' = i2c_core_log_stop_comb fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ i2c_core_log_start_comb fext s s' = i2c_core_log_start_comb fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ i2c_core_load_tcount_comb fext s s' = i2c_core_load_tcount_comb fext s $ fmt_fifo_rvalid fext s s')

∧ (counter_gt_one_comb fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ i2c_core_curr_delay_comb fext s s' = i2c_core_curr_delay_comb fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ i2c_core_delay_comb fext s s' = i2c_core_delay_comb fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_counter_wptr_wrap_cnt fext s s' = fmt_fifo_counter_wptr_wrap_cnt fext s $ fmt_fifo_rvalid fext s s')

                   
∧ (i2c_core_next_state fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_counter_wptr_wrap fext s s' = fmt_fifo_counter_wptr_wrap fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_wdata fext s s' = fmt_fifo_wdata fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_incr_wptr fext s s' = fmt_fifo_incr_wptr fext s $ fmt_fifo_rvalid fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_wvalid fext s s' = fmt_fifo_wvalid fext s $ fmt_fifo_full fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_counter_rptr_wrap_cnt fext s s' = fmt_fifo_counter_rptr_wrap_cnt fext s $ fmt_fifo_full fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_counter_rptr_wrap fext s s' = fmt_fifo_counter_rptr_wrap fext s $ fmt_fifo_full fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_incr_rptr fext s s' = fmt_fifo_incr_rptr fext s $ fmt_fifo_full fext s s')
                 
∧ (i2c_core_next_state fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_full fext s s')
∧ (fmt_fifo_empty fext s $ fmt_fifo_rready fext s s' = fmt_fifo_rready fext s $ fmt_fifo_empty fext s s')

∧ (i2c_core_next_state fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ i2c_core_next_state fext s s')
∧ (counter_gt_one_comb fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ counter_gt_one_comb fext s s')
∧ (fifo_depth fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fifo_depth fext s s')
∧ (fmt_fifo_flag_read_bytes fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_flag_read_bytes fext s s')
∧ (fmt_fifo_flag_stop_after fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_flag_stop_after fext s s')
∧ (fmt_fifo_flag_start_before fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_flag_start_before fext s s')
∧ (fmt_fifo_rvalid fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_rvalid fext s s')
∧ (fmt_fifo_full fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_full fext s s')
∧ (fmt_fifo_empty fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_empty fext s s')
∧ (fmt_fifo_rdata fext s $ fmt_fifo_reset fext s s' = fmt_fifo_reset fext s $ fmt_fifo_rdata fext s s')

Proof
  rw [i2c_core_read_byte_clr_comb_def, i2c_core_shift_data_en_comb_def, counter_gt_one_comb_def, fifo_depth_def,
      i2c_core_next_byte_index_comb_def, i2c_core_byte_decr_comb_def, i2c_core_byte_num_comb_def, i2c_core_byte_clr_comb_def,
      i2c_core_next_counter_def, i2c_core_next_stretch_idle_cnt_def, i2c_core_next_scl_rx_val_comb_def, i2c_core_scl_d_comb_def,
      i2c_core_stretch_en_comb_def, bit_decr_def, bit_clr_def, req_restart_def, fmt_byte_def, fmt_fifo_flag_nak_ok_def,
      fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def, fmt_fifo_flag_start_before_def, fmt_fifo_rvalid_def,
      i2c_core_log_stop_comb_def, i2c_core_log_start_comb_def, i2c_core_load_tcount_comb_def, i2c_core_delay_comb_def,
      fmt_fifo_counter_wptr_wrap_cnt_def, fmt_fifo_counter_wptr_wrap_def, fmt_fifo_wdata_def, fmt_fifo_incr_wptr_def,
      fmt_fifo_full_def, fmt_fifo_wvalid_def, fmt_fifo_counter_rptr_wrap_cnt_def, fmt_fifo_counter_rptr_wrap_def,
      fmt_fifo_incr_rptr_def, fmt_fifo_empty_def, fmt_fifo_rready_def, fmt_fifo_rdata_def, fmt_fifo_reset_def]
  >> fs [ite_rec_sel, next_state_disjoint]
  >> ( rewrite_tac [i2c_core_curr_delay_comb_def, i2c_core_next_state_def] >> rw [fupd_ite])
QED
        
Theorem next_state_i2c_core_combs:
  (procs i2c_core_combs fext s s').next_state =
  (i2c_core_next_state fext s
     (counter_gt_one_comb fext s
        (fifo_depth fext s
           (fmt_fifo_flag_read_bytes fext s
              (fmt_fifo_flag_stop_after fext s
                 (fmt_fifo_flag_start_before fext s
                    (fmt_fifo_rvalid fext s
                       (fmt_fifo_full fext s
                          (fmt_fifo_empty fext s (fmt_fifo_rdata fext s s')))))))))).next_state         
Proof
  rw [i2c_core_combs_def, procs_def, next_state_comb_access, commute_with_next_state, next_state_commute_curr_delay_comb ]
QED

Theorem simp_rvalid:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).fmt_fifo.rvalid
  =
  (fmt_fifo_rvalid fext s $ fmt_fifo_empty fext s s').fmt_fifo.rvalid
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED

Theorem simp_read_bytes:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.read_bytes
  =
  ( fmt_fifo_flag_read_bytes fext s
  $ fmt_fifo_rvalid fext s
  $ fmt_fifo_empty fext s
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.read_bytes
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED

Theorem simp_start_before:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.start_before
  =
  ( fmt_fifo_flag_start_before fext s
  $ fmt_fifo_rvalid fext s
  $ fmt_fifo_empty fext s
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.start_before
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED

Theorem simp_stop_after:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.stop_after
  =
  ( fmt_fifo_flag_stop_after fext s
  $ fmt_fifo_rvalid fext s
  $ fmt_fifo_empty fext s
  $ fmt_fifo_rdata fext s s'
  ).fmt_flag.stop_after
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED
        
Theorem simp_cnt_gt_one:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).cnt_gt_one
  =
  (counter_gt_one_comb fext s s').cnt_gt_one
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED

Theorem simp_depth:
  ( counter_gt_one_comb fext s
  $ fifo_depth fext s 
  $ fmt_fifo_flag_read_bytes fext s 
  $ fmt_fifo_flag_stop_after fext s 
  $ fmt_fifo_flag_start_before fext s 
  $ fmt_fifo_rvalid fext s 
  $ fmt_fifo_full fext s 
  $ fmt_fifo_empty fext s 
  $ fmt_fifo_rdata fext s s'
  ).fmt_fifo.depth
  =
  (fifo_depth fext s $ fmt_fifo_full fext s s').fmt_fifo.depth
Proof
  rw [counter_gt_one_comb_def, fifo_depth_def, ite_rec_sel, fmt_fifo_flag_read_bytes_def, fmt_fifo_flag_stop_after_def,
      fmt_fifo_flag_start_before_def, fmt_fifo_full_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def, fmt_fifo_rdata_def]
QED

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

Theorem fsm_state_comb_access:
  ((next_trans_started_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((next_pend_restart_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((hw2reg_intr_state_cmd_complete_d_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((hw2reg_intr_state_cmd_complete_de_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((next_intr_nak_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((hw2reg_intr_state_nak_de_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_counter_wptr_wrap_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_incr_wptr_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_full_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_wdata_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_wvalid_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_counter_rptr_wrap_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_incr_rptr_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_empty_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_rready_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_rdata_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_rx_fifo_reset_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_sda_rx_val_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_shift_data_en_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_read_byte_clr_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_byte_index_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_byte_num_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_byte_decr_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_byte_clr_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_counter fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_stretch_idle_cnt fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_scl_rx_val_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_scl_d_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_stretch_en_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((bit_decr fext s s').fsm_state = s'.fsm_state)
  ∧ ((bit_clr fext s s').fsm_state = s'.fsm_state)
  ∧ ((req_restart fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_byte fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_flag_nak_ok fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_flag_read_bytes fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_flag_stop_after fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_flag_start_before fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_log_stop_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_log_start_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_load_tcount_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_curr_delay_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_delay_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_counter_wptr_wrap_cnt fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_counter_wptr_wrap fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_wdata fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_incr_wptr fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_full fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_wvalid fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_counter_rptr_wrap_cnt fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_counter_rptr_wrap fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_incr_rptr fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_rready fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_reset fext s s').fsm_state = s'.fsm_state)
  ∧ ((i2c_core_next_state fext s s').fsm_state = s'.fsm_state)
  ∧ ((counter_gt_one_comb fext s s').fsm_state = s'.fsm_state)
  ∧ ((fifo_depth fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_rvalid fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_empty fext s s').fsm_state = s'.fsm_state)
  ∧ ((fmt_fifo_rdata fext s s').fsm_state = s'.fsm_state)
Proof
  rw [next_trans_started_comb_def, next_pend_restart_comb_def, hw2reg_intr_state_cmd_complete_d_comb_def,
      hw2reg_intr_state_cmd_complete_de_comb_def, next_intr_nak_comb_def, hw2reg_intr_state_nak_de_comb_def,
      i2c_core_rx_fifo_counter_wptr_wrap_cnt_comb_def, i2c_core_rx_fifo_counter_wptr_wrap_comb_def,
      i2c_core_rx_fifo_incr_wptr_comb_def, i2c_core_rx_fifo_full_comb_def, i2c_core_rx_fifo_wdata_comb_def,
      i2c_core_rx_fifo_wvalid_comb_def, i2c_core_rx_fifo_counter_rptr_wrap_cnt_comb_def,
      i2c_core_rx_fifo_counter_rptr_wrap_comb_def, i2c_core_rx_fifo_incr_rptr_comb_def,
      i2c_core_rx_fifo_empty_comb_def, i2c_core_rx_fifo_rready_comb_def, i2c_core_rx_fifo_rdata_comb_def,
      i2c_core_rx_fifo_reset_comb_def, i2c_core_next_sda_rx_val_comb_def, i2c_core_shift_data_en_comb_def,
      i2c_core_read_byte_clr_comb_def, i2c_core_next_byte_index_comb_def, i2c_core_byte_num_comb_def,
      i2c_core_byte_decr_comb_def, i2c_core_byte_clr_comb_def, i2c_core_next_counter_def,
      i2c_core_next_stretch_idle_cnt_def, i2c_core_next_scl_rx_val_comb_def, i2c_core_scl_d_comb_def,
      i2c_core_stretch_en_comb_def, bit_decr_def, bit_clr_def, req_restart_def, fmt_byte_def,
      fmt_fifo_flag_nak_ok_def, i2c_core_log_stop_comb_def, i2c_core_log_start_comb_def,
      i2c_core_load_tcount_comb_def, i2c_core_curr_delay_comb_def, i2c_core_delay_comb_def,
      fmt_fifo_counter_wptr_wrap_cnt_def, fmt_fifo_counter_wptr_wrap_def, fmt_fifo_wdata_def,
      fmt_fifo_incr_wptr_def, fmt_fifo_full_def, fmt_fifo_wvalid_def, fmt_fifo_counter_rptr_wrap_cnt_def,
      fmt_fifo_counter_rptr_wrap_def, fmt_fifo_incr_rptr_def, fmt_fifo_rready_def, fmt_fifo_reset_def,
      i2c_core_next_state_def, counter_gt_one_comb_def, fifo_depth_def, fmt_fifo_flag_read_bytes_def,
      fmt_fifo_flag_stop_after_def, fmt_fifo_flag_start_before_def, fmt_fifo_rvalid_def, fmt_fifo_empty_def,
      fmt_fifo_rdata_def
      ]
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

Theorem i2c_core_ffs1_rx_fifo:
  ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((byte_index_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((pend_restart_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr) 
∧ ((bit_index_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.incr_wptr = s'.rx_fifo.incr_wptr)

∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((byte_index_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((pend_restart_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile) 
∧ ((bit_index_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)
∧ ((i2c_core_counter_ff fext s s').rx_fifo_regfile = s'.rx_fifo_regfile)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((byte_index_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((pend_restart_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata) 
∧ ((bit_index_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.wdata = s'.rx_fifo.wdata)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((byte_index_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((pend_restart_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset) 
∧ ((bit_index_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.reset = s'.rx_fifo.reset)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((byte_index_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((pend_restart_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap) 
∧ ((bit_index_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.counter.rptr_wrap = s'.rx_fifo.counter.rptr_wrap)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((byte_index_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((pend_restart_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt) 
∧ ((bit_index_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.counter.rptr_wrap_cnt = s'.rx_fifo.counter.rptr_wrap_cnt)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((byte_index_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((pend_restart_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr) 
∧ ((bit_index_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.wptr = s'.rx_fifo.wptr)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((byte_index_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((pend_restart_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap) 
∧ ((bit_index_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.counter.wptr_wrap = s'.rx_fifo.counter.wptr_wrap)

∧ ((i2c_core_rx_fifo_regfile fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((i2c_core_rx_fifo_rptr_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((byte_index_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((pend_restart_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt) 
∧ ((bit_index_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((fmt_fifo_wptr_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((i2c_core_rx_fifo_wptr_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((fmt_fifo_regfile_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((fmt_fifo_rptr_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((i2c_core_stretch_idle_cnt_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)
∧ ((i2c_core_counter_ff fext s s').rx_fifo.counter.wptr_wrap_cnt = s'.rx_fifo.counter.wptr_wrap_cnt)

                        
Proof
  rw [i2c_core_rx_fifo_rptr_ff_def, byte_index_ff_def, pend_restart_ff_def, bit_index_ff_def,
      fmt_fifo_wptr_ff_def, i2c_core_rx_fifo_wptr_ff_def, fmt_fifo_regfile_ff_def,
      fmt_fifo_rptr_ff_def, i2c_core_stretch_idle_cnt_ff_def, i2c_core_counter_ff_def, i2c_core_rx_fifo_regfile_def]
QED
        
Theorem cstate_rx_fifo_regfile:
  (procs i2c_core_ffs1 fext s s').rx_fifo_regfile =
  (if s'.rx_fifo.incr_wptr then
     s'.rx_fifo_regfile ⦇((5 >< 0) s.rx_fifo.wptr :word6) ↦ s'.rx_fifo.wdata ⦈
   else s'.rx_fifo_regfile)         
Proof
  simp [i2c_core_ffs1_def, procs_def, i2c_core_ff_def, i2c_core_rx_fifo_regfile_def, i2c_core_ffs1_rx_fifo, ite_rec_sel]
QED

Theorem cstate_rx_fifo_rptr:
  (procs i2c_core_ffs1 fext s s').rx_fifo.rptr =
  if s'.rx_fifo.reset then 0w
  else if s'.rx_fifo.counter.rptr_wrap then
    s'.rx_fifo.counter.rptr_wrap_cnt
  else s.rx_fifo.rptr + 1w         
Proof
  simp [i2c_core_ffs1_def, procs_def, i2c_core_ff_def, i2c_core_rx_fifo_regfile_def,
        i2c_core_ffs1_rx_fifo, ite_rec_sel,  i2c_core_rx_fifo_rptr_ff_def]        
QED

Theorem cstate_rx_fifo_wptr:
  (procs i2c_core_ffs1 fext s s').rx_fifo.wptr =
  if s'.rx_fifo.reset then 0w
  else if s'.rx_fifo.counter.wptr_wrap then
    s'.rx_fifo.counter.wptr_wrap_cnt
  else s.rx_fifo.wptr + 1w         
Proof
  simp [i2c_core_ffs1_def, procs_def, i2c_core_ff_def, i2c_core_ffs1_rx_fifo, i2c_core_rx_fifo_wptr_ff_def,
        ite_rec_sel]
QED

(* prove that i2c_tick (HOL4) simulates i2c_core (shallowly embedded)
 - provide a relation ‘core_sim_rel’ (relate abstract and concrete states)
 *)

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
     drule_then assume_tac cheshire_req_fsm_state
     >> drule_then assume_tac i2c_tick_fsm_state
     >> simp [Abbr ‘cstate1_seq’, cstate_fsm_state, Abbr ‘cstate’,
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
     rewrite_tac [i2c_tick_rx_fifo, mstate_with_fnums]
     >> rpt IF_CASES_TAC
     >> rpt $ qpat_x_assum ‘_ ∧ _’ strip_assume_tac
     >> simp [Abbr ‘cstate1_seq’,i2c_core_ffs1_rx_fifo, cstate_rx_fifo_regfile, cstate_rx_fifo_rptr, cstate_rx_fifo_wptr]
     >> cheat      
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
