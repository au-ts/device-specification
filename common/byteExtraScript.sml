open HolKernel Parse boolLib bossLib;
open wordsLib;
open arithmeticTheory byteTheory dividesTheory fcpTheory listTheory wordsTheory;

val _ = new_theory "byteExtra";

Theorem word_to_bytes_aux_length:
  LENGTH (word_to_bytes_aux n _ _) = n
Proof
  Induct_on ‘n’
  >> simp [word_to_bytes_aux_def]
QED

Theorem word_to_bytes_length:
  LENGTH (word_to_bytes (w: 'a word) be) = dimindex (:'a) DIV 8
Proof
  simp [word_to_bytes_def, word_to_bytes_aux_length]
QED

Theorem MIN_VAL_1[simp]:
  a <= b ==> MIN a b = a
Proof
  simp [MIN_DEF]
QED

Theorem MIN_VAL_2[simp]:
  b <= a ==> MIN a b = b
Proof
  simp [MIN_DEF]
QED

Theorem MAX_VAL_1[simp]:
  a <= b ==> MAX a b = b
Proof
  simp [MAX_DEF]
QED

Theorem MAX_VAL_2[simp]:
  b <= a ==> MAX a b = a
Proof
  simp [MAX_DEF]
QED

Theorem word_slice_alt_or[simp]:
  word_slice_alt h l (a || b) = word_slice_alt h l a || word_slice_alt h l b
Proof
  (* FCP_ss is broken, so we have to manually write the theorems it contains. *)
  simp [word_slice_alt_def, word_or_def, FCP_BETA, FCP_ETA, CART_EQ, LEFT_AND_OVER_OR]
QED

Theorem word_slice_alt_lsl:
  word_slice_alt h l (w << n) = word_slice_alt (h - n) (l - n) w << n
Proof
  simp [word_slice_alt_def, word_lsl_def, FCP_BETA, FCP_ETA, CART_EQ]
  >> strip_tac
  >> Cases_on ‘i < n’
  >- simp []
  >- (Cases_on ‘0 < h - n’
      >> simp [])
QED

Theorem word_slice_alt_w2w_1:
  l >= dimindex (:'a)
  ==> word_slice_alt h l (w2w (w: 'a word)) = 0w
Proof
  simp [word_slice_alt_def, w2w, FCP_BETA, FCP_ETA, CART_EQ, word_0, Cong OR_CONG]
QED

Theorem word_slice_alt_w2w_2:
  h >= dimindex (:'a)
  ==> word_slice_alt h 0 (w2w (w: 'a word)) = w2w w
Proof
  simp [word_slice_alt_def, w2w, FCP_BETA, FCP_ETA, CART_EQ]
  >> simp [Cong AND_CONG]
QED

Theorem word_slice_alt_h_zero[simp]:
  word_slice_alt 0 l w = 0w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ, word_0]
QED

Theorem word_slice_alt_lsl_w2w_1:
  h <= s \/ l >= s + dimindex (:'a)
  ==> word_slice_alt h l (w2w (w: 'a word) << s) = 0w
Proof
  strip_tac
  >- (‘h - s = 0’ by simp []
      >> simp [word_slice_alt_lsl])
  >- (‘l - s >= dimindex (:'a)’ by simp []
      >> simp [word_slice_alt_lsl, word_slice_alt_w2w_1, SF WORD_ss])
QED

Theorem word_slice_alt_lsl_w2w_2:
  l <= s /\ s + dimindex (:'a) <= h
  ==> word_slice_alt h l (w2w (w: 'a word) << s) = w2w w << s
Proof
  strip_tac
  >> ‘h - s >= dimindex (:'a)’ by simp []
  >> ‘l - s = 0’ by simp []
  >> simp [word_slice_alt_lsl, word_slice_alt_w2w_2]
QED

Theorem word_slice_alt_word_slice_alt:
  word_slice_alt h1 l1 (word_slice_alt h2 l2 w) = word_slice_alt (MIN h1 h2) (MAX l1 l2) w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ]
  >> decide_tac
QED

Theorem word_slice_alt_dimindex:
  word_slice_alt (MIN h (dimindex (:'a))) l (w: 'a word) = word_slice_alt h l w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ]
QED

Theorem word_slice_alt_empty[simp]:
  h <= l ==> word_slice_alt h l w = 0w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ, word_0]
  >> rpt strip_tac
  >> spose_not_then assume_tac
  >> simp []
QED

Theorem word_slice_alt_full[simp]:
  dimindex (:'a) <= h ==> word_slice_alt h 0 (w: 'a word) = w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ]
QED

Theorem word_slice_alt_adjacent:
  word_slice_alt a b w || word_slice_alt b c w = word_slice_alt (MAX a b) (MIN b c) w
Proof
  simp [word_slice_alt_def, FCP_BETA, FCP_ETA, CART_EQ, word_or_def]
  >> rpt strip_tac
  >> Cases_on ‘i >= b’
  >> simp []
QED


Theorem word_slice_alt_set_byte_1:
  h <= byte_index a be \/ l >= byte_index a be + 8
  ==> word_slice_alt h l (set_byte a b w be) = word_slice_alt h l w
Proof
  strip_tac
  >> simp [set_byte_def]
  >- simp [word_slice_alt_lsl_w2w_1, word_slice_alt_word_slice_alt]
  >- simp [word_slice_alt_lsl_w2w_1, word_slice_alt_word_slice_alt, word_slice_alt_dimindex]
QED

Theorem word_slice_alt_set_byte_2:
  l <= byte_index a be /\ byte_index a be + 8 <= h
  ==> word_slice_alt h l (set_byte a b w be) = set_byte a b (word_slice_alt h l w) be
Proof
  simp [set_byte_def, word_slice_alt_lsl_w2w_2, word_slice_alt_word_slice_alt, MIN_COMM]
QED

Theorem lt_or_gt:
  (a: num) <> b ==> a < b \/ a > b
Proof
  simp []
QED

Theorem byte_index_lt_or_gt:
  w2n (n: 'a word) MOD (dimindex (:'a) DIV 8) <> w2n (m: 'a word) MOD (dimindex (:'a) DIV 8)
  /\ dimindex (:'a) DIV 8 > 0
  ==> byte_index m be >= byte_index n be + 8 \/ byte_index m be + 8 <= byte_index n be
Proof
  strip_tac
  >> drule lt_or_gt
  >> strip_tac
  >> Cases_on ‘be’
  >> simp [byte_index_def]
  >> qabbrev_tac ‘bytes = dimindex (:'a) DIV 8’
  >> ‘w2n m MOD bytes < bytes’ by simp []
  >> ‘w2n n MOD bytes < bytes’ by simp []
  >> simp []
QED

Theorem set_byte_independent:
  w2n n MOD (dimindex (:'a) DIV 8) <> w2n m MOD (dimindex (:'a) DIV 8)
  /\ dimindex (:'a) DIV 8 > 0
  ==> set_byte n x (set_byte m y (w: 'a word) be) be = set_byte m y (set_byte n x w be) be
Proof
  strip_tac
  >> drule_all_then (qspec_then ‘be’ assume_tac) byte_index_lt_or_gt
  >> rw []
  >> simp [Once set_byte_def, word_slice_alt_set_byte_1]
  >> simp [Once set_byte_def, word_slice_alt_set_byte_1]
  >> simp [Once set_byte_def, word_slice_alt_set_byte_1]
  >> simp [Once set_byte_def, word_slice_alt_set_byte_1]
  >> simp [word_slice_alt_word_slice_alt]
  >> qspecl_then [‘1’, ‘dimindex (:'a)’, ‘8’] assume_tac X_LE_DIV
  >> ‘8 <= dimindex (:'a)’ by simp []
  >> simp [byte_index_offset, word_slice_alt_lsl_w2w_2, MIN_COMM]
QED

Theorem w2n_add_2:
  w2n (a: 'a word) + w2n b < dimword (:'a) ==> w2n (a + b) = w2n a + w2n b
Proof
  simp [word_add_def]
QED

Theorem word_of_bytes_SNOC:
  !n. LENGTH bs < dimindex (:'a) DIV 8 /\ w2n (n: 'a word) + LENGTH bs < dimword (:'a)
      ==> word_of_bytes be n (SNOC b bs) = set_byte (n + n2w (LENGTH bs)) b (word_of_bytes be n bs) be
Proof
  Induct_on ‘bs’
  >- simp [word_of_bytes_def]
  >- (rpt strip_tac
      >> last_x_assum (qspec_then ‘n + 1w’ mp_tac)
      >> impl_tac
      (* Seems like only fs will rewrite assumptions. *)
      >- fs [w2n_add_2]
      >- (fs [word_of_bytes_def, ADD1, GSYM word_add_n2w]
          >> strip_tac
          >> irule set_byte_independent
          >> simp [w2n_add_2]
          >> ‘0 < dimindex (:'a) DIV 8’ by simp []
          >> dxrule_then (qspecl_then [‘LENGTH bs + 1’, ‘0’, ‘w2n n’] assume_tac) ADD_MOD
          >> simp [Once EQ_SYM_EQ]
          >> fs []))
QED

Theorem word_of_bytes_0_SNOC:
  LENGTH bs < dimindex (:'a) DIV 8
  ==> word_of_bytes be 0w (SNOC b bs): 'a word = set_byte (n2w (LENGTH bs)) b (word_of_bytes be 0w bs) be
Proof
  strip_tac
  >> ‘dimindex (:'a) DIV 8 <= dimindex (:'a)’ by simp [DIV_LESS_EQ]
  >> simp [dimindex_lt_dimword, LESS_LESS_EQ_TRANS, LESS_TRANS, word_of_bytes_SNOC]
QED

Theorem word_bits_dimindex:
  (MIN h (dimindex (:'a) - 1) -- l) (w: 'a word) = (h -- l) w
Proof
  Cases_on ‘h > dimindex (:'a) - 1’
  >- simp [WORD_BITS_MIN_HIGH]
  >- simp []
QED

Theorem word_bits_lsr_2:
  (h -- l) (w >>> n) = (h + n -- l + n) w
Proof
  simp [word_lsr_n2w, WORD_BITS_COMP_THM, MIN_COMM, word_bits_dimindex]
QED

Theorem word_of_bytes_word_to_bytes_aux_le:
  n <= dimindex (:'a) DIV 8 /\ 8 <= dimindex (:'a)
  ==> word_of_bytes F 0w (word_to_bytes_aux n (w: 'a word) F) = word_slice_alt (8 * n) 0 w
Proof
  Induct_on ‘n’
  >- simp [word_to_bytes_aux_def, word_of_bytes_def]
  >- (strip_tac
      >> ‘dimindex (:'a) DIV 8 <= dimindex (:'a)’ by simp [DIV_LESS_EQ]
      >> ‘n < dimword (:'a)’ by simp [dimindex_lt_dimword, LESS_TRANS, LESS_LESS_EQ_TRANS]
      (* The n < dimword (:'a) happens to be needed for reasons other than word_of_bytes_SNOC, so there's no point in switching to word_of_bytes_0_SNOC. *)
      >> simp [word_to_bytes_aux_def, GSYM SNOC_APPEND, word_to_bytes_aux_length, word_of_bytes_SNOC, set_byte_def, get_byte_def, word_slice_alt_word_slice_alt, byte_index_def, w2w_w2w, word_bits_lsr_2, GSYM WORD_SLICE_THM]
      >> qspecl_then [‘SUC n’, ‘dimindex (:'a)’, ‘8’] assume_tac X_LE_DIV
      >> rfs [GSYM word_slice_alt_word_slice, word_slice_alt_adjacent, ADD1]
      >> simp [GSYM ADD1, MULT_CLAUSES])
QED

(* TODO: big-endian *)
(* The fact that the divides 8 (dimindex (:'a)) is necessary is arguably a bug in word_to_bytes. *)
Theorem word_to_bytes_word_of_bytes_le:
  8 <= dimindex (:'a) /\ divides 8 (dimindex (:'a))
  ==> word_of_bytes F 0w (word_to_bytes (w: 'a word) F) = w
Proof
  simp [word_to_bytes_def, word_of_bytes_word_to_bytes_aux_le, DIVIDES_DIV]
QED

val _ = export_theory ();
