(* A library for flattening a shallowly-embedded Verilog process (resolving the
 * value of each field, and proving that it returns the input record with those
 * fields updated to their new values). *)
structure shallowFlattenLib =
struct

open HolKernel Parse boolLib bossLib;
open combinSyntax TypeBase;

val COND_2RAND = Q.prove (`
  !f b x y z w.
  f (if b then x else z) (if b then y else w) =
  (if b then f x y else f z w)
`,
  Cases_on `b` >> simp []
);

val COND_2RAND_K = Q.prove (`
  !f b x y z w.
  f (K (if b then x else z)) (if b then y else w) =
  (if b then f (K x) y else f (K z) w)
`,
  Cases_on `b` >> simp []
);

(* A version of TypeBase.fields_of which uses the concrete input type rather
 * than the generalised one. *)
fun fields_of_concrete (rty: hol_type) = map (fn (name, {accessor, fupd, ty}) => let
  val accessor' = inst (match_type (accessor |> type_of |> dom_rng |> fst) rty) accessor;
  val fupd' = inst (match_type (fupd |> type_of |> dom_rng |> snd) (rty --> rty)) fupd;
  val ty' = accessor' |> type_of |> dom_rng |> snd;
in
  (name, {accessor = accessor', fupd = fupd', ty = ty'})
end) (fields_of rty)

fun prove_identity_fupds (rty: hol_type) = let
  val fields = fields_of_concrete rty;
  val accessors = accessors_of rty;
  val updates = updates_of rty;
  val nchotomy = nchotomy_of rty;
in
  LIST_CONJ (map (fn ((_, {accessor, fupd, ty}), accessor_thm, update_thm) =>
    prove (``!r. ^fupd (K (^accessor r)) r = r``,
      gen_tac
      >> qspec_then `r` strip_assume_tac nchotomy
      >> first_x_assum (fn thm => pure_rewrite_tac [thm, accessor_thm, update_thm, combinTheory.K_THM])
      >> REFL_TAC)
  ) (Portable.zip3 (fields, accessors, updates)))
end

fun FORCE_FUPD_CONV ({accessor, fupd, ...}: rcd_fieldinfo) (tm: term) = let
  val (f, _) = strip_comb tm;
in
  if term_eq f fupd then
    raise UNCHANGED
  else
    prove (``^tm = ^fupd (K (^accessor ^tm)) ^tm``, pure_rewrite_tac [prove_identity_fupds (type_of tm)] >> REFL_TAC)
end

(* TODO: handle literal_case too *)
fun COND_RECORD_CONV tm = DEPTH_CONV (fn tm =>
  if is_cond tm andalso TypeBase.is_record_type (type_of tm) then let
    val fields = type_of tm |> fields_of_concrete;
    val (cond, thn, els) = dest_cond tm;
    val (thn_f, thn_args) = strip_comb thn;
    val (els_f, els_args) = strip_comb els;
    val info = get_first (fn (_, info as {fupd, ...}) =>
      if term_eq thn_f fupd orelse term_eq els_f fupd then
        SOME info
      else
        NONE
    ) fields;
  in case info of
      SOME (info as {fupd, ...}) =>
        (LAND_CONV (QCONV (FORCE_FUPD_CONV info))
        THENC RAND_CONV (QCONV (FORCE_FUPD_CONV info))
        THENC (if (not $ term_eq thn_f fupd orelse is_K_1 (el 1 thn_args))
          andalso (not $ term_eq els_f fupd orelse is_K_1 (el 1 els_args))
        then
          REWR_CONV (GSYM COND_2RAND_K)
        else
          REWR_CONV (GSYM COND_2RAND))
        (* Make sure the new ifs we've just generated are covered too (and also clean up
         * any needless ones). *)
        THENC (LAND_CONV (REWR_CONV COND_ID ORELSEC COND_RECORD_CONV))
        THENC (RAND_CONV (REWR_CONV COND_ID ORELSEC COND_RECORD_CONV))) tm
    | NONE => raise UNCHANGED
  end else
    raise UNCHANGED) tm

end
