(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*          David Monniaux, CNRS / Verimag                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Additional operations and proofs about IEEE-754 binary
    floating-point numbers, on top of the Flocq library. *)

From Stdlib Require Import Reals SpecFloat ZArith Psatz Bool Eqdep_dec.
From Stdlib Require Znumtheory.
Require Import Core Digits Operations Round Bracket Sterbenz
                          BinarySingleNaN Binary Round_odd.

Require Import Coq.Logic.FunctionalExtensionality.

Local Open Scope Z_scope.


Lemma Znearest_lub :
  forall choice (n : Z) (x : R), (IZR n <= x)%R -> (n <= Znearest choice x)%Z.
Proof.
  intros until x. intro BND.
  pose proof (Zfloor_lub n x BND).
  pose proof (Znearest_ge_floor choice x).
  lia.
Qed.

Lemma Znearest_glb :
  forall choice (n : Z) (x : R), (x <= IZR n)%R -> (Znearest choice x <= n)%Z.
Proof.
  intros until x. intro BND.
  pose proof (Zceil_glb n x BND).
  pose proof (Znearest_le_ceil choice x).
  lia.
Qed.

Lemma Znearest_IZR :
  forall choice n, (Znearest choice (IZR n)) = n.
Proof.
  intros.
  unfold Znearest.
  case Rcompare_spec ; intro ORDER.
  - apply Zfloor_IZR.
  - destruct choice.
    + apply Zceil_IZR.
    + apply Zfloor_IZR.
  - apply Zceil_IZR.
Qed.

Lemma ZnearestE_IZR:
  forall n, (ZnearestE (IZR n)) = n.
Proof.
  apply Znearest_IZR.
Qed.

Lemma Zfloor_opp :
  forall x : R, (Zfloor (- x)) = - (Zceil x).
Proof.
  unfold Zceil, Zfloor.
  intro x.
  rewrite Z.opp_involutive.
  reflexivity.
Qed.

Lemma Zceil_opp :
  forall x : R, (Zceil (- x)) = - (Zfloor x).
Proof.
  unfold Zceil, Zfloor.
  intro x.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma ZnearestE_opp
     : forall x : R, ZnearestE (- x) = - ZnearestE x.
Proof.
  intro.
  rewrite Znearest_opp.
  f_equal.
  f_equal.
  apply functional_extensionality.
  intro.
  rewrite Z.even_opp.
  fold (Z.succ x0).
  rewrite Z.even_succ.
  f_equal.
  apply Z.negb_odd.
Qed.

Lemma Zceil_non_floor:
  forall x : R, (x > IZR(Zfloor x))%R -> Zceil x = Z.succ(Zfloor x).
Proof.
  intros x BETWEEN.
  unfold Z.succ.
  apply Zceil_imp.
  split.
  { rewrite minus_IZR.
    rewrite plus_IZR.
    lra.
  }
  rewrite plus_IZR.
  pose proof (Zfloor_ub x).
  lra.
Qed.

(** more complicated way of proving
Lemma Zceil_non_ceil:
  forall x : R, (x < IZR(Zceil x))%R -> Zceil x = Z.succ(Zfloor x).
Proof.
  intros x BETWEEN.
  unfold Z.succ.
  cut (Zfloor x = (Zceil x) - 1). { intros; lia. }
  apply Zfloor_imp.
  split.
  { rewrite minus_IZR.
    pose proof (Zceil_lb x).
    lra.
  }
  rewrite plus_IZR.
  rewrite minus_IZR.
  lra.
Qed.    

Lemma ZnearestE_opp
     : forall x : R, ZnearestE (- x) = - ZnearestE x.
Proof.
  intro x.
  unfold ZnearestE.
  case (Rcompare_spec (x - IZR (Zfloor x)) (/ 2)); intro CMP.
  - pose proof (Zfloor_lb x) as LB.
    destruct (Rcompare_spec x (IZR (Zfloor x))) as [ ABSURD | EXACT | INEXACT].
    lra.
    { set (n := Zfloor x) in *.
      rewrite EXACT.
      rewrite <- opp_IZR.
      rewrite Zfloor_IZR.
      rewrite opp_IZR.
      rewrite Rcompare_Lt by lra.
      reflexivity.
    }
    rewrite Rcompare_Gt.
    { apply Zceil_opp. }
    rewrite Zfloor_opp.
    rewrite opp_IZR.
    rewrite Zceil_non_floor by assumption.
    unfold Z.succ.
    rewrite plus_IZR.
    lra.
  - rewrite Rcompare_Eq.
    { rewrite Zceil_opp.
      rewrite Zfloor_opp.
      rewrite Z.even_opp.
      rewrite Zceil_non_floor by lra.
      rewrite Z.even_succ.
      rewrite Z.negb_odd.
      destruct (Z.even (Zfloor x)); reflexivity.
    }
    rewrite Zfloor_opp.
    rewrite opp_IZR.
    ring_simplify.
    rewrite Zceil_non_floor by lra.
    unfold Z.succ.
    rewrite plus_IZR.
    lra.
  - rewrite Rcompare_Lt.
    { apply Zfloor_opp. }
    rewrite Zfloor_opp.
    rewrite opp_IZR.
    rewrite Zceil_non_floor by lra.
    unfold Z.succ.
    rewrite plus_IZR.
    lra.
Qed.
 *)

Lemma Znearest_imp2:
  forall choice x, (Rabs (IZR (Znearest choice x) - x) <= /2)%R.
Proof.
  intros.
  unfold Znearest.
  pose proof (Zfloor_lb x) as FL.
  pose proof (Zceil_ub x) as CU.
  pose proof (Zceil_non_floor x) as NF.
  case Rcompare_spec; intro CMP; apply Rabs_le; split; try lra.
  - destruct choice; lra.
  - destruct choice. 2: lra.
    rewrite NF. 2: lra.
    unfold Z.succ. rewrite plus_IZR. lra.
  - rewrite NF. 2: lra.
    unfold Z.succ. rewrite plus_IZR. lra.
Qed.

Theorem Znearest_le
  : forall choice (x y : R), (x <= y)%R -> Znearest choice x <= Znearest choice y.
Proof.
  intros.
  destruct (Z_le_gt_dec (Znearest choice x) (Znearest choice y)) as [LE | GT].
  assumption.
  exfalso.
  assert (1 <= IZR (Znearest choice x) - IZR(Znearest choice y))%R as GAP.
  { rewrite <- minus_IZR.
    apply IZR_le.
    lia.
  }
  pose proof (Znearest_imp2 choice x) as Rx.
  pose proof (Znearest_imp2 choice y) as Ry.
  apply Rabs_le_inv in Rx.
  apply Rabs_le_inv in Ry.
  assert (x = y) by lra.
  subst y.
  lia.
Qed.

Section Extra_ops.

(** [prec] is the number of bits of the mantissa including the implicit one.
    [emax] is the exponent of the infinities.
    Typically p=24 and emax = 128 in single precision. *)

Variable prec emax : Z.
Context (prec_gt_0_ : Prec_gt_0 prec).
Context (prec_lt_emax_ : Prec_lt_emax prec emax).
Notation emin := (emin prec emax).
Notation fexp := (fexp prec emax).
Notation binary_float := (binary_float prec emax).

(** Remarks on [is_finite] *)

Remark is_finite_not_is_nan:
  forall (f: binary_float), is_finite _ _ f = true -> is_nan _ _ f = false.
Proof.
  destruct f; reflexivity || discriminate.
Qed.

Remark is_finite_strict_finite:
  forall (f: binary_float), is_finite_strict _ _ f = true -> is_finite _ _ f = true.
Proof.
  destruct f; reflexivity || discriminate.
Qed.

(** Digression on FP numbers that cannot be [-0.0]. *)

Definition is_finite_pos0 (f: binary_float) : bool :=
  match f with
  | B754_zero _ _ s => negb s
  | B754_infinity _ _ _ => false
  | B754_nan _ _ _ _ _ => false
  | B754_finite _ _ _ _ _ _ => true
  end.

Lemma Bsign_pos0:
  forall x, is_finite_pos0 x = true -> Bsign _ _ x = Rlt_bool (B2R _ _ x) 0%R.
Proof.
  intros. destruct x as [ [] | | | [] ex mx Bx ]; try discriminate; simpl.
- rewrite Rlt_bool_false; auto. lra.
- rewrite Rlt_bool_true; auto. apply F2R_lt_0. compute; auto.
- rewrite Rlt_bool_false; auto.
  assert ((F2R (Float radix2 (Z.pos ex) mx) > 0)%R) by
    ( apply F2R_gt_0; compute; auto ).
  lra.
Qed.

Theorem B2R_inj_pos0:
  forall x y,
  is_finite_pos0 x = true -> is_finite_pos0 y = true ->
  B2R _ _ x = B2R _ _ y ->
  x = y.
Proof.
  intros. apply B2R_Bsign_inj.
  destruct x; reflexivity||discriminate.
  destruct y; reflexivity||discriminate.
  auto.
  rewrite ! Bsign_pos0 by auto. rewrite H1; auto.
Qed.

(** ** Decidable equality *)

Definition Beq_dec: forall (f1 f2: binary_float), {f1 = f2} + {f1 <> f2}.
Proof.
  assert (UIP_bool: forall (b1 b2: bool) (e e': b1 = b2), e = e').
  { intros. apply UIP_dec. decide equality. }
  Ltac try_not_eq := try solve [right; congruence].
  destruct f1 as [s1|s1|s1 p1 H1|s1 m1 e1 H1], f2 as [s2|s2|s2 p2 H2|s2 m2 e2 H2];
  try destruct s1; try destruct s2;
  try solve [left; auto]; try_not_eq.
  destruct (Pos.eq_dec p1 p2); try_not_eq;
    subst; left; f_equal; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec p1 p2); try_not_eq;
    subst; left; f_equal; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec m1 m2); try_not_eq;
  destruct (Z.eq_dec e1 e2); try solve [right; intro H; inversion H; congruence];
  subst; left; f_equal; apply UIP_bool.
  destruct (Pos.eq_dec m1 m2); try_not_eq;
  destruct (Z.eq_dec e1 e2); try solve [right; intro H; inversion H; congruence];
  subst; left; f_equal; apply UIP_bool.
Defined.

(** ** Conversion from an integer to a FP number *)

(** Integers that can be represented exactly as FP numbers. *)

Definition integer_representable (n: Z): Prop :=
  Z.abs n <= 2^emax - 2^(emax - prec) /\ generic_format radix2 fexp (IZR n).

Lemma int_upper_bound_eq: 2^emax - 2^(emax - prec) = (2^prec - 1) * 2^(emax - prec).
Proof.
  red in prec_gt_0_, prec_lt_emax_.
  ring_simplify.
  rewrite <- (Zpower_plus radix2) by lia.
  now replace (emax - prec + prec)%Z with emax by ring.
Qed.

Lemma integer_representable_n2p:
  forall n p,
  -2^prec < n < 2^prec -> 0 <= p -> p <= emax - prec ->
  integer_representable (n * 2^p).
Proof.
  intros; split.
- red in prec_gt_0_, prec_lt_emax_. replace (Z.abs (n * 2^p)) with (Z.abs n * 2^p).
  rewrite int_upper_bound_eq.
  apply Zmult_le_compat. lia. apply (Zpower_le radix2); lia.
  lia. apply (Zpower_ge_0 radix2).
  rewrite Z.abs_mul. f_equal. rewrite Z.abs_eq. auto. apply (Zpower_ge_0 radix2).
- apply generic_format_FLT. exists (Float radix2 n p).
  unfold F2R; simpl.
  rewrite <- IZR_Zpower by auto. apply mult_IZR.
  simpl; lia.
  unfold emin, Fexp; red in prec_gt_0_, prec_lt_emax_; lia.
Qed.

Lemma integer_representable_2p:
  forall p,
  0 <= p <= emax - 1 ->
  integer_representable (2^p).
Proof.
  intros; split.
- red in prec_gt_0_.
  rewrite Z.abs_eq by (apply (Zpower_ge_0 radix2)).
  apply Z.le_trans with (2^(emax-1)).
  apply (Zpower_le radix2); lia.
  assert (2^emax = 2^(emax-1)*2).
  { change 2 with (2^1) at 3. rewrite <- (Zpower_plus radix2) by lia.
    f_equal. lia. }
  assert (2^(emax - prec) <= 2^(emax - 1)).
  { apply (Zpower_le radix2). lia. }
  lia.
- red in prec_gt_0_, prec_lt_emax_.
  apply generic_format_FLT. exists (Float radix2 1 p).
  unfold F2R; simpl.
  rewrite Rmult_1_l. rewrite <- IZR_Zpower. auto. lia.
  simpl Z.abs. change 1 with (2^0). apply (Zpower_lt radix2). lia. auto.
  unfold emin, Fexp; lia.
Qed.

Lemma integer_representable_opp:
  forall n, integer_representable n -> integer_representable (-n).
Proof.
  intros n (A & B); split. rewrite Z.abs_opp. auto.
  rewrite opp_IZR. apply generic_format_opp; auto.
Qed.

Lemma integer_representable_n2p_wide:
  forall n p,
  -2^prec <= n <= 2^prec -> 0 <= p -> p < emax - prec ->
  integer_representable (n * 2^p).
Proof.
  intros. red in prec_gt_0_.
  destruct (Z.eq_dec n (2^prec)); [idtac | destruct (Z.eq_dec n (-2^prec))].
- rewrite e. rewrite <- (Zpower_plus radix2) by lia.
  apply integer_representable_2p. lia.
- rewrite e. rewrite <- Zopp_mult_distr_l. apply integer_representable_opp.
  rewrite <- (Zpower_plus radix2) by lia.
  apply integer_representable_2p. lia.
- apply integer_representable_n2p; lia.
Qed.

Lemma integer_representable_n:
  forall n, -2^prec <= n <= 2^prec -> integer_representable n.
Proof.
  red in prec_gt_0_, prec_lt_emax_. intros.
  replace n with (n * 2^0) by (change (2^0) with 1; ring).
  apply integer_representable_n2p_wide. auto. lia. lia.
Qed.

Lemma round_int_no_overflow:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) ->
  (Rabs (round radix2 fexp (round_mode mode_NE) (IZR n)) < bpow radix2 emax)%R.
Proof.
  intros. red in prec_gt_0_, prec_lt_emax_.
  rewrite <- round_NE_abs.
  apply Rle_lt_trans with (IZR (2^emax - 2^(emax-prec))).
  apply round_le_generic. apply fexp_correct; auto. apply valid_rnd_N.
  apply generic_format_FLT. exists (Float radix2 (2^prec-1) (emax-prec)).
  rewrite int_upper_bound_eq. unfold F2R; simpl.
  rewrite <- IZR_Zpower by lia. rewrite <- mult_IZR. auto.
  assert (0 < 2^prec) by (apply (Zpower_gt_0 radix2); lia).
  unfold Fnum; simpl; zify; lia.
  unfold emin, Fexp; lia.
  rewrite <- abs_IZR. apply IZR_le. auto.
  rewrite <- IZR_Zpower by lia. apply IZR_lt. simpl.
  assert (0 < 2^(emax-prec)) by (apply (Zpower_gt_0 radix2); lia).
  lia.
  apply fexp_correct. auto.
Qed.

(** Conversion from an integer.  Round to nearest. *)

Definition BofZ (n: Z) : binary_float :=
  binary_normalize prec emax _ _ mode_NE n 0 false.

Theorem BofZ_correct:
  forall n,
  if Rlt_bool (Rabs (round radix2 fexp (round_mode mode_NE) (IZR n))) (bpow radix2 emax)
  then
    B2R prec emax (BofZ n) = round radix2 fexp (round_mode mode_NE) (IZR n) /\
    is_finite _ _ (BofZ n) = true /\
    Bsign prec emax (BofZ n) = Z.ltb n 0
  else
    B2FF prec emax (BofZ n) = binary_overflow prec emax mode_NE (Z.ltb n 0).
Proof.
  intros.
  generalize (binary_normalize_correct prec emax _ _ mode_NE n 0 false).
  fold emin; fold fexp; fold (BofZ n).
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n).
  destruct Rlt_bool.
- intros (A & B & C). split; [|split].
  + auto.
  + auto.
  + rewrite C. rewrite Rcompare_IZR.
    unfold Z.ltb. auto.
- intros A; rewrite A. f_equal.
  generalize (Z.ltb_spec n 0); intros SPEC; inversion SPEC.
  apply Rlt_bool_true; apply IZR_lt; auto.
  apply Rlt_bool_false; apply IZR_le; auto.
- unfold F2R; simpl. ring.
Qed.

Theorem BofZ_finite:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) ->
  B2R _ _ (BofZ n) = round radix2 fexp (round_mode mode_NE) (IZR n)
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = Z.ltb n 0%Z.
Proof.
  intros.
  generalize (BofZ_correct n). rewrite Rlt_bool_true. auto.
  apply round_int_no_overflow; auto.
Qed.

Theorem BofZ_representable:
  forall n,
  integer_representable n ->
  B2R _ _ (BofZ n) = IZR n
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = (n <? 0).
Proof.
  intros. destruct H as (P & Q). destruct (BofZ_finite n) as (A & B & C). auto.
  intuition. rewrite A. apply round_generic. apply valid_rnd_round_mode. auto.
Qed.

Theorem BofZ_exact:
  forall n,
  -2^prec <= n <= 2^prec ->
  B2R _ _ (BofZ n) = IZR n
  /\ is_finite _ _ (BofZ n) = true
  /\ Bsign _ _ (BofZ n) = Z.ltb n 0%Z.
Proof.
  intros. apply BofZ_representable. apply integer_representable_n; auto.
Qed.

Lemma BofZ_finite_pos0:
  forall n,
  Z.abs n <= 2^emax - 2^(emax-prec) -> is_finite_pos0 (BofZ n) = true.
Proof.
  intros.
  generalize (binary_normalize_correct prec emax _ _ mode_NE n 0 false).
  fold emin; fold fexp; fold (BofZ n).
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n) by
    (unfold F2R; simpl; ring).
  rewrite Rlt_bool_true by (apply round_int_no_overflow; auto).
  intros (A & B & C).
  destruct (BofZ n); auto; try discriminate.
  simpl in *. rewrite C. rewrite Rcompare_IZR.
  generalize (Zcompare_spec n 0); intros SPEC; destruct SPEC; auto.
  assert ((round radix2 fexp ZnearestE (IZR n) <= -1)%R).
  { apply round_le_generic. apply fexp_correct. auto. apply valid_rnd_N.
    apply (integer_representable_opp 1).
    apply (integer_representable_2p 0).

    red in prec_gt_0_, prec_lt_emax_; lia.
    apply IZR_le; lia.
  }
  lra.
Qed.

Lemma BofZ_finite_equal:
  forall x y,
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  Z.abs y <= 2^emax - 2^(emax-prec) ->
  B2R _ _ (BofZ x) = B2R _ _ (BofZ y) ->
  BofZ x = BofZ y.
Proof.
  intros. apply B2R_inj_pos0; auto; apply BofZ_finite_pos0; auto.
Qed.

(** Commutation properties with addition, subtraction, multiplication. *)

Theorem BofZ_plus:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  Bplus _ _ _ _ nan mode_NE (BofZ p) (BofZ q) = BofZ (p + q).
Proof.
  intros.
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bplus_correct _ _ _ _ nan mode_NE (BofZ p) (BofZ q) B E).
  fold emin; fold fexp.
  rewrite A, D. rewrite <- plus_IZR.
  generalize (BofZ_correct (p + q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W, C, F.
  rewrite Rcompare_IZR. unfold Z.ltb at 3.
  generalize (Zcompare_spec (p + q) 0); intros SPEC; inversion SPEC; auto.
  assert (EITHER: 0 <= p \/ 0 <= q) by lia.
  destruct EITHER; [apply andb_false_intro1 | apply andb_false_intro2];
  apply Zlt_bool_false; auto.
- intros P (U & V).
  apply B2FF_inj.
  rewrite P, U, C. f_equal. rewrite C, F in V.
  generalize (Zlt_bool_spec p 0) (Zlt_bool_spec q 0). rewrite <- V.
  intros SPEC1 SPEC2; inversion SPEC1; inversion SPEC2; try congruence; symmetry.
  apply Zlt_bool_true; lia.
  apply Zlt_bool_false; lia.
Qed.

Theorem BofZ_minus:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  Bminus _ _ _ _ nan mode_NE (BofZ p) (BofZ q) = BofZ (p - q).
Proof.
  intros.
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bminus_correct _ _ _ _ nan mode_NE (BofZ p) (BofZ q) B E).
  fold emin; fold fexp.
  rewrite A, D. rewrite <- minus_IZR.
  generalize (BofZ_correct (p - q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W, C, F.
  rewrite Rcompare_IZR. unfold Z.ltb at 3.
  generalize (Zcompare_spec (p - q) 0); intros SPEC; inversion SPEC; auto.
  assert (EITHER: 0 <= p \/ q < 0) by lia.
  destruct EITHER; [apply andb_false_intro1 | apply andb_false_intro2].
  rewrite Zlt_bool_false; auto.
  rewrite Zlt_bool_true; auto.
- intros P (U & V).
  apply B2FF_inj.
  rewrite P, U, C. f_equal. rewrite C, F in V.
  generalize (Zlt_bool_spec p 0) (Zlt_bool_spec q 0). rewrite V.
  intros SPEC1 SPEC2; inversion SPEC1; inversion SPEC2; symmetry.
  rewrite <- H3 in H1; discriminate.
  apply Zlt_bool_true; lia.
  apply Zlt_bool_false; lia.
  rewrite <- H3 in H1; discriminate.
Qed.

Theorem BofZ_mult:
  forall nan p q,
  integer_representable p -> integer_representable q ->
  0 < q ->
  Bmult _ _ _ _ nan mode_NE (BofZ p) (BofZ q) = BofZ (p * q).
Proof.
  intros.
  assert (SIGN: xorb (p <? 0) (q <? 0) = (p * q <? 0)).
  {
    rewrite (Zlt_bool_false q) by lia.
    generalize (Zlt_bool_spec p 0); intros SPEC; inversion SPEC; simpl; symmetry.
    apply Zlt_bool_true. rewrite Z.mul_comm. apply Z.mul_pos_neg; lia.
    apply Zlt_bool_false. apply Zsame_sign_imp; lia.
  }
  destruct (BofZ_representable p) as (A & B & C); auto.
  destruct (BofZ_representable q) as (D & E & F); auto.
  generalize (Bmult_correct _ _ _ _ nan mode_NE (BofZ p) (BofZ q)).
  fold emin; fold fexp.
  rewrite A, B, C, D, E, F. rewrite <- mult_IZR.
  generalize (BofZ_correct (p * q)). destruct Rlt_bool.
- intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U; auto.
  rewrite R, W; auto.
  apply is_finite_not_is_nan; auto.
- intros P U.
  apply B2FF_inj. rewrite P, U. f_equal. auto.
Qed.

Theorem BofZ_mult_2p:
  forall nan x p,
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  2^prec <= Z.abs x ->
  0 <= p <= emax - 1 ->
  Bmult _ _ _ _ nan mode_NE (BofZ x) (BofZ (2^p)) = BofZ (x * 2^p).
Proof.
  intros.
  destruct (Z.eq_dec x 0).
- subst x. apply BofZ_mult.
    apply integer_representable_n.
    generalize (Zpower_ge_0 radix2 prec). simpl; lia.
    apply integer_representable_2p. auto.
    apply (Zpower_gt_0 radix2).
    lia.
- assert (IZR x <> 0%R) by (apply (IZR_neq _ _ n)).
  destruct (BofZ_finite x H) as (A & B & C).
  destruct (BofZ_representable (2^p)) as (D & E & F).
    apply integer_representable_2p. auto.
  assert (cexp radix2 fexp (IZR (x * 2^p)) =
          cexp radix2 fexp (IZR x) + p).
  {
    unfold cexp, fexp. rewrite mult_IZR.
    change (2^p) with (radix2^p). rewrite IZR_Zpower by lia.
    rewrite mag_mult_bpow by auto.
    assert (prec + 1 <= mag radix2 (IZR x)).
    { rewrite <- (mag_abs radix2 (IZR x)).
      rewrite <- (mag_bpow radix2 prec).
      apply mag_le.
      apply bpow_gt_0. rewrite <- IZR_Zpower by (red in prec_gt_0_;lia).
      rewrite <- abs_IZR. apply IZR_le; auto. }
    unfold FLT_exp.
    unfold emin; red in prec_gt_0_; zify; lia.
  }
  assert (forall m, round radix2 fexp m (IZR x) * IZR (2^p) =
                    round radix2 fexp m (IZR (x * 2^p)))%R.
  {
    intros. unfold round, scaled_mantissa. rewrite H3.
    rewrite mult_IZR. rewrite Z.opp_add_distr. rewrite bpow_plus.
    set (a := IZR x); set (b := bpow radix2 (- cexp radix2 fexp a)).
    replace (a * IZR (2^p) * (b * bpow radix2 (-p)))%R with (a * b)%R.
    unfold F2R; simpl. rewrite Rmult_assoc. f_equal.
    rewrite bpow_plus.  f_equal. apply (IZR_Zpower radix2). lia.
    transitivity ((a * b) * (IZR (2^p) * bpow radix2 (-p)))%R.
    rewrite (IZR_Zpower radix2). rewrite <- bpow_plus.
    replace (p + -p) with 0 by lia. change (bpow radix2 0) with 1%R. ring.
    lia.
    ring.
  }
  assert (forall m x,
    round radix2 fexp (round_mode m) (round radix2 fexp (round_mode m) x) =
    round radix2 fexp (round_mode m) x).
  {
    intros. apply round_generic. apply valid_rnd_round_mode.
    apply generic_format_round.  apply fexp_correct; auto.
    apply valid_rnd_round_mode.
  }
  assert (xorb (x <? 0) (2^p <? 0) = (x * 2^p <? 0)).
  {
    assert (0 < 2^p) by (apply (Zpower_gt_0 radix2); lia).
    rewrite (Zlt_bool_false (2^p)) by lia. rewrite xorb_false_r.
    symmetry. generalize (Zlt_bool_spec x 0); intros SPEC; inversion SPEC.
    apply Zlt_bool_true. apply Z.mul_neg_pos; auto.
    apply Zlt_bool_false. apply Z.mul_nonneg_nonneg; lia.
  }
  generalize (Bmult_correct _ _ _ _ nan mode_NE (BofZ x) (BofZ (2^p)))
             (BofZ_correct (x * 2^p)).
  fold emin; fold fexp. rewrite A, B, C, D, E, F, H4, H5.
  destruct Rlt_bool.
+ intros (P & Q & R) (U & V & W).
  apply B2R_Bsign_inj; auto.
  rewrite P, U. auto.
  rewrite R, W. auto.
  apply is_finite_not_is_nan; auto.
+ intros P U.
  apply B2FF_inj. rewrite P, U. f_equal; auto.
Qed.

(** Rounding to odd the argument of [BofZ]. *)

Lemma round_odd_flt:
  forall prec' emin' x choice,
  prec > 1 -> prec' > 1 -> prec' >= prec + 2 -> emin' <= emin - 2 ->
  round radix2 fexp (Znearest choice) (round radix2 (FLT_exp emin' prec') Zrnd_odd x) =
  round radix2 fexp (Znearest choice) x.
Proof.
  intros. apply round_N_odd. auto. apply fexp_correct; auto.
  apply exists_NE_FLT. right; lia.
  apply FLT_exp_valid. red; lia.
  apply exists_NE_FLT. right; lia.
  unfold fexp, FLT_exp; intros. zify; lia.
Qed.

Corollary round_odd_fix:
  forall x p choice,
  prec > 1 ->
  0 <= p ->
  (bpow radix2 (prec + p + 1) <= Rabs x)%R ->
  round radix2 fexp (Znearest choice) (round radix2 (FIX_exp p) Zrnd_odd x) =
  round radix2 fexp (Znearest choice) x.
Proof.
  intros. destruct (Req_EM_T x 0%R).
- subst x. rewrite round_0. auto. apply valid_rnd_odd.
- set (prec' := mag radix2 x - p).
  set (emin' := emin - 2).
  assert (PREC: mag radix2 (bpow radix2 (prec + p + 1)) <= mag radix2 x).
  { rewrite <- (mag_abs radix2 x).
    apply mag_le; auto. apply bpow_gt_0. }
  rewrite mag_bpow in PREC.
  assert (CANON: cexp radix2 (FLT_exp emin' prec') x =
                 cexp radix2 (FIX_exp p) x).
  {
    unfold cexp, FLT_exp, FIX_exp.
    replace (mag radix2 x - prec') with p by (unfold prec'; lia).
    apply Z.max_l. unfold emin', emin. red in prec_gt_0_, prec_lt_emax_; lia.
  }
  assert (RND: round radix2 (FIX_exp p) Zrnd_odd x =
               round radix2 (FLT_exp emin' prec') Zrnd_odd x).
  {
    unfold round, scaled_mantissa. rewrite CANON. auto.
  }
  rewrite RND.
  apply round_odd_flt. auto.
  unfold prec'. red in prec_gt_0_; lia.
  unfold prec'. lia.
  unfold emin'. lia.
Qed.

Definition int_round_odd (x: Z) (p: Z) :=
  (if Z.eqb (x mod 2^p) 0 || Z.odd (x / 2^p) then x / 2^p else x / 2^p + 1) * 2^p.

Lemma Zrnd_odd_int:
  forall n p, 0 <= p ->
  Zrnd_odd (IZR n * bpow radix2 (-p)) * 2^p =
  int_round_odd n p.
Proof.
  clear. intros.
  assert (0 < 2^p) by (apply (Zpower_gt_0 radix2); lia).
  assert (n = (n / 2^p) * 2^p + n mod 2^p) by (rewrite Z.mul_comm; apply Z.div_mod; lia).
  assert (0 <= n mod 2^p < 2^p) by (apply Z_mod_lt; lia).
  unfold int_round_odd. set (q := n / 2^p) in *; set (r := n mod 2^p) in *.
  f_equal.
  pose proof (bpow_gt_0 radix2 (-p)).
  assert (bpow radix2 p * bpow radix2 (-p) = 1)%R.
  { rewrite <- bpow_plus. replace (p + -p) with 0 by lia. auto. }
  assert (IZR n * bpow radix2 (-p) = IZR q + IZR r * bpow radix2 (-p))%R.
  { rewrite H1. rewrite plus_IZR, mult_IZR.
    change (IZR (2^p)) with (IZR (radix2^p)).
    rewrite IZR_Zpower by lia. ring_simplify.
    rewrite Rmult_assoc. rewrite H4. ring. }
  assert (0 <= IZR r < bpow radix2 p)%R.
  { split. apply IZR_le; lia.
    rewrite <- IZR_Zpower by lia. apply IZR_lt; tauto. }
  assert (0 <= IZR r * bpow radix2 (-p) < 1)%R.
  { generalize (bpow_gt_0 radix2 (-p)). intros.
    split. apply Rmult_le_pos; lra.
    rewrite <- H4. apply Rmult_lt_compat_r. auto. tauto. }
  assert (Zfloor (IZR n * bpow radix2 (-p)) = q).
  { apply Zfloor_imp. rewrite H5. rewrite plus_IZR. lra. }
  unfold Zrnd_odd. destruct Req_EM_T.
- assert (IZR r * bpow radix2 (-p) = 0)%R.
  { rewrite H8 in e. rewrite e in H5. lra. }
  apply Rmult_integral in H9. destruct H9; [ | lra ].
  apply (eq_IZR r 0) in H9. apply <- Z.eqb_eq in H9. rewrite H9. assumption.
- assert (IZR r * bpow radix2 (-p) <> 0)%R.
  { rewrite H8 in n0. lra. }
  destruct (Z.eqb r 0) eqn:RZ.
  apply Z.eqb_eq in RZ. rewrite RZ in H9.
  rewrite Rmult_0_l in H9. congruence.
  rewrite Zceil_floor_neq by lra. rewrite H8.
  change Zeven with Z.even. rewrite Zodd_even_bool. destruct (Z.even q); auto.
Qed.

Lemma int_round_odd_le:
  forall p x y, 0 <= p ->
  x <= y -> int_round_odd x p <= int_round_odd y p.
Proof.
  clear. intros.
  assert (Zrnd_odd (IZR x * bpow radix2 (-p)) <= Zrnd_odd (IZR y * bpow radix2 (-p))).
  { apply Zrnd_le. apply valid_rnd_odd. apply Rmult_le_compat_r. apply bpow_ge_0.
    apply IZR_le; auto. }
  rewrite <- ! Zrnd_odd_int by auto.
  apply Zmult_le_compat_r. auto. apply (Zpower_ge_0 radix2).
Qed.

Lemma int_round_odd_exact:
  forall p x, 0 <= p ->
  (2^p | x) -> int_round_odd x p = x.
Proof.
  clear. intros. unfold int_round_odd. apply Znumtheory.Zdivide_mod in H0.
  rewrite H0. simpl. rewrite Z.mul_comm. symmetry. apply Z_div_exact_2.
  apply Z.lt_gt. apply (Zpower_gt_0 radix2). auto. auto.
Qed.

Theorem BofZ_round_odd:
  forall x p,
  prec > 1 ->
  Z.abs x <= 2^emax - 2^(emax-prec) ->
  0 <= p <= emax - prec ->
  2^(prec + p + 1) <= Z.abs x ->
  BofZ x = BofZ (int_round_odd x p).
Proof.
  intros x p PREC XRANGE PRANGE XGE.
  assert (DIV: (2^p | 2^emax - 2^(emax - prec))).
  { rewrite int_upper_bound_eq. apply Z.divide_mul_r.
    exists (2^(emax - prec - p)). red in prec_gt_0_.
    rewrite <- (Zpower_plus radix2) by lia. f_equal; lia. }
  assert (YRANGE: Z.abs (int_round_odd x p) <= 2^emax - 2^(emax-prec)).
  { apply Z.abs_le. split.
    replace (-(2^emax - 2^(emax-prec))) with (int_round_odd (-(2^emax - 2^(emax-prec))) p).
    apply int_round_odd_le; zify; lia.
    apply int_round_odd_exact. lia. apply Z.divide_opp_r. auto.
    replace (2^emax - 2^(emax-prec)) with (int_round_odd (2^emax - 2^(emax-prec)) p).
    apply int_round_odd_le; zify; lia.
    apply int_round_odd_exact. lia. auto. }
  destruct (BofZ_finite x XRANGE) as (X1 & X2 & X3).
  destruct (BofZ_finite (int_round_odd x p) YRANGE) as (Y1 & Y2 & Y3).
  apply BofZ_finite_equal; auto.
  rewrite X1, Y1.
  assert (IZR (int_round_odd x p) = round radix2 (FIX_exp p) Zrnd_odd (IZR x)).
  {
     unfold round, scaled_mantissa, cexp, FIX_exp.
     rewrite <- Zrnd_odd_int by lia.
     unfold F2R; simpl. rewrite mult_IZR. f_equal. apply (IZR_Zpower radix2). lia.
  }
  rewrite H. symmetry. apply round_odd_fix. auto. lia.
  rewrite <- IZR_Zpower. rewrite <- abs_IZR. apply IZR_le; auto.
  red in prec_gt_0_; lia.
Qed.

Lemma int_round_odd_shifts:
  forall x p, 0 <= p ->
  int_round_odd x p =
  Z.shiftl (if Z.eqb (x mod 2^p) 0 then Z.shiftr x p else Z.lor (Z.shiftr x p) 1) p.
Proof.
  clear. intros.
  unfold int_round_odd. rewrite Z.shiftl_mul_pow2 by auto. f_equal.
  rewrite Z.shiftr_div_pow2 by auto.
  destruct (x mod 2^p =? 0) eqn:E. auto.
  assert (forall n, (if Z.odd n then n else n + 1) = Z.lor n 1).
  { destruct n; simpl; auto.
    destruct p0; auto.
    destruct p0; auto. induction p0; auto. }
  simpl. apply H0.
Qed.

Lemma int_round_odd_bits:
  forall x y p, 0 <= p ->
  (forall i, 0 <= i < p -> Z.testbit y i = false) ->
  Z.testbit y p = (if Z.eqb (x mod 2^p) 0 then Z.testbit x p else true) ->
  (forall i, p < i -> Z.testbit y i = Z.testbit x i) ->
  int_round_odd x p = y.
Proof.
  clear. intros until p; intros PPOS BELOW AT ABOVE.
  rewrite int_round_odd_shifts by auto.
  apply Z.bits_inj'. intros.
  generalize (Zcompare_spec n p); intros SPEC; inversion SPEC.
- rewrite BELOW by auto. apply Z.shiftl_spec_low; auto.
- subst n. rewrite AT. rewrite Z.shiftl_spec_high by lia.
  replace (p - p) with 0 by lia.
  destruct (x mod 2^p =? 0).
  + rewrite Z.shiftr_spec by lia. f_equal; lia.
  + rewrite Z.lor_spec. apply orb_true_r.
- rewrite ABOVE by auto.  rewrite Z.shiftl_spec_high by lia.
  destruct (x mod 2^p =? 0).
  rewrite Z.shiftr_spec by lia. f_equal; lia.
  rewrite Z.lor_spec, Z.shiftr_spec by lia.
  change 1 with (Z.ones 1). rewrite Z.ones_spec_high by lia. rewrite orb_false_r.
  f_equal; lia.
Qed.

(** ** Conversion from a FP number to an integer *)

(** Always rounds toward zero. *)

Definition ZofB (f: binary_float): option Z :=
  match f with
    | B754_finite _ _ s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Z.pow_pos radix2 e)%Z
    | B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite _ _ s m (Zneg e) _ => Some (cond_Zopp s (Zpos m / Z.pow_pos radix2 e))%Z
    | B754_zero _ _ _ => Some 0%Z
    | _ => None
  end.

Theorem ZofB_correct:
  forall f,
  ZofB f = if is_finite _ _ f then Some (Ztrunc (B2R _ _ f)) else None.
Proof.
  destruct f as [s|s|s p H|s m e H]; simpl; auto.
- f_equal. symmetry. apply (Ztrunc_IZR 0).
- destruct e; f_equal.
  + unfold F2R; simpl. rewrite Rmult_1_r. rewrite Ztrunc_IZR. auto.
  + unfold F2R; simpl. rewrite <- mult_IZR. rewrite Ztrunc_IZR. auto.
  + unfold F2R; simpl. rewrite IZR_cond_Zopp. rewrite <- cond_Ropp_mult_l.
    assert (EQ: forall x, Ztrunc (cond_Ropp s x) = cond_Zopp s (Ztrunc x)).
    {
      intros. destruct s; simpl; auto. apply Ztrunc_opp.
    }
    rewrite EQ. f_equal.
    generalize (Zpower_pos_gt_0 2 p (eq_refl _)); intros.
    rewrite Ztrunc_floor. symmetry. apply Zfloor_div. lia.
    apply Rmult_le_pos. apply IZR_le. compute; congruence.
    apply Rlt_le. apply Rinv_0_lt_compat. apply IZR_lt. auto.
Qed.

(** Interval properties. *)

Remark Ztrunc_range_pos:
  forall x, 0 < Ztrunc x -> (IZR (Ztrunc x) <= x < IZR (Ztrunc x + 1)%Z)%R.
Proof.
  intros.
  rewrite Ztrunc_floor. split. apply Zfloor_lb. rewrite plus_IZR. apply Zfloor_ub.
  generalize (Rle_bool_spec 0%R x). intros RLE; inversion RLE; subst; clear RLE.
  auto.
  rewrite Ztrunc_ceil in H by lra. unfold Zceil in H.
  assert (-x < 0)%R.
  { apply Rlt_le_trans with (IZR (Zfloor (-x)) + 1)%R. apply Zfloor_ub.
    rewrite <- plus_IZR.
    apply IZR_le. lia. }
  lra.
Qed.

Remark Ztrunc_range_zero:
  forall x, Ztrunc x = 0 -> (-1 < x < 1)%R.
Proof.
  intros; generalize (Rle_bool_spec 0%R x). intros RLE; inversion RLE; subst; clear RLE.
- rewrite Ztrunc_floor in H by auto. split.
  + apply Rlt_le_trans with 0%R; auto. rewrite <- Ropp_0. apply Ropp_lt_contravar. apply Rlt_0_1.
  + replace 1%R with (IZR (Zfloor x) + 1)%R. apply Zfloor_ub. rewrite H. simpl. apply Rplus_0_l.
- rewrite Ztrunc_ceil in H by (apply Rlt_le; auto). split.
  + apply (Ropp_lt_cancel (-(1))). rewrite Ropp_involutive.
    replace 1%R with (IZR (Zfloor (-x)) + 1)%R. apply Zfloor_ub.
    unfold Zceil in H. replace (Zfloor (-x)) with 0 by lia. simpl. apply Rplus_0_l.
  + apply Rlt_le_trans with 0%R; auto. apply Rle_0_1.
Qed.

Theorem ZofB_range_pos:
  forall f n, ZofB f = Some n -> 0 < n -> (IZR n <= B2R _ _ f < IZR (n + 1)%Z)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  apply Ztrunc_range_pos. congruence.
Qed.

Theorem ZofB_range_neg:
  forall f n, ZofB f = Some n -> n < 0 -> (IZR (n - 1)%Z < B2R _ _ f <= IZR n)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  set (x := B2R prec emax f) in *. set (y := (-x)%R).
  assert (A: (IZR (Ztrunc y) <= y < IZR (Ztrunc y + 1)%Z)%R).
  { apply Ztrunc_range_pos. unfold y. rewrite Ztrunc_opp. lia. }
  destruct A as [B C].
  unfold y in B, C. rewrite Ztrunc_opp in B, C.
  replace (- Ztrunc x + 1) with (- (Ztrunc x - 1)) in C by lia.
  rewrite opp_IZR in B, C. lra.
Qed.

Theorem ZofB_range_zero:
  forall f, ZofB f = Some 0 -> (-1 < B2R _ _ f < 1)%R.
Proof.
  intros. rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  apply Ztrunc_range_zero. auto.
Qed.

Theorem ZofB_range_nonneg:
  forall f n, ZofB f = Some n -> 0 <= n -> (-1 < B2R _ _ f < IZR (n + 1)%Z)%R.
Proof.
  intros. destruct (Z.eq_dec n 0).
- subst n. apply ZofB_range_zero. auto.
- destruct (ZofB_range_pos f n) as (A & B). auto. lia.
  split; auto. apply Rlt_le_trans with 0%R. simpl; lra.
  apply Rle_trans with (IZR n); auto. apply IZR_le; auto.
Qed.

(** For representable integers, [ZofB] is left inverse of [BofZ]. *)

Theorem ZofBofZ_exact:
  forall n, integer_representable n -> ZofB (BofZ n) = Some n.
Proof.
  intros. destruct (BofZ_representable n H) as (A & B & C).
  rewrite ZofB_correct. rewrite A, B. f_equal. apply Ztrunc_IZR.
Qed.

(** Compatibility with subtraction *)

Remark Zfloor_minus:
  forall x n, Zfloor (x - IZR n) = Zfloor x - n.
Proof.
  intros. apply Zfloor_imp. replace (Zfloor x - n + 1) with ((Zfloor x + 1) - n) by lia.
  rewrite ! minus_IZR. unfold Rminus. split.
  apply Rplus_le_compat_r. apply Zfloor_lb.
  apply Rplus_lt_compat_r. rewrite plus_IZR. apply Zfloor_ub.
Qed.

Theorem ZofB_minus:
  forall minus_nan m f p q,
  ZofB f = Some p -> 0 <= p < 2*q -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB (Bminus _ _ _ _ minus_nan m f (BofZ q)) = Some (p - q).
Proof.
  intros.
  assert (Q: -2^prec <= q <= 2^prec).
  { split; auto.  generalize (Zpower_ge_0 radix2 prec); simpl; lia. }
  assert (RANGE: (-1 < B2R _ _ f < IZR (p + 1)%Z)%R) by (apply ZofB_range_nonneg; auto; lia).
  rewrite ZofB_correct in H. destruct (is_finite prec emax f) eqn:FIN; try discriminate.
  assert (PQ2: (IZR (p + 1) <= IZR q * 2)%R).
  { rewrite <- mult_IZR. apply IZR_le. lia. }
  assert (EXACT: round radix2 fexp (round_mode m) (B2R _ _ f - IZR q)%R = (B2R _ _ f - IZR q)%R).
  { apply round_generic. apply valid_rnd_round_mode.
    apply sterbenz_aux. now apply FLT_exp_valid. apply FLT_exp_monotone. apply generic_format_B2R.
    apply integer_representable_n. auto. lra. }
  destruct (BofZ_exact q Q) as (A & B & C).
  generalize (Bminus_correct _ _ _ _ minus_nan m f (BofZ q) FIN B).
  rewrite Rlt_bool_true.
- fold emin; fold fexp. intros (D & E & F).
  rewrite ZofB_correct. rewrite E. rewrite D. rewrite A. rewrite EXACT.
  inversion H. f_equal. rewrite ! Ztrunc_floor. apply Zfloor_minus.
  lra. lra.
- rewrite A. fold emin; fold fexp. rewrite EXACT.
  apply Rle_lt_trans with (bpow radix2 prec).
  apply Rle_trans with (IZR q). apply Rabs_le. lra.
  rewrite <- IZR_Zpower. apply IZR_le; auto. red in prec_gt_0_; lia.
  apply bpow_lt. auto.
Qed.

(** A variant of [ZofB] that bounds the range of representable integers. *)

Definition ZofB_range (f: binary_float) (zmin zmax: Z): option Z :=
  match ZofB f with
  | None => None
  | Some z => if Z.leb zmin z && Z.leb z zmax then Some z else None
  end.

Theorem ZofB_range_correct:
  forall f min max,
  let n := Ztrunc (B2R _ _ f) in
  ZofB_range f min max =
  if is_finite _ _ f && Z.leb min n && Z.leb n max then Some n else None.
Proof.
  intros. unfold ZofB_range. rewrite ZofB_correct. fold n.
  destruct (is_finite prec emax f); auto.
Qed.

Lemma ZofB_range_inversion:
  forall f min max n,
  ZofB_range f min max = Some n ->
  min <= n /\ n <= max /\ ZofB f = Some n.
Proof.
  intros. rewrite ZofB_range_correct in H. rewrite ZofB_correct.
  destruct (is_finite prec emax f); try discriminate.
  set (n1 := Ztrunc (B2R _ _ f)) in *.
  destruct (min <=? n1) eqn:MIN; try discriminate.
  destruct (n1 <=? max) eqn:MAX; try discriminate.
  simpl in H. inversion H. subst n.
  split. apply Zle_bool_imp_le; auto.
  split. apply Zle_bool_imp_le; auto.
  auto.
Qed.

Theorem ZofB_range_minus:
  forall minus_nan m f p q,
  ZofB_range f 0 (2 * q - 1) = Some p -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB_range (Bminus _ _ _ _ minus_nan m f (BofZ q)) (-q) (q - 1) = Some (p - q).
Proof.
  intros. destruct (ZofB_range_inversion _ _ _ _ H) as (A & B & C).
  set (f' := Bminus prec emax _ _ minus_nan m f (BofZ q)).
  assert (D: ZofB f' = Some (p - q)).
  { apply ZofB_minus. auto. lia. auto. auto. }
  unfold ZofB_range. rewrite D. rewrite Zle_bool_true by lia. rewrite Zle_bool_true by lia. auto.
Qed.

(** ZofB_ne : convert float to integer, round to nearest *)

Definition Zdiv_ne (a b : Z) :=
  let q := Z.div a b in
  let q1 := Z.succ q in
  match Z.compare (a-b*q) (b*q1-a) with
  | Lt => q
  | Gt => q1
  | Eq => (if Z.even q then q else q1)
  end.

Definition ZofB_ne (f: binary_float): option Z :=
  match f with
    | B754_finite _ _ s m (Zpos e) _ => Some (cond_Zopp s (Zpos m) * Z.pow_pos radix2 e)%Z
    | B754_finite _ _ s m 0 _ => Some (cond_Zopp s (Zpos m))
    | B754_finite _ _ s m (Zneg e) _ => Some (cond_Zopp s (Zdiv_ne (Zpos m)  (Z.pow_pos radix2 e)))%Z
    | B754_zero _ _ _ => Some 0%Z
    | _ => None
  end.

Ltac field_simplify_den := field_simplify ; [idtac | lra].
Ltac Rdiv_lt_0_den := apply Rdiv_lt_0_compat ; [idtac | lra].

Hint Rewrite <- plus_IZR minus_IZR opp_IZR mult_IZR : l_IZR.
Ltac l_IZR := autorewrite with l_IZR.

Theorem ZofB_ne_correct:
  forall f,
    ZofB_ne f = if is_finite _ _ f then Some (ZnearestE (B2R _ _ f)) else None.
Proof.
  destruct f as [s|s|s p H|s m e H]; simpl; auto.
- f_equal. symmetry. apply (ZnearestE_IZR 0).
- destruct e; f_equal.
  + unfold F2R; cbn. rewrite Rmult_1_r. rewrite ZnearestE_IZR. auto.
  + unfold F2R; cbn. rewrite <- mult_IZR. rewrite ZnearestE_IZR. auto.
  + unfold F2R; cbn. rewrite IZR_cond_Zopp. rewrite <- cond_Ropp_mult_l.
    assert (EQ: forall x, ZnearestE (cond_Ropp s x) = cond_Zopp s (ZnearestE x)).
    { intros. destruct s; cbn; auto. apply ZnearestE_opp. }
    rewrite EQ. f_equal.
    generalize (Zpower_pos_gt_0 2 p (eq_refl _)); intros.
    set (p2p := (Z.pow_pos 2 p)) in *.
    set (zm := Z.pos m) in *.
    assert (p2p > 0) as POS by lia.
    assert (0 < IZR p2p)%R as POS2.
    { apply IZR_lt. assumption. }
    unfold Zdiv_ne, Z.succ in *.
    case Z.compare_spec; intro CMP.
    * pose proof (Z_div_mod_eq_full zm p2p) as DECOMPOSE.
      destruct (Z_mod_lt zm p2p POS) as [MOD1 MOD2].
      set (q := zm / p2p) in *.
      set (r := zm mod p2p) in *.
      rewrite inbetween_int_NE with (m := q) (l := loc_Inexact Eq).
      { cbn. unfold cond_incr.
        destruct Z.even; reflexivity.
      }
      constructor.
      split.
      ** assert (0 < IZR zm / IZR p2p - IZR q)%R.
         2: lra.
         field_simplify_den.
         Rdiv_lt_0_den.
         l_IZR.
         apply IZR_lt.
         lia.
      ** assert (0 < IZR (q + 1) - (IZR zm * / IZR p2p))%R.
         2: lra.
         field_simplify_den.
         Rdiv_lt_0_den.
         l_IZR.
         apply IZR_lt.
         lia.
      ** apply Rcompare_Eq.
         assert ((IZR q + IZR (q + 1))/2 - (IZR zm * / IZR p2p) = 0)%R; [idtac|lra].
         field_simplify_den.
         l_IZR.
         replace (q * p2p + (q + 1) * p2p - 2 * zm) with 0 by lia.
         field. apply IZR_neq. lia.
    * symmetry.
      apply Znearest_imp with (n := zm / p2p).
      apply Rabs_lt. split.
     ** pose proof (Z_mult_div_ge zm p2p POS).
        assert (0 <= IZR zm * / IZR p2p - IZR (zm / p2p))%R.
        2: lra.
        field_simplify_den.
        apply Rmult_le_pos.
        { l_IZR.
          apply IZR_le.
          lia.
        }
        assert (0 < / IZR p2p)%R.
        2: lra.
        apply Rinv_0_lt_compat. assumption.
     ** assert (0 < 2*(IZR p2p * IZR (zm / p2p) - IZR zm) + (IZR p2p))%R as LT.
        { l_IZR.
          apply IZR_lt.
          lia. }
        assert (0 < -(IZR zm * / IZR p2p - IZR (zm / p2p) - / 2))%R as GT.
        2: lra.
        field_simplify_den.
        Rdiv_lt_0_den.
        lra.
    * symmetry.
      apply Znearest_imp.
      apply Rabs_lt. split.
      ** assert (0 < (IZR zm - IZR p2p * IZR (zm / p2p)) - (IZR p2p * (IZR (zm / p2p) + 1) - IZR zm))%R.
         { ring_simplify.
           l_IZR.
           apply IZR_lt.
           lia.
         }
         assert (0 < (/ 2) + IZR zm * / IZR p2p - IZR (zm / p2p + 1))%R.
         2: lra.
         field_simplify_den.
         Rdiv_lt_0_den.
         rewrite plus_IZR.
         lra.
      ** assert (0 < IZR (zm / p2p + 1) - (IZR zm * / IZR p2p))%R.
         2: lra.
         field_simplify_den.
         Rdiv_lt_0_den.
         l_IZR.
         apply IZR_lt.
         pose proof (Z_div_mod_eq_full zm p2p) as DECOMPOSE.
         ring_simplify.
         set (q := (zm / p2p)) in *.
         pose proof (Z_mod_lt zm p2p POS) as MOD.
         lia.
Qed.

Theorem ZofB_ne_ball:
  forall f n, ZofB_ne f = Some n -> (IZR n-1/2 <= B2R _ _ f <= IZR n+1/2)%R.
Proof.
  intros. rewrite ZofB_ne_correct in H. destruct (is_finite prec emax f) eqn:FIN; inversion H.
  pose proof (Znearest_imp2  (fun x => negb (Z.even x)) (B2R prec emax f)) as ABS.
  pose proof (Rabs_le_inv _ _ ABS).
  lra.
Qed.

(*
Theorem ZofB_ne_minus:
  forall minus_nan m f p q,
  ZofB_ne f = Some p -> 0 <= p < 2*q -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB_ne (Bminus _ _ _ Hmax minus_nan m f (BofZ q)) = Some (p - q).
Proof.
  intros.
  assert (Q: -2^prec <= q <= 2^prec).
  { split; auto.  generalize (Zpower_ge_0 radix2 prec); simpl; lia. }
  assert (RANGE: (IZR p -1/2 <= B2R _ _ f <= IZR p + 1/2)%R) by ( apply ZofB_ne_ball; auto ).    
  rewrite ZofB_ne_correct in H. destruct (is_finite prec emax f) eqn:FIN; try discriminate.
  assert (PQ2: (IZR p + 1 <= IZR q * 2)%R).
  { l_IZR. apply IZR_le. lia. }
  assert (EXACT: round radix2 fexp (round_mode m) (B2R _ _ f - IZR q)%R = (B2R _ _ f - IZR q)%R).
  { apply round_generic. apply valid_rnd_round_mode.
    apply sterbenz_aux. now apply FLT_exp_valid. apply FLT_exp_monotone. apply generic_format_B2R.
    apply integer_representable_n. auto. lra. }
  destruct (BofZ_exact q Q) as (A & B & C).
  generalize (Bminus_correct _ _ _ Hmax minus_nan m f (BofZ q) FIN B).
  rewrite Rlt_bool_true.
- fold emin; fold fexp. intros (D & E & F).
  rewrite ZofB_ne_correct. rewrite E. rewrite D. rewrite A. rewrite EXACT.
  inversion H. f_equal.
  rewrite ! Ztrunc_floor. apply Zfloor_minus.
  lra. lra.
- rewrite A. fold emin; fold fexp. rewrite EXACT.
  apply Rle_lt_trans with (bpow radix2 prec).
  apply Rle_trans with (IZR q). apply Rabs_le. lra.
  rewrite <- IZR_Zpower. apply IZR_le; auto. red in prec_gt_0_; lia.
  apply bpow_lt. auto.
Qed.
 *)

Definition ZofB_ne_range (f: binary_float) (zmin zmax: Z): option Z :=
  match ZofB_ne f with
  | None => None
  | Some z => if Z.leb zmin z && Z.leb z zmax then Some z else None
  end.

Theorem ZofB_ne_range_correct:
  forall f min max,
  let n := ZnearestE (B2R _ _ f) in
  ZofB_ne_range f min max =
  if is_finite _ _ f && Z.leb min n && Z.leb n max then Some n else None.
Proof.
  intros. unfold ZofB_ne_range. rewrite ZofB_ne_correct. fold n.
  destruct (is_finite prec emax f); auto.
Qed.

Lemma ZofB_ne_range_inversion:
  forall f min max n,
  ZofB_ne_range f min max = Some n ->
  min <= n /\ n <= max /\ ZofB_ne f = Some n.
Proof.
  intros. rewrite ZofB_ne_range_correct in H. rewrite ZofB_ne_correct.
  destruct (is_finite prec emax f); try discriminate.
  set (n1 := ZnearestE (B2R _ _ f)) in *.
  destruct (min <=? n1) eqn:MIN; try discriminate.
  destruct (n1 <=? max) eqn:MAX; try discriminate.
  simpl in H. inversion H. subst n.
  split. apply Zle_bool_imp_le; auto.
  split. apply Zle_bool_imp_le; auto.
  auto.
Qed.


(*
Theorem ZofB_ne_range_minus:
  forall minus_nan m f p q,
  ZofB_ne_range f 0 (2 * q - 1) = Some p -> q <= 2^prec -> (IZR q <= B2R _ _ f)%R ->
  ZofB_ne_range (Bminus _ _ _ Hmax minus_nan m f (BofZ q)) (-q) (q - 1) = Some (p - q).
Proof.
  intros. destruct (ZofB_ne_range_inversion _ _ _ _ H) as (A & B & C).
  set (f' := Bminus prec emax prec_gt_0_ Hmax minus_nan m f (BofZ q)).
  assert (D: ZofB_ne f' = Some (p - q)).
  { apply ZofB_ne_minus. auto. lia. auto. auto. }
  unfold ZofB_range. rewrite D. rewrite Zle_bool_true by lia. rewrite Zle_bool_true by lia. auto.
Qed.
 *)

(** ** Algebraic identities *)

(** Commutativity of addition and multiplication *)

Theorem Bplus_commut:
  forall plus_nan mode (x y: binary_float),
  plus_nan x y = plus_nan y x ->
  Bplus _ _ _ _ plus_nan mode x y = Bplus _ _ _ _ plus_nan mode y x.
Proof.
  intros until y; intros NAN.
  unfold Bplus. rewrite NAN. f_equal.
  destruct x as [sx|sx|sx px Hx|sx mx ex Hx]; destruct y as [sy|sy|sy py Hy|sy my ey Hy]; auto; simpl.
- rewrite (eqb_sym sy sx). destruct (eqb sx sy) eqn:EQB; auto.
  f_equal; apply eqb_prop; auto.
- rewrite (eqb_sym sy sx). destruct (eqb sx sy) eqn:EQB; auto.
  f_equal; apply eqb_prop; auto.
- rewrite Z.min_comm. f_equal.
  apply Zplus_comm.
Qed.

Theorem Bmult_commut:
  forall mult_nan mode (x y: binary_float),
  mult_nan x y = mult_nan y x ->
  Bmult _ _ _ _ mult_nan mode x y = Bmult _ _ _ _ mult_nan mode y x.
Proof.
  intros until y; intros NAN.
  unfold Bmult. rewrite NAN. f_equal.
  destruct x as [sx|sx|sx px Hx|sx mx ex Hx]; destruct y as [sy|sy|sy py Hy|sy my ey Hy]; auto;
    simpl; try rewrite xorb_comm; auto.
  apply B2SF_inj. rewrite 2!B2SF_SF2B.
  now rewrite xorb_comm, Pos.mul_comm, Zplus_comm.
Qed.

Lemma F2R_not0:
  forall radix s m e,
    F2R (beta:=radix) {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |} <> 0%R.
Proof.
  intros.
  assert ((IZR (Z.pos m) * bpow radix e) > 0)%R as POS.
  { apply Rmult_gt_0_compat.
    { apply IZR_lt. lia. }
    pose proof (bpow_gt_0 radix e). lra.
  }
  destruct s; unfold F2R; cbn.
  {
    change (Z.neg m) with (- Z.pos m).
    rewrite opp_IZR.
    rewrite Ropp_mult_distr_l_reverse.
    lra.
  }
  lra.
Qed.

Lemma fully_known: forall x y
  (xNAN : is_nan prec emax x= false)
  (yNAN : is_nan prec emax y= false)                        
  (Req : B2R prec emax x = B2R prec emax y)
  (Feq : is_finite prec emax x = is_finite prec emax y)
  (Seq : Bsign prec emax x = Bsign prec emax y),
    x=y.
Proof.
  intros.
  destruct x; destruct y; cbn in *; try congruence.
  1, 2: exfalso; apply (F2R_not0 radix2 s0 m e); congruence.
  unfold bounded in *.
  { subst s0.
    assert ((Float radix2 (cond_Zopp s (Z.pos m)) e) =
           (Float radix2 (cond_Zopp s (Z.pos m0)) e1)).
    { eapply canonical_unique.
      { apply canonical_canonical_mantissa  with (prec := prec) (emax := emax).
        eapply andb_true_iff. rewrite andb_comm. exact e0.
      }
      { apply canonical_canonical_mantissa  with (prec := prec) (emax := emax).
        eapply andb_true_iff. rewrite andb_comm. exact e2.
      }
      assumption.
    }
    destruct s; cbn in H;
    inversion H; subst m0; subst e1;
    f_equal;
    apply Eqdep_dec.UIP_dec;
      decide equality.
  } 
Qed.  

Lemma round_mode_IZR : forall mode x, round_mode mode (IZR x) = x.
Proof.
  intros. destruct mode; cbn.
  - apply Znearest_IZR.
  - apply Ztrunc_IZR.
  - apply Zfloor_IZR.
  - apply Zceil_IZR.
  - apply Znearest_IZR.
Qed.

Lemma round_F2R: forall mode s m e
 (BOUNDED : bounded prec emax m e = true),
 round radix2 fexp (round_mode mode)
       (F2R (Float radix2 (cond_Zopp s (Z.pos m)) e)) =
   (F2R (Float radix2 (cond_Zopp s (Z.pos m)) e)).
Proof.
intros.
unfold bounded in BOUNDED.
rewrite andb_true_iff in BOUNDED.
destruct BOUNDED as (CANONICAL & EMAX).
unfold canonical_mantissa in CANONICAL.
pose proof (canonical_canonical_mantissa _ _ s _ _ CANONICAL) as CANON.
  unfold canonical in CANON. simpl Fexp in CANON.
unfold round.
rewrite CANON.
unfold scaled_mantissa, cexp.
rewrite mag_F2R; cycle 1.
{ destruct s; cbn; intro ZERO; lia. }
rewrite mag_F2R; cycle 1.
{ destruct s; cbn; intro ZERO; lia. }
set (m' := (cond_Zopp s (Z.pos m))).
unfold F2R. simpl Fnum. simpl Fexp.
rewrite Rmult_assoc.
rewrite <- bpow_plus.
rewrite bpow_powerRZ.
unfold cexp in CANON. fold m' in CANON.
unfold F2R in CANON. simpl Fnum in CANON. simpl Fexp in CANON.
rewrite mag_mult_bpow in CANON; cycle 1.
{ unfold m'; destruct s; cbn; intro ZERO; apply eq_IZR in ZERO; lia.
}
rewrite <- CANON.
rewrite <- CANON.
replace (e + - e) with 0 by ring.
simpl.
rewrite <- mult_IZR.
rewrite round_mode_IZR.
rewrite -> mult_IZR.
ring.
Qed.

Lemma round_B2R:
  forall mode x,
  round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode mode)
        (B2R prec emax x) = B2R prec emax x.
Proof.
  intros. destruct x.
  1,2,3: apply round_0; apply valid_rnd_round_mode.
  apply round_F2R. assumption.
Qed.

(*
(** Multiplication by 1 is identity *)
Theorem Bmult_1_id_r_finite:
  forall mult_nan mode (x : binary_float) (x_finite : is_finite _ _ x = true),
  Bmult _ _ _ Hmax mult_nan mode x (BofZ 1%Z) = x.
Proof.
  intros.
  assert (2^0 <= 2 ^ prec) as HPREC.
  unfold Prec_gt_0 in *.
  { apply Z.pow_le_mono_r. reflexivity. lia. }
  change (2^0) with 1 in HPREC.
  assert (- 2 ^ prec <= 1 <= 2 ^ prec) as ONE_PREC by lia.
  pose proof (BofZ_exact 1 ONE_PREC) as (C1R & C1F & C1S).
  pose proof (Bmult_correct prec emax prec_gt_0_ Hmax mult_nan mode x (BofZ 1)) as C2.
  rewrite C1R in C2. rewrite C1F in C2. rewrite C1S in C2.
  rewrite Rmult_1_r in C2.
  rewrite andb_true_r in C2.
  change (1 <? 0) with false in C2.
  rewrite xorb_false_r in C2.
  rewrite x_finite in C2.
  destruct Rlt_bool eqn:RLT.
  { destruct C2 as (C2R & C2F & C2S).
    apply fully_known.
    - apply is_finite_not_is_nan. assumption.
    - apply is_finite_not_is_nan. assumption.
    - rewrite C2R. apply round_B2R.
    - congruence.
    - apply C2S. apply is_finite_not_is_nan.
      assumption.
  }
  rewrite round_B2R in RLT.
  pose proof (abs_B2R_lt_emax prec emax x) as MAX.
  apply Rlt_bool_true in MAX.
  congruence.
Qed.

Definition nan_copies_r binop_nan :=
  forall x y, (is_nan prec emax x)=true ->(is_nan prec emax y)=false ->
              proj1_sig (A := Binary.binary_float prec emax) (P := fun w => is_nan prec emax w = true) (binop_nan x y) =x.

(* If NaN payload is copied from the first argument, then multiplication by 1 is the identity *)
Theorem Bmult_1_id_r:
  forall mult_nan
         (NAN_OK : nan_copies_r mult_nan)
         mode (x : binary_float),
  Bmult _ _ _ Hmax mult_nan mode x (BofZ 1%Z) = x.
Proof.
  intros.
  assert (2^0 <= 2 ^ prec) as HPREC.
  unfold Prec_gt_0 in *.
  { apply Z.pow_le_mono_r. reflexivity. lia. }
  change (2^0) with 1 in HPREC.
  assert (- 2 ^ prec <= 1 <= 2 ^ prec) as ONE_PREC by lia.
  pose proof (BofZ_exact 1 ONE_PREC) as (C1R & C1F & C1S).
  pose proof (Bmult_correct prec emax prec_gt_0_ Hmax mult_nan mode x (BofZ 1)) as C2.
  rewrite C1R in C2. rewrite C1F in C2. rewrite C1S in C2.
  assert ((Rlt_bool 0 (bpow radix2 emax))=true) as BPOW0.
  { apply Rlt_bool_true.
    apply bpow_gt_0.
  }
  change (1 <? 0) with false in C2.
  rewrite xorb_false_r in C2.
  rewrite andb_true_r in C2.
  rewrite Rmult_1_r in C2.
  rewrite round_B2R in C2.
  destruct x.
  1,4: apply Bmult_1_id_r_finite; reflexivity.
  1,2: simpl B2R in C2.
  1,2: rewrite Rabs_R0 in C2.
  1,2: rewrite BPOW0 in C2.
  1,2: destruct C2 as (C2R & C2F & C2S).
  { unfold Bmult.
    destruct (BofZ 1); cbn in *.
    1, 2, 3: lra.
    rewrite C2S by trivial.
    reflexivity.
  }
  unfold Bmult.
  pose proof (NAN_OK  (B754_nan prec emax s pl e) (BofZ 1)) as NAN_OK_x_y.
  change ( is_nan prec emax (B754_nan prec emax s pl e)) with true in NAN_OK_x_y.
  rewrite is_finite_not_is_nan in NAN_OK_x_y by assumption.
  intuition.
  destruct mult_nan; cbn in H3.
  subst x. unfold build_nan. reflexivity.
Qed.
 *)

(** Multiplication by 2 is diagonal addition. *)

Theorem Bmult2_Bplus:
  forall plus_nan mult_nan mode (f: binary_float),
  (forall (x y: binary_float),
   is_nan _ _ x = true -> is_finite _ _ y = true -> plus_nan x x = mult_nan x y) ->
  Bplus _ _ _ _ plus_nan mode f f = Bmult _ _ _ _ mult_nan mode f (BofZ 2%Z).
Proof.
  intros until f; intros NAN.
  destruct (BofZ_representable 2) as (A & B & C).
  apply (integer_representable_2p 1). red in prec_gt_0_, prec_lt_emax_; lia.
  pose proof (Bmult_correct _ _ _ _ mult_nan mode f (BofZ 2%Z)). fold emin in H.
  rewrite A, B, C in H. rewrite xorb_false_r in H.
  destruct (is_finite _ _ f) eqn:FIN.
- pose proof (Bplus_correct _ _ _ _ plus_nan mode f f FIN FIN). fold emin in H0.
  assert (EQ: (B2R prec emax f * IZR 2%Z = B2R prec emax f + B2R prec emax f)%R).
  { ring. }
  rewrite <- EQ in H0. destruct Rlt_bool.
  + destruct H0 as (P & Q & R). destruct H as (S & T & U).
    apply B2R_Bsign_inj; auto.
    rewrite P, S. auto.
    rewrite R, U.
    replace 0%R with (0 * 2)%R by ring. rewrite Rcompare_mult_r.
    rewrite andb_diag, orb_diag. destruct f as [s|s|s p H|s m e H]; try discriminate; simpl.
    rewrite Rcompare_Eq by auto. destruct mode; auto.
    replace 0%R with (@F2R radix2 {| Fnum := 0%Z; Fexp := e |}).
    rewrite Rcompare_F2R. destruct s; auto.
    unfold F2R. simpl. ring.
    apply IZR_lt. lia.
    destruct (Bmult prec emax _ _ mult_nan mode f (BofZ 2)); reflexivity || discriminate.
  + destruct H0 as (P & Q). apply B2FF_inj. rewrite P, H. auto.
- destruct f as [sf|sf|sf pf Hf|sf mf ef Hf]; try discriminate.
  + unfold Bplus. simpl BinarySingleNaN.Bplus. rewrite eqb_true. destruct (BofZ 2) as [| | |s2 m2 e2 H2] eqn:B2; try discriminate; simpl in *.
    assert ((0 = 2)%Z) by (apply eq_IZR; auto). discriminate.
    subst s2. unfold Bmult. simpl. rewrite xorb_false_r. auto.
    auto.
  + unfold Bplus, Bmult. rewrite <- NAN by auto. auto.
Qed.

(** Divisions that can be turned into multiplications by an inverse *)

Definition Bexact_inverse_mantissa := Z.iter (prec - 1) xO xH.

Remark Bexact_inverse_mantissa_value:
  Zpos Bexact_inverse_mantissa = 2 ^ (prec - 1).
Proof.
  assert (REC: forall n, Z.pos (nat_rect _ xH (fun _ => xO) n) = 2 ^ (Z.of_nat n)).
  { induction n. reflexivity.
    simpl nat_rect. transitivity (2 * Z.pos (nat_rect _ xH (fun _ => xO) n)). reflexivity.
    rewrite Nat2Z.inj_succ. rewrite IHn. unfold Z.succ. rewrite Zpower_plus by lia.
    change (2 ^ 1) with 2. ring. }
  red in prec_gt_0_.
  unfold Bexact_inverse_mantissa. rewrite iter_nat_of_Z by lia. rewrite REC.
  rewrite Zabs2Nat.id_abs. rewrite Z.abs_eq by lia. auto.
Qed.

Remark Bexact_inverse_mantissa_digits2_pos:
  Z.pos (digits2_pos Bexact_inverse_mantissa) = prec.
Proof.
  assert (DIGITS: forall n, digits2_pos (nat_rect _ xH (fun _ => xO) n) = Pos.of_nat (n+1)).
  { induction n; simpl. auto. rewrite IHn. destruct n; auto. }
  red in prec_gt_0_.
  unfold Bexact_inverse_mantissa. rewrite iter_nat_of_Z by lia. rewrite DIGITS.
  rewrite Zabs2Nat.abs_nat_nonneg, Z2Nat.inj_sub by lia.
  destruct prec; try  discriminate. rewrite Nat.sub_add.
  simpl. rewrite Pos2Nat.id. auto.
  simpl. zify; lia.
Qed.

Remark bounded_Bexact_inverse:
  forall e,
  emin <= e <= emax - prec <-> bounded prec emax Bexact_inverse_mantissa e = true.
Proof.
  intros. unfold bounded, canonical_mantissa. rewrite andb_true_iff.
  rewrite <- Zeq_is_eq_bool. rewrite <- Zle_is_le_bool.
  rewrite Bexact_inverse_mantissa_digits2_pos.
  unfold fexp, FLT_exp, emin. lia.
Qed.

Program Definition Bexact_inverse (f: binary_float) : option binary_float :=
  match f with
  | B754_finite _ _ s m e B =>
      if Pos.eq_dec m Bexact_inverse_mantissa then
      let e' := -e - (prec - 1) * 2 in
      if Z_le_dec emin e' then
      if Z_le_dec e' emax then
        Some(B754_finite _ _ s m e' _)
      else None else None else None
  | _ => None
  end.
Next Obligation.
  rewrite <- bounded_Bexact_inverse in B. rewrite <- bounded_Bexact_inverse.
  unfold emin in *. lia.
Qed.

Lemma Bexact_inverse_correct:
  forall f f', Bexact_inverse f = Some f' ->
  is_finite_strict _ _ f = true
  /\ is_finite_strict _ _ f' = true
  /\ B2R _ _ f' = (/ B2R _ _ f)%R
  /\ B2R _ _ f <> 0%R
  /\ Bsign _ _ f' = Bsign _ _ f.
Proof with (try discriminate).
  intros f f' EI. unfold Bexact_inverse in EI. destruct f as [s|s|s p H|s m e H]...
  destruct (Pos.eq_dec m Bexact_inverse_mantissa)...
  set (e' := -e - (prec - 1) * 2) in *.
  destruct (Z_le_dec emin e')...
  destruct (Z_le_dec e' emax)...
  inversion EI; clear EI; subst f' m.
  split. auto. split. auto. split. unfold B2R. rewrite Bexact_inverse_mantissa_value.
  unfold F2R; simpl. rewrite IZR_cond_Zopp.
  rewrite <- ! cond_Ropp_mult_l.
  red in prec_gt_0_.
  replace (IZR (2 ^ (prec - 1))) with (bpow radix2 (prec - 1))
  by (symmetry; apply (IZR_Zpower radix2); lia).
  rewrite <- ! bpow_plus.
  replace (prec - 1 + e') with (- (prec - 1 + e)) by (unfold e'; lia).
  rewrite bpow_opp. unfold cond_Ropp; destruct s; auto.
  field. apply Rgt_not_eq. apply bpow_gt_0.
  split. simpl. apply F2R_neq_0. destruct s; simpl in H; discriminate.
  auto.
Qed.

Theorem Bdiv_mult_inverse:
  forall div_nan mult_nan mode x y z,
  (forall (x y z: binary_float),
   is_nan _ _ x = true -> is_finite _ _ y = true -> is_finite _ _ z = true ->
   div_nan x y = mult_nan x z) ->
  Bexact_inverse y = Some z ->
  Bdiv _ _ _ _ div_nan mode x y = Bmult _ _ _ _ mult_nan mode x z.
Proof.
  intros until z; intros NAN; intros. destruct (Bexact_inverse_correct _ _ H) as (A & B & C & D & E).
  pose proof (Bmult_correct _ _ _ _ mult_nan mode x z).
  fold emin in H0. fold fexp in H0.
  pose proof (Bdiv_correct _ _ _ _ div_nan mode x y D).
  fold emin in H1. fold fexp in H1.
  unfold Rdiv in H1. rewrite <- C in H1.
  destruct (is_finite _ _ x) eqn:FINX.
- destruct Rlt_bool.
  + destruct H0 as (P & Q & R). destruct H1 as (S & T & U).
    apply B2R_Bsign_inj; auto.
    rewrite Q. simpl. apply is_finite_strict_finite; auto.
    rewrite P, S. auto.
    rewrite R, U, E. auto.
    apply is_finite_not_is_nan; auto.
    apply is_finite_not_is_nan. rewrite Q. simpl. apply is_finite_strict_finite; auto.  + apply B2FF_inj. rewrite H0, H1. rewrite E. auto.
- destruct y; try discriminate. destruct z; try discriminate.
  destruct x; try discriminate; simpl.
  + simpl in E. now rewrite E.
  + unfold Bdiv. now rewrite (NAN _ _ (B754_finite prec emax s0 m0 e1 e2)).
Qed.

(** ** Conversion from scientific notation *)

(** Russian peasant exponentiation *)

Fixpoint pos_pow (x y: positive) : positive :=
  match y with
  | xH => x
  | xO y => Pos.square (pos_pow x y)
  | xI y => Pos.mul x (Pos.square (pos_pow x y))
  end.

Lemma pos_pow_spec:
  forall x y, Z.pos (pos_pow x y) = Z.pos x ^ Z.pos y.
Proof.
  intros x.
  assert (REC: forall y a, Pos.iter (Pos.mul x) a y = Pos.mul (pos_pow x y) a).
  { induction y; simpl; intros.
  - rewrite ! IHy, Pos.square_spec, ! Pos.mul_assoc. auto.
  - rewrite ! IHy, Pos.square_spec, ! Pos.mul_assoc. auto.
  - auto.
  }
  intros. simpl. rewrite <- Pos2Z.inj_pow_pos. unfold Pos.pow. rewrite REC. rewrite Pos.mul_1_r. auto.
Qed.

(** Given a base [base], a mantissa [m] and an exponent [e], the following function
  computes the FP number closest to [m * base ^ e], using round to odd, ties break to even.
  The algorithm is naive, computing [base ^ |e|] exactly before doing a multiplication or
  division with [m].  However, we treat specially very large or very small values of [e],
  when the result is known to be [+infinity] or [0.0] respectively. *)

Program Definition Bparse (base: positive) (m: positive) (e: Z): binary_float :=
  match e with
  | Z0 =>
     BofZ (Zpos m)
  | Zpos p =>
     if e * Z.log2 (Zpos base) <? emax
     then BofZ (Zpos m * Zpos (pos_pow base p))
     else B754_infinity _ _ false
  | Zneg p =>
     if e * Z.log2 (Zpos base) + Z.log2_up (Zpos m) <? emin
     then B754_zero _ _ false
     else BSN2B' prec emax (SF2B _ (proj1 (Bdiv_correct_aux prec emax _ _ mode_NE
                                     false m Z0 false (pos_pow base p) Z0))) _
  end.
Next Obligation.
destruct Bdiv_correct_aux as [H1 H2].
rewrite is_nan_SF2B.
clear H1.
destruct SFdiv_core_binary as [[mz ez] lz].
destruct Rlt_bool.
destruct H2 as [_ [H _]].
now destruct BinarySingleNaN.binary_round_aux.
simpl in H2.
rewrite H2.
apply is_nan_binary_overflow.
Qed.

(** Properties of [Z.log2] and [Z.log2_up]. *)

Lemma Zpower_log:
  forall (base: radix) n,
  0 < n ->
  2 ^ (n * Z.log2 base) <= base ^ n <= 2 ^ (n * Z.log2_up base).
Proof.
  intros.
  assert (A: 0 < base) by apply radix_gt_0.
  assert (B: 0 <= Z.log2 base) by apply Z.log2_nonneg.
  assert (C: 0 <= Z.log2_up base) by apply Z.log2_up_nonneg.
  destruct (Z.log2_spec base) as [D E]; auto.
  destruct (Z.log2_up_spec base) as [F G]. apply radix_gt_1.
  assert (K: 0 <= 2 ^ Z.log2 base) by (apply Z.pow_nonneg; lia).
  rewrite ! (Z.mul_comm n). rewrite ! Z.pow_mul_r by lia.
  split; apply Z.pow_le_mono_l; lia.
Qed.

Lemma bpow_log_pos:
  forall (base: radix) n,
  0 < n ->
  (bpow radix2 (n * Z.log2 base)%Z <= bpow base n)%R.
Proof.
  intros. rewrite <- ! IZR_Zpower. apply IZR_le; apply Zpower_log; auto.
  lia.
  rewrite Z.mul_comm; apply Zmult_gt_0_le_0_compat. lia. apply Z.log2_nonneg.
Qed.

Lemma bpow_log_neg:
  forall (base: radix) n,
  n < 0 ->
  (bpow base n <= bpow radix2 (n * Z.log2 base)%Z)%R.
Proof.
  intros. set (m := -n). replace n with (-m) by (unfold m; lia).
  rewrite ! Z.mul_opp_l, ! bpow_opp. apply Rinv_le.
  apply bpow_gt_0.
  apply bpow_log_pos. unfold m; lia.
Qed.

(** Overflow and underflow conditions. *)

Lemma round_integer_overflow:
  forall (base: radix) e m,
  0 < e ->
  emax <= e * Z.log2 base ->
  (bpow radix2 emax <= round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e))%R.
Proof.
  intros.
  rewrite <- (round_generic radix2 fexp (round_mode mode_NE) (bpow radix2 emax)); auto.
  apply round_le; auto. apply fexp_correct; auto. apply valid_rnd_round_mode.
  rewrite <- (Rmult_1_l (bpow radix2 emax)). apply Rmult_le_compat.
  apply Rle_0_1.
  apply bpow_ge_0.
  apply IZR_le. zify; lia.
  eapply Rle_trans. eapply bpow_le. eassumption. apply bpow_log_pos; auto.
  apply generic_format_FLT. exists (Float radix2 1 emax).
  unfold F2R; simpl. ring.
  simpl. apply (Zpower_gt_1 radix2); auto.
  simpl. unfold emin; red in prec_gt_0_, prec_lt_emax_; lia.
Qed.

Lemma round_NE_underflows:
  forall x,
  (0 <= x <= bpow radix2 (emin - 1))%R ->
  round radix2 fexp (round_mode mode_NE) x = 0%R.
Proof.
  intros.
  set (eps := bpow radix2 (emin - 1)) in *.
  assert (A: round radix2 fexp (round_mode mode_NE) eps = 0%R).
  { unfold round. simpl.
    assert (E: cexp radix2 fexp eps = emin).
    { unfold cexp, eps. rewrite mag_bpow. unfold fexp, FLT_exp. zify; red in prec_gt_0_; lia. }
    unfold scaled_mantissa; rewrite E.
    assert (P: (eps * bpow radix2 (-emin) = / 2)%R).
    { unfold eps. rewrite <- bpow_plus. replace (emin - 1 + -emin) with (-1) by lia. auto. }
    rewrite P. unfold Znearest.
    assert (F: Zfloor (/ 2)%R = 0).
    { apply Zfloor_imp. simpl. lra. }
    rewrite F. rewrite Rminus_0_r. rewrite Rcompare_Eq by auto.
    simpl. unfold F2R; simpl. apply Rmult_0_l.
  }
  apply Rle_antisym.
- rewrite <- A. apply round_le. apply fexp_correct; auto. apply valid_rnd_round_mode. tauto.
- rewrite <- (round_0 radix2 fexp (round_mode mode_NE)).
  apply round_le. apply fexp_correct; auto. apply valid_rnd_round_mode. tauto.
Qed.

Lemma round_integer_underflow:
  forall (base: radix) e m,
  e < 0 ->
  e * Z.log2 base + Z.log2_up (Zpos m) < emin ->
  round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e) = 0%R.
Proof.
  intros. apply round_NE_underflows. split.
- apply Rmult_le_pos. apply IZR_le. zify; lia. apply bpow_ge_0.
- apply Rle_trans with (bpow radix2 (Z.log2_up (Z.pos m) + e * Z.log2 base)).
+ rewrite bpow_plus. apply Rmult_le_compat.
  apply IZR_le; zify; lia.
  apply bpow_ge_0.
  rewrite <- IZR_Zpower. apply IZR_le.
  destruct (Z.eq_dec (Z.pos m) 1).
  rewrite e0. simpl. lia.
  apply Z.log2_up_spec. zify; lia.
  apply Z.log2_up_nonneg.
  apply bpow_log_neg. auto.
+ apply bpow_le. lia.
Qed.

(** Correctness of Bparse *)

Theorem Bparse_correct:
  forall b m e (BASE: 2 <= Zpos b),
  let base := {| radix_val := Zpos b; radix_prop := Zle_imp_le_bool _ _ BASE |} in
  let r := round radix2 fexp (round_mode mode_NE) (IZR (Zpos m) * bpow base e) in
  if Rlt_bool (Rabs r) (bpow radix2 emax) then
     B2R _ _ (Bparse b m e) = r
  /\ is_finite _ _ (Bparse b m e) = true
  /\ Bsign _ _ (Bparse b m e) = false
  else
    B2FF _ _ (Bparse b m e) = F754_infinity false.
Proof.
  intros.
  assert (A: forall x, @F2R radix2 {| Fnum := x; Fexp := 0 |} = IZR x).
  { intros. unfold F2R, Fnum; simpl. ring. }
  unfold Bparse, r. destruct e as [ | e | e].
- (* e = Z0 *)
  change (bpow base 0) with 1%R. rewrite Rmult_1_r.
  exact (BofZ_correct (Z.pos m)).
- (* e = Zpos e *)
  destruct (Z.ltb_spec (Z.pos e * Z.log2 (Z.pos b)) emax).
+ (* no overflow *)
  rewrite pos_pow_spec. rewrite <- IZR_Zpower by (zify; lia). rewrite <- mult_IZR.
  replace false with (Z.pos m * Z.pos b ^ Z.pos e <? 0).
  exact (BofZ_correct (Z.pos m * Z.pos b ^ Z.pos e)).
  rewrite Z.ltb_ge. rewrite Z.mul_comm. apply Zmult_gt_0_le_0_compat. zify; lia.  apply (Zpower_ge_0 base).
+ (* overflow *)
  rewrite Rlt_bool_false. auto. eapply Rle_trans; [idtac|apply Rle_abs].
  apply (round_integer_overflow base). zify; lia. auto.
- (* e = Zneg e *)
  destruct (Z.ltb_spec (Z.neg e * Z.log2 (Z.pos b) + Z.log2_up (Z.pos m)) emin).
+ (* undeflow *)
  rewrite round_integer_underflow; auto.
  rewrite Rlt_bool_true. auto.
  replace (Rabs 0)%R with 0%R. apply bpow_gt_0. apply (abs_IZR 0).
  zify; lia.
+ (* no underflow *)
  rewrite B2R_BSN2B', B2R_SF2B.
  rewrite B2FF_BSN2B', B2SF_SF2B.
  rewrite Bsign_BSN2B', Bsign_SF2B.
  rewrite is_finite_BSN2B', is_finite_SF2B.
  generalize (Bdiv_correct_aux prec emax _ _ mode_NE false m 0 false (pos_pow b e) 0).
  set (f := let '(mz, ez, lz) := SFdiv_core_binary prec emax (Z.pos m) 0 (Z.pos (pos_pow b e)) 0
         in binary_round_aux prec emax mode_NE (xorb false false) mz ez lz).
  fold emin; fold fexp. rewrite ! A. unfold cond_Zopp. rewrite pos_pow_spec.
  assert (B: (IZR (Z.pos m) / IZR (Z.pos b ^ Z.pos e) =
              IZR (Z.pos m) * bpow base (Z.neg e))%R).
  { change (Z.neg e) with (- (Z.pos e)). rewrite bpow_opp. auto. }
  rewrite B. intros [P Q].
  destruct (Rlt_bool
     (Rabs
        (round radix2 fexp (round_mode mode_NE)
           (IZR (Z.pos m) * bpow base (Z.neg e))))
    (bpow radix2 emax)).
* destruct Q as (Q1 & Q2 & Q3).
  split. rewrite Q1. auto.
  split; auto.
* rewrite Q. auto.
Qed.

End Extra_ops.

(** ** Conversions between two FP formats *)

Section Conversions.

Variable prec1 emax1 prec2 emax2 : Z.
Context (prec1_gt_0_ : Prec_gt_0 prec1) (prec2_gt_0_ : Prec_gt_0 prec2).
Let emin1 := (3 - emax1 - prec1)%Z.
Let fexp1 := FLT_exp emin1 prec1.
Let emin2 := (3 - emax2 - prec2)%Z.
Let fexp2 := FLT_exp emin2 prec2.
Hypothesis Hmax1 : (prec1 < emax1)%Z.
Hypothesis Hmax2 : (prec2 < emax2)%Z.
Let binary_float1 := binary_float prec1 emax1.
Let binary_float2 := binary_float prec2 emax2.

Definition Bconv (conv_nan: binary_float1 -> {x | is_nan prec2 emax2 x = true}) (md: mode) (f: binary_float1) : binary_float2 :=
  match f with
    | B754_nan _ _ _ _ _ => build_nan prec2 emax2 (conv_nan f)
    | B754_infinity _ _ s => B754_infinity _ _ s
    | B754_zero _ _ s => B754_zero _ _ s
    | B754_finite _ _ s m e _ => binary_normalize _ _ _ Hmax2 md (cond_Zopp s (Zpos m)) e s
  end.

Theorem Bconv_correct:
  forall conv_nan m f,
  is_finite _ _ f = true ->
  if Rlt_bool (Rabs (round radix2 fexp2 (round_mode m) (B2R _ _ f))) (bpow radix2 emax2)
  then
     B2R _ _ (Bconv conv_nan m f) = round radix2 fexp2 (round_mode m) (B2R _ _ f)
  /\ is_finite _ _ (Bconv conv_nan m f) = true
  /\ Bsign _ _ (Bconv conv_nan m f) = Bsign _ _ f
  else
     B2FF _ _ (Bconv conv_nan m f) = binary_overflow prec2 emax2 m (Bsign _ _ f).
Proof.
  intros. destruct f as [sf|sf|sf pf Hf|sf mf ef Hf]; try discriminate.
- simpl. rewrite round_0. rewrite Rabs_R0. rewrite Rlt_bool_true. auto.
  apply bpow_gt_0. apply valid_rnd_round_mode.
- generalize (binary_normalize_correct _ _ _ Hmax2 m (cond_Zopp sf (Zpos mf)) ef sf).
  fold emin2; fold fexp2. simpl. destruct Rlt_bool.
  + intros (A & B & C). split. auto. split. auto. rewrite C.
    destruct sf; simpl.
    rewrite Rcompare_Lt. auto. apply F2R_lt_0. simpl. compute; auto.
    rewrite Rcompare_Gt. auto. apply F2R_gt_0. simpl. compute; auto.
  + intros A. rewrite A. f_equal. destruct sf.
    apply Rlt_bool_true. apply F2R_lt_0. simpl. compute; auto.
    apply Rlt_bool_false. apply Rlt_le. apply Rgt_lt. apply F2R_gt_0. simpl. compute; auto.
Qed.

(** Converting a finite FP number to higher or equal precision preserves its value. *)

Theorem Bconv_widen_exact:
  (prec2 >= prec1)%Z -> (emax2 >= emax1)%Z ->
  forall conv_nan m f,
  is_finite _ _ f = true ->
     B2R _ _ (Bconv conv_nan m f) = B2R _ _ f
  /\ is_finite _ _ (Bconv conv_nan m f) = true
  /\ Bsign _ _ (Bconv conv_nan m f) = Bsign _ _ f.
Proof.
  intros PREC EMAX; intros. generalize (Bconv_correct conv_nan m f H).
  assert (LT: (Rabs (B2R _ _ f) < bpow radix2 emax2)%R).
  {
    destruct f; try discriminate; simpl.
    rewrite Rabs_R0. apply bpow_gt_0.
    apply Rlt_le_trans with (bpow radix2 emax1).
    rewrite F2R_cond_Zopp. rewrite abs_cond_Ropp. rewrite <- F2R_Zabs. simpl Z.abs.
    eapply bounded_lt_emax; eauto.
    apply bpow_le. lia.
  }
  assert (EQ: round radix2 fexp2 (round_mode m) (B2R prec1 emax1 f) = B2R prec1 emax1 f).
  {
    apply round_generic. apply valid_rnd_round_mode. eapply generic_inclusion_le.
    5: apply generic_format_B2R. apply fexp_correct; auto. apply fexp_correct; auto.
    instantiate (1 := emax2). intros. unfold fexp, fexp2, FLT_exp. unfold emin, emin2. lia.
    apply Rlt_le; auto.
  }
  rewrite EQ. rewrite Rlt_bool_true by auto. auto.
Qed.

(** Conversion from integers and change of format *)

Theorem Bconv_BofZ:
  forall conv_nan n,
  integer_representable prec1 emax1 n ->
  Bconv conv_nan mode_NE (BofZ prec1 emax1 _ Hmax1 n) = BofZ prec2 emax2 _ Hmax2 n.
Proof.
  intros.
  destruct (BofZ_representable _ _ _ Hmax1 n H) as (A & B & C).
  set (f := BofZ prec1 emax1 prec1_gt_0_ Hmax1 n) in *.
  generalize (Bconv_correct conv_nan mode_NE f B).
  unfold BofZ.
  generalize (binary_normalize_correct _ _ _ Hmax2 mode_NE n 0 false).
  fold emin2; fold fexp2. rewrite A.
  replace (F2R {| Fnum := n; Fexp := 0 |}) with (IZR n).
  destruct Rlt_bool.
- intros (P & Q & R) (D & E & F). apply B2R_Bsign_inj; auto.
  now rewrite P, D.
  rewrite F, C, R. rewrite Rcompare_IZR.
  unfold Z.ltb. auto.
- intros P Q. apply B2FF_inj. rewrite P, Q. rewrite C. f_equal.
  generalize (Zlt_bool_spec n 0); intros LT; inversion LT.
  rewrite Rlt_bool_true; auto. apply IZR_lt; auto.
  rewrite Rlt_bool_false; auto. apply IZR_le; auto.
- unfold F2R; simpl. rewrite Rmult_1_r. auto.
Qed.

(** Change of format (to higher precision) and conversion to integer. *)

Theorem ZofB_Bconv:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall conv_nan m f n,
  ZofB _ _ f = Some n -> ZofB _ _ (Bconv conv_nan m f) = Some n.
Proof.
  intros. rewrite ZofB_correct in H1. destruct (is_finite _ _ f) eqn:FIN; inversion H1.
  destruct (Bconv_widen_exact H H0 conv_nan m f) as (A & B & C). auto.
  rewrite ZofB_correct. rewrite B. rewrite A. auto.
Qed.

Theorem ZofB_range_Bconv:
  forall min1 max1 min2 max2,
  prec2 >= prec1 -> emax2 >= emax1 -> min2 <= min1 -> max1 <= max2 ->
  forall conv_nan m f n,
  ZofB_range _ _ f min1 max1 = Some n ->
  ZofB_range _ _ (Bconv conv_nan m f) min2 max2 = Some n.
Proof.
  intros.
  destruct (ZofB_range_inversion _ _ _ _ _ _ H3) as (A & B & C).
  unfold ZofB_range. erewrite ZofB_Bconv by eauto.
  rewrite ! Zle_bool_true by lia. auto.
Qed.

(** Change of format (to higher precision) and comparison. *)

Theorem Bcompare_Bconv_widen:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall conv_nan m x y,
  Bcompare _ _ (Bconv conv_nan m x) (Bconv conv_nan m y) = Bcompare _ _ x y.
Proof.
  intros. destruct (is_finite _ _ x && is_finite _ _ y) eqn:FIN.
- apply andb_true_iff in FIN. destruct FIN.
  destruct (Bconv_widen_exact H H0 conv_nan m x H1) as (A & B & C).
  destruct (Bconv_widen_exact H H0 conv_nan m y H2) as (D & E & F).
  rewrite ! Bcompare_correct by auto. rewrite A, D. auto.
- generalize (Bconv_widen_exact H H0 conv_nan m x)
             (Bconv_widen_exact H H0 conv_nan m y); intros P Q.
  destruct x as [sx|sx|sx px Hx|sx mx ex Hx], y as [sy|sy|sy py Hy|sy my ey Hy]; try discriminate; simpl in P, Q; simpl;
  repeat (match goal with |- context [conv_nan ?b ?pl] => destruct (conv_nan b pl) end);
  auto.
  destruct Q as (D & E & F); auto.
  now destruct binary_normalize.
  destruct P as (A & B & C); auto.
  now destruct binary_normalize.
  destruct P as (A & B & C); auto.
  now destruct binary_normalize.
Qed.

Lemma is_finite_Bopp: forall prec emax map x, is_finite prec emax (Bopp _ _ map x) = is_finite _ _ x.
Proof.
  intros; destruct x; reflexivity.
Qed.

Lemma is_nan_Bopp: forall prec emax map x, is_nan prec emax (Bopp _ _ map x) = is_nan _ _ x.
Proof.
  intros; destruct x; reflexivity.
Qed.

Lemma B2R_negb : forall s m e e0,
    (B2R prec1 emax1 (B754_finite prec1 emax1 (negb s) m e e0)) =
      (- (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0)))%R.
Proof.
  simpl. intros.
  rewrite cond_Zopp_negb.
  rewrite <- F2R_opp. reflexivity.
Qed.

Lemma is_nan_Bconv: forall map_nan mode x,
    is_nan _ _ (Bconv map_nan mode x) = is_nan _ _ x.
Proof.
  destruct x; try reflexivity. simpl.
  unfold binary_normalize, BinarySingleNaN.binary_normalize.
  destruct s; apply is_nan_BSN2B'.
Qed.

Lemma Rcompare_F2R_0:
  forall s m e,
    Rcompare (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) 0 =
      if s then Lt else Gt.
Proof.
  intros. unfold F2R. simpl.
  pose proof (bpow_gt_0 radix2 e) as BPOW.
  destruct s; simpl.
  - apply Rcompare_Lt.
    assert (IZR (Z.neg m) < 0)%R.
    { apply IZR_lt. lia. }
    nra.
  - apply Rcompare_Gt.
    assert (0 < IZR (Z.pos m))%R.
    { apply IZR_lt. lia. }
    nra.
Qed.

Lemma Rlt_bool_F2R_0:
  forall s m e,
    (Rlt_bool (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) 0) = s.
Proof.
  intros.
  pose proof (Rcompare_spec (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) 0).
  rewrite Rcompare_F2R_0 in H.
  destruct s; inversion H.
  - apply Rlt_bool_true. assumption.
  - apply Rlt_bool_false. lra.
Qed.

Lemma Bsign_Bconv_f:
  forall map_nan mode s m e e0,
  (Bsign prec2 emax2
     (Bconv map_nan mode (B754_finite prec1 emax1 s m e e0))) = s.
Proof.
  intros. unfold Bconv, binary_normalize.
  rewrite Bsign_BSN2B'.
  pose proof (BinarySingleNaN.binary_normalize_correct
                prec2 emax2 prec2_gt_0_ Hmax2 mode
                (cond_Zopp s (Z.pos m)) e s) as CORRECT.
  simpl in CORRECT.
  destruct Rlt_bool.
  { destruct CORRECT as (VAL & FINITE & SIGN).
    rewrite SIGN.
    rewrite Rcompare_F2R_0. destruct s; reflexivity.
  }
  unfold BinarySingleNaN.binary_normalize in *.
  rewrite Rlt_bool_F2R_0 in CORRECT.
  destruct s; simpl in *; rewrite B2SF_SF2B in CORRECT; rewrite Bsign_SF2B; rewrite CORRECT.
  all: unfold BinarySingleNaN.binary_overflow, overflow_to_inf;
    destruct mode; reflexivity.
Qed.

Theorem Bopp_Bconv_DN:
  forall map_nan1 map_nan1' map_nan2 map_nan2' (x: binary_float1) (NOT_NAN: is_nan _ _ x = false),
    (Bopp _ _ map_nan2 (Bconv map_nan1 mode_DN x)) =
      Bconv map_nan2' mode_UP (Bopp _ _ map_nan1' x).
Proof.
  intros.
  destruct x. 1,2: reflexivity. discriminate.
  destruct ((is_finite _ _  (Bconv map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0))) && (is_finite _ _ (Bconv map_nan2' mode_UP
                                                                                                              (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))))) eqn:FINITE.
  { rewrite andb_true_iff in FINITE.
    destruct FINITE as (FINITE1 & FINITE2).
    change  (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))
              with (B754_finite prec1 emax1 (negb s) m e e0).
    apply B2R_Bsign_inj.
    { rewrite is_finite_Bopp. assumption. }
    assumption.
    { rewrite B2R_Bopp.
      assert (is_finite _ _ (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0)) = true) as FINITE3'.
      { apply is_finite_Bopp. }
      pose proof (Bconv_correct map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0) (eq_refl _)) as CORRECT1.
      pose proof (Rlt_bool_spec
                (Rabs
                   (round radix2 fexp2 (round_mode mode_DN)
                      (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))))
                (bpow radix2 emax2)) as RLT1.
      destruct Rlt_bool; inversion RLT1; clear RLT1.
      { destruct CORRECT1 as (VAL1 & FIN1 & SIGN1).
        rewrite VAL1.
        pose proof (Bconv_correct map_nan2' mode_UP (B754_finite prec1 emax1 (negb s) m e e0)) as CORRECT2.
        pose proof (Rlt_bool_spec (Rabs
                   (round radix2 fexp2 (round_mode mode_UP)
                      (B2R prec1 emax1
                         (B754_finite prec1 emax1 (negb s) m e e0))))
                (bpow radix2 emax2)) as RLT2.
        destruct Rlt_bool; inversion RLT2; clear RLT2.
        { destruct CORRECT2 as (VAL2 & FIN2 & SIGN2).
          reflexivity.
          rewrite VAL2.
          change (round_mode mode_DN) with Zfloor.
          change (round_mode mode_UP) with Zceil.
          rewrite <- round_UP_opp.
          simpl.
          rewrite cond_Zopp_negb.
          rewrite <- F2R_opp.
          reflexivity.
        }
        change (round_mode mode_DN) with Zfloor in *.
        change (round_mode mode_UP) with Zceil in *.
        rewrite B2R_negb in H0.
        rewrite round_UP_opp in H0.
        rewrite Rabs_Ropp in H0.
        lra.
      }
      pose proof (Bconv_correct map_nan2' mode_UP (B754_finite prec1 emax1 (negb s) m e e0) (eq_refl _)) as CORRECT2.
      pose proof (Rlt_bool_spec (Rabs
                     (round radix2 fexp2 (round_mode mode_UP)
                      (B2R prec1 emax1
                         (B754_finite prec1 emax1 (negb s) m e e0))))
                (bpow radix2 emax2)) as RLT2.
      destruct Rlt_bool; inversion RLT2; clear RLT2.
      { change (round_mode mode_DN) with Zfloor in *.
        change (round_mode mode_UP) with Zceil in *.
        rewrite B2R_negb in H0.
        rewrite round_UP_opp in H0.
        rewrite Rabs_Ropp in H0.
        lra.
      }
      repeat rewrite <- FF2R_B2FF.
      rewrite CORRECT1. rewrite CORRECT2. simpl.
      destruct s; simpl. lra.
      rewrite <- F2R_opp. reflexivity.
    }
    rewrite Bsign_Bopp.
    2: { apply is_nan_Bconv. }
    repeat rewrite Bsign_Bconv_f.
    reflexivity.
  }
  rewrite andb_false_iff in FINITE.
  destruct FINITE as [INFINITE | INFINITE].
  - pose proof (Bconv_correct map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0) (eq_refl _)) as CORRECT1.
    pose proof (Rlt_bool_spec
               (Rabs
                  (round radix2 fexp2 (round_mode mode_DN)
                     (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))))
               (bpow radix2 emax2)) as RLT.
    destruct Rlt_bool; inversion RLT; clear RLT.
    { destruct CORRECT1 as (VAL & FINITE & SIGN).
      congruence. }
    assert (is_nan  _ _ (Bconv map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0)) = false) as NOT_NAN1.
    { apply is_nan_Bconv. }
    assert (Bsign _ _ (Bconv map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0)) = s) as SIGN.
    { apply Bsign_Bconv_f. }
    destruct (Bconv map_nan1 mode_DN (B754_finite prec1 emax1 s m e e0)); try discriminate.
    simpl in SIGN. subst s0. simpl.
    pose proof (binary_normalize_correct prec2 emax2 prec2_gt_0_ Hmax2 mode_UP
                  (cond_Zopp (negb s) (Z.pos m)) e (negb s)) as CORRECT2.
    pose proof (Rlt_bool_spec
                (Rabs
                   (round radix2 (fexp prec2 emax2) 
                      (round_mode mode_UP)
                      (@F2R radix2
                         {| Fnum := cond_Zopp (negb s) (Z.pos m); Fexp := e |})))
                (bpow radix2 emax2)) as SPEC.
    destruct Rlt_bool; inversion SPEC; clear SPEC; cycle 1.
    { rewrite Rlt_bool_F2R_0 in CORRECT2.
      unfold binary_overflow,BinarySingleNaN.binary_overflow, overflow_to_inf in CORRECT2.
      destruct s;
        destruct binary_normalize; simpl in *; try discriminate.
      injection CORRECT2; intro. subst s. reflexivity.
    }
    destruct CORRECT2 as (VAL2 & FINITE2 & SIGN2).
    change (round_mode mode_DN) with Zfloor in *.
    change (round_mode mode_UP) with Zceil in *.
    rewrite cond_Zopp_negb in H0.
    change {| Fnum := - cond_Zopp s (Z.pos m); Fexp := e |} with
      (@Fopp radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) in H0.
    rewrite F2R_opp in H0.
    rewrite round_UP_opp in H0.
    rewrite Rabs_Ropp in H0.
    change (round radix2 fexp2 Zfloor
               (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))) with
             (round radix2 (fexp prec2 emax2) Zfloor
                (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |})) in H.
    lra.
  - pose proof (Bconv_correct map_nan2' mode_UP
                  (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0)) (eq_refl _)) as CORRECT2.
    pose proof (Rlt_bool_spec (Rabs
                   (round radix2 fexp2 (round_mode mode_UP)
                      (B2R prec1 emax1
                         (Bopp prec1 emax1 map_nan1'
                            (B754_finite prec1 emax1 s m e e0)))))
                (bpow radix2 emax2)) as RLT.
    destruct Rlt_bool; inversion RLT; clear RLT.
    { destruct CORRECT2 as (VAL & FINITE & SIGN).
      congruence. }
    assert (is_nan _ _ (Bconv map_nan2' mode_UP
                          (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))) = false) as NOT_NAN2.
    { apply is_nan_Bconv. }
    assert (Bsign _ _ (Bconv map_nan2' mode_UP
    (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))) = (negb s)) as SIGN.
    { apply Bsign_Bconv_f. }
    destruct (Bconv map_nan2' mode_UP
    (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))); try discriminate.
    simpl in SIGN. subst s0. simpl.
    pose proof
           (binary_normalize_correct prec2 emax2 prec2_gt_0_ Hmax2 mode_DN
       (cond_Zopp s (Z.pos m)) e s) as CORRECT1.
    pose proof (Rlt_bool_spec
                   (Rabs
                   (round radix2 (fexp prec2 emax2) 
                      (round_mode mode_DN)
                      (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |})))
                (bpow radix2 emax2)) as SPEC.
    destruct Rlt_bool; inversion SPEC; clear SPEC; cycle 1.
    { rewrite Rlt_bool_F2R_0 in CORRECT1.
      unfold binary_overflow,BinarySingleNaN.binary_overflow, overflow_to_inf in CORRECT1.
      destruct s;
        destruct binary_normalize; simpl in *; try discriminate.
      injection CORRECT1; intro. subst s. reflexivity.
    }
    destruct CORRECT1 as (VAL1 & FINITE1 & SIGN1).
    change (round_mode mode_DN) with Zfloor in *.
    change (round_mode mode_UP) with Zceil in *.
    rewrite <- Rabs_Ropp in H0.    
    rewrite <- round_UP_opp in H0.
    simpl in H.
    rewrite cond_Zopp_negb in H.
    change {| Fnum := - cond_Zopp s (Z.pos m); Fexp := e |}
      with (@Fopp radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) in H.
    rewrite F2R_opp in H.
    change fexp2 with (fexp prec2 emax2) in H.
    lra.
Qed.
      
Theorem Bopp_Bconv_NE:
  forall map_nan1 map_nan1' map_nan2 map_nan2' (x: binary_float1) (NOT_NAN: is_nan _ _ x = false),
    (Bopp _ _ map_nan2 (Bconv map_nan1 mode_NE x)) =
      Bconv map_nan2' mode_NE (Bopp _ _ map_nan1' x).
Proof.
  intros.
  destruct x. 1,2: reflexivity. discriminate.
  destruct ((is_finite _ _  (Bconv map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0))) && (is_finite _ _ (Bconv map_nan2' mode_NE
                                                                                                              (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))))) eqn:FINITE.
  { rewrite andb_true_iff in FINITE.
    destruct FINITE as (FINITE1 & FINITE2).
    change  (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))
              with (B754_finite prec1 emax1 (negb s) m e e0).
    apply B2R_Bsign_inj.
    { rewrite is_finite_Bopp. assumption. }
    assumption.
    { rewrite B2R_Bopp.
      assert (is_finite _ _ (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0)) = true) as FINITE3'.
      { apply is_finite_Bopp. }
      pose proof (Bconv_correct map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0) (eq_refl _)) as CORRECT1.
      pose proof (Rlt_bool_spec
                (Rabs
                   (round radix2 fexp2 (round_mode mode_NE)
                      (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))))
                (bpow radix2 emax2)) as RLT1.
      destruct Rlt_bool; inversion RLT1; clear RLT1.
      { destruct CORRECT1 as (VAL1 & FIN1 & SIGN1).
        rewrite VAL1.
        pose proof (Bconv_correct map_nan2' mode_NE (B754_finite prec1 emax1 (negb s) m e e0)) as CORRECT2.
        pose proof (Rlt_bool_spec (Rabs
                   (round radix2 fexp2 (round_mode mode_NE)
                      (B2R prec1 emax1
                         (B754_finite prec1 emax1 (negb s) m e e0))))
                (bpow radix2 emax2)) as RLT2.
        destruct Rlt_bool; inversion RLT2; clear RLT2.
        { destruct CORRECT2 as (VAL2 & FIN2 & SIGN2).
          reflexivity.
          rewrite VAL2.
          change (round_mode mode_NE) with ZnearestE.
          rewrite <- round_NE_opp.
          simpl.
          rewrite cond_Zopp_negb.
          rewrite <- F2R_opp.
          reflexivity.
        }
        change (round_mode mode_NE) with ZnearestE in *.
        rewrite B2R_negb in H0.
        rewrite round_NE_opp in H0.
        rewrite Rabs_Ropp in H0.
        lra.
      }
      pose proof (Bconv_correct map_nan2' mode_NE (B754_finite prec1 emax1 (negb s) m e e0) (eq_refl _)) as CORRECT2.
      pose proof (Rlt_bool_spec (Rabs
                     (round radix2 fexp2 (round_mode mode_NE)
                      (B2R prec1 emax1
                         (B754_finite prec1 emax1 (negb s) m e e0))))
                (bpow radix2 emax2)) as RLT2.
      destruct Rlt_bool; inversion RLT2; clear RLT2.
      { change (round_mode mode_NE) with ZnearestE in *.
        rewrite B2R_negb in H0.
        rewrite round_NE_opp in H0.
        rewrite Rabs_Ropp in H0.
        lra.
      }
      repeat rewrite <- FF2R_B2FF.
      rewrite CORRECT1. rewrite CORRECT2. simpl. lra.
    }
    rewrite Bsign_Bopp.
    2: { apply is_nan_Bconv. }
    repeat rewrite Bsign_Bconv_f.
    reflexivity.
  }
  rewrite andb_false_iff in FINITE.
  destruct FINITE as [INFINITE | INFINITE].
  - pose proof (Bconv_correct map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0) (eq_refl _)) as CORRECT1.
    pose proof (Rlt_bool_spec
               (Rabs
                  (round radix2 fexp2 (round_mode mode_NE)
                     (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))))
               (bpow radix2 emax2)) as RLT.
    destruct Rlt_bool; inversion RLT; clear RLT.
    { destruct CORRECT1 as (VAL & FINITE & SIGN).
      congruence. }
    assert (is_nan  _ _ (Bconv map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0)) = false) as NOT_NAN1.
    { apply is_nan_Bconv. }
    assert (Bsign _ _ (Bconv map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0)) = s) as SIGN.
    { apply Bsign_Bconv_f. }
    destruct (Bconv map_nan1 mode_NE (B754_finite prec1 emax1 s m e e0)); try discriminate.
    simpl in SIGN. subst s0. simpl.
    pose proof (binary_normalize_correct prec2 emax2 prec2_gt_0_ Hmax2 mode_NE
                  (cond_Zopp (negb s) (Z.pos m)) e (negb s)) as CORRECT2.
    pose proof (Rlt_bool_spec
                (Rabs
                   (round radix2 (fexp prec2 emax2) 
                      (round_mode mode_NE)
                      (@F2R radix2
                         {| Fnum := cond_Zopp (negb s) (Z.pos m); Fexp := e |})))
                (bpow radix2 emax2)) as SPEC.
    destruct Rlt_bool; inversion SPEC; clear SPEC; cycle 1.
    { rewrite Rlt_bool_F2R_0 in CORRECT2.
      unfold binary_overflow,BinarySingleNaN.binary_overflow, overflow_to_inf in CORRECT2.
      destruct s;
        destruct binary_normalize; simpl in *; try discriminate;
      injection CORRECT2; intro; subst s; reflexivity.
    }
    destruct CORRECT2 as (VAL2 & FINITE2 & SIGN2).
    change (round_mode mode_NE) with ZnearestE in *.
    rewrite cond_Zopp_negb in H0.
    change {| Fnum := - cond_Zopp s (Z.pos m); Fexp := e |} with
      (@Fopp radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) in H0.
    rewrite F2R_opp in H0.
    rewrite round_NE_opp in H0.
    rewrite Rabs_Ropp in H0.
    change (round radix2 fexp2 ZnearestE
               (B2R prec1 emax1 (B754_finite prec1 emax1 s m e e0))) with
             (round radix2 (fexp prec2 emax2) ZnearestE
                (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |})) in H.
    lra.
  - pose proof (Bconv_correct map_nan2' mode_NE
                  (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0)) (eq_refl _)) as CORRECT2.
    pose proof (Rlt_bool_spec (Rabs
                   (round radix2 fexp2 (round_mode mode_NE)
                      (B2R prec1 emax1
                         (Bopp prec1 emax1 map_nan1'
                            (B754_finite prec1 emax1 s m e e0)))))
                (bpow radix2 emax2)) as RLT.
    destruct Rlt_bool; inversion RLT; clear RLT.
    { destruct CORRECT2 as (VAL & FINITE & SIGN).
      congruence. }
    assert (is_nan _ _ (Bconv map_nan2' mode_NE
                          (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))) = false) as NOT_NAN2.
    { apply is_nan_Bconv. }
    assert (Bsign _ _ (Bconv map_nan2' mode_NE
    (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))) = (negb s)) as SIGN.
    { apply Bsign_Bconv_f. }
    destruct (Bconv map_nan2' mode_NE
    (Bopp prec1 emax1 map_nan1' (B754_finite prec1 emax1 s m e e0))); try discriminate.
    simpl in SIGN. subst s0. simpl.
    pose proof
           (binary_normalize_correct prec2 emax2 prec2_gt_0_ Hmax2 mode_NE
       (cond_Zopp s (Z.pos m)) e s) as CORRECT1.
    pose proof (Rlt_bool_spec
                   (Rabs
                   (round radix2 (fexp prec2 emax2) 
                      (round_mode mode_NE)
                      (@F2R radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |})))
                (bpow radix2 emax2)) as SPEC.
    destruct Rlt_bool; inversion SPEC; clear SPEC; cycle 1.
    { rewrite Rlt_bool_F2R_0 in CORRECT1.
      unfold binary_overflow,BinarySingleNaN.binary_overflow, overflow_to_inf in CORRECT1.
      destruct s;
        destruct binary_normalize; simpl in *; try discriminate;
      injection CORRECT1; intro; subst s; reflexivity.
    }
    destruct CORRECT1 as (VAL1 & FINITE1 & SIGN1).
    change (round_mode mode_DN) with ZnearestE in *.
    rewrite <- Rabs_Ropp in H0.    
    rewrite <- round_NE_opp in H0.
    simpl in H.
    rewrite cond_Zopp_negb in H.
    change {| Fnum := - cond_Zopp s (Z.pos m); Fexp := e |}
      with (@Fopp radix2 {| Fnum := cond_Zopp s (Z.pos m); Fexp := e |}) in H.
    rewrite F2R_opp in H.
    change fexp2 with (fexp prec2 emax2) in H.
    lra.
Qed.
End Conversions.


Section Compose_Conversions.

Variable prec1 emax1 prec2 emax2 : Z.
Context (prec1_gt_0_ : Prec_gt_0 prec1) (prec2_gt_0_ : Prec_gt_0 prec2).
Let emin1 := (3 - emax1 - prec1)%Z.
Let fexp1 := FLT_exp emin1 prec1.
Let emin2 := (3 - emax2 - prec2)%Z.
Let fexp2 := FLT_exp emin2 prec2.
Hypothesis Hmax1 : (prec1 < emax1)%Z.
Hypothesis Hmax2 : (prec2 < emax2)%Z.
Let binary_float1 := binary_float prec1 emax1.
Let binary_float2 := binary_float prec2 emax2.

(** Converting to a higher precision then down to the original format
    is the identity. *)
Theorem Bconv_narrow_widen:
  prec2 >= prec1 -> emax2 >= emax1 ->
  forall narrow_nan widen_nan m f,
  is_nan _ _ f = false ->
  Bconv prec2 emax2 prec1 emax1 _ Hmax1 narrow_nan m (Bconv prec1 emax1 prec2 emax2 _ Hmax2 widen_nan m f) = f.
Proof.
  intros. destruct (is_finite _ _ f) eqn:FIN.
- assert (EQ: round radix2 fexp1 (round_mode m) (B2R prec1 emax1 f) = B2R prec1 emax1 f).
  { apply round_generic. apply valid_rnd_round_mode. apply generic_format_B2R. }
  generalize (Bconv_widen_exact _ _ _ _ _ _ Hmax2 H H0 widen_nan m f FIN).
  set (f' := Bconv prec1 emax1 prec2 emax2 _ Hmax2 widen_nan m f).
  intros (A & B & C).
  generalize (Bconv_correct _ _ _ _ _ Hmax1 narrow_nan m f' B).
  fold emin1. fold fexp1. rewrite A, C, EQ. rewrite Rlt_bool_true.
  intros (D & E & F).
  apply B2R_Bsign_inj; auto.
  destruct f; try discriminate; simpl.
  rewrite Rabs_R0. apply bpow_gt_0.
  rewrite F2R_cond_Zopp. rewrite abs_cond_Ropp. rewrite <- F2R_Zabs. simpl Z.abs.
  eapply bounded_lt_emax; eauto.
- destruct f; try discriminate. simpl. auto.
Qed.

End Compose_Conversions.

(* What happens when a lower precision value is cast to higher precision then compared to a higher precision value: possibility of using a lower precision comaprison. *)
Lemma Bcompare_refl:
  forall prec emax (x : binary_float prec emax)
         (not_NaN: is_nan _ _ x = false),
    Bcompare _ _ x x = Some Eq.
Proof.
  intros.
  destruct (is_finite  _ _ x) eqn:FINITE.
  { rewrite (Bcompare_correct _ _ _ _ FINITE FINITE).
    f_equal.
    pose proof (Rcompare_spec (B2R prec emax x) (B2R prec emax x)) as SPEC.
    destruct Rcompare; inversion SPEC; try lra. reflexivity.
  }
  destruct x; try discriminate.
  destruct s; reflexivity.
Qed.

Lemma Bcompare_eq_swap:
  forall prec emax (x y : binary_float prec emax),
    Bcompare _ _ x y = Some Eq -> Bcompare _ _ y x = Some Eq.
Proof.
  intros.
  rewrite Bcompare_swap. rewrite H. reflexivity.
Qed.

Definition option_comparison_eq_dec:
  forall (x y : option comparison), {x=y}+{x<>y}.
Proof.
  decide equality. decide equality.
Defined.

Lemma round_up_ge: forall r e (VALID: Valid_exp e) x,
    (round r e (round_mode mode_UP) x >= x)%R.
Proof.
  intros. simpl.
  destruct (@round_UP_pt r e VALID x) as (FORMAT & LE & H).
  apply Rle_ge. assumption.
Qed.

Lemma is_nan_binary_normalize:
  forall prec emax prec_gt_0_ Hmax mode m e s,
    is_nan _ _ (binary_normalize prec emax prec_gt_0_ Hmax mode m e s) = false.
Proof.
  unfold binary_normalize.
  intros.
  apply is_nan_BSN2B'.
Qed.

Definition cmp_ge_nan nan_answer cmp_opt :=
  match cmp_opt with
  | Some (Gt | Eq) => true
  | Some _ => false
  | None => nan_answer
  end.

Lemma Bcompare_plus_infinity:
  forall nan_ans prec emax x (x_NOT_NAN : is_nan _ _ x = false),
    cmp_ge_nan nan_ans (Bcompare prec emax (B754_infinity prec emax false) x) = true.
Proof.
  destruct x; intros; try discriminate; trivial.
  destruct s; reflexivity.
Qed.

Lemma sfcompare_infinity: forall x (FINITE : is_finite_SF x = true) s,
    (SFcompare x (S754_infinity s)) = Some (if s then Gt else Lt).
Proof.
  destruct x; try discriminate; reflexivity.
Qed.

Lemma is_finite_B2SF:
  forall prec emax x,
    (is_finite_SF (B2SF prec emax x)) = is_finite _ _ x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma Bsign_false_B2R: forall prec emax x,
    Bsign prec emax x = false -> (0 <= B2R prec emax x)%R.
Proof.
  destruct x; simpl; intro; try lra.
  subst. simpl. unfold F2R. simpl.
  assert (1 <= IZR (Z.pos m))%R.
  { change 1%R with (IZR 1).
    apply IZR_le. lia. }
  assert (0 < bpow radix2 e)%R.
  { apply bpow_gt_0. }
  nra.
Qed.
                  
Lemma Bsign_true_B2R:
  forall (prec emax : Z) (x : binary_float prec emax),
    Bsign prec emax x = true -> (B2R prec emax x <= 0)%R.
Proof.
  destruct x; simpl; intro; try lra.
  subst. simpl. unfold F2R. simpl.
  change (Z.neg m) with (- (Z.pos m)).
  rewrite Ropp_Ropp_IZR.
  assert (1 <= IZR (Z.pos m))%R.
  { change 1%R with (IZR 1).
    apply IZR_le. lia. }
  assert (0 < bpow radix2 e)%R.
  { apply bpow_gt_0. }
  nra.
Qed.

Lemma Rabs_neg_eq: forall x (NEG: (x <= 0)%R), Rabs x = (-x)%R.
Proof.
  unfold Rabs. intros.
  destruct Rcase_abs. reflexivity. lra.
Qed.

Lemma  beta_pnm1_pos: forall beta (BETA: 2 <= beta) n (POS: 1 <= n),
    0 < beta ^ n - 1.
Proof.
  intros.
  replace n with (1 + (n-1)) by ring.
  rewrite Z.pow_add_r by lia.
  assert (1 ^(n-1) <= beta^(n-1)) as YY.
  { apply Z.pow_le_mono_l. lia. }
  rewrite Z.pow_1_l in YY by lia.
  rewrite Z.pow_1_r.
  nia.
Qed.
  
Lemma Zdigits_beta_m1: forall beta n (POS: 1 <= n), (Zdigits beta (beta ^ n - 1)) = n.
Proof.
  intros.
  assert (beta ^ (n - 1) <= Z.abs (beta ^ n - 1) < beta ^ n) as ITV.
  { destruct beta as (beta & LO). simpl.
    rewrite Z.abs_eq; cycle 1.
    { assert (1 ^n <= beta^n).
      { apply Z.pow_le_mono_l. lia. }
      lia.
    }
    replace (beta ^n) with (beta * (beta ^ (n - 1))). nia.
    replace beta with (beta ^ 1) at 1.
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    apply Z.pow_1_r.
  }
  apply (Zdigits_unique beta (beta ^ n - 1) n ITV).
Qed.

Remark is_finite_pos0' : forall prec emax x,
    is_finite_pos0 prec emax x = true -> is_finite _ _ x = true.
Proof.
  intros. destruct x; try reflexivity; try discriminate.
Qed.

Lemma Bcompare_eq_maps:
  forall prec emax (x x' y : binary_float prec emax)
    (EQ : Bcompare _ _ x x' = Some Eq), Bcompare _ _ x y = Bcompare _ _ x' y.
Proof.
  intros.
  destruct (is_finite  _ _ x && is_finite _ _ x' && is_finite _ _ y) eqn:FINITE.
  { repeat rewrite andb_true_iff in FINITE.
    destruct FINITE as [[FINITE_x FINITE_x'] FINITE_y].
    rewrite (Bcompare_correct _ _ _ _ FINITE_x FINITE_x') in EQ.
    inversion EQ. clear EQ.
    pose proof (Rcompare_spec (B2R prec emax x) (B2R prec emax x')) as SPEC.
    rewrite H0 in SPEC. clear H0. inversion SPEC.
    rename H into x_eq_x'.
    rewrite (Bcompare_correct _ _ _ _ FINITE_x FINITE_y).
    rewrite (Bcompare_correct _ _ _ _ FINITE_x' FINITE_y).
    rewrite x_eq_x'. reflexivity.
  }

  repeat rewrite andb_false_iff in FINITE.
  destruct FINITE as [[INFINITE_x | INFINITE_x'] | INFINITE_y].
  { destruct x; try discriminate.
    destruct x'; try discriminate; destruct s, s0; try discriminate; reflexivity.
  }
  { destruct x'; try discriminate; try (rewrite Bcompare_swap in EQ; discriminate).
    destruct x; try discriminate; destruct s, s0; try discriminate; reflexivity.
  }
  rewrite (Bcompare_swap _ _ y x).
  rewrite (Bcompare_swap _ _ y x').
  destruct y; try discriminate; try reflexivity.
  destruct x; try discriminate; destruct s;
    destruct x'; try discriminate; destruct s0; simpl; try reflexivity.
  all: destruct s; try discriminate; reflexivity.
Qed.


Lemma Bconv_is_finite:
  forall {prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan mode x},
    is_finite _ _ (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan mode x) = true
    -> is_finite _ _ x = true.
Proof.
  intros. destruct x; try discriminate; reflexivity.
Qed.

Section Conversions2.
  
Variable prec1 emax1 prec2 emax2 : Z.
Context (prec1_gt_0_ : Prec_gt_0 prec1) (prec2_gt_0_ : Prec_gt_0 prec2).
Let emin1 := (3 - emax1 - prec1)%Z.
Let fexp1 := FLT_exp emin1 prec1.
Let emin2 := (3 - emax2 - prec2)%Z.
Let fexp2 := FLT_exp emin2 prec2.
Hypothesis Hmax1 : (prec1 < emax1)%Z.
Hypothesis Hmax2 : (prec2 < emax2)%Z.
Let binary_float1 := binary_float prec1 emax1.
Let binary_float2 := binary_float prec2 emax2.
Hypothesis Hprec: prec2 >= prec1.
Hypothesis Hemax: emax2 >= emax1.

Lemma Bcompare_min_float: forall nan_ans x (FINITE: is_finite _ _ x = true) bounded,
  cmp_ge_nan nan_ans (Bcompare prec1 emax1 x
       (B754_finite prec1 emax1 true (Z.to_pos (2 ^ prec1 - 1))
          (emax1 - prec1) bounded)) = true.
Proof.
  intros.
  rewrite Bcompare_correct. 2: assumption. 2: reflexivity.
  assert (NONNEG : 0 < 2 ^ prec1 - 1).
  { apply beta_pnm1_pos. lia. assert (0 < prec1) by assumption. lia. }
  simpl.
  replace (Z.neg (Z.to_pos (2 ^ prec1 - 1))) with (- (2 ^ prec1 - 1)); cycle 1.
  { change (Z.neg (Z.to_pos (2 ^ prec1 - 1))) with
      (- (Z.pos (Z.to_pos (2 ^ prec1 - 1)))).
    rewrite Z2Pos.id. reflexivity. assumption. }
  change  {| Fnum := - (2 ^ prec1 - 1); Fexp := emax1 - prec1 |} with
    (@Fopp radix2 {| Fnum := (2 ^ prec1 - 1); Fexp := emax1 - prec1 |}).
  rewrite F2R_opp.
  pose proof (BinarySingleNaN.bounded_lt_emax _ _ _ _ bounded) as BOUND.
  pose proof (abs_B2R_le_emax_minus_prec prec1 emax1 prec1_gt_0_ x) as BOUND2.
  pose proof (Rcompare_spec (B2R prec1 emax1 x)
                (- @F2R radix2 {| Fnum := 2 ^ prec1 - 1; Fexp := emax1 - prec1 |})) as SPEC.
  destruct Rcompare; try reflexivity.
  exfalso. inversion SPEC. clear SPEC.
  replace (Z.pos (Z.to_pos (2 ^ prec1 - 1))) with (2 ^ prec1 - 1) in BOUND; cycle 1.
  { rewrite Z2Pos.id. reflexivity. assumption. }
  set (x' := B2R prec1 emax1 x) in *.
  set (fltmax := F2R {| Fnum := 2 ^ prec1 - 1; Fexp := emax1 - prec1 |}) in *.
  assert (fltmax > 0)%R.
  { unfold fltmax. unfold F2R. simpl.
    assert (0 < IZR (2 ^ prec1 - 1))%R.
    { change 0%R with (IZR 0).
      apply IZR_lt. assumption.
    }
    pose proof (bpow_gt_0 radix2 (emax1 - prec1)).
    nra.
  }
  unfold Rabs in BOUND2. destruct Rcase_abs.
  2: lra.
  assert (fltmax = (bpow radix2 emax1 - bpow radix2 (emax1 - prec1))%R).
  { unfold fltmax, F2R. simpl.
    rewrite minus_IZR.
    rewrite Rmult_minus_distr_r.
    rewrite Rmult_1_l.
    change (2 ^ prec1) with (radix2 ^ prec1).
    rewrite IZR_Zpower by (assert (0 < prec1) by assumption; lia).
    rewrite <- bpow_plus.
    f_equal. f_equal. ring.
  }
  lra.
Qed.
 
Theorem Bcompare_Bconv_widen_ge:
  forall nan_ans conv_nan1 conv_nan2 m (x: binary_float1) (y: binary_float2),
    cmp_ge_nan nan_ans (Bcompare _ _ (Bconv _ _ _ _ _ Hmax2 conv_nan1 m x) y) =
      cmp_ge_nan nan_ans (Bcompare _ _ x (Bconv _ _ _ _ _ Hmax1 conv_nan2 mode_UP y)).
Proof.
  intros.
  destruct ((is_finite _ _ x) && (is_finite _ _ y)) eqn:FINITE; cycle 1.
  { destruct x, y; simpl in FINITE; try reflexivity; try discriminate; try (rewrite Bcompare_swap; reflexivity).
    - simpl.
      
      pose proof  (binary_normalize_correct prec1 emax1 prec1_gt_0_ Hmax1 mode_UP
                     (cond_Zopp s0 (Z.pos m0)) e s0) as CORRECT.
      destruct Rlt_bool.
      { destruct CORRECT as (VAL' & FINITE' & SIGN').
        destruct binary_normalize; simpl in FINITE; try discriminate; reflexivity.
      }
      destruct s; cycle 1.
      { rewrite Bcompare_plus_infinity. reflexivity.
        apply is_nan_binary_normalize.
      }
      unfold Bcompare, BinarySingleNaN.Bcompare.
      repeat rewrite B2SF_B2BSN.
      rewrite <- (FF2SF_B2FF _ _ (binary_normalize prec1 emax1 prec1_gt_0_ Hmax1 mode_UP
                                    (cond_Zopp s0 (Z.pos m0)) e s0)).
      rewrite CORRECT.
      unfold binary_overflow, BinarySingleNaN.binary_overflow.
      rewrite FF2SF_SF2FF.
      unfold overflow_to_inf.
      destruct Rlt_bool; reflexivity.
    - change (B754_infinity prec2 emax2 s0)
        with (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 m
                (B754_infinity prec1 emax1 s0)).
      rewrite Bcompare_Bconv_widen; trivial.
  }
  rewrite andb_true_iff in FINITE.
  destruct FINITE as (x_FINITE & y_FINITE).
  destruct (Bconv_widen_exact _ _ _ _ prec1_gt_0_ prec2_gt_0_ Hmax2 Hprec Hemax conv_nan1 m x x_FINITE) as (VAL & FINITE & SIGN).
  rewrite Bcompare_correct by assumption.
  rewrite VAL.
  pose proof (Bconv_correct _ _ _ _ prec1_gt_0_ Hmax1 conv_nan2 mode_UP y y_FINITE) as CONV.
  pose proof (Rlt_bool_spec (Rabs
               (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                  (round_mode mode_UP) (B2R prec2 emax2 y)))
            (bpow radix2 emax1)) as BOUND.
  assert (VALID_EXP: Valid_exp (FLT_exp (3 - emax1 - prec1) prec1)).
  { apply FLT_exp_valid; assumption. }
  pose proof (round_up_ge radix2 _ VALID_EXP (B2R prec2 emax2 y)) as ROUND_GE.
  destruct (@round_UP_pt radix2 (FLT_exp (3 - emax1 - prec1) prec1) VALID_EXP (B2R prec2 emax2 y)) as (FORMAT & UP & BOUNDS).
  assert (GENF: generic_format radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                  (B2R prec1 emax1 x)).
  { apply generic_format_B2R. }
  destruct Rlt_bool; inversion BOUND; clear BOUND; rename H into BOUND; cycle 1.
  {
    destruct (Bsign prec2 emax2 y) eqn:SIGN2; simpl; cycle 1.
    {
      unfold Bcompare, BinarySingleNaN.Bcompare.
      repeat rewrite B2SF_B2BSN.
      rewrite <- (FF2SF_B2FF prec1 emax1
                    (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_UP y)).
      rewrite CONV.
      unfold binary_overflow, BinarySingleNaN.binary_overflow.
      rewrite FF2SF_SF2FF.
      unfold overflow_to_inf. simpl.
      rewrite sfcompare_infinity by (rewrite is_finite_B2SF; assumption).
      assert (0 <= (B2R prec2 emax2 y))%R as NONNEG.
      { apply  Bsign_false_B2R. assumption. } 
      rewrite Rabs_pos_eq in BOUND by lra.
      simpl.
      (*pose proof (Rcompare_spec (B2R prec1 emax1 x) (B2R prec2 emax2 y)) as CMP. *)
      destruct (Rle_lt_dec  (B2R prec2 emax2 y) (B2R prec1 emax1 x)) as [GE|LT]; cycle 1.
      { rewrite Rcompare_Lt by assumption. reflexivity. }
      pose proof (BOUNDS _ GENF GE) as BOUNDS'.
      assert (ZZ: (bpow radix2 emax1 <= B2R prec1 emax1 x)%R).
      { eapply Rle_trans. eassumption. exact BOUNDS'. }
      pose proof (abs_B2R_lt_emax _ _ x) as YY.
      pose proof (Rle_abs (B2R prec1 emax1 x)).
      exfalso. lra.
    }
    assert ((B2R prec2 emax2 y) <= 0)%R as NEG.
    { apply  Bsign_true_B2R. assumption. }
    assert ((round radix2 (FLT_exp (3 - emax1 - prec1) prec1) 
               (round_mode mode_UP) (B2R prec2 emax2 y) <= 0)%R) as NEG'.
    {  erewrite <- round_0 by (apply valid_rnd_UP).
      apply round_le. 1,3: assumption.
      apply valid_rnd_UP. }
    rewrite Rabs_neg_eq in BOUND by assumption.
    unfold Bcompare, BinarySingleNaN.Bcompare.
    rewrite (B2SF_B2BSN prec1 emax1 (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2
                                       mode_UP y)).
    rewrite <- FF2SF_B2FF.
    rewrite CONV.
    unfold binary_overflow, BinarySingleNaN.binary_overflow, overflow_to_inf.
    simpl.
    assert (BOUNDED : bounded prec1 emax1 (Z.to_pos (2 ^ prec1 - 1)) (emax1 - prec1) = true).
    { assert (1 <= prec1) as PREC1.
      { assert (0 < prec1) by assumption. lia. }
      unfold bounded, canonical_mantissa.
      rewrite Zpos_digits2_pos.
      rewrite Z2Pos.id.
      2: { apply beta_pnm1_pos. lia. assumption. }
      rewrite Zdigits_beta_m1 by assumption.
      rewrite andb_true_iff. split.
      2: { apply Z.leb_refl. }
      replace (prec1 + (emax1 - prec1)) with emax1 by lia.
      rewrite fexp_emax by assumption.
      apply Zeq_bool_diag.
    }
    assert (RLT : Rlt_bool
                      (Rabs
                         (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                            (round_mode mode_UP) (B2R prec2 emax2 y))) 
                      (bpow radix2 emax1) = false).
    { apply Rlt_bool_false. rewrite Rabs_neg_eq by assumption. lra. }
    change (S754_finite true (Z.to_pos (2 ^ prec1 - 1)) (emax1 - prec1))
      with (B2SF _ _ (B754_finite _ _ true (Z.to_pos (2 ^ prec1 - 1)) (emax1 - prec1) BOUNDED)).
    change (SFcompare (BinarySingleNaN.B2SF (B2BSN prec1 emax1 x))
       (B2SF prec1 emax1
          (B754_finite prec1 emax1 true (Z.to_pos (2 ^ prec1 - 1))
             (emax1 - prec1) BOUNDED)))
       with (Bcompare _ _ x (B754_finite prec1 emax1 true (Z.to_pos (2 ^ prec1 - 1))
                               (emax1 - prec1) BOUNDED)).
    rewrite Bcompare_min_float by assumption.
    pose proof (Rcompare_spec (B2R prec1 emax1 x) (B2R prec2 emax2 y)) as SPEC.
    destruct Rcompare; inversion SPEC; try reflexivity.
    exfalso.
    rename H into LT. clear RLT. clear SPEC.
    pose proof (abs_B2R_lt_emax prec1 emax1 x) as BOUND2.
    rewrite Rabs_neg_eq in BOUND2 by lra.
    lra.
  }
  destruct CONV as (VAL' & FINITE' & SIGN').
  rewrite Bcompare_correct by assumption.
  rewrite VAL'.
  assert (Vep : Valid_exp (FLT_exp (3 - emax1 - prec1) prec1)).
  { apply FLT_exp_valid; assumption.
  }
  pose proof (round_up_ge radix2 (FLT_exp (3 - emax1 - prec1) prec1) Vep
                (B2R prec2 emax2 y)) as GE.
  simpl round_mode in *.
  pose proof (Rcompare_spec (B2R prec1 emax1 x) (B2R prec2 emax2 y)) as CMP.
  pose proof (Rcompare_spec (B2R prec1 emax1 x)
          (round radix2 (FLT_exp (3 - emax1 - prec1) prec1) Zceil
             (B2R prec2 emax2 y))) as CMP'.
  destruct (Rcompare  (B2R prec1 emax1 x)
          (round radix2 (FLT_exp (3 - emax1 - prec1) prec1) Zceil
             (B2R prec2 emax2 y))); inversion CMP'.
  { destruct Rcompare; try reflexivity. exfalso.
    inversion CMP. lra. }
  { destruct Rcompare; inversion CMP.
    { assert ((round radix2 (FLT_exp (3 - emax1 - prec1) prec1) Zceil
                 (B2R prec2 emax2 y)) <=  (B2R prec1 emax1 x))%R as ZZ.
      { apply BOUNDS; trivial. lra. }
      lra.
    }
    reflexivity.
    exfalso.
    assert ((round radix2 (FLT_exp (3 - emax1 - prec1) prec1) Zceil
               (B2R prec2 emax2 y)) <=  (B2R prec1 emax1 x))%R as ZZ.
    { apply BOUNDS; trivial. lra. }
    lra.
  }
  f_equal. f_equal. apply Rcompare_Gt. lra.
Qed.

Theorem Bcompare_Bconv_widen_eq1:
  forall conv_nan1 conv_nan2 m m' (x: binary_float1) (y: binary_float2)
     (CV: (Bconv _ _ _ _ _ Hmax2 conv_nan1 m (Bconv _ _ _ _ _ Hmax1 conv_nan2 m' y)) = y),
    Bcompare _ _ (Bconv _ _ _ _ _ Hmax2 conv_nan1 m x) y =
      Bcompare _ _ x (Bconv _ _ _ _ _ Hmax1 conv_nan2 m' y).
Proof.
  intros.
  erewrite <- (Bcompare_Bconv_widen prec1) with (Hmax2:=Hmax2) (conv_nan:=conv_nan1) (m:=m) by assumption.
  rewrite CV.
  reflexivity.
Qed.

Theorem Bconv_is_exact1:
  forall (x : binary_float1) (y : binary_float2)
         conv_nan1 conv_nan2
         (FINITE_x: is_finite _ _ x = true)
         (FINITE_y': is_finite _ _  (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y) = true)
         (EQ : (B2R _ _ x) = (B2R _ _ y)),
    Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
      (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y) = y.
Proof.
  intros.
  pose proof (Bconv_is_finite FINITE_y') as FINITE_y. 
  destruct (is_finite_pos0 _ _
              (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
                 (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y))
            && is_finite_pos0 _ _ y) eqn:FINITE_pos0.
  { rewrite andb_true_iff in FINITE_pos0.
    destruct FINITE_pos0 as (FINITE_pos1 & FINITE_pos2).
    apply B2R_inj_pos0; trivial.
    destruct (Bconv_widen_exact
                prec1 emax1 prec2 emax2 prec1_gt_0_ prec2_gt_0_ Hmax2 Hprec Hemax conv_nan1 mode_NE _ FINITE_y') as (VAL & FINITE & SIGN).
    rewrite VAL.
    pose proof (Bconv_correct  prec2 emax2  prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y FINITE_y) as CONV.
    pose proof (Rlt_bool_spec (Rabs
                                 (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                                    (round_mode mode_NE) (B2R prec2 emax2 y))) 
                  (bpow radix2 emax1)) as RANGE.
    destruct Rlt_bool; inversion RANGE; clear RANGE.
    { destruct CONV as (VAL' & FINITE' & SIGN').
      rewrite VAL'.
      rewrite <- EQ.
      apply round_generic.
      { apply valid_rnd_round_mode. }
      apply generic_format_B2R.
    }
    exfalso.
    unfold binary_overflow, BinarySingleNaN.binary_overflow, overflow_to_inf in CONV. simpl in CONV.
    rewrite <- is_finite_B2FF in FINITE_y'.
    rewrite CONV in FINITE_y'.
    discriminate.
  }
  destruct y; try discriminate.
  reflexivity.
  rewrite andb_true_r in FINITE_pos0.
  destruct (Bconv_widen_exact prec1 emax1 prec2 emax2 prec1_gt_0_ prec2_gt_0_ Hmax2 Hprec Hemax conv_nan1 mode_NE _ FINITE_y') as (VAL & FINITE & SIGN).
  destruct (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1
              mode_NE
              (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1
                 conv_nan2 mode_NE (B754_finite prec2 emax2 s m e e0))); try discriminate.
  exfalso.
  destruct s0; try discriminate. clear FINITE_pos0 FINITE.
  rewrite Bsign_Bconv_f in SIGN. simpl in SIGN. subst s.
  destruct x; try discriminate.
  { simpl in EQ.
    pose proof (F2R_neq_0 radix2 {| Fnum := Z.neg m; Fexp := e |}).
    apply H. discriminate. symmetry. assumption.
  }
  clear FINITE_x FINITE_y.
  change (B2R prec2 emax2 (B754_zero prec2 emax2 true)) with 0%R in VAL.
  pose proof (Bconv_correct prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2
                mode_NE (B754_finite prec2 emax2 true m e e0) (eq_refl _)) as CORRECT.
  pose proof (Rlt_bool_spec  (Rabs
         (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                     (round_mode mode_NE)
                     (B2R prec2 emax2 (B754_finite prec2 emax2 true m e e0))))
                   (bpow radix2 emax1)) as SPEC.
  destruct Rlt_bool; inversion SPEC; clear SPEC.
  2: { unfold binary_overflow, BinarySingleNaN.binary_overflow, overflow_to_inf in CORRECT.
       simpl in FINITE_y'. simpl in CORRECT.
       destruct binary_normalize; discriminate.
  }
  destruct CORRECT as (VAL1 & FINITE1 & SIGN1). clear FINITE1.
  rewrite VAL1 in VAL. clear VAL1.
  rewrite <- EQ in VAL.
  rewrite round_B2R in VAL.
  simpl in VAL.
  pose proof (F2R_neq_0 radix2 {| Fnum := cond_Zopp s (Z.pos m0); Fexp := e1 |}).
  apply H0. destruct s; discriminate.
  symmetry. assumption.
Qed.

Theorem Bconv_is_exact:
  forall x y conv_nan1 conv_nan2
  (CMP : Bcompare prec2 emax2
          (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE x) y =
        Some Eq),
  Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
    (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y) = y.
Proof.
  intros.
  destruct ((is_finite _ _ x) && (is_finite _ _ (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE y))) eqn:FINITE.
  { rewrite andb_true_iff in FINITE.
    destruct FINITE as (FINITE_x & FINITE_y').
    pose proof (Bconv_is_finite FINITE_y') as FINITE_y. 
    
    apply Bconv_is_exact1 with (x:=x); trivial.
    destruct (Bconv_widen_exact prec1 emax1 prec2 emax2
                prec1_gt_0_ prec2_gt_0_ Hmax2 Hprec Hemax conv_nan1 mode_NE x FINITE_x)
      as (VAL & FINITE & SIGN).
    rewrite (Bcompare_correct _ _ _ _ FINITE FINITE_y) in CMP.
    inversion CMP. clear CMP.
    rewrite <- (Rcompare_Eq_inv _ _ H0).
    symmetry. assumption.
  }
  destruct y; try reflexivity.
  { rewrite Bcompare_swap in CMP. discriminate. }
  destruct x; try discriminate.
  1,2: destruct s, s0; discriminate.
  pose proof (Bconv_correct prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2
                mode_NE (B754_finite prec2 emax2 s m e e0) (eq_refl _)) as CORRECT.
  pose proof (Rlt_bool_spec (Rabs
                  (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
                     (round_mode mode_NE)
                     (B2R prec2 emax2 (B754_finite prec2 emax2 s m e e0))))
                (bpow radix2 emax1)) as SPEC.
  destruct Rlt_bool; inversion SPEC; clear SPEC.
  { destruct CORRECT as (VAL' & FINITE' & SIGN').
    rewrite FINITE' in FINITE. discriminate. }
  clear FINITE.
  destruct (is_finite _ _  (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
                              (B754_finite prec1 emax1 s0 m0 e1 e2))) eqn:FINITE2.
  2: { destruct (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
                   (B754_finite prec1 emax1 s0 m0 e1 e2)); try discriminate.
       destruct s1; discriminate. }
  rewrite (Bcompare_correct _ _ _ (B754_finite prec2 emax2 s m e e0) FINITE2 (eq_refl _)) in CMP.
  Local Opaque Bconv B2R.
  injection CMP. clear CMP. intro EQ.
  apply Rcompare_Eq_inv in EQ.
  destruct (Bconv_widen_exact prec1 emax1 prec2 emax2 prec1_gt_0_ prec2_gt_0_ Hmax2 Hprec Hemax conv_nan1 mode_NE (B754_finite prec1 emax1 s0 m0 e1 e2) (eq_refl _)) as (VAL & FINITE & SIGN).
  rewrite VAL in EQ.
  rewrite <- EQ in H.
  pose proof (abs_B2R_le_emax_minus_prec prec1 emax1 prec1_gt_0_ (B754_finite prec1 emax1 s0 m0 e1 e2)) as BOUND.
  assert (Rabs (round radix2 (FLT_exp (3 - emax1 - prec1) prec1)
            (round_mode mode_NE)
            (B2R prec1 emax1 (B754_finite prec1 emax1 s0 m0 e1 e2)))
          <= bpow radix2 emax1 - bpow radix2 (emax1 - prec1))%R.
  { 
    apply abs_round_le_generic.
    { apply FLT_exp_valid; assumption. }
    { apply valid_rnd_round_mode. }
    { apply generic_format_FLT.
      eapply FLT_spec with (f := {| Fnum := (2^prec1) - 1; Fexp := emax1-prec1 |}).
      3: { unfold Prec_gt_0 in *. simpl Fexp. lia. }
      { unfold F2R. simpl.
        rewrite minus_IZR.
        change 2 with (radix_val radix2).
        rewrite IZR_Zpower. 2: { unfold Prec_gt_0 in *. lia. }
        rewrite Rmult_minus_distr_r.
        rewrite <- bpow_plus.
        rewrite Rmult_1_l. f_equal. f_equal. ring.
      }
      simpl.
      rewrite Z.abs_eq. lia.
      assert (radix2 ^ 0 <= radix2 ^ prec1) as LE.
      { apply Zpower_le. unfold Prec_gt_0 in *. lia. }
      simpl in LE. lia.
    }
    assumption.
  }
  assert (bpow radix2 (emax1 - prec1) > 0)%R.
  { apply bpow_gt_0. }
  lra.
Qed.
                                                                      
Theorem Bcompare_Bconv_widen_eq2:
  forall conv_nan1 conv_nan2 (x: binary_float1) (y: binary_float2)
    (COMPARE: (Bcompare _ _ (Bconv _ _ _ _ _ Hmax2 conv_nan1 mode_NE (Bconv _ _ _ _ _ Hmax1 conv_nan2 mode_NE y)) y) <> Some Eq),
    (Bcompare _ _ (Bconv _ _ _ _ _ Hmax2 conv_nan1 mode_NE x) y <> Some Eq).
Proof.
  intros.
  destruct (is_nan _ _ y) eqn:NAN_Y.
  { rewrite Bcompare_swap in COMPARE.
    destruct y; try discriminate.
    rewrite Bcompare_swap. discriminate.
  }
  intro CMP. apply COMPARE. clear COMPARE.
  destruct (Beq_dec _ _ (Bconv prec1 emax1 prec2 emax2 prec2_gt_0_ Hmax2 conv_nan1 mode_NE
                 (Bconv prec2 emax2 prec1 emax1 prec1_gt_0_ Hmax1 conv_nan2 mode_NE
                    y)) y).
  { rewrite <- e at 2.
    rewrite Bcompare_Bconv_widen by assumption.
    apply Bcompare_refl.
    rewrite is_nan_Bconv. assumption.
  }
  exfalso. apply n. clear n.
  eapply Bconv_is_exact. eassumption.
Qed.

Theorem Bcompare_eqv_eq: forall prec emax (x y : binary_float prec emax),
    Bcompare _ _ x y = Some Eq <->
      (x=y /\ is_nan _ _ x = false)
            \/ ((x = B754_zero _ _ true  /\ y = B754_zero _ _ false) \/
                (x = B754_zero _ _ false /\ y = B754_zero _ _ true )).
Proof.
  split; cycle 1.
  - intro CASES.
    destruct CASES as [[EQ NOT_NAN] | [[ZEROx ZEROy] | [ZEROx ZEROy]]]; subst; try reflexivity.
    apply Bcompare_refl. assumption.
  - intro COMPARE.
    destruct x, y; try discriminate.
    all: try (destruct s, s0; try discriminate; tauto).
    left. split. 2: reflexivity.
    rewrite Bcompare_correct in COMPARE by reflexivity.
    Local Opaque B2R.
    injection COMPARE. clear COMPARE. intro EQ.
    apply B2R_inj. 1, 2: reflexivity.
    apply Rcompare_Eq_inv. assumption.
Qed.
                                                                      
Theorem Bcompare_Bconv_widen_eq3:
  forall conv_nan1 conv_nan2 (x: binary_float1) (y: binary_float2)
    (CV: (Bconv _ _ _ _ _ Hmax2 conv_nan1 mode_NE (Bconv _ _ _ _ _ Hmax1 conv_nan2 mode_NE y)) <> y),
    (Bcompare _ _ (Bconv _ _ _ _ _ Hmax2 conv_nan1 mode_NE x) y <> Some Eq).
Proof.
  intros.
  Local Transparent Bconv.
  destruct y; try (simpl in CV; contradiction).
  { rewrite Bcompare_swap. discriminate. }
  eapply Bcompare_Bconv_widen_eq2.
  intro EQ.
  apply Bcompare_eqv_eq in EQ.
  destruct EQ as [[EQ NOT_NAN] | [[ZERO1 ZERO2] | [ZERO1 ZERO2] ]].
  contradiction.
  congruence.
  congruence.
Qed.

End Conversions2.

Lemma F2R_opp_sign: forall radix x e,
         @F2R radix {| Fnum := -x ; Fexp := e |}
         = (-@F2R radix {| Fnum := x; Fexp := e |})%R.
Proof.
  intros.
  change   {| Fnum := -x; Fexp := e |}
    with (@Fopp radix {| Fnum := x; Fexp := e |}).
  apply F2R_opp.
Qed.

Theorem Bcompare_opp: forall prec emax (x y : binary_float prec emax) nanx nany,
    Bcompare _ _ x y = option_map CompOpp (Bcompare _ _ (Bopp _ _ nanx x) (Bopp _ _ nany y)).
Proof.
  intros.
  destruct x, y.
  reflexivity.
  all: try (destruct s; reflexivity).
  all: try (destruct s, s0; reflexivity).
  repeat rewrite Bcompare_correct by reflexivity.
  simpl. f_equal.
  
  repeat rewrite cond_Zopp_negb.  
  repeat rewrite F2R_opp_sign.
  rewrite Rcompare_opp.
  apply Rcompare_sym.
Qed.
