(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  with a few contributions from Boulmé, Monniaux, Verimag            *)
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

(** Formalizations of machine integers modulo $2^N$ #2<sup>N</sup>#. *)

From Stdlib Require Import Eqdep_dec Zquot Zwf.
Require Import Coqlib Zbits Axioms.
Require Archi.
Require Import Lia.

(* Some general arithmetic lemmas *)

Lemma two_power_nat_less_div: forall m n (LESS : (m <= n)%nat),
    (two_power_nat m | two_power_nat n).
Proof.
  intros.
  exists (two_power_nat (n - m)%nat).
  repeat rewrite two_power_nat_equiv.
  rewrite <- Z.pow_add_r. 2,3: lia.
  f_equal. lia.
Qed.

Lemma two_power_nat_div_iff: forall m n, (two_power_nat m | two_power_nat n) <-> (m <= n)%nat.
Proof.
  split. 2: intros; apply two_power_nat_less_div; auto.
  revert m; induction n; cbn.
  - unfold two_power_nat; cbn. intros m H; apply Z.divide_1_r_nonneg in H; auto with zarith.
    inv H. destruct m; cbn in *; auto. inv H1.
  - destruct m; cbn; auto with arith.
    rewrite !two_power_nat_S, Z.mul_divide_cancel_l; auto with arith. lia.
Qed.

Lemma two_power_nat_monotonic: forall m n (LESS : (m <= n)%nat),
  (two_power_nat m <= two_power_nat n).
Proof.
  intros. eapply Z.divide_pos_le.
  specialize (two_power_nat_pos n). auto with zarith.
  apply two_power_nat_less_div; auto.
Qed.

Lemma two_power_nat_order: forall n m, two_power_nat m <= two_power_nat n -> (m <= n)%nat.
Proof.
  induction n; cbn.
  - intros m; rewrite two_power_nat_O. destruct m; auto with arith. rewrite two_power_nat_S. 
    specialize (two_power_nat_pos m). lia.
  - intros m. destruct m; auto with arith.
Qed.

Lemma two_power_nat_div_le: forall n m, (two_power_nat m | two_power_nat n) <-> two_power_nat m <= two_power_nat n.
Proof.
  intros; rewrite two_power_nat_div_iff. split. 
  - apply two_power_nat_monotonic.
  - apply two_power_nat_order.
Qed.

Lemma two_power_nat_div: forall m n, (n | two_power_nat m) -> 0 <= n -> exists k, n = two_power_nat k.
Proof.
  induction m.
  - intros n; rewrite two_power_nat_O. intros ? ?. rewrite (Z.divide_1_r_nonneg n); auto.
    exists O. auto.
  - intros n. rewrite two_power_nat_S. intros DIV H.
    destruct n as [ | [ p | p | ] | ]; try lia. 
    + (* absurd: 0 *) apply Z.divide_0_l in DIV. specialize (two_power_nat_pos m). lia.
    + (* absurd: odd > 1 *)
      apply Z.gauss in DIV; eauto.
      rewrite Z.gcd_comm, <- Z.gcd_mod; auto with zarith.
      replace (Zpos p~1) with ((1+(Zpos p)*2)) by auto with zarith.
      rewrite Z.mod_add; auto with zarith.
    + (* recursive case *)
      replace (Zpos p~0) with (2*(Zpos p)) in DIV by auto with zarith.
      rewrite Z.mul_divide_cancel_l in DIV; auto with zarith.
      exploit IHm; eauto. intros (k & EQ).
      exists (S k). rewrite two_power_nat_S. rewrite <- EQ. auto.
    + exists O. auto.
Qed.

(** computes [Nat.min n (log2 x)] *)
Fixpoint bpos_log2 (n: nat) (x : positive) { struct n } : nat :=
  match n with
  | O => O
  | S n =>
     match x with
     | xH => O
     | xI z | xO z => S (bpos_log2 n z)
     end
  end.

Lemma bpos_log2_le: forall n x, two_power_nat (bpos_log2 n x) <= Zpos x.
Proof.
  induction n; cbn.
  + unfold two_power_nat. cbn. intros; auto with zarith.
  + intros x; destruct x; auto with zarith;
    rewrite two_power_nat_S; specialize (IHn x); lia.
Qed.

Lemma bpos_log2_bnd: forall n x, (bpos_log2 n x <= n)%nat.
Proof.
  induction n; cbn; auto with arith.
  intros x; destruct x; auto with arith.
Qed.

(** computes the greatest power of 2 bounded by [n] that divides [x]
    (aka the best alignment of [x] on [n] bits).
 *)
Fixpoint al_pos (n: nat) (x : positive) { struct n } : nat :=
  match n with
  | O => O
  | S n => match x with
          | xH | xI _ => O
          | xO z => S (al_pos n z)
          end
  end.

Lemma al_pos_div: forall n x, (two_power_nat (al_pos n x) | Zpos x).
Proof.
  induction n; cbn.
  + unfold two_power_nat. cbn. intros. apply Z.divide_1_l.
  + destruct x as [|x|]; auto with zarith.
    replace (Zpos x~0) with (2 * Zpos x) by reflexivity.
    rewrite two_power_nat_S, Z.mul_divide_cancel_l; auto with zarith.
Qed.

Lemma al_pos_bpos_log2: forall n x, (al_pos n x <= bpos_log2 n x)%nat.
Proof.
  induction n; cbn; auto with zarith.
  destruct x as [|x|]; auto with zarith.
  specialize (IHn x); auto with zarith.
Qed.

Lemma al_pos_bnd: forall n z, (al_pos n z <= n)%nat.
Proof.
  intros; etransitivity.
  + apply al_pos_bpos_log2.
  + apply bpos_log2_bnd.
Qed.

Lemma al_pos_min n: forall m, (n <= m)%nat -> forall x, al_pos n x = Nat.min n (al_pos m x).
Proof.
  induction n; cbn; auto.
  intros m H; inv H.
  + destruct x; cbn; auto with arith.
  + destruct x; cbn; auto with arith.
Qed.

Lemma al_pos_shift_nat m: forall n, al_pos m (shift_nat n 1) = Nat.min m n.
Proof.
  induction m; cbn; auto.
  destruct n; cbn; auto.
  rewrite <- IHm; auto.
Qed.

Lemma al_pos_mul n: forall x p, (al_pos n x <= al_pos n (x*p))%nat.
Proof.
  induction n; cbn; auto with zarith.
  destruct x as [|x|]; auto with zarith.
  intros p; replace (x~0*p)%positive with ((x*p)~0)%positive by lia.
  specialize (IHn x p); auto with zarith.
Qed.

Definition al_Z (n: nat) (x : Z) : nat :=
 match x with
 | Z0 => n
 | Zneg p | Zpos p => al_pos n p
 end.

Lemma al_Z_destruct (n: nat) (x: Z):
  (x = 0 \/ exists p, Z.abs x = Zpos p /\ al_Z n x = al_pos n p).
Proof.
  destruct x as [|p|p]; cbn; eauto.
Qed.

Lemma al_Z_div n z: (two_power_nat (al_Z n z) | z).
Proof.
  destruct (al_Z_destruct n z) as [->|(p & H1 & ->)].
  - apply Z.divide_0_r.
  - rewrite <- Z.divide_abs_r, H1. apply al_pos_div.
Qed.

Lemma al_Z_bnd: forall n z, (al_Z n z <= n)%nat.
Proof.
  destruct z as [|p|p]; auto with arith; apply al_pos_bnd.
Qed.

Lemma al_Z_min n m: (n <= m)%nat -> forall x, al_Z n x = Nat.min n (al_Z m x).
Proof.
  intros H.
  destruct x as [|p|p]; cbn; try apply al_pos_min; auto.
  apply Nat.min_l in H. auto.
Qed.

Lemma al_Z_al_Z n x y: al_Z (al_Z n x) y = Nat.min (al_Z n x) (al_Z n y).
Proof.
  intros; apply al_Z_min, al_Z_bnd.
Qed.

Lemma al_Z_two_power_nat m: forall n, al_Z m (two_power_nat n) = Nat.min m n.
Proof.
  intros; cbn; apply al_pos_shift_nat.
Qed.

Local Opaque Z.mul.

Lemma al_Z_div_mono n x y: (x | y) -> (al_Z n x <= al_Z n y)%nat.
Proof.
  intros H; destruct (al_Z_destruct n x) as [->|(p & H1 & ->)].
  + inv H. replace (x * 0) with 0; cbn; auto with zarith.
  + rewrite <- Z.divide_abs_l in H. rewrite H1 in H. erewrite Zdivide_Zdiv_eq with (b:=y). 3: eapply H. 2: eauto with zarith.
    clear H1. destruct (al_Z_destruct n (Z.pos p * (y / Z.pos p))) as [H0|(q & H1 & ->)].
    - assert (X: y = 0). {
        eapply Z.mul_eq_0_r in H0; auto with zarith.
        rewrite Z.div_small_iff in H0; auto with zarith.
        case (zeq 0 y); auto.
        intros; case H0.
        + intros. apply Z.divide_pos_le in H; lia.
        + intros. rewrite <- Z.divide_abs_r in H. apply Z.divide_pos_le in H; lia.
      }
      subst. cbn. apply al_pos_bnd.
    - rewrite Z.abs_mul in H1. Local Opaque Z.mul. cbn in H1. Transparent Z.mul.
      destruct (y / Z.pos p) eqn: X.
      * cbn in H1. lia.
      * cbn in H1. injection H1. intros <-. apply al_pos_mul.
      * cbn in H1. injection H1. intros <-. apply al_pos_mul.
Qed.

Lemma al_Z_full_mono n m x y:
  (n <= m)%nat -> (x | y) -> (al_Z n x <= al_Z m y)%nat.
Proof.
  intros; etransitivity. eapply al_Z_div_mono. eauto.
  erewrite al_Z_min; eauto.
  lia.
Qed.

Lemma al_Z_gcd n x y: al_Z (al_Z n x) y = al_Z n (Z.gcd x y).
Proof.
  apply Nat.le_antisymm.
  - (* <= *)
    set (k:=(al_Z (al_Z n x) y)%nat).
    assert (X: (two_power_nat k | x)). {
      eapply Z.divide_trans. 2: eapply al_Z_div.
      apply two_power_nat_less_div, al_Z_bnd.
    }
    assert (Y: (two_power_nat k | y)). {
      eapply al_Z_div.
    }
    exploit Z.gcd_greatest. apply X. apply Y.
    intros G. eapply al_Z_div_mono in G.
    etransitivity. 2: eauto.
    rewrite al_Z_two_power_nat, Nat.min_r; auto.
    unfold k. etransitivity; apply al_Z_bnd.
 - (* >= *)
   rewrite al_Z_al_Z. apply Nat.min_case.
   + apply al_Z_div_mono, Z.gcd_divide_l.
   + apply al_Z_div_mono, Z.gcd_divide_r.
Qed.

(** division *)
Lemma Z_sub_mod_eq_zero a b p: p <> 0 -> (a - b) mod p = 0 <-> (a mod p) = (b mod p).
Proof.
  intros POS; split.
  - intros; replace (b mod p) with ((b mod p) mod p). 2: apply Zmod_mod.
    replace (b mod p) with ((a - b) mod p + b mod p) by lia.
    rewrite <- Z.add_mod; auto.
    replace (a - b + b) with a; lia.
  - rewrite Zminus_mod; intros. replace (a mod p - b mod p) with 0; auto. lia.
Qed.

Definition multiplicative_inverse (n x : Z) :=
  match euclid n x with
  | Euclid_intro _ _ u v d EQ GCD =>
      if zlt d 0
      then -v
      else v
  end.

Lemma multiplicative_inverse_correct :
  forall n x (INVERTIBLE : rel_prime n x),
    (eqmod n (x * (multiplicative_inverse n x)) 1).
Proof.
  unfold multiplicative_inverse.
  intros.
  rewrite <- Zgcd_1_rel_prime in INVERTIBLE.
  destruct euclid. destruct zlt.
  - apply Zis_gcd_opp in z.
    apply Zis_gcd_gcd in z. 2: lia.
    rewrite Z.gcd_comm in z.
    exists u. lia.
  - apply Zis_gcd_gcd in z. 2: lia.
    exists (-u). lia.
Qed.

Fixpoint Pmax_two_power_rec (x : positive) (p0 : nat) :=
  match x with
  | xH | xI _ => (p0, x)
  | xO x' => Pmax_two_power_rec x' (S p0)
  end.

Lemma Pmax_two_power_rec_less:
  forall x n p0 (LESS : (x < shift_nat n 1)%positive),
    (fst (Pmax_two_power_rec x p0) < p0 + n)%nat.
Proof.
  induction x; cbn; intros.
  all: destruct n; try (cbn in LESS; lia).
  replace (p0 + S n)%nat with ((S p0) + n)%nat by lia.
  apply IHx.
  change (S n) with (1 + n)%nat in LESS.
  rewrite shift_nat_plus in LESS.
  change (shift_nat 1 (shift_nat n 1)) with ((shift_nat n 1)~0)%positive in LESS.
  lia.
Qed.

Definition pos_odd x :=
  match x with
  | xH | xI _ => true
  | xO _ => false
  end.

Lemma Pmax_two_power_rec_spec: forall x p0,
    let (p1, x1) := Pmax_two_power_rec x p0 in
    exists p2,
      pos_odd x1 = true /\
      x = shift_nat p2 x1 /\ (p1 = p0 + p2)%nat.
Proof.
  induction x; intros; cbn.
  1,3: exists 0%nat; cbn; auto; fail.
  pose proof (IHx (S p0)) as ZZ.
  destruct Pmax_two_power_rec.
  destruct ZZ as (p2 & COND1 & COND2 & COND3).
  exists (S p2). simpl.
  split. assumption. split.
  congruence. lia.
Qed.

Definition Pmax_two_power x := Pmax_two_power_rec x 0.

Lemma Pmax_two_power_less:
  forall x n (LESS : (x < shift_nat n 1)%positive),
    (fst (Pmax_two_power x) < n)%nat.
Proof.
  intros. unfold Pmax_two_power.
  change n with (0 + n)%nat.
  apply Pmax_two_power_rec_less. assumption.
Qed.

Lemma Pmax_two_power_spec: forall x,
    let (p1, x1) := Pmax_two_power x in
    pos_odd x1 = true /\ x = shift_nat p1 x1.
Proof.
  unfold Pmax_two_power. intros.
  pose proof (Pmax_two_power_rec_spec x 0).
  destruct Pmax_two_power_rec.
  cbn in H.
  destruct H as (n' & COND1 & COND2 & COND3). subst n'.
  auto.
Qed.

Definition Zmax_two_power x :=
  match x with
  | Z0 => (1, 0)
  | Zpos x => let (p, x') := Pmax_two_power x in (Z.of_nat p, Zpos x')
  | Zneg x => let (p, x') := Pmax_two_power x in (Z.of_nat p, Zneg x')
  end.

Definition z_odd x :=
  match x with
  | Z0 => false
  | Zpos x' | Zneg x' => pos_odd x'
  end.

Lemma Zmax_two_power_range:
  forall x n
    (NONZERO : x <> 0)
    (LESS : -two_power_nat n < x < two_power_nat n),
    0 <= fst (Zmax_two_power x) < (Z.of_nat n).
Proof.
  unfold Zmax_two_power. destruct x; cbn; intros.
  - contradiction.
  - pose proof (Pmax_two_power_less p n) as MAX.
    destruct Pmax_two_power. cbn in *.
    unfold two_power_nat in LESS. lia.
  - pose proof (Pmax_two_power_less p n) as MAX.
    destruct Pmax_two_power. cbn in *.
    unfold two_power_nat in LESS. lia.
Qed.
  
Lemma Zmax_two_power_spec: forall x (NONZERO: x <> 0),
    let (p1, x1) := Zmax_two_power x in
    z_odd x1 = true /\ x = Z.shiftl x1 p1 /\ p1 >= 0.
Proof.
  unfold Zmax_two_power. destruct x; intro xNZ.
  - contradiction.
  - clear xNZ.
    pose proof (Pmax_two_power_spec p) as ZZ.
    destruct Pmax_two_power.
    destruct ZZ as (ZZ1 & ZZ2). split. exact ZZ1. split. 2: lia.
    subst p.
    rewrite Zshiftl_mul_two_p by lia.
    rewrite shift_nat_correct. rewrite Z.mul_comm. f_equal.
    rewrite <- two_power_nat_correct.
    apply two_power_nat_two_p.
  - clear xNZ.
    pose proof (Pmax_two_power_spec p) as ZZ.
    destruct Pmax_two_power.
    destruct ZZ as (ZZ1 & ZZ2). split. exact ZZ1. split. 2: lia.
    subst p.
    rewrite <- Pos2Z.opp_pos. rewrite <- Pos2Z.opp_pos.
    rewrite Zshiftl_mul_two_p by lia.
    rewrite shift_nat_correct.
    rewrite <- two_power_nat_correct.
    rewrite two_power_nat_two_p. lia.
Qed.

Lemma div2_not_odd: forall x, (2 | x) -> z_odd x = false.
Proof.
  intros. destruct H. rewrite H. clear H.
  unfold z_odd, pos_odd. rewrite Z.mul_comm.
  destruct x0; reflexivity.
Qed.

Lemma odd_is_rel_prime_2: forall x,
    z_odd x = true -> rel_prime x 2.
Proof.
  intros. unfold rel_prime. constructor.
  1,2: apply Z.divide_1_l; fail.
  intros.
  destruct x0.
  - destruct H1. lia.
  - assert (Z.pos p <= 2) as LE.
    { apply Z.divide_pos_le. lia. assumption. }
    assert (Z.pos p = 1 \/ Z.pos p = 2) as Z by lia.
    destruct Z as [Z | Z].
    + rewrite Z. apply Z.divide_1_l.
    + exfalso. rewrite Z in H0.
      pose proof (div2_not_odd _ H0).
      congruence.
  - assert (Z.pos p <= 2) as LE.
    { apply Z.divide_pos_le. lia.
      apply Z.divide_Zpos_Zneg_l. assumption. }
    assert (Z.pos p = 1 \/ Z.pos p = 2) as Z by lia.
    apply Z.divide_Zpos_Zneg_l.
    destruct Z as [Z | Z].
    + rewrite Z. apply Z.divide_1_l.
    + exfalso. rewrite <- Z.divide_Zpos_Zneg_l in H0.
      rewrite Z in H0.
      pose proof (div2_not_odd _ H0).
      congruence.
Qed.

Lemma odd_is_rel_prime_2pow: forall x n,
    z_odd x = true -> rel_prime x (two_power_nat n).
Proof.
  induction n; intros; cbn.
  - apply rel_prime_sym. apply rel_prime_1.
  - rewrite two_power_nat_S.
    apply rel_prime_mult.
    + apply odd_is_rel_prime_2. assumption.
    + apply IHn. assumption.
Qed.

Lemma eqmod_inverse_mul :
  forall m a b c, b <> 0 -> (b | c) ->
    eqmod m (a * b) 1 -> eqmod m (c / b) (c * a).
Proof.
  intros until c. intros NONZERO DIV EQMOD;
  destruct DIV as (q & DIVq). subst c.
  rewrite Z.div_mul by assumption.
  replace q with (q * 1) at 1 by ring.
  replace (q * b * a) with (q * (a * b)) by ring.
  apply eqmod_mult.
  { apply eqmod_refl. }
  apply eqmod_sym. assumption.
Qed.

Theorem divexact_to_mul_inverse: forall n x y
     (NONZERO: y <> 0) (EXACT: (y | x)%Z),
    let (py, oy) := Zmax_two_power y in
    eqmod (two_power_nat n) (x/y)
          ((Z.shiftr x py) * (multiplicative_inverse (two_power_nat n) oy)).
Proof.
  intros.
  pose proof (Zmax_two_power_spec y NONZERO) as TWO_POWER.
  destruct Zmax_two_power as (exponent & y1).
  destruct TWO_POWER as (ODD & SHIFT & NONNEG).
  subst y.
  pose proof (odd_is_rel_prime_2pow y1 n ODD) as REL_PRIME.
  apply rel_prime_sym in REL_PRIME.
  pose proof (multiplicative_inverse_correct _ _ REL_PRIME) as INVERSE.
  set (z0_inv := multiplicative_inverse (two_power_nat n) y1) in *.
  rewrite Zshiftl_mul_two_p by lia.
  assert (two_p exponent > 0) as POW_POS.
  { apply two_p_gt_ZERO. lia. }
  replace  (x / (y1 * two_p exponent)) with ((x / two_p exponent) / y1); cycle 1.
  { destruct (zlt y1 0).
    - replace y1 with (- (- y1)) at 1 by lia.
      rewrite Z_div_zero_opp_r; cycle 1.
      { apply Z.mod_opp_r_z. lia.
        destruct EXACT as (q & EQq). subst x.
        rewrite Zshiftl_mul_two_p by lia.
        replace  (q * (y1 * two_p exponent)) with
          ((q * y1) * two_p exponent) by ring.
        rewrite Z.div_mul by lia.
        apply Z_mod_mult.
      }
      rewrite Zdiv_Zdiv by lia.
      replace (y1 * two_p exponent) with (- (- (y1 * two_p exponent))) by ring.
      rewrite Z_div_zero_opp_r; cycle 1.
      { rewrite Z.mod_opp_r_z. lia. nia.
        rewrite Zshiftl_mul_two_p in EXACT.
        apply Zdivide_mod. assumption. lia. }
      f_equal. f_equal. ring.
    - destruct (zeq y1 0). subst y1. cbn in ODD. discriminate.
      rewrite Zdiv_Zdiv; cycle 1. assumption. lia.
      rewrite Z.mul_comm. reflexivity.
  }
  rewrite <- Zshiftr_div_two_p by lia.
  apply eqmod_inverse_mul.
  { intro ZERO. subst y1. cbn in ODD. discriminate. }
  { destruct EXACT as (q & EQ). subst x.
    rewrite Zshiftl_mul_two_p by lia.
    rewrite Zshiftr_div_two_p by lia.
    replace (q * (y1 * two_p exponent)) with ((q * y1) *  two_p exponent) by ring.
    rewrite Z.div_mul by lia.
    exists q. reflexivity.
  }
  rewrite Z.mul_comm. assumption.
Qed.
    
(** Backwards compatibility for Hint Rewrite locality attributes. *)
Set Warnings "-unsupported-attributes".

(** * Comparisons *)

Inductive comparison : Type :=
  | Ceq : comparison               (**r same *)
  | Cne : comparison               (**r different *)
  | Clt : comparison               (**r less than *)
  | Cle : comparison               (**r less than or equal *)
  | Cgt : comparison               (**r greater than *)
  | Cge : comparison.              (**r greater than or equal *)

Definition comparison_eq: forall (x y: comparison), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

(** * Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Parameter wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition zwordsize: Z := Z.of_nat wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos: zwordsize > 0.
Proof.
  unfold zwordsize, wordsize. generalize WS.wordsize_not_zero. lia.
Qed.

Remark modulus_power: modulus = two_p zwordsize.
Proof.
  unfold modulus. apply two_power_nat_two_p.
Qed.

Remark modulus_gt_one: modulus > 1.
Proof.
  rewrite modulus_power. apply Z.lt_gt. apply (two_p_monotone_strict 0).
  generalize wordsize_pos; lia.
Qed.

Remark modulus_pos: modulus > 0.
Proof.
  generalize modulus_gt_one; lia.
Qed.

Global Hint Resolve modulus_pos: ints.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded). *)

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

(** Fast normalization modulo [2^wordsize] *)

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p wordsize
  | Zneg p => let r := P_mod_two_p p wordsize in if zeq r 0 then 0 else modulus - r
  end.

Lemma Z_mod_modulus_range:
  forall x, 0 <= Z_mod_modulus x < modulus.
Proof (Z_mod_two_p_range wordsize).

Lemma Z_mod_modulus_range':
  forall x, -1 < Z_mod_modulus x < modulus.
Proof.
  intros. generalize (Z_mod_modulus_range x); intuition auto with zarith.
Qed.

Lemma Z_mod_modulus_eq:
  forall x, Z_mod_modulus x = x mod modulus.
Proof (Z_mod_two_p_eq wordsize).

(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr (x: Z) : int :=
  mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr zwordsize.

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros. subst y.
  assert (forall (n m: Z) (P1 P2: n < m), P1 = P2).
  {
    unfold Z.lt; intros.
    apply eq_proofs_unicity.
    intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  destruct Px as [Px1 Px2]. destruct Py as [Py1 Py2].
  rewrite (H _ _ Px1 Py1).
  rewrite (H _ _ Px2 Py2).
  reflexivity.
Qed.

Lemma eq_dec: forall (x y: int), {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y. destruct (zeq intval0 intval1).
  left. apply mkint_eq. auto.
  right. red; intro. injection H. exact n.
Defined.

(** * Arithmetic and logical operations over machine integers *)

Definition eq (x y: int) : bool :=
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: int) : int := repr (- unsigned x).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

Definition divs (x y: int) : int :=
  repr (Z.quot (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Z.rem (signed x) (signed y)).

Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr ((unsigned x) mod (unsigned y)).

(** Bitwise boolean operations. *)

Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: int): int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: int) : int := repr (Z.lxor (unsigned x) (unsigned y)).

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int := repr (Z.shiftl (unsigned x) (unsigned y)).
Definition shru (x y: int): int := repr (Z.shiftr (unsigned x) (unsigned y)).
Definition shr (x y: int): int := repr (Z.shiftr (signed x) (unsigned y)).

Definition rol (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
Definition ror (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).

Definition rolm (x a m: int): int := and (rol x a) m.

(** Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. *)

Definition shrx (x y: int): int :=
  divs x (shl one y).

(** High half of full multiply. *)

Definition mulhu (x y: int): int := repr ((unsigned x * unsigned y) / modulus).
Definition mulhs (x y: int): int := repr ((signed x * signed y) / modulus).

(** Condition flags *)

Definition negative (x: int): int :=
  if lt x zero then one else zero.

Definition add_carry (x y cin: int): int :=
  if zlt (unsigned x + unsigned y + unsigned cin) modulus then zero else one.

Definition add_overflow (x y cin: int): int :=
  let s := signed x + signed y + signed cin in
  if zle min_signed s && zle s max_signed then zero else one.

Definition sub_borrow (x y bin: int): int :=
  if zlt (unsigned x - unsigned y - unsigned bin) 0 then one else zero.

Definition sub_overflow (x y bin: int): int :=
  let s := signed x - signed y - signed bin in
  if zle min_signed s && zle s max_signed then zero else one.

(** [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted away. *)

Definition shr_carry (x y: int) : int :=
  if lt x zero && negb (eq (and x (sub (shl one y) one)) zero)
  then one else zero.

(** Zero and sign extensions *)

Definition zero_ext (n: Z) (x: int) : int := repr (Zzero_ext n (unsigned x)).
Definition sign_ext (n: Z) (x: int) : int := repr (Zsign_ext n (unsigned x)).

(** Decomposition of a number as a sum of powers of two. *)

Definition one_bits (x: int) : list int :=
  List.map repr (Z_one_bits wordsize (unsigned x) 0).

(** Recognition of powers of two. *)

Definition is_power2 (x: int) : option int :=
  match Z_is_power2 (unsigned x) with
  | Some i => Some (repr i)
  | None => None
  end.

(** Comparisons. *)

Definition cmp (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

Definition is_false (x: int) : Prop := x = zero.
Definition is_true  (x: int) : Prop := x <> zero.
Definition notbool  (x: int) : int  := if eq x zero then one else zero.

(** Count leading zeros. *)

Definition clz (x: int) : int :=
  if eq x zero then repr zwordsize
  else repr (zwordsize - 1 - Z.log2 (unsigned x)).

(** Reverse all bits. *)

Definition reverse_bits (x: int) : int :=
  repr (Z_reverse_bits zwordsize (unsigned x)).

(** Count trailing zeros. *)

Definition ctz (x: int) : int := clz (reverse_bits x).

(** Byte-reverse a 32-bit integer (the [bswap32] / [rev] operation).
    Defined as the canonical OR-of-shifts chain so that platform
    [Obswap32] operators that lower to a single instruction can match
    its semantics by construction.  Equivalent to
    [Int.repr (decode_int (List.rev (encode_int 4 (Int.unsigned n))))]
    on little-endian targets. *)

Definition bswap32 (n : int) : int :=
  or (or (or
            (shl (and n (repr 65280)) (repr 8))
            (shl (and n (repr 255)) (repr 24)))
            (shru (and n (repr 16711680)) (repr 8)))
            (shru (and n (repr 4278190080)) (repr 24)).

(** x86-style extended division and modulus *)

Definition divmodu2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.div_eucl (unsigned nhi * modulus + unsigned nlo) (unsigned d) in
    if zle q max_unsigned then Some(repr q, repr r) else None).

Definition divmods2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.quotrem (signed nhi * modulus + unsigned nlo) (signed d) in
    if zle min_signed q && zle q max_signed then Some(repr q, repr r) else None).

(** * Properties of integers and integer arithmetic *)

(** ** Properties of [modulus], [max_unsigned], etc. *)

Remark half_modulus_power:
  half_modulus = two_p (zwordsize - 1).
Proof.
  unfold half_modulus. rewrite modulus_power.
  set (ws1 := zwordsize - 1).
  replace (zwordsize) with (Z.succ ws1).
  rewrite two_p_S. rewrite Z.mul_comm. apply Z_div_mult. lia.
  unfold ws1. generalize wordsize_pos; lia.
  unfold ws1. lia.
Qed.

Remark half_modulus_modulus: modulus = 2 * half_modulus.
Proof.
  rewrite half_modulus_power. rewrite modulus_power.
  rewrite <- two_p_S. apply f_equal. lia.
  generalize wordsize_pos; lia.
Qed.

(** Relative positions, from greatest to smallest:
<<
      max_unsigned
      max_signed
      2*wordsize-1
      wordsize
      0
      min_signed
>>
*)

Remark half_modulus_pos: half_modulus > 0.
Proof.
  rewrite half_modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; lia.
Qed.

Remark min_signed_neg: min_signed < 0.
Proof.
  unfold min_signed. generalize half_modulus_pos. lia.
Qed.

Remark max_signed_pos: max_signed >= 0.
Proof.
  unfold max_signed. generalize half_modulus_pos. lia.
Qed.

Remark wordsize_max_unsigned: zwordsize <= max_unsigned.
Proof.
  assert (zwordsize < modulus).
    rewrite modulus_power. apply two_p_strict.
    generalize wordsize_pos. lia.
  unfold max_unsigned. lia.
Qed.

Remark two_wordsize_max_unsigned: 2 * zwordsize - 1 <= max_unsigned.
Proof.
  assert (2 * zwordsize - 1 < modulus).
    rewrite modulus_power. apply two_p_strict_2. generalize wordsize_pos; lia.
  unfold max_unsigned; lia.
Qed.

Remark max_signed_unsigned: max_signed < max_unsigned.
Proof.
  unfold max_signed, max_unsigned. rewrite half_modulus_modulus.
  generalize half_modulus_pos. lia.
Qed.

Lemma unsigned_repr_eq:
  forall x, unsigned (repr x) = Z.modulo x modulus.
Proof.
  intros. simpl. apply Z_mod_modulus_eq.
Qed.

Lemma signed_repr_eq:
  forall x, signed (repr x) = if zlt (Z.modulo x modulus) half_modulus then Z.modulo x modulus else Z.modulo x modulus - modulus.
Proof.
  intros. unfold signed. rewrite unsigned_repr_eq. auto.
Qed.
  
(** ** Modulo arithmetic *)

(** [eqm] is equality modulo $2^{wordsize}$ #2<sup>wordsize</sup>#. *)

Definition eqm := eqmod modulus.

Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Global Hint Resolve eqm_refl: ints.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Global Hint Resolve eqm_refl2: ints.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (eqmod_sym modulus).
Global Hint Resolve eqm_sym: ints.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (eqmod_trans modulus).
Global Hint Resolve eqm_trans: ints.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (eqmod_small_eq modulus).
Global Hint Resolve eqm_small_eq: ints.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (eqmod_add modulus).
Global Hint Resolve eqm_add: ints.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (eqmod_neg modulus).
Global Hint Resolve eqm_neg: ints.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (eqmod_sub modulus).
Global Hint Resolve eqm_sub: ints.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (eqmod_mult modulus).
Global Hint Resolve eqm_mult: ints.

Lemma eqm_same_bits:
  forall x y,
  (forall i, 0 <= i < zwordsize -> Z.testbit x i = Z.testbit y i) ->
  eqm x y.
Proof (eqmod_same_bits wordsize).

Lemma same_bits_eqm:
  forall x y i,
  eqm x y ->
  0 <= i < zwordsize ->
  Z.testbit x i = Z.testbit y i.
Proof (same_bits_eqmod wordsize).

(** ** Properties of the coercions between [Z] and [int] *)

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
Proof.
  intros. unfold repr. apply mkint_eq.
  rewrite !Z_mod_modulus_eq. apply eqmod_mod_eq. auto with ints. exact H.
Qed.

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
Proof.
  unfold eqm; intros. rewrite unsigned_repr_eq. apply eqmod_mod. auto with ints.
Qed.
Global Hint Resolve eqm_unsigned_repr: ints.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
Proof.
  intros. apply eqm_trans with a.
  apply eqm_sym. apply eqm_unsigned_repr. auto.
Qed.
Global Hint Resolve eqm_unsigned_repr_l: ints.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
Proof.
  intros. apply eqm_trans with b. auto.
  apply eqm_unsigned_repr.
Qed.
Global Hint Resolve eqm_unsigned_repr_r: ints.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
Proof.
  intros; red. unfold signed. set (y := unsigned x).
  case (zlt y half_modulus); intro.
  apply eqmod_refl. red; exists (-1); ring.
Qed.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
Proof.
  destruct i. simpl. lia.
Qed.
Global Hint Resolve unsigned_range: ints.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
Proof.
  intro; unfold max_unsigned.
  generalize (unsigned_range i). lia.
Qed.
Global Hint Resolve unsigned_range_2: ints.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
Proof.
  intros. unfold signed.
  generalize (unsigned_range i). set (n := unsigned i). intros.
  case (zlt n half_modulus); intro.
  unfold max_signed. generalize min_signed_neg. lia.
  unfold min_signed, max_signed.
  rewrite half_modulus_modulus in *. lia.
Qed.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
Proof.
  destruct i; simpl. unfold repr. apply mkint_eq.
  rewrite Z_mod_modulus_eq. apply Z.mod_small; lia.
Qed.
Global Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
Proof.
  intros. transitivity (repr (unsigned i)).
  apply eqm_samerepr. apply eqm_signed_unsigned. auto with ints.
Qed.
Global Hint Resolve repr_signed: ints.

Opaque repr.

Lemma eqm_repr_eq: forall x y, eqm x (unsigned y) -> repr x = y.
Proof.
  intros. rewrite <- (repr_unsigned y). apply eqm_samerepr; auto.
Qed.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
Proof.
  intros. rewrite unsigned_repr_eq.
  apply Z.mod_small. unfold max_unsigned in H. lia.
Qed.
Global Hint Resolve unsigned_repr: ints.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
Proof.
  intros. unfold signed. destruct (zle 0 z).
  replace (unsigned (repr z)) with z.
  rewrite zlt_true. auto. unfold max_signed in H. lia.
  symmetry. apply unsigned_repr. generalize max_signed_unsigned. lia.
  pose (z' := z + modulus).
  replace (repr z) with (repr z').
  replace (unsigned (repr z')) with z'.
  rewrite zlt_false. unfold z'. lia.
  unfold z'. unfold min_signed in H.
  rewrite half_modulus_modulus. lia.
  symmetry. apply unsigned_repr.
  unfold z', max_unsigned. unfold min_signed, max_signed in H.
  rewrite half_modulus_modulus. lia.
  apply eqm_samerepr. unfold z'; red. exists 1. lia.
Qed.

Theorem signed_eq_unsigned:
  forall x, unsigned x <= max_signed -> signed x = unsigned x.
Proof.
  intros. unfold signed. destruct (zlt (unsigned x) half_modulus).
  auto. unfold max_signed in H. extlia.
Qed.

Theorem signed_positive:
  forall x, signed x >= 0 <-> unsigned x <= max_signed.
Proof.
  intros. unfold signed, max_signed.
  generalize (unsigned_range x) half_modulus_modulus half_modulus_pos; intros.
  destruct (zlt (unsigned x) half_modulus); lia.
Qed.

Lemma nonneg_signed_is_unsigned: forall n,
    signed n >= 0 -> signed n = unsigned n.
Proof.
  unfold signed. intros.
  destruct zlt. reflexivity.
  pose proof (unsigned_range n).
  lia.
Qed.

(** ** Properties of zero, one, minus one *)

Theorem unsigned_zero: unsigned zero = 0.
Proof.
  unfold zero; rewrite unsigned_repr_eq. apply Zmod_0_l.
Qed.

Theorem unsigned_one: unsigned one = 1.
Proof.
  unfold one; rewrite unsigned_repr_eq. apply Z.mod_small. split. lia.
  unfold modulus. replace wordsize with (S(Init.Nat.pred wordsize)).
  rewrite two_power_nat_S. generalize (two_power_nat_pos (Init.Nat.pred wordsize)).
  lia.
  generalize wordsize_pos. unfold zwordsize. lia.
Qed.

Theorem unsigned_mone: unsigned mone = modulus - 1.
Proof.
  unfold mone; rewrite unsigned_repr_eq.
  replace (-1) with ((modulus - 1) + (-1) * modulus).
  rewrite Z_mod_plus_full. apply Z.mod_small.
  generalize modulus_pos. lia. lia.
Qed.

Theorem signed_zero: signed zero = 0.
Proof.
  unfold signed. rewrite unsigned_zero. apply zlt_true. generalize half_modulus_pos; lia.
Qed.

Theorem signed_one: zwordsize > 1 -> signed one = 1.
Proof.
  intros. unfold signed. rewrite unsigned_one. apply zlt_true. 
  change 1 with (two_p 0). rewrite half_modulus_power. apply two_p_monotone_strict. lia. 
Qed.

Theorem signed_mone: signed mone = -1.
Proof.
  unfold signed. rewrite unsigned_mone.
  rewrite zlt_false. lia.
  rewrite half_modulus_modulus. generalize half_modulus_pos. lia.
Qed.

Theorem one_not_zero: one <> zero.
Proof.
  assert (unsigned one <> unsigned zero).
  rewrite unsigned_one; rewrite unsigned_zero; congruence.
  congruence.
Qed.

Theorem unsigned_repr_wordsize:
  unsigned iwordsize = zwordsize.
Proof.
  unfold iwordsize; rewrite unsigned_repr_eq. apply Z.mod_small.
  generalize wordsize_pos wordsize_max_unsigned; unfold max_unsigned; lia.
Qed.


(** exact division *)

Definition divu_exact (x y : int) : option int :=
  if negb (zeq (unsigned y) 0) && zeq ((unsigned x) mod (unsigned y)) 0
  then Some (repr ((unsigned x) / (unsigned y)))
  else None.

Theorem divu_exact_expand: forall x y,
    match divu_exact x y with
    | None => True
    | Some d =>
      let (py, oy) := Zmax_two_power (unsigned y) in
      d = mul (shru x (repr py)) (repr (multiplicative_inverse modulus oy))
    end.
Proof.
  unfold divu_exact. intros.
  destruct zeq as [ZERO | NONZERO]; cbn. { trivial. }
  destruct zeq as [EXACT | INEXACT]; cbn; cycle 1. { trivial. }
  pose proof (divexact_to_mul_inverse wordsize (unsigned x) (unsigned y) NONZERO (Zmod_divide _ _ NONZERO EXACT)) as CORRECT.
  change (two_power_nat wordsize) with modulus in *.
  change (eqmod modulus) with eqm in *.
  assert (- two_power_nat wordsize < unsigned y < two_power_nat wordsize) as RANGE.
  { pose proof (unsigned_range y) as RANGE. unfold modulus in RANGE. lia. } 
  pose proof (Zmax_two_power_range (unsigned y) wordsize NONZERO RANGE) as SMALL.
  clear RANGE.
  destruct Zmax_two_power as (py & oy). cbn in SMALL.
  fold zwordsize in SMALL.
  unfold mul, shru.
  apply eqm_samerepr.
  eapply eqm_trans. exact CORRECT. clear CORRECT.
  apply eqm_mult.
  - apply eqm_unsigned_repr_r.
    rewrite unsigned_repr; cycle 1.
    { pose proof wordsize_max_unsigned. lia. }
    apply eqm_refl.
  - apply eqm_unsigned_repr_r. apply eqm_refl.
Qed.

Definition divs_exact (x y : int) : option int :=
  if negb (zeq (signed y) 0) && zeq ((signed x) mod (signed y)) 0
  then Some (repr ((signed x) / (signed y)))
  else None.

Lemma signed_0_unsigned_0: forall x, signed x = 0 <-> unsigned x = 0.
Proof.
  unfold signed. intros.
  pose proof (unsigned_range x).
  rewrite half_modulus_modulus in *.
  destruct zlt. { intuition. }
  lia.
Qed.
  
Theorem divs_exact_expand: forall x y,
    match divs_exact x y with
    | None => True
    | Some d =>
      let (py, oy) := Zmax_two_power (signed y) in
      d = mul (shr x (repr py)) (repr (multiplicative_inverse modulus oy))
    end.
Proof.
  unfold divs_exact. intros.
  destruct zeq as [ZERO | NONZERO]; cbn. { trivial. }
  destruct zeq as [EXACT | INEXACT]; cbn; cycle 1. { trivial. }
  pose proof (divexact_to_mul_inverse wordsize (signed x) (signed y) NONZERO (Zmod_divide _ _ NONZERO EXACT)) as CORRECT.
  change (two_power_nat wordsize) with modulus in *.
  change (eqmod modulus) with eqm in *.
  assert (- two_power_nat wordsize < signed y < two_power_nat wordsize) as RANGE.
  { pose proof (signed_range y) as RANGE.
    unfold min_signed, max_signed in RANGE.
    change  (two_power_nat wordsize) with modulus.
    rewrite half_modulus_modulus. lia. }
  pose proof (Zmax_two_power_range (signed y) wordsize NONZERO RANGE) as SMALL.
  clear RANGE.
  destruct Zmax_two_power as (py & oy). cbn in SMALL.
  fold zwordsize in SMALL.
  unfold mul, shru.
  apply eqm_samerepr.
  eapply eqm_trans. exact CORRECT. clear CORRECT.
  apply eqm_mult.
  - apply eqm_unsigned_repr_r.
    rewrite unsigned_repr; cycle 1.
    { pose proof wordsize_max_unsigned. lia. }
    apply eqm_refl.
  - apply eqm_unsigned_repr_r. apply eqm_refl.
Qed.

(** ** Properties of equality *)

Theorem eq_sym:
  forall x y, eq x y = eq y x.
Proof.
  intros; unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  rewrite e. rewrite zeq_true. auto.
  rewrite zeq_false. auto. auto.
Qed.

Theorem eq_spec: forall (x y: int), if eq x y then x = y else x <> y.
Proof.
  intros; unfold eq. case (eq_dec x y); intro.
  subst y. rewrite zeq_true. auto.
  rewrite zeq_false. auto.
  destruct x; destruct y.
  simpl. red; intro. elim n. apply mkint_eq. auto.
Qed.

Theorem eq_true: forall x, eq x x = true.
Proof.
  intros. generalize (eq_spec x x); case (eq x x); intros; congruence.
Qed.

Theorem eq_false: forall x y, x <> y -> eq x y = false.
Proof.
  intros. generalize (eq_spec x y); case (eq x y); intros; congruence.
Qed.

Theorem lt_false: forall x, lt x x = false.
Proof.
  intros. unfold lt.
  destruct zlt. lia. reflexivity.
Qed.

Theorem ltu_false: forall x, ltu x x = false.
Proof.
  intros. unfold ltu.
  destruct zlt. lia. reflexivity.
Qed.

Theorem same_if_eq: forall x y, eq x y = true -> x = y.
Proof.
  intros. generalize (eq_spec x y); rewrite H; auto.
Qed.

Theorem eq_signed:
  forall x y, eq x y = if zeq (signed x) (signed y) then true else false.
Proof.
  intros. predSpec eq eq_spec x y.
  subst x. rewrite zeq_true; auto.
  destruct (zeq (signed x) (signed y)); auto.
  elim H. rewrite <- (repr_signed x). rewrite <- (repr_signed y). congruence.
Qed.

(** ** Properties of addition *)

Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
Proof. intros; reflexivity.
Qed.

Theorem add_signed: forall x y, add x y = repr (signed x + signed y).
Proof.
  intros. rewrite add_unsigned. apply eqm_samerepr.
  apply eqm_add; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof. intros; unfold add. decEq. lia. Qed.

Theorem add_zero: forall x, add x zero = x.
Proof.
  intros. unfold add. rewrite unsigned_zero.
  rewrite Z.add_0_r. apply repr_unsigned.
Qed.

Theorem add_zero_l: forall x, add zero x = x.
Proof.
  intros. rewrite add_commut. apply add_zero.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  intros; unfold add.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr.
  apply eqm_trans with ((x' + y') + z').
  auto with ints.
  rewrite <- Z.add_assoc. auto with ints.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_neg_zero: forall x, add x (neg x) = zero.
Proof.
  intros; unfold add, neg, zero. apply eqm_samerepr.
  replace 0 with (unsigned x + (- (unsigned x))).
  auto with ints. lia.
Qed.

Theorem unsigned_add_carry:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus.
Proof.
  intros.
  unfold add, add_carry. rewrite unsigned_zero. rewrite Z.add_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. apply Zmod_unique with 0. lia. lia.
  rewrite unsigned_one. apply Zmod_unique with 1. lia. lia.
Qed.

Corollary unsigned_add_either:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y
  \/ unsigned (add x y) = unsigned x + unsigned y - modulus.
Proof.
  intros. rewrite unsigned_add_carry. unfold add_carry.
  rewrite unsigned_zero. rewrite Z.add_0_r.
  destruct (zlt (unsigned x + unsigned y) modulus).
  rewrite unsigned_zero. left; lia.
  rewrite unsigned_one. right; lia.
Qed.

(** ** Properties of negation *)

Theorem neg_repr: forall z, neg (repr z) = repr (-z).
Proof.
  intros; unfold neg. apply eqm_samerepr. auto with ints.
Qed.

Theorem neg_zero: neg zero = zero.
Proof.
  unfold neg. rewrite unsigned_zero. auto.
Qed.

Theorem neg_involutive: forall x, neg (neg x) = x.
Proof.
  intros; unfold neg.
  apply eqm_repr_eq. eapply eqm_trans. apply eqm_neg.
  apply eqm_unsigned_repr_l. apply eqm_refl. apply eqm_refl2. lia.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  intros; unfold neg, add. apply eqm_samerepr.
  apply eqm_trans with (- (unsigned x + unsigned y)).
  auto with ints.
  replace (- (unsigned x + unsigned y))
     with ((- unsigned x) + (- unsigned y)).
  auto with ints. lia.
Qed.

(** ** Properties of subtraction *)

Theorem sub_zero_l: forall x, sub x zero = x.
Proof.
  intros; unfold sub. rewrite unsigned_zero.
  replace (unsigned x - 0) with (unsigned x) by lia. apply repr_unsigned.
Qed.

Theorem sub_zero_r: forall x, sub zero x = neg x.
Proof.
  intros; unfold sub, neg. rewrite unsigned_zero. auto.
Qed.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
Proof.
  intros; unfold sub, add, neg. apply eqm_samerepr.
  apply eqm_add; auto with ints.
Qed.

Theorem sub_idem: forall x, sub x x = zero.
Proof.
  intros; unfold sub. unfold zero. decEq. lia.
Qed.

Theorem sub_add_l: forall x y z, sub (add x y) z = add (sub x z) y.
Proof.
  intros. repeat rewrite sub_add_opp.
  repeat rewrite add_assoc. decEq. apply add_commut.
Qed.

Theorem sub_add_r: forall x y z, sub x (add y z) = add (sub x z) (neg y).
Proof.
  intros. repeat rewrite sub_add_opp.
  rewrite neg_add_distr. rewrite add_permut. apply add_commut.
Qed.

Theorem sub_shifted:
  forall x y z,
  sub (add x z) (add y z) = sub x y.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_add_distr.
  rewrite add_assoc.
  rewrite (add_commut (neg y) (neg z)).
  rewrite <- (add_assoc z). rewrite add_neg_zero.
  rewrite (add_commut zero). rewrite add_zero.
  symmetry. apply sub_add_opp.
Qed.

Theorem sub_signed:
  forall x y, sub x y = repr (signed x - signed y).
Proof.
  intros. unfold sub. apply eqm_samerepr.
  apply eqm_sub; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

Theorem unsigned_sub_borrow:
  forall x y,
  unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus.
Proof.
  intros.
  unfold sub, sub_borrow. rewrite unsigned_zero. rewrite Z.sub_0_r.
  rewrite unsigned_repr_eq.
  generalize (unsigned_range x) (unsigned_range y). intros.
  destruct (zlt (unsigned x - unsigned y) 0).
  rewrite unsigned_one. apply Zmod_unique with (-1). lia. lia.
  rewrite unsigned_zero. apply Zmod_unique with 0. lia. lia.
Qed.

(** ** Properties of multiplication *)

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  intros; unfold mul. decEq. ring.
Qed.

Theorem mul_zero: forall x, mul x zero = zero.
Proof.
  intros; unfold mul. rewrite unsigned_zero.
  unfold zero. decEq. ring.
Qed.

Theorem mul_one: forall x, mul x one = x.
Proof.
  intros; unfold mul. rewrite unsigned_one.
  transitivity (repr (unsigned x)). decEq. ring.
  apply repr_unsigned.
Qed.

Theorem mul_mone: forall x, mul x mone = neg x.
Proof.
  intros; unfold mul, neg. rewrite unsigned_mone.
  apply eqm_samerepr.
  replace (-unsigned x) with (0 - unsigned x) by lia.
  replace (unsigned x * (modulus - 1)) with (unsigned x * modulus - unsigned x) by ring.
  apply eqm_sub. exists (unsigned x). lia. apply eqm_refl.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  intros; unfold mul.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_samerepr. apply eqm_trans with ((x' * y') * z').
  auto with ints.
  rewrite <- Z.mul_assoc. auto with ints.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  intros; unfold mul, add.
  apply eqm_samerepr.
  set (x' := unsigned x).
  set (y' := unsigned y).
  set (z' := unsigned z).
  apply eqm_trans with ((x' + y') * z').
  auto with ints.
  replace ((x' + y') * z') with (x' * z' + y' * z').
  auto with ints.
  ring.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  intros. rewrite mul_commut. rewrite mul_add_distr_l.
  decEq; apply mul_commut.
Qed.

Theorem neg_mul_distr_l:
  forall x y, neg(mul x y) = mul (neg x) y.
Proof.
  intros. unfold mul, neg.
  set (x' := unsigned x).  set (y' := unsigned y).
  apply eqm_samerepr. apply eqm_trans with (- (x' * y')).
  auto with ints.
  replace (- (x' * y')) with ((-x') * y') by ring.
  auto with ints.
Qed.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
Proof.
  intros. rewrite (mul_commut x y). rewrite (mul_commut x (neg y)).
  apply neg_mul_distr_l.
Qed.

Theorem mul_signed:
  forall x y, mul x y = repr (signed x * signed y).
Proof.
  intros; unfold mul. apply eqm_samerepr.
  apply eqm_mult; apply eqm_sym; apply eqm_signed_unsigned.
Qed.

(** ** Properties of division and modulus *)

Lemma modu_divu_Euclid:
  forall x y, y <> zero -> x = add (mul (divu x y) y) (modu x y).
Proof.
  intros. unfold add, mul, divu, modu.
  transitivity (repr (unsigned x)). auto with ints.
  apply eqm_samerepr.
  set (x' := unsigned x). set (y' := unsigned y).
  apply eqm_trans with ((x' / y') * y' + x' mod y').
  apply eqm_refl2. rewrite Z.mul_comm. apply Z_div_mod_eq.
  generalize (unsigned_range y); intro.
  assert (unsigned y <> 0). red; intro.
  elim H. rewrite <- (repr_unsigned y). unfold zero. congruence.
  unfold y'. lia.
  auto with ints.
Qed.

Theorem modu_divu:
  forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).
Proof.
  intros.
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H0. apply modu_divu_Euclid. auto.
Qed.

Lemma mods_divs_Euclid:
  forall x y, x = add (mul (divs x y) y) (mods x y).
Proof.
  intros. unfold add, mul, divs, mods.
  transitivity (repr (signed x)). auto with ints.
  apply eqm_samerepr.
  set (x' := signed x). set (y' := signed y).
  apply eqm_trans with ((Z.quot x' y') * y' + Z.rem x' y').
  apply eqm_refl2. rewrite Z.mul_comm. apply Z.quot_rem'.
  apply eqm_add; auto with ints.
  apply eqm_unsigned_repr_r. apply eqm_mult; auto with ints.
  unfold y'. apply eqm_signed_unsigned.
Qed.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
Proof.
  intros.
  assert (forall a b c, a = add b c -> c = sub a b).
  intros. subst a. rewrite sub_add_l. rewrite sub_idem.
  rewrite add_commut. rewrite add_zero. auto.
  apply H. apply mods_divs_Euclid.
Qed.

Theorem divu_one:
  forall x, divu x one = x.
Proof.
  unfold divu; intros. rewrite unsigned_one. rewrite Zdiv_1_r. apply repr_unsigned.
Qed.

Theorem divs_one:
  forall x, zwordsize > 1 -> divs x one = x.
Proof.
  unfold divs; intros. rewrite signed_one. rewrite Z.quot_1_r. apply repr_signed. auto.
Qed.

Theorem modu_one:
  forall x, modu x one = zero.
Proof.
  intros. rewrite modu_divu. rewrite divu_one. rewrite mul_one. apply sub_idem.
  apply one_not_zero.
Qed.

Theorem divs_mone:
  forall x, divs x mone = neg x.
Proof.
  unfold divs, neg; intros.
  rewrite signed_mone.
  replace (Z.quot (signed x) (-1)) with (- (signed x)).
  apply eqm_samerepr. apply eqm_neg. apply eqm_signed_unsigned.
  set (x' := signed x).
  set (one := 1).
  change (-1) with (- one). rewrite Zquot_opp_r.
  assert (Z.quot x' one = x').
  symmetry. apply Zquot_unique_full with 0. red.
  change (Z.abs one) with 1.
  destruct (zle 0 x'). left. lia. right. lia.
  unfold one; ring.
  congruence.
Qed.

Theorem mods_mone:
  forall x, mods x mone = zero.
Proof.
  intros. rewrite mods_divs. rewrite divs_mone.
  rewrite <- neg_mul_distr_l. rewrite mul_mone. rewrite neg_involutive. apply sub_idem.
Qed.

Theorem divmodu2_divu_modu:
  forall n d,
  d <> zero -> divmodu2 zero n d = Some (divu n d, modu n d).
Proof.
  unfold divmodu2, divu, modu; intros.
  rewrite dec_eq_false by auto.
  set (N := unsigned zero * modulus + unsigned n).
  assert (E1: unsigned n = N) by (unfold N; rewrite unsigned_zero; ring). rewrite ! E1.
  set (D := unsigned d).
  set (Q := N / D); set (R := N mod D).
  assert (E2: Z.div_eucl N D = (Q, R)).
  { unfold Q, R, Z.div, Z.modulo. destruct (Z.div_eucl N D); auto. }
  rewrite E2. rewrite zle_true. auto.
  assert (unsigned d <> 0).
  { red; intros. elim H. rewrite <- (repr_unsigned d). rewrite H0; auto. }
  assert (0 < D).
  { unfold D. generalize (unsigned_range d); intros. lia. }
  assert (0 <= Q <= max_unsigned).
  { unfold Q. apply Zdiv_interval_2.
    rewrite <- E1; apply unsigned_range_2.
    lia. unfold max_unsigned; generalize modulus_pos; lia. lia. }
  lia.
Qed.

Lemma unsigned_signed:
  forall n, unsigned n = if lt n zero then signed n + modulus else signed n.
Proof.
  intros. unfold lt. rewrite signed_zero. unfold signed.
  generalize (unsigned_range n). rewrite half_modulus_modulus. intros.
  destruct (zlt (unsigned n) half_modulus).
- rewrite zlt_false by lia. auto.
- rewrite zlt_true by lia. ring.
Qed.

Theorem divmods2_divs_mods:
  forall n d,
  d <> zero -> n <> repr min_signed \/ d <> mone ->
  divmods2 (if lt n zero then mone else zero) n d = Some (divs n d, mods n d).
Proof.
  unfold divmods2, divs, mods; intros.
  rewrite dec_eq_false by auto.
  set (N := signed (if lt n zero then mone else zero) * modulus + unsigned n).
  set (D := signed d).
  assert (D <> 0).
  { unfold D; red; intros. elim H. rewrite <- (repr_signed d). rewrite H1; auto. }
  assert (N = signed n).
  { unfold N. rewrite unsigned_signed. destruct (lt n zero).
    rewrite signed_mone. ring.
    rewrite signed_zero. ring. }
  set (Q := Z.quot N D); set (R := Z.rem N D).
  assert (E2: Z.quotrem N D = (Q, R)).
  { unfold Q, R, Z.quot, Z.rem. destruct (Z.quotrem N D); auto. }
  rewrite E2.
  assert (min_signed <= N <= max_signed) by (rewrite H2; apply signed_range).
  assert (min_signed <= Q <= max_signed).
  { unfold Q. destruct (zeq D 1); [ | destruct (zeq D (-1))].
  - (* D = 1 *)
    rewrite e. rewrite Z.quot_1_r; auto.
  - (* D = -1 *)
    rewrite e. change (-1) with (Z.opp 1). rewrite Z.quot_opp_r by lia.
    rewrite Z.quot_1_r.
    assert (N <> min_signed).
    { red; intros; destruct H0.
    + elim H0. rewrite <- (repr_signed n). rewrite <- H2. rewrite H4. auto.
    + elim H0. rewrite <- (repr_signed d). unfold D in e; rewrite e; auto. }
    unfold min_signed, max_signed in *. lia.
  - (* |D| > 1 *)
    assert (Z.abs (Z.quot N D) < half_modulus).
    { rewrite <- Z.quot_abs by lia. apply Zquot_lt_upper_bound.
      extlia. extlia.
      apply Z.le_lt_trans with (half_modulus * 1).
      rewrite Z.mul_1_r. unfold min_signed, max_signed in H3; extlia.
      apply Zmult_lt_compat_l. generalize half_modulus_pos; lia. extlia. }
    rewrite Z.abs_lt in H4.
    unfold min_signed, max_signed; lia.
  }
  unfold proj_sumbool; rewrite ! zle_true by lia; simpl.
  unfold Q, R; rewrite H2; auto.
Qed.
  
(** ** Bit-level properties *)

Definition testbit (x: int) (i: Z) : bool := Z.testbit (unsigned x) i.

Lemma testbit_repr:
  forall x i,
  0 <= i < zwordsize ->
  testbit (repr x) i = Z.testbit x i.
Proof.
  intros. unfold testbit. apply same_bits_eqm; auto with ints.
Qed.

Lemma same_bits_eq:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = testbit y i) ->
  x = y.
Proof.
  intros. rewrite <- (repr_unsigned x). rewrite <- (repr_unsigned y).
  apply eqm_samerepr. apply eqm_same_bits. auto.
Qed.

Lemma bits_above:
  forall x i, i >= zwordsize -> testbit x i = false.
Proof.
  intros. apply Ztestbit_above with wordsize; auto. apply unsigned_range.
Qed.

Lemma bits_below:
  forall x i, i < 0 -> testbit x i = false.
Proof.
  intros. apply Z.testbit_neg_r; auto.
Qed.

Lemma bits_zero:
  forall i, testbit zero i = false.
Proof.
  intros. unfold testbit. rewrite unsigned_zero. apply Ztestbit_0.
Qed.

Remark bits_one: forall n, testbit one n = zeq n 0.
Proof.
  unfold testbit; intros. rewrite unsigned_one. apply Ztestbit_1.
Qed.

Lemma bits_mone:
  forall i, 0 <= i < zwordsize -> testbit mone i = true.
Proof.
  intros. unfold mone. rewrite testbit_repr; auto. apply Ztestbit_m1. lia.
Qed.

#[global]
Hint Rewrite bits_zero bits_mone : ints.

Ltac bit_solve :=
  intros; apply same_bits_eq; intros; autorewrite with ints; auto with bool.

Lemma sign_bit_of_unsigned:
  forall x, testbit x (zwordsize - 1) = if zlt (unsigned x) half_modulus then false else true.
Proof.
  intros. unfold testbit.
  set (ws1 := Init.Nat.pred wordsize).
  assert (zwordsize - 1 = Z.of_nat ws1).
    unfold zwordsize, ws1, wordsize.
    destruct WS.wordsize as [] eqn:E.
    elim WS.wordsize_not_zero; auto.
    rewrite Nat2Z.inj_succ. simpl. lia.
  assert (half_modulus = two_power_nat ws1).
    rewrite two_power_nat_two_p. rewrite <- H. apply half_modulus_power.
  rewrite H; rewrite H0.
  apply Zsign_bit. rewrite two_power_nat_S. rewrite <- H0.
  rewrite <- half_modulus_modulus. apply unsigned_range.
Qed.

Local Transparent repr.
Lemma sign_bit_of_signed: forall x,
    (testbit x (zwordsize - 1)) = lt x zero.
Proof.
  intro.
  rewrite sign_bit_of_unsigned.
  unfold lt.
  unfold signed, unsigned.
  simpl.
  pose proof half_modulus_pos as HMOD.
  destruct (zlt 0 half_modulus) as [HMOD' | HMOD'].
  2: lia.
  clear HMOD'.
  destruct (zlt (intval x) half_modulus) as [ LOW | HIGH].
  {
    destruct x as [ix RANGE].
    simpl in *.
    destruct (zlt ix 0). lia.
    reflexivity.
  }
  destruct (zlt _ _) as [LOW' | HIGH']; trivial.
  destruct x as [ix RANGE].
  simpl in *.
  rewrite half_modulus_modulus in *.
  lia.
Qed.
Local Opaque repr.

Lemma bits_signed:
  forall x i, 0 <= i ->
  Z.testbit (signed x) i = testbit x (if zlt i zwordsize then i else zwordsize - 1).
Proof.
  intros.
  destruct (zlt i zwordsize).
  - apply same_bits_eqm. apply eqm_signed_unsigned. lia.
  - unfold signed. rewrite sign_bit_of_unsigned. destruct (zlt (unsigned x) half_modulus).
    + apply Ztestbit_above with wordsize. apply unsigned_range. auto.
    + apply Ztestbit_above_neg with wordsize.
      fold modulus. generalize (unsigned_range x). lia. auto.
Qed.

Lemma bits_le:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = true -> testbit y i = true) ->
  unsigned x <= unsigned y.
Proof.
  intros. apply Ztestbit_le. generalize (unsigned_range y); lia.
  intros. fold (testbit y i). destruct (zlt i zwordsize).
  apply H. lia. auto.
  fold (testbit x i) in H1. rewrite bits_above in H1; auto. congruence.
Qed.

(** ** Properties of bitwise and, or, xor *)

Lemma bits_and:
  forall x y i, 0 <= i < zwordsize ->
  testbit (and x y) i = testbit x i && testbit y i.
Proof.
  intros. unfold and. rewrite testbit_repr; auto. rewrite Z.land_spec; intuition.
Qed.

Lemma bits_or:
  forall x y i, 0 <= i < zwordsize ->
  testbit (or x y) i = testbit x i || testbit y i.
Proof.
  intros. unfold or. rewrite testbit_repr; auto. rewrite Z.lor_spec; intuition.
Qed.

Lemma bits_xor:
  forall x y i, 0 <= i < zwordsize ->
  testbit (xor x y) i = xorb (testbit x i) (testbit y i).
Proof.
  intros. unfold xor. rewrite testbit_repr; auto. rewrite Z.lxor_spec; intuition.
Qed.

Lemma bits_not:
  forall x i, 0 <= i < zwordsize ->
  testbit (not x) i = negb (testbit x i).
Proof.
  intros. unfold not. rewrite bits_xor; auto. rewrite bits_mone; auto.
Qed.

#[global]
Hint Rewrite bits_and bits_or bits_xor bits_not: ints.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  bit_solve.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  bit_solve.
Qed.

Theorem and_zero: forall x, and x zero = zero.
Proof.
  bit_solve; apply andb_b_false.
Qed.

Corollary and_zero_l: forall x, and zero x = zero.
Proof.
  intros. rewrite and_commut. apply and_zero.
Qed.

Theorem and_mone: forall x, and x mone = x.
Proof.
  bit_solve; apply andb_b_true.
Qed.

Corollary and_mone_l: forall x, and mone x = x.
Proof.
  intros. rewrite and_commut. apply and_mone.
Qed.

Theorem and_idem: forall x, and x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  bit_solve.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  bit_solve.
Qed.

Theorem or_zero: forall x, or x zero = x.
Proof.
  bit_solve.
Qed.

Corollary or_zero_l: forall x, or zero x = x.
Proof.
  intros. rewrite or_commut. apply or_zero.
Qed.

Theorem or_mone: forall x, or x mone = mone.
Proof.
  bit_solve.
Qed.

Theorem or_idem: forall x, or x x = x.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
Proof.
  bit_solve. apply demorgan1.
Qed.

Corollary and_or_distrib_l:
  forall x y z,
  and (or x y) z = or (and x z) (and y z).
Proof.
  intros. rewrite (and_commut (or x y)). rewrite and_or_distrib. f_equal; apply and_commut.
Qed.

Theorem or_and_distrib:
  forall x y z,
  or x (and y z) = and (or x y) (or x z).
Proof.
  bit_solve. apply orb_andb_distrib_r.
Qed.

Corollary or_and_distrib_l:
  forall x y z,
  or (and x y) z = and (or x z) (or y z).
Proof.
  intros. rewrite (or_commut (and x y)). rewrite or_and_distrib. f_equal; apply or_commut.
Qed.

Theorem and_or_absorb: forall x y, and x (or x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a && (a || b) = a) by destr_bool.
  auto.
Qed.

Theorem or_and_absorb: forall x y, or x (and x y) = x.
Proof.
  bit_solve.
  assert (forall a b, a || (a && b) = a) by destr_bool.
  auto.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  bit_solve. apply xorb_comm.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  bit_solve. apply xorb_assoc.
Qed.

Theorem xor_zero: forall x, xor x zero = x.
Proof.
  bit_solve. apply xorb_false.
Qed.

Corollary xor_zero_l: forall x, xor zero x = x.
Proof.
  intros. rewrite xor_commut. apply xor_zero.
Qed.

Theorem xor_idem: forall x, xor x x = zero.
Proof.
  bit_solve. apply xorb_nilpotent.
Qed.

Theorem xor_zero_one: xor zero one = one.
Proof. rewrite xor_commut. apply xor_zero. Qed.

Theorem xor_one_one: xor one one = zero.
Proof. apply xor_idem. Qed.

Theorem xor_zero_equal: forall x y, xor x y = zero -> x = y.
Proof.
  intros. apply same_bits_eq; intros.
  assert (xorb (testbit x i) (testbit y i) = false).
    rewrite <- bits_xor; auto. rewrite H. apply bits_zero.
  destruct (testbit x i); destruct (testbit y i); reflexivity || discriminate.
Qed.

Theorem xor_is_zero: forall x y, eq (xor x y) zero = eq x y.
Proof.
  intros. predSpec eq eq_spec (xor x y) zero.
- apply xor_zero_equal in H. subst y. rewrite eq_true; auto. 
- predSpec eq eq_spec x y.
+ elim H; subst y; apply xor_idem. 
+ auto.
Qed. 

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
Proof.
  bit_solve.
  assert (forall a b c, a && (xorb b c) = xorb (a && b) (a && c)) by destr_bool.
  auto.
Qed.

Theorem and_le:
  forall x y, unsigned (and x y) <= unsigned x.
Proof.
  intros. apply bits_le; intros.
  rewrite bits_and in H0; auto. rewrite andb_true_iff in H0. tauto.
Qed.

Theorem or_le:
  forall x y, unsigned x <= unsigned (or x y).
Proof.
  intros. apply bits_le; intros.
  rewrite bits_or; auto. rewrite H0; auto.
Qed.

(** ** Properties of count leading zeros. *)

Remark clz_zero: clz zero = repr zwordsize.
Proof.
  unfold clz. rewrite eq_true. auto.
Qed.

Remark zwordsize_lt_modulus: zwordsize < modulus.
Proof.
  rewrite modulus_power. apply two_p_strict. generalize wordsize_pos; lia.
Qed.

Lemma unsigned_pos: forall x, x <> zero -> 0 < unsigned x.
Proof.
  intros. generalize (unsigned_range x). unfold unsigned.
  destruct (zeq (intval x) 0).
  - exfalso. apply H. rewrite <- (repr_unsigned x). unfold unsigned. rewrite e. auto.
  - lia.
Qed.

Lemma log2_unsigned_lt: forall x,
  x <> zero -> Z.log2 (unsigned x) < zwordsize.
Proof.
  intros.
  assert (Hpos: 0 < unsigned x) by (apply unsigned_pos; auto).
  assert (Hbound: unsigned x < modulus) by (generalize (unsigned_range x); lia).
  rewrite modulus_power in Hbound.
  destruct (Z.log2_lt_pow2 (unsigned x) zwordsize Hpos) as [Hfwd _].
  apply Hfwd. rewrite <- two_p_correct. auto.
Qed.

Remark unsigned_clz: forall x,
  0 <= unsigned (clz x) <= zwordsize.
Proof.
  intros. unfold clz.
  predSpec eq eq_spec x zero.
  - subst. rewrite unsigned_repr_eq.
    assert (0 <= zwordsize < modulus) by (generalize wordsize_pos zwordsize_lt_modulus; lia).
    rewrite (Z.mod_small _ _ H). lia.
  - rewrite unsigned_repr_eq.
    assert (0 <= zwordsize - 1 - Z.log2 (unsigned x) < modulus).
    { generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x H) zwordsize_lt_modulus. lia. }
    rewrite (Z.mod_small _ _ H0).
    generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x H). lia.
Qed.

Lemma clz_div_wordsize: forall x,
  unsigned (clz x) / zwordsize = if eq x zero then 1 else 0.
Proof.
  intros. unfold clz. predSpec eq eq_spec x zero.
  - assert (0 <= zwordsize <= max_unsigned).
    { unfold max_unsigned. generalize wordsize_pos zwordsize_lt_modulus. lia. }
    rewrite unsigned_repr by lia. apply Z.div_same. generalize wordsize_pos; lia.
  - rewrite unsigned_repr.
    apply Z.div_small.
    generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x H) wordsize_pos. lia.
    generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x H) zwordsize_lt_modulus wordsize_pos.
    unfold max_unsigned. lia.
Qed.

Lemma clz_wordsize_zero: forall x, unsigned (clz x) = zwordsize -> unsigned x = 0.
Proof.
  intros x H. unfold clz in H. destruct (eq x zero) eqn:E.
  - apply same_if_eq in E. subst. apply unsigned_zero.
  - exfalso.
    assert (NZ: x <> zero) by (intro; subst; rewrite eq_true in E; discriminate).
    rewrite unsigned_repr in H.
    + generalize (Z.log2_nonneg (unsigned x)). lia.
    + generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x NZ)
                 zwordsize_lt_modulus. unfold max_unsigned. lia.
Qed.

Lemma clz_bits_zero: forall x i (RANGE: zwordsize - unsigned (clz x) <= i < zwordsize), testbit x i = false.
Proof.
  intros. unfold clz in RANGE. destruct (eq x zero) eqn:E.
  - apply same_if_eq in E. subst. apply bits_zero.
  - assert (NZ: x <> zero) by (intro; subst; rewrite eq_true in E; discriminate).
    rewrite unsigned_repr in RANGE.
    2: { generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x NZ)
                    zwordsize_lt_modulus. unfold max_unsigned. lia. }
    unfold testbit. apply Z.bits_above_log2.
    + generalize (unsigned_range x); lia.
    + lia.
Qed.

Lemma clz_bit_nonzero1: forall x, unsigned (clz x) < zwordsize -> testbit x (zwordsize - unsigned (clz x) - 1) = true.
Proof.
  intros x H. unfold clz in H. destruct (eq x zero) eqn:E.
  - rewrite unsigned_repr in H.
    + lia.
    + unfold max_unsigned. generalize zwordsize_lt_modulus wordsize_pos. lia.
  - assert (NZ: x <> zero) by (intro; subst; rewrite eq_true in E; discriminate).
    unfold clz. rewrite E.
    rewrite unsigned_repr.
    2: { generalize (Z.log2_nonneg (unsigned x)) (log2_unsigned_lt x NZ)
                    zwordsize_lt_modulus. unfold max_unsigned. lia. }
    replace (zwordsize - (zwordsize - 1 - Z.log2 (unsigned x)) - 1)
       with (Z.log2 (unsigned x)) by lia.
    unfold testbit. apply Z.bit_log2.
    apply unsigned_pos. exact NZ.
Qed.

Lemma clz_bit_nonzero2: forall x i, testbit x i = true -> i < zwordsize - unsigned (clz x).
Proof.
  intros x i H.
  destruct (zlt i (zwordsize - unsigned (clz x))) as [LT|GE]; auto.
  exfalso.
  destruct (zlt i zwordsize).
  - rewrite (clz_bits_zero x i) in H by lia. discriminate.
  - rewrite bits_above in H by lia. discriminate.
Qed.

(** ** Properties of bit reversal. *)

Lemma bits_reverse_bits:
  forall x i, 0 <= i < zwordsize ->
  testbit (reverse_bits x) i = testbit x (zwordsize - 1 - i).
Proof.
  intros. unfold reverse_bits, testbit.
  rewrite unsigned_repr.
  - rewrite Z_reverse_bits_spec by lia.
    rewrite zlt_true by lia. auto.
  - unfold max_unsigned. rewrite modulus_power.
    generalize (Z_reverse_bits_range zwordsize (unsigned x)).
    generalize (unsigned_range x) wordsize_pos. lia.
Qed.

Theorem reverse_bits_involutive:
  forall x, reverse_bits (reverse_bits x) = x.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_reverse_bits by auto.
  rewrite bits_reverse_bits by lia.
  f_equal. lia.
Qed.

Lemma reverse_bits_zero: reverse_bits zero = zero.
Proof.
  apply same_bits_eq; intros.
  rewrite bits_reverse_bits by auto.
  rewrite !bits_zero. auto.
Qed.

Lemma reverse_bits_eq_zero:
  forall x, reverse_bits x = zero <-> x = zero.
Proof.
  split; intro.
  - rewrite <- (reverse_bits_involutive x). rewrite H. apply reverse_bits_zero.
  - subst. apply reverse_bits_zero.
Qed.

Lemma eq_reverse_bits:
  forall x, eq (reverse_bits x) zero = eq x zero.
Proof.
  intros. predSpec eq eq_spec (reverse_bits x) zero;
  predSpec eq eq_spec x zero; auto.
  - exfalso. apply H0. apply reverse_bits_eq_zero. exact H.
  - subst. rewrite reverse_bits_zero in H. congruence.
Qed.

(** ** Properties of count trailing zeros. *)

Remark ctz_zero: ctz zero = repr zwordsize.
Proof.
  unfold ctz. rewrite reverse_bits_zero. apply clz_zero.
Qed.

Remark unsigned_ctz: forall x,
  0 <= unsigned (ctz x) <= zwordsize.
Proof.
  intros. unfold ctz. apply unsigned_clz.
Qed.

Lemma ctz_div_wordsize: forall x,
  unsigned (ctz x) / zwordsize = if eq x zero then 1 else 0.
Proof.
  intros. unfold ctz.
  rewrite clz_div_wordsize. rewrite eq_reverse_bits. auto.
Qed.

Lemma ctz_wordsize_zero: forall x, unsigned (ctz x) = zwordsize -> unsigned x = 0.
Proof.
  intros x H. unfold ctz in H.
  apply clz_wordsize_zero in H.
  assert (Hx: reverse_bits x = zero).
  { rewrite <- (repr_unsigned (reverse_bits x)). rewrite H. auto. }
  assert (Hx2: x = zero).
  { rewrite <- (reverse_bits_involutive x). rewrite Hx. apply reverse_bits_zero. }
  subst. apply unsigned_zero.
Qed.

Lemma ctz_bits_zero: forall x i,
  0 <= i < unsigned (ctz x) -> testbit x i = false.
Proof.
  intros. unfold ctz in H.
  assert (R: 0 <= i < zwordsize) by (generalize (unsigned_clz (reverse_bits x)); lia).
  replace (testbit x i) with (testbit (reverse_bits x) (zwordsize - 1 - i)).
  - apply clz_bits_zero. lia.
  - rewrite bits_reverse_bits by lia. f_equal. lia.
Qed.

Lemma ctz_bit_nonzero1: forall x,
  unsigned (ctz x) < zwordsize -> testbit x (unsigned (ctz x)) = true.
Proof.
  intros x H.
  unfold ctz in H |- *.
  set (y := reverse_bits x) in *.
  assert (Hy: testbit y (zwordsize - unsigned (clz y) - 1) = true)
    by (apply clz_bit_nonzero1; auto).
  rewrite <- (reverse_bits_involutive x). fold y.
  rewrite bits_reverse_bits by (generalize (unsigned_clz y); lia).
  replace (zwordsize - 1 - unsigned (clz y))
    with (zwordsize - unsigned (clz y) - 1) by lia.
  exact Hy.
Qed.

Lemma ctz_bit_nonzero2: forall x i,
  testbit x i = true -> unsigned (ctz x) <= i.
Proof.
  intros x i H.
  destruct (zlt i zwordsize).
  - assert (R: 0 <= i) by (destruct (Z.neg_nonneg_cases i); auto;
      rewrite bits_below in H by lia; discriminate).
    unfold ctz.
    set (y := reverse_bits x).
    assert (Hy: testbit y (zwordsize - 1 - i) = true).
    { unfold y. rewrite bits_reverse_bits by lia.
      replace (zwordsize - 1 - (zwordsize - 1 - i)) with i by lia. exact H. }
    generalize (clz_bit_nonzero2 y (zwordsize - 1 - i) Hy). lia.
  - generalize (unsigned_ctz x). lia.
Qed.

(** ** Linking properties between [clz], [ctz] and [reverse_bits]. *)

Lemma clz_reverse_bits: forall x,
  clz (reverse_bits x) = ctz x.
Proof.
  intros. reflexivity.
Qed.

Lemma ctz_reverse_bits: forall x,
  ctz (reverse_bits x) = clz x.
Proof.
  intros. unfold ctz. rewrite reverse_bits_involutive. reflexivity.
Qed.

(** ** Properties of bitwise complement.*)

Theorem not_involutive:
  forall (x: int), not (not x) = x.
Proof.
  intros. unfold not. rewrite xor_assoc. rewrite xor_idem. apply xor_zero.
Qed.

Theorem not_zero:
  not zero = mone.
Proof.
  unfold not. rewrite xor_commut. apply xor_zero.
Qed.

Theorem not_mone:
  not mone = zero.
Proof.
  rewrite <- (not_involutive zero). symmetry. decEq. apply not_zero.
Qed.

Theorem not_or_and_not:
  forall x y, not (or x y) = and (not x) (not y).
Proof.
  bit_solve. apply negb_orb.
Qed.

Theorem not_and_or_not:
  forall x y, not (and x y) = or (not x) (not y).
Proof.
  bit_solve. apply negb_andb.
Qed.

Theorem and_not_self:
  forall x, and x (not x) = zero.
Proof.
  bit_solve.
Qed.

Theorem or_not_self:
  forall x, or x (not x) = mone.
Proof.
  bit_solve.
Qed.

Theorem xor_not_self:
  forall x, xor x (not x) = mone.
Proof.
  bit_solve. destruct (testbit x i); auto.
Qed.

Lemma unsigned_not:
  forall x, unsigned (not x) = max_unsigned - unsigned x.
Proof.
  intros. transitivity (unsigned (repr(-unsigned x - 1))).
  f_equal. bit_solve. rewrite testbit_repr; auto. symmetry. apply Z_one_complement. lia.
  rewrite unsigned_repr_eq. apply Zmod_unique with (-1).
  unfold max_unsigned. lia.
  generalize (unsigned_range x). unfold max_unsigned. lia.
Qed.

Theorem not_neg:
  forall x, not x = add (neg x) mone.
Proof.
  bit_solve.
  rewrite <- (repr_unsigned x) at 1. unfold add.
  rewrite !testbit_repr; auto.
  transitivity (Z.testbit (-unsigned x - 1) i).
  symmetry. apply Z_one_complement. lia.
  apply same_bits_eqm; auto.
  replace (-unsigned x - 1) with (-unsigned x + (-1)) by lia.
  apply eqm_add.
  unfold neg. apply eqm_unsigned_repr.
  rewrite unsigned_mone. exists (-1). ring.
Qed.

Theorem neg_not:
  forall x, neg x = add (not x) one.
Proof.
  intros. rewrite not_neg. rewrite add_assoc.
  replace (add mone one) with zero. rewrite add_zero. auto.
  apply eqm_samerepr. rewrite unsigned_mone. rewrite unsigned_one.
  exists (-1). ring.
Qed.

Theorem sub_add_not:
  forall x y, sub x y = add (add x (not y)) one.
Proof.
  intros. rewrite sub_add_opp. rewrite neg_not.
  rewrite ! add_assoc. auto.
Qed.

Theorem sub_add_not_3:
  forall x y b,
  b = zero \/ b = one ->
  sub (sub x y) b = add (add x (not y)) (xor b one).
Proof.
  intros. rewrite ! sub_add_not. rewrite ! add_assoc. f_equal. f_equal.
  rewrite <- neg_not. rewrite <- sub_add_opp. destruct H; subst b.
  rewrite xor_zero_l. rewrite sub_zero_l. auto.
  rewrite xor_idem. rewrite sub_idem. auto.
Qed.

Theorem sub_borrow_add_carry:
  forall x y b,
  b = zero \/ b = one ->
  sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one.
Proof.
  intros. unfold sub_borrow, add_carry. rewrite unsigned_not.
  replace (unsigned (xor b one)) with (1 - unsigned b).
  destruct (zlt (unsigned x - unsigned y - unsigned b)).
  rewrite zlt_true. rewrite xor_zero_l; auto.
  unfold max_unsigned; lia.
  rewrite zlt_false. rewrite xor_idem; auto.
  unfold max_unsigned; lia.
  destruct H; subst b.
  rewrite xor_zero_l. rewrite unsigned_one, unsigned_zero; auto.
  rewrite xor_idem. rewrite unsigned_one, unsigned_zero; auto.
Qed.

(** ** Connections between [add] and bitwise logical operations. *)

Lemma Z_add_is_or:
  forall i, 0 <= i ->
  forall x y,
  (forall j, 0 <= j <= i -> Z.testbit x j && Z.testbit y j = false) ->
  Z.testbit (x + y) i = Z.testbit x i || Z.testbit y i.
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x y EXCL.
  rewrite (Zdecomp x) in *. rewrite (Zdecomp y) in *.
  transitivity (Z.testbit (Zshiftin (Z.odd x || Z.odd y) (Z.div2 x + Z.div2 y)) i).
  - f_equal. rewrite !Zshiftin_spec.
    exploit (EXCL 0). lia. rewrite !Ztestbit_shiftin_base. intros.
Opaque Z.mul.
    destruct (Z.odd x); destruct (Z.odd y); simpl in *; discriminate || ring.
  - rewrite !Ztestbit_shiftin; auto.
    destruct (zeq i 0).
    + auto.
    + apply IND. lia. intros.
      exploit (EXCL (Z.succ j)). lia.
      rewrite !Ztestbit_shiftin_succ. auto.
      lia. lia.
Qed.

Theorem add_is_or:
  forall x y,
  and x y = zero ->
  add x y = or x y.
Proof.
  bit_solve. unfold add. rewrite testbit_repr; auto.
  apply Z_add_is_or. lia.
  intros.
  assert (testbit (and x y) j = testbit zero j) by congruence.
  autorewrite with ints in H2. assumption. lia.
Qed.

Theorem xor_is_or:
  forall x y, and x y = zero -> xor x y = or x y.
Proof.
  bit_solve.
  assert (testbit (and x y) i = testbit zero i) by congruence.
  autorewrite with ints in H1; auto.
  destruct (testbit x i); destruct (testbit y i); simpl in *; congruence.
Qed.

Theorem add_is_xor:
  forall x y,
  and x y = zero ->
  add x y = xor x y.
Proof.
  intros. rewrite xor_is_or; auto. apply add_is_or; auto.
Qed.

Theorem add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
Proof.
  intros. rewrite add_is_or.
  rewrite and_or_distrib; auto.
  rewrite (and_commut x y).
  rewrite and_assoc.
  repeat rewrite <- (and_assoc x).
  rewrite (and_commut (and x x)).
  rewrite <- and_assoc.
  rewrite H. rewrite and_commut. apply and_zero.
Qed.

(** ** Properties of shifts *)

Lemma bits_shl:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl x y) i =
  if zlt i (unsigned y) then false else testbit x (i - unsigned y).
Proof.
  intros. unfold shl. rewrite testbit_repr; auto.
  destruct (zlt i (unsigned y)).
  apply Z.shiftl_spec_low. auto.
  apply Z.shiftl_spec_high. lia. lia.
Qed.

Lemma bits_shru:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru x y) i =
  if zlt (i + unsigned y) zwordsize then testbit x (i + unsigned y) else false.
Proof.
  intros. unfold shru. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. fold (testbit x (i + unsigned y)).
  destruct (zlt (i + unsigned y) zwordsize).
  auto.
  apply bits_above; auto.
  lia.
Qed.

Lemma bits_shr:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr x y) i =
  testbit x (if zlt (i + unsigned y) zwordsize then i + unsigned y else zwordsize - 1).
Proof.
  intros. unfold shr. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. apply bits_signed.
  generalize (unsigned_range y); lia.
  lia.
Qed.

#[global]
Hint Rewrite bits_shl bits_shru bits_shr: ints.

Theorem shl_zero: forall x, shl x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_false. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shl:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shl x n) (shl y n) = shl (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shl; auto.
  destruct (zlt i (unsigned n)); auto.
  rewrite H; auto. generalize (unsigned_range n); lia.
Qed.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
Proof.
  intros. apply bitwise_binop_shl with andb. exact bits_and. auto.
Qed.

Theorem or_shl:
  forall x y n,
  or (shl x n) (shl y n) = shl (or x y) n.
Proof.
  intros. apply bitwise_binop_shl with orb. exact bits_or. auto.
Qed.

Theorem xor_shl:
  forall x y n,
  xor (shl x n) (shl y n) = shl (xor x y) n.
Proof.
  intros. apply bitwise_binop_shl with xorb. exact bits_xor. auto.
Qed.

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
Proof.
  unfold ltu; intros. destruct (zlt (unsigned x) (unsigned y)).
  split; auto. generalize (unsigned_range x); lia.
  discriminate.
Qed.

Lemma ltu_iwordsize_inv:
  forall x, ltu x iwordsize = true -> 0 <= unsigned x < zwordsize.
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize. auto.
Qed.

Theorem shl_shl:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shl (shl x y) z = shl x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite bits_shl; auto.
  destruct (zlt i (unsigned z)).
  - rewrite bits_shl; auto. rewrite zlt_true. auto. lia.
  - rewrite bits_shl. destruct (zlt (i - unsigned z) (unsigned y)).
    + rewrite bits_shl; auto. rewrite zlt_true. auto. lia.
    + rewrite bits_shl; auto. rewrite zlt_false. f_equal. lia. lia.
    + lia.
Qed.

Theorem sub_ltu:
  forall x y,
    ltu x y = true ->
    0 <= unsigned y - unsigned x <= unsigned y.
Proof.
  intros.
  generalize (ltu_inv x y H). intros .
  split. lia. lia.
Qed.

Theorem shru_zero: forall x, shru x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shru:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shru x n) (shru y n) = shru (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned n) zwordsize); auto.
  rewrite H; auto. generalize (unsigned_range n); lia.
Qed.

Theorem and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
Proof.
  intros. apply bitwise_binop_shru with andb; auto. exact bits_and.
Qed.

Theorem or_shru:
  forall x y n,
  or (shru x n) (shru y n) = shru (or x y) n.
Proof.
  intros. apply bitwise_binop_shru with orb; auto. exact bits_or.
Qed.

Theorem xor_shru:
  forall x y n,
  xor (shru x n) (shru y n) = shru (xor x y) n.
Proof.
  intros. apply bitwise_binop_shru with xorb; auto. exact bits_xor.
Qed.

Theorem shru_shru:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shru (shru x y) z = shru x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_shru. destruct (zlt (i + unsigned z + unsigned y) zwordsize).
    + rewrite bits_shru; auto. rewrite zlt_true. f_equal. lia. lia.
    + rewrite bits_shru; auto. rewrite zlt_false. auto. lia.
    + lia.
  - rewrite bits_shru; auto. rewrite zlt_false. auto. lia.
Qed.

Theorem shr_zero: forall x, shr x zero = x.
Proof.
  bit_solve. rewrite unsigned_zero. rewrite zlt_true. f_equal; lia. lia.
Qed.

Lemma bitwise_binop_shr:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f (shr x n) (shr y n) = shr (f x y) n.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_shr; auto.
  rewrite H; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  generalize (unsigned_range n); lia.
  lia.
Qed.

Theorem and_shr:
  forall x y n,
  and (shr x n) (shr y n) = shr (and x y) n.
Proof.
  intros. apply bitwise_binop_shr with andb. exact bits_and.
Qed.

Theorem or_shr:
  forall x y n,
  or (shr x n) (shr y n) = shr (or x y) n.
Proof.
  intros. apply bitwise_binop_shr with orb. exact bits_or.
Qed.

Theorem xor_shr:
  forall x y n,
  xor (shr x n) (shr y n) = shr (xor x y) n.
Proof.
  intros. apply bitwise_binop_shr with xorb. exact bits_xor.
Qed.

Theorem shr_shr:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shr (shr x y) z = shr x (add y z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  assert (unsigned (add y z) = unsigned y + unsigned z).
    unfold add. apply unsigned_repr.
    generalize two_wordsize_max_unsigned; lia.
  apply same_bits_eq; intros.
  rewrite !bits_shr; auto. f_equal.
  destruct (zlt (i + unsigned z) zwordsize).
  rewrite H4. replace (i + (unsigned y + unsigned z)) with (i + unsigned z + unsigned y) by lia. auto.
  rewrite (zlt_false _ (i + unsigned (add y z))).
  destruct (zlt (zwordsize - 1 + unsigned y) zwordsize); lia.
  lia.
  destruct (zlt (i + unsigned z) zwordsize); lia.
Qed.

Theorem and_shr_shru:
  forall x y z,
  and (shr x z) (shru y z) = shru (and x y) z.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite bits_shr; auto. rewrite !bits_shru; auto.
  destruct (zlt (i + unsigned z) zwordsize).
  - rewrite bits_and; auto. generalize (unsigned_range z); lia.
  - apply andb_false_r.
Qed.

Theorem shr_and_shru_and:
  forall x y z,
  shru (shl z y) y = z ->
  and (shr x y) z = and (shru x y) z.
Proof.
  intros.
  rewrite <- H.
  rewrite and_shru. rewrite and_shr_shru. auto.
Qed.

Theorem shru_lt_zero:
  forall x,
  shru x (repr (zwordsize - 1)) = if lt x zero then one else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shru; auto.
  rewrite unsigned_repr.
  destruct (zeq i 0).
  subst i. rewrite Z.add_0_l. rewrite zlt_true.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. auto. generalize (unsigned_range x); lia.
  rewrite zlt_true. unfold one; rewrite testbit_repr; auto.
  generalize (unsigned_range x); lia.
  lia.
  rewrite zlt_false.
  unfold testbit. rewrite Ztestbit_eq. rewrite zeq_false.
  destruct (lt x zero).
  rewrite unsigned_one. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  rewrite unsigned_zero. simpl Z.div2. rewrite Z.testbit_0_l; auto.
  auto. lia. lia.
  generalize wordsize_max_unsigned; lia.
Qed.

Theorem shr_lt_zero:
  forall x,
  shr x (repr (zwordsize - 1)) = if lt x zero then mone else zero.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_shr; auto.
  rewrite unsigned_repr.
  transitivity (testbit x (zwordsize - 1)).
  f_equal. destruct (zlt (i + (zwordsize - 1)) zwordsize); lia.
  rewrite sign_bit_of_unsigned.
  unfold lt. rewrite signed_zero. unfold signed.
  destruct (zlt (unsigned x) half_modulus).
  rewrite zlt_false. rewrite bits_zero; auto. generalize (unsigned_range x); lia.
  rewrite zlt_true. rewrite bits_mone; auto. generalize (unsigned_range x); lia.
  generalize wordsize_max_unsigned; lia.
Qed.

(** ** Properties of rotations *)

Lemma bits_rol:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (rol x y) i = testbit x ((i - unsigned y) mod zwordsize).
Proof.
  intros. unfold rol.
  exploit (Z_div_mod_eq (unsigned y) zwordsize). apply wordsize_pos.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  intros EQ.
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: lia.
  destruct (zlt i j).
  - rewrite Z.shiftl_spec_low; auto. simpl.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (-k - 1).
    rewrite EQ. ring.
    lia.
  - rewrite Z.shiftl_spec_high.
    fold (testbit x (i + (zwordsize - j))).
    rewrite bits_above. rewrite orb_false_r.
    fold (testbit x (i - j)).
    f_equal. symmetry. apply Zmod_unique with (-k).
    rewrite EQ. ring.
    lia. lia. lia. lia.
Qed.

Lemma bits_ror:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (ror x y) i = testbit x ((i + unsigned y) mod zwordsize).
Proof.
  intros. unfold ror.
  exploit (Z_div_mod_eq (unsigned y) zwordsize). apply wordsize_pos.
  set (j := unsigned y mod zwordsize). set (k := unsigned y / zwordsize).
  intros EQ.
  exploit (Z_mod_lt (unsigned y) zwordsize). apply wordsize_pos.
  fold j. intros RANGE.
  rewrite testbit_repr; auto.
  rewrite Z.lor_spec. rewrite Z.shiftr_spec. 2: lia.
  destruct (zlt (i + j) zwordsize).
  - rewrite Z.shiftl_spec_low; auto. rewrite orb_false_r.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with k.
    rewrite EQ. ring.
    lia. lia.
  - rewrite Z.shiftl_spec_high.
    fold (testbit x (i + j)).
    rewrite bits_above. simpl.
    unfold testbit. f_equal.
    symmetry. apply Zmod_unique with (k + 1).
    rewrite EQ. ring.
    lia. lia. lia. lia.
Qed.

#[global]
Hint Rewrite bits_rol bits_ror: ints.

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shl; auto. rewrite bits_rol; auto.
  destruct (zlt i (unsigned n)).
  - rewrite andb_false_r; auto.
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    symmetry. apply Z.mod_small. lia.
    lia.
Qed.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
Proof.
  intros. generalize (ltu_inv _ _ H). rewrite unsigned_repr_wordsize; intros.
  unfold rolm. apply same_bits_eq; intros.
  rewrite bits_and; auto. rewrite !bits_shru; auto. rewrite bits_rol; auto.
  destruct (zlt (i + unsigned n) zwordsize).
  - generalize (unsigned_range n); intros.
    rewrite bits_mone. rewrite andb_true_r. f_equal.
    unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
    symmetry. apply Zmod_unique with (-1). ring. lia.
    rewrite unsigned_repr_wordsize. generalize wordsize_max_unsigned. lia.
    lia.
  - rewrite andb_false_r; auto.
Qed.

Theorem rol_zero:
  forall x,
  rol x zero = x.
Proof.
  bit_solve. f_equal. rewrite unsigned_zero. rewrite Z.sub_0_r.
  apply Z.mod_small; auto.
Qed.

Lemma bitwise_binop_rol:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  rol (f x y) n = f (rol x n) (rol y n).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite H; auto. rewrite !bits_rol; auto. rewrite H; auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with andb. exact bits_and.
Qed.

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with orb. exact bits_or.
Qed.

Theorem rol_xor:
  forall x y n,
  rol (xor x y) n = xor (rol x n) (rol y n).
Proof.
  intros. apply bitwise_binop_rol with xorb. exact bits_xor.
Qed.

Theorem rol_rol:
  forall x n m,
  Z.divide zwordsize modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
Proof.
  bit_solve. f_equal. apply eqmod_mod_eq. apply wordsize_pos.
  set (M := unsigned m); set (N := unsigned n).
  apply eqmod_trans with (i - M - N).
  apply eqmod_sub.
  apply eqmod_sym. apply eqmod_mod. apply wordsize_pos.
  apply eqmod_refl.
  replace (i - M - N) with (i - (M + N)) by lia.
  apply eqmod_sub.
  apply eqmod_refl.
  apply eqmod_trans with (Z.modulo (unsigned n + unsigned m) zwordsize).
  replace (M + N) with (N + M) by lia. apply eqmod_mod. apply wordsize_pos.
  unfold modu, add. fold M; fold N. rewrite unsigned_repr_wordsize.
  assert (forall a, eqmod zwordsize a (unsigned (repr a))).
    intros. eapply eqmod_divides. apply eqm_unsigned_repr. assumption.
  eapply eqmod_trans. 2: apply H1.
  apply eqmod_refl2. apply eqmod_mod_eq. apply wordsize_pos. auto.
  apply Z_mod_lt. apply wordsize_pos.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
Proof.
  intros. unfold rolm. rewrite rol_zero. auto.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  Z.divide zwordsize modulus ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) iwordsize)
           (and (rol m1 n2) m2).
Proof.
  intros.
  unfold rolm. rewrite rol_and. rewrite and_assoc.
  rewrite rol_rol. reflexivity. auto.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2).
Proof.
  intros; unfold rolm. symmetry. apply and_or_distrib.
Qed.

Theorem ror_rol:
  forall x y,
  ltu y iwordsize = true ->
  ror x y = rol x (sub iwordsize y).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H); intros.
  apply same_bits_eq; intros.
  rewrite bits_ror; auto. rewrite bits_rol; auto. f_equal.
  unfold sub. rewrite unsigned_repr. rewrite unsigned_repr_wordsize.
  apply eqmod_mod_eq. apply wordsize_pos. exists 1. ring.
  rewrite unsigned_repr_wordsize.
  generalize wordsize_pos; generalize wordsize_max_unsigned; lia.
Qed.

Theorem ror_rol_neg:
  forall x y, (zwordsize | modulus) -> ror x y = rol x (neg y).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_ror by auto. rewrite bits_rol by auto.
  f_equal. apply eqmod_mod_eq. lia.
  apply eqmod_trans with (i - (- unsigned y)).
  apply eqmod_refl2; lia.
  apply eqmod_sub. apply eqmod_refl.
  apply eqmod_divides with modulus.
  apply eqm_unsigned_repr. auto.
Qed.

Theorem or_ror:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  add y z = iwordsize ->
  ror x z = or (shl x y) (shru x z).
Proof.
  intros.
  generalize (ltu_iwordsize_inv _ H) (ltu_iwordsize_inv _ H0); intros.
  unfold ror, or, shl, shru. apply same_bits_eq; intros.
  rewrite !testbit_repr; auto.
  rewrite !Z.lor_spec. rewrite orb_comm. f_equal; apply same_bits_eqm; auto.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    rewrite Z.mod_small; auto.
    assert (unsigned (add y z) = zwordsize).
      rewrite H1. apply unsigned_repr_wordsize.
    unfold add in H5. rewrite unsigned_repr in H5.
    lia.
    generalize two_wordsize_max_unsigned; lia.
  - apply eqm_unsigned_repr_r. apply eqm_refl2. f_equal.
    apply Z.mod_small; auto.
Qed.

(** ** Properties of [is_power2]. *)

Remark is_power2_inv:
  forall n logn,
  is_power2 n = Some logn ->
  Z_is_power2 (unsigned n) = Some (unsigned logn) /\ 0 <= unsigned logn < zwordsize.
Proof.
  unfold is_power2; intros.
  destruct (Z_is_power2 (unsigned n)) as [i|] eqn:E; inv H.
  assert (0 <= i < zwordsize).
  { apply Z_is_power2_range with (unsigned n). 
    generalize wordsize_pos; lia.
    rewrite <- modulus_power. apply unsigned_range.
    auto. }
  rewrite unsigned_repr; auto. generalize wordsize_max_unsigned; lia.
Qed.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < zwordsize.
Proof.
  intros. apply (is_power2_inv n logn); auto.
Qed.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn iwordsize = true.
Proof.
  intros. unfold ltu. rewrite unsigned_repr_wordsize.
  apply zlt_true. generalize (is_power2_rng _ _ H). tauto.
Qed.

Lemma is_power2_correct:
  forall n logn,
  is_power2 n = Some logn ->
  unsigned n = two_p (unsigned logn).
Proof.
  intros. apply is_power2_inv in H. destruct H as [P Q].
  apply Z_is_power2_sound in P. tauto.
Qed.

Remark two_p_range:
  forall n,
  0 <= n < zwordsize ->
  0 <= two_p n <= max_unsigned.
Proof.
  intros. split.
  assert (two_p n > 0). apply two_p_gt_ZERO. lia. lia.
  generalize (two_p_monotone_strict _ _ H).
  unfold zwordsize; rewrite <- two_power_nat_two_p.
  unfold max_unsigned, modulus. lia.
Qed.

Lemma is_power2_two_p:
  forall n, 0 <= n < zwordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
Proof.
  intros. unfold is_power2. rewrite unsigned_repr.
  rewrite Z_is_power2_complete by lia; auto.
  apply two_p_range. auto.
Qed.

(** ** Relation between bitwise operations and multiplications / divisions by powers of 2 *)

(** Left shifts and multiplications by powers of 2. *)

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
Proof.
  intros. unfold shl, mul. apply eqm_samerepr.
  rewrite Zshiftl_mul_two_p. auto with ints.
  generalize (unsigned_range y); lia.
Qed.

Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
Proof.
  intros.
  assert (shl one y = repr (two_p (unsigned y))).
  {
    rewrite shl_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
  }
  rewrite H. apply shl_mul_two_p.
Qed.

Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
Proof.
  intros. generalize (is_power2_correct n logn H); intro.
  rewrite shl_mul_two_p. rewrite <- H0. rewrite repr_unsigned.
  auto.
Qed.

Theorem shifted_or_is_add:
  forall x y n,
  0 <= n < zwordsize ->
  unsigned y < two_p n ->
  or (shl x (repr n)) y = repr(unsigned x * two_p n + unsigned y).
Proof.
  intros. rewrite <- add_is_or.
  - unfold add. apply eqm_samerepr. apply eqm_add; auto with ints.
    rewrite shl_mul_two_p. unfold mul. apply eqm_unsigned_repr_l.
    apply eqm_mult; auto with ints. apply eqm_unsigned_repr_l.
    apply eqm_refl2. rewrite unsigned_repr. auto.
    generalize wordsize_max_unsigned; lia.
  - bit_solve.
    rewrite unsigned_repr.
    destruct (zlt i n).
    + auto.
    + replace (testbit y i) with false. apply andb_false_r.
      symmetry. unfold testbit.
      assert (EQ: Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
      apply Ztestbit_above with (Z.to_nat n).
      rewrite <- EQ in H0. rewrite <- two_power_nat_two_p in H0.
      generalize (unsigned_range y); lia.
      rewrite EQ; auto.
    + generalize wordsize_max_unsigned; lia.
Qed.

(** Unsigned right shifts and unsigned divisions by powers of 2. *)

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
Proof.
  intros. unfold shru.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); lia.
Qed.

Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
Proof.
  intros. generalize (is_power2_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. apply shru_div_two_p.
Qed.

(** Signed right shifts and signed divisions by powers of 2. *)

Lemma shr_div_two_p:
  forall x y,
  shr x y = repr (signed x / two_p (unsigned y)).
Proof.
  intros. unfold shr.
  rewrite Zshiftr_div_two_p. auto.
  generalize (unsigned_range y); lia.
Qed.

Theorem divs_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divs x n = shrx x logn.
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  unfold shrx. rewrite shl_mul_two_p.
  rewrite mul_commut. rewrite mul_one.
  rewrite <- H0. rewrite repr_unsigned. auto.
Qed.

(** Unsigned modulus over [2^n] is masking with [2^n-1]. *)

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
Proof.
  intros. generalize (is_power2_correct _ _ H); intro.
  generalize (is_power2_rng _ _ H); intro.
  apply same_bits_eq; intros.
  rewrite bits_and; auto.
  unfold sub. rewrite testbit_repr; auto.
  rewrite H0. rewrite unsigned_one.
  unfold modu. rewrite testbit_repr; auto. rewrite H0.
  rewrite Ztestbit_mod_two_p. rewrite Ztestbit_two_p_m1.
  destruct (zlt i (unsigned logn)).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto. tauto. tauto. tauto.
Qed.

(** ** Properties of [shrx] (signed division by a power of 2) *)

Theorem shrx_zero:
  forall x, zwordsize > 1 -> shrx x zero = x.
Proof.
  intros. unfold shrx. rewrite shl_zero. unfold divs. rewrite signed_one by auto.
  rewrite Z.quot_1_r. apply repr_signed.
Qed. 

Theorem shrx_shr:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y.
Proof.
  intros.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  rewrite shr_div_two_p. unfold shrx. unfold divs.
  assert (shl one y = repr (two_p uy)).
    transitivity (mul one (repr (two_p uy))).
    symmetry. apply mul_pow2. replace y with (repr uy).
    apply is_power2_two_p. lia. apply repr_unsigned.
    rewrite mul_commut. apply mul_one.
  assert (two_p uy > 0). apply two_p_gt_ZERO. lia.
  assert (two_p uy < half_modulus).
    rewrite half_modulus_power.
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (unsigned (shl one y) = two_p uy).
    rewrite H1. apply unsigned_repr. unfold max_unsigned. lia.
  assert (signed (shl one y) = two_p uy).
    rewrite H1. apply signed_repr.
    unfold max_signed. generalize min_signed_neg. lia.
  rewrite H6.
  rewrite Zquot_Zdiv; auto.
  unfold lt. rewrite signed_zero.
  destruct (zlt (signed x) 0); auto.
  rewrite add_signed.
  assert (signed (sub (shl one y) one) = two_p uy - 1).
    unfold sub. rewrite H5. rewrite unsigned_one.
    apply signed_repr.
    generalize min_signed_neg. unfold max_signed. lia.
  rewrite H7. rewrite signed_repr. f_equal. f_equal. lia.
  generalize (signed_range x). intros.
  assert (two_p uy - 1 <= max_signed). unfold max_signed. lia. lia.
Qed.

Theorem shrx_shr_2:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y.
Proof.
  intros.
  rewrite shrx_shr by auto. f_equal.
  rewrite shr_lt_zero. destruct (lt x zero).
- set (uy := unsigned y).
  generalize (unsigned_range y); fold uy; intros.
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  f_equal. rewrite shl_mul_two_p. fold uy. rewrite mul_commut. rewrite mul_one.
  unfold sub. rewrite unsigned_one. rewrite unsigned_repr.
  rewrite unsigned_repr_wordsize. fold uy.
  apply same_bits_eq; intros. rewrite bits_shru by auto.
  rewrite testbit_repr by auto. rewrite Ztestbit_two_p_m1 by lia.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  destruct (zlt i uy).
  rewrite zlt_true by lia. rewrite bits_mone by lia. auto.
  rewrite zlt_false by lia. auto.
  assert (two_p uy > 0) by (apply two_p_gt_ZERO; lia). unfold max_unsigned; lia.
- replace (shru zero (sub iwordsize y)) with zero.
  rewrite add_zero; auto.
  bit_solve. destruct (zlt (i + unsigned (sub iwordsize y)) zwordsize); auto.
Qed.

Theorem shrx1_shr:
  forall x,
  ltu one (repr (zwordsize - 1)) = true ->
  shrx x (repr 1) = shr (add x (shru x (repr (zwordsize - 1)))) (repr 1).
Proof.
  intros.
  rewrite shrx_shr by assumption.
  rewrite shl_mul_two_p.
  rewrite mul_commut. rewrite mul_one.
  change (repr 1) with one.
  rewrite unsigned_one.
  change (two_p 1) with 2.
  unfold sub.
  rewrite unsigned_one.
  assert (0 <= 2 <= max_unsigned).
  {
    unfold max_unsigned, modulus.
    unfold zwordsize in *.
    unfold ltu in *.
    rewrite unsigned_one in H.
    rewrite unsigned_repr in H.
    {
      destruct (zlt 1 (Z.of_nat wordsize - 1)) as [ LT | NONE].
      2: discriminate.
      clear H.
      rewrite two_power_nat_two_p.
      split.
      lia.
      set (w := (Z.of_nat wordsize)) in *.
      assert ((two_p 2) <= (two_p w)) as MONO.
      {
        apply two_p_monotone.
        lia.
      }
      change (two_p 2) with 4 in MONO.
      lia.
    }
    generalize wordsize_max_unsigned.
    fold zwordsize.
    generalize wordsize_pos.
    lia.
  }
  rewrite unsigned_repr by assumption.
  simpl.
  rewrite shru_lt_zero.
  destruct (lt x zero).
  reflexivity.
  rewrite add_zero.
  reflexivity.
Qed.

Theorem shrx_carry:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = add (shr x y) (shr_carry x y).
Proof.
  intros. rewrite shrx_shr; auto. unfold shr_carry.
  unfold lt. set (sx := signed x). rewrite signed_zero.
  destruct (zlt sx 0); simpl.
  2: rewrite add_zero; auto.
  set (uy := unsigned y).
  assert (0 <= uy < zwordsize - 1).
    generalize (ltu_inv _ _ H). rewrite unsigned_repr. auto.
    generalize wordsize_pos wordsize_max_unsigned; lia.
  assert (shl one y = repr (two_p uy)).
    rewrite shl_mul_two_p. rewrite mul_commut. apply mul_one.
  assert (and x (sub (shl one y) one) = modu x (repr (two_p uy))).
    symmetry. rewrite H1. apply modu_and with (logn := y).
    rewrite is_power2_two_p. unfold uy. rewrite repr_unsigned. auto.
    lia.
  rewrite H2. rewrite H1.
  repeat rewrite shr_div_two_p. fold sx. fold uy.
  assert (two_p uy > 0). apply two_p_gt_ZERO. lia.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (two_p uy < half_modulus).
    rewrite half_modulus_power.
    apply two_p_monotone_strict. auto.
  assert (two_p uy < modulus).
    rewrite modulus_power. apply two_p_monotone_strict. lia.
  assert (sub (repr (two_p uy)) one = repr (two_p uy - 1)).
    unfold sub. apply eqm_samerepr. apply eqm_sub. apply eqm_sym; apply eqm_unsigned_repr.
    rewrite unsigned_one. apply eqm_refl.
  rewrite H7. rewrite add_signed. fold sx.
  rewrite (signed_repr (two_p uy - 1)). rewrite signed_repr.
  unfold modu. rewrite unsigned_repr.
  unfold eq. rewrite unsigned_zero. rewrite unsigned_repr.
  assert (unsigned x mod two_p uy = sx mod two_p uy).
    apply eqmod_mod_eq; auto. apply eqmod_divides with modulus.
    fold eqm. unfold sx. apply eqm_sym. apply eqm_signed_unsigned.
    unfold modulus. rewrite two_power_nat_two_p.
    exists (two_p (zwordsize - uy)). rewrite <- two_p_is_exp.
    f_equal. fold zwordsize; lia. lia. lia.
  rewrite H8. rewrite Zdiv_shift; auto.
  unfold add. apply eqm_samerepr. apply eqm_add.
  apply eqm_unsigned_repr.
  destruct (zeq (sx mod two_p uy) 0); simpl.
  rewrite unsigned_zero. apply eqm_refl.
  rewrite unsigned_one. apply eqm_refl.
  generalize (Z_mod_lt (unsigned x) (two_p uy) H3). unfold max_unsigned. lia.
  unfold max_unsigned; lia.
  generalize (signed_range x). fold sx. intros. split. lia. unfold max_signed. lia.
  generalize min_signed_neg. unfold max_signed. lia.
Qed.

(** Connections between [shr] and [shru]. *)

Lemma shr_shru_positive:
  forall x y,
  signed x >= 0 ->
  shr x y = shru x y.
Proof.
  intros.
  rewrite shr_div_two_p. rewrite shru_div_two_p.
  rewrite signed_eq_unsigned. auto. apply signed_positive. auto.
Qed.

Lemma and_positive:
  forall x y, signed y >= 0 -> signed (and x y) >= 0.
Proof.
  intros.
  assert (unsigned y < half_modulus). rewrite signed_positive in H. unfold max_signed in H; lia.
  generalize (sign_bit_of_unsigned y). rewrite zlt_true; auto. intros A.
  generalize (sign_bit_of_unsigned (and x y)). rewrite bits_and. rewrite A.
  rewrite andb_false_r. unfold signed.
  destruct (zlt (unsigned (and x y)) half_modulus).
  intros. generalize (unsigned_range (and x y)); lia.
  congruence.
  generalize wordsize_pos; lia.
Qed.

Theorem shr_and_is_shru_and:
  forall x y z,
  lt y zero = false -> shr (and x y) z = shru (and x y) z.
Proof.
  intros. apply shr_shru_positive. apply and_positive.
  unfold lt in H. rewrite signed_zero in H. destruct (zlt (signed y) 0). congruence. auto.
Qed.

(** ** Properties of [mulhu] (upper bits of unsigned multiplication) *)

Lemma mulhu_zero:
  forall x, mulhu x zero = zero.
Proof.
  intros. unfold mulhu. rewrite unsigned_zero. rewrite Z.mul_0_r.
  reflexivity.
Qed.

Lemma mulhu_one:
  forall x, mulhu x one = zero.
Proof.
  intros. unfold mulhu. rewrite unsigned_one. rewrite Z.mul_1_r.
  rewrite Zdiv_small. reflexivity. apply unsigned_range.
Qed.

Lemma mulhu_commut:
  forall x y, mulhu x y = mulhu y x.
Proof.
  intros. unfold mulhu. rewrite Z.mul_comm. reflexivity.
Qed.

(** ** Properties of [mulhs] (upper bits of signed multiplication) *)

Lemma mulhs_zero:
  forall x, mulhs x zero = zero.
Proof.
  intros. unfold mulhs. rewrite signed_zero. rewrite Z.mul_0_r.
  reflexivity.
Qed.

Lemma mulhs_commut:
  forall x y, mulhs x y = mulhs y x.
Proof.
  intros. unfold mulhs. rewrite Z.mul_comm. reflexivity.
Qed.


(** ** Properties of integer zero extension and sign extension. *)

Lemma bits_zero_ext:
  forall n x i, 0 <= i ->
  testbit (zero_ext n x) i = if zlt i n then testbit x i else false.
Proof.
  intros. unfold zero_ext. destruct (zlt i zwordsize).
  rewrite testbit_repr; auto. rewrite Zzero_ext_spec. auto. auto.
  rewrite !bits_above; auto. destruct (zlt i n); auto.
Qed.

Lemma bits_sign_ext:
  forall n x i, 0 <= i < zwordsize ->
  testbit (sign_ext n x) i = testbit x (if zlt i n then i else n - 1).
Proof.
  intros. unfold sign_ext.
  rewrite testbit_repr; auto. apply Zsign_ext_spec. lia. 
Qed.

#[global]
Hint Rewrite bits_zero_ext bits_sign_ext: ints.

Theorem zero_ext_above:
  forall n x, n >= zwordsize -> zero_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_zero_ext. apply zlt_true. lia. lia.
Qed.

Theorem zero_ext_below:
  forall n x, n <= 0 -> zero_ext n x = zero.
Proof.
  intros. bit_solve. destruct (zlt i n); auto. apply bits_below; lia. lia.
Qed.

Theorem sign_ext_above:
  forall n x, n >= zwordsize -> sign_ext n x = x.
Proof.
  intros. apply same_bits_eq; intros.
  unfold sign_ext; rewrite testbit_repr; auto.
  rewrite Zsign_ext_spec. rewrite zlt_true. auto. lia. lia.
Qed.

Theorem sign_ext_below:
  forall n x, n <= 0 -> sign_ext n x = zero.
Proof.
  intros. bit_solve. apply bits_below. destruct (zlt i n); lia.
Qed.

Theorem zero_ext_and:
  forall n x, 0 <= n -> zero_ext n x = and x (repr (two_p n - 1)).
Proof.
  bit_solve. rewrite testbit_repr; auto. rewrite Ztestbit_two_p_m1; intuition.
  destruct (zlt i n).
  rewrite andb_true_r; auto.
  rewrite andb_false_r; auto.
  tauto.
Qed.

Theorem zero_ext_mod:
  forall n x, 0 <= n < zwordsize ->
  unsigned (zero_ext n x) = Z.modulo (unsigned x) (two_p n).
Proof.
  intros. apply equal_same_bits. intros.
  rewrite Ztestbit_mod_two_p; auto.
  fold (testbit (zero_ext n x) i).
  destruct (zlt i zwordsize).
  rewrite bits_zero_ext; auto.
  rewrite bits_above. rewrite zlt_false; auto. lia. lia.
  lia.
Qed.

Theorem zero_ext_widen:
  forall x n n', 0 <= n <= n' ->
  zero_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. lia.
  destruct (zlt i n'); auto.
  tauto. tauto.
Qed.

Theorem sign_ext_widen:
  forall x n n', 0 < n <= n' ->
  sign_ext n' (sign_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve. destruct (zlt i n').
  auto.
  rewrite (zlt_false _ i n).
  destruct (zlt (n' - 1) n); f_equal; lia.
  lia.
  destruct (zlt i n'); lia.
  apply sign_ext_above; auto.
Qed.

Theorem sign_zero_ext_widen:
  forall x n n', 0 <= n < n' ->
  sign_ext n' (zero_ext n x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n').
  auto.
  rewrite !zlt_false. auto. lia. lia. lia.
  destruct (zlt i n'); lia.
  apply sign_ext_above; auto.
Qed.

Theorem zero_ext_narrow:
  forall x n n', 0 <= n <= n' ->
  zero_ext n (zero_ext n' x) = zero_ext n x.
Proof.
  bit_solve. destruct (zlt i n).
  apply zlt_true. lia.
  auto.
  lia. lia. lia.
Qed.

Theorem sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  sign_ext n (sign_ext n' x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve. destruct (zlt i n); f_equal; apply zlt_true; lia.
  destruct (zlt i n); lia.
  rewrite (sign_ext_above n'). auto. lia.
Qed.

Theorem zero_sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  zero_ext n (sign_ext n' x) = zero_ext n x.
Proof.
  intros. destruct (zlt n' zwordsize).
  bit_solve.
  destruct (zlt i n); auto.
  rewrite zlt_true; auto. lia.
  lia. lia.
  rewrite sign_ext_above; auto.
Qed.

Theorem zero_ext_idem:
  forall n x, 0 <= n -> zero_ext n (zero_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_ext_widen. lia.
Qed.

Theorem sign_ext_idem:
  forall n x, 0 < n -> sign_ext n (sign_ext n x) = sign_ext n x.
Proof.
  intros. apply sign_ext_widen. lia.
Qed.
 
Theorem sign_ext_zero_ext:
  forall n x, 0 < n -> sign_ext n (zero_ext n x) = sign_ext n x.
Proof.
  intros. destruct (zlt n zwordsize).
  bit_solve.
  destruct (zlt i n).
  rewrite zlt_true; auto.
  rewrite zlt_true; auto. lia.
  destruct (zlt i n); lia.
  rewrite zero_ext_above; auto.
Qed.

Theorem zero_ext_sign_ext:
  forall n x, 0 < n -> zero_ext n (sign_ext n x) = zero_ext n x.
Proof.
  intros. apply zero_sign_ext_narrow. lia.
Qed.

Theorem sign_ext_equal_if_zero_equal:
  forall n x y, 0 < n ->
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
Proof.
  intros. rewrite <- (sign_ext_zero_ext n x H).
  rewrite <- (sign_ext_zero_ext n y H). congruence.
Qed.

Theorem shru_shl:
  forall x y z, ltu y iwordsize = true -> ltu z iwordsize = true ->
  shru (shl x y) z =
  if ltu z y then shl (zero_ext (zwordsize - unsigned y) x) (sub y z)
             else zero_ext (zwordsize - unsigned z) (shru x (sub z y)).
Proof.
  intros. apply ltu_iwordsize_inv in H; apply ltu_iwordsize_inv in H0.
  unfold ltu. set (Y := unsigned y) in *; set (Z := unsigned z) in *.
  apply same_bits_eq; intros. rewrite bits_shru by auto. fold Z.
  destruct (zlt Z Y).
- assert (A: unsigned (sub y z) = Y - Z).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  symmetry; rewrite bits_shl, A by lia.
  destruct (zlt (i + Z) zwordsize).
+ rewrite bits_shl by lia. fold Y.
  destruct (zlt i (Y - Z)); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
  rewrite bits_zero_ext by lia. rewrite zlt_true by lia. f_equal; lia.
+ rewrite bits_zero_ext by lia. rewrite ! zlt_false by lia. auto.
- assert (A: unsigned (sub z y) = Z - Y).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_zero_ext, bits_shru, A by lia.
  destruct (zlt (i + Z) zwordsize); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
  rewrite bits_shl by lia. fold Y.
  destruct (zlt (i + Z) Y).
+ rewrite zlt_false by lia. auto.
+ rewrite zlt_true by lia. f_equal; lia.
Qed.

Corollary zero_ext_shru_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  zero_ext n x = shru (shl x y) y.
Proof.
  intros.
  assert (A: unsigned y = zwordsize - n).
  { unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. lia. }
  assert (B: ltu y iwordsize = true).
  { unfold ltu; rewrite A, unsigned_repr_wordsize. apply zlt_true; lia. }
  rewrite shru_shl by auto. unfold ltu; rewrite zlt_false by lia.
  rewrite sub_idem, shru_zero. f_equal. rewrite A; lia.
Qed.

Theorem shr_shl:
  forall x y z, ltu y iwordsize = true -> ltu z iwordsize = true ->
  shr (shl x y) z =
  if ltu z y then shl (sign_ext (zwordsize - unsigned y) x) (sub y z)
             else sign_ext (zwordsize - unsigned z) (shr x (sub z y)).
Proof.
  intros. apply ltu_iwordsize_inv in H; apply ltu_iwordsize_inv in H0.
  unfold ltu. set (Y := unsigned y) in *; set (Z := unsigned z) in *.
  apply same_bits_eq; intros. rewrite bits_shr by auto. fold Z.
  rewrite bits_shl by (destruct (zlt (i + Z) zwordsize); lia). fold Y.
  destruct (zlt Z Y).
- assert (A: unsigned (sub y z) = Y - Z).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_shl, A by lia.
  destruct (zlt i (Y - Z)).
+ apply zlt_true. destruct (zlt (i + Z) zwordsize); lia.
+ rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  rewrite bits_sign_ext by lia. f_equal. 
  destruct (zlt (i + Z) zwordsize).
  rewrite zlt_true by lia. lia.
  rewrite zlt_false by lia. lia.
- assert (A: unsigned (sub z y) = Z - Y).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_sign_ext by lia.
  rewrite bits_shr by (destruct (zlt i (zwordsize - Z)); lia).
  rewrite A. rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  f_equal. destruct (zlt i (zwordsize - Z)).
+ rewrite ! zlt_true by lia. lia.
+ rewrite ! zlt_false by lia. rewrite zlt_true by lia. lia.
Qed.

Corollary sign_ext_shr_shl:
  forall n x,
  0 < n <= zwordsize ->
  let y := repr (zwordsize - n) in
  sign_ext n x = shr (shl x y) y.
Proof.
  intros.
  assert (A: unsigned y = zwordsize - n).
  { unfold y. apply unsigned_repr. generalize wordsize_max_unsigned. lia. }
  assert (B: ltu y iwordsize = true).
  { unfold ltu; rewrite A, unsigned_repr_wordsize. apply zlt_true; lia. }
  rewrite shr_shl by auto. unfold ltu; rewrite zlt_false by lia.
  rewrite sub_idem, shr_zero. f_equal. rewrite A; lia.
Qed.

Theorem shr_shl2:
  forall x y z, ltu y iwordsize = true -> ltu z iwordsize = true ->
  shr (shl x y) z =
  if ltu z y then shl (sign_ext (zwordsize - unsigned y) x) (sub y z)
             else sign_ext (zwordsize - unsigned z) (shru x (sub z y)).
Proof.
  intros. apply ltu_iwordsize_inv in H; apply ltu_iwordsize_inv in H0.
  unfold ltu. set (Y := unsigned y) in *; set (Z := unsigned z) in *.
  apply same_bits_eq; intros. rewrite bits_shr by auto. fold Z.
  rewrite bits_shl by (destruct (zlt (i + Z) zwordsize); lia). fold Y.
  destruct (zlt Z Y).
- assert (A: unsigned (sub y z) = Y - Z).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_shl, A by lia.
  destruct (zlt i (Y - Z)).
+ apply zlt_true. destruct (zlt (i + Z) zwordsize); lia.
+ rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  rewrite bits_sign_ext by lia. f_equal. 
  destruct (zlt (i + Z) zwordsize).
  rewrite zlt_true by lia. lia.
  rewrite zlt_false by lia. lia.
- assert (A: unsigned (sub z y) = Z - Y).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_sign_ext by lia.
  rewrite bits_shru by (destruct (zlt i (zwordsize - Z)); lia).
  rewrite A. rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  f_equal. destruct (zlt i (zwordsize - Z)).
+ rewrite ! zlt_true by lia. f_equal. lia.
+ rewrite ! zlt_false by lia. rewrite zlt_true by lia. f_equal. lia.
Qed.

(** [zero_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [0...2^n-1]. *)

Lemma zero_ext_range:
  forall n x, 0 <= n < zwordsize -> 0 <= unsigned (zero_ext n x) < two_p n.
Proof.
  intros. rewrite zero_ext_mod; auto. apply Z_mod_lt. apply two_p_gt_ZERO. lia.
Qed.

Lemma eqmod_zero_ext:
  forall n x, 0 <= n < zwordsize -> eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x).
Proof.
  intros. rewrite zero_ext_mod; auto. apply eqmod_sym. apply eqmod_mod.
  apply two_p_gt_ZERO. lia.
Qed.

(** [sign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. *)

Lemma sign_ext_range:
  forall n x, 0 < n < zwordsize -> -two_p (n-1) <= signed (sign_ext n x) < two_p (n-1).
Proof.
  intros. rewrite sign_ext_shr_shl by lia.
  set (X := shl x (repr (zwordsize - n))).
  assert (two_p (n - 1) > 0) by (apply two_p_gt_ZERO; lia).
  assert (unsigned (repr (zwordsize - n)) = zwordsize - n).
    apply unsigned_repr.
    split. lia. generalize wordsize_max_unsigned; lia.
  rewrite shr_div_two_p.
  rewrite signed_repr.
  rewrite H1.
  apply Zdiv_interval_1.
  lia. lia. apply two_p_gt_ZERO; lia.
  replace (- two_p (n - 1) * two_p (zwordsize - n))
     with (- (two_p (n - 1) * two_p (zwordsize - n))) by ring.
  rewrite <- two_p_is_exp.
  replace (n - 1 + (zwordsize - n)) with (zwordsize - 1) by lia.
  rewrite <- half_modulus_power.
  generalize (signed_range X). unfold min_signed, max_signed. lia.
  lia. lia.
  apply Zdiv_interval_2. apply signed_range.
  generalize min_signed_neg; lia.
  generalize max_signed_pos; lia.
  rewrite H1. apply two_p_gt_ZERO. lia.
Qed.

Lemma eqmod_sign_ext':
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x).
Proof.
  intros.
  set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; lia).
  rewrite <- H0. rewrite <- two_power_nat_two_p.
  apply eqmod_same_bits; intros.
  rewrite H0 in H1. rewrite H0.
  fold (testbit (sign_ext n x) i). rewrite bits_sign_ext.
  rewrite zlt_true. auto. lia. lia.
Qed.

Lemma eqmod_sign_ext:
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (signed (sign_ext n x)) (unsigned x).
Proof.
  intros. apply eqmod_trans with (unsigned (sign_ext n x)).
  apply eqmod_divides with modulus. apply eqm_signed_unsigned.
  exists (two_p (zwordsize - n)).
  unfold modulus. rewrite two_power_nat_two_p. fold zwordsize.
  rewrite <- two_p_is_exp. f_equal. lia. lia. lia.
  apply eqmod_sign_ext'; auto.
Qed.

(** Combinations of shifts and zero/sign extensions *)

Lemma shl_zero_ext:
  forall n m x, 0 <= n ->
  shl (zero_ext n x) m = zero_ext (n + unsigned m) (shl x m).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_zero_ext, ! bits_shl by lia.
  destruct (zlt i (unsigned m)).
- rewrite zlt_true by lia; auto.
- rewrite bits_zero_ext by lia.
  destruct (zlt (i - unsigned m) n); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
Qed.

Lemma shl_sign_ext:
  forall n m x, 0 < n ->
  shl (sign_ext n x) m = sign_ext (n + unsigned m) (shl x m).
Proof.
  intros. generalize (unsigned_range m); intros.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext, ! bits_shl by lia.
  destruct (zlt i (n + unsigned m)).
- rewrite bits_shl by auto. destruct (zlt i (unsigned m)); auto.
  rewrite bits_sign_ext by lia. f_equal. apply zlt_true. lia.
- rewrite zlt_false by lia. rewrite bits_shl by lia. rewrite zlt_false by lia.
  rewrite bits_sign_ext by lia. f_equal. rewrite zlt_false by lia. lia.
Qed.

Lemma shru_zero_ext:
  forall n m x, 0 <= n ->
  shru (zero_ext (n + unsigned m) x) m = zero_ext n (shru x m).
Proof.
  intros. bit_solve.
- destruct (zlt (i + unsigned m) zwordsize).
* destruct (zlt i n); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
* destruct (zlt i n); auto.
- generalize (unsigned_range m); lia.
- lia.
Qed.

Lemma shru_zero_ext_0:
  forall n m x, n <= unsigned m ->
  shru (zero_ext n x) m = zero.
Proof.
  intros. bit_solve.
- destruct (zlt (i + unsigned m) zwordsize); auto.
  apply zlt_false. lia.
- generalize (unsigned_range m); lia.
Qed.

Lemma shr_sign_ext:
  forall n m x, 0 < n -> n + unsigned m < zwordsize ->
  shr (sign_ext (n + unsigned m) x) m = sign_ext n (shr x m).
Proof.
  intros. generalize (unsigned_range m); intros.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext, bits_shr by auto.
  rewrite bits_sign_ext, bits_shr.
- f_equal.
  destruct (zlt i n), (zlt (i + unsigned m) zwordsize).
+ apply zlt_true; lia.
+ apply zlt_true; lia.
+ rewrite zlt_false by lia. rewrite zlt_true by lia. lia.
+ rewrite zlt_false by lia. rewrite zlt_true by lia. lia.
- destruct (zlt i n); lia.
- destruct (zlt (i + unsigned m) zwordsize); lia.
Qed.

Lemma zero_ext_shru_min:
  forall s x n, ltu n iwordsize = true ->
  zero_ext s (shru x n) = zero_ext (Z.min s (zwordsize - unsigned n)) (shru x n).
Proof.
  intros. apply ltu_iwordsize_inv in H.
  apply Z.min_case_strong; intros; auto.
  bit_solve; try lia.
  destruct (zlt i (zwordsize - unsigned n)).
  rewrite zlt_true by lia. auto.
  destruct (zlt i s); auto. rewrite zlt_false by lia; auto.
Qed.

Lemma sign_ext_shr_min:
  forall s x n, ltu n iwordsize = true ->
  sign_ext s (shr x n) = sign_ext (Z.min s (zwordsize - unsigned n)) (shr x n).
Proof.
  intros. apply ltu_iwordsize_inv in H.
  rewrite Z.min_comm. 
  destruct (Z.min_spec (zwordsize - unsigned n) s) as [[A B] | [A B]]; rewrite B; auto.
  apply same_bits_eq; intros. rewrite ! bits_sign_ext by auto.
  destruct (zlt i (zwordsize - unsigned n)). 
  rewrite zlt_true by lia. auto.
  assert (C: testbit (shr x n) (zwordsize - unsigned n - 1) = testbit x (zwordsize - 1)).
  { rewrite bits_shr by lia. rewrite zlt_true by lia. f_equal; lia. }
  rewrite C. destruct (zlt i s); rewrite bits_shr by lia.
  rewrite zlt_false by lia. auto.
  rewrite zlt_false by lia. auto.
Qed.

Lemma shl_zero_ext_min:
  forall s x n, ltu n iwordsize = true ->
  shl (zero_ext s x) n = shl (zero_ext (Z.min s (zwordsize - unsigned n)) x) n.
Proof.
  intros. apply ltu_iwordsize_inv in H.
  apply Z.min_case_strong; intros; auto.
  apply same_bits_eq; intros. rewrite ! bits_shl by auto.
  destruct (zlt i (unsigned n)); auto.
  rewrite ! bits_zero_ext by lia.
  destruct (zlt (i - unsigned n) s).
  rewrite zlt_true by lia; auto.
  rewrite zlt_false by lia; auto.
Qed.

Lemma shl_sign_ext_min:
  forall s x n, ltu n iwordsize = true ->
  shl (sign_ext s x) n = shl (sign_ext (Z.min s (zwordsize - unsigned n)) x) n.
Proof.
  intros. apply ltu_iwordsize_inv in H.
  rewrite Z.min_comm. 
  destruct (Z.min_spec (zwordsize - unsigned n) s) as [[A B] | [A B]]; rewrite B; auto.
  apply same_bits_eq; intros. rewrite ! bits_shl by auto.
  destruct (zlt i (unsigned n)); auto.
  rewrite ! bits_sign_ext by lia. f_equal.
  destruct (zlt (i - unsigned n) s).
  rewrite zlt_true by lia; auto.
  extlia.
Qed.

(** ** Properties of [one_bits] (decomposition in sum of powers of two) *)

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i iwordsize = true.
Proof.
  assert (A: forall p, 0 <= p < zwordsize -> ltu (repr p) iwordsize = true).
    intros. unfold ltu, iwordsize. apply zlt_true.
    repeat rewrite unsigned_repr. tauto.
    generalize wordsize_max_unsigned; lia.
    generalize wordsize_max_unsigned; lia.
  unfold one_bits. intros.
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]].
  subst i. apply A. apply Z_one_bits_range with (unsigned x); auto.
Qed.

Fixpoint int_of_one_bits (l: list int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl one a) (int_of_one_bits b)
  end.

Theorem one_bits_decomp:
  forall x, x = int_of_one_bits (one_bits x).
Proof.
  intros.
  transitivity (repr (powerserie (Z_one_bits wordsize (unsigned x) 0))).
  transitivity (repr (unsigned x)).
  auto with ints. decEq. apply Z_one_bits_powerserie.
  auto with ints.
  unfold one_bits.
  generalize (Z_one_bits_range wordsize (unsigned x)).
  generalize (Z_one_bits wordsize (unsigned x) 0).
  induction l.
  intros; reflexivity.
  intros; simpl. rewrite <- IHl. unfold add. apply eqm_samerepr.
  apply eqm_add. rewrite shl_mul_two_p. rewrite mul_commut.
  rewrite mul_one. apply eqm_unsigned_repr_r.
  rewrite unsigned_repr. auto with ints.
  generalize (H a (in_eq _ _)). change (Z.of_nat wordsize) with zwordsize.
  generalize wordsize_max_unsigned. lia.
  auto with ints.
  intros; apply H; auto with coqlib.
Qed.

(** ** Properties of comparisons *)

Theorem negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb (cmp c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb (cmpu c x y).
Proof.
  intros. destruct c; simpl; try rewrite negb_elim; auto.
Qed.

Theorem swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Theorem swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
Proof.
  intros. destruct c; simpl; auto. apply eq_sym. decEq. apply eq_sym.
Qed.

Lemma translate_eq:
  forall x y d,
  eq (add x d) (add y d) = eq x y.
Proof.
  intros. unfold eq. case (zeq (unsigned x) (unsigned y)); intro.
  unfold add. rewrite e. apply zeq_true.
  apply zeq_false. unfold add. red; intro. apply n.
  apply eqm_small_eq; auto with ints.
  replace (unsigned x) with ((unsigned x + unsigned d) - unsigned d).
  replace (unsigned y) with ((unsigned y + unsigned d) - unsigned d).
  apply eqm_sub. apply eqm_trans with (unsigned (repr (unsigned x + unsigned d))).
  eauto with ints. apply eqm_trans with (unsigned (repr (unsigned y + unsigned d))).
  eauto with ints. eauto with ints. eauto with ints.
  lia. lia.
Qed.

Lemma translate_ltu:
  forall x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  ltu (add x d) (add y d) = ltu x y.
Proof.
  intros. unfold add. unfold ltu.
  repeat rewrite unsigned_repr; auto. case (zlt (unsigned x) (unsigned y)); intro.
  apply zlt_true. lia.
  apply zlt_false. lia.
Qed.

Theorem translate_cmpu:
  forall c x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  cmpu c (add x d) (add y d) = cmpu c x y.
Proof.
  intros. unfold cmpu.
  rewrite translate_eq. repeat rewrite translate_ltu; auto.
Qed.

Lemma translate_lt:
  forall x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  lt (add x d) (add y d) = lt x y.
Proof.
  intros. repeat rewrite add_signed. unfold lt.
  repeat rewrite signed_repr; auto. case (zlt (signed x) (signed y)); intro.
  apply zlt_true. lia.
  apply zlt_false. lia.
Qed.

Theorem translate_cmp:
  forall c x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  cmp c (add x d) (add y d) = cmp c x y.
Proof.
  intros. unfold cmp.
  rewrite translate_eq. repeat rewrite translate_lt; auto.
Qed.

Theorem notbool_isfalse_istrue:
  forall x, is_false x -> is_true (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros; subst x.
  rewrite eq_true. apply one_not_zero.
Qed.

Theorem notbool_istrue_isfalse:
  forall x, is_true x -> is_false (notbool x).
Proof.
  unfold is_false, is_true, notbool; intros.
  generalize (eq_spec x zero). case (eq x zero); intro.
  contradiction. auto.
Qed.

Theorem ltu_range_test:
  forall x y,
  ltu x y = true -> unsigned y <= max_signed ->
  0 <= signed x < unsigned y.
Proof.
  intros.
  unfold ltu in H. destruct (zlt (unsigned x) (unsigned y)); try discriminate.
  rewrite signed_eq_unsigned.
  generalize (unsigned_range x). lia. lia.
Qed.

Theorem lt_sub_overflow:
  forall x y,
  xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero.
Proof.
  intros. unfold negative, sub_overflow, lt. rewrite sub_signed.
  rewrite signed_zero. rewrite Z.sub_0_r.
  generalize (signed_range x) (signed_range y).
  set (X := signed x); set (Y := signed y). intros RX RY.
  unfold min_signed, max_signed in *.
  generalize half_modulus_pos half_modulus_modulus; intros HM MM.
  destruct (zle 0 (X - Y)).
- unfold proj_sumbool at 1; rewrite zle_true at 1 by lia. simpl.
  rewrite (zlt_false _ X) by lia.
  destruct (zlt (X - Y) half_modulus).
  + unfold proj_sumbool; rewrite zle_true by lia.
    rewrite signed_repr. rewrite zlt_false by lia. apply xor_idem.
    unfold min_signed, max_signed; lia.
  + unfold proj_sumbool; rewrite zle_false by lia.
    replace (signed (repr (X - Y))) with (X - Y - modulus).
    rewrite zlt_true by lia. apply xor_idem.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y).
    rewrite zlt_false; auto.
    symmetry. apply Zmod_unique with 0; lia.
- unfold proj_sumbool at 2. rewrite zle_true at 1 by lia. rewrite andb_true_r.
  rewrite (zlt_true _ X) by lia.
  destruct (zlt (X - Y) (-half_modulus)).
  + unfold proj_sumbool; rewrite zle_false by lia.
    replace (signed (repr (X - Y))) with (X - Y + modulus).
    rewrite zlt_false by lia. apply xor_zero.
    rewrite signed_repr_eq. replace ((X - Y) mod modulus) with (X - Y + modulus).
    rewrite zlt_true by lia; auto.
    symmetry. apply Zmod_unique with (-1); lia.
  + unfold proj_sumbool; rewrite zle_true by lia.
    rewrite signed_repr. rewrite zlt_true by lia. apply xor_zero_l.
    unfold min_signed, max_signed; lia.
Qed.

Lemma signed_eq:
  forall x y, eq x y = zeq (signed x) (signed y).
Proof.
  intros. unfold eq. unfold proj_sumbool.
  destruct (zeq (unsigned x) (unsigned y));
  destruct (zeq (signed x) (signed y)); auto.
  elim n. unfold signed. rewrite e; auto.
  elim n. apply eqm_small_eq; auto with ints.
  eapply eqm_trans. apply eqm_sym. apply eqm_signed_unsigned.
  rewrite e. apply eqm_signed_unsigned.
Qed.

Lemma not_lt:
  forall x y, negb (lt y x) = (lt x y || eq x y).
Proof.
  intros. unfold lt. rewrite signed_eq. unfold proj_sumbool.
  destruct (zlt (signed y) (signed x)).
  rewrite zlt_false. rewrite zeq_false. auto. lia. lia.
  destruct (zeq (signed x) (signed y)).
  rewrite zlt_false. auto. lia.
  rewrite zlt_true. auto. lia.
Qed.

Lemma lt_not:
  forall x y, lt y x = negb (lt x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_lt. rewrite negb_involutive. auto.
Qed.

Lemma not_ltu:
  forall x y, negb (ltu y x) = (ltu x y || eq x y).
Proof.
  intros. unfold ltu, eq.
  destruct (zlt (unsigned y) (unsigned x)).
  rewrite zlt_false. rewrite zeq_false. auto. lia. lia.
  destruct (zeq (unsigned x) (unsigned y)).
  rewrite zlt_false. auto. lia.
  rewrite zlt_true. auto. lia.
Qed.

Lemma ltu_not:
  forall x y, ltu y x = negb (ltu x y) && negb (eq x y).
Proof.
  intros. rewrite <- negb_orb. rewrite <- not_ltu. rewrite negb_involutive. auto.
Qed.

(** ** Non-overlapping test *)

Definition no_overlap (ofs1: int) (sz1: Z) (ofs2: int) (sz2: Z) : bool :=
  let x1 := unsigned ofs1 in let x2 := unsigned ofs2 in
     zlt (x1 + sz1) modulus && zlt (x2 + sz2) modulus
  && (zle (x1 + sz1) x2 || zle (x2 + sz2) x1).

Lemma no_overlap_sound:
  forall ofs1 sz1 ofs2 sz2 base,
  sz1 > 0 -> sz2 > 0 -> no_overlap ofs1 sz1 ofs2 sz2 = true ->
  unsigned (add base ofs1) + sz1 <= unsigned (add base ofs2)
  \/ unsigned (add base ofs2) + sz2 <= unsigned (add base ofs1).
Proof.
  intros.
  destruct (andb_prop _ _ H1). clear H1.
  destruct (andb_prop _ _ H2). clear H2.
  apply proj_sumbool_true in H1.
  apply proj_sumbool_true in H4.
  assert (unsigned ofs1 + sz1 <= unsigned ofs2 \/ unsigned ofs2 + sz2 <= unsigned ofs1).
  destruct (orb_prop _ _ H3). left. eapply proj_sumbool_true; eauto. right. eapply proj_sumbool_true; eauto.
  clear H3.
  generalize (unsigned_range ofs1) (unsigned_range ofs2). intros P Q.
  generalize (unsigned_add_either base ofs1) (unsigned_add_either base ofs2).
  intros [C|C] [D|D]; lia.
Qed.

(** ** Size of integers, in bits. *)

Definition size (x: int) : Z := Zsize (unsigned x).

Theorem size_zero: size zero = 0.
Proof.
  unfold size; rewrite unsigned_zero; auto.
Qed.

Theorem bits_size_1:
  forall x, x = zero \/ testbit x (Z.pred (size x)) = true.
Proof.
  intros. destruct (zeq (unsigned x) 0).
  left. rewrite <- (repr_unsigned x). rewrite e; auto.
  right. apply Ztestbit_size_1. generalize (unsigned_range x); lia.
Qed.

Theorem bits_size_2:
  forall x i, size x <= i -> testbit x i = false.
Proof.
  intros. apply Ztestbit_size_2. generalize (unsigned_range x); lia.
  fold (size x); lia.
Qed.

Theorem size_range:
  forall x, 0 <= size x <= zwordsize.
Proof.
  intros; split. apply Zsize_pos.
  destruct (bits_size_1 x).
  subst x; unfold size; rewrite unsigned_zero; simpl. generalize wordsize_pos; lia.
  destruct (zle (size x) zwordsize); auto.
  rewrite bits_above in H. congruence. lia.
Qed.

Theorem bits_size_3:
  forall x n,
  0 <= n ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x <= n.
Proof.
  intros. destruct (zle (size x) n). auto.
  destruct (bits_size_1 x).
  subst x. unfold size; rewrite unsigned_zero; assumption.
  rewrite (H0 (Z.pred (size x))) in H1. congruence.
  generalize (size_range x); lia.
Qed.

Theorem bits_size_4:
  forall x n,
  0 <= n ->
  testbit x (Z.pred n) = true ->
  (forall i, n <= i < zwordsize -> testbit x i = false) ->
  size x = n.
Proof.
  intros.
  assert (size x <= n).
    apply bits_size_3; auto.
  destruct (zlt (size x) n).
  rewrite bits_size_2 in H0. congruence. lia.
  lia.
Qed.

Theorem size_interval_1:
  forall x, 0 <= unsigned x < two_p (size x).
Proof.
  intros; apply Zsize_interval_1. generalize (unsigned_range x); lia.
Qed.

Theorem size_interval_2:
  forall x n, 0 <= n -> 0 <= unsigned x < two_p n -> n >= size x.
Proof.
  intros. apply Zsize_interval_2; auto.
Qed.

Theorem size_and:
  forall a b, size (and a b) <= Z.min (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.min (size a) (size b)).
    generalize (size_range a) (size_range b). zify; lia.
  apply bits_size_3. auto. intros.
  rewrite bits_and by lia.
  rewrite andb_false_iff.
  generalize (bits_size_2 a i).
  generalize (bits_size_2 b i).
  zify; intuition auto with zarith.
Qed.

Corollary and_interval:
  forall a b, 0 <= unsigned (and a b) < two_p (Z.min (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (and a b)); intros.
  assert (two_p (size (and a b)) <= two_p (Z.min (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (and a b)); lia.
  apply size_and.
  lia.
Qed.

Theorem size_or:
  forall a b, size (or a b) = Z.max (size a) (size b).
Proof.
  intros. generalize (size_range a) (size_range b); intros.
  destruct (bits_size_1 a).
  subst a. rewrite size_zero. rewrite or_zero_l. zify; lia.
  destruct (bits_size_1 b).
  subst b. rewrite size_zero. rewrite or_zero. zify; lia.
  zify. destruct H3 as [[P Q] | [P Q]]; subst.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H2. apply orb_true_r.
  lia.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. lia. lia. lia.
  apply bits_size_4. tauto. rewrite bits_or. rewrite H1. apply orb_true_l.
  destruct (zeq (size a) 0). unfold testbit in H1. rewrite Z.testbit_neg_r in H1.
  congruence. lia. lia.
  intros. rewrite bits_or. rewrite !bits_size_2. auto. lia. lia. lia.
Qed.

Corollary or_interval:
  forall a b, 0 <= unsigned (or a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros. rewrite <- size_or. apply size_interval_1.
Qed.

Theorem size_xor:
  forall a b, size (xor a b) <= Z.max (size a) (size b).
Proof.
  intros.
  assert (0 <= Z.max (size a) (size b)).
    generalize (size_range a) (size_range b). zify; lia.
  apply bits_size_3. auto. intros.
  rewrite bits_xor. rewrite !bits_size_2. auto.
  zify; lia.
  zify; lia.
  lia.
Qed.

Corollary xor_interval:
  forall a b, 0 <= unsigned (xor a b) < two_p (Z.max (size a) (size b)).
Proof.
  intros.
  generalize (size_interval_1 (xor a b)); intros.
  assert (two_p (size (xor a b)) <= two_p (Z.max (size a) (size b))).
  apply two_p_monotone. split. generalize (size_range (xor a b)); lia.
  apply size_xor.
  lia.
Qed.

(** ** Accessing bit fields *)

Definition unsigned_bitfield_extract (pos width: Z) (n: int) : int :=
  zero_ext width (shru n (repr pos)).

Definition signed_bitfield_extract (pos width: Z) (n: int) : int :=
  sign_ext width (shru n (repr pos)).

Definition bitfield_insert (pos width: Z) (n p: int) : int :=
  let mask := shl (repr (two_p width - 1)) (repr pos) in
  or (shl (zero_ext width p) (repr pos))
     (and n (not mask)).

Lemma bits_unsigned_bitfield_extract:
  forall pos width n i,
  0 <= pos -> 0 < width -> pos + width <= zwordsize ->
  0 <= i < zwordsize ->
  testbit (unsigned_bitfield_extract pos width n) i =
  if zlt i width then testbit n (i + pos) else false.
Proof.
  intros. unfold unsigned_bitfield_extract. rewrite bits_zero_ext by lia.
  destruct (zlt i width); auto.
  rewrite bits_shru by auto. rewrite unsigned_repr, zlt_true. auto.
  lia.
  generalize wordsize_max_unsigned; lia.
Qed.

Lemma bits_signed_bitfield_extract:
  forall pos width n i,
  0 <= pos -> 0 < width -> pos + width <= zwordsize ->
  0 <= i < zwordsize ->
  testbit (signed_bitfield_extract pos width n) i =
  testbit n (if zlt i width then i + pos else width - 1 + pos).
Proof.
  intros. unfold signed_bitfield_extract. rewrite bits_sign_ext by lia.
  rewrite bits_shru, unsigned_repr, zlt_true.
  destruct (zlt i width); auto.
  destruct (zlt i width); lia.
  generalize wordsize_max_unsigned; lia.
  destruct (zlt i width); lia.
Qed.

Lemma bits_bitfield_insert:
  forall pos width n p i,
  0 <= pos -> 0 < width -> pos + width <= zwordsize ->
  0 <= i < zwordsize ->
  testbit (bitfield_insert pos width n p) i =
  if zle pos i && zlt i (pos + width) then testbit p (i - pos) else testbit n i.
Proof.
  intros. unfold bitfield_insert.
  assert (P: unsigned (repr pos) = pos).
  { apply unsigned_repr. generalize wordsize_max_unsigned; lia. }
  rewrite bits_or, bits_and, bits_not, ! bits_shl, ! P by auto.
  destruct (zlt i pos).
- unfold proj_sumbool; rewrite zle_false by lia. cbn. apply andb_true_r.
- unfold proj_sumbool; rewrite zle_true by lia; cbn.
  rewrite bits_zero_ext, testbit_repr, Ztestbit_two_p_m1 by lia.
  destruct (zlt (i - pos) width); cbn.
+ rewrite zlt_true by lia. rewrite andb_false_r, orb_false_r. auto.
+ rewrite zlt_false by lia. apply andb_true_r.
Qed.

Lemma unsigned_bitfield_extract_by_shifts:
  forall pos width n,
  0 <= pos -> 0 < width -> pos + width <= zwordsize ->
  unsigned_bitfield_extract pos width n =
  shru (shl n (repr (zwordsize - pos - width))) (repr (zwordsize - width)).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_unsigned_bitfield_extract by lia.
  rewrite bits_shru by auto.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  destruct (zlt i width).
- rewrite bits_shl by lia.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  rewrite zlt_true by lia. rewrite zlt_false by lia. f_equal; lia.
- rewrite zlt_false by lia. auto.
Qed.

Lemma signed_bitfield_extract_by_shifts:
  forall pos width n,
  0 <= pos -> 0 < width -> pos + width <= zwordsize ->
  signed_bitfield_extract pos width n =
  shr (shl n (repr (zwordsize - pos - width))) (repr (zwordsize - width)).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_signed_bitfield_extract by lia.
  rewrite bits_shr by auto.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  rewrite bits_shl.
  rewrite unsigned_repr by (generalize wordsize_max_unsigned; lia).
  symmetry. rewrite zlt_false. f_equal.
  destruct (zlt i width); [rewrite zlt_true | rewrite zlt_false]; lia.
  destruct zlt; lia.
  destruct zlt; lia.
Qed.

Lemma bitfield_insert_alternative:
  forall pos width n p,
  0 <= width ->
  bitfield_insert pos width n p =
  let mask := shl (repr (two_p width - 1)) (repr pos) in
  or (and (shl p (repr pos)) mask)
     (and n (not mask)).
Proof.
  intros. unfold bitfield_insert. 
  set (m1 := repr (two_p width - 1)).
  set (m2 := shl m1 (repr pos)).
  f_equal.
  rewrite zero_ext_and by lia. fold m1. unfold m2. rewrite <- and_shl. auto.
Qed.

Lemma unsigned_huge_two_p: forall x,
    (zwordsize <= x) ->
    unsigned (repr (2 ^ x)) = 0.
Proof.
  Local Transparent repr.
  unfold repr. cbn. intros.
  rewrite Z_mod_modulus_eq.
  unfold modulus.
  rewrite two_power_nat_two_p.
  rewrite two_p_equiv.
  fold zwordsize.
  replace (2 ^ x) with ((2 ^ (x - zwordsize)) * (2 ^ zwordsize)).
  { apply Z_mod_mult. }
  rewrite <- Z.pow_add_r.
  { f_equal. ring. }
  lia.
  pose proof wordsize_pos. lia.
Qed.

(** Connections between [shrx] and [shru] *)

Remark min_signed_wraps:
  signed (repr (2 ^ (zwordsize - 1))) = - (2 ^ (zwordsize - 1)).
Proof.
  unfold signed.
  assert (0 <= 2 ^ (zwordsize - 1) <= max_unsigned) as RANGE.
  { unfold max_unsigned, modulus.
    rewrite two_power_nat_two_p.
    rewrite two_p_equiv. fold zwordsize.
    replace zwordsize with ((zwordsize - 1) + 1) at 3 by ring.
    pose proof wordsize_pos.
    rewrite Z.pow_add_r by lia. change (2^1) with 2.
    split. { apply Z.pow_nonneg. lia. }
    lia.
  }
  rewrite unsigned_repr by assumption.
  rewrite half_modulus_power.
  rewrite two_p_equiv. fold zwordsize.
  destruct zlt. lia.
  rewrite modulus_power.
  rewrite two_p_equiv. fold zwordsize.
  replace zwordsize with ((zwordsize - 1) + 1) at 2 by ring.
  pose proof wordsize_pos.
  rewrite Z.pow_add_r by lia. change (2^1) with 2.
  lia.
Qed.

Lemma nonneg_shrx_is_shru:
  forall x (xRANGE : signed x >= 0) n,
    shrx x n = shru x n.
Proof.
  intros.
  pose proof (unsigned_range x) as xRANGE'.
  pose proof (unsigned_range n) as nRANGE'.
  unfold shrx, shru, shl, divs.
  rewrite unsigned_one.
  rewrite Zshiftr_div_two_p by lia.
  rewrite Zshiftl_mul_two_p by lia.
  rewrite Z.mul_1_l.
  rewrite nonneg_signed_is_unsigned by lia.
  destruct (zle (unsigned n) (zwordsize-2)) as [nRANGE | nRANGE].
  - assert (two_p (unsigned n) <= two_p (zwordsize-2)).
    { apply two_p_monotone. lia. }
    assert (two_p (unsigned n) > 0).
    { apply two_p_gt_ZERO. lia. }
    assert (0 <= two_p (unsigned n) <= max_signed) as TWO_P.
    { unfold max_signed, half_modulus, modulus.
      rewrite two_power_nat_two_p. fold zwordsize.
      replace (two_p zwordsize) with (two_p ((zwordsize - 2) + 2)); cycle 1.
      { f_equal. ring. }
      rewrite two_p_is_exp by lia.
      change (two_p 2) with 4.
      replace (two_p (zwordsize - 2) * 4) with ((two_p (zwordsize - 2) * 2) * 2) by ring.
      rewrite Z_div_mult by lia.
      lia. }
    pose proof max_signed_unsigned as MAX.
    rewrite signed_eq_unsigned; cycle 1.
    { rewrite unsigned_repr by lia. lia. }
    rewrite unsigned_repr by lia.
    f_equal.
    apply Zquot_Zdiv_pos; lia.
    
  - destruct (zeq (unsigned n) (zwordsize - 1)) as [EQ | GT].
    + rewrite EQ.
      rewrite two_p_equiv.
      rewrite min_signed_wraps.
      rewrite Zquot_opp_r by lia.
      rewrite Zquot_Zdiv_pos by lia.
      unfold signed in xRANGE.
      destruct zlt as [SMALL | BIG] in xRANGE. 2: lia.
      rewrite half_modulus_power in SMALL.
      rewrite two_p_equiv in SMALL.
      rewrite Zdiv_small by lia. reflexivity.
    + assert (unsigned n >= zwordsize) as BIG by lia.
      assert (two_p zwordsize <= two_p (unsigned n)) as HUGE.
      { apply two_p_monotone.
        pose proof wordsize_pos.
        lia. }
      rewrite two_p_equiv in HUGE.
      rewrite two_p_equiv in HUGE.
      rewrite Zdiv_small; cycle 1.
      { rewrite modulus_power in xRANGE'.
        rewrite two_p_equiv in xRANGE'.
        rewrite two_p_equiv.
        lia. } 
      unfold signed.
      rewrite two_p_equiv.
      rewrite unsigned_huge_two_p by lia.
      destruct zlt.
      { rewrite Zquot_0_r. reflexivity. }
      replace (0 - modulus) with (- modulus) by ring.
      rewrite Zquot_opp_r by lia.
      rewrite Zquot_Zdiv_pos by lia.
      rewrite Zdiv_small by lia.
      reflexivity.
Qed.

End Make.

(** * Specialization to integers of size 8, 32, and 64 bits *)

Module Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_32.

Strategy opaque [Wordsize_32.wordsize].

Module Int := Make(Wordsize_32).

Strategy 0 [Wordsize_32.wordsize].

Notation int := Int.int.

Remark int_wordsize_divides_modulus:
  Z.divide (Z.of_nat Int.wordsize) Int.modulus.
Proof.
  exists (two_p (32-5)); reflexivity.
Qed.

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_8.

Strategy opaque [Wordsize_8.wordsize].

Module Byte := Make(Wordsize_8).

Strategy 0 [Wordsize_8.wordsize].

Notation byte := Byte.int.

Module Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_64.

Strategy opaque [Wordsize_64.wordsize].

Module Int64.

Include Make(Wordsize_64).

(** Shifts with amount given as a 32-bit integer *)

Definition iwordsize': Int.int := Int.repr zwordsize.

Definition shl' (x: int) (y: Int.int): int :=
  repr (Z.shiftl (unsigned x) (Int.unsigned y)).
Definition shru' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (unsigned x) (Int.unsigned y)).
Definition shr' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (signed x) (Int.unsigned y)).
Definition rol' (x: int) (y: Int.int): int :=
  rol x (repr (Int.unsigned y)).
Definition ror' (x: int) (y: Int.int) :int :=
  ror x (repr (Int.unsigned y)).
Definition shrx' (x: int) (y: Int.int): int :=
  divs x (shl' one y).
Definition shr_carry' (x: int) (y: Int.int): int :=
  if lt x zero && negb (eq (and x (sub (shl' one y) one)) zero)
  then one else zero.

Lemma bits_shl':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl' x y) i =
  if zlt i (Int.unsigned y) then false else testbit x (i - Int.unsigned y).
Proof.
  intros. unfold shl'. rewrite testbit_repr; auto.
  destruct (zlt i (Int.unsigned y)).
  apply Z.shiftl_spec_low. auto.
  apply Z.shiftl_spec_high. lia. lia.
Qed.

Lemma bits_shru':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru' x y) i =
  if zlt (i + Int.unsigned y) zwordsize then testbit x (i + Int.unsigned y) else false.
Proof.
  intros. unfold shru'. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. fold (testbit x (i + Int.unsigned y)).
  destruct (zlt (i + Int.unsigned y) zwordsize).
  auto.
  apply bits_above; auto.
  lia.
Qed.

Lemma bits_shr':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr' x y) i =
  testbit x (if zlt (i + Int.unsigned y) zwordsize then i + Int.unsigned y else zwordsize - 1).
Proof.
  intros. unfold shr'. rewrite testbit_repr; auto.
  rewrite Z.shiftr_spec. apply bits_signed.
  generalize (Int.unsigned_range y); lia.
  lia.
Qed.

Remark int_unsigned_range:
  forall x, 0 <= Int.unsigned x <= max_unsigned.
Proof.
  intros.
  unfold max_unsigned. unfold modulus.
  generalize (Int.unsigned_range x).
  unfold Int.modulus in *.
  change (wordsize) with  64%nat in *.
  change (Int.wordsize) with 32%nat in *.
  unfold two_power_nat. simpl.
  lia.
Qed.

Remark int_unsigned_repr:
  forall x, unsigned (repr (Int.unsigned x)) = Int.unsigned x.
Proof.
  intros. rewrite unsigned_repr. auto.
  apply int_unsigned_range.
Qed.

Lemma bits_rol':
  forall x y i,
  0 <= i < zwordsize ->
  testbit (rol' x y) i = testbit x ((i - Int.unsigned y) mod zwordsize).
Proof.
  intros. unfold rol'. rewrite bits_rol; auto. rewrite int_unsigned_repr.
  auto.
Qed.

Lemma shl'_mul_two_p:
  forall x y,
  shl' x y = mul x (repr (two_p (Int.unsigned y))).
Proof.
  intros. unfold shl', mul. apply eqm_samerepr.
  rewrite Zshiftl_mul_two_p. apply eqm_mult. apply eqm_refl. apply eqm_unsigned_repr.
  generalize (Int.unsigned_range y); lia.
Qed.

Lemma shl'_one_two_p:
  forall y, shl' one y = repr (two_p (Int.unsigned y)).
Proof.
  intros. rewrite shl'_mul_two_p. rewrite mul_commut. rewrite mul_one. auto.
Qed.

Theorem shl'_mul:
  forall x y,
  shl' x y = mul x (shl' one y).
Proof.
  intros. rewrite shl'_one_two_p. apply shl'_mul_two_p.
Qed.

Theorem shl'_zero:
  forall x, shl' x Int.zero = x.
Proof.
  intros. unfold shl'. rewrite Int.unsigned_zero. unfold Z.shiftl.
  apply repr_unsigned.
Qed.

Theorem shru'_zero :
  forall x, shru' x Int.zero = x.
Proof.
  intros. unfold shru'. rewrite Int.unsigned_zero. unfold Z.shiftr.
  apply repr_unsigned.
Qed.

Theorem shr'_zero :
  forall x, shr' x Int.zero = x.
Proof.
  intros. unfold shr'. rewrite Int.unsigned_zero. unfold Z.shiftr.
  apply repr_signed.
Qed.

Theorem shrx'_zero:
  forall x, shrx' x Int.zero = x.
Proof.
  intros. change (shrx' x Int.zero) with (shrx x zero). apply shrx_zero. compute; auto.
Qed.

Theorem shrx'_carry:
  forall x y,
  Int.ltu y (Int.repr 63) = true ->
  shrx' x y = add (shr' x y) (shr_carry' x y).
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 63)) with 63 in H.
  set (y1 := Int64.repr (Int.unsigned y)).
  assert (U: unsigned y1 = Int.unsigned y).
  { apply unsigned_repr. assert (63 < max_unsigned) by reflexivity. lia. }
  transitivity (shrx x y1).
- unfold shrx', shrx, shl', shl. rewrite U; auto.
- rewrite shrx_carry. 
+ f_equal. 
  unfold shr, shr'. rewrite U; auto.
  unfold shr_carry, shr_carry', shl, shl'. rewrite U; auto.
+ unfold ltu. apply zlt_true. rewrite U; tauto. 
Qed.

Theorem shrx'_shr_2:
  forall x y,
  Int.ltu y (Int.repr 63) = true ->
  shrx' x y = shr' (add x (shru' (shr' x (Int.repr 63)) (Int.sub (Int.repr 64) y))) y.
Proof.
  intros.
  set (z := repr (Int.unsigned y)).
  apply Int.ltu_inv in H. change (Int.unsigned (Int.repr 63)) with 63 in H.
  assert (N1: 63 < max_unsigned) by reflexivity.
  assert (N2: 63 < Int.max_unsigned) by reflexivity.
  assert (A: unsigned z = Int.unsigned y).
  { unfold z; apply unsigned_repr; lia. }
  assert (B: unsigned (sub (repr 64) z) = Int.unsigned (Int.sub (Int.repr 64) y)).
  { unfold z. unfold sub, Int.sub.
    change (unsigned (repr 64)) with 64.
    change (Int.unsigned (Int.repr 64)) with 64.
    rewrite (unsigned_repr (Int.unsigned y)) by lia.
    rewrite unsigned_repr, Int.unsigned_repr by lia.
    auto. }
  unfold shrx', shr', shru', shl'.
  rewrite <- A.
  change (Int.unsigned (Int.repr 63)) with (unsigned (repr 63)).
  rewrite <- B.
  apply shrx_shr_2.
  unfold ltu. apply zlt_true. change (unsigned z < 63). rewrite A; lia.
Qed.

Lemma shr'63:
  forall x, (shr' x (Int.repr 63)) = if lt x zero then mone else zero.
Proof.
  intro.
  unfold shr', mone, zero.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  apply same_bits_eq.
  intros i BIT.
  rewrite testbit_repr by assumption.
  rewrite Z.shiftr_spec by lia.
  rewrite bits_signed by lia.
  simpl.
  change zwordsize with 64 in *.
  destruct (zlt _ _) as [LT | GE].
  {
    replace i with 0 in * by lia.
    change (0 + 63) with (zwordsize - 1).
    rewrite  sign_bit_of_signed.
    destruct (lt x _).
    all: rewrite testbit_repr by (change zwordsize with 64 in *; lia).
    all: simpl; reflexivity.
  }
  change (64 - 1) with (zwordsize - 1).
  rewrite  sign_bit_of_signed.
  destruct (lt x _).
  all: rewrite testbit_repr by (change zwordsize with 64 in *; lia).
  { symmetry.
    apply Ztestbit_m1.
    tauto.
  }
  symmetry.
  apply Ztestbit_0.
Qed.

Lemma shru'63:
  forall x, (shru' x (Int.repr 63)) = if lt x zero then one else zero.
Proof.
  intro.
  unfold shru'.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  apply same_bits_eq.
  intros i BIT.
  rewrite testbit_repr by assumption.
  rewrite Z.shiftr_spec by lia.
  unfold lt.
  rewrite signed_zero.
  unfold one, zero.
  destruct (zlt _ 0) as [LT | GE].
  {
    rewrite testbit_repr by assumption.
    destruct (zeq i 0) as [IZERO | INONZERO].
    { subst i.
      change (Z.testbit (unsigned x) (0 + 63)) with (testbit x (zwordsize - 1)).
      rewrite sign_bit_of_signed.
      unfold lt.
      rewrite signed_zero.
      destruct (zlt _ _); try lia.
      reflexivity.
    }
    change (Z.testbit (unsigned x) (i + 63)) with (testbit x (i+63)).
    rewrite bits_above by (change zwordsize with 64; lia).
    rewrite Ztestbit_1.
    destruct (zeq i 0); trivial.
    subst i.
    lia.
  }
  destruct (zeq i 0) as [IZERO | INONZERO].
  { subst i.
    change (Z.testbit (unsigned x) (0 + 63)) with (testbit x (zwordsize - 1)).
    rewrite sign_bit_of_signed.
    unfold lt.
    rewrite signed_zero.
    rewrite bits_zero.
    destruct (zlt _ _); try lia; reflexivity.
  }
  change (Z.testbit (unsigned x) (i + 63)) with (testbit x (i + 63)).
  rewrite bits_zero.
  apply bits_above.
  change zwordsize with 64.
  lia.
Qed.
  
Theorem shrx'1_shr':
  forall x,
  Int.ltu Int.one (Int.repr (zwordsize - 1)) = true ->
  shrx' x (Int.repr 1) = shr' (add x (shru' x (Int.repr (Int64.zwordsize - 1)))) (Int.repr 1).
Proof.
  intros.
  rewrite shrx'_shr_2 by reflexivity.
  change (Int.sub (Int.repr 64) (Int.repr 1)) with (Int.repr 63).
  f_equal. f_equal.
  rewrite shr'63.
  rewrite shru'63.
  rewrite shru'63.
  destruct (lt x zero); reflexivity.
Qed.  

Remark int_ltu_2_inv:
  forall y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.unsigned (Int.add y z) <= Int.unsigned iwordsize' ->
  let y' := repr (Int.unsigned y) in
  let z' := repr (Int.unsigned z) in
     Int.unsigned y = unsigned y'
  /\ Int.unsigned z = unsigned z'
  /\ ltu y' iwordsize = true
  /\ ltu z' iwordsize = true
  /\ Int.unsigned (Int.add y z) = unsigned (add y' z')
  /\ add y' z' = repr (Int.unsigned (Int.add y z)).
Proof.
  intros. apply Int.ltu_inv in H. apply Int.ltu_inv in H0.
  change (Int.unsigned iwordsize') with 64 in *.
  assert (128 < max_unsigned) by reflexivity.
  assert (128 < Int.max_unsigned) by reflexivity.
  assert (Y: unsigned y' = Int.unsigned y) by (apply unsigned_repr; lia).
  assert (Z: unsigned z' = Int.unsigned z) by (apply unsigned_repr; lia).
  assert (P: Int.unsigned (Int.add y z) = unsigned (add y' z')).
  { unfold Int.add. rewrite Int.unsigned_repr by lia.
    unfold add. rewrite unsigned_repr by lia. congruence. }
  intuition auto.
  apply zlt_true. rewrite Y; auto.
  apply zlt_true. rewrite Z; auto.
  rewrite P. rewrite repr_unsigned. auto.
Qed.

Theorem or_ror':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.add y z = iwordsize' ->
  ror x (repr (Int.unsigned z)) = or (shl' x y) (shru' x z).
Proof.
  intros. destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. rewrite H1; lia.
  replace (shl' x y) with (shl x (repr (Int.unsigned y))).
  replace (shru' x z) with (shru x (repr (Int.unsigned z))).
  apply or_ror; auto. rewrite F, H1. reflexivity.
  unfold shru, shru'; rewrite <- B; auto.
  unfold shl, shl'; rewrite <- A; auto.
Qed.

Theorem shl'_shl':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shl' (shl' x y) z = shl' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. lia.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shl' x y) with (shl x y').
  replace (shl' (shl x y') z) with (shl (shl x y') z').
  replace (shl' x (Int.add y z)) with (shl x (add y' z')).
  apply shl_shl; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shl, shl'. rewrite E; auto.
  unfold shl at 1, shl'. rewrite <- B; auto.
  unfold shl, shl'; rewrite <- A; auto.
Qed.

Theorem shru'_shru':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shru' (shru' x y) z = shru' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. lia.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shru' x y) with (shru x y').
  replace (shru' (shru x y') z) with (shru (shru x y') z').
  replace (shru' x (Int.add y z)) with (shru x (add y' z')).
  apply shru_shru; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shru, shru'. rewrite E; auto.
  unfold shru at 1, shru'. rewrite <- B; auto.
  unfold shru, shru'; rewrite <- A; auto.
Qed.

Theorem shr'_shr':
  forall x y z,
  Int.ltu y iwordsize' = true ->
  Int.ltu z iwordsize' = true ->
  Int.ltu (Int.add y z) iwordsize' = true ->
  shr' (shr' x y) z = shr' x (Int.add y z).
Proof.
  intros. apply Int.ltu_inv in H1.
  destruct (int_ltu_2_inv y z) as (A & B & C & D & E & F); auto. lia.
  set (y' := repr (Int.unsigned y)) in *.
  set (z' := repr (Int.unsigned z)) in *.
  replace (shr' x y) with (shr x y').
  replace (shr' (shr x y') z) with (shr (shr x y') z').
  replace (shr' x (Int.add y z)) with (shr x (add y' z')).
  apply shr_shr; auto. apply zlt_true. rewrite <- E.
  change (unsigned iwordsize) with zwordsize. tauto.
  unfold shr, shr'. rewrite E; auto.
  unfold shr at 1, shr'. rewrite <- B; auto.
  unfold shr, shr'; rewrite <- A; auto.
Qed.

Theorem shru'_shl':
  forall x y z, Int.ltu y iwordsize' = true -> Int.ltu z iwordsize' = true ->
  shru' (shl' x y) z =
  if Int.ltu z y then shl' (zero_ext (zwordsize - Int.unsigned y) x) (Int.sub y z)
                 else zero_ext (zwordsize - Int.unsigned z) (shru' x (Int.sub z y)).
Proof.
  intros. apply Int.ltu_inv in H; apply Int.ltu_inv in H0.
  change (Int.unsigned iwordsize') with zwordsize in *.
  unfold Int.ltu. set (Y := Int.unsigned y) in *; set (Z := Int.unsigned z) in *.
  apply same_bits_eq; intros. rewrite bits_shru' by auto. fold Z.
  destruct (zlt Z Y).
- assert (A: Int.unsigned (Int.sub y z) = Y - Z).
  { apply Int.unsigned_repr. assert (zwordsize < Int.max_unsigned) by reflexivity. lia. }
  symmetry; rewrite bits_shl', A by lia.
  destruct (zlt (i + Z) zwordsize).
+ rewrite bits_shl' by lia. fold Y.
  destruct (zlt i (Y - Z)); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
  rewrite bits_zero_ext by lia. rewrite zlt_true by lia. f_equal; lia.
+ rewrite bits_zero_ext by lia. rewrite ! zlt_false by lia. auto.
- assert (A: Int.unsigned (Int.sub z y) = Z - Y).
  { apply Int.unsigned_repr. assert (zwordsize < Int.max_unsigned) by reflexivity. lia. }
  rewrite bits_zero_ext, bits_shru', A by lia.
  destruct (zlt (i + Z) zwordsize); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
  rewrite bits_shl' by lia. fold Y.
  destruct (zlt (i + Z) Y).
+ rewrite zlt_false by lia. auto.
+ rewrite zlt_true by lia. f_equal; lia.
Qed.

Theorem shr'_shl':
  forall x y z, Int.ltu y iwordsize' = true -> Int.ltu z iwordsize' = true ->
  shr' (shl' x y) z =
  if Int.ltu z y then shl' (sign_ext (zwordsize - Int.unsigned y) x) (Int.sub y z)
                 else sign_ext (zwordsize - Int.unsigned z) (shr' x (Int.sub z y)).
Proof.
  intros. apply Int.ltu_inv in H; apply Int.ltu_inv in H0.
  change (Int.unsigned iwordsize') with zwordsize in *.
  unfold Int.ltu. set (Y := Int.unsigned y) in *; set (Z := Int.unsigned z) in *.
  apply same_bits_eq; intros. rewrite bits_shr' by auto. fold Z.
  rewrite bits_shl' by (destruct (zlt (i + Z) zwordsize); lia). fold Y.
  destruct (zlt Z Y).
- assert (A: Int.unsigned (Int.sub y z) = Y - Z).
  { apply Int.unsigned_repr. assert (zwordsize < Int.max_unsigned) by reflexivity. lia. }
  rewrite bits_shl', A by lia.
  destruct (zlt i (Y - Z)).
+ apply zlt_true. destruct (zlt (i + Z) zwordsize); lia.
+ rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  rewrite bits_sign_ext by lia. f_equal. 
  destruct (zlt (i + Z) zwordsize).
  rewrite zlt_true by lia. lia.
  rewrite zlt_false by lia. lia.
- assert (A: Int.unsigned (Int.sub z y) = Z - Y).
  { apply Int.unsigned_repr. assert (zwordsize < Int.max_unsigned) by reflexivity. lia. }
  rewrite bits_sign_ext by lia.
  rewrite bits_shr' by (destruct (zlt i (zwordsize - Z)); lia).
  rewrite A. rewrite zlt_false by (destruct (zlt (i + Z) zwordsize); lia).
  f_equal. destruct (zlt i (zwordsize - Z)).
+ rewrite ! zlt_true by lia. lia.
+ rewrite ! zlt_false by lia. rewrite zlt_true by lia. lia.
Qed.

Lemma shl'_zero_ext:
  forall n m x, 0 <= n ->
  shl' (zero_ext n x) m = zero_ext (n + Int.unsigned m) (shl' x m).
Proof.
  intros. apply same_bits_eq; intros.
  rewrite bits_zero_ext, ! bits_shl' by lia.
  destruct (zlt i (Int.unsigned m)).
- rewrite zlt_true by lia; auto.
- rewrite bits_zero_ext by lia.
  destruct (zlt (i - Int.unsigned m) n); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
Qed.

Lemma shl'_sign_ext:
  forall n m x, 0 < n ->
  shl' (sign_ext n x) m = sign_ext (n + Int.unsigned m) (shl' x m).
Proof.
  intros. generalize (Int.unsigned_range m); intros.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext, ! bits_shl' by lia.
  destruct (zlt i (n + Int.unsigned m)).
- rewrite bits_shl' by auto. destruct (zlt i (Int.unsigned m)); auto.
  rewrite bits_sign_ext by lia. f_equal. apply zlt_true. lia.
- rewrite zlt_false by lia. rewrite bits_shl' by lia. rewrite zlt_false by lia.
  rewrite bits_sign_ext by lia. f_equal. rewrite zlt_false by lia. lia.
Qed.

Lemma shru'_zero_ext:
  forall n m x, 0 <= n ->
  shru' (zero_ext (n + Int.unsigned m) x) m = zero_ext n (shru' x m).
Proof.
  intros. generalize (Int.unsigned_range m); intros.
  bit_solve; [|lia]. rewrite bits_shru', bits_zero_ext, bits_shru' by lia.
  destruct (zlt (i + Int.unsigned m) zwordsize).
* destruct (zlt i n); [rewrite zlt_true by lia|rewrite zlt_false by lia]; auto.
* destruct (zlt i n); auto.
Qed.

Lemma shru'_zero_ext_0:
  forall n m x, n <= Int.unsigned m ->
  shru' (zero_ext n x) m = zero.
Proof.
  intros. generalize (Int.unsigned_range m); intros.
  bit_solve. rewrite bits_shru', bits_zero_ext by lia.
  destruct (zlt (i + Int.unsigned m) zwordsize); auto.
  apply zlt_false. lia.
Qed.

Lemma shr'_sign_ext:
  forall n m x, 0 < n -> n + Int.unsigned m < zwordsize ->
  shr' (sign_ext (n + Int.unsigned m) x) m = sign_ext n (shr' x m).
Proof.
  intros. generalize (Int.unsigned_range m); intros.
  apply same_bits_eq; intros.
  rewrite bits_sign_ext, bits_shr' by auto.
  rewrite bits_sign_ext, bits_shr'.
- f_equal.
  destruct (zlt i n), (zlt (i + Int.unsigned m) zwordsize).
+ apply zlt_true; lia.
+ apply zlt_true; lia.
+ rewrite zlt_false by lia. rewrite zlt_true by lia. lia.
+ rewrite zlt_false by lia. rewrite zlt_true by lia. lia.
- destruct (zlt i n); lia.
- destruct (zlt (i + Int.unsigned m) zwordsize); lia.
Qed.

Lemma zero_ext_shru'_min:
  forall s x n, Int.ltu n iwordsize' = true ->
  zero_ext s (shru' x n) = zero_ext (Z.min s (zwordsize - Int.unsigned n)) (shru' x n).
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned iwordsize') with zwordsize in H.
  apply Z.min_case_strong; intros; auto.
  bit_solve; try lia. rewrite ! bits_shru' by lia. 
  destruct (zlt i (zwordsize - Int.unsigned n)).
  rewrite zlt_true by lia. auto.
  destruct (zlt i s); auto. rewrite zlt_false by lia; auto.
Qed.

Lemma sign_ext_shr'_min:
  forall s x n, Int.ltu n iwordsize' = true ->
  sign_ext s (shr' x n) = sign_ext (Z.min s (zwordsize - Int.unsigned n)) (shr' x n).
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned iwordsize') with zwordsize in H.
  rewrite Z.min_comm. 
  destruct (Z.min_spec (zwordsize - Int.unsigned n) s) as [[A B] | [A B]]; rewrite B; auto.
  apply same_bits_eq; intros. rewrite ! bits_sign_ext by auto.
  destruct (zlt i (zwordsize - Int.unsigned n)). 
  rewrite zlt_true by lia. auto.
  assert (C: testbit (shr' x n) (zwordsize - Int.unsigned n - 1) = testbit x (zwordsize - 1)).
  { rewrite bits_shr' by lia. rewrite zlt_true by lia. f_equal; lia. }
  rewrite C. destruct (zlt i s); rewrite bits_shr' by lia.
  rewrite zlt_false by lia. auto.
  rewrite zlt_false by lia. auto.
Qed.

Lemma shl'_zero_ext_min:
  forall s x n, Int.ltu n iwordsize' = true ->
  shl' (zero_ext s x) n = shl' (zero_ext (Z.min s (zwordsize - Int.unsigned n)) x) n.
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned iwordsize') with zwordsize in H.
  apply Z.min_case_strong; intros; auto.
  apply same_bits_eq; intros. rewrite ! bits_shl' by auto.
  destruct (zlt i (Int.unsigned n)); auto.
  rewrite ! bits_zero_ext by lia.
  destruct (zlt (i - Int.unsigned n) s).
  rewrite zlt_true by lia; auto.
  rewrite zlt_false by lia; auto.
Qed.

Lemma shl'_sign_ext_min:
  forall s x n, Int.ltu n iwordsize' = true ->
  shl' (sign_ext s x) n = shl' (sign_ext (Z.min s (zwordsize - Int.unsigned n)) x) n.
Proof.
  intros. apply Int.ltu_inv in H. change (Int.unsigned iwordsize') with zwordsize in H.
  rewrite Z.min_comm. 
  destruct (Z.min_spec (zwordsize - Int.unsigned n) s) as [[A B] | [A B]]; rewrite B; auto.
  apply same_bits_eq; intros. rewrite ! bits_shl' by auto.
  destruct (zlt i (Int.unsigned n)); auto.
  rewrite ! bits_sign_ext by lia. f_equal.
  destruct (zlt (i - Int.unsigned n) s).
  rewrite zlt_true by lia; auto.
  extlia.
Qed.

(** Connections between [shrx'] and [shru'] *)

Lemma nonneg_shrx'_is_shru':
  forall x (xRANGE : signed x >= 0) n,
    shrx' x n = shru' x n.
Proof.
  intros.
  pose proof (unsigned_range x) as xRANGE'.
  pose proof (Int.unsigned_range n) as nRANGE'.
  unfold shrx', shru', shl', divs.
  rewrite unsigned_one.
  rewrite Zshiftr_div_two_p by lia.
  rewrite Zshiftl_mul_two_p by lia.
  rewrite Z.mul_1_l.
  rewrite nonneg_signed_is_unsigned by lia.
  destruct (zle (Int.unsigned n) 62) as [nRANGE | nRANGE].
  - assert (two_p (Int.unsigned n) <= two_p 62).
    { apply two_p_monotone. lia. }
    change (two_p 62) with 4611686018427387904 in *.
    assert (two_p (Int.unsigned n) > 0).
    { apply two_p_gt_ZERO. lia. }
    rewrite signed_eq_unsigned; cycle 1.
    { rewrite unsigned_repr.
      { change max_signed with 9223372036854775807.
        lia.
      }
      change max_unsigned with 18446744073709551615.
      lia.
    }
    rewrite unsigned_repr; cycle 1.
    { change max_unsigned with 18446744073709551615.
      lia. }
    f_equal.
    apply Zquot_Zdiv_pos; lia.
  - destruct (zeq (Int.unsigned n) 63) as [EQ | GT].
    + rewrite EQ.
      rewrite two_p_equiv.
      change (signed (repr (2 ^ 63))) with (- (2 ^ 63)).
      rewrite Zquot_opp_r by lia.
      rewrite Zquot_Zdiv_pos by lia.
      unfold signed in xRANGE.
      destruct zlt as [SMALL | BIG] in xRANGE. 2: lia.
      change half_modulus with (2^63) in SMALL.
      rewrite Zdiv_small by lia. reflexivity.
    + assert (Int.unsigned n >= 64) as BIG by lia.
      assert (two_p 64 <= two_p (Int.unsigned n)) as HUGE.
      { apply two_p_monotone. lia. }
      rewrite two_p_equiv in HUGE.
      rewrite two_p_equiv in HUGE.
      rewrite two_p_equiv.
      change modulus with (2^64) in *.
      rewrite Zdiv_small by lia.
      unfold signed.
      rewrite unsigned_huge_two_p by (change zwordsize with 64; lia).
      destruct zlt.
      { rewrite Zquot_0_r. reflexivity. }
      change half_modulus with 9223372036854775808 in *.
      lia.
Qed.

(** Powers of two with exponents given as 32-bit ints *)

Definition one_bits' (x: int) : list Int.int :=
  List.map Int.repr (Z_one_bits wordsize (unsigned x) 0).

Definition is_power2' (x: int) : option Int.int :=
  match Z_one_bits wordsize (unsigned x) 0 with
  | i :: nil => Some (Int.repr i)
  | _ => None
  end.

Theorem one_bits'_range:
  forall x i, In i (one_bits' x) -> Int.ltu i iwordsize' = true.
Proof.
  intros.
  destruct (list_in_map_inv _ _ _ H) as [i0 [EQ IN]].
  exploit Z_one_bits_range; eauto. fold zwordsize. intros R.
  unfold Int.ltu. rewrite EQ. rewrite Int.unsigned_repr.
  change (Int.unsigned iwordsize') with zwordsize. apply zlt_true. lia.
  assert (zwordsize < Int.max_unsigned) by reflexivity. lia.
Qed.

Fixpoint int_of_one_bits' (l: list Int.int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl' one a) (int_of_one_bits' b)
  end.

Theorem one_bits'_decomp:
  forall x, x = int_of_one_bits' (one_bits' x).
Proof.
  assert (REC: forall l,
           (forall i, In i l -> 0 <= i < zwordsize) ->
           int_of_one_bits' (List.map Int.repr l) = repr (powerserie l)).
  { induction l; simpl; intros.
  - auto.
  - rewrite IHl by eauto. apply eqm_samerepr; apply eqm_add.
  + rewrite shl'_one_two_p. rewrite Int.unsigned_repr. apply eqm_sym; apply eqm_unsigned_repr.
    exploit (H a). auto. assert (zwordsize < Int.max_unsigned) by reflexivity. lia.
  + apply eqm_sym; apply eqm_unsigned_repr.
  }
  intros. rewrite <- (repr_unsigned x) at 1. unfold one_bits'. rewrite REC.
  rewrite <- Z_one_bits_powerserie. auto. apply unsigned_range.
  apply Z_one_bits_range.
Qed.

Lemma is_power2'_rng:
  forall n logn,
  is_power2' n = Some logn ->
  0 <= Int.unsigned logn < zwordsize.
Proof.
  unfold is_power2'; intros n logn P2.
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv P2.
  assert (0 <= i < zwordsize).
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  rewrite Int.unsigned_repr. auto.
  assert (zwordsize < Int.max_unsigned) by reflexivity.
  lia.
Qed.

Theorem is_power2'_range:
  forall n logn,
  is_power2' n = Some logn -> Int.ltu logn iwordsize' = true.
Proof.
  intros. unfold Int.ltu. change (Int.unsigned iwordsize') with zwordsize.
  apply zlt_true. generalize (is_power2'_rng _ _ H). tauto.
Qed.

Lemma is_power2'_correct:
  forall n logn,
  is_power2' n = Some logn ->
  unsigned n = two_p (Int.unsigned logn).
Proof.
  unfold is_power2'; intros.
  destruct (Z_one_bits wordsize (unsigned n) 0) as [ | i [ | ? ?]] eqn:B; inv H.
  rewrite (Z_one_bits_powerserie wordsize (unsigned n)) by (apply unsigned_range).
  rewrite Int.unsigned_repr. rewrite B; simpl. lia.
  assert (0 <= i < zwordsize).
  { apply Z_one_bits_range with (unsigned n). rewrite B; auto with coqlib. }
  assert (zwordsize < Int.max_unsigned) by reflexivity.
  lia.
Qed.

Theorem mul_pow2':
  forall x n logn,
  is_power2' n = Some logn ->
  mul x n = shl' x logn.
Proof.
  intros. rewrite shl'_mul. f_equal. rewrite shl'_one_two_p.
  rewrite <- (repr_unsigned n). f_equal. apply is_power2'_correct; auto.
Qed.

Theorem divu_pow2':
  forall x n logn,
  is_power2' n = Some logn ->
  divu x n = shru' x logn.
Proof.
  intros. generalize (is_power2'_correct n logn H). intro.
  symmetry. unfold divu. rewrite H0. unfold shru'. rewrite Zshiftr_div_two_p. auto.
  eapply is_power2'_rng; eauto.
Qed.

(** Decomposing 64-bit ints as pairs of 32-bit ints *)

Definition loword (n: int) : Int.int := Int.repr (unsigned n).

Definition hiword (n: int) : Int.int := Int.repr (unsigned (shru n (repr Int.zwordsize))).

Definition ofwords (hi lo: Int.int) : int :=
  or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize)) (repr (Int.unsigned lo)).

Lemma bits_loword:
  forall n i, 0 <= i < Int.zwordsize -> Int.testbit (loword n) i = testbit n i.
Proof.
  intros. unfold loword. rewrite Int.testbit_repr; auto.
Qed.

Lemma bits_hiword:
  forall n i, 0 <= i < Int.zwordsize -> Int.testbit (hiword n) i = testbit n (i + Int.zwordsize).
Proof.
  intros. unfold hiword. rewrite Int.testbit_repr; auto.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  fold (testbit (shru n (repr Int.zwordsize)) i). rewrite bits_shru.
  change (unsigned (repr Int.zwordsize)) with Int.zwordsize.
  apply zlt_true. lia. lia.
Qed.

Lemma bits_ofwords:
  forall hi lo i, 0 <= i < zwordsize ->
  testbit (ofwords hi lo) i =
  if zlt i Int.zwordsize then Int.testbit lo i else Int.testbit hi (i - Int.zwordsize).
Proof.
  intros. unfold ofwords. rewrite bits_or; auto. rewrite bits_shl; auto.
  change (unsigned (repr Int.zwordsize)) with Int.zwordsize.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  destruct (zlt i Int.zwordsize).
  rewrite testbit_repr; auto.
  rewrite !testbit_repr; auto.
  fold (Int.testbit lo i). rewrite Int.bits_above. apply orb_false_r. auto.
  lia.
Qed.

Lemma lo_ofwords:
  forall hi lo, loword (ofwords hi lo) = lo.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite bits_loword; auto. rewrite bits_ofwords. apply zlt_true. lia.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. lia.
Qed.

Lemma hi_ofwords:
  forall hi lo, hiword (ofwords hi lo) = hi.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite bits_hiword; auto. rewrite bits_ofwords.
  rewrite zlt_false. f_equal. lia. lia.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. lia.
Qed.

Lemma ofwords_recompose:
  forall n, ofwords (hiword n) (loword n) = n.
Proof.
  intros. apply same_bits_eq; intros. rewrite bits_ofwords; auto.
  destruct (zlt i Int.zwordsize).
  apply bits_loword. lia.
  rewrite bits_hiword. f_equal. lia.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity. lia.
Qed.

Lemma ofwords_add:
  forall lo hi, ofwords hi lo = repr (Int.unsigned hi * two_p 32 + Int.unsigned lo).
Proof.
  intros. unfold ofwords. rewrite shifted_or_is_add.
  apply eqm_samerepr. apply eqm_add. apply eqm_mult.
  apply eqm_sym; apply eqm_unsigned_repr.
  apply eqm_refl.
  apply eqm_sym; apply eqm_unsigned_repr.
  change Int.zwordsize with 32; change zwordsize with 64; lia.
  rewrite unsigned_repr. generalize (Int.unsigned_range lo). intros [A B]. exact B.
  assert (Int.max_unsigned < max_unsigned) by (compute; auto).
  generalize (Int.unsigned_range_2 lo); lia.
Qed.

Lemma ofwords_add':
  forall lo hi, unsigned (ofwords hi lo) = Int.unsigned hi * two_p 32 + Int.unsigned lo.
Proof.
  intros. rewrite ofwords_add. apply unsigned_repr.
  generalize (Int.unsigned_range hi) (Int.unsigned_range lo).
  change (two_p 32) with Int.modulus.
  change Int.modulus with 4294967296.
  change max_unsigned with 18446744073709551615.
  lia.
Qed.

Remark eqm_mul_2p32:
  forall x y, Int.eqm x y -> eqm (x * two_p 32) (y * two_p 32).
Proof.
  intros. destruct H as [k EQ]. exists k. rewrite EQ.
  change Int.modulus with (two_p 32).
  change modulus with (two_p 32 * two_p 32).
  ring.
Qed.

Lemma ofwords_add'':
  forall lo hi, signed (ofwords hi lo) = Int.signed hi * two_p 32 + Int.unsigned lo.
Proof.
  intros. rewrite ofwords_add.
  replace (repr (Int.unsigned hi * two_p 32 + Int.unsigned lo))
     with (repr (Int.signed hi * two_p 32 + Int.unsigned lo)).
  apply signed_repr.
  generalize (Int.signed_range hi) (Int.unsigned_range lo).
  change (two_p 32) with Int.modulus.
  change min_signed with (Int.min_signed * Int.modulus).
  change max_signed with (Int.max_signed * Int.modulus + Int.modulus - 1).
  change Int.modulus with 4294967296.
  lia.
  apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. apply Int.eqm_signed_unsigned. apply eqm_refl.
Qed.

(** Expressing 64-bit operations in terms of 32-bit operations *)

Lemma decompose_bitwise_binop:
  forall f f64 f32 xh xl yh yl,
  (forall x y i, 0 <= i < zwordsize -> testbit (f64 x y) i = f (testbit x i) (testbit y i)) ->
  (forall x y i, 0 <= i < Int.zwordsize -> Int.testbit (f32 x y) i = f (Int.testbit x i) (Int.testbit y i)) ->
  f64 (ofwords xh xl) (ofwords yh yl) = ofwords (f32 xh yh) (f32 xl yl).
Proof.
  intros. apply Int64.same_bits_eq; intros.
  rewrite H by auto. rewrite ! bits_ofwords by auto.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  destruct (zlt i Int.zwordsize); rewrite H0 by lia; auto.
Qed.

Lemma decompose_and:
  forall xh xl yh yl,
  and (ofwords xh xl) (ofwords yh yl) = ofwords (Int.and xh yh) (Int.and xl yl).
Proof.
  intros. apply decompose_bitwise_binop with andb.
  apply bits_and. apply Int.bits_and.
Qed.

Lemma decompose_or:
  forall xh xl yh yl,
  or (ofwords xh xl) (ofwords yh yl) = ofwords (Int.or xh yh) (Int.or xl yl).
Proof.
  intros. apply decompose_bitwise_binop with orb.
  apply bits_or. apply Int.bits_or.
Qed.

Lemma decompose_xor:
  forall xh xl yh yl,
  xor (ofwords xh xl) (ofwords yh yl) = ofwords (Int.xor xh yh) (Int.xor xl yl).
Proof.
  intros. apply decompose_bitwise_binop with xorb.
  apply bits_xor. apply Int.bits_xor.
Qed.

Lemma decompose_not:
  forall xh xl,
  not (ofwords xh xl) = ofwords (Int.not xh) (Int.not xl).
Proof.
  intros. unfold not, Int.not. rewrite <- decompose_xor. f_equal.
  apply (Int64.eq_spec mone (ofwords Int.mone Int.mone)).
Qed.

Lemma decompose_shl_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shl' (ofwords xh xl) y =
  ofwords (Int.or (Int.shl xh y) (Int.shru xl (Int.sub Int.iwordsize y)))
          (Int.shl xl y).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; lia. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize). rewrite Int.bits_shl by lia.
  destruct (zlt i (Int.unsigned y)). auto.
  rewrite bits_ofwords by lia. rewrite zlt_true by lia. auto.
  rewrite zlt_false by lia. rewrite bits_ofwords by lia.
  rewrite Int.bits_or by lia. rewrite Int.bits_shl by lia.
  rewrite Int.bits_shru by lia. rewrite H0.
  destruct (zlt (i - Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by lia. rewrite zlt_true by lia.
  rewrite orb_false_l. f_equal. lia.
  rewrite zlt_false by lia. rewrite zlt_false by lia.
  rewrite orb_false_r. f_equal. lia.
Qed.

Lemma decompose_shl_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shl' (ofwords xh xl) y =
  ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero.
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). lia. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shl' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize). rewrite zlt_true by lia. apply Int.bits_zero.
  rewrite Int.bits_shl by lia.
  destruct (zlt i (Int.unsigned y)).
  rewrite zlt_true by lia. auto.
  rewrite zlt_false by lia.
  rewrite bits_ofwords by lia. rewrite zlt_true by lia. f_equal. lia.
Qed.

Lemma decompose_shru_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shru' (ofwords xh xl) y =
  ofwords (Int.shru xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; lia. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite zlt_true by lia.
  rewrite bits_ofwords by lia.
  rewrite Int.bits_or by lia. rewrite Int.bits_shl by lia.
  rewrite Int.bits_shru by lia. rewrite H0.
  destruct (zlt (i + Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by lia.
  rewrite orb_false_r. auto.
  rewrite zlt_false by lia.
  rewrite orb_false_l. f_equal. lia.
  rewrite Int.bits_shru by lia.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite bits_ofwords by lia.
  rewrite zlt_true by lia. rewrite zlt_false by lia. f_equal. lia.
  rewrite zlt_false by lia. auto.
Qed.

Lemma decompose_shru_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shru' (ofwords xh xl) y =
  ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize)).
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). lia. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shru' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite Int.bits_shru by lia. rewrite H1.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite zlt_true by lia. rewrite bits_ofwords by lia.
  rewrite zlt_false by lia. f_equal; lia.
  rewrite zlt_false by lia. auto.
  rewrite zlt_false by lia. apply Int.bits_zero.
Qed.

Lemma decompose_shr_1:
  forall xh xl y,
  0 <= Int.unsigned y < Int.zwordsize ->
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh y)
          (Int.or (Int.shru xl y) (Int.shl xh (Int.sub Int.iwordsize y))).
Proof.
  intros.
  assert (Int.unsigned (Int.sub Int.iwordsize y) = Int.zwordsize - Int.unsigned y).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize Int.wordsize_max_unsigned; lia. }
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  apply Int64.same_bits_eq; intros.
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite zlt_true by lia.
  rewrite bits_ofwords by lia.
  rewrite Int.bits_or by lia. rewrite Int.bits_shl by lia.
  rewrite Int.bits_shru by lia. rewrite H0.
  destruct (zlt (i + Int.unsigned y) (Int.zwordsize)).
  rewrite zlt_true by lia.
  rewrite orb_false_r. auto.
  rewrite zlt_false by lia.
  rewrite orb_false_l. f_equal. lia.
  rewrite Int.bits_shr by lia.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite bits_ofwords by lia.
  rewrite zlt_true by lia. rewrite zlt_false by lia. f_equal. lia.
  rewrite zlt_false by lia. rewrite bits_ofwords by lia.
  rewrite zlt_false by lia. f_equal.
Qed.

Lemma decompose_shr_2:
  forall xh xl y,
  Int.zwordsize <= Int.unsigned y < zwordsize ->
  shr' (ofwords xh xl) y =
  ofwords (Int.shr xh (Int.sub Int.iwordsize Int.one))
          (Int.shr xh (Int.sub y Int.iwordsize)).
Proof.
  intros.
  assert (zwordsize = 2 * Int.zwordsize) by reflexivity.
  assert (Int.unsigned (Int.sub y Int.iwordsize) = Int.unsigned y - Int.zwordsize).
  { unfold Int.sub. rewrite Int.unsigned_repr. auto.
    rewrite Int.unsigned_repr_wordsize. generalize (Int.unsigned_range_2 y). lia. }
  apply Int64.same_bits_eq; intros.
  rewrite bits_shr' by auto. symmetry. rewrite bits_ofwords by auto.
  destruct (zlt i Int.zwordsize).
  rewrite Int.bits_shr by lia. rewrite H1.
  destruct (zlt (i + Int.unsigned y) zwordsize).
  rewrite zlt_true by lia. rewrite bits_ofwords by lia.
  rewrite zlt_false by lia. f_equal; lia.
  rewrite zlt_false by lia. rewrite bits_ofwords by lia.
  rewrite zlt_false by lia. auto.
  rewrite Int.bits_shr by lia.
  change (Int.unsigned (Int.sub Int.iwordsize Int.one)) with (Int.zwordsize - 1).
  destruct (zlt (i + Int.unsigned y) zwordsize);
  rewrite bits_ofwords by lia.
  symmetry. rewrite zlt_false by lia. f_equal.
  destruct (zlt (i - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); lia.
  symmetry. rewrite zlt_false by lia. f_equal.
  destruct (zlt (i - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); lia.
Qed.

Lemma decompose_add:
  forall xh xl yh yl,
  add (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh yh) (Int.add_carry xl yl Int.zero))
          (Int.add xl yl).
Proof.
  intros. symmetry. rewrite ofwords_add. rewrite add_unsigned.
  apply eqm_samerepr.
  rewrite ! ofwords_add'. rewrite (Int.unsigned_add_carry xl yl).
  set (cc := Int.add_carry xl yl Int.zero).
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh).
  change Int.modulus with (two_p 32).
  replace (Xh * two_p 32 + Xl + (Yh * two_p 32 + Yl))
     with ((Xh + Yh) * two_p 32 + (Xl + Yl)) by ring.
  replace (Int.unsigned (Int.add (Int.add xh yh) cc) * two_p 32 +
              (Xl + Yl - Int.unsigned cc * two_p 32))
     with ((Int.unsigned (Int.add (Int.add xh yh) cc) - Int.unsigned cc) * two_p 32
           + (Xl + Yl)) by ring.
  apply eqm_add. 2: apply eqm_refl. apply eqm_mul_2p32.
  replace (Xh + Yh) with ((Xh + Yh + Int.unsigned cc) - Int.unsigned cc) by ring.
  apply Int.eqm_sub. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
Qed.

Lemma decompose_sub:
  forall xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.sub (Int.sub xh yh) (Int.sub_borrow xl yl Int.zero))
          (Int.sub xl yl).
Proof.
  intros. symmetry. rewrite ofwords_add.
  apply eqm_samerepr.
  rewrite ! ofwords_add'. rewrite (Int.unsigned_sub_borrow xl yl).
  set (bb := Int.sub_borrow xl yl Int.zero).
  set (Xl := Int.unsigned xl); set (Xh := Int.unsigned xh);
  set (Yl := Int.unsigned yl); set (Yh := Int.unsigned yh).
  change Int.modulus with (two_p 32).
  replace (Xh * two_p 32 + Xl - (Yh * two_p 32 + Yl))
     with ((Xh - Yh) * two_p 32 + (Xl - Yl)) by ring.
  replace (Int.unsigned (Int.sub (Int.sub xh yh) bb) * two_p 32 +
              (Xl - Yl + Int.unsigned bb * two_p 32))
     with ((Int.unsigned (Int.sub (Int.sub xh yh) bb) + Int.unsigned bb) * two_p 32
           + (Xl - Yl)) by ring.
  apply eqm_add. 2: apply eqm_refl. apply eqm_mul_2p32.
  replace (Xh - Yh) with ((Xh - Yh - Int.unsigned bb) + Int.unsigned bb) by ring.
  apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_add. 2: apply Int.eqm_refl.
  apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
Qed.

Lemma decompose_sub':
  forall xh xl yh yl,
  sub (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add xh (Int.not yh)) (Int.add_carry xl (Int.not yl) Int.one))
          (Int.sub xl yl).
Proof.
  intros. rewrite decompose_sub. f_equal.
  rewrite Int.sub_borrow_add_carry by auto.
  rewrite Int.sub_add_not_3. rewrite Int.xor_assoc. rewrite Int.xor_idem.
  rewrite Int.xor_zero. auto.
  rewrite Int.xor_zero_l. unfold Int.add_carry.
  destruct (zlt (Int.unsigned xl + Int.unsigned (Int.not yl) + Int.unsigned Int.one) Int.modulus);
  compute; [right|left]; apply Int.mkint_eq; auto.
Qed.

Definition mul' (x y: Int.int) : int := repr (Int.unsigned x * Int.unsigned y).

Lemma mul'_mulhu:
  forall x y, mul' x y = ofwords (Int.mulhu x y) (Int.mul x y).
Proof.
  intros.
  rewrite ofwords_add. unfold mul', Int.mulhu, Int.mul.
  set (p := Int.unsigned x * Int.unsigned y).
  set (ph := p / Int.modulus). set (pl := p mod Int.modulus).
  transitivity (repr (ph * Int.modulus + pl)).
- f_equal. rewrite Z.mul_comm. apply Z_div_mod_eq. apply Int.modulus_pos.
- apply eqm_samerepr. apply eqm_add. apply eqm_mul_2p32. auto with ints.
  rewrite Int.unsigned_repr_eq. apply eqm_refl.
Qed.

Lemma decompose_mul:
  forall xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (hiword (mul' xl yl)) (Int.mul xl yh)) (Int.mul xh yl))
          (loword (mul' xl yl)).
Proof.
  intros.
  set (pl := loword (mul' xl yl)); set (ph := hiword (mul' xl yl)).
  assert (EQ0: unsigned (mul' xl yl) = Int.unsigned ph * two_p 32 + Int.unsigned pl).
  { rewrite <- (ofwords_recompose (mul' xl yl)). apply ofwords_add'. }
  symmetry. rewrite ofwords_add. unfold mul. rewrite !ofwords_add'.
  set (XL := Int.unsigned xl); set (XH := Int.unsigned xh);
  set (YL := Int.unsigned yl); set (YH := Int.unsigned yh).
  set (PH := Int.unsigned ph) in *. set (PL := Int.unsigned pl) in *.
  transitivity (repr (((PH + XL * YH) + XH * YL) * two_p 32 + PL)).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  apply eqm_mul_2p32.
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add.
  rewrite Int.add_unsigned. apply Int.eqm_unsigned_repr_l. apply Int.eqm_add.
  apply Int.eqm_refl.
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
  unfold Int.mul. apply Int.eqm_unsigned_repr_l. apply Int.eqm_refl.
  transitivity (repr (unsigned (mul' xl yl) + (XL * YH + XH * YL) * two_p 32)).
  rewrite EQ0. f_equal. ring.
  transitivity (repr ((XL * YL + (XL * YH + XH * YL) * two_p 32))).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  unfold mul'. apply eqm_unsigned_repr_l. apply eqm_refl.
  transitivity (repr (0 + (XL * YL + (XL * YH + XH * YL) * two_p 32))).
  rewrite Z.add_0_l; auto.
  transitivity (repr (XH * YH * (two_p 32 * two_p 32) + (XL * YL + (XL * YH + XH * YL) * two_p 32))).
  apply eqm_samerepr. apply eqm_add. 2: apply eqm_refl.
  change (two_p 32 * two_p 32) with modulus. exists (- XH * YH). ring.
  f_equal. ring.
Qed.

Lemma decompose_mul_2:
  forall xh xl yh yl,
  mul (ofwords xh xl) (ofwords yh yl) =
  ofwords (Int.add (Int.add (Int.mulhu xl yl) (Int.mul xl yh)) (Int.mul xh yl))
          (Int.mul xl yl).
Proof.
  intros. rewrite decompose_mul. rewrite mul'_mulhu.
  rewrite hi_ofwords, lo_ofwords. auto.
Qed.

Lemma decompose_ltu:
  forall xh xl yh yl,
  ltu (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh.
Proof.
  intros. unfold ltu. rewrite ! ofwords_add'. unfold Int.ltu, Int.eq.
  destruct (zeq (Int.unsigned xh) (Int.unsigned yh)).
  rewrite e. destruct (zlt (Int.unsigned xl) (Int.unsigned yl)).
  apply zlt_true; lia.
  apply zlt_false; lia.
  change (two_p 32) with Int.modulus.
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl).
  change Int.modulus with 4294967296. intros.
  destruct (zlt (Int.unsigned xh) (Int.unsigned yh)).
  apply zlt_true; lia.
  apply zlt_false; lia.
Qed.

Lemma decompose_leu:
  forall xh xl yh yl,
  negb (ltu (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.ltu xh yh.
Proof.
  intros. rewrite decompose_ltu. rewrite Int.eq_sym.
  unfold Int.eq. destruct (zeq (Int.unsigned xh) (Int.unsigned yh)).
  auto.
  unfold Int.ltu. destruct (zlt (Int.unsigned xh) (Int.unsigned yh)).
  rewrite zlt_false by lia; auto.
  rewrite zlt_true by lia; auto.
Qed.

Lemma decompose_lt:
  forall xh xl yh yl,
  lt (ofwords xh xl) (ofwords yh yl) = if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh.
Proof.
  intros. unfold lt. rewrite ! ofwords_add''. rewrite Int.eq_signed.
  destruct (zeq (Int.signed xh) (Int.signed yh)).
  rewrite e. unfold Int.ltu. destruct (zlt (Int.unsigned xl) (Int.unsigned yl)).
  apply zlt_true; lia.
  apply zlt_false; lia.
  change (two_p 32) with Int.modulus.
  generalize (Int.unsigned_range xl) (Int.unsigned_range yl).
  change Int.modulus with 4294967296. intros.
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh)).
  apply zlt_true; lia.
  apply zlt_false; lia.
Qed.

Lemma decompose_le:
  forall xh xl yh yl,
  negb (lt (ofwords yh yl) (ofwords xh xl)) =
  if Int.eq xh yh then negb (Int.ltu yl xl) else Int.lt xh yh.
Proof.
  intros. rewrite decompose_lt. rewrite Int.eq_sym.
  rewrite Int.eq_signed. destruct (zeq (Int.signed xh) (Int.signed yh)).
  auto.
  unfold Int.lt. destruct (zlt (Int.signed xh) (Int.signed yh)).
  rewrite zlt_false by lia; auto.
  rewrite zlt_true by lia; auto.
Qed.

(** Utility proofs for mixed 32bit and 64bit arithmetic *)

Lemma int_sub_ltu:
  forall x y,
    Int.ltu x y= true ->
    Int.unsigned (Int.sub y x) = unsigned (sub (repr (Int.unsigned y)) (repr (Int.unsigned x))).
Proof.
  intros. generalize (Int.sub_ltu x y H). intros. unfold Int.sub. unfold sub.
  rewrite Int.unsigned_repr. rewrite unsigned_repr.
  rewrite unsigned_repr by apply int_unsigned_range. rewrite int_unsigned_repr. reflexivity.
  rewrite unsigned_repr by apply int_unsigned_range.
  rewrite int_unsigned_repr. generalize (int_unsigned_range y).
  lia.
  generalize (Int.sub_ltu x y H). intros.
  generalize (Int.unsigned_range_2 y). intros. lia.
Qed.

End Int64.

Strategy 0 [Wordsize_64.wordsize].

Definition int_eq: forall (i1 i2: int), {i1=i2} + {i1<>i2}.
Proof.
  generalize Z.eq_dec. intros.
  destruct i1. destruct i2. generalize (H intval intval0). intro.
  inversion H0.
  - subst. left. assert (intrange = intrange0) by (apply proof_irr). congruence.
  - right. intro. inversion H2. contradiction.
Qed.

Notation int64 := Int64.int.

Definition int64_eq: forall (i1 i2: int64), {i1=i2} + {i1<>i2}.
Proof.
  generalize Z.eq_dec. intros.
  destruct i1. destruct i2. generalize (H intval intval0). intro.
  inversion H0.
  - subst. left. assert (intrange = intrange0) by (apply proof_irr). congruence.
  - right. intro. inversion H2. contradiction.
Qed.

Lemma int_clz_shru5: forall x,
  Int.shru (Int.clz x) (Int.repr 5) = if Int.eq x Int.zero then Int.one else Int.zero.
Proof.
  intros. unfold Int.shru. f_equal.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (Int.unsigned (Int.repr 5)) with 5.
  rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. change 32 with Int.zwordsize.
  rewrite Int.clz_div_wordsize.
  destruct (Int.eq x Int.zero); reflexivity.
Qed.

Lemma int64_clz_shru6: forall x,
  Int64.shru (Int64.clz x) (Int64.repr 6) = if Int64.eq x Int64.zero then Int64.one else Int64.zero.
Proof.
  intros. unfold Int64.shru. f_equal.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  change (Int64.unsigned (Int64.repr 6)) with 6.
  rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64. change 64 with Int64.zwordsize.
  rewrite Int64.clz_div_wordsize.
  destruct (Int64.eq x Int64.zero); reflexivity.
Qed.

Lemma int64_clz_shru6': forall x,
  Int64.shru' (Int64.clz x) (Int.repr 6) = if Int64.eq x Int64.zero then Int64.one else Int64.zero.
Proof.
  intros. unfold Int64.shru'.
  change (Int.unsigned (Int.repr 6)) with 6.
  generalize (Int64.unsigned_clz x). intros [H1 H2].
  rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64. change 64 with Int64.zwordsize.
  rewrite Int64.clz_div_wordsize.
  destruct (Int64.eq x Int64.zero); reflexivity.
Qed.

Lemma int_ctz_shru5: forall x,
  Int.shru (Int.ctz x) (Int.repr 5) = if Int.eq x Int.zero then Int.one else Int.zero.
Proof.
  intros. unfold Int.shru. f_equal.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (Int.unsigned (Int.repr 5)) with 5.
  rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. change 32 with Int.zwordsize.
  rewrite Int.ctz_div_wordsize.
  destruct (Int.eq x Int.zero); reflexivity.
Qed.

Lemma int64_ctz_shru6: forall x,
  Int64.shru (Int64.ctz x) (Int64.repr 6) = if Int64.eq x Int64.zero then Int64.one else Int64.zero.
Proof.
  intros. unfold Int64.shru. f_equal.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  change (Int64.unsigned (Int64.repr 6)) with 6.
  rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64. change 64 with Int64.zwordsize.
  rewrite Int64.ctz_div_wordsize.
  destruct (Int64.eq x Int64.zero); reflexivity.
Qed.

Lemma int64_ctz_shru6': forall x,
  Int64.shru' (Int64.ctz x) (Int.repr 6) = if Int64.eq x Int64.zero then Int64.one else Int64.zero.
Proof.
  intros. unfold Int64.shru'.
  change (Int.unsigned (Int.repr 6)) with 6.
  generalize (Int64.unsigned_ctz x). intros [H1 H2].
  rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64. change 64 with Int64.zwordsize.
  rewrite Int64.ctz_div_wordsize.
  destruct (Int64.eq x Int64.zero); reflexivity.
Qed.

Global Opaque Int.repr Int64.repr Byte.repr.

(** * Specialization to offsets in pointer values *)

Module Wordsize_Ptrofs.
  Definition wordsize := if Archi.ptr64 then 64%nat else 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; destruct Archi.ptr64; congruence. Qed.
End Wordsize_Ptrofs.

Strategy opaque [Wordsize_Ptrofs.wordsize].

Module Ptrofs.

Include Make(Wordsize_Ptrofs).

Definition to_int (x: int): Int.int := Int.repr (unsigned x).

Definition to_int64 (x: int): Int64.int := Int64.repr (unsigned x).

Definition of_int (x: Int.int) : int := repr (Int.unsigned x).

Definition of_intu := of_int.

Definition of_ints (x: Int.int) : int := repr (Int.signed x).

Definition of_int64 (x: Int64.int) : int := repr (Int64.unsigned x).

Definition of_int64u := of_int64.

Definition of_int64s (x: Int64.int) : int := repr (Int64.signed x).

Section AGREE32.

Hypothesis _32: Archi.ptr64 = false.

Lemma modulus_eq32: modulus = Int.modulus.
Proof.
  unfold modulus, wordsize.
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%nat else 32%nat).
  rewrite _32. reflexivity.
Qed.

Lemma eqm32:
  forall x y, Int.eqm x y <-> eqm x y.
Proof.
  intros. unfold Int.eqm, eqm. rewrite modulus_eq32; tauto.
Qed.

Definition agree32 (a: Ptrofs.int) (b: Int.int) : Prop :=
  Ptrofs.unsigned a = Int.unsigned b.

Lemma agree32_repr:
  forall i, agree32 (Ptrofs.repr i) (Int.repr i).
Proof.
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int.unsigned_repr_eq.
  apply f_equal2. auto. apply modulus_eq32.
Qed.

Lemma agree32_signed:
  forall a b, agree32 a b -> Ptrofs.signed a = Int.signed b.
Proof.
  unfold agree32; intros. unfold signed, Int.signed, half_modulus, Int.half_modulus.
  rewrite modulus_eq32. rewrite H. auto.
Qed.

Lemma agree32_of_int:
  forall b, agree32 (of_int b) b.
Proof.
  unfold of_int; intros. rewrite <- (Int.repr_unsigned b) at 2. apply agree32_repr.
Qed.

Lemma agree32_of_ints:
  forall b, agree32 (of_ints b) b.
Proof.
  unfold of_int; intros. rewrite <- (Int.repr_signed b) at 2. apply agree32_repr.
Qed.

Lemma agree32_of_int_eq:
  forall a b, agree32 a b -> of_int b = a.
Proof.
  unfold agree32, of_int; intros. rewrite <- H. apply repr_unsigned.
Qed.

Lemma agree32_of_ints_eq:
  forall a b, agree32 a b -> of_ints b = a.
Proof.
  unfold of_ints; intros. erewrite <- agree32_signed by eauto. apply repr_signed.
Qed.

Lemma agree32_to_int:
  forall a, agree32 a (to_int a).
Proof.
  unfold agree32, to_int; intros. rewrite <- (agree32_repr (unsigned a)).
  rewrite repr_unsigned; auto.
Qed.

Lemma agree32_to_int_eq:
  forall a b, agree32 a b -> to_int a = b.
Proof.
  unfold agree32, to_int; intros. rewrite H. apply Int.repr_unsigned.
Qed.

Lemma agree32_neg:
  forall a1 b1, agree32 a1 b1 -> agree32 (Ptrofs.neg a1) (Int.neg b1).
Proof.
  unfold agree32, Ptrofs.neg, Int.neg; intros. rewrite H. apply agree32_repr.
Qed.

Lemma agree32_add:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.add a1 a2) (Int.add b1 b2).
Proof.
  unfold agree32, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_sub:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.sub a1 a2) (Int.sub b1 b2).
Proof.
  unfold agree32, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_mul:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.mul a1 a2) (Int.mul b1 b2).
Proof.
  unfold agree32, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree32_repr.
Qed.

Lemma agree32_divs:
  forall a1 b1 a2 b2,
  agree32 a1 b1 -> agree32 a2 b2 -> agree32 (Ptrofs.divs a1 a2) (Int.divs b1 b2).
Proof.
  intros; unfold agree32, Ptrofs.divs, Int.divs.
  erewrite ! agree32_signed by eauto. apply agree32_repr.
Qed.

Lemma of_int_to_int:
  forall n, of_int (to_int n) = n.
Proof.
  intros; unfold of_int, to_int. apply eqm_repr_eq. rewrite <- eqm32.
  apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma to_int_of_int:
  forall n, to_int (of_int n) = n.
Proof.
  intros; unfold of_int, to_int. rewrite unsigned_repr. apply Int.repr_unsigned.
  unfold max_unsigned. rewrite modulus_eq32. destruct (Int.unsigned_range n); lia.
Qed.

End AGREE32.

Section AGREE64.

Hypothesis _64: Archi.ptr64 = true.

Lemma modulus_eq64: modulus = Int64.modulus.
Proof.
  unfold modulus, wordsize.
  change Wordsize_Ptrofs.wordsize with (if Archi.ptr64 then 64%nat else 32%nat).
  rewrite _64. reflexivity.
Qed.

Lemma eqm64:
  forall x y, Int64.eqm x y <-> eqm x y.
Proof.
  intros. unfold Int64.eqm, eqm. rewrite modulus_eq64; tauto.
Qed.

Definition agree64 (a: Ptrofs.int) (b: Int64.int) : Prop :=
  Ptrofs.unsigned a = Int64.unsigned b.

Lemma agree64_repr:
  forall i, agree64 (Ptrofs.repr i) (Int64.repr i).
Proof.
  intros; red. rewrite Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq.
  apply f_equal2. auto. apply modulus_eq64.
Qed.

Lemma agree64_signed:
  forall a b, agree64 a b -> Ptrofs.signed a = Int64.signed b.
Proof.
  unfold agree64; intros. unfold signed, Int64.signed, half_modulus, Int64.half_modulus.
  rewrite modulus_eq64. rewrite H. auto.
Qed.

Lemma agree64_of_int:
  forall b, agree64 (of_int64 b) b.
Proof.
  unfold of_int64; intros. rewrite <- (Int64.repr_unsigned b) at 2. apply agree64_repr.
Qed.

Lemma agree64_of_int_eq:
  forall a b, agree64 a b -> of_int64 b = a.
Proof.
  unfold agree64, of_int64; intros. rewrite <- H. apply repr_unsigned.
Qed.

Lemma agree64_to_int:
  forall a, agree64 a (to_int64 a).
Proof.
  unfold agree64, to_int64; intros. rewrite <- (agree64_repr (unsigned a)).
  rewrite repr_unsigned; auto.
Qed.

Lemma agree64_to_int_eq:
  forall a b, agree64 a b -> to_int64 a = b.
Proof.
  unfold agree64, to_int64; intros. rewrite H. apply Int64.repr_unsigned.
Qed.

Lemma agree64_neg:
  forall a1 b1, agree64 a1 b1 -> agree64 (Ptrofs.neg a1) (Int64.neg b1).
Proof.
  unfold agree64, Ptrofs.neg, Int64.neg; intros. rewrite H. apply agree64_repr.
Qed.

Lemma agree64_add:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.add a1 a2) (Int64.add b1 b2).
Proof.
  unfold agree64, Ptrofs.add, Int.add; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_sub:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.sub a1 a2) (Int64.sub b1 b2).
Proof.
  unfold agree64, Ptrofs.sub, Int.sub; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_mul:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.mul a1 a2) (Int64.mul b1 b2).
Proof.
  unfold agree64, Ptrofs.mul, Int.mul; intros. rewrite H, H0. apply agree64_repr.
Qed.

Lemma agree64_divs:
  forall a1 b1 a2 b2,
  agree64 a1 b1 -> agree64 a2 b2 -> agree64 (Ptrofs.divs a1 a2) (Int64.divs b1 b2).
Proof.
  intros; unfold agree64, Ptrofs.divs, Int64.divs.
  erewrite ! agree64_signed by eauto. apply agree64_repr.
Qed.

Lemma of_int64_to_int64:
  forall n, of_int64 (to_int64 n) = n.
Proof.
  intros; unfold of_int64, to_int64. apply eqm_repr_eq. rewrite <- eqm64.
  apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma to_int64_of_int64:
  forall n, to_int64 (of_int64 n) = n.
Proof.
  intros; unfold of_int64, to_int64. rewrite unsigned_repr. apply Int64.repr_unsigned.
  unfold max_unsigned. rewrite  modulus_eq64. destruct (Int64.unsigned_range n); lia.
Qed.

End AGREE64.

Global Hint Resolve
  agree32_repr agree32_of_int agree32_of_ints agree32_of_int_eq agree32_of_ints_eq
  agree32_to_int agree32_to_int_eq agree32_neg agree32_add agree32_sub agree32_mul agree32_divs
  agree64_repr agree64_of_int agree64_of_int_eq
  agree64_to_int agree64_to_int_eq agree64_neg agree64_add agree64_sub agree64_mul agree64_divs : ptrofs.

End Ptrofs.

Strategy 0 [Wordsize_Ptrofs.wordsize].

Notation ptrofs := Ptrofs.int.

Definition ptrofs_eq: forall (i1 i2: ptrofs), {i1=i2} + {i1<>i2}.
Proof.
  generalize Z.eq_dec. intros.
  destruct i1. destruct i2. generalize (H intval intval0). intro.
  inversion H0.
  - subst. left. assert (intrange = intrange0) by (apply proof_irr). congruence.
  - right. intro. inversion H2. contradiction.
Qed.

Global Opaque Ptrofs.repr.

Global Hint Resolve
  Int.modulus_pos Int.eqm_refl Int.eqm_refl2 Int.eqm_sym Int.eqm_trans
  Int.eqm_small_eq Int.eqm_add Int.eqm_neg Int.eqm_sub Int.eqm_mult
  Int.eqm_unsigned_repr Int.eqm_unsigned_repr_l Int.eqm_unsigned_repr_r
  Int.unsigned_range Int.unsigned_range_2
  Int.repr_unsigned Int.repr_signed Int.unsigned_repr : ints.

Global Hint Resolve
  Int64.modulus_pos Int64.eqm_refl Int64.eqm_refl2 Int64.eqm_sym Int64.eqm_trans
  Int64.eqm_small_eq Int64.eqm_add Int64.eqm_neg Int64.eqm_sub Int64.eqm_mult
  Int64.eqm_unsigned_repr Int64.eqm_unsigned_repr_l Int64.eqm_unsigned_repr_r
  Int64.unsigned_range Int64.unsigned_range_2
  Int64.repr_unsigned Int64.repr_signed Int64.unsigned_repr : ints.

Global Hint Resolve
  Ptrofs.modulus_pos Ptrofs.eqm_refl Ptrofs.eqm_refl2 Ptrofs.eqm_sym Ptrofs.eqm_trans
  Ptrofs.eqm_small_eq Ptrofs.eqm_add Ptrofs.eqm_neg Ptrofs.eqm_sub Ptrofs.eqm_mult
  Ptrofs.eqm_unsigned_repr Ptrofs.eqm_unsigned_repr_l Ptrofs.eqm_unsigned_repr_r
  Ptrofs.unsigned_range Ptrofs.unsigned_range_2
  Ptrofs.repr_unsigned Ptrofs.repr_signed Ptrofs.unsigned_repr : ints.

