Require Import RelationClasses.
Require Import PathToSubtree.
From Stdlib Require Import Arith.
From Stdlib Require Import Relations.
From Stdlib Require Import Lia.

Arguments clos_refl_trans {_}.

(* TODO: give a scope. *)
Global Notation "R ^*" := (clos_refl_trans R).

Lemma clos_refl_trans_ind_left' A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, R^* a b -> P a b -> R b c -> P a c) :
  forall a b, R^* a b -> P a b.
Proof. intros ? b. revert b. eapply clos_refl_trans_ind_left; eauto. Qed.

Lemma clos_refl_trans_ind_right' A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, R a b -> R^* b c -> P b c -> P a c) :
  forall a b, R^* a b -> P a b.
Proof. intros ? b. eapply clos_refl_trans_ind_right with (P := fun a => P a b); eauto. Qed.

Global Instance clos_refl_trans_refl A (R : relation A) : Reflexive R^*.
Proof. intros ?. apply rt_refl. Qed.

Global Instance clos_refl_trans_trans A (R : relation A) : Transitive R^*.
Proof. intros ?. apply rt_trans. Qed.

Inductive measured_closure {A : Type} (R : nat -> A -> A -> Prop) : nat -> A -> A -> Prop :=
  | MC_base n x y : R n x y -> measured_closure R n x y
  | MC_refl n x : measured_closure R n x x
  | MC_trans m n x y z :
      measured_closure R m x y -> measured_closure R n y z -> measured_closure R (m + n) x z
.

(* Now let's assume that a relation <_n is equipped with an integer measure.
 * We can define a reflexive-transitive closure that takes the measure into account. *)
Notation "R ^{ n }" := (measured_closure R n).

Global Instance measured_closure_refl A R n : Reflexive (@measured_closure A R n).
Proof. intros ?. apply MC_refl. Qed.

Lemma measured_closure_over_approx {A} R m n x y :
  m <= n -> R^{m} x y -> (@measured_closure A R n x y).
Proof.
  intros ? ?. replace n with (m + (n - m)); [ | lia]. eapply MC_trans.
  - eassumption.
  - reflexivity.
Qed.

Lemma measured_closure_equiv A R Rn (H : forall x y : A, R x y <-> exists n, Rn n x y) :
  forall x y, R^* x y <-> exists n, measured_closure Rn n x y.
Proof.
  intros x y. split.
  - induction 1 as [x y | | x y z ? IH0 ? IH1].
    + destruct (H x y) as ((n & ?) & _); [assumption | ]. exists n. constructor. assumption.
    + exists 0. reflexivity.
    + destruct IH0 as (m & ?). destruct IH1 as (n & ?). exists (m + n).
      eapply MC_trans; eassumption.
  - intros (n & G). induction G.
    + constructor. firstorder.
    + reflexivity.
    + etransitivity; eassumption.
Qed.

(* TODO: name *)
Lemma measure_closure_cases {A} (R : nat -> A -> A -> Prop) n x z :
  R^{n} x z -> x = z \/ exists p q y, R^{p} x y /\ R q y z /\ p + q <= n.
Proof.
  induction 1 as [n x z | | m n x y z ? IH0 ? IH1].
  - right. exists 0, n, x. auto using MC_refl.
  - auto.
  - destruct IH1 as [-> | (p & q & y' & ? & ? & ?)].
    + destruct IH0 as [ | (p & q & y & ? & ? & ?)]; [auto | ].
      right. exists p, q, y. repeat split; try assumption. lia.
    + right. eexists _, _, y'. repeat split; [ | eassumption | ].
      * eapply MC_trans; eassumption.
      * lia.
Qed.

(* Chaining two relations. *)
Definition chain {A B C} (RAB : A -> B -> Prop) (RBC : B -> C -> Prop) a c :=
  exists b, RAB a b /\ RBC b c.

Global Instance reflexive_chain {A} (R S : relation A) `{Reflexive A R} `{Reflexive A S} :
  Reflexive (chain R S).
Proof. intros x. exists x. split; reflexivity. Qed.

(* The general definition of forward simulation. That means that for all a >= b (with
   a : A and b : B) and a -> c (with c : C), then there exists d : D that completes
   the following square diagram:
   b <= a
   |    |
   v    v
   d <= c
   If A = B and C = D, we call it "preservation".

   Genarally,
   - The Leq relations is between states (S <= S'), or pairs of value and state ((v, S) <= (v', S')).
   - The Red relations are among the following ones:
     - Evaluation of operands.
     - Evalutaion of rvalues.
     - Reorganization.
     - Evaluation of statements.
 *)
Definition forward_simulation {A B C D : Type}
  (LeqBA : B -> A -> Prop) (LeqDC : D -> C -> Prop)
  (RedAC : A -> C -> Prop) (RedBD : B -> D -> Prop) :=
  forall a c, RedAC a c -> forall b, LeqBA b a -> exists d, LeqDC d c /\ RedBD b d.

Lemma execution_step {B C D : Type}
  (LeqDC : D -> C -> Prop) (RedBD : B -> D -> Prop) Sl S'l S'r :
  RedBD Sl S'l -> LeqDC S'l S'r
  -> exists S'l, LeqDC S'l S'r /\ RedBD Sl S'l.
Proof. exists S'l. split; assumption. Qed.

(* Generally, to prove preservation when the relation is a reflexive transitive closure, it
 * suffices to prove it for the base cases. *)
Lemma preservation_by_base_case {A B : Type}
  {LeqA : relation A} {LeqB : relation B} `{Reflexive _ LeqB} `{Transitive _ LeqB}
  {Red : A -> B -> Prop} :
  forward_simulation LeqA LeqB Red Red ->
  forward_simulation LeqA^* LeqB Red Red.
Proof.
  intros Hloc a b red_ab a' Leq_a_a'. revert b red_ab.
  induction Leq_a_a' as [ | | a2 a1 a0 _ IH0 _ IH1].
  - intros. eapply Hloc; eassumption.
  - intros. eexists. split; [reflexivity | eassumption].
  - intros b0 Red_a0_b0.
    destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
    destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
    exists b2. split; [ | assumption]. transitivity b1; assumption.
Qed.

Lemma preservation_by_base_case' {A B : Type}
  {LeqA : relation A} {LeqB : relation B} {Red : B -> A -> Prop} :
  forward_simulation Red Red LeqA LeqB ->
  forward_simulation Red Red LeqA^* LeqB^*.
Proof.
  intros Hloc a a' Leq_a_a'.
  induction Leq_a_a' as [? ? Hleq | | a0 a1 a2 _ IH0 _ IH1].
  - intros ? Hred. specialize (Hloc _ _ Hleq _ Hred). destruct Hloc as (? & ? & ?).
    eexists. split; [ | constructor]; eassumption.
  - intros. eexists. split; [eassumption | reflexivity].
  - intros b0 Red_b0_a0.
    destruct (IH0 _ Red_b0_a0) as (b1 & Red_b1_a1 & ?).
    destruct (IH1 _ Red_b1_a1) as (b2 & Red_b2_a2 & ?).
    exists b2. split; [assumption | ]. transitivity b1; assumption.
Qed.

(* TODO: define an equivalence between relations? *)
Lemma forward_simulation_chain {S0 S1} (R0l R0r : S0 -> S0 -> Prop) (R1l R1r : S1 -> S1 -> Prop)
  (red : S0 -> S1 -> Prop) :
  forward_simulation R0l R1l red red -> forward_simulation R0r R1r red red ->
  forward_simulation (chain R0l R0r) (chain R1l R1r) red red.
Proof.
  intros Sim_l Sim_r Sr S'r red_Sr_S'r Sl (Sm & R_Sl_Sm & R_Sm_Sr).
  specialize (Sim_r _ _ red_Sr_S'r _ R_Sm_Sr). destruct Sim_r as (S'm & R_S'm_S'r & red_Sm_S'm).
  specialize (Sim_l _ _ red_Sm_S'm _ R_Sl_Sm). destruct Sim_l as (S'l & R_S'l_S'm & red_Sl_S'l).
  exists S'l. split; [ | assumption]. exists S'm. split; assumption.
Qed.

(* Relations are generally defined for types of states, for any semantics between LLBC# and
   HLPL. In the following section, we will define the relation S <= S' for states,
   and (v, S) <= (v', S') for pairs of value and state.
*)
Class LeqBase state := leq_base : state -> state -> Prop.

(* TODO: is this class useful? *)
Class WellFormed state := well_formed : state -> Prop.

Section LeqValStateUtils.
  Context `{State state V}.
  Context `{LB : LeqBase state}.

  Definition leq_val_state_base (vSl vSr : V * state) :=
    forall a, fresh_anon (snd vSl) a -> fresh_anon (snd vSr) a ->
    leq_base ((snd vSl),, a |-> fst vSl) ((snd vSr),, a |-> fst vSr).

  (* The following two lemmas are used by the tactic `leq_val_state_step`. *)
  Lemma prove_leq_val_state_right_to_left vSl vm Sm vr Sr
    (G : forall a, fresh_anon Sm a -> fresh_anon Sr a ->
         exists vSm, leq_base vSm (Sr,, a |-> vr) /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* vSl (vm, Sm) ->
    leq_val_state_base^* vSl (vr, Sr).
  Proof.
    intros ?. eapply rt_trans; [eassumption | ]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
  Qed.

  Lemma prove_leq_val_state_left_to_right vl Sl vm Sm vSr
    (G : forall a, fresh_anon Sm a -> fresh_anon Sl a ->
         exists vSm, leq_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* (vm, Sm) vSr ->
    leq_val_state_base^* (vl, Sl) vSr.
  Proof.
    intros ?. eapply rt_trans; [ | eassumption]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
  Qed.

  (* This lemma is used by the tactic `leq_val_state_add_anon`. *)
  Lemma prove_leq_val_state_add_anon vl Sl vm Sm vSr b w
    (fresh_b : fresh_anon Sl b)
    (G : forall a, fresh_anon Sm a -> fresh_anon Sl a -> fresh_anon (Sl,, a |-> vl) b ->
         exists vSm, leq_base (Sl,, a |-> vl) vSm /\ vSm = Sm,, a |-> vm,, b |-> w) :
    leq_val_state_base^* (vm, Sm,, b |-> w) vSr ->
    leq_val_state_base^* (vl, Sl) vSr.
  Proof.
    intros ?. eapply rt_trans; [ | eassumption]. constructor.
    intros a ? (? & ?)%fresh_anon_add_anon. cbn in *.
    rewrite add_anon_commute by congruence.
    destruct (G a) as (? & ? & ->); try assumption.
    now apply fresh_anon_add_anon.
  Qed.

  (* The issue by directly applying the lemma `preservation_by_base_case` is that it
     obfuscates the relation le, by unfolding it and replacing it with a reflexive transitive
     closure.
     We're going to give similar statements, but these types, the hypothesis uses the relation le.
   *)
  (*
  Lemma preservation_by_base_case_leq_state_leq_val_state
    (red : state -> (V * state) -> Prop) :
    forward_simulation E equiv_val_state red red
    -> forward_simulation (@leq_base _ LB) (@leq _ LeqStateVal) red red
    -> forward_simulation (clos_refl_trans _ leq_base) LeqStateVal red.
  Proof. apply preservation_by_base_case. intros ? ? ? ?. reflexivity. Qed.
   *)
End LeqValStateUtils.

(* TODO: split into two tactics/lemmas:
 * - leq_val_state_step_left
 * - leq_val_state_step_right
 *)
(* This lemma is used to prove a goal of the form ?vSl < (vr, Sr) or (vl, Sl) < ?vSr without
 * exhibiting the existential variable ?vSl or ?vSr. *)
Ltac leq_val_state_step :=
  let a := fresh "a" in
  lazymatch goal with
  (* When proving a goal `leq ?vSl (vr, Sr)`, using this tactic creates three subgoals:
     1. leq_base ?vSm (Sr,, a |-> v)
     2. ?vSm = ?Sm,, a |-> ?vm
     3. leq ?vSl (?vm, ?Sm) *)
  | |- ?leq_star ?vSl (?vr, ?Sr) =>
      eapply prove_leq_val_state_right_to_left; [intros a ? ?; eexists; split | ]
  end.

Ltac leq_val_state_step_left :=
  let a := fresh "a" in
  lazymatch goal with
  (* When proving a goal `leq (vl, Sl) ?vSr`, using this tactic creates three subgoals:
     1. leq_base (Sl,, a |-> v) ?vSm
     2. ?vSm = ?Sm,, a |-> ?vm
     3. leq (?vm, ?Sm) ?vSr *)
  (* Note: the hypothesis that a is fresh in ?Sm creates problems.
     Indeed, ?Sm is an existential and it can be accidently instantiated to a wrong value by
     eauto. That's why we're removing this hypothesis.
     TODO: remove it from the hypotheses of the lemma? *)
  | |- ?leq_star (?vl, ?Sl) ?vSr =>
      eapply prove_leq_val_state_left_to_right; [intros a _ ?; eexists; split | ]
  end.

(* In LLBC+, some base rules are of the form S < S',, b |-> w (with b fresh in S). The presence of
 * two anonymous variables, we need to do a special case.
 * Let a be a fresh anon. We prove that
 * 1. Sl,, a |-> vl < ?vSm
 * 2. ?vSm = Sm,, a |-> vm,, b |-> w
 * 3. (?vm, ?Sm) <* ?vSr
 *
 * To apply the base rule in (1), we need a hypothesis that b is fresh in Sl,, a |-> vl. This is
 * true because a and b are two different fresh variables.
 *
 * Because a and b are fresh, we can perform the following commutation:
 * Sm,, a |-> vm,, b |-> w = Sm,, b |-> w,, a |-> vm
 * Using (2), that shows that (vl, Sl) < (vm, Sm,, b |-> w).
 *)
Ltac leq_val_state_add_anon :=
  let a := fresh "a" in
  lazymatch goal with
  |  |- ?leq_star (?vl, ?Sl) ?vSr =>
      eapply prove_leq_val_state_add_anon;
        (* The hypothesis fresh_anon Sl b should be resolved automatically, because there should be
         * a single hypothesis of the form "fresh_anon Sr b" in the context, with Sr an expression
         * of Sl, that can be used. *)
        [eauto with spath; fail |
         intros a ? ? ?; eexists; split |
        ]
  end.

Section Leq.
  Context `{LeqBase state}.
  Context {equiv : state -> state -> Prop}.
  Context `{Reflexive _ equiv}.
  Context `{Transitive _ equiv}.
  Context (sim_equiv_leq_base : forward_simulation equiv equiv leq_base leq_base).

  Definition leq := chain leq_base^* equiv.

  Global Instance reflexive_leq : Reflexive leq.
  Proof. intros x. exists x. split; reflexivity. Qed.

  Global Instance transitive_leq : Transitive leq.
  Proof.
    intros x y z (y' & ? & equiv_y'_y) (z' & leq_y_z' & ?).
    apply preservation_by_base_case' in sim_equiv_leq_base.
    specialize (sim_equiv_leq_base _ _ leq_y_z' _ equiv_y'_y).
    destruct sim_equiv_leq_base as (z'' & ? & ?). exists z''. split.
    - transitivity y'; assumption.
    - transitivity z'; assumption.
  Qed.
End Leq.

Section WellFormedSimulations.
  Context `{LB : LeqBase state}.
  Context `{WF : WellFormed state}.

  (* Preservation of reorgs require well-formedness. However, well-formedness for related states is
   * not proved the same in LLBC+ and HLPL+:
   * - In HLPL+, we prove that well-formedness is preserves from right-to-left. That means that
   *   if Sl < Sr and Sr is well-formed, than Sl is well-formed.
   * - In LLBC+, we prove that well-formedness is preserves from left-to-right. That means that
   *   if Sl < Sr and Sl is well-formed, than Sr is well-formed.
   * Thus, we are going to state two different definitions and lemmas. *)
  Definition well_formed_forward_simulation_r {B C D : Type}
    (LeqBA : B -> state -> Prop) (LeqDC : D -> C -> Prop)
    (RedAC : state -> C -> Prop) (RedBD : B -> D -> Prop) :=
    forall a c, well_formed a -> RedAC a c -> forall b, LeqBA b a -> exists d, LeqDC d c /\ RedBD b d.

  Definition well_formed_forward_simulation_l {A C D : Type}
  (LeqBA : state -> A -> Prop) (LeqDC : D -> C -> Prop)
  (RedAC : A -> C -> Prop) (RedBD : state -> D -> Prop) :=
  forall a b c, well_formed b -> RedAC a c -> LeqBA b a -> exists d, LeqDC d c /\ RedBD b d.

  (* Reorganizations and leq are defined as reflexive-transitive closure of relations (that we are
   * going to denote < and reorg). When we want to prove the preservation, ie:

      Sl <*  Sr

      |      |
      *      *
      v      v

     Sl' <* Sr'

   * We want to derive it by only considering the cases of < and reorg, and ignoring the reflexive and
   * transitive cases:

      Sl <  Sr

      |     |
      *     |
      v     v

     Sl' <* Sr'

   * However, this proof scheme is wrong in general. Our strategy is to exhibit a measure |.| from
   * states to a well-founded order, that is decreasing by applications of < and reorg.
   *)
  Lemma preservation_reorg_r (reorg : state -> state -> Prop)
    (measure : state -> nat)
    (leq_decreasing : forall a b, leq_base a b -> measure a < measure b)
    (reorg_decreasing : forall a b, reorg a b -> measure b < measure a)
    (leq_base_preserves_wf_r : forall a b, well_formed b -> leq_base a b -> well_formed a)
    (reorg_preserves_wf : forall a b, reorg a b -> @well_formed _ WF a -> @well_formed _ WF b)
    (H : well_formed_forward_simulation_r (@leq_base _ LB) (@leq_base _ LB)^* reorg reorg^*) :
    well_formed_forward_simulation_r leq_base^* leq_base^* reorg^* reorg^*.
  Proof.
    (* Sequences of reorgenizations make the measure decrease. *)
    assert (forall S S', reorg^* S S' -> measure S' <= measure S).
    { intros ? ? Hreorg. induction Hreorg; subst; eauto using Nat.lt_le_incl, Nat.le_trans. }
    (* The well-formedness is preserved by sequences of the base. *)
    assert (forall Sl Sr, well_formed Sr -> leq_base^* Sl Sr -> well_formed Sl).
    { intros ? ? ? G. induction G; eauto. }
    intros Sr. remember (measure Sr) as n eqn:EQN. revert Sr EQN.
    induction n as [? IH] using lt_wf_ind. intros Sr -> Sr' well_formed_Sr reorg_Sr_Sr'.
    destruct reorg_Sr_Sr' as [ | Sr Sr' Sr'' reorg_Sr_Sr' ? _] using clos_refl_trans_ind_right'.
    { intros. eexists. split; [eassumption | apply rt_refl]. }
    intros Sl leq_Sl_Sr.
    destruct leq_Sl_Sr as [ | Sl Sm Sr ? _ leq_Sm_Sr] using clos_refl_trans_ind_left'.
    { eexists. split; [apply rt_refl | ]. eapply rt_trans; [constructor | ]; eassumption. }
    specialize (H _ _ well_formed_Sr reorg_Sr_Sr' _ leq_Sm_Sr). destruct H as (Sm' & leq_Sm'_Sr' & reorg_Sm_Sm').
    assert (exists Sl', leq_base^* Sl' Sm' /\ reorg^* Sl Sl')
      as (Sl' & ? & ?)
      by eauto.
    assert (exists Sm'', leq_base^* Sm'' Sr'' /\ reorg^* Sm' Sm'')
      as (Sm'' & ? & ?)
      by eauto.
    assert (exists Sl'', leq_base^* Sl'' Sm'' /\ reorg^* Sl' Sl'')
      as (? & ? & ?).
    { eapply IH; [ | reflexivity | | eassumption..]; eauto using Nat.le_lt_trans. }
    eexists. split; eapply rt_trans; eassumption.
  Qed.

  Lemma preservation_reorg_l
    (reorg : state -> state -> Prop) (leq_base_n : nat -> state -> state -> Prop)
    (measure : state -> nat)
    (leq_decreasing : forall n a b, leq_base_n n a b -> measure a < measure b + n)
    (reorg_decreasing : forall a b, reorg a b -> measure b < measure a)
    (H : forall n, forward_simulation (leq_base_n n) (measured_closure leq_base_n n) reorg reorg^*) :
    forall n, forward_simulation (measured_closure leq_base_n n) (measured_closure leq_base_n n) reorg^* reorg^*.
  Proof.
    assert (leq_clos_decreasing : forall S S', reorg^* S S' -> measure S' <= measure S).
    { intros ? ? Hreorg. induction Hreorg; eauto using Nat.lt_le_incl, Nat.le_trans. }
    intros n Sr.
    remember (measure Sr + n) as N eqn:EQN.
    revert n Sr EQN. induction N as [? IH] using lt_wf_ind.
    intros n Sr -> S''r reorg_Sr_S''r Sl leq_Sl_Sr.
    destruct reorg_Sr_S''r as [ | Sr S'r S''r reorg_Sr_S'r ? _] using clos_refl_trans_ind_right'.
    { eexists. split; [exact leq_Sl_Sr | reflexivity]. }
    apply measure_closure_cases in leq_Sl_Sr.
    destruct leq_Sl_Sr as [ | (p & q & Sm & leq_Sl_Sm & leq_Sm_Sr & ?)].
    { subst. exists S''r. split; [reflexivity | ]. transitivity S'r; [constructor | ]; assumption. }
    specialize (H q _ _ reorg_Sr_S'r _ leq_Sm_Sr). destruct H as (S'm & leq_S'm_S'r & reorg_Sm_S'm).
    specialize (leq_decreasing _ _ _ leq_Sm_Sr).
    edestruct IH with (Sr := Sm) as (S'l & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    specialize (reorg_decreasing _ _ reorg_Sr_S'r).
    edestruct IH with (Sr := S'r) as (S''m & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    specialize (leq_clos_decreasing _ _ reorg_Sm_S'm).
    edestruct IH with (Sr := S'm) as (S''l & ? & ?);
      [ | reflexivity | eassumption.. | ]. lia.
    exists S''l. split.
    - eapply measured_closure_over_approx; [eassumption | ].
      apply MC_trans with (y := S''m); assumption.
    - transitivity S'l; assumption.
  Qed.

  (* TODO: reformulate this theorem for the measured relation. *)
  Lemma _preservation_reorg_l (reorg : state -> state -> Prop)
    (measure : state -> nat)
    (leq_decreasing : forall a b, leq_base a b -> measure a < measure b)
    (reorg_decreasing : forall a b, reorg a b -> measure b < measure a)
    (leq_base_preserves_wf_l : forall a b, well_formed a -> leq_base a b -> well_formed b)
    (reorg_preserves_wf : forall a b, reorg a b -> @well_formed _ WF a -> @well_formed _ WF b)
    (H : well_formed_forward_simulation_l (@leq_base _ LB) (@leq_base _ LB)^* reorg reorg^*) :
    well_formed_forward_simulation_l leq_base^* leq_base^* reorg^* reorg^*.
  Proof.
    assert (forall S S', reorg^* S S' -> measure S' <= measure S).
    { intros ? ? Hreorg. induction Hreorg; eauto using Nat.lt_le_incl, Nat.le_trans. }
    assert (forall S S', well_formed S -> reorg^* S S' -> well_formed S').
    { intros ? ? ? Hreorg. induction Hreorg; eauto. }
    assert (forall Sl Sr, well_formed Sl -> leq_base^* Sl Sr -> well_formed Sr).
    { intros ? ? ? G. induction G; eauto. }
    intros Sr.
    remember (measure Sr) as n eqn:EQN. revert Sr EQN.
    induction n as [? IH] using lt_wf_ind.
    intros Sr -> Sl Sr' well_formed_Sl reorg_Sr_Sr'.
    destruct reorg_Sr_Sr' as [ | Sr Sr' Sr'' reorg_Sr_Sr' ? _] using clos_refl_trans_ind_right'.
    { intros. eexists. split; [eassumption | apply rt_refl]. }
    intros leq_Sl_Sr.
    destruct leq_Sl_Sr as [ | Sl Sm Sr ? _ leq_Sm_Sr] using clos_refl_trans_ind_left'.
    { eexists. split; [apply rt_refl | ]. eapply rt_trans; [constructor | ]; eassumption. }
    destruct (H Sr Sm Sr') as (Sm' & leq_Sm'_Sr' & reorg_Sm_Sm'); [eauto.. | ].
    assert (exists Sl', leq_base^* Sl' Sm' /\ clos_refl_trans reorg Sl Sl')
      as (Sl' & ? & ?)
      by eauto.
    assert (exists Sm'', leq_base^* Sm'' Sr'' /\ clos_refl_trans reorg Sm' Sm'')
      as (Sm'' & ? & ?)
      by eauto.
    assert (exists Sl'', leq_base^* Sl'' Sm'' /\ clos_refl_trans reorg Sl' Sl'')
      as (? & ? & ?).
    { eapply IH; [ | reflexivity | | eassumption..]; eauto using Nat.le_lt_trans. }
    eexists. split; eapply rt_trans; eassumption.
  Qed.
End WellFormedSimulations.

Definition rel_compose {A B C : Type} (R : A -> B -> Prop) (S : B -> C -> Prop) a c :=
  exists b, R a b /\ S b c.

Lemma forward_simulation_closure A (E R : relation A) :
  forward_simulation E E R R -> forward_simulation E E R^* R^*.
Proof.
  intros H ? ? G. induction G as [ | | ? ? ? ? IH0 ? IH1].
  - intros. edestruct H as (? & ? & ?); [eassumption.. | ].
    eexists. split; [ | constructor]; eassumption.
  - intros. eexists. split; [ | apply rt_refl]. assumption.
  - intros.
    edestruct IH0 as (? & ? & ?); [eassumption | ].
    edestruct IH1 as (? & ? & ?); [eassumption | ].
    eexists. split; [ | eapply rt_trans]; eassumption.
Qed.

(* Lemmas to prove the commutation of reorganizations. *)
(* TODO: document it *)
Lemma do_reorg_step {S} {reorg leq : relation S} S0 S1 Sr:
  reorg S0 S1 -> (exists Sl, leq Sl Sr /\ reorg^* S1 Sl) ->
  exists Sl, leq Sl Sr /\ reorg^* S0 Sl.
Proof.
  intros ? (Sl & ? & ?). exists Sl. split; [assumption | ].
  etransitivity; [constructor | ]; eassumption.
Qed.

Lemma do_reorgs {S} {reorg leq : relation S} S0 S1 Sr:
  reorg^* S0 S1 -> (exists Sl, leq Sl Sr /\ reorg^* S1 Sl) ->
  exists Sl, leq Sl Sr /\ reorg^* S0 Sl.
Proof.
  intros ? (Sl & ? & ?). exists Sl. split; [assumption | ].
  etransitivity; eassumption.
Qed.

Lemma reorgs_done {S} {reorg leq : relation S} S0 Sr:
  leq S0 Sr -> exists Sl, leq Sl Sr /\ reorg^* S0 Sl.
Proof. exists S0. split; [assumption | reflexivity]. Qed.

Lemma leq_step_right {S} {R : relation S} Sl Sm Sr : R Sm Sr -> R^* Sl Sm -> R^* Sl Sr.
Proof. intros. transitivity Sm; [ | constructor]; assumption. Qed.
