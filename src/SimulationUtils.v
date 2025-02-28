Require Import RelationClasses.
Require Import PathToSubtree.
Require Import Arith.

(* The general definition of forward simulation. That means that for all a >= b (with
   a : A and b : B) and a -> c (with c : C), then there exists d : D that completes
   the following square diagram:
   b <= a
   |    |
   v    v
   d <= c
   If A = B and C = D, we call it "preservation".

   Genarally,
   - The Le relations is between states (S <= S'), or pairs of value and state ((v, S) <= (v', S')).
   - The Red relations are among the following ones:
     - Evaluation of operands.
     - Evalutaion of rvalues.
     - Reorganization.
     - Evaluation of statements.
 *)
Definition forward_simulation {A B C D : Type}
  (LeBA : B -> A -> Prop) (LeDC : D -> C -> Prop)
  (RedAC : A -> C -> Prop) (RedBD : B -> D -> Prop) :=
  forall a c, RedAC a c -> forall b, LeBA b a -> exists d, LeDC d c /\ RedBD b d.

(* The reflexive-transitive R* closure of a relation R. *)
Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| Cl_base x y : R x y -> refl_trans_closure R x y
| Cl_refl x : refl_trans_closure R x x
| Cl_trans x y z :
    refl_trans_closure R x y -> refl_trans_closure R y z -> refl_trans_closure R x z.

Global Instance reflexive_refl_trans_closure A (R : A -> A -> Prop) :
  Reflexive (refl_trans_closure R).
Proof. intro. apply Cl_refl. Qed.

Global Instance transitive_refl_trans_closure A (R : A -> A -> Prop) :
  Transitive (refl_trans_closure R).
Proof. intros ? ? ?. apply Cl_trans. Qed.

Lemma refl_trans_closure_ind_left A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, R a b -> refl_trans_closure R b c -> P b c -> P a c) :
  forall a b, refl_trans_closure R a b -> P a b.
Proof.
  intros a b rel_a_b.
  assert (forall c, refl_trans_closure R b c -> P b c -> P a c).
  { induction rel_a_b; eauto using Cl_trans. }
  auto using Cl_refl.
Qed.

Lemma refl_trans_closure_ind_right A R (P : A -> A -> Prop)
  (Prefl : forall a : A, P a a)
  (Pstep : forall a b c, refl_trans_closure R a b -> P a b -> R b c -> P a c) :
  forall a b, refl_trans_closure R a b -> P a b.
Proof.
  intros b c rel_b_c.
  assert (forall a, refl_trans_closure R a b -> P a b -> P a c).
  { induction rel_b_c; eauto using Cl_trans. }
  auto using Cl_refl.
Qed.

(* Generally, to prove preservation when the relation is a reflexive transitive closure, it
 * suffices to prove it for the base cases. *)
Lemma preservation_by_base_case {A B : Type}
  (LeA : A -> A -> Prop) (LeB : B -> B -> Prop) (RedAB : A -> B -> Prop) :
  forward_simulation LeA (refl_trans_closure LeB) RedAB RedAB ->
  forward_simulation (refl_trans_closure LeA) (refl_trans_closure LeB) RedAB RedAB.
Proof.
  intros H a b red_ab a' Le_a_a'. revert b red_ab.
  induction Le_a_a' as [ | | a2 a1 a0 _ IH0 _ IH1].
  - intros. eapply H; eassumption.
  - intros. eexists. split; [reflexivity | eassumption].
  - intros b0 Red_a0_b0.
    destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
    destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
    exists b2. split; [ | assumption]. transitivity b1; assumption.
Qed.

(* Generally, to complete the square diagram, we will prove that:
   - there exists d0 such that c -> d0
   - there exists d1 such that b <= d1
   - d0 = d1
   This lemma allows us to not exhibit the terms d0 and d1 explicitely. As the relations LeCD and
   RedBD are generally inductively defined, these terms are constructed by applying inductive
   constructors. This is why the constructors of the relation should be on the form:
   - red S E[S] for the reduction
   - E[S] < S for the base relation
   Finally, the last goal d0 = d1 is intended to be solved automatically, using the tactic
   states_eq.
 *)
Lemma complete_square_diagram {B C D : Type}
  (LeDC : D -> C -> Prop) (RedBD : B -> D -> Prop) b c (d0 d1 : D) :
  LeDC d0 c -> RedBD b d1 -> d0 = d1
  -> exists d, LeDC d c /\ RedBD b d.
Proof. intros ? ? <-. exists d0. auto. Qed.

(* Generally, two types A and B will have a canonical relation Le. *)
Class Le (A B : Type) :=
{ le : A -> B -> Prop }.

Definition preservation {A B} `{LeA : Le A A} `{LeB : Le B B} (RedAB : A -> B -> Prop) :=
  forward_simulation (@le A A LeA) (@le B B LeB) RedAB RedAB.

(* Relations are generally defined for types of states, for any semantics between LLBC# and
   HLPL. In the following section, we will define the relation S <= S' for states,
   and (v, S) <= (v', S') for pairs of value and state.
   We also specify a well-formedness predicate for states. Indeed, some preservation properties
   require the well-formedness to be proven.
*)
Class LeBase state := {
  le_base : state -> state -> Prop;
  well_formed : state ->  Prop;
  le_base_preserves_well_formedness Sl Sr : well_formed Sr -> le_base Sl Sr -> well_formed Sl;
}.

Global Instance LeState state `(LeBase state) : Le (state) (state) :=
{ le := refl_trans_closure le_base }.

Section LeValStateUtils.
  Context `{State state V}.
  Context `{LB : LeBase state}.

  Definition le_val_state_base (vSl vSr : V * state) :=
    forall a, fresh_anon (snd vSl) a -> fresh_anon (snd vSr) a ->
    le_base ((snd vSl),, a |-> fst vSl) ((snd vSr),, a |-> fst vSr).

  (* For pair of value and states, we have:
     (v, S) <= (v', S') ::= S,, _ |-> v <= S', _ |-> v'
   *)
  Global Instance LeStateVal : Le (V * state) (V * state) :=
  { le := refl_trans_closure le_val_state_base }.

  Lemma prove_le_val_state vSl vm Sm vr Sr
    (G : forall a, fresh_anon Sm a -> fresh_anon Sr a ->
         exists vSm, le_base vSm Sr,, a |-> vr /\ vSm = Sm,, a |-> vm) :
    @le _ _ LeStateVal vSl (vm, Sm) ->
    @le _ _ LeStateVal vSl (vr, Sr).
  Proof.
    intros ?. etransitivity; [eassumption | ]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
  Qed.

  (* The issue by directly applying the lemma `preservation_by_base_case` is that it
     obfuscates the relation le, by unfolding it and replacing it with a reflexive transitive
     closure.
     We're going to give similar statements, but these types, the hypothesis uses the relation le.
   *)
  Lemma preservation_by_base_case_le_state_le_val_state
    (red : state -> (V * state) -> Prop) :
    forward_simulation (@le_base _ LB) (@le _ _ LeStateVal) red red
    -> @preservation _ _ (@LeState _ LB) LeStateVal red.
  Proof. apply preservation_by_base_case. Qed.
End LeValStateUtils.

(* When proving a goal `le ?vSl (vr, Sr)`, using this tactic create three subgoals:
   1. le_base ?vSm (Sr,, a |-> v)r
   2. ?vSm = ?Sm,, a |-> ?vm
   3. le ?vSl (?vm, ?Sm)

   The first goal is used by applying the adequate base rule. Here, a is a fresh anon.
   The second goal is proved by rewriting (with `autorewrite with spath`) then reflexivity.
   The third goal is proved by applying again this tactic, or concluding by reflexivity.

   With this strategy, the states and values ?vSl, ?vSm, ?vm and ?Sm never have to be instantiated
   explicitely.
 *)
Ltac le_val_state_step :=
  let a := fresh "a" in
  eapply prove_le_val_state; [intros a ? ?; eexists; split | ].

Section WellFormedSimulations.
  Context `{LB : LeBase state}.
  Definition well_formed_forward_simulation {B C D : Type}
    (LeBA : B -> state -> Prop) (LeDC : D -> C -> Prop)
    (RedAC : state -> C -> Prop) (RedBD : B -> D -> Prop) :=
    forall a c, well_formed a -> RedAC a c -> forall b, LeBA b a -> exists d, LeDC d c /\ RedBD b d.

  Definition well_formed_preservation (Red : state -> state -> Prop) :=
    well_formed_forward_simulation (@le _ _ (@LeState _ LB)) (@le _ _ (@LeState _ LB)) Red Red.

  Lemma le_preserves_well_formedness Sl Sr : well_formed Sr -> le Sl Sr -> well_formed Sl.
  Proof. intros ? H. induction H; eauto using le_base_preserves_well_formedness. Qed.

  (* Reorganizations and le are defined as reflexive-transitive closure of relations (that we are
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
  (* Note: for the moment, we just use natural measures. *)
  Lemma preservation_reorg (reorg : state -> state -> Prop)
    (measure : state -> nat)
    (le_decreasing : forall a b, le_base a b -> measure a < measure b)
    (reorg_decreasing : forall a b, reorg a b -> measure b < measure a)
    (reorg_preserves_wf : forall a b, reorg a b -> @well_formed _ LB a -> @well_formed _ LB b)
    (H : well_formed_forward_simulation (@le_base _ LB) (@le _ _ (@LeState _ LB)) reorg (refl_trans_closure reorg)) :
    well_formed_preservation (refl_trans_closure reorg).
  Proof.
    assert (forall S S', refl_trans_closure reorg S S' -> measure S' <= measure S).
    { intros ? ? Hreorg. induction Hreorg; eauto using Nat.lt_le_incl, Nat.le_trans. }
    intros Sr.
    remember (measure Sr) as n eqn:EQN. revert Sr EQN.
    induction n as [? IH] using lt_wf_ind.
    intros Sr -> Sr' well_formed_Sr reorg_Sr_Sr'.
    destruct reorg_Sr_Sr' as [ | Sr Sr' Sr'' reorg_Sr_Sr' ? _] using refl_trans_closure_ind_left.
    { intros. eexists. split; [eassumption | reflexivity]. }
    intros Sl le_Sl_Sr.
    destruct le_Sl_Sr as [ | Sl Sm Sr ? _ le_Sm_Sr] using refl_trans_closure_ind_right.
    { eexists. split; [reflexivity | ]. transitivity Sr'; [constructor | ]; assumption. }
    specialize (H _ _ well_formed_Sr reorg_Sr_Sr' _ le_Sm_Sr). destruct H as (Sm' & le_Sm'_Sr' & reorg_Sm_Sm').
    assert (exists Sl', le Sl' Sm' /\ refl_trans_closure reorg Sl Sl')
      as (Sl' & ? & ?)
    by eauto using le_base_preserves_well_formedness.
    assert (exists Sm'', le Sm'' Sr'' /\ refl_trans_closure reorg Sm' Sm'')
      as (Sm'' & ? & ?)
      by eauto.
    assert (exists Sl'', le Sl'' Sm'' /\ refl_trans_closure reorg Sl' Sl'')
      as (? & ? & ?).
    { eapply IH; [ | reflexivity | | eassumption..];
      eauto using Nat.le_lt_trans, le_preserves_well_formedness. }
    eexists. split; [transitivity Sm'' | transitivity Sl']; eassumption.
  Qed.
End WellFormedSimulations.
