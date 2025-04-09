Require Import RelationClasses.
Require Import PathToSubtree.
From Stdlib Require Import Arith.
From Stdlib Require Import Relations.

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

(* Generally, to complete the square diagram, we will prove that:
   - there exists d0 such that c -> d0
   - there exists d1 such that b <= d1
   - d0 = d1
   This lemma allows us to not exhibit the terms d0 and d1 explicitely. As the relations LeqCD and
   RedBD are generally inductively defined, these terms are constructed by applying inductive
   constructors. This is why the constructors of the relation should be on the form:
   - red S E[S] for the reduction
   - E[S] < S for the base relation
   Finally, the last goal d0 = d1 is intended to be solved automatically, using the tactic
   states_eq.
 *)
Lemma complete_square_diagram {B C D : Type}
  (LeqDC : D -> C -> Prop) (RedBD : B -> D -> Prop) b c (d0 d1 : D) :
  LeqDC d0 c -> RedBD b d1 -> d0 = d1
  -> exists d, LeqDC d c /\ RedBD b d.
Proof. intros ? ? <-. exists d0. auto. Qed.

(* Generally, to prove preservation when the relation is a reflexive transitive closure, it
 * suffices to prove it for the base cases. *)
Lemma preservation_by_base_case {A B : Type}
  (LeqA : relation A) (LeqB : relation B) (Red : A -> B -> Prop) :
  forward_simulation LeqA LeqB^* Red Red ->
  forward_simulation LeqA^* LeqB^* Red Red.
Proof.
  intros H a b red_ab a' Leq_a_a'. revert b red_ab.
  induction Leq_a_a' as [ | | a2 a1 a0 _ IH0 _ IH1].
  - intros. eapply H; eassumption.
  - intros. eexists. split; [apply rt_refl | eassumption].
  - intros b0 Red_a0_b0.
    destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
    destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
    exists b2. split; [ | assumption]. apply rt_trans with (y := b1); assumption.
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

  Lemma prove_leq_val_state vSl vm Sm vr Sr
    (G : forall a, fresh_anon Sm a -> fresh_anon Sr a ->
         exists vSm, leq_base vSm Sr,, a |-> vr /\ vSm = Sm,, a |-> vm) :
    leq_val_state_base^* vSl (vm, Sm) ->
    leq_val_state_base^* vSl (vr, Sr).
  Proof.
    intros ?. eapply rt_trans; [eassumption | ]. constructor.
    intros a ? ?. cbn in *. destruct (G a) as (? & ? & ->); [assumption.. | ]. assumption.
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

(* When proving a goal `leq ?vSl (vr, Sr)`, using this tactic create three subgoals:
   1. leq_base ?vSm (Sr,, a |-> v)r
   2. ?vSm = ?Sm,, a |-> ?vm
   3. leq ?vSl (?vm, ?Sm)

   The first goal is used by applying the adequate base rule. Here, a is a fresh anon.
   The second goal is proved by rewriting (with `autorewrite with spath`) then reflexivity.
   The third goal is proved by applying again this tactic, or concluding by reflexivity.

   With this strategy, the states and values ?vSl, ?vSm, ?vm and ?Sm never have to be instantiated
   explicitely.
 *)
Ltac leq_val_state_step :=
  let a := fresh "a" in
  eapply prove_leq_val_state; [intros a ? ?; eexists; split | ].

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
  (* Note: for the moment, we just use natural measures. *)
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

  Lemma preservation_reorg_l (reorg : state -> state -> Prop)
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
