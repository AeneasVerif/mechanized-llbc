Require Import RelationClasses.
Require Import PathToSubtree.

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
   RedBD are generally inductively defined, these terms are constructed by
   Finally, the last goal d0 = d1 is intended to be solved automatically, using the tactic
   prove_states_eq.
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
Class LeBase (B V : Type) := {
  le_base : state B V -> state B V -> Prop;
  well_formed : state B V ->  Prop;
  anon : B;
  le_base_preserves_well_formedness Sl Sr : well_formed Sr -> le_base Sl Sr -> well_formed Sl
}.

(* A restriction of a relation to the set of well-formed states *)
Variant restrict {B V} `{LB : LeBase B V} (red : state B V -> state B V -> Prop) :
  sig (@well_formed _ _ LB) -> sig (@well_formed _ _ LB) -> Prop :=
  | Lift S0 S1 : red (proj1_sig S0) (proj1_sig S1) -> restrict red S0 S1.

Global Instance LeState B V `(LeBase B V) : Le (state B V) (state B V) :=
{ le := refl_trans_closure le_base }.

(* For pair of value and states, we have:
   (v, S) <= (v', S') ::= S,, _ |-> v <= S', _ |-> v'
 *)
Global Instance LeStateVal B V `(LeBase B V) : Le (V * state B V) (V * state B V) :=
{ le := refl_trans_closure
    (fun vS0 vS1 => le_base ((snd vS0),, anon |-> (fst vS0)) ((snd vS1),, anon |-> (fst vS1)))
}.

Global Instance LeStateWF B V `(LB : LeBase B V) :
  Le (@sig (state B V) well_formed) (@sig (state B V) well_formed) :=
{ le := refl_trans_closure
    (fun S0 S1 => le_base (proj1_sig S0) (proj1_sig S1)) }.

Lemma prove_le_state_val B V `(LB : LeBase B V) vl Sl vSm vm Sm vr Sr :
  @le_base _ _ LB vSm (Sr,, (@anon _ _ LB) |-> vr)
  -> vSm = (Sm,, (@anon _ _ LB) |-> vm)
  -> @le _ _ (LeStateVal _ _ LB) (vl, Sl) (vm, Sm)
  -> @le _ _ (LeStateVal _ _ LB) (vl, Sl) (vr, Sr).
Proof. intros. subst. transitivity (vm, Sm); [ | constructor]; assumption. Qed.

(* The issue by directly applying the lemma `preservation_by_base_case` is that it
   obfuscates the relation le, by unfolding it and replacing it with a reflexive transitive
   closure.
   We're going to give similar statements, but these types, the hypothesis uses the relation le.
 *)
Lemma preservation_by_base_case_le_state_le_state_val B V `(LB : LeBase B V)
  (red : state B V -> (V * state B V) -> Prop) :
  forward_simulation (@le_base _ _ LB) (@le _ _ (LeStateVal _ _ LB)) red red
  -> @preservation _ _ (@LeState _ _ LB) (LeStateVal _ _ LB) red.
Proof. apply preservation_by_base_case. Qed.

Lemma preservation_state_implies_preservation_restriction B V `(LB : LeBase B V) Sl Sr :
  le Sl (proj1_sig Sr) -> exists WF_Sl, le (exist well_formed Sl WF_Sl) Sr.
Proof.
  destruct Sr as (Sr & WF_Sr). cbn. intros Hle.
  induction Hle as [Sl | | Sl Sm ? _ IH0 _ IH1].
  - assert (WF_Sl : well_formed Sl).
     (eapply le_base_preserves_well_formedness; eassumption).
    exists WF_Sl. constructor. eassumption.
  - eexists. reflexivity.
  - specialize (IH1 WF_Sr). destruct IH1 as (WF_Sm & ?).
    specialize (IH0 WF_Sm). destruct IH0.
    eexists. etransitivity; eassumption.
Qed.

(* When proving preservation on well-formed states, we can use an additional hypothesis on
   the base case: that the state Sr (such that Sl <= Sr) is well-formed. *)
Lemma preservation_by_base_case_le_state_le_restriction B V `(LB : LeBase B V)
  (red : state B V -> state B V -> Prop) :
  (forall Sr Sr', red Sr Sr' -> @well_formed _ _ LB Sr -> forall Sl, @le_base _ _ LB Sl Sr
   -> exists Sl', @le _ _ (@LeState _ _ LB) Sl' Sr' /\ red Sl Sl')
  -> @preservation _ _ (@LeStateWF _ _ LB) (@LeStateWF _ _ LB) (restrict red).
Proof.
  intros simulation.
  apply preservation_by_base_case.
  intros Sr Sr' red_Sr_Sr' (Sl & WF_Sl) Hle.
  destruct red_Sr_Sr' as [(Sr & WF_Sr) Sr' red_Sr_Sr']. cbn in red_Sr_Sr'.
  edestruct (simulation _ _ red_Sr_Sr') as (Sl' & le_Sl'_Sr' & red_Sl_Sl'); [eassumption.. | ].
  apply preservation_state_implies_preservation_restriction in le_Sl'_Sr'.
  destruct le_Sl'_Sr' as (WF_Sl' & le_Sl'_Sr').
  exists (exist _ Sl' WF_Sl'). split; [ | constructor]; assumption.
Qed.

(* Choose the right `preservation_by_case_XXX` lemma to apply depending on the type: *)
Ltac preservation_by_base_case :=
  match goal with
  | |- @preservation _ _ (@LeState ?B ?V ?LB) (LeStateVal ?B ?V ?LB) ?red =>
      refine (preservation_by_base_case_le_state_le_state_val B V LB red _)
  end.
