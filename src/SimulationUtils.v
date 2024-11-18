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
Lemma complete_square_diagram {A B C D : Type}
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
   and (v, S) <= (v', S') for pairs of value and state. *)
Class LeBase (B V : Type) := {
  le_base : state B V -> state B V -> Prop;
  anon : B;
  le_base_app_last S0 S1 v : le_base S0 S1 -> le_base (S0,, anon |-> v) (S1,, anon |-> v);
}.

Global Instance LeState B V `(LeBase B V) : Le (state B V) (state B V) :=
{ le := refl_trans_closure le_base }.

(* For pair of value and states, we have:
   (v, S) <= (v', S') ::= S,, _ |-> v <= S', _ |-> v'
 *)
Global Instance LeStateVal B V `(LeBase B V) : Le (V * state B V) (V * state B V) :=
{ le := refl_trans_closure
    (fun vS0 vS1 => le_base ((snd vS0),, anon |-> (fst vS0)) ((snd vS1),, anon |-> (fst vS1)))
}.

Lemma prove_le_state_val B V `(LB : LeBase B V) Slvl Sl vl vr Sr :
  @le_base _ _ LB Slvl (Sr,, (@anon _ _ LB) |-> vr)
  -> Slvl = (Sl,, (@anon _ _ LB) |-> vl)
  -> @le _ _ (LeStateVal _ _ LB) (vl, Sl) (vr, Sr).
Proof. intros. subst. constructor. assumption. Qed.

(* A useful lemma to prove preservation when both the states S0 and S1 evaluates to the same value
   v and are unaffected by the evaluation. This corresponds to the following square diagram:
    S0   >=  S1
    |        |
    v        v
   v, S0 >= v, S1
   For example, this can happen in the following contexts:
   - Evaluation of constants
   - Evaluation of copies
   - Evaluation of pointers (&p or &mut p) when the path p is already borrowed.

   In this case, we just have to show that S0 >= S1 (generally, this hypothesis is in the context),
   and S1 -> (v, S1). *)
Lemma complete_square_diagram_by_invariance {B V} `(LB : LeBase B V)
  (Red : state B V -> V * state B  V -> Prop) S0 S1 (v : V) :
  (@le_base _ _ LB S1 S0) -> Red S1 (v, S1)
  -> exists vS, (@le _ _ (LeStateVal _ _ LB) vS (v, S0)) /\ Red S1 vS.
Proof.
  intros. exists (v, S1). split; [ | assumption].
  apply Cl_base, le_base_app_last. assumption.
Qed.

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

(* Choose the right `preservation_by_case_XXX` lemma to apply depending on the type: *)
Ltac preservation_by_base_case :=
  match goal with
  | |- @preservation _ _ (@LeState ?B ?V ?LB) (LeStateVal ?B ?V ?LB) ?red =>
      refine (preservation_by_base_case_le_state_le_state_val B V LB red _)
  end.
