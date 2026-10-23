(* TODO: documentation. *)
Require Import RelationClasses.
Require Import PathToSubtree.
From Stdlib Require Import Arith.
From Stdlib Require Import Relations.
From Stdlib Require Import Lia.

Arguments clos_refl_trans {_}.
Arguments clos_refl {_}.

(* TODO: give a scope. *)
Global Notation "R ^*" := (clos_refl_trans R).
Global Notation "R ^=" := (clos_refl R).

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

Global Instance clos_refl_refl A (R : relation A) : Reflexive R^=.
Proof. intros ?. apply r_refl. Qed.

Global Instance clos_refl_trans_trans A (R : relation A) : Transitive R^*.
Proof. intros ?. apply rt_trans. Qed.

Inductive measured_closure {A : Type} (R : nat -> A -> A -> Prop) : nat -> A -> A -> Prop :=
  | MC_base n x y : R n x y -> measured_closure R n x y
  | MC_refl x : measured_closure R 0 x x
  | MC_trans m n x y z :
      measured_closure R m x y -> measured_closure R n y z -> measured_closure R (m + n) x z
.

(* Now let's assume that a relation <_n is equipped with an integer measure.
 * We can define a reflexive-transitive closure that takes the measure into account. *)
Notation "R ^{ n }" := (measured_closure R n).

Definition equiv_rel {A B} (R0 R1 : A -> B -> Prop) := forall a b, R0 a b <-> R1 a b.

Local Instance equiv_rel_refl A B : Reflexive (@equiv_rel A B).
Proof. intros R a b. reflexivity. Qed.

Lemma measured_closure_equiv A R Rn (H : forall x y : A, R x y <-> exists n, Rn n x y) :
  forall x y, R^* x y <-> exists n, measured_closure Rn n x y.
Proof.
  intros x y. split.
  - induction 1 as [x y | | x y z ? IH0 ? IH1].
    + destruct (H x y) as ((n & ?) & _); [assumption | ]. exists n. constructor. assumption.
    + exists 0. apply MC_refl.
    + destruct IH0 as (m & ?). destruct IH1 as (n & ?). exists (m + n).
      eapply MC_trans; eassumption.
  - intros (n & G). induction G.
    + constructor. firstorder.
    + reflexivity.
    + etransitivity; eassumption.
Qed.

(* TODO: name *)
Lemma measure_closure_cases_left {A} (R : nat -> A -> A -> Prop) n x z :
  R^{n} x z -> x = z /\ n = 0 \/ exists p q y, R^{p} x y /\ R q y z /\ n = p + q.
Proof.
  induction 1 as [n x z | | m n x y z ? IH0 ? IH1].
  - right. exists 0, n, x. auto using MC_refl.
  - auto.
  - destruct IH1 as [(-> & ->) | (p & q & y' & ? & ? & ->)].
    + destruct IH0 as [(-> & ->) | (p & q & y & ? & ? & ->)]; [auto | ].
      right. exists p, q, y. repeat split; try assumption. lia.
    + right. eexists _, q, y'. repeat split; [ | eassumption | ].
      * eapply MC_trans; eassumption.
      * lia.
Qed.

Lemma measure_closure_cases_right {A} (R : nat -> A -> A -> Prop) n x z :
  R^{n} x z -> x = z /\ n = 0 \/ exists p q y, R p x y /\ R^{q} y z /\ n = p + q.
Proof.
  induction 1 as [n x z | | m n x y z ? IH0 ? IH1].
  - right. exists n, 0, z. auto using MC_refl.
  - auto.
  - destruct IH0 as [(<- & ->) | (p & q & y' & ? & ? & ->)].
    + destruct IH1 as [(<- & ->) | (p & q & y & ? & ? & ->)]; [auto | ].
      right. exists p, q, y. auto.
    + right. eexists p, _, y'. repeat split; [eassumption | | ].
      * eapply MC_trans; eassumption.
      * lia.
Qed.

(** Chaining two relations. *)
Definition chain {A B C} (RAB : A -> B -> Prop) (RBC : B -> C -> Prop) a c :=
  exists b, RAB a b /\ RBC b c.

Global Instance reflexive_chain {A} (R S : relation A) `{Reflexive A R} `{Reflexive A S} :
  Reflexive (chain R S).
Proof. intros x. exists x. split; reflexivity. Qed.

(* TODO: new documentation. *)
(* TODO: the direction of the relations LeAB and LeCD are the opposite of the diagrams. *)
(* TODO: The relation RedAC is supposed to be the "right" reduction, and RedBC the "left"
 * reduction, but these relations are reversed. *)
(** The general definition of forward simulation. That means that for all [a >= b] (with
    [a : A] and [b : B]) and [a -> c] (with [c : C]), then there exists [d : D] that completes
    the following square diagram:
<<
b <= a
|    |
v    v
d <= c
>>
    If [A = B] and [C = D], we call it "preservation".

    Genarally,
    - The Le relations is between states ([S <= S']), or pairs of value and state ([(v, S) <= (v', S')]).
    - The Red relations are among the following ones:
      - Evaluation of operands.
      - Evalutaion of rvalues.
      - Store operation.
      - Reorganization.
      - Evaluation of statements.
 *)
Definition forward_simulation {A B C D : Type}
  (LeBA : B -> A -> Prop) (LeDC : D -> C -> Prop)
  (RedAC : A -> C -> Prop) (RedBD : B -> D -> Prop) :=
  forall a c, RedAC a c -> forall b, LeBA b a -> exists d, LeDC d c /\ RedBD b d.

Lemma prove_execution_step {B C D : Type}
  (LeDC : D -> C -> Prop) (RedBD : B -> D -> Prop) Sl S'l S'r :
  RedBD Sl S'l -> LeDC S'l S'r
  -> exists S'l, LeDC S'l S'r /\ RedBD Sl S'l.
Proof. exists S'l. split; assumption. Qed.

Ltac execution_step := eapply prove_execution_step.

(** Generally, to prove preservation when the relation is a reflexive transitive closure, it
    suffices to prove it for the base cases. *)
Lemma preservation_by_base_case {A B : Type}
  {LeA : relation A} {LeB : relation B} `{Reflexive _ LeB} `{Transitive _ LeB}
  {Red : A -> B -> Prop} :
  forward_simulation LeA LeB Red Red ->
  forward_simulation LeA^* LeB Red Red.
Proof.
  intros Hloc a b red_ab a' Le_a_a'. revert b red_ab.
  induction Le_a_a' as [ | | a2 a1 a0 _ IH0 _ IH1].
  - intros. eapply Hloc; eassumption.
  - intros. eexists. split; [reflexivity | eassumption].
  - intros b0 Red_a0_b0.
    destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
    destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
    exists b2. split; [ | assumption]. transitivity b1; assumption.
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

(** Tactics to prove commutation of reorganizations. *)
(* TODO: document it *)
Lemma le_step_right {S} {R : relation S} Sl Sm Sr : R Sm Sr -> R^* Sl Sm -> R^* Sl Sr.
Proof. intros. transitivity Sm; [ | constructor]; assumption. Qed.

Lemma le_step_left {S} {R : relation S} Sl Sm Sr : R Sl Sm -> R^* Sm Sr -> R^* Sl Sr.
Proof. intros. transitivity Sm; [constructor | ]; assumption. Qed.

(** Definition and lemmas for simulation for well-formed states, in HLPL+. *)
Section WellFormedSimulations.
  Context {state : Type}.
  Context (le_base reorg : state -> state -> Prop).
  Context (well_formed : state -> Prop).
  Context (le_base_preserves_wf_r : forall a b, well_formed b -> le_base a b -> well_formed a).
  Context (reorg_preserves_wf : forall a b, reorg a b -> well_formed a -> well_formed b).

  Definition well_formed_forward_simulation_r {B C D : Type}
    (LeBA : B -> state -> Prop) (LeDC : D -> C -> Prop)
    (RedAC : state -> C -> Prop) (RedBD : B -> D -> Prop) :=
    forall a c, well_formed a -> RedAC a c -> forall b, LeBA b a -> exists d, LeDC d c /\ RedBD b d.

  (** Hindley-Rosen lemma for well-formed states in HLPL+. *)
  Context
    (local_commutation : well_formed_forward_simulation_r le_base le_base^= reorg reorg^*).

  Lemma reorgs_preserve_le_base :
    well_formed_forward_simulation_r le_base le_base^= reorg^* reorg^*.
  Proof.
    intros Sr Sl well_formed_Sr reorg_Sr_Sl.
    induction reorg_Sr_Sl
        as [Sr | Sr S'r S''r reorg_Sr_S'r reorg_S'r_S''r IH] using clos_refl_trans_ind_right';
        intros Sl le_Sl_Sr.
    - exists Sl. split; [ | reflexivity]. constructor. assumption.
    - specialize (local_commutation Sr S'r well_formed_Sr reorg_Sr_S'r Sl le_Sl_Sr).
      destruct local_commutation as (S'l & le_S'l_S'r & reorg_Sl_S'l).
      destruct le_S'l_S'r as [S'r le_S'l_S'r | ]; subst.
      + edestruct IH as (S''l & le_S''l_S''l & reorg_S'l_S''l).
        { eapply reorg_preserves_wf; eassumption. }
        { exact le_S'l_S'r. }
        exists S''l. split; [assumption | ]. transitivity S'l; assumption.
      + exists S''r. split; [reflexivity | ]. transitivity S'l; eassumption.
  Qed.

  Lemma global_commutation_hlpl_plus :
    well_formed_forward_simulation_r le_base^* le_base^* reorg^* reorg^*.
  Proof.
    intros Sr S'r well_formed_Sr reorg_Sr_S'r Sl le_Sl_Sr.
    revert S'r reorg_Sr_S'r.
    induction le_Sl_Sr
        as [Sr | Sl Sm Sr le_Sl_Sm IH le_Sm_Sr]
        using clos_refl_trans_ind_left';
        intros S'r reorg_Sr_S'r.
    - exists S'r. split; [reflexivity | assumption].
    - edestruct reorgs_preserve_le_base as (S'm & le_S'm_S'r%clos_r_clos_rt & reorg_Sm_S'm);
        [eassumption.. | ].
      edestruct IH as (S'l & le_S'l_S'm & reorg_Sl_S'l); eauto.
      exists S'l. split; [ | assumption]. transitivity S'm; assumption.
  Qed.
End WellFormedSimulations.

(** Simulation principles for LLBC\# and LLBC+, taking into account equivalence. *)
Section SymbolicSimulations.
  Context {state : Type}.
  Context {equiv : state -> state -> Prop}.
  Context `{Reflexive _ equiv}.
  Context `{Transitive _ equiv}.
  Context (le_base : state -> state -> Prop).
  Context (sim_le_base_equiv : forward_simulation le_base le_base equiv equiv).

  Definition le := chain equiv le_base^*.

  Global Instance reflexive_le : Reflexive le.
  Proof. intros x. exists x. split; reflexivity. Qed.

  Lemma sim_le_equiv : forward_simulation le_base^* le_base^* equiv equiv.
  Proof.
    intros a b red_ab a' Le_a_a'. revert b red_ab.
    induction Le_a_a' as [? ? Le_a_a' | | a2 a1 a0 _ IH0 _ IH1].
    - intros. specialize (sim_le_base_equiv _ _ red_ab _ Le_a_a').
      destruct sim_le_base_equiv as (d & ? & ?). exists d. split; [constructor | ]; assumption.
    - intros. eexists. split; [reflexivity | eassumption].
    - intros b0 Red_a0_b0.
      destruct (IH1 _ Red_a0_b0) as (b1 & ? & Red_a1_b1).
      destruct (IH0 _ Red_a1_b1) as (b2 & ? & Red_a2_b2).
      exists b2. split; [ | assumption]. transitivity b1; assumption.
  Qed.

  Global Instance transitive_le : Transitive le.
  Proof.
    intros x y z (y' & ? & le_y'_y) (z' & equiv_y_z' & ?).
    pose proof (sim_le_equiv _ _ equiv_y_z' _ le_y'_y) as G.
    destruct G as (z'' & ? & ?). exists z''. split.
    - transitivity y'; assumption.
    - transitivity z'; assumption.
  Qed.

  Context (measure : state -> nat).
  Context (reorg : state -> state -> Prop).
  Context (reorg_n : nat -> state -> state -> Prop).
  Context (le_base_n : nat -> state -> state -> Prop).
  Definition le_n n := chain equiv (measured_closure le_base_n n).

  Hypothesis (le_decreasing : forall n a b, le_base_n n a b -> measure a < measure b + n).
  Hypothesis (reorg_decreasing : forall n a b, reorg_n n a b -> measure b + n < measure a).
  (*Hypothesis (equiv_measure : forall S S', equiv S S' -> measure S = measure S').*)

  Lemma reorgs_decreasing n S S' : reorg_n^{n} S S' -> measure S' + n <= measure S.
  Proof. induction 1; [ | lia..]. apply Nat.lt_le_incl, reorg_decreasing. assumption. Qed.

  Hypothesis (reorg_preserves_equiv :
    forall n, forward_simulation equiv equiv (reorg_n n) (reorg_n n)
  ).

  Lemma reorgs_preserve_equiv n :
    forward_simulation equiv equiv (reorg_n^{n}) (reorg_n^{n}).
  Proof.
    intros a b. induction 1 as [? ? ? Hreorg | | p q a0 a1 a2 ? IH0 ? IH1].
    - intros ? Hequiv. specialize (reorg_preserves_equiv _ _ _ Hreorg _ Hequiv).
      destruct reorg_preserves_equiv as (d & ? & ?). exists d.
      split; [ | constructor]; assumption.
    - intros. eexists. split; [eassumption | apply MC_refl].
    - intros b0 equiv_b0_a0.
      destruct (IH0 _ equiv_b0_a0) as (b1 & Red_b1_a1 & ?).
      destruct (IH1 _ Red_b1_a1) as (b2 & Red_b2_a1 & ?).
      exists b2. split; [assumption | ]. eapply MC_trans; eassumption.
  Qed.

  Context (sim_equiv_le_base_n :
    forall n, forward_simulation (le_base_n n) (le_base_n n) equiv equiv).

  Lemma le_n_cases n Sl Sr (G : le_n n Sl Sr) :
    (equiv Sl Sr) \/
    (exists p q Sm, le_n p Sl Sm /\ le_base_n q Sm Sr /\ n = p + q).
  Proof.
    destruct G as (Sr' & Gequiv & Gcases%measure_closure_cases_left).
    destruct Gcases as [(-> & ->) | (p & q & Sm & ? & G & ->)].
    - left. assumption.
    - right. exists p, q, Sm. firstorder.
  Qed.

  Lemma sim_equiv_le_n n : forward_simulation (le_base_n^{n}) (le_base_n^{n}) equiv equiv.
  Proof.
    intros a b equiv_ab a' Le_a'_a. revert b equiv_ab.
    induction Le_a'_a as [n ? ? Le_a'_a | | p q a2 a1 a0 _ IH0 _ IH1].
    - intros. specialize (sim_equiv_le_base_n n _ _ equiv_ab _ Le_a'_a).
      destruct sim_equiv_le_base_n as (d & ? & ?). exists d. split; [constructor | ]; assumption.
    - intros. eexists. split; [apply MC_refl | eassumption].
    - intros b0 equiv_a0_b0.
      destruct (IH1 _ equiv_a0_b0) as (b1 & ? & equiv_a1_b1).
      destruct (IH0 _ equiv_a1_b1) as (b2 & ? & equiv_a2_b2).
      exists b2. split; [ | assumption]. eapply MC_trans; eassumption.
  Qed.

  Lemma le_n_trans Sl Sm Sr p q : le_n p Sl Sm -> le_n q Sm Sr -> le_n (p + q) Sl Sr.
  Proof.
    intros (S'l & ? & le_S'l_Sm) (S'm & equiv_Sm_S'm & ?).
    pose proof (sim_equiv_le_n p _ _ equiv_Sm_S'm _ le_S'l_Sm) as (S''l & ? & ?).
    exists S''l. split.
    - transitivity S'l; assumption.
    - eapply MC_trans; eassumption.
  Qed.

  Context (local_commutation :
    forall p Sh q S'h, reorg_n q Sh S'h -> forall Sl, le_base_n p Sl Sh ->
    exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ r + s <= p + q
  ).

  Lemma measured_preservation_reorg :
    forall p Sh q S'h, reorg_n^{q} Sh S'h -> forall Sl, le_n p Sl Sh ->
    exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ r + s <= p + q.
  Proof.
    intros p Sr. remember (measure Sr + p) as N eqn:EQN.
    revert p Sr EQN. induction N as [? IH] using lt_wf_ind.
    intros ? Sr -> q S''r reorg_Sr_S''r Sl le_Sl_Sr.
    destruct (measure_closure_cases_right _ _ _ _ reorg_Sr_S''r)
      as [(-> & ->) | (? & ? & S'r & reorg_Sr_S'r & ? & ->)].
    { eexists _, _, _. repeat split; [eassumption | apply MC_refl | lia]. }
    apply le_n_cases in le_Sl_Sr.
    destruct le_Sl_Sr as [Hequiv | (? & ? & Sm & le_Sl_Sm & le_Sm_Sr & ->)].
    { eapply reorgs_preserve_equiv in Hequiv; [ | exact reorg_Sr_S''r].
      destruct Hequiv as (Sl' & ? & ?).
      eexists 0, _, Sl'. repeat split; [ | eassumption | lia].
      eexists. split; [eassumption | apply MC_refl]. }
    specialize (local_commutation _ _ _ _ reorg_Sr_S'r _ le_Sm_Sr).
    destruct local_commutation as (? & ? & S'm & le_S'm_S'r & reorg_Sm_S'm & ?).
    pose proof (le_decreasing _ _ _ le_Sm_Sr).
    edestruct IH with (Sr := Sm) as (? & ? & S'l & le_S'l_S'm & reorg_Sl_S'l & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    pose proof (reorg_decreasing _ _ _ reorg_Sr_S'r).
    edestruct IH with (Sr := S'r);
      [ | reflexivity | eassumption | eapply le_n_trans; eassumption | ];
      [lia | ].
    edestruct IH with (Sr := S'r) as (? & ? & S''m & ? & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    pose proof (reorgs_decreasing _ _ _ reorg_Sm_S'm).
    edestruct IH with (Sr := S'm) as (? & ? & S''l & ? & ? & ?);
      [ | reflexivity | eassumption.. | ];
      [lia | ].
    eexists _, _, S''l. split; [ | split].
    - eapply le_n_trans; eassumption.
    - eapply MC_trans; eassumption.
    - lia.
  Qed.

  Context (le_base_is_le_base_n : forall Sl Sr, le_base Sl Sr <-> exists n, le_base_n n Sl Sr).
  Context (reorg_is_reorg_n : forall Sl Sr, reorg Sl Sr <-> exists n, reorg_n n Sl Sr).

  Lemma le_n_is_le Sl Sr : le Sl Sr <-> exists n, le_n n Sl Sr.
  Proof.
    split.
    - intros (Sl' & Hequiv & Hle).
      rewrite measured_closure_equiv in Hle by exact le_base_is_le_base_n.
      destruct Hle as (n & Hle). exists n, Sl'. auto.
    - intros (n & Sl' & Hequiv & Hle). exists Sl'. split; [assumption | ].
      rewrite measured_closure_equiv by exact le_base_is_le_base_n.
      exists n. exact Hle.
  Qed.

  Corollary global_commutation_llbc_plus : forward_simulation le le reorg^* reorg^*.
  Proof.
    intros Sr S'l reorg_Sr_S'r Sl le_Sl_Sr.
    rewrite le_n_is_le in le_Sl_Sr.
    destruct le_Sl_Sr as (p & le_n_Sl_Sr).
    rewrite measured_closure_equiv in reorg_Sr_S'r by exact reorg_is_reorg_n.
    destruct reorg_Sr_S'r as (q & reorgs_n_Sr_S'r).
    pose proof (measured_preservation_reorg _ _ _ _ reorgs_n_Sr_S'r _ le_n_Sl_Sr)
      as (r & s & Sl' & ? & ? & _).
    exists Sl'. split.
    - rewrite le_n_is_le. exists r. assumption.
    - rewrite measured_closure_equiv by exact reorg_is_reorg_n. exists s. assumption.
  Qed.
End SymbolicSimulations.

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
