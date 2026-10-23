From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import pmap.
From rustc Require Import OptionMonad.
Require Import base SimulationUtils PathToSubtree lang.
Require Import Symbolic_states Symbolic_relations.
(* We import the << LLBC_plus >> module after << LLBC_sharp >> so the LLBC+ definition
   of [eval_stmt] overwrites the LLBC# definition. *)
Require Import LLBC_sharp.
Require Import LLBC_plus.

Local Open Scope llbc_sharp_scope.
Local Open Scope llbc_plus_scope.

(** * Tactics to structure the proof. *)
Lemma le_val_state_ut_step_left vSl vSm vSh :
  le_val_state_base vSl vSm -> le_val_state_ut vSm vSh -> le_val_state_ut vSl vSh.
Proof.
  intros. transitivity vSm; [ | assumption].
  exists vSl. split; [reflexivity | constructor; assumption].
Qed.

(** The goal is to complete a simulation diagram, that is a property of the form:
   [(exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ r + s <= p + q)]
   Note that this property contains a weight inequality [r + s <= p + q]. The idea is taht we
   are going to perform reorganization and abstraction steps that have weight. The total weight
   is stored in an "accumulator" acc. More generally, we are going to prove the property:
   [(exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ acc + r + s <= p + q)]

   To complete a diagram, we first perform reorganization steps using tactic
   tactic [reorg_step], each time incremeting the accumulator. Once all steps have been
   performed, we apply [reorg_done], leaving a goal of the form:
   [(exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ acc + r + s <= p + q)]

   Then, we can do abstraction steps with [eapply prove_le_step] (or occasionally
   [eapply prove_le_steps]), each time incrementing the accumulator. Once all steps have been
   performed, we apply [le_done], leaving two goals: an equivalence (between [S'h] and the state
   obtained from [Sl] by successive reorganization and abstraction steps) and the inequality
   [acc <= p + q].
 *)
(** TODO: the lemmas [prove_le_step] and [prove_le_step_0] should be part of the
   tactic [le_step_left]. *)
Lemma prove_reorg_steps acc q Sl S'l S'h n :
  reorg_n^{q} Sl S'l ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} S'l S''l /\ (acc + q) + r + s <= n) ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} Sl S''l /\ acc + r + s <= n).
Proof.
  intros ? (r & s & S''l & ? & ? & ?). exists r, (q + s), S''l.
  split; [assumption | ]. split; [ | lia]. eapply MC_trans; eassumption.
Qed.

(* The parameter [acc] is the accumulator. The weight [q] of the performed reorganization step
  is added to the accumulator. *)
Lemma prove_reorg_step acc q Sl S'l S'h n :
  reorg_n q Sl S'l ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} S'l S''l /\ (acc + q) + r + s <= n) ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} Sl S''l /\ acc + r + s <= n).
Proof. intros ?. apply prove_reorg_steps. constructor. assumption. Qed.

(* This lemma is applied when an accumulator has not yet been introduced. It is initalized with
  the weight parameter [q] of the reorganization rule. *)
Lemma prove_reorg_step_0 q Sl S'l S'h n :
  reorg_n q Sl S'l ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} S'l S''l /\ q + r + s <= n) ->
  (exists r s S''l, le_n r S''l S'h /\ reorg_n^{s} Sl S''l /\ r + s <= n).
Proof. apply (prove_reorg_step 0). Qed.

Lemma reorg_done acc n Sl S'h :
  (exists r, le_n r Sl S'h /\ acc + r <= n) ->
  (exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ acc + r + s <= n).
Proof.
  intros (r & ? & ?). exists r, 0, Sl. repeat split; [assumption | apply MC_refl | lia].
Qed.

(* This tactic is used when no accumulator has been introduced. *)
Lemma reorg_done_0 n Sl S'h :
  (exists r, le_n r Sl S'h /\ r <= n) ->
  (exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ r + s <= n).
Proof. apply (reorg_done 0). Qed.

Lemma le_n_steps acc p n Sl Sm Sr :
  le_state_base_n^{p} Sl Sm -> (exists r, le_n r Sm Sr /\ (acc + p) + r <= n) ->
  exists r, le_n r Sl Sr /\ acc + r <= n.
Proof.
  intros H (r & (Sr' & G & ?) & ?).
  destruct (sim_equiv_le_n _ le_n_equiv_states_commute _ _ _ G _ H) as (Sl' & ? & ?).
  exists (p + r). split; [ | lia]. exists Sl'. split; [assumption | ].
  eapply MC_trans; eassumption.
Qed.

Lemma le_n_step acc p n Sl Sm Sr :
  le_state_base_n p Sl Sm -> (exists r, le_n r Sm Sr /\ (acc + p) + r <= n) ->
  exists r, le_n r Sl Sr /\ acc + r <= n.
Proof. intros ?. apply le_n_steps. constructor. assumption. Qed.

(** This lemma is applied when an accumulator has not yet been introduced. It is initalized with
  the weight parameter [p] of the abstraction rule. *)
Lemma le_n_step_0 p n Sl Sm Sr :
  le_state_base_n p Sl Sm -> (exists r, le_n r Sm Sr /\ p + r <= n) ->
  exists r, le_n r Sl Sr /\ r <= n.
Proof. apply (le_n_step 0). Qed.

Lemma le_done acc n Sl Sr :
  equiv_states Sl Sr -> acc <= n -> exists r, le_n r Sl Sr /\ acc + r <= n.
Proof.
  intros ? ?. exists 0. split; [ | lia]. exists Sr. split; [assumption | apply MC_refl].
Qed.

Lemma prove_le_n n Sl Sr Sr' :
  le_state_base_n^{n} Sl Sr -> equiv_states Sr Sr' -> le_n n Sl Sr'.
Proof.
  intros H G.
  pose proof le_n_equiv_states_commute as Hsim.
  eapply sim_equiv_le_n in Hsim. specialize (Hsim _ _ G _ H).
  destruct Hsim as (Sl' & ? & ?). exists Sl'. split; assumption.
Qed.

Ltac reorg_step := first [eapply prove_reorg_step | eapply prove_reorg_step_0].
Ltac reorg_steps := eapply prove_reorg_steps.
Ltac reorg_done := first [apply reorg_done | apply reorg_done_0].
Ltac le_done := apply le_done.

(** This tactic is used to prove a goal of the form [(vl, Sl) < ?vSr] without
    exhibiting the existential variable [?vSr]. *)
Ltac le_step_left :=
  lazymatch goal with
  | |- exists r, le_n r ?Sl ?Sr /\ r <= ?n => eapply le_n_step_0
  | |- exists r, le_n r ?Sl ?Sr /\ ?acc + r <= ?n => eapply le_n_step
  | |- le_val_state_ut _ _ => eapply le_val_state_ut_step_left
  | |- ?le_star ?Sl ?Sr => eapply le_step_left
  end.

(** * Simulation proofs for place evaluation. *)
Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Lemma eval_path_preservation Sl Sr perm p R :
  (forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) ->
  forward_simulation R R (eval_path Sr perm p) (eval_path Sl perm p).
Proof.
  intros preservation_proj. intros ? ? Heval_path.
  induction Heval_path.
  - intros ?. intros ?. eexists. split; [eassumption | constructor].
  - intros pi_l HR.
    edestruct preservation_proj as (pi_l' & ? & ?); [eassumption.. | ].
    edestruct IHHeval_path as (pi_l'' & ? & ?); [eassumption | ].
    exists pi_l''. split; [ | econstructor]; eassumption.
Qed.

(* This lemma is use to prove preservation of place evaluation for a relation rule Sl < Sr.
 * We prove that if p evaluates to a spath pi_r on Sr, then it also evaluates for a spath
 * pi_l on the left, with R pi_l pi_r.
 * The relation R depends on the rule, but for most rules it is simply going to be the equality. *)
Lemma eval_place_preservation Sl Sr perm p (R : spath -> spath -> Prop)
  (* Initial case: the relation R must be preserved for all spath corresponding to a variable. *)
  (R_nil : forall x, R (encode_var x, []) (encode_var x, []))
  (* All of the variables of Sr are variables of Sl.
   * Since most of the time, Sr is Sl with alterations on region abstractions, anonymous variables
   * or by sset, this is always true. *)
  (dom_eq : dom (vars Sl) = dom (vars Sr))
  (Hsim : forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) :
  forall pi_r, eval_place Sr perm p pi_r -> exists pi_l, R pi_l pi_r /\ eval_place Sl perm p pi_l.
Proof.
  intros pi_r ((? & G%mk_is_Some & _) & Heval_path).
  cbn in G. unfold encode_var in G. rewrite !sum_maps_lookup_l in G.
  rewrite <-elem_of_dom, <-dom_eq, elem_of_dom, <-get_at_var in G. destruct G as (? & ?).
  eapply eval_path_preservation in Heval_path; [ | eassumption].
  edestruct Heval_path as (pi_l' & ? & ?); [apply R_nil | ].
  exists pi_l'. split; [assumption | ]. split; [ | assumption].
  eexists. split; [eassumption | constructor].
Qed.

Lemma sset_preserves_vars_dom S sp v : dom (vars (S.[sp <- v])) = dom (vars S).
Proof.
  unfold sset. unfold alter_at_accessor. cbn. repeat autodestruct.
  intros. apply dom_alter_L.
Qed.

Lemma add_anon_preserves_vars_dom S a v : dom (vars (S,, a |-> v)) = dom (vars S).
Proof. reflexivity. Qed.

Lemma eval_place_ToSymbolic S sp p pi ty perm
  (Htype : is_of_type ty (S.[sp]))
  (H : (S.[sp <- VSymbolic ty]) |-{p} p =>^{perm} pi) :
  S |-{p} p =>^{perm} pi /\ ~strict_prefix sp pi.
Proof.
  pose proof (valid_pi := H). apply eval_place_valid in valid_pi.
  eapply eval_place_preservation with (R := eq) in H.
  - split.
    + destruct H as (? & -> & H). exact H.
    + eapply get_zeroary_not_strict_prefix'; [eassumption | reflexivity].
  - reflexivity.
  - symmetry. apply sset_preserves_vars_dom.
  - intros proj pi_r pi_r' Heval_proj ? ->. eexists. split; [reflexivity | ].
    inversion Heval_proj; subst.
    + autorewrite with spath in get_q. eapply E_Deref_MutBorrow; eassumption.
Qed.

(* While we only have mutable loans and borrows, we cannot "jump into" an abstraction. When we
 * introduce shared loans/borrows, we need to redefine this relation. *)
Definition rel_ToAbs a i (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ fst p <> anon_accessor a.

(* Note: the hypothesis [no_borrow] is not necessary to prove this lemma. *)
(* The hypothesis [no_loan] is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_ToAbs S a i v A p perm
  (fresh_a : fresh_anon S a)
  (fresh_i : fresh_abstraction S i)
  (Hto_abs : to_abs v A) :
  forall pi_r, (S,,, i |-> A) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_ToAbs a i pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; [now eapply var_not_in_abstraction | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'.
    inversion Heval_proj; subst. repeat split; auto.
    autorewrite with spath in get_q. econstructor; autorewrite with spath; eassumption.
Qed.

(* Let Sl < Sr be two states in relation. Let's assume that there is a difference of one anonymous
 * variables between the two states.
 * Ex: Sr = Sl.[p <- v],, a |- w, or Sr = remove_anon a Sl
 * Any valid spath in Sl and Sr cannot be in the anonymous variable a.
 * The relation "rel_change_anon a" relates two equal paths in Sl and Sr that are not in a. *)
Definition rel_change_anon a (p q : spath) := p = q /\ fst p <> anon_accessor a.

(* Relates two equal paths pi_l and pi_r such that:
 * - Neither is in the anonymous variable a.
 * - Neither is under a given spath sp. *)
(* Used by the rules Le_MoveValue and Le_Fresh_MutLoan. *)
Definition rel_change_anon_not_in_spath sp a pi_l pi_r :=
  rel_change_anon a pi_l pi_r /\ ~strict_prefix sp pi_l.

(* Note: the hypothesis [no_borrow] is not necessary to prove this lemma. *)
(* The hypothesis [no_loan] is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_RemoveAnon S perm a v p
  (fresh_a : fresh_anon S a)
  (no_loan : not_contains_loan v) :
  forall pi_r, S |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  eapply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + autorewrite with spath in get_q.
      repeat split; try assumption.
      eapply E_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

(* Take Sr = Sl.[sp <- bot],, a |-> Sl.[sp] the left state. Relation between the evaluation
 * pi_l in Sl and pi_r in Sr: *)
Definition rel_MoveValue_imm sp a pi_l pi_r :=
  (pi_l = pi_r /\ ~strict_prefix sp pi_l /\ fst pi_l <> encode_anon a) \/
  (* If there is a (non-outer) mutable loan in S.[sp], it's possible to evaluate a place p there.
   * What happens is that in Sl, pi_l is under sp whereas in Sr, pi_r is in the newly added
   * anonymous variable. *)
  (* However, this is only possible when evaluating in mode Imm. *)
  (exists r, pi_l = sp +++ r /\ pi_r = (encode_anon a, r)).

Lemma eval_place_MoveValue_imm S sp a p
  (fresh_a : fresh_anon S a)
  (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{Imm} pi_r ->
  exists pi_l, rel_MoveValue_imm sp a pi_l pi_r /\ S |-{p} p =>^{Imm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. left. repeat split; [apply not_strict_prefix_nil | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as [(-> & ? & ?) | (r & -> & ->)].
      * rewrite sget_add_anon in get_q by assumption.
        exists (pi_r +++ [0]). split.
        -- left. repeat split; [solve_comp | assumption].
        -- eapply E_Deref_MutBorrow. assumption.
           autorewrite with spath in get_q. exact get_q.
      * exists ((sp +++ r) +++ [0]). split.
        --- right. exists (r ++ [0]). split; autorewrite with spath; reflexivity.
        --- eapply E_Deref_MutBorrow. assumption.
            autorewrite with spath in get_q. exact get_q.
Qed.

Lemma eval_place_change_anon_not_in_spath S sp a perm p
  (Hperm : perm <> Imm) (fresh_a : fresh_anon S a) (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. repeat split; [inversion 1 | apply not_strict_prefix_nil].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as ((-> & ?) & ?).
      rewrite sget_add_anon in get_q by assumption.
      exists (pi_r +++ [0]). split.
      * repeat split; [assumption | solve_comp].
      * eapply E_Deref_MutBorrow. assumption.
         autorewrite with spath in get_q. exact get_q.
Qed.

Definition rel_MergeAbs i j (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ ~in_abstraction j (fst p) /\ ~in_abstraction i (fst q).

Lemma eval_place_MergeAbs S i j A B C perm p
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) (diff : i <> j) :
    forall pi_r, (S,,, i |-> C) |-{p} p =>^{perm} pi_r ->
    exists pi_l, rel_MergeAbs i j pi_l pi_r /\ (S,,, i |-> A,,, j |-> B) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; intros (? & ?); easy.
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as (-> & ? & ? & ?). exists (pi_r +++ [0]).
      repeat split; [assumption.. | ].
      autorewrite with spath in get_q.
      eapply E_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_Fresh_MutLoan S sp l a perm p ty :
  forall pi_r, (S.[sp <- loan^m(ty, l)],, a |-> borrow^m(l, S.[sp])) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; auto with spath.
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? ((-> & ?) & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + (* We must perform a single rewrite in order to have the information required to prove
       * ~prefix sp pi_r. *)
      rewrite sget_add_anon in get_q by assumption.
      assert (~prefix sp pi_r) by solve_comp.
      autorewrite with spath in get_q.
      repeat split; [assumption | solve_comp | ].
      eapply E_Deref_MutBorrow; eassumption.
Qed.

Lemma eval_place_Reborrow_MutBorrow S sp l0 l1 a perm p ty
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0)) pi_r :
  (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(ty, l1))) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  revert pi_r. apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption.
      destruct (decide (sp = pi_r)) as [<- | ].
      * eapply E_Deref_MutBorrow; eassumption.
      * autorewrite with spath in get_q.
        (* Note: this rewrite take up to 2s, with 80% of time spent on eauto with spath. *)
        eapply E_Deref_MutBorrow; eassumption.
Qed.

Lemma eval_place_Reborrow_MutBorrow_Mov S sp l0 l1 a p ty
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0)) pi_r :
  (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(ty, l1))) |-{p} p =>^{Mov} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{Mov} pi_l.
Proof.
  revert pi_r. apply eval_place_preservation.
  - split; [split; [reflexivity | inversion 1] | apply not_strict_prefix_nil].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? ((-> & ?) & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; [assumption | solve_comp | ].
      destruct (decide (sp = pi_r)) as [<- | ].
      * eapply E_Deref_MutBorrow; eassumption.
      * autorewrite with spath in get_q.
        (* Note: this rewrite take up to 2s, with 80% of time spent on eauto with spath. *)
        eapply E_Deref_MutBorrow; eassumption.
Qed.

(* When we add shared borrows and loans, this lemma becomes false when v contains a loan that can
 * be accessed in *)
Lemma eval_place_add_anon S a perm p v :
  forall pi_r, (S,, a |-> v) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption. autorewrite with spath in get_q.
      eapply E_Deref_MutBorrow; eassumption.
Qed.

Definition rel_Borrow_Abstraction i j a (p q : spath) :=
  p = q /\ fst p <> anon_accessor a /\ fst p <> encode_abstraction (i, j).

Definition rel_Borrow_Abstraction_Mut a (p q : spath) :=
  p = q /\ fst p <> anon_accessor a /\ not_in_abstraction p.

Lemma eval_place_Borrow_Abstraction S i j a A perm p l' ty
  (fresh_i : fresh_abstraction S i) (fresh_j : lookup j A = None)
  (fresh_l' : is_fresh l' (S,,, i |-> A)) :
  forall pi_r, (S,,, i |-> insert j (loan^m(ty, l')) A,, a |-> borrow^m(l', VSymbolic ty)) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Borrow_Abstraction i j a pi_l pi_r /\
               S,,, i |-> A |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | split; inversion 1].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'. destruct Heval_proj.
    + autorewrite with spath in get_q. repeat split; try assumption.
      eapply E_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_Borrow_Abstraction_Mut S i j a A perm p l' ty (Hperm : perm <> Imm)
  (fresh_i : fresh_abstraction S i) (fresh_j : lookup j A = None)
  (fresh_l' : is_fresh l' (S,,, i |-> A)) :
  forall pi_r, (S,,, i |-> insert j (loan^m(ty, l')) A,, a |-> borrow^m(l', VSymbolic ty)) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Borrow_Abstraction_Mut a pi_l pi_r /\
               S,,, i |-> A |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | split; [inversion 1 | eapply var_not_in_abstraction; reflexivity] ].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'. destruct Heval_proj.
    + autorewrite with spath in get_q. repeat split; try assumption.
      eapply E_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Definition rel_Abs_ClearValue i j (p q : spath) := p = q /\ fst p <> encode_abstraction (i, j).

Definition rel_Abs_ClearValue_Mut (p q : spath) := p = q /\ not_in_abstraction p.

Lemma eval_place_Abs_ClearValue S i j v A perm p :
  forall pi_r, S,,, i |-> A |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Abs_ClearValue i j pi_l pi_r /\ S,,, i |-> insert j v A |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'. destruct Heval_proj.
    + repeat split; try assumption.
      eapply E_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_Abs_ClearValue_Mut S i j v A perm p (Hperm : perm <> Imm) :
  forall pi_r, S,,, i |-> A |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Abs_ClearValue_Mut pi_l pi_r /\ S,,, i |-> insert j v A |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | eapply var_not_in_abstraction; reflexivity].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'. destruct Heval_proj.
    + repeat split; try assumption.
      eapply E_Deref_MutBorrow; autorewrite with spath in *; eassumption.
Qed.

(** Suppose that [Sl < Sr], and that p evaluates to a spath [pi] in [Sr]
   ([Sr |-{p} p =>^{perm} pi]).
    This tactic chooses the right lemmas to apply in order to prove that [p] reduces to a spath [pi'] in [Sl], and generates facts about [pi'].
   Finally, it proves that [pi] is valid in [Sr], and clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  let eval_p_in_Sl := fresh "eval_p_in_Sl" in
  let pi_l := fresh "pi_l" in
  let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
  lazymatch goal with

  (* Case [Le_ToSymbolic]: *)
  | Htype : (is_of_type ?ty (?S.[?sp])),
    H : (?S.[?sp <- VSymbolic ?ty]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply (eval_place_ToSymbolic _ _ _ _ _ _ Htype) in H;
        destruct H as (eval_p_in_Sl & ?)

  (* Case [Le_ToAbs]: *)
  | fresh_a : fresh_anon ?S ?a,
    fresh_i : fresh_abstraction ?S ?i,
    Hto_abs : to_abs ?v ?A,
    Heval : (?S,,, ?i |-> ?A) |-{p} ?p =>^{?perm} ?pi |- _ =>
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        (* Proving that pi is a valid spath of (remove_anon a S),,, i |-> A *)
        pose proof (eval_place_valid _ _ _ _ Heval) as valid_pi;
        apply (eval_place_ToAbs _ _ _ _ _ _ _ fresh_a fresh_i Hto_abs) in Heval;
        destruct Heval as (? & (-> & pi_not_in_abstraction & pi_not_in_a) & eval_p_in_Sl);
        (* We can then prove that pi is a valid spath of (remove_anon a S) *)
        rewrite (not_in_abstraction_valid_spath _ _ _ _ pi_not_in_abstraction) in valid_pi

  (* Case MoveValue *)
  (* Preservation of place evaluation with permission Imm. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{Imm} ?pi |- _ =>
        apply (eval_place_MoveValue_imm _ _ _ _ fresh_a valid_sp Hnot_in_abstraction) in H;
        destruct H as (pi_l & rel_pi_l_pi_r & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Mut or Mov. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_change_anon_not_in_spath in H;[ | discriminate | assumption..];
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  (* Case [Le_MergeAbs]: *)
  | fresh_i : fresh_abstraction ?S ?i, fresh_j : fresh_abstraction ?S ?j,
    Hmerge : merge_abstractions ?A ?B ?C, diff : ?i <> ?j,
    Heval : (?S,,, ?i |-> ?C) |-{p} ?p =>^{?perm} ?pi_r
    |- _ =>
        apply (eval_place_MergeAbs _ _ _ _ _ _ _ _ fresh_i fresh_j Hmerge diff) in Heval;
        destruct Heval as (? & (-> & ? & ? & ?) & eval_p_in_Sl)

  (* Case Fresh_MutLoan *)
  | H : (?S.[?sp <- loan^m(?ty, ?l)],, ?a |-> borrow^m(?l, ?S.[?sp])) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_Fresh_MutLoan in H;
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  (* Case Reborrow_MutBorrow *)
  (* Preservation of place evaluation with permission Mov. *)
  | eval_p_in_Sr : (rename_mut_borrow ?S ?sp ?l1,, ?a |-> borrow^m(?l0, loan^m(?ty, ?l1))) |-{p} ?p =>^{Mov} ?pi |- _ =>
        apply eval_place_Reborrow_MutBorrow_Mov in eval_p_in_Sr; [ | assumption];
        destruct eval_p_in_Sr as (? & ((-> & ?) & ?) & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Imm or Mut. *)
  | eval_p_in_Sr : (rename_mut_borrow ?S ?sp ?l1,, ?a |-> borrow^m(?l0, loan^m(?ty, ?l1))) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_Reborrow_MutBorrow in eval_p_in_Sr; [ | assumption];
        destruct eval_p_in_Sr as (? & (-> & ?) & eval_p_in_Sl)

  (* Case Borrow-Abstraction *)
  (* Preservation of place evaluation with permission [Imm]. *)
  | eval_p_in_Sr : (?S,,, ?i |-> insert ?j (loan^m (?ty, ?l)) ?A,, ?a |-> borrow^m(?l, VSymbolic ?ty)) |-{p} ?p =>^{Imm} ?pi |- _ =>
      apply eval_place_Borrow_Abstraction in eval_p_in_Sr; [ | assumption..];
      destruct eval_p_in_Sr as (? & (-> & ? & ?) & eval_p_in_Sl)
  (* Preservation of place evaluation with permission [Mut] or [Mov]. *)
  | eval_p_in_Sr : (?S,,, ?i |-> insert ?j (loan^m (?ty, ?l)) ?A,, ?a |-> borrow^m(?l, VSymbolic ?ty)) |-{p} ?p =>^{?k} ?pi |- _ =>
      apply eval_place_Borrow_Abstraction_Mut in eval_p_in_Sr;
        [ | discriminate | assumption.. | not_contains];
      destruct eval_p_in_Sr as (? & (-> & ? & ?) & eval_p_in_Sl)

  (* Case Abs_ClearValue *)
  | no_loan : not_contains_loan ?v,
    Heval : ?S,,,  ?i |-> ?A |-{p} ?p =>^{Imm} ?pi_r |- _ =>
        eapply eval_place_Abs_ClearValue in Heval;
        destruct Heval as (? & (-> & ?) & eval_p_in_Sl)
  | no_loan : not_contains_loan ?v,
    Heval : ?S,,,  ?i |-> ?A |-{p} ?p =>^{?perm} ?pi_r |- _ =>
        eapply eval_place_Abs_ClearValue_Mut in Heval; [ | discriminate];
        destruct Heval as (? & (-> & ?) & eval_p_in_Sl)

  (* Case AnonValue *)
  | eval_p_in_Sr : (?S,, ?a |-> bot) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_add_anon in eval_p_in_Sr;
        destruct eval_p_in_Sr as (? & (-> & ?) & eval_p_in_Sl)

  (* Case RemoveAnon *)
  | fresh_a : fresh_anon ?S ?a,
    no_loan : not_contains_loan ?v,
    Heval : ?S |-{p} ?p =>^{?perm} ?pi |- _ =>
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        pose proof (eval_place_valid _ _ _ _ Heval) as valid_pi;
        apply (eval_place_RemoveAnon _ _ _ _ _ fresh_a no_loan) in Heval;
        destruct Heval as (? & (-> & pi_not_a) & eval_p_in_Sl)
  end.

Lemma eval_place_permutation S permission P sp permutation
  (valid_permutation : is_state_equivalence permutation S) :
  S |-{p} P =>^{permission} sp ->
  apply_state_permutation permutation S |-{p} P =>^{permission} permutation_spath permutation sp.
Proof.
  intros ((v & get_v & _) & H). split.
  { eexists. split; [ | constructor]. cbn [fst] in *. rewrite get_at_var in *.
    cbn. simpl_map. reflexivity. }
  remember (encode_var P.1.1, []) as sp0 eqn:EQN.
  replace sp0 with (permutation_spath permutation sp0)
    by (unfold permutation_spath; rewrite EQN; cbn [fst]; now rewrite perm_at_var).
  clear EQN get_v. induction H.
  - constructor.
  - econstructor; [ | eassumption]. destruct Heval_proj.
    + rewrite <-permutation_spath_app. eapply E_Deref_MutBorrow; [assumption | ].
      autorewrite with spath. rewrite get_q. reflexivity.
Qed.

(** * Simulation proofs for operand evaluation. *)
Lemma copy_val_to_symbolic v w p ty (valid_p : valid_vpath v p)
  (no_mut_loan : not_contains_loan v)
  (Htype : is_of_type ty (v.[[p]]))
  (Hcopy_val : copy_val (v.[[p <- VSymbolic ty]]) w) :
  exists w0 q, copy_val v w0 /\ w = w0.[[q <- VSymbolic ty]] /\
               is_of_type ty (w0.[[q]]).
Proof.
  remember (v.[[p <- VSymbolic ty]]) eqn:EQN. induction Hcopy_val.
  - exfalso. symmetry in EQN. assert (p = []) as ->; [ | discriminate].
    eapply vset_is_zeroary; [eassumption | now rewrite EQN].
  - exfalso. symmetry in EQN. assert (p = []) as ->; [ | discriminate].
    eapply vset_is_zeroary; [eassumption | now rewrite EQN].
  - assert (p = []).
    { eapply vset_is_zeroary; [eassumption | ]. rewrite <-EQN. reflexivity. }
    subst. inversion EQN. subst.
    exists v, []. split; [ | auto]. cbn in Htype. inversion Htype; try (constructor; assumption).
    subst. exfalso. eapply no_mut_loan; [apply valid_nil | constructor].
Qed.

Lemma copied_val_no_bot v w : copy_val v w -> not_contains_bot v.
Proof. induction 1; not_contains. Qed.

Lemma copied_val_no_mut_loan v w : copy_val v w -> not_contains_loan v.
Proof. induction 1; not_contains. Qed.

Lemma copied_val_no_mut_borrow v w : copy_val v w -> not_contains_borrow v.
Proof. induction 1; not_contains. Qed.

Lemma copy_no_loan v w : copy_val v w -> not_contains_loan w.
Proof. induction 1; not_contains. Qed.

Lemma copy_no_mut_borrow v w : copy_val v w -> not_contains_borrow w.
Proof. induction 1; not_contains. Qed.

Lemma is_fresh_copy l S pi v :
  is_fresh l S -> copy_val (S.[pi]) v -> not_value_contains (is_loan_id l) v.
Proof.
  intros Hfresh Hcopy.
  destruct (decidable_valid_spath S pi).
  - eapply not_state_contains_implies_not_value_contains_sget in Hfresh; [ | eassumption].
    induction Hcopy; not_contains.
  - rewrite sget_invalid in Hcopy by assumption. inversion Hcopy.
Qed.
Hint Resolve is_fresh_copy : spath.

Lemma operand_preserves_le_steps op :
  forward_simulation le_state_base^* le_val_state_base^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = IntConst n *)
  - destruct Hle; destruct Hle.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor.
        eapply Le_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply Le_ToAbs with (a := a) (i := i) (A := A).
        all: autorewrite with spath; assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor.
        apply Le_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_MergeAbs _ i j A B C); assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_AnonValue _ a); [assumption.. | ]. eassumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. apply Le_Fresh_MutLoan; eauto. not_contains. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Reborrow_MutBorrow; eauto. not_contains. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Borrow_Abstraction; eauto. not_contains. }
      states_eq.

  (* op = BoolConst n *)
  - destruct Hle; destruct Hle.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor.
        eapply Le_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply Le_ToAbs with (a := a) (i := i) (A := A).
        all: autorewrite with spath; assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor.
        apply Le_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_MergeAbs _ i j A B C); assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { econstructor. apply (Le_AnonValue _ a); [assumption.. | ]. eassumption. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. apply Le_Fresh_MutLoan; eauto. not_contains. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Reborrow_MutBorrow; eauto. not_contains. }
      reflexivity.
    + execution_step. { constructor. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Borrow_Abstraction; eauto. not_contains. }
      states_eq.

  (* op = copy p *)
  - destruct Hle; destruct Hle.
    (* Le-ToSymbolic *)
    + eval_place_preservation.
      assert (not_contains_loan (S.[pi])).
      { eapply not_value_contains_sset_rev.
        - eapply copied_val_no_mut_loan. eassumption.
        - assumption.
        - validity. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: we copy the newly introduced symbolic value. *)
      * autorewrite with spath in Hcopy_val.
        apply copy_val_to_symbolic in Hcopy_val;
          [ | validity | assumption | autorewrite with spath; assumption].
          destruct Hcopy_val as (w & q' & Hcopy_val & -> & get_int').
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { econstructor.
          apply Le_ToSymbolic with (sp := pi +++ q); autorewrite with spath; eassumption. }
        pose proof (copy_no_mut_borrow _ _ Hcopy_val).
        pose proof (copy_no_loan _ _ Hcopy_val).
        le_step_left.
        { eapply Le_ToSymbolic_Val with (vp := q'). eassumption.
          all: apply not_value_contains_vget; eauto with spath. }
        reflexivity.
      (* Case 2: we do not copy the newly introduced symbolic value. *)
      * assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { econstructor.
          apply Le_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
        reflexivity.

    (* Le-ToAbs *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; [eassumption | ]. autorewrite with spath. eassumption. }
      le_step_left.
      { econstructor. apply Le_ToAbs with (i := i); eauto with spath. }
      reflexivity.

    (* Le-RemoveAnon *)
    + eval_place_preservation.
      execution_step. { econstructor; [eassumption | ]. autorewrite with spath. eassumption. }
      le_step_left.
      { econstructor. apply Le_RemoveAnon; eauto with spath. }
      reflexivity.

    (* Le-MoveValue *)
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [(-> & ? & ?) | (r & -> & ->)].
      (* Case 1: the place we copy is not in the moved value. *)
      * rewrite sget_add_anon in Hcopy_val by assumption.
        (* The place we copy is in fact disjoint from the moved value, because the copied
           value cannot contain an unitialized value. *)
        assert (~prefix pi sp).
        { intros (q & <-). autorewrite with spath in Hcopy_val.
          eapply copied_val_no_bot; [eassumption | | now rewrite vset_vget_equal by validity].
          eapply vset_same_valid. validity. }
        assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { econstructor. apply Le_MoveValue with (a := a) (sp := sp); eauto with spath. }
        reflexivity.
      (* Case 2: the place we copy is in the moved value (this can only happen with shared
       * borrows. *)
      * autorewrite with spath in Hcopy_val.
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { econstructor. apply Le_MoveValue with (a := a) (sp := sp); eauto with spath. }
        reflexivity.

    (* Le-MergeAbs *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor. eassumption. autorewrite with spath. eassumption. }
      le_step_left.
      { econstructor. apply Le_MergeAbs; eauto with spath. }
      reflexivity.

    (* Le-Abs-ClearValue *)
    + eval_place_preservation.
      execution_step. { econstructor. eassumption. autorewrite with spath. eassumption. }
      le_step_left.
      { econstructor. eapply Le_Abs_ClearValue with (i := i) (j := j); eassumption. }
      reflexivity.

    (* Le-AnonValue *)
    + eval_place_preservation. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      le_step_left.
      { econstructor. apply Le_AnonValue with (a := a). assumption. }
      reflexivity.

    (* Le-Fresh-MutLoan *)
    + eval_place_preservation.
      rewrite sget_add_anon in Hcopy_val by assumption.
      assert (~prefix pi sp).
      { intros (q & <-). rewrite sset_sget_prefix in Hcopy_val by validity.
        eapply copied_val_no_mut_loan;
          [eassumption | | rewrite vset_vget_equal by validity; constructor].
        apply vset_same_valid. validity. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. apply Le_Fresh_MutLoan. all: eauto with spath. }
      reflexivity.

    (* Le-Reborrow-MutBorrow *)
    + eval_place_preservation. rewrite sget_add_anon in Hcopy_val by assumption.
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in Hcopy_val.
        eapply copied_val_no_mut_borrow;
          [eassumption | | rewrite vset_vget_equal by validity; constructor].
        apply vset_same_valid. validity. }
      autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. apply Le_Reborrow_MutBorrow. all: eauto with spath. }
      reflexivity.

    (* Le-Borrow-Abstraction *)
    + eval_place_preservation.
      autorewrite with spath in Hcopy_val.
      execution_step. { econstructor; eassumption. }
      le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Borrow_Abstraction. all: eauto with spath. }
      reflexivity.

  (* op = move p *)
  - destruct Hle; destruct Hle.
    (* Le-ToSymbolic *)
    + eval_place_preservation.
      execution_step.
      { constructor. eassumption. not_contains. not_contains. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the value we turn into a symbolic value is in the place we move. *)
      * autorewrite with spath in * |-.
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := q).
          all: autorewrite with spath; eassumption. }
        states_eq.

      (* Case 2: the value we turn into a symbolic value is disjoint to the place we move. *)
      * assert (disj pi sp) by solve_comp.
        autorewrite with spath in * |-.
        le_step_left.
        { econstructor. apply Le_ToSymbolic with (sp := sp).
          all: autorewrite with spath; eassumption. }
        states_eq.

    (* Le-ToAbs *)
    + eval_place_preservation.
      autorewrite with spath in *.
      execution_step. { apply E_Move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath in *.
      le_step_left.
      { econstructor.
        apply Le_ToAbs with (a := a) (i := i); [ | autorewrite with spath | ]; eauto with spath. }
      reflexivity.

    (* Le-RemoveAnon *)
    + eval_place_preservation.
      execution_step. { apply E_Move. eassumption. all: autorewrite with spath; eassumption. }
      autorewrite with spath. le_step_left.
      { econstructor. apply Le_RemoveAnon with (a := a). eauto with spath.
        all: autorewrite with spath; assumption. }
      reflexivity.

    (* Le-MoveValue *)
    + eval_place_preservation.
      (* The place pi we move does not contain any bottom value is the right state, as a
         condition of the move rule.
         The right state is Sr = S.[sp <- bot],, a |-> S.[sp].
         That means that that sp cannot be inside sp, thus pi and sp are disjoint. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_bot. eapply move_no_bot with (p := q).
        apply vset_same_valid. validity. autorewrite with spath. reflexivity. }
      assert (disj pi sp) by solve_comp.
      autorewrite with spath in * |-.
      execution_step. { apply E_Move; eassumption. }
      le_step_left.
       { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
         autorewrite with spath; assumption. auto with spath. validity.
         eauto with spath. assumption. }
      states_eq.

    (* Le-MergeAbs *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      execution_step. { apply E_Move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath. le_step_left.
      { econstructor. eapply Le_MergeAbs; eauto with spath. }
      reflexivity.

    (* Le-Abs-ClearValue *)
    + eval_place_preservation. autorewrite with spath in * |-.
      execution_step. { constructor. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath.
      le_step_left.
      { econstructor. eapply Le_Abs_ClearValue with (i := i) (j := j); auto with spath. }
      reflexivity.

    (* Le-AnonValue *)
    + eval_place_preservation.
      autorewrite with spath in *.
      execution_step. { econstructor; eassumption. }
      le_step_left.
      { econstructor. apply Le_AnonValue with (a := a). auto with spath. }
      reflexivity.

    (* Le-Fresh-MutLoan *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      (* Because the path pi we move does not contain any loan, it cannot contain the spath sp
         where the mutable loan is written. *)
      (* Note: this is similar to a reasonning we do for the case Le_MoveValue. Make a lemma? *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_loan.
        eapply move_no_loan with (p := q). apply vset_same_valid. validity.
        autorewrite with spath. constructor. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in *.
      execution_step. { apply E_Move; eassumption. }
      le_step_left.
      { eapply Le_ValState_FreshLoan.
        apply Le_Fresh_MutLoan with (sp := sp) (l' := l') (a := a) (ty := ty).
        all: autorewrite with spath; auto with spath. not_contains. not_contains. }
      states_eq.

    (* Le-Reborrow-MutBorrow *)
    + eval_place_preservation.
      (* TODO: time wasted by the rule [sget_reborrow_mut_borrow_not_prefix]. *)
      autorewrite with spath in * |-. (* TODO: long. *)
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the spath [sp] we reborrow is in the place [pi] we move. *)
      * execution_step.
        { apply E_Move. eassumption.
          eapply not_contains_rename_mut_borrow; eauto with spath.
          eapply not_contains_rename_mut_borrow; eauto with spath. }
         le_step_left.
        (* Because the place we reborrow was at [sp +++ q], and that we move and return
           [S.[sp]], the borrow is now in the anonymous value we evaluate a0, at path
           [q]. *)
        { apply Le_Reborrow_MutBorrow_Val with (vp := q) (l1 := l1) (a := a).
          auto with spath. autorewrite with spath. eassumption.
          autorewrite with spath in Htype |- *. exact Htype. not_contains. not_contains. }
        autorewrite with spath. reflexivity.

       (* Case 2: the spath sp we reborrow is disjoint from the place [pi] we move. *)
      * assert (disj pi sp) by solve_comp.
        autorewrite with spath in * |-. execution_step.
        { apply E_Move; eassumption. }
        le_step_left.
        { eapply Le_ValState_FreshLoan.
          apply Le_Reborrow_MutBorrow with (sp := sp) (l1 := l1) (a := a).
          all: autorewrite with spath; eauto with spath. not_contains. not_contains. }
        autorewrite with spath. reflexivity.

    (* Le-Borrow-Abstraction *)
    + eval_place_preservation. autorewrite with spath in * |-.
      execution_step. { econstructor. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath. le_step_left.
      { eapply Le_ValState_FreshLoan.
        eapply Le_Borrow_Abstraction with (l' := l') (a := a).
        all: eauto with spath. not_contains. not_contains. }
      reflexivity.
Qed.

Lemma copy_val_rename_value m v w : copy_val v w -> copy_val (rename_value m v) (rename_value m w).
Proof. induction 1; constructor. assumption. Qed.

Lemma copy_val_loan_set v w : copy_val v w -> subseteq (loan_set_val w) (loan_set_val v).
Proof. induction 1; set_solver. Qed.

Lemma operand_preserves_equiv op :
  forward_simulation equiv_states equiv_val_state (eval_operand op) (eval_operand op).
Proof.
  intros S0 S1 Heval S'0 Hequiv. destruct Heval.
  - execution_step. { constructor. } destruct Hequiv as (perm & ? & ?). exists perm. set_solver.

  - execution_step. { constructor. } destruct Hequiv as (perm & ? & ?). exists perm. set_solver.

  - symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ->).
    assert (valid_spath S pi) by eauto with spath.
    eapply eval_place_permutation in Heval_place; [ | eassumption].
    execution_step.
    { econstructor. eassumption. autorewrite with spath. apply copy_val_rename_value. eassumption. }
    symmetry. exists perm. repeat (easy || split).
    etransitivity; [apply copy_val_loan_set; eassumption | ].
    etransitivity; [apply loan_set_sget | apply Hperm].

  - symmetry in Hequiv. destruct Hequiv as (perm & ? & ->).
    assert (valid_spath S pi) by eauto with spath.
    eapply eval_place_permutation in Heval; [ | eassumption].
    execution_step.
    { econstructor. eassumption. all: autorewrite with spath; eauto with spath. }
    symmetry. exists perm. autorewrite with spath. repeat (eauto with spath || split).
    etransitivity; [apply loan_set_sget | apply H].
Qed.

Lemma operand_preserves_le op :
  forward_simulation le_symbolic le_val_state (eval_operand op) (eval_operand op).
Proof.
  apply forward_simulation_chain.
  - apply operand_preserves_equiv.
  - apply operand_preserves_le_steps.
Qed.

(** * Simulation proofs for rvalue evaluation. *)
Lemma integer_zeroary v :
  not_contains_loan v -> is_of_type TInt v -> arity (get_node v) = 0.
Proof. intros ? H. inversion H; reflexivity. Qed.

Lemma integer_does_not_contain_borrow v : is_of_type TInt v -> not_contains_borrow v.
Proof. inversion 1; not_contains. Qed.
Hint Resolve integer_does_not_contain_borrow : spath.

Lemma boolean_does_not_contain_borrow v : is_of_type TBool v -> not_contains_borrow v.
Proof. inversion 1; not_contains. Qed.
Hint Resolve boolean_does_not_contain_borrow : spath.

Lemma le_val_state_base_integer (vSl vSr : value * state) :
  le_val_state_base vSl vSr ->
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  is_of_type TInt vr -> not_contains_loan vr ->
  (vl = vr /\ le_state_base Sl Sr) \/
  (is_of_type TInt vl /\ not_contains_loan vl /\ vr = VSymbolic TInt /\ Sl = Sr).
Proof.
  destruct 1; intros int_vr no_loan_vr.
  - left. split; [reflexivity | econstructor; eassumption].
  - left. split; [reflexivity | eapply Le_FreshLoan; eassumption].
  - assert (vp = []) as ->.
    { eapply valid_vpath_zeroary.
      - apply integer_zeroary; [exact no_loan_vr | exact int_vr].
      - apply vset_same_valid; eauto with spath. }
    inversion int_vr. subst. right. auto.
  - exfalso. eapply integer_does_not_contain_borrow with (p := vp).
    + exact int_vr.
    + apply vset_same_valid. validity.
    + autorewrite with spath. constructor.
Qed.

Lemma le_val_state_integer vSl vSr :
  le_val_state_base^* vSl vSr ->
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  is_of_type TInt vr -> not_contains_loan vr ->
  (vl = vr \/ is_of_type TInt vl /\ not_contains_loan vl /\ vr = VSymbolic TInt) /\ le_state_base^* Sl Sr.
Proof.
  induction 1 as [(v & S) | (vl & Sl) (vm & Sm) (vr & Sr) ? ? le_step]
    using clos_refl_trans_ind_left'.
  - split; [ | reflexivity]. left. reflexivity.
  - intros. eapply le_val_state_base_integer in le_step.
    destruct le_step as [(? & ?) | (? & ? & ? & ?)]; [assumption.. | | ]; subst.
    + destruct IHclos_refl_trans; [assumption.. | ]. split; [assumption | ].
      transitivity Sm; [ | constructor]; assumption.
    + destruct IHclos_refl_trans as ([ | (? & ? & ?)] & ?); [assumption.. | | ];
        subst; auto.
Qed.

Lemma to_abs_not_contains v A l :
  map_Forall (fun _ => not_value_contains (is_loan_id l)) A -> to_abs v A ->
  not_value_contains (is_loan_id l) v.
Proof.
  intros G. induction 1.
  - rewrite map_Forall_insert in G by now simpl_map.
    destruct G as ((? & ?)%is_fresh_mut_borrow & G).
    rewrite map_Forall_singleton in G by now simpl_map.
    apply is_fresh_mut_loan in G. not_contains.
  - rewrite map_Forall_singleton in G by now simpl_map.
    apply is_fresh_mut_borrow in G. destruct G as (? & _). not_contains.
Qed.

Lemma add_is_integer v0 v1 w (H : eval_binary_op BAdd v0 v1 w) :
  is_of_type TInt v0 /\ is_of_type TInt v1 /\ is_of_type TInt w.
Proof. inversion H; repeat split; constructor. Qed.

Lemma add_no_loan v0 v1 w (H : eval_binary_op BAdd v0 v1 w) :
  not_contains_loan v0 /\ not_contains_loan v1 /\ not_contains_loan w.
Proof. inversion H; repeat split; not_contains. Qed.

Lemma le_is_bool v0 v1 w (H : eval_binary_op BLe v0 v1 w) :
  is_of_type TInt v0 /\ is_of_type TInt v1 /\ is_of_type TBool w.
Proof. inversion H; repeat split; constructor. Qed.

Lemma le_no_loan v0 v1 w (H : eval_binary_op BLe v0 v1 w) :
  not_contains_loan v0 /\ not_contains_loan v1 /\ not_contains_loan w.
Proof. inversion H; repeat split; not_contains. Qed.

Lemma le_base_implies_le_val_state_base Sl Sr v
  (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
  le_state_base^* Sl Sr -> le_val_state_ut (v, Sl) (v, Sr).
Proof.
  intros H. eexists. split; [reflexivity | ].
  induction H as [Sl Sr H | | ]; [destruct H | ..].
  - constructor. econstructor. eassumption.
  - constructor. eapply Le_ValState_FreshLoan; eauto with spath.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Lemma binop_integers v0 v1 binop :
  not_contains_loan v0 -> not_contains_loan v1 ->
  is_of_type TInt v0 -> is_of_type TInt v1 -> exists w, eval_binary_op binop v0 v1 w.
Proof.
  intros v0_no_loan v1_no_loan H G.
  destruct v0; inversion H; destruct v1; inversion G.
  all: try (exfalso; eapply loan_contains_loan; eassumption).
  all: destruct binop; eexists; constructor.
Qed.

Lemma rename_value_subset v m m' :
  subseteq (loan_set_val v) (dom m) -> subseteq m m' ->
  rename_value m' v = rename_value m v.
Proof.
  induction v; intros H Hincl; try reflexivity.
  - cbn in H. apply singleton_subseteq_l, elem_of_dom in H. cbn. unfold rename_loan_id.
    destruct H as (? & G). setoid_rewrite G.
    eapply map_subseteq_spec in Hincl; [ | exact G]. setoid_rewrite Hincl. reflexivity.
  - rewrite loan_set_borrow in H. apply union_subseteq in H. destruct H as (H & ?).
    rewrite !rename_loan_id_borrow. rewrite IHv by assumption.
    apply singleton_subseteq_l, elem_of_dom in H. cbn. unfold rename_loan_id.
    destruct H as (? & H). setoid_rewrite H.
    eapply map_subseteq_spec in Hincl; [ | exact H]. setoid_rewrite Hincl. reflexivity.
Qed.

Lemma rename_state_subset S m m' :
  subseteq (loan_set_state S) (dom m) -> subseteq m m' ->
  rename_state m' S = rename_state m S.
Proof.
  intros ? ?. apply state_eq_ext.
  - rewrite !get_map_rename_state. apply map_fmap_ext. intros.
    apply rename_value_subset; [ | assumption]. etransitivity; [ | eassumption].
    eapply loan_set_val_subset_eq_loan_set_state. eassumption.
  - rewrite !get_extra_rename_state. reflexivity.
Qed.

Lemma rename_loan_eval_mut_borrow S l l' pi ty (valid_pi : valid_spath S pi)
  (fresh_l : is_fresh l S) (fresh_l' : is_fresh l' S) :
  equiv_val_state_up_to_loan_renaming (borrow^m(l', S.[pi]), S.[pi <- loan^m(ty, l')])
                                      (borrow^m(l, S.[pi]), S.[pi <- loan^m(ty, l)]).
Proof.
  exists (insert l' l (id_loan_map (loan_set_state S))). split; split.
  - apply map_inj_insert; [ | apply id_loan_map_inj].
    intros l'' G. pose proof (lookup_id_loan_map _ _ _ G). subst.
    apply mk_is_Some, elem_of_dom in G.
    rewrite dom_id_loan_map, elem_of_loan_set_state in G. destruct G as (q & G).
    eapply fresh_l; [eapply get_loan_id_valid_spath | ]; exact G.
  - setoid_rewrite dom_insert_L. rewrite dom_id_loan_map.
    pose proof (loan_set_sset S pi (loan^m(ty, l'))) as H. cbn [loan_set_val] in H.
    set_solver.
  - setoid_rewrite dom_insert_L. rewrite dom_id_loan_map.
    rewrite loan_set_borrow. pose proof (loan_set_sget S pi). set_solver.
  - rewrite rename_state_sset by (setoid_rewrite dom_insert_L; apply union_subseteq_l).
    rewrite rename_loan_id_borrow. cbn [rename_value].
    unfold rename_loan_id. setoid_rewrite lookup_insert_eq.
    rewrite <-rename_state_sget. replace (rename_state _ S) with S; auto.
    erewrite rename_state_subset, rename_state_identity.
    + reflexivity.
    + rewrite dom_id_loan_map. reflexivity.
    + apply insert_subseteq.
      rewrite eq_None_not_Some, <-elem_of_dom, dom_id_loan_map, elem_of_loan_set_state.
      intros (p & get_l').
      eapply fresh_l'; [eapply get_loan_id_valid_spath | ]; exact get_l'.
Qed.

Lemma merge_abstraction_is_fresh l S i j A B C :
  fresh_abstraction S i -> fresh_abstraction S j -> i <> j ->
  is_fresh l (S,,, i |-> A,,, j |-> B) -> merge_abstractions A B C ->
  is_fresh l (S,,, i |-> C).
Proof.
  intros ? ? ? Hfresh Hmerge.
  rewrite !not_state_contains_add_abstraction in * by auto with spath.
  destruct Hfresh as ((? & fresh_A) & fresh_B). split; [assumption | ].
  intros k v get_v%insert_delete_id. rewrite <-get_v in Hmerge.
  apply merge_abstractions_contains in Hmerge; [ | now simpl_map].
  destruct Hmerge as [(? & -> & _ & _) | (? & ? & -> & _ & _)].
  - eapply fresh_A, lookup_insert_eq.
  - eapply fresh_B, lookup_insert_eq.
Qed.

Lemma le_val_state_by_equiv vSl vSr :
  equiv_val_state_up_to_loan_renaming vSl vSr -> le_val_state_ut vSl vSr.
Proof. exists vSr. split; [assumption | reflexivity]. Qed.

Lemma rvalue_preserves_le_steps rv :
  forward_simulation le_state_base^* le_val_state_ut (eval_rvalue rv) (eval_rvalue rv).
Proof.
  apply preservation_by_base_case.
  intros Sr vSr eval_rv Sl Hle. destruct eval_rv.
  - apply operand_preserves_le_steps in Heval_op.
    edestruct Heval_op as (vS'l & ? & ?); [constructor; eassumption | ].
    exists vS'l. split.
    + eexists. split; [reflexivity | assumption].
    + constructor. assumption.

  - apply operand_preserves_le_steps in eval_op_0, eval_op_1.
    edestruct eval_op_0 as ((v0l & S'l) & le_S'l_S' & H); [constructor; eassumption | ].
    destruct binop.
    + destruct (add_is_integer _ _ _ Hbinop) as (? & ? & ?).
      destruct (add_no_loan _ _ _ Hbinop) as (? & ? & ?).
      apply le_val_state_integer in le_S'l_S'.
      destruct le_S'l_S' as (Hv0 & le_S'l_S'); [assumption.. | ].
      edestruct eval_op_1 as ((v1l & S''l) & le_S''l_S'' & ?); [exact le_S'l_S' | ].
      apply le_val_state_integer in le_S''l_S''.
      destruct le_S''l_S'' as (Hv1 & le_S''l_S''); [assumption.. | ].
      destruct Hv0 as [-> | (? & ? & ->)]; destruct Hv1 as [-> | (? & ? & ->)].
      * execution_step. { econstructor; eassumption. }
        apply le_base_implies_le_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0 v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TInt) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0l v1 wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TInt) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BAdd v0l v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (add_is_integer _ _ _ Hwl) as (_ & _ & ?).
        destruct (add_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TInt) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath.
    + destruct (le_is_bool _ _ _ Hbinop) as (? & ? & ?).
      destruct (le_no_loan _ _ _ Hbinop) as (? & ? & ?).
      apply le_val_state_integer in le_S'l_S'.
      destruct le_S'l_S' as (Hv0 & le_S'l_S'); [assumption.. | ].
      edestruct eval_op_1 as ((v1l & S''l) & le_S''l_S'' & ?); [exact le_S'l_S' | ].
      apply le_val_state_integer in le_S''l_S''.
      destruct le_S''l_S'' as (Hv1 & le_S''l_S''); [assumption.. | ].
      destruct Hv0 as [-> | (? & ? & ->)]; destruct Hv1 as [-> | (? & ? & ->)].
      * execution_step. { econstructor; eassumption. }
        apply le_base_implies_le_val_state_base; eauto with spath.
      * assert (exists wl, eval_binary_op BLe v0 v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TBool) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath; not_contains.
      * assert (exists wl, eval_binary_op BLe v0l v1 wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TBool) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath; not_contains.
      * assert (exists wl, eval_binary_op BLe v0l v1l wl) as (wl & Hwl)
          by now apply binop_integers.
        destruct (le_is_bool _ _ _ Hwl) as (_ & _ & ?).
        destruct (le_no_loan _ _ _ Hwl) as (_ & _ & ?).
        execution_step. { econstructor; eassumption. }
        le_step_left.
        { apply Le_ToSymbolic_Val with (vp := []).
          all: autorewrite with spath; eauto with spath. }
        replace w with (VSymbolic TBool) by now inversion Hbinop.
        apply le_base_implies_le_val_state_base; eauto with spath; not_contains.

  - destruct Hle; destruct Hle.
    (* Case [Le_ToSymbolic]: *)
    + eval_place_preservation.
      execution_step.
      { eapply E_MutBorrow with (l := l); [eassumption | not_contains.. | ].
        eapply is_of_type_sset_rev; try eassumption. constructor. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the symbolic value is in the borrowed value. *)
      * le_step_left.
        { eapply Le_ToSymbolic_Val with (vp := [0] ++ q).
          all: autorewrite with spath; eassumption. }
        autorewrite with spath. reflexivity.
      (* Case 2: the symbolic value is out of the borrowed value, the place where it is and
       * the borrowed place are disjoint. *)
      * assert (disj pi sp) by solve_comp.
        le_step_left.
        { econstructor. eapply Le_ToSymbolic with (sp := sp).
          all: autorewrite with spath; eassumption. }
        states_eq.
    (* Case [Le_ToAbs]: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { eapply E_MutBorrow with (l := l); autorewrite with spath; try eassumption.
        not_contains. eapply to_abs_not_contains; eassumption. }
      autorewrite with spath. le_step_left.
      { econstructor. apply Le_ToAbs with (i := i); eauto with spath. }
      reflexivity.
    (* Case [Le_RemoveAnon]: *)
    + eval_place_preservation.
      execution_step.
      { eapply E_MutBorrow with (l := l). eassumption.
        all: autorewrite with spath; not_contains. }
      autorewrite with spath. le_step_left.
      { econstructor. apply Le_RemoveAnon; eauto with spath. }
      reflexivity.
    (* Case [Le_MoveValue]: *)
    + eval_place_preservation.
      (* The moved value cannot be in the borrowed value, because it does not contain
       * uninitialized values. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in borrow_no_bot.
        eapply borrow_no_bot with (p := q).
        - apply vset_same_valid. validity.
        - autorewrite with spath. reflexivity. }
      assert (disj pi sp) by solve_comp.
      autorewrite with spath in *.
      execution_step.
      { eapply E_MutBorrow with (l := l); try eassumption. not_contains. }
      le_step_left.
      { econstructor. apply Le_MoveValue with (a := a) (sp := sp). not_contains_outer.
        eauto with spath. validity. eauto with spath. assumption. }
      states_eq.
    (* Case [Le_MergeAbs]: *)
    + autorewrite with spath. eval_place_preservation.
      destruct (exists_fresh_loan_id (S,,, i |-> A,,, j |-> B)) as (l' & fresh_l').
      execution_step.
      { eapply E_MutBorrow with (l := l'); try eassumption.
        all: autorewrite with spath in *; not_contains. }
      autorewrite with spath. le_step_left.
      { econstructor. eapply Le_MergeAbs; eauto with spath. }
      apply le_val_state_by_equiv.
      (* Sadly I have to undo the automatic rewritings, there is probably a better way to do
       * it. *)
      rewrite <-!sset_add_abstraction_notin by auto with spath.
      rewrite <-!(sget_add_abstraction_notin S i C) by auto with spath.
      apply rename_loan_eval_mut_borrow; eauto with spath.
      eapply merge_abstraction_is_fresh; eassumption.
    (* Case [Le_Abs_ClearValue]: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { eapply E_MutBorrow with (l := l); autorewrite with spath; try eassumption.
        apply not_state_contains_add_abstraction_value; auto with spath. }
      autorewrite with spath. le_step_left.
      { econstructor. apply Le_Abs_ClearValue with (i := i) (j := j).
        autorewrite with spath. all: auto with spath. }
      reflexivity.
    (* Case [Le_AnonValue]: *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step.
      { apply E_MutBorrow with (l := l); [eassumption.. | | eassumption]. not_contains. }
      le_step_left.
      { econstructor. eapply Le_AnonValue with (a := a). eauto with spath. }
      reflexivity.
    (* Case [Le_Fresh_MutLoan]: *)
    + eval_place_preservation.
      (* The loan cannot be in the borrowed value. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in borrow_no_loan.
        eapply borrow_no_loan with (p := q).
        - apply vset_same_valid. validity.
        - autorewrite with spath. constructor. }
      assert (disj pi sp) by solve_comp. autorewrite with spath in *.
      execution_step.
      { eapply E_MutBorrow with (l := l); try eassumption. not_contains. }
      le_step_left.
      { eapply Le_ValState_FreshLoan.
        apply Le_Fresh_MutLoan with (a := a) (sp := sp) (l' := l').
        eauto with spath. validity. assumption.
        autorewrite with spath. eassumption. not_contains. not_contains. }
      states_eq.
    (* Case [Le_Reborrow_MutBorrow]: *)
    + eval_place_preservation. rewrite sget_add_anon in * by assumption.
      autorewrite with spath in Htype.
      execution_step.
      { eapply E_MutBorrow with (l := l); try eassumption; not_contains.
        eapply is_of_type_rename_mut_borrow; eassumption. }
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the reborrow is in the borrowed value. *)
      * le_step_left.
        { eapply Le_Reborrow_MutBorrow_Val with (vp := [0] ++ q) (l1 := l1) (a := a).
          eauto with spath. autorewrite with spath. eassumption. eauto with spath.
          autorewrite with spath in Htype0 |- *. eassumption. not_contains. not_contains. }
        autorewrite with spath. reflexivity.
      (* Case 2: the reborrow is not in the borrowed value. *)
      * le_step_left.
        { eapply Le_ValState_FreshLoan. eapply Le_Reborrow_MutBorrow.
          eauto with spath. autorewrite with spath. eassumption. eauto with spath.
          eapply is_of_type_rename_mut_borrow in Htype; [ | eassumption].
          eapply is_of_type_sset_sget; try eassumption. constructor.
          not_contains. not_contains. }
        autorewrite with spath. reflexivity.
    (* Case [Le_Borrow_Abstraction]: *)
    + eval_place_preservation. autorewrite with spath in * |-.
      execution_step.
      { eapply E_MutBorrow with (l := l). eassumption.
        all: autorewrite with spath; try eassumption. not_contains. }
      autorewrite with spath. le_step_left.
      { eapply Le_ValState_FreshLoan. eapply Le_Borrow_Abstraction with (l' := l') (a := a).
        all: eauto with spath. not_contains. not_contains. }
      states_eq.
Qed.

Lemma bin_op_rename_value v0 v1 m0 m1 w binop
  (H : eval_binary_op binop (rename_value m0 v0) (rename_value m1 v1) w) :
  eval_binary_op binop v0 v1 w.
Proof.
  replace (rename_value m0 v0) with v0 in H by now destruct v0.
  replace (rename_value m1 v1) with v1 in H by now destruct v1.
  exact H.
Qed.

Lemma rvalue_preserves_equiv rv :
  forward_simulation equiv_states equiv_val_state (eval_rvalue rv) (eval_rvalue rv).
Proof.
  intros S0 S1 Heval S'0 Hequiv. destruct Heval.
  - apply operand_preserves_equiv in Heval_op.
    edestruct Heval_op as (vS'' & ? & ?); [exact Hequiv | ].
    execution_step. { constructor. eassumption. } assumption.
  - apply operand_preserves_equiv in eval_op_0, eval_op_1.
    edestruct eval_op_0 as ((v'0 & ?) & Hequiv' & ?); [exact Hequiv | ].
    edestruct eval_op_1 as ((v'1 & ?) & Hequiv'' & ?);
      [eapply equiv_val_state_weaken; exact Hequiv' | ].
    destruct Hequiv' as (perm & _ & _ & _ & ->).
    destruct Hequiv'' as (perm' & ? & _ & -> & ->).
    apply bin_op_rename_value in Hbinop.
    execution_step. { econstructor; eassumption. }
    exists perm'. assert (loan_set_val w = empty) by now inversion Hbinop.
    rewrite rename_value_no_loan_id by assumption.
    repeat (assumption || split). set_solver.
  - symmetry in Hequiv. destruct Hequiv as (_perm & Hperm & ->).
    apply (extend_state_permutation (singleton l)) in Hperm.
    destruct Hperm as (perm & Hperm & Hl & ->).
    pose proof Hl as (l' & Hl')%singleton_subseteq_l%elem_of_dom.
    eapply eval_place_permutation in eval_p; [ | eassumption].
    execution_step.
    { econstructor. eassumption.
      all: autorewrite with spath; eauto with spath. eapply is_fresh_apply_permutation; eassumption. }
    symmetry. exists perm. autorewrite with spath.
    split; [auto with spath | ]. split.
    + rewrite loan_set_borrow. destruct Hperm as (_ & (_ & ?)).
      pose proof (loan_set_sget S pi). set_solver.
    + cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl'. auto.
Qed.

Lemma rvalue_preserves_le rv :
  forward_simulation le_symbolic le_val_state (eval_rvalue rv) (eval_rvalue rv).
Proof.
  intros S0 (v & S'0) eval_rv S2 (S1 & equiv_S2_S1 & le_S1_S0).
  eapply rvalue_preserves_le_steps in eval_rv.
  specialize (eval_rv S1 le_S1_S0). destruct eval_rv as (vS'1 & le_S'1_S'0 & eval_rv).
  eapply rvalue_preserves_equiv in eval_rv.
  specialize (eval_rv S2 equiv_S2_S1). destruct eval_rv as (vS'2 & equiv_S'2_S'1 & eval_rv).
  exists vS'2. split; [ | exact eval_rv].
  destruct le_S'1_S'0 as (vS''1 & ? & ?). exists vS''1. split; [ | assumption].
  etransitivity; [eassumption | ].
  apply equiv_val_state_up_to_loan_renaming_implies_equiv_val_state. assumption.
Qed.

(** * Simulation proofs for the [store] operation. *)
(** We only store values that come from rvalue evaluations, and these values do not contain loans or
    unitialized values. This can be used to prune cases. *)
Lemma eval_rvalue_no_bot S S' rv v : S |-{rv} rv => (v, S') -> not_contains_bot v.
Proof.
  inversion 1; subst; [ | inversion Hbinop; not_contains | not_contains].
  inversion Heval_op; subst.
  + not_contains.
  + not_contains.
  + induction Hcopy_val; not_contains.
  + assumption.
Qed.

Lemma eval_rvalue_no_loan S S' rv v : S |-{rv} rv => (v, S') -> not_contains_loan v.
Proof.
  inversion 1; subst; [ | inversion Hbinop; not_contains | not_contains].
  inversion Heval_op; subst.
  + not_contains.
  + not_contains.
  + induction Hcopy_val; not_contains.
  + assumption.
Qed.

Lemma not_contains_outer_loan_rename_mut_borrow S sp l0 l1 sp_store :
  get_node (S.[sp]) = nborrow^m(l0) ->
  not_contains_outer_loan (rename_mut_borrow S sp l1.[sp_store]) ->
  not_contains_outer_loan (S.[sp_store]).
Proof.
  intros get_borrow no_outer.
  destruct (decidable_prefix sp_store sp) as [(q & <-) | ].
  - intros r ? get_loan. rewrite <-sget_app in get_loan.
    destruct (decidable_vprefix q r) as [ | not_prefix].
    + exists q. rewrite <-sget_app, get_borrow. split; [ | constructor].
      apply vprefix_and_neq_implies_vstrict_prefix; [assumption | ].
      intros ->. destruct get_loan. discriminate.
    + destruct (no_outer r) as (? & ? & is_borrow).
      * eapply valid_spath_app, valid_spath_rename_mut_borrow.
        -- eassumption.
        -- apply is_loan_valid. assumption.
      * rewrite <-sget_app, get_node_rename_mut_borrow.
        -- assumption.
        -- rewrite get_borrow. constructor.
        -- intros ->%app_spath_vpath_inv_head. apply not_prefix. reflexivity.
      * eexists. split; [eassumption | ].
        rewrite <-sget_app in *. rewrite get_node_rename_mut_borrow in is_borrow.
        -- assumption.
        -- rewrite get_borrow. constructor.
        -- intros ->%app_spath_vpath_inv_head. apply not_prefix. eauto with spath.
  - autorewrite with spath in no_outer. assumption.
Qed.

Lemma eval_place_not_in_abstraction S p sp : S |-{p} p =>^{Mut} sp -> not_in_abstraction sp.
Proof.
  intros (_ & H). remember (encode_var p.1.1, []) as sp0 eqn:EQN.
  assert (not_in_abstraction sp0).
  { rewrite EQN. intros ? (? & ?). discriminate. }
  clear EQN. induction H.
  - assumption.
  - apply IHeval_path. destruct Heval_proj. assumption.
Qed.

Lemma store_preserves_le_steps p :
  forward_simulation le_val_state_base^* le_symbolic (store p) (store p).
Proof.
  apply preservation_by_base_case.
  intros vSr S'r Hstore (vl & Sl) Hle.
  destruct Hstore as [vr Sr sp_store a ? ? ? fresh_a].
  (* TODO: delete? *)
  assert (valid_spath Sr sp_store) by eauto with spath.
  assert (not_in_abstraction sp_store) by (eapply eval_place_not_in_abstraction; eassumption).
  (* In general, we cannot store the overwritten value in the anonymous variable a in the left
   * state. Indeed, this anonymous binding can be used in the left state (rules Le_ToAbs and
   * Le_RemoveAnon). Thus, we are going to store it in an anonymous variable b that is fresh in
   * both the left and the right state. *)
  destruct (exists_fresh_anon2 Sl Sr) as (b & fresh_b_l & fresh_b_r).
  (* By equivalence, we can rename a into b. *)
  cut (exists S'l, le_state_base^* S'l (Sr .[sp_store <- vr],, b |-> Sr .[sp_store]) /\
                   store p (vl, Sl) S'l).
  { intros (S'l & ? & ?). exists S'l. split; [ | assumption].
    etransitivity.
    - eexists. split; [reflexivity | eassumption].
    - eexists. split; [ | reflexivity]. eapply prove_equiv_states; [reflexivity | ].
      apply equiv_states_add_anon; eauto with spath. }
  clear a fresh_a.
  remember (vl, Sl) eqn:EQN_l. remember (vr, Sr) eqn:EQN_r.
  destruct Hle;
    rewrite pair_eq in * |-; destruct EQN_l, EQN_r; subst;
    [destruct le_states | destruct le_states | ..].
  (* Case [Le_ToSymbolic]: *)
  - eval_place_preservation. execution_step.
    { eapply Store; try eassumption. not_contains_outer.
      eapply store_compatible_types_sset; try eassumption. constructor. }
    destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
    (* Case 1: the symbolic value is introduced in the overwritten value. *)
    + autorewrite with spath in *. eapply le_step_left.
      { econstructor. eapply Le_ToSymbolic with (sp := (encode_anon b, r)).
        all: autorewrite with spath; eassumption. }
      autorewrite with spath. reflexivity.
    (* Case 2: the symbolic value is introduced in the overwritten value. *)
    + assert (disj sp_store sp) by solve_comp.
      autorewrite with spath in *. eapply le_step_left.
      { econstructor. eapply Le_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      states_eq.

  (* Case [Le_ToAbs]: *)
  - eval_place_preservation. autorewrite with spath in *.
    execution_step.
    { eapply Store with (a := b); autorewrite with spath; try eassumption.
      rewrite store_compatible_types_add_abstraction in Hstore_type by eauto with spath.
      rewrite store_compatible_types_add_anon; assumption. }
    rewrite fresh_anon_add_anon in fresh_b_l. destruct fresh_b_l as (_ & ?).
    autorewrite with spath. rewrite add_anon_commute by congruence. le_step_left.
    { econstructor. apply Le_ToAbs with (i := i); eauto with spath. }
    autorewrite with spath. reflexivity.

  (* Case [Le_RemoveAnon]: *)
  - (* There are two fresh anonymous binding identifiers here, [a] and [b],
       so we have to do a manual application of [eval_place_preservation]. *)
    eapply eval_place_RemoveAnon with (a := a) in eval_p; [ | eassumption..].
    destruct eval_p as (? & (-> & ?) & eval_p).
    execution_step.
    { apply Store with (a := b); autorewrite with spath; try eassumption.
      rewrite store_compatible_types_add_anon; assumption. }
    rewrite fresh_anon_add_anon in fresh_b_l. destruct fresh_b_l as (_ & ?).
    autorewrite with spath. rewrite add_anon_commute by congruence. le_step_left.
    { econstructor. apply Le_RemoveAnon; eauto with spath. }
    reflexivity.

  (* Case [Le_MoveValue]: *)
  - eval_place_preservation. rewrite sget_add_anon in no_outer_loan by assumption.
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    execution_step.
    { eapply Store with (a := b); try eassumption. not_contains_outer.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_moved_value; eassumption. }
    destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
    + autorewrite with spath in *.
      le_step_left.
      { econstructor. eapply Le_MoveValue with (sp := (anon_accessor b, r)) (a := a).
        autorewrite with spath. assumption.
        eauto with spath.
        eauto with spath.
        (* TODO: automate *)
        rewrite no_ancestor_anon by reflexivity. cbn.
        intros q Hq (? & ? & <-). autorewrite with spath in Hq.
        eapply sp_not_in_borrow. exact Hq.
        eexists _, _. autorewrite with spath. reflexivity.
        eauto with spath.
      }
      states_eq.
    + assert (disj sp_store sp) by solve_comp. autorewrite with spath in *.
      le_step_left.
      { econstructor. eapply Le_MoveValue with (sp := sp) (a := a).
        autorewrite with spath. all: eauto with spath. }
      states_eq.

  (* Case [Le_MergeAbs]: *)
  - eval_place_preservation.
    execution_step.
    { apply Store. eassumption. autorewrite with spath in *. assumption.
      rewrite !store_compatible_types_add_abstraction in *; eauto with spath.
      eauto with spath. }
    autorewrite with spath. rewrite <-!add_abstraction_add_anon.
    le_step_left. { econstructor. eapply Le_MergeAbs; eauto with spath. }
    reflexivity.

  (* Case [Le_Abs_ClearValue]: *)
  - eval_place_preservation. autorewrite with spath in * |-.
    execution_step.
    { eapply Store with (a := b); autorewrite with spath; try eassumption.
      rewrite store_compatible_types_add_abstraction in * by auto with spath. assumption. }
    autorewrite with spath. le_step_left.
    { rewrite <-add_abstraction_add_anon.
      econstructor. apply Le_Abs_ClearValue with (i := i) (j := j); auto with spath. }
    states_eq.

  (* Case [Le_AnonValue]: *)
  - eval_place_preservation. autorewrite with spath in * |-.
    (* TODO: used several times. automate? *)
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    rewrite store_compatible_types_add_anon in Hstore_type by assumption.
    execution_step. { eapply Store with (a := b); eassumption. }
    le_step_left.
    { econstructor. apply Le_AnonValue with (a := a). eauto with spath. }
    states_eq.

  (* Case [Le_Fresh_MutLoan]: *)
  - eval_place_preservation.
    rewrite sget_add_anon in no_outer_loan by assumption.
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    execution_step.
    { eapply Store with (a := b); try eassumption.
      eapply not_contains_outer_sset_contains; try eassumption. constructor.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_sset; try eassumption. constructor. }
    destruct (decidable_prefix sp_store sp) as [(q & <-) | ].
    (* Case 1: the fresh mutable loan is introduced in the value we overwrite. *)
    + le_step_left.
      { eapply Le_FreshLoan.
        apply Le_Fresh_MutLoan with (a := a) (sp := (anon_accessor b, q)) (l' := l').
        eauto with spath. validity. eauto with spath.
        autorewrite with spath. eassumption. not_contains. }
      states_eq.
    (* Case 2: the fresh mutable loan is introduced in a place disjoint from the place we
       overwrite. *)
    + assert (disj sp_store sp) by solve_comp.
      le_step_left.
      { eapply Le_FreshLoan, Le_Fresh_MutLoan with (a := a) (sp := sp) (l' := l').
        eauto with spath. validity. assumption.
        autorewrite with spath. eassumption. not_contains. }
      states_eq.

  (* Case [Le_Reborrow_MutBorrow]: *)
  - eval_place_preservation. rewrite sget_add_anon in no_outer_loan by assumption.
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    execution_step.
    { eapply Store with (a := b); try eassumption.
      eapply not_contains_outer_loan_rename_mut_borrow; eassumption.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_rename_mut_borrow; eassumption. }
    destruct (decidable_prefix sp_store sp) as [(r & <-) | ].
    (* Case 1: the renames borrow is in the ovewritten value. *)
    + le_step_left.
      { eapply Le_FreshLoan.
        eapply Le_Reborrow_MutBorrow with (sp := (anon_accessor b, r)) (a := a) (l1 := l1).
        eauto with spath. autorewrite with spath. eassumption. eauto with spath.
        autorewrite with spath in Htype |- *. exact Htype. not_contains. }
      states_eq.
    (* Case 2.b: the renames borrow is in a path disjoint from the path we overwrite. *)
    + rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      (* TODO: this is a subtile piece of proof. I should make a separate lemma and
       * document it. *)
      assert (is_of_type ty (S.[ sp_store <- vr].[ sp +++ [0] ])).
      { destruct (decidable_prefix (sp +++ [0]) sp_store) as [(r & <-) | ].
        - autorewrite with spath.
          destruct Hstore_type as (ty' & G & ?); [exists sp; split | ].
          + autorewrite with spath. exists 0, r. reflexivity.
          + autorewrite with spath. constructor.
          + eapply vset_preserves_type; try eassumption.
            autorewrite with spath in G |- *. exact G.
        - assert (disj sp_store sp) by solve_comp. autorewrite with spath. assumption.
      }
      le_step_left.
      { eapply Le_FreshLoan, Le_Reborrow_MutBorrow with (sp := sp) (a := a) (l1 := l1).
        eauto with spath. autorewrite with spath. eassumption.
        eauto with spath. rewrite sget_add_anon; eauto with spath. not_contains. }
      states_eq.

  (* Case [Le_Borrow_Abstraction]: *)
  - eval_place_preservation. autorewrite with spath in * |-.
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    execution_step.
    { eapply Store with (a := b). eassumption. autorewrite with spath. assumption.
      rewrite store_compatible_types_add_anon in * |- by congruence.
      rewrite store_compatible_types_add_abstraction in * by auto with spath.
      assumption. auto with spath. }
    le_step_left.
    { autorewrite with spath. rewrite <-add_abstraction_add_anon.
      eapply Le_FreshLoan, Le_Borrow_Abstraction with (j := j) (l' := l') (ty' := ty') (a := a).
      auto with spath. assumption. auto with spath.
      (* TODO: automate. *) not_contains. apply eval_place_valid in eval_p_in_Sl.
      autorewrite with spath in eval_p_in_Sl. assumption. }
    states_eq.

  (* Case Le_ToSymbolic_Val. *)
  - execution_step.
    { econstructor; try eassumption.
      eapply store_compatible_types_vset_symbolic; eassumption. }
    eapply le_step_left.
    { econstructor. eapply Le_ToSymbolic with (sp := sp_store +++ vp).
      all: autorewrite with spath; eassumption. }
    autorewrite with spath. reflexivity.

  (* Case Le_Reborrow_MutBorrow_Val. *)
  - (* TODO: eval_place_preservation. *)
    apply eval_place_add_anon in eval_p. destruct eval_p as (? & (-> & ?) & eval_p_in_Sl).
    autorewrite with spath in * |-. execution_step.
    { apply Store with (a := b); try eassumption.
      rewrite store_compatible_types_add_anon in Hstore_type by assumption.
      eapply store_compatible_types_rename_mut_borrow_val; eassumption. }
    rewrite fresh_anon_add_anon in fresh_b_r. destruct fresh_b_r as (_ & ?).
    le_step_left.
    { eapply Le_FreshLoan.
      eapply Le_Reborrow_MutBorrow with (a := a) (sp := sp_store +++ vp) (l1 := l1).
      auto with spath. autorewrite with spath. eassumption. assumption.
      autorewrite with spath. eassumption. not_contains. }
    states_eq.
Qed.

Lemma is_mut_borrow_valid_spath S p (H : is_mut_borrow (get_node (S.[p]))) : valid_spath S p.
Proof. apply valid_get_node_sget_not_bot. intros G. rewrite G in H. inversion H. Qed.
Hint Resolve is_mut_borrow_valid_spath : spath.

(* TODO: move *)
Lemma _permutation_spath_app perm p q :
  (_permutation_spath perm p) +++ q = _permutation_spath perm (p +++ q).
Proof. unfold permutation_spath. cbn. autodestruct. Qed.

Lemma rename_value_preserves_type_rev r v ty :
  is_of_type ty (rename_value r v) -> is_of_type ty v.
Proof.
  remember (rename_value r v) as v' eqn:EQN.
  induction 1. all: destruct v; inversion EQN; subst; constructor.
Qed.

Lemma _store_compatible_types_permutation perm S sp v :
  is_state_equivalence perm S -> valid_spath S sp ->
  store_compatible_types (apply_state_permutation perm S)
    (permutation_spath perm sp) (rename_value (loan_id_names perm) v) ->
  store_compatible_types S sp v.
Proof.
  intros Hperm valid_sp Hcomp (q & Hprefix & Hmut_borrow).
  remember (get_node (S.[q])) eqn:EQN. destruct Hmut_borrow as [l]. symmetry in EQN.
  destruct Hcomp as (ty & type_S & type_v); [exists (permutation_spath perm q); split | ].
  - destruct Hprefix as (? & ? & <-). rewrite <-_permutation_spath_app.
    eexists _, _. reflexivity.
  - autorewrite with spath. rewrite EQN. constructor.
  - exists ty. split.
    + autorewrite with spath in type_S.
      now apply rename_value_preserves_type_rev in type_S.
    +  apply rename_value_preserves_type_rev in type_v. assumption.
Qed.

Lemma store_compatible_types_rename_value S p v r :
  store_compatible_types S p v -> store_compatible_types S p (rename_value r v).
Proof.
  intros Hcomp borrow_prefix. specialize (Hcomp borrow_prefix).
  destruct Hcomp as (ty & ? & ?). exists ty. split; [assumption | ].
  apply rename_value_preserves_type. assumption.
Qed.

Lemma store_compatible_types_permutation perm S sp v :
  is_state_equivalence perm S -> valid_spath S sp ->
  store_compatible_types S sp v ->
  store_compatible_types (apply_state_permutation perm S)
    (permutation_spath perm sp) (rename_value (loan_id_names perm) v).
Proof.
  intros valid_perm valid_sp H. destruct (valid_perm) as (valid_accessor_perm & _).
  eapply _store_compatible_types_permutation with (perm := invert_state_permutation perm).
  - apply invert_state_permutation_is_permutation. assumption.
  - apply permutation_valid_spath; assumption.
  - rewrite apply_invert_state_permutation by assumption.
    cbn. erewrite invert_state_permutation_spath by eassumption.
    repeat apply store_compatible_types_rename_value. assumption.
Qed.

Lemma store_preserves_equiv p :
  forward_simulation equiv_val_state equiv_states (store p) (store p).
Proof.
  intros (v0 & S0) S1 Heval (? & S'0) Hequiv.
  symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ? & -> & ->).
  inversion Heval; subst.
  assert (valid_spath S0 sp) by eauto with spath.
  destruct (exists_fresh_anon (apply_state_permutation perm S0)) as (b & fresh_b).
  eapply eval_place_permutation in eval_p; [ | eassumption].
  execution_step.
  { econstructor. eassumption. autorewrite with spath.
    apply not_contains_outer_loan_rename_value. assumption.
    apply store_compatible_types_permutation; assumption. eassumption. }
  symmetry. eexists. split.
  - apply add_anon_perm_equivalence with (b := b); eauto with spath.
    + etransitivity; [apply loan_set_sget | apply Hperm].
    + autorewrite with spath. assumption.
  - autorewrite with spath.
    + auto.
    + etransitivity; [apply loan_set_sget | apply Hperm].
    + autorewrite with spath. assumption.
Qed.

Lemma store_preserves_LLBC_plus_rel p vr Sr S'r vl Sl :
  not_contains_loan vr -> not_contains_bot vr ->
  store p (vr, Sr) S'r -> le_val_state (vl, Sl) (vr, Sr) ->
  exists S'l, store p (vl, Sl) S'l /\ le_symbolic S'l S'r.
Proof.
  intros no_loan no_bot Hstore ((vm & Sm) & Hequiv & Hle).
  edestruct store_preserves_le_steps as (S'm & (? & Hequiv' & Hle') & Hstore'); eauto.
  eapply store_preserves_equiv in Hstore'. specialize (Hstore' _ Hequiv).
  destruct Hstore' as (S'l & ? & ?).
  exists S'l. split.
  - assumption.
  - eexists. split; [ | eassumption]. etransitivity; eassumption.
Qed.

(** * Simulation proofs for reorganizations. *)
Lemma size_abstractions_sset S p v : size (abstractions (S.[p <- v])) = size (abstractions S).
Proof.
  unfold sset, alter_at_accessor. cbn. repeat autodestruct. cbn.
  rewrite<- !size_dom, dom_alter_L. reflexivity.
Qed.

Lemma size_abstraction_add_anon S a v :
  size (abstractions (S,, a |-> v)) = size (abstractions S).
Proof. reflexivity. Qed.

Lemma size_abstraction_add_abstraction S i A (H : fresh_abstraction S i) :
  size (abstractions (S,,, i |-> A)) = 1 + size (abstractions S).
Proof. cbn. rewrite map_size_insert, H. reflexivity. Qed.

Hint Rewrite size_abstractions_sset : weight.
Hint Rewrite size_abstraction_add_anon : weight.
Hint Rewrite size_abstraction_add_abstraction using auto with spath; fail : weight.
Hint Rewrite (@map_size_insert_Some positive) using auto : weight.

Lemma le_state_base_n_decreases n Sl Sr (H : le_state_base_n n Sl Sr) :
  measure Sl < measure Sr + n.
Proof.
  unfold measure. destruct H; destruct Hle.
  - weight_inequality.
  - autorewrite with weight. destruct Hto_abs.
    + autorewrite with weight; [lia | simpl_map; reflexivity].
    + weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
  - weight_inequality.
Qed.

Lemma measure_add_anons S A S' :
  add_anons S A S' -> measure S' = measure S + abs_measure A.
Proof.
  rewrite add_anons_alt. induction 1.
  - rewrite Nat.add_comm. reflexivity.
  - rewrite IHadd_anons'. unfold measure. autorewrite with weight. lia.
Qed.

Lemma reorg_decreases q S S' (H : reorg_n q S S') : measure S' + q < measure S.
Proof.
  destruct H.
  - unfold measure. weight_inequality.
  - unfold measure. autorewrite with weight spath.
    weight_given_node. autorewrite with weight. lia.
  - apply measure_add_anons in Hadd_anons. rewrite Hadd_anons.
    unfold measure. autorewrite with weight. lia.
Qed.

(** Lemmas used to prove the local commutation between le_state_base and reorg: *)
Lemma vget_borrow l v p c : get_node (borrow^m(l, v).[[p]]) = c -> c <> nbot ->
  p = [] /\ nborrow^m(l) = c \/ exists q, p = [0] ++ q /\ get_node (v.[[q]]) = c.
Proof.
  intros H G. destruct p as [ | [ | ] q].
  - left. auto.
  - right. exists q. auto.
  - exfalso. eapply G. rewrite <-H, vget_cons. cbn. rewrite nth_error_nil.
    replace nbot with (get_node bot) by reflexivity. f_equal. exact (vget_bot q).
Qed.

(* This variant is used for the commutation of the rule Le_Reborrow_MutBorrow_n with the ending of
 * a borrow. *)
Lemma vget_borrow_loan l0 l1 p c ty :
  get_node (borrow^m(l0, loan^m(ty, l1)).[[p]]) = c -> c <> nbot ->
  p = [] /\ nborrow^m(l0) = c \/ p = [0] /\ nloan^m(ty, l1) = c.
Proof.
  intros H G. apply vget_borrow in H; [ | assumption]. destruct H as [ | (q & -> & H)].
  - left. assumption.
  - right. destruct q.
    + auto.
    + exfalso. apply G. rewrite <-H. cbn. rewrite nth_error_nil.
      replace nbot with (get_node bot) by reflexivity. f_equal. exact (vget_bot q).
Qed.

(* This lemma is used once, when studying reorganizations and the rule Le_Fresh_MutLoan. *)
Lemma fresh_mut_loan_get_loan S l sp a p ty ty' (fresh_l : is_fresh l S) :
  get_node ((S.[sp <- loan^m(ty, l)],, a |-> borrow^m(l, S.[sp])).[p]) = nloan^m(ty', l) ->
  p = sp.
Proof.
  intros get_loan. destruct (decide (fst p = anon_accessor a)) as [H | ].
  - autorewrite with spath in get_loan. apply vget_borrow in get_loan; [ | discriminate].
    destruct get_loan as [(_ & ?) | (q & ? & get_loan)].
    + discriminate.
    + autorewrite with spath in get_loan. exfalso.
      eapply fresh_l; [ | rewrite get_loan]; auto with spath.
  - autorewrite with spath in get_loan.
    destruct (decidable_spath_eq p sp).
    + assumption.
    + exfalso. assert (~strict_prefix sp p) by eauto with spath.
      autorewrite with spath in get_loan. eapply fresh_l; [ | rewrite get_loan].
      * validity.
      * reflexivity.
Qed.

Lemma get_borrow_rename_mut_borrow S p l l0 q :
  get_node ((rename_mut_borrow S p l).[q]) = nborrow^m(l) -> is_fresh l S ->
  get_node (S.[p]) = nborrow^m(l0) -> p = q.
Proof.
  intros get_borrow fresh_l ?. destruct (decidable_spath_eq p q); [assumption | ].
  exfalso. autorewrite with spath in get_borrow.
  eapply fresh_l; [ | rewrite get_borrow; reflexivity]. validity.
Qed.

Inductive add_anonymous_bots : nat -> state -> state -> Prop :=
  | Add_no_bots S : add_anonymous_bots 0 S S
  | Add_anonymous_bot n S a S' :
      add_anonymous_bots n S S' -> fresh_anon S' a ->
      add_anonymous_bots (1 + n) S (S',, a |-> bot).

Lemma add_anonymous_bots_fresh_abstraction n S S' i :
  add_anonymous_bots n S S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof. induction 1; eauto with spath. Qed.
Hint Resolve add_anonymous_bots_fresh_abstraction : spath.

Lemma abs_measure_remove_loans A B A' B' :
  remove_loans A B A' B' -> abs_measure A' <= abs_measure A /\ abs_measure B' <= abs_measure B.
Proof.
  induction 1.
  - auto.
  - repeat lazymatch goal with
    | H : lookup ?i ?A = Some ?v |- _ =>
        apply (map_sum_delete (vweight (fun _ => 1))) in H
    end.
    lia.
Qed.

(* Note: this could be made into a tactic. *)
Lemma prove_add_anons S0 A S1 :
  (exists S', add_anons S' A S1 /\ S0 = S') -> add_anons S0 A S1.
Proof. intros (? & ? & ->). assumption. Qed.

(* The crucial lemma for the commutation between le and reorganizations, when we end a region C that
 * is the merge of two regions A and B. By definition, C is the union of A' and B' where we removed
 * common loans and borrows.
 * After ending the region B and placing its borrows in anonymous bindings, we must end all the
 * borrows that are in B \ B', and the corresponding loans in A \ A'.
 * TODO: explain the add_anonymous_bots operation. *)
Lemma end_removed_loans S0 S0_A_anons i A B A' B'
  (H : remove_loans A B A' B') (fresh_i : fresh_abstraction S0 i) :
  add_anons (S0,,, i |-> A) B S0_A_anons ->
  exists n s S1 S1_anons,
    add_anonymous_bots n S0 S1 /\
    2 * n + s <= abs_measure A + abs_measure B - abs_measure A' - abs_measure B' /\
    reorg_n^{s} S0_A_anons (S1_anons,,, i |-> A') /\
    add_anons S1 B' S1_anons /\
    fresh_abstraction S1_anons i.
Proof.
  intros (S0_anons & -> &Hadd_anons)%add_anons_add_abstraction.
  induction H as [ | A' B' j ? l ty Hremove_loans IH HA' HB'].
  - eexists 0, 0, _, S0_anons. repeat split.
    + constructor.
    + apply le_0_n.
    + apply MC_refl.
    + assumption.
    + eapply add_anons_fresh_abstraction; eassumption.
  - clear Hadd_anons.
    destruct IH as (n & s & S1 & S1_anons & ? & ? & ? & Hadd_anons & ?).
    rewrite <-(insert_delete_id _ _ _ HB') in Hadd_anons.
    eapply add_anons_delete in Hadd_anons; [ | simpl_map; reflexivity].
    destruct Hadd_anons as (a & fresh_a & Hadd_anons).
    eexists (1 + n), (s + vweight (fun _ => 1) (VSymbolic ty)), _, _.
    split.
    { econstructor; eassumption. }
    split.
    { apply (map_sum_delete (vweight (fun _ => 1))) in HA', HB'.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      apply abs_measure_remove_loans in Hremove_loans. lia. }
    assert (not_in_abstraction (anon_accessor a, [])) by now eapply anon_not_in_abstraction.
    split.
    { eapply MC_trans; [eassumption | ]. constructor.
      rewrite <-(insert_delete_id _ _ _ HA') at 1.
      apply add_anons_sget with (p := (anon_accessor a, [])) in Hadd_anons; [ | validity].
      autorewrite with spath in Hadd_anons.
      assert (get_symbolic : S1_anons.[(anon_accessor a, []) +++ [0] ] = VSymbolic ty).
      { rewrite sget_app, Hadd_anons. reflexivity. }
      rewrite <-get_symbolic.
      apply Reorg_End_MutBorrow_in_abstraction with (l := l) (ty := ty).
        - assumption.
        - simpl_map. reflexivity.
        - rewrite Hadd_anons. reflexivity.
        - rewrite get_symbolic. constructor.
        - rewrite get_symbolic. not_contains.
        - intros ? ?. eauto with spath.
        - assumption. }
    split.
    { apply add_anons_sset with (p := (anon_accessor a, [])) (v := bot) in Hadd_anons;
        [ | validity].
      autorewrite with spath in Hadd_anons. exact Hadd_anons. }
    { auto with spath. }
Qed.

Lemma commute_add_anonymous_bots_anons S0 S1 S2 n A :
  add_anonymous_bots n S0 S1 -> add_anons S1 A S2 ->
  exists S'1, add_anons S0 A S'1 /\ add_anonymous_bots n S'1 S2.
Proof.
  setoid_rewrite add_anons_alt. intros H. revert S2. induction H.
  - eexists. split; [eassumption | constructor].
  - intros S2 G.
    apply add_anon_add_anons' in G; [ | assumption]. destruct G as (? & -> & ? & ?).
    edestruct IHadd_anonymous_bots as (S'1 & ? & ?); [eassumption | ].
    exists S'1. split; [assumption | ]. constructor; assumption.
Qed.

Lemma le_n_add_anonymous_bots S S' n :
  add_anonymous_bots n S S' -> le_state_base_n^{2 * n} S' S.
Proof.
  induction 1 as [ | ? ? ? S'].
  - apply MC_refl.
  - replace (2 * (1 + n)) with (2 + 2 * n) by lia. eapply MC_trans.
    + constructor.
      replace 2 with (1 + vweight (fun _ => 1) bot) by reflexivity.
      econstructor. apply Le_RemoveAnon; autorewrite with spath.
      assumption. unfold not_contains_loan. not_contains. unfold not_contains_borrow. not_contains.
    + apply IHadd_anonymous_bots.
Qed.

Lemma add_anons_abstraction_set S B j v w q S' :
  add_anons S (abstraction_set j q v B) S' ->
  lookup j B = Some w -> valid_vpath w q ->
  exists S'' a,
    add_anons S B S'' /\ S' = S''.[(anon_accessor a, q) <- v] /\
    S''.[(anon_accessor a, q)] = w.[[q]].
Proof.
  unfold abstraction_set. intros Hadd_anons get_w ?.
  erewrite alter_alt_Some, <-insert_delete_eq in Hadd_anons by exact get_w.
  apply add_anons_delete in Hadd_anons; [ | now simpl_map].
  destruct Hadd_anons as (a & fresh_a & Hadd_anons).
  assert (valid_vpath (w .[[ q <- v]]) q) by now apply vset_same_valid.
  assert (valid_spath S' (anon_accessor a, q)).
  { eapply add_anons_valid_spath; [ | eassumption]. validity. }
  pose proof Hadd_anons as get_S'_v.
  eapply add_anons_sget with (p := (anon_accessor a, q)) in get_S'_v; [ | validity].
  autorewrite with spath in get_S'_v.
  eapply add_anons_sset with (p := (anon_accessor a, q)) in Hadd_anons; [ | validity].
  rewrite sset_anon in Hadd_anons by reflexivity.
  rewrite vset_twice_equal, vset_same in Hadd_anons.
  rewrite add_anons_alt in Hadd_anons.
  eapply AddAnons_insert in Hadd_anons; [ | now simpl_map | assumption].
  rewrite insert_delete_id, <-add_anons_alt in Hadd_anons by assumption.
  eexists _, a. split; [exact Hadd_anons | ].
  rewrite sset_sget_equal by assumption. autorewrite with spath. rewrite <-get_S'_v.
  autorewrite with spath. auto.
Qed.

Lemma not_contains_loan_abstraction_alter (A : Pmap value) j p v w :
  lookup j A = Some v ->
  not_contains_loan (v.[[p]]) ->
  map_Forall (fun _ => not_contains_loan) (alter (vset p w) j A) ->
  map_Forall (fun _ => not_contains_loan) A.
Proof.
  intros get_v ?.
  rewrite (alter_alt_Some _ _ _ _ get_v), <-insert_delete_eq, <-(insert_delete_id _ _ _ get_v).
  rewrite !map_Forall_insert, delete_insert_id by now simpl_map.
  intros (? & ?). split; [ | assumption]. not_contains.
Qed.

Lemma insert_is_alter (A B : Pmap value) i j v w f :
  lookup i A = None -> lookup j B = Some w -> insert i v A = alter f j B ->
  v = f w \/
  (i <> j /\ exists C, A = alter f j C /\ B = insert i v C).
Proof.
  intros Ai Bj H. destruct (decide (i = j)).
  - left. subst. apply (f_equal (lookup j)) in H.
    simpl_map. rewrite Bj in H. injection H. auto.
  - right. split; [assumption | ]. exists (delete i B). repeat split.
    + apply (f_equal (delete i)) in H.
      rewrite delete_insert_id, delete_alter_ne in H by congruence. exact H.
    + symmetry. apply insert_delete_id. apply (f_equal (lookup i)) in H. now simpl_map.
Qed.

Lemma insert_is_insert (A B : Pmap value) i j v w :
  lookup i A = None -> lookup j B = None -> insert i v A = insert j w B ->
  (i = j /\ v = w /\ A = B) \/
  (i <> j /\ exists C, A = insert j w C /\ B = insert i v C).
Proof.
  intros ? ? H. destruct (decide (i = j)).
  - left. split; [assumption | ]. subst. split.
    + apply (f_equal (lookup j)) in H. simpl_map. congruence.
    + apply (f_equal (delete j)) in H. rewrite !delete_insert_id in H; assumption.
  - right. split; [assumption | ]. exists (delete i B). repeat split.
    + apply (f_equal (delete i)) in H.
      rewrite delete_insert_id, delete_insert_ne in H by congruence. exact H.
    + symmetry. apply insert_delete_id. apply (f_equal (lookup i)) in H. now simpl_map.
Qed.

(* TODO: move *)
Lemma not_fresh_add_loan S i j A l ty : ~is_fresh l (S,,, i |-> insert j (loan^m(ty, l)) A).
Proof.
  set (S' := (S,,, i |-> insert j (loan^m(ty, l)) A)).
  assert (get_loan : S'.[(encode_abstraction (i, j), [])] = loan^m(ty, l)).
  { unfold S'. erewrite sget_add_abstraction; [ | reflexivity | now simpl_map]. reflexivity. }
  intros fresh_l. eapply fresh_l.
  - apply get_not_bot_valid_spath. rewrite get_loan. discriminate.
  - rewrite get_loan. reflexivity.
Qed.

Lemma reorg_local_preservation :
    forall p Sh q S'h, reorg_n q Sh S'h -> forall Sl, le_state_base_n p Sl Sh ->
    exists r s S'l, le_n r S'l S'h /\ reorg_n^{s} Sl S'l /\ r + s <= p + q.
Proof.
  intros a ? b ? Hreorg. destruct Hreorg.
  (* Case [Reorg_End_MutBorrow]: *)
  - intros c Hle. destruct Hle; destruct Hle.
    (* Case [Le_ToSymbolic]: *)
    + assert (disj sp p). solve_comp.
      autorewrite with spath in *. (* TODO: takes a bit of time. *)
      reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q); try eassumption.
        (* TODO: hint. *)
        eapply is_of_type_sset_rev; eauto with spath. constructor.
        eapply get_zeroary_not_strict_prefix'; eauto with spath.
        not_contains. }
      destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
      * autorewrite with spath in *.
        reorg_done.
        le_step_left.
        { econstructor.
          apply Le_ToSymbolic with (sp := p +++ r); autorewrite with spath; eassumption. }
        le_done. { states_eq. } { autorewrite with spath. cbn. lia. }
      * assert (disj sp q) by solve_comp.
        reorg_done.
        le_step_left.
        { econstructor. apply Le_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
        le_done. { states_eq. } { autorewrite with spath. lia. }
    (* Case [Le_ToAbs]: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath.
      le_step_left.
      { econstructor. apply Le_ToAbs; eauto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_RemoveAnon]: *)
    + reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath.
      le_step_left.
      { econstructor. apply Le_RemoveAnon; eauto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_MoveValue]: *)
    + destruct (decide (fst p = anon_accessor a)).
      * destruct (decide (fst q = anon_accessor a)).
        (* Case 1: the borrow and the loan are in the value we move. *)
        -- destruct Hdisj as [ | (_ & Hdisj)]; [congruence | ].
           autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow; try eassumption. eauto with spath.
             all: autorewrite with spath; try assumption. not_contains. solve_comp. }
           reorg_done. le_step_left.
           { econstructor. apply Le_MoveValue with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           le_done. { autorewrite with spath. reflexivity. } { reflexivity. }
        (* Case 2: the loan is in the value we move, not the borrow. *)
        -- rewrite sget_add_anon in * by assumption.
           assert (~prefix sp q) by solve_comp.
           autorewrite with spath in get_borrow.
           (* TODO: automate *)
           assert (~strict_prefix q sp).
           { apply sp_not_in_borrow. rewrite get_borrow. constructor. }
           assert (disj sp q). solve_comp. autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow; try eassumption. solve_comp. }
           reorg_done. le_step_left.
           { econstructor. apply Le_MoveValue with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           le_done. { states_eq. } { reflexivity. }
      * rewrite sget_add_anon in get_loan by assumption.
        assert (disj sp p). solve_comp.
        destruct (decide (fst q = anon_accessor a)).
        (* Case 3: the borrow is in the value we move, not the loan. *)
        -- autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow; try eassumption.
             all: autorewrite with spath; eauto with spath. solve_comp. }
           reorg_done. le_step_left.
           { econstructor. apply Le_MoveValue with (sp := sp) (a := a); autorewrite with spath.
             not_contains_outer. assumption. not_contains. assumption. assumption. }
           le_done. { states_eq. } { reflexivity. }
        (* Case 4: neither the borrow nor the loan is in the value we move. *)
        -- rewrite sget_add_anon in * by eassumption.
           assert (~prefix sp q) by solve_comp. autorewrite with spath in get_borrow.
           (* TODO: automate *)
           assert (~strict_prefix q sp).
           { apply sp_not_in_borrow. rewrite get_borrow. constructor. }
           assert (disj sp q) by solve_comp. autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow with (p := p) (q := q); eassumption. }
           reorg_done. le_step_left.
           { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
             all: autorewrite with spath; try assumption. validity. }
           le_done. { states_eq. } { reflexivity. }
    (* Case [Le_MergeAbs]: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q); autorewrite with spath; eassumption. }
      reorg_done. autorewrite with spath. le_step_left.
      { econstructor. apply Le_MergeAbs; eauto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_Abs_ClearValue]: *)
    + autorewrite with spath in *. reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q).
        all: autorewrite with spath; eassumption. }
      reorg_done. autorewrite with spath. le_step_left.
      { econstructor. apply Le_Abs_ClearValue; auto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_AnonValue]: *)
    + (* TODO: automate? *)
      assert (fst q <> anon_accessor a).
      { intros ?. autorewrite with spath in get_borrow. rewrite vget_bot in get_borrow. discriminate. }
      assert (fst p <> anon_accessor a).
      { intros ?. autorewrite with spath in get_loan. rewrite vget_bot in get_loan. discriminate. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q); eauto with spath. }
      reorg_done. le_step_left.
      { econstructor. apply Le_AnonValue with (a := a). eauto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_Fresh_MutLoan]: *)
    + destruct (decidable_spath_eq q (anon_accessor a, [])) as [-> | ].
      (* Case 1: the borrow we end is the newly introduced borrow of identifier l'. *)
      * (* We prove that l' = l. *)
        autorewrite with spath in get_borrow. inversion get_borrow. subst.
        (* The loan we end is the newly introduced loan. *)
        apply fresh_mut_loan_get_loan in get_loan; [ | exact fresh_l']. subst.
        (* Issues with rewrite sget_anon, and hints like [valid_spath_diff_fresh_anon] *)
          (* TODO: long. *) autorewrite with spath.
        (* The left state is just S,, a |-> bot. It does not contain the borrow of
         * loan id l. Thus, we don't have to do any reorganization step. *)
        reorg_done.
        (* We just have to do one step: adding an anonymous binding a |-> bot. *)
        le_step_left.
        { econstructor. apply Le_AnonValue with (a := a). assumption. }
        le_done. { reflexivity. } { lia. }
      * assert (fst q <> anon_accessor a).
        { eapply not_in_borrow_add_borrow_anon; eassumption. }
        rewrite sget_add_anon in * by assumption.
        assert (disj sp q) by solve_comp.
        autorewrite with spath in *.
        destruct (decide (fst p = anon_accessor a)).
        (* Case 2: the loan we end is in the anonymous binding a, containing the value of
         * the newly introduced loan. *)
        -- autorewrite with spath in get_loan.
           apply vget_borrow in get_loan; [ | discriminate].
           destruct get_loan as [(_ & [=]) | (r & G & get_loan)].
           autorewrite with spath in *. rewrite G.
           reorg_step.
           { eapply Reorg_End_MutBorrow; try eassumption. solve_comp. }
           reorg_done. le_step_left.
           { eapply Le_FreshLoan_n, Le_Fresh_MutLoan with (sp := sp) (l' := l') (a := a).
             eauto with spath. validity. eauto with spath.
             (* TODO: automate. *)
             autorewrite with spath. eapply vset_preserves_type; autorewrite with spath; eauto.
             (* TODO: for zeroary values, we should more easily derive their value
              * when we know their nodes. *)
             destruct (S.[sp +++ r]); inversion get_loan. constructor. not_contains. }
           le_done. { states_eq. } { reflexivity. }
        (* Case 3: the loan we end is disjoint from the anonymous binding a, containing the
           value of the newly introduced loan. *)
        -- autorewrite with spath in *.
           assert (disj sp p). solve_comp.
           (* TODO: automate *)
           { intros ->. autorewrite with spath in get_loan. inversion get_loan. subst.
             eapply fresh_l'; [ | rewrite get_borrow]; auto with spath. }
           autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow; eassumption. }
           reorg_done. le_step_left.
           { eapply Le_FreshLoan_n, Le_Fresh_MutLoan with (sp := sp) (l' := l') (a := a).
             eauto with spath. validity. assumption.
             autorewrite with spath. eassumption. not_contains. }
           le_done. { states_eq. } { reflexivity. }
    (* Case [Le_Reborrow_MutBorrow]: *)
    + (* The pointer we end cannot be in the anonymous binding a, because it contains a loan. *)
      assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ].
        intros ->. autorewrite with spath in Hno_loan. eapply Hno_loan; constructor. }
      rewrite sget_add_anon in * by assumption.
      destruct (decide (fst p = anon_accessor a)).
      (* Case 1: the borrow we end is the renamed borrow. *)
      * autorewrite with spath in get_loan. autorewrite with spath.
        apply vget_borrow_loan in get_loan; [ | discriminate].
        destruct get_loan as [(_ & [=]) | (-> & [=-> ->])].
        eapply (get_borrow_rename_mut_borrow S) in get_borrow; [ | eassumption..]. subst.
        reorg_done. (* We don't have any reorganization step to perform. *)
        autorewrite with spath in *. assert (not_contains_loan (S.[q])) as Hno_loan'.
        { rewrite sget_app in Hno_loan. destruct (S.[q]); inversion get_borrow_l0.
          eapply not_value_contains_unary; eauto with spath. }
        le_step_left.
        { econstructor. apply Le_MoveValue with (sp := q) (a := a). not_contains_outer.
          assumption. validity. assumption. assumption. }
        le_done.
        { rewrite sget_app. destruct (S.[q]); inversion get_borrow_l0. reflexivity. }
        { reflexivity. }
      (* Case 2: the borrow we end is different to the renamed borrow. *)
      * assert (sp <> p).
        { intros <-. rewrite sget_add_anon in get_loan by assumption.
          rewrite sset_sget_equal in get_loan by validity. discriminate. }
        autorewrite with spath in get_loan, Hnot_in_borrow.
        assert (l1 <> l).
        { intros ->. eapply fresh_l1; [ | rewrite get_loan; reflexivity]. validity. }
        assert (~prefix sp q). eapply prove_not_prefix.
        (* TODO: automate *)
        { eapply sset_sget_diff; [eassumption | cbn; congruence | discriminate]. }
        { eapply Hnot_in_borrow. autorewrite with spath. constructor. }
        autorewrite with spath in *.
        reorg_step.
        { apply Reorg_End_MutBorrow with (p := p) (q := q) (l := l) (ty := ty); try assumption.
          (* TODO: automate. *)
          eapply is_of_type_rename_mut_borrow; eassumption.
          eapply not_contains_rename_mut_borrow; try eassumption. inversion 1. }
        reorg_done.
        destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
        (* Case 2a: the renamed borrow is in the ended borrow. *)
        -- autorewrite with spath in get_borrow_l0. le_step_left.
           { eapply Le_FreshLoan_n, Le_Reborrow_MutBorrow with (l1 := l1) (a := a) (sp := p +++ r).
             eauto with spath. autorewrite with spath. eassumption. assumption.
             autorewrite with spath in Htype |- *. exact Htype. not_contains. }
           le_done. { states_eq. } { reflexivity. }
           (* Case 2b: the renamed borrow is disjoint from the from the ended borrow. *)
        -- assert (disj sp q) by solve_comp. autorewrite with spath. le_step_left.
           { eapply Le_FreshLoan_n, Le_Reborrow_MutBorrow with (l1 := l1) (a := a) (sp := sp).
             eauto with spath. autorewrite with spath. eassumption. assumption.
             (* TODO: automate. *)
             autorewrite with spath.
             eapply is_of_type_sset_sget; [eassumption | ..].
             eapply is_of_type_rename_mut_borrow; eassumption.
             destruct (S.[p]); inversion get_loan; constructor. not_contains. }
           le_done. { states_eq. } { reflexivity. }
    (* Case [Le_Borrow_Abstraction]: *)
    + assert (fst p <> anon_accessor a).
      { intros ?. autorewrite with spath in get_loan.
        assert (not_contains_loan (borrow^m(l', VSymbolic ty'))) as G by not_contains.
        apply (G (snd p)); [validity | rewrite get_loan; constructor]. }
      autorewrite with spath in get_loan.
      assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ]. intros ->.
        autorewrite with spath in get_borrow. inversion get_borrow. subst.
        apply (fresh_l' p); [validity | ].
        autorewrite with spath. rewrite get_loan. constructor. }
      autorewrite with spath in *.
      reorg_step.
      { eapply Reorg_End_MutBorrow with (p := p) (q := q).
        all: autorewrite with spath; eassumption. }
      reorg_done.
      autorewrite with spath. le_step_left.
      { eapply Le_FreshLoan_n, Le_Borrow_Abstraction with (j := j) (ty' := ty') (l' := l') (a := a).
        auto with spath. assumption. auto with spath. not_contains. }
      le_done. { reflexivity. } { lia. }

  (* Case [Reorg_End_MutBorrow_in_abstraction]: *)
  - intros ? Hle. remember (S,,, i' |-> (insert j' (loan^m(ty, l)) A')) as _S eqn:EQN.
    destruct Hle; destruct Hle; subst.
    (* Case [Le_ToSymbolic]: *)
    + destruct (decide (in_abstraction i' (fst sp))) as [(j & Hj) | ].
      * process_state_eq.
        assert (valid_spath (S,,, i' |-> B) sp) as (w & get_w & valid_sp) by validity.
        rewrite Hj, get_at_abstraction in get_w. cbn in get_w. simpl_map. cbn in get_w.
        erewrite sget_add_abstraction in * |- by eassumption.
        eapply insert_is_alter in eq_abs; [ | eassumption..].
        destruct eq_abs as [contradiction | (? & C & -> & ->)].
        -- eapply vset_same_valid in valid_sp. rewrite <-contradiction in valid_sp.
          apply valid_vpath_zeroary in valid_sp; [ | reflexivity].
          rewrite valid_sp in contradiction. discriminate.
        -- simpl_map. reorg_step.
           { apply Reorg_End_MutBorrow_in_abstraction with (q := q); assumption. }
           reorg_done. le_step_left.
           { econstructor. apply Le_ToSymbolic with (sp := sp).
             all: erewrite sget_add_abstraction; eassumption. }
           erewrite sset_add_abstraction, !sget_add_abstraction
             by (try eassumption; simpl_map; reflexivity).
           le_done. { reflexivity. } { lia. }
      * process_state_eq.
        assert (~prefix sp q) by solve_comp. autorewrite with spath in *.
        reorg_step.
        { apply Reorg_End_MutBorrow_in_abstraction with (q := q); try assumption.
          (* TODO: automate *)
          eapply is_of_type_sset_rev; try eassumption. constructor. solve_comp. not_contains. }
        reorg_done.
        destruct (decidable_prefix (q +++ [0]) sp) as [(r & <-) | ].
        -- le_done. { states_eq. } { autorewrite with spath weight. lia. }
        -- assert (disj sp q) by solve_comp. le_step_left.
           { econstructor. apply Le_ToSymbolic with (sp := sp).
             all: autorewrite with spath; eassumption. }
           le_done. { states_eq. } { autorewrite with spath. lia. }
    (* Case [Le_ToAbs]: *)
    + process_state_eq.
      * inversion Hto_abs.
        -- assert (j' = kl /\ l = l1 /\ ty0 = ty) as (-> & <- & ->).
           { apply (f_equal (lookup j')) in H1. simpl_map.
             apply lookup_insert_Some in H1. destruct H1 as [ | (_ & H1)]; [easy | ].
             rewrite lookup_singleton_Some in H1. destruct H1 as (<- & get_loan).
             inversion get_loan. auto. }
           apply (f_equal (delete kl)) in H1.
           rewrite delete_insert_id, delete_insert_ne, delete_singleton_eq in H1 by
           auto.
           subst. reorg_step.
           { eapply Reorg_End_MutBorrow with (p := (anon_accessor a, []) +++ [0]) (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath. le_step_left.
           { econstructor. apply Le_ToAbs with (i := i') (a := a); eauto with spath.
             apply ToAbs_MutBorrow with (k := kb); [eassumption.. | ].
             (* For the moment, typed values do not contain borrows. *)
             inversion type_borrow; not_contains. }
           le_done.
           { reflexivity. }
           { autorewrite with weight. lia. }
        (* The abstraction H does not contain loans, we can eliminate this case. *)
        -- apply (f_equal (lookup j')) in H1. simpl_map. apply lookup_singleton_Some in H1.
           destruct H1. discriminate.
      * autorewrite with spath in * |-.
        rewrite <-add_abstraction_add_anon. reorg_step.
        { apply Reorg_End_MutBorrow_in_abstraction with (q := q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done.
      autorewrite with spath. le_step_left.
      { econstructor. apply Le_ToAbs; eauto with spath. }
      le_done.
      { (* TODO: states_eq *) rewrite add_abstraction_commute by congruence. reflexivity. }
      { lia. }
    (* Case [Le_RemoveAnon]: *)
    + autorewrite with spath in fresh_a.
      rewrite <-add_abstraction_add_anon. reorg_step.
      { apply Reorg_End_MutBorrow_in_abstraction with (q := q).
        all: autorewrite with spath; eauto with spath. }
      reorg_done. autorewrite with spath.
      le_step_left.
      { econstructor. apply Le_RemoveAnon; auto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_MoveValue]: *)
    + process_state_eq. destruct (decide (fst q = anon_accessor a)).
      (* Case 1: the borrow we end is in the anonymous binding a that contains the moved
       * value. *)
      * autorewrite with spath in *.
        rewrite <-add_abstraction_add_anon. reorg_step.
        { apply Reorg_End_MutBorrow_in_abstraction with (q := sp +++ snd q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done. le_step_left.
        { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
          all: autorewrite with spath; eauto with spath. not_contains_outer. }
        le_done; autorewrite with spath. { reflexivity. } { lia. }
      * autorewrite with spath in valid_sp.
        assert (~prefix sp q).
        { intros (? & <-). autorewrite with spath in get_borrow.
          rewrite vget_bot in get_borrow. discriminate. }
        autorewrite with spath in *.
        (* TODO: lemma. *)
        assert (~prefix (q +++ [0]) sp).
        { intros (r & <-).
          pose proof valid_sp.
          rewrite valid_spath_app in valid_sp. destruct valid_sp as (? & ?).
          autorewrite with spath in type_borrow. eapply is_of_type_does_not_contain_bot.
          - exact type_borrow.
          - apply vset_same_valid. assumption.
          - autorewrite with spath. reflexivity. }
        assert (disj sp q) by solve_comp. autorewrite with spath in * |-.
        reorg_step.
        { eapply Reorg_End_MutBorrow_in_abstraction with (i' := i') (j' := j') (q := q).
          all: eauto with spath. }
        reorg_done. le_step_left.
        { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
          all: autorewrite with spath; eauto with spath. }
        le_done. { states_eq. } { autorewrite with spath. lia. }
    (* Case [Le_MergeAbs]: *)
    + process_state_eq.
      * eapply merge_abstractions_contains in Hmerge; [ | eassumption].
        destruct Hmerge as [(A'' & -> & G & Hmerge) | (B'' & k & -> & G & Hmerge)].
        -- rewrite add_abstraction_commute by congruence. reorg_step.
           { apply Reorg_End_MutBorrow_in_abstraction with (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath. rewrite add_abstraction_commute by congruence.
           le_step_left.
           { econstructor. apply Le_MergeAbs; eauto with spath. }
           le_done.
           { reflexivity. }
           { autorewrite with weight. lia. }
        -- reorg_step.
           { apply Reorg_End_MutBorrow_in_abstraction with (q := q).
             all: autorewrite with spath; eauto with spath. }
           reorg_done.
           autorewrite with spath. le_step_left.
           { econstructor. apply Le_MergeAbs; eauto with spath. }
           le_done.
           { reflexivity. }
           { autorewrite with weight. lia. }
      * autorewrite with spath in * |-.
        apply fresh_abstraction_add_abstraction_rev in fresh_j. destruct fresh_j.
        rewrite !(add_abstraction_commute _ i') by congruence.
        reorg_step.
        { apply Reorg_End_MutBorrow_in_abstraction with (q := q).
          all: autorewrite with spath; eauto with spath. }
        reorg_done.
        autorewrite with spath. rewrite <-!(add_abstraction_commute _ i') by congruence.
        le_step_left.
        { econstructor. apply Le_MergeAbs; eauto with spath. }
        le_done. { reflexivity. } { lia. }
    (* Case [Le_Abs_ClearValue]: *)
    + process_state_eq.
      * rewrite lookup_insert_None in fresh_j. destruct fresh_j as (fresh_j & ?).
        rewrite insert_insert_ne by congruence.
        reorg_step.
        { apply Reorg_End_MutBorrow_in_abstraction with (q := q); try assumption.
          simpl_map. assumption. }
        reorg_done. le_step_left.
        { econstructor. apply Le_Abs_ClearValue; auto with spath. }
        le_done. { reflexivity. } { lia. }
      * autorewrite with spath in *.
        reorg_step.
        { rewrite add_abstraction_commute by congruence.
          apply Reorg_End_MutBorrow_in_abstraction with (q := q).
          all: autorewrite with spath; assumption. }
        reorg_done. autorewrite with spath. le_step_left.
        { rewrite add_abstraction_commute by congruence.
          econstructor. apply Le_Abs_ClearValue; auto with spath. }
        le_done.
        { rewrite add_abstraction_commute by congruence. reflexivity. }
        { lia. }
    (* Case [Le_AnonValue]: *)
    + process_state_eq.
      assert (fst q <> anon_accessor a).
      { intros ?. autorewrite with spath in get_borrow.
        rewrite vget_bot in get_borrow. discriminate. }
      autorewrite with spath in *. reorg_step.
      { apply Reorg_End_MutBorrow_in_abstraction with (q := q); assumption. }
      reorg_done. le_step_left.
      { econstructor. apply Le_AnonValue with (a := a). auto with spath. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_Fresh_MutLoan]: *)
    + process_state_eq.
      assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ]. intros ->.
        autorewrite with spath in get_borrow. inversion get_borrow. subst.
        eapply not_fresh_add_loan. eassumption. }
      rewrite sget_add_anon in * by assumption. autorewrite with spath in valid_sp.
      assert (disj sp q) by solve_comp.
      autorewrite with spath in *.
      rewrite <-add_abstraction_add_anon. reorg_step.
      { apply Reorg_End_MutBorrow_in_abstraction with (q := q); eassumption. }
      reorg_done. le_step_left.
      { eapply Le_FreshLoan_n, Le_Fresh_MutLoan with (l' := l') (a := a) (sp := sp).
        all: eauto with spath. autorewrite with spath. eassumption. not_contains. }
      le_done. { states_eq. } { lia. }
    (* Case [Le_Reborrow_MutBorrow]: *)
    + process_state_eq.
      assert (fst q <> anon_accessor a).
      { eapply not_in_borrow_add_borrow_anon; [eassumption | ].
        intros ->. autorewrite with spath in Hno_loan. eapply loan_contains_loan, Hno_loan. }
      rewrite sget_add_anon in * by assumption. autorewrite with spath in get_borrow_l0.
      assert (disj q sp). apply prove_disj.
      (* The node q contains a borrow of loan identifier l <> l1 (freshness of l1). *)
      { intros <-. autorewrite with spath in get_borrow. inversion get_borrow; subst.
        eapply not_fresh_add_loan; eassumption. }
      (* If sp is in q, there is a nested borrow (sp in q), and we currently do not handle
       * nested borrows. *)
      (* Eventually, we are going to lift this restriction. There will be two cases to
       * consider, one of them being that q is a strict prefix of sp. *)
      { eapply not_prefix_one_child.
        - rewrite length_children_is_arity, get_borrow. reflexivity.
        - validity.
        - assert (valid_spath S1 sp) as valid_sp by validity.
          intros (r & <-). apply valid_spath_app in valid_sp. destruct valid_sp.
          autorewrite with spath in type_borrow.
          eapply is_of_type_does_not_contain_borrow.
          + exact type_borrow.
          + apply vset_same_valid. assumption.
          + autorewrite with spath. constructor. }
      (* q is not in a borrow. *)
      { intros (? & ? & <-). eapply Hnot_in_borrow with (q := sp).
        - autorewrite with spath. constructor.
        - eexists _, _; reflexivity. }
      assert (sp <> q +++ [0]). { intros ->. eapply not_prefix_disj; eauto with spath. }
      autorewrite with spath in *.
      reorg_step.
      { apply Reorg_End_MutBorrow_in_abstraction with (q := q); assumption. }
      reorg_done. le_step_left.
      { eapply Le_FreshLoan_n, Le_Reborrow_MutBorrow with (l0 := l0) (l1 := l1) (a := a) (sp := sp).
        all: autorewrite with spath; eauto with spath. not_contains. }
      le_done. { states_eq. } { lia. }
    (* Case [Le_Borrow_Abstraction]: *)
    + process_state_eq.
      (* Case 1: the loan we end is in the abstraction we add a loan with [Le_Borrow_Abstraction_n] *)
       * apply insert_is_insert in eq_abs; [ | assumption..].
         destruct eq_abs as [(<- & [=-> ->] & <-) | (? & B & -> & ->)].
         (* Case 1a: the loan we end is the loan we added with [Le_Borrow_Abstraction_n]. *)
         -- assert (q = (anon_accessor a, [])) as ->.
            { apply dec_stable.
              intros K. eapply not_in_borrow_add_borrow_anon in K; [ | eassumption].
              autorewrite with spath in get_borrow.
              eapply fresh_l' with (p := q); [validity | ].
              autorewrite with spath. rewrite get_borrow. constructor. }
            autorewrite with spath.
            (* The reorganization step at the right only ended borrow introduced by
               rule [Le_Borrow_Abstraction_n]. Thus, there is no reorganization to
               do en the left. *)
            reorg_done.
            le_step_left.
            { econstructor. apply Le_AnonValue with (a := a). auto with spath. }
            le_done. { reflexivity. } { lia. }
         (* Case 1b: the loan we end is another loan in thi abstraction. *)
         -- simpl_map.
             assert (fst q <> anon_accessor a).
             { eapply not_in_borrow_add_borrow_anon; [eassumption | ]. intros ->.
               autorewrite with spath in get_borrow. inversion get_borrow. subst.
               eapply not_fresh_add_loan. eassumption. }
             autorewrite with spath in *.
             reorg_step.
             { apply Reorg_End_MutBorrow_in_abstraction with (q := q); assumption. }
             reorg_done.
             le_step_left.
             { eapply Le_FreshLoan_n, Le_Borrow_Abstraction with (j := j) (l' := l') (a := a).
               all: auto with spath. not_contains. }
             le_done. { reflexivity. } { lia. }
       (* Case 2: the loan we end is in another abstraction. *)
       * assert (fst q <> anon_accessor a).
         { eapply not_in_borrow_add_borrow_anon; [eassumption | ]. intros ->.
           autorewrite with spath in get_borrow. inversion get_borrow. subst.
           rewrite <-add_abstraction_commute in fresh_l' by congruence.
           eapply not_fresh_add_loan. eassumption. }
         autorewrite with spath in *.
         reorg_step.
         { rewrite add_abstraction_commute by congruence.
           apply Reorg_End_MutBorrow_in_abstraction with (q := q).
           all: autorewrite with spath; assumption. }
         reorg_done.
         autorewrite with spath. rewrite !(add_abstraction_commute _ i) by congruence.
         le_step_left.
         { eapply Le_FreshLoan_n, Le_Borrow_Abstraction with (j := j) (l' := l') (a := a).
           all: auto with spath. not_contains. }
         le_done. { reflexivity. } { lia. }

  (* Case [Reorg_End_Abstraction]: *)
  - intros ? Hle. remember (S,,, i' |-> A') as _S eqn:EQN.
    destruct Hle; destruct Hle.
    (* Case Le_ToSymbolic *)
    + destruct (decide (in_abstraction i' (fst sp))) as [(j & Hj) | ].
      * process_state_eq.
        assert (valid_spath (S,,, i' |-> B) sp) as valid_sp by validity.
        destruct sp as (? & q). cbn in Hj. subst.
        apply in_abstraction_valid_spath in valid_sp. destruct valid_sp as (w & ? & ?).
        erewrite sget_add_abstraction in * by eauto.
        cbn in A_no_loans, Hadd_anons.
        eapply add_anons_abstraction_set in Hadd_anons; [ | eassumption | validity].
        destruct Hadd_anons as (S'' & a & Hadd_anons & -> & get_S''_a_q).
        reorg_step.
        { apply Reorg_End_Abstraction. eassumption.
          eapply not_contains_loan_abstraction_alter; eassumption. eassumption. }
        reorg_done. le_step_left.
        { econstructor. apply Le_ToSymbolic; rewrite get_S''_a_q; eassumption. }
        le_done.
        { reflexivity. }
        { rewrite get_S''_a_q. cbn. lia. }
      * process_state_eq. autorewrite with spath in *.
        apply add_anons_sset_rev in Hadd_anons; [ | validity].
        destruct Hadd_anons as (S'' & Hadd_anons & ->).
        reorg_step.
        { eapply Reorg_End_Abstraction; eassumption. }
        reorg_done. le_step_left.
        { econstructor. apply Le_ToSymbolic; erewrite add_anons_sget; eauto with spath. }
        le_done.
        { reflexivity. }
        { erewrite add_anons_sget by eauto with spath. lia. }
    (* Case Le_ToAbs *)
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      (* Case 1: we end the abstraction we just introduced. *)
      * destruct EQN as (<- & -> & <-). destruct Hto_abs.
        (* Case 1.a: a reborrow is turned into a region. But we can't end a region that
         * contains a loan. We eliminate this case by contradiction. *)
        -- exfalso. rewrite map_Forall_lookup in A_no_loans.
           eapply A_no_loans with (i := kl).
           simpl_map. reflexivity. constructor. constructor.
           (* Case 1.b. *)
        -- apply add_anons_singleton in Hadd_anons. destruct Hadd_anons as (b & fresh_b & ->).
           (* If v is an integer, we must perform an extra relation step to turn it into a
            * symbolic value. Because when we end the region A, the anonymous binding introduced
            * is a symbolic value. *)
           reorg_done.
           le_step_left.
           { econstructor. apply Le_ToSymbolic with (sp := (anon_accessor a, []) +++ [0]).
             all: autorewrite with spath; eassumption. }
           autorewrite with spath. le_done.
           { eapply prove_equiv_states; [reflexivity | ].
             apply equiv_states_add_anon; assumption. }
           { autorewrite with weight. lia. }

      (* Case 2: the abstraction we introduce and the abstraction we end are
       * different. *)
      * destruct EQN as (_ & S1 & -> & ->).
        apply fresh_abstraction_add_abstraction_rev in fresh_i', fresh_i.
        destruct fresh_i'. destruct fresh_i as (fresh_i & _).
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (? & -> & Hadd_anons).
        rewrite fresh_anon_add_abstraction in fresh_a.
        apply add_anons_add_anon with (a := a) (v := v) in Hadd_anons; [ | assumption].
        destruct Hadd_anons as (S'1 & Hadd_anons & ? & ?).
        assert (fresh_abstraction S'1 i).
        { apply add_anons_fresh_abstraction with (i := i) in Hadd_anons; eauto with spath. }
        reorg_step.
        { rewrite <-add_abstraction_add_anon.
          apply Reorg_End_Abstraction; eauto with spath. }
        reorg_done. le_step_left.
        { econstructor. apply Le_ToAbs; eassumption. }
        le_done.
        { eapply prove_equiv_states; [reflexivity | ].
          apply equiv_add_abstraction; assumption. }
        { lia. }
    (* Case [Le_RemoveAnon]: *)
    + subst. rewrite fresh_anon_add_abstraction in fresh_a.
        apply add_anons_add_anon with (a := a) (v := v) in Hadd_anons; [ | assumption].
        destruct Hadd_anons as (S'' & Hadd_anons & ? & ?).
      reorg_step.
        { rewrite <-add_abstraction_add_anon.
          apply Reorg_End_Abstraction; eauto with spath. }
        reorg_done. le_step_left.
        { econstructor. apply Le_RemoveAnon; eassumption. }
        le_done. { eapply prove_equiv_states; easy. } { lia. }
    (* Case [Le_MoveValue]: *)
    + process_state_eq. autorewrite with spath in * |-.
      apply add_anons_remove_anon_sset in Hadd_anons; [ | assumption..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_End_Abstraction; eauto with spath. }
      reorg_done. le_step_left.
      { econstructor. apply Le_MoveValue with (sp := sp) (a := a).
        all: autorewrite with spath; eauto with spath.
        erewrite add_anons_sget by eauto with spath. eassumption.
        eapply add_anons_valid_spath; eassumption.
        eapply not_in_borrow_add_anons; eauto with spath. }
      le_done.
      { erewrite add_anons_sget by eassumption. reflexivity. }
      { reflexivity. }
    (* Case [Le_MergeAbs]: *)
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      * destruct EQN as (<- & -> & <-).
        assert (map_Forall (fun _ => not_contains_loan) B) by eauto using merge_no_loan.
        destruct Hmerge as (A' & B' & Hremove_loans & union_A'_B').
        destruct (exists_add_anons (S,,, i |-> A) B) as (Sl1 & HSl1).
        (* Ending the region B: *)
        reorg_step.
        { eapply Reorg_End_Abstraction. eauto with spath. assumption. exact HSl1. }
        eapply end_removed_loans with (i := i) in Hremove_loans;
          [ | exact fresh_i | exact HSl1].
        destruct Hremove_loans as (n & s & Sbots & Sl2 & Hadd_bots & Hn & reorg_Sl2 & Hadd_anons_Sl2 & ?).
        (* Ending all the borrows in the difference between B and B': *)
        reorg_steps. { exact reorg_Sl2. }
        destruct (exists_add_anons Sl2 A') as (Sl3 & HSl3).
        (* Ending the region A: *)
        reorg_step.
        { apply Reorg_End_Abstraction. assumption.
           (* TODO: lemma *)
           intros ? ? G. eapply union_contains_left in G; [ | exact union_A'_B'].
           eapply A_no_loans. eassumption. eassumption. }
        reorg_done.

        edestruct commute_add_anonymous_bots_anons as (Sl1' & Hadd_anons_Sl1' & Hadd_bots_Sl2);
          [exact Hadd_bots | exact Hadd_anons_Sl2 | ].
        edestruct commute_add_anonymous_bots_anons as (Sl2' & Hadd_anons_Sl2' & Hadd_bots_Sl3);
          [exact Hadd_bots_Sl2 | exact HSl3 | ].
        eapply le_n_steps.
        { eapply le_n_add_anonymous_bots. eassumption. }
        le_done.
        { eapply add_anons_assoc; eassumption. }
        { eapply map_sum_union_maps in union_A'_B'. rewrite union_A'_B'. lia. }
      * destruct EQN as (? & ? & -> & ->).
        autorewrite with spath in * |-.
        apply fresh_abstraction_add_abstraction_rev in fresh_j. destruct fresh_j.
        rewrite !(add_abstraction_commute _ i') by congruence.
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (S'' & -> & Hadd_anons).
        reorg_step.
        { apply Reorg_End_Abstraction. eauto with spath. assumption.
          repeat apply add_abstraction_add_anons. eassumption. }
        reorg_done.
        le_step_left.
        { econstructor. apply Le_MergeAbs; eauto with spath. }
        le_done. { reflexivity. } { lia. }
    (* Case [Le_Abs_ClearValue]: *)
    + process_state_eq.
      * destruct (exists_fresh_anon S') as (a & fresh_a).
        eapply add_anons_insert with (v := v) in Hadd_anons; [ | eassumption..].
        reorg_step.
        { eapply Reorg_End_Abstraction; try eassumption. apply map_Forall_insert_2; auto. }
        reorg_done.
        le_step_left.
        { econstructor. apply Le_RemoveAnon; assumption. }
        le_done. { reflexivity. } { lia. }
      * autorewrite with spath in *.
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (S2 & -> & Hadd_anons).
        reorg_step.
        { rewrite add_abstraction_commute. apply Reorg_End_Abstraction. auto with spath.
          assumption. apply add_abstraction_add_anons. eassumption. congruence. }
        reorg_done. le_step_left.
        { econstructor. apply Le_Abs_ClearValue with (v := v); try assumption.
          eapply add_anons_fresh_abstraction; eassumption. }
        le_done. { reflexivity. } { lia. }
    (* Case [Le_AnonValue]: *)
    + process_state_eq.
      apply add_anons_remove_anon in Hadd_anons; [ | assumption].
      destruct Hadd_anons as (S'' & -> & ? & Hadd_anons).
      reorg_step.
      { eapply Reorg_End_Abstraction; eassumption. }
      reorg_done. le_step_left.
      { econstructor. apply Le_AnonValue. eassumption. }
      le_done. { reflexivity. } { lia. }
    (* Case [Le_Fresh_MutLoan]: *)
    + process_state_eq.
      apply not_in_abstraction_valid_spath in valid_sp; [ | eauto].
      apply add_anons_remove_anon_sset in Hadd_anons; [ | assumption..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_End_Abstraction; eauto with spath. }
      reorg_done.
      autorewrite with spath in Htype |- *.
      le_step_left.
      { eapply Le_FreshLoan_n, Le_Fresh_MutLoan with (sp := sp) (a := a) (l' := l').
        all: autorewrite with spath; eauto with spath.
        eapply add_anons_valid_spath; eassumption.
        erewrite add_anons_sget by eauto with spath. eassumption.
        eapply is_fresh_add_anons; eassumption. }
      le_done.
      { erewrite add_anons_sget by eassumption. reflexivity. }
      { reflexivity. }
    (* Case [Le_Reborrow_MutBorrow]: *)
    + process_state_eq. autorewrite with spath in *.
      apply add_anons_remove_anon_sset in Hadd_anons; [ | eauto with spath..].
      destruct Hadd_anons as (S'' & Hadd_anons & -> & ?).
      reorg_step.
      { apply Reorg_End_Abstraction; eauto with spath. }
      reorg_done. le_step_left.
      { eapply Le_FreshLoan_n, Le_Reborrow_MutBorrow.
        all: autorewrite with spath; eauto with spath.
        erewrite add_anons_sget; eauto with spath.
        erewrite add_anons_sget; eauto with spath.
        eapply is_fresh_add_anons; eassumption. }
      le_done.
      { erewrite add_anons_sget by eauto with spath. reflexivity. }
      { reflexivity. }
    (* Case [Le_Borrow_Abstraction]: *)
    + process_state_eq.
      (* The loan we add with [Le_Borrow_Abstraction_n] cannot be in the
         abstraction we end. *)
      * exfalso. eapply A_no_loans; [apply lookup_insert_eq | constructor..].
      * (* TODO: unconsistent lemma naming. *)
        apply add_anons_remove_anon in Hadd_anons; [ | auto with spath].
        destruct Hadd_anons as (_S & -> & ? & Hadd_anons).
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (S' & -> & Hadd_anons).
        autorewrite with spath in * |-.
        reorg_step.
        { rewrite add_abstraction_commute by congruence.
          apply Reorg_End_Abstraction. auto with spath. assumption.
          apply add_abstraction_add_anons. eassumption. }
        reorg_done. le_step_left.
        { eapply Le_FreshLoan_n, Le_Borrow_Abstraction with (j := j) (l' := l') (a := a).
          all: eauto with spath.
          rewrite add_abstraction_commute in fresh_l' by congruence.
          eapply is_fresh_add_anons; [ | eassumption | ].
          auto with spath. apply add_abstraction_add_anons. assumption. }
        le_done. { reflexivity. } { lia. }
Qed.

Lemma reorg_preserve_equiv n :
  forward_simulation equiv_states equiv_states (reorg_n n) (reorg_n n).
Proof.
  intros S0 S1 Hreorg S'0 Hequiv. symmetry in Hequiv. destruct Hequiv as (perm & Hperm & ->).
  destruct Hreorg.
  - execution_step.
    { eapply Reorg_End_MutBorrow with (p := permutation_spath perm p)
                                     (q := permutation_spath perm q).
      all: eauto with spath.
      rewrite permutation_sget, get_node_rename_value, get_loan; eauto with spath.
      rewrite permutation_sget, get_node_rename_value, get_borrow; eauto with spath.
      all: autorewrite with spath; eauto with spath. }
    assert (subseteq (loan_set_val (S .[q +++ [0] ])) (dom (loan_id_names perm))).
    { etransitivity; [apply loan_set_sget | apply Hperm]. }
    symmetry. eexists. autorewrite with spath. auto with spath.

  - apply remove_abstraction_perm_equivalence in Hperm; [ | assumption].
    destruct Hperm as (perm_S & p & perm_A & -> & Hloan_set).
    edestruct (is_permutation_delete _ _ _ _ fresh_j' perm_A) as (? & ? & ? & ?).
    execution_step.
    { erewrite <-vsize_rename_value, <-permutation_sget, <-permutation_spath_app;
        [ | eassumption | validity].
      autorewrite with spath. rewrite fmap_insert.
      erewrite apply_permutation_insert;
        [ | apply perm_A | simpl_map; now rewrite fresh_j' | eassumption].
      eapply prove_rel_n.
      - eapply Reorg_End_MutBorrow_in_abstraction
        with (q := permutation_spath (remove_abstraction_perm perm i') q);
        autorewrite with spath; eauto with spath.
        { now apply lookup_pkmap_None. }
        { rewrite get_borrow. reflexivity. }
      - autorewrite with spath. reflexivity.
      - reflexivity. }
    rewrite loan_set_abstraction_insert in Hloan_set by assumption.
    apply union_subseteq in Hloan_set. destruct Hloan_set as (_ & Hloan_set).
    symmetry. eexists. split; [eauto with spath | autorewrite with spath; reflexivity].

  - process_state_equivalence. autorewrite with spath.
    set (S0 := apply_state_permutation (remove_abstraction_perm perm i') S).
    set (B := apply_permutation p (rename_set (loan_id_names perm) A')).
    destruct (exists_add_anons S0 B) as (S'0 & Hadd_anons').
    execution_step.
    { apply Reorg_End_Abstraction; [eauto with spath | | exact Hadd_anons'].
      eauto with spath. unfold B. rewrite pkmap_fmap by apply map_inj_equiv, perm_A.
      apply map_Forall_fmap. apply permutation_forall; [assumption | ].
      intros ? ? ?. eauto with spath. }
    symmetry. eapply add_anons_equiv; eassumption.
Qed.

Lemma reorg_preserves_LLBC_plus_rel : forward_simulation le_symbolic le_symbolic reorg^* reorg^*.
Proof.
  eapply preservation_reorg_l.
  - exact le_state_base_n_decreases.
  - exact reorg_decreases.
  - exact reorg_preserve_equiv.
  - exact le_n_equiv_states_commute.
  - exact reorg_local_preservation.
  - exact le_state_base_n_is_le_state_base.
  - reflexivity.
Qed.

(** * Simulation proofs for statement evaluation. *)
(** The LLBC+ rules for statement [E_Seq_Unit_Propagate], [E_IfThenElse_Symbolic] and [E_Loop_Continue] require exhibiting a "join state" of two states [B0] and [B1]. Let take the general form for the diagram:
<<
Sl <= Sr
|     |
v     v
Bl <= Br
>>

   This kind of square diagrams is tricky, because we must exhibit the "join state" [Bl] so that we can prove the statement evaluation [Sl |-{stmt} s ~>{n} Bl]. To do so, we must know the states [B0] and [B1], but these states can be quite complex. Finally, the exact join state [Bl] is not really important. It can be the result of the function [exists_join_state B0 B1 Br]. What only matters is that the states [B0] and [B1] are related to [Br].

   The following lemma (and the associated tactic) removes the need to exhibit a state [Bl]. The proof of the evaluation is conducted first. The branching state [Bl] and the "join" property [Hjoin_l : is_join ?B0 ?B1 Bl] are assumed. When the assumption [Hjoin_l] is used, it determine the values of [B0] and [B1], that were introduced as existential variables. It is only after that the relations [B0 <= Br] and [B1 <= Br] are shown.
 *)
(* TODO: lemma and tactic names. *)
Lemma execution_join_state n s Sl (B0 B1 Br : branching_state) :
  (forall Bl, is_join B0 B1 Bl -> Sl |-{stmt} s ~>{n} Bl) ->
  le_branching B0 Br ->
  le_branching B1 Br ->
  exists Bl, le_branching Bl Br /\ Sl |-{stmt} s ~>{n} Bl.
Proof.
  intros G le_0 le_1. destruct (exists_join_state _ _ _ le_0 le_1) as (? & ?).
  exists (compute_join B0 B1 Br). auto.
Qed.
Ltac execution_join_state :=
  let Bjoin_l := fresh "Bjoin_l" in
  let Hjoin_l := fresh "Hjoin_l" in
  eapply execution_join_state; [intros Bjoin_l Hjoin_l | | ].

Lemma boolean_does_not_contain_symbolic b : not_contains_symbolic (VBool b).
Proof. not_contains. Qed.

Lemma le_val_state_base_boolean vl Sl b Sr :
  le_val_state_base (vl, Sl) (VBool b, Sr) -> vl = VBool b /\ le_state_base Sl Sr.
Proof.
  inversion 1 as [ | | ? ? ? ? ? ? ? fuck G |  ? ? ? ? ? ? ? ? ? ? ? ? shit G]; subst.
  - split; [reflexivity | econstructor; eassumption].
  - split; [reflexivity | eapply Le_FreshLoan; eassumption].
  - exfalso. eapply boolean_does_not_contain_symbolic with (p := vp).
    + rewrite <-G. apply vset_same_valid. validity.
    + rewrite <-G. autorewrite with spath. constructor.
  - exfalso. apply boolean_does_not_contain_borrow with (v := VBool b) (p := vp).
    + constructor.
    + rewrite <-G. apply vset_same_valid. validity.
    + rewrite <-G. autorewrite with spath. constructor.
Qed.

Lemma _le_val_state_boolean vSl b Sr :
  le_val_state_base^* vSl (VBool b, Sr) ->
  let (vl, Sl) := vSl in vl = VBool b /\ le_state_base^* Sl Sr.
Proof.
  intros H. remember (VBool b, Sr) as vSr eqn:EQN. revert Sr EQN.
  induction H as [(v & S) | (vl & Sl) (vm & Sm) (vr & Sr) ? IH le_step]
    using clos_refl_trans_ind_left';
    intros ?; inversion 1; subst.
  - split; reflexivity.
  - apply le_val_state_base_boolean in le_step. destruct le_step as (-> & ?).
    edestruct IH as (? & ?); [reflexivity | ].
    split; [assumption | ]. etransitivity; [ | constructor]; eassumption.
Qed.

Lemma le_val_state_boolean vSl b Sh :
  le_val_state vSl (VBool b, Sh) -> let (vl, Sl) := vSl in vl = VBool b /\ le_symbolic Sl Sh.
Proof.
  intros ((v'h & S'h) & H & G).
  apply _le_val_state_boolean in G. destruct G as (-> & G).
  symmetry in H. destruct vSl. destruct H as (perm & ? & _ & -> & ->).
  split; [reflexivity | ]. eexists. split; [ | exact G]. symmetry. exists perm. eauto.
Qed.

Lemma le_val_state_base_symbolic_boolean vl Sl Sh :
  le_val_state_base (vl, Sl) (VSymbolic TBool, Sh) ->
  ((exists b, vl = VBool b) \/ vl = VSymbolic TBool) /\ le_state_base^* Sl Sh.
Proof.
  inversion 1 as [ | | ? ? ? ? ? ? ? fuck G |  ? ? ? ? ? ? ? ? ? ? ? ? shit G]; subst.
  - split; [auto | constructor; econstructor; eassumption].
  - split; [auto | constructor; eapply Le_FreshLoan; eassumption].
  - split; [ | reflexivity]. assert (vp = []) as ->.
    { eapply valid_vpath_zeroary with (v := VSymbolic TBool).
      - reflexivity.
      - rewrite <-G. apply vset_same_valid. validity. }
    inversion G. subst. inversion Htype; eauto.
    exfalso. eapply no_loan with (p := []). validity. rewrite <-H1. constructor.
  - exfalso. apply boolean_does_not_contain_borrow with (v := VSymbolic TBool) (p := vp).
    + constructor.
    + rewrite <-G. apply vset_same_valid. validity.
    + rewrite <-G. autorewrite with spath. constructor.
Qed.

Lemma _le_val_state_symbolic_boolean vSl Sh :
  le_val_state_base^* vSl (VSymbolic TBool, Sh) ->
  let (vl, Sl) := vSl in
  ((exists b, vl = VBool b) \/ vl = VSymbolic TBool) /\ le_state_base^* Sl Sh.
Proof.
  intros H. remember (VSymbolic TBool, Sh) as vSh eqn:EQN. revert Sh EQN.
  induction H as [(v & S) | (vl & Sl) (vm & Sm) (vh & Sh) H IH le_step]
    using clos_refl_trans_ind_left';
    intros ?; inversion 1; subst.
  - split; [auto | reflexivity].
  - apply le_val_state_base_symbolic_boolean in le_step.
    destruct le_step as ([(b & ->) | ->] & ?).
    + apply _le_val_state_boolean in H. destruct H. split; [eauto | ]. now transitivity Sm.
    + edestruct IH as (? & ?); [reflexivity | ]. split; [assumption | ]. now transitivity Sm.
Qed.

Lemma le_val_state_symbolic_boolean vSl Sh :
  le_val_state vSl (VSymbolic TBool, Sh) ->
  let (vl, Sl) := vSl in
  ((exists b, vl = VBool b) \/ vl = VSymbolic TBool) /\ le_symbolic Sl Sh.
Proof.
  intros ((v'h & S'h) & H & G).
  apply _le_val_state_symbolic_boolean in G. destruct G as (Hv'h & G).
  symmetry in H. destruct vSl. destruct H as (perm & ? & _ & -> & ->).
  split.
  - destruct Hv'h as [(b & ->) | ->]; eauto.
  - eexists. split; [ | exact G]. symmetry. exists perm. eauto.
Qed.

Lemma le_end_loop Bl Br : le_branching Bl Br -> le_branching (end_loop Bl) (end_loop Br).
Proof.
  intros H r. destruct (lookup r (end_loop Bl)) eqn:EQN.
  - pose proof EQN as G.
    apply mk_is_Some, lookup_pkmap_rev in G; [ | exact partial_inj_end_loop_tag].
    destruct G as (r0 & get_r).
    unfold end_loop, branching_state in *.
    erewrite lookup_pkmap in EQN |- * by exact get_r || exact partial_inj_end_loop_tag.
    specialize (H r0). unfold branching_state in H. rewrite EQN in H.
    inversion H. constructor. assumption.
  - constructor.
Qed.
Hint Resolve le_end_loop : spath.

Lemma le_branching_None_left_branch Bl Br r :
  le_branching Bl Br -> lookup r Br = None -> lookup r Bl = None.
Proof.
  intros Hle G. specialize (Hle r). rewrite G in Hle. inversion Hle. reflexivity.
Qed.
Hint Resolve le_branching_None_left_branch : spath.

Lemma lookup_token_cases Bl Br Sr r :
  le_branching Bl Br -> lookup r Br = Some Sr ->
  (lookup r Bl = None /\ le_branching Bl (delete r Br) \/
   exists Sl, lookup r Bl = Some Sl /\
              le_symbolic Sl Sr /\ le_branching (delete r Bl) (delete r Br)).
Proof.
  intros Hle_B Hcontinue.
  pose proof (Hle_B r) as Hle_S. apply (le_branching_delete r) in Hle_B.
  rewrite Hcontinue in Hle_S.
  destruct (lookup r Bl) as [Sl | ] eqn:EQN.
  - inversion Hle_S; subst. eauto.
  - rewrite (delete_id _ _ EQN) in Hle_B. auto.
Qed.

Lemma end_loop_delete_rContinue B : end_loop (delete rContinue B) = end_loop B.
Proof.
  destruct (lookup rContinue B) as [S | ] eqn:EQN.
  - apply insert_delete_id in EQN. rewrite <-EQN at 2.
    unfold end_loop. rewrite pkmap_insert.
    + reflexivity.
    + apply partial_inj_end_loop_tag.
    + apply lookup_delete_eq.
  - now setoid_rewrite delete_id.
Qed.

Lemma stmt_preserves_LLBC_plus_rel n s :
  forward_simulation le_symbolic le_branching (eval_stmt n s) (eval_stmt n s).
Proof.
  intros Sr S'r Heval. induction Heval; intros Sl Hle.
  (* Case [E_Step_Zero] *)
  - execution_step. { constructor. } reflexivity.

  (* Case [E_Nop]. *)
  - execution_step. { constructor. } apply le_singleton. assumption.
  (* Case [E_Panic]. *)
  - execution_step. { constructor. } apply le_singleton. assumption.
  (* Case [E_Break]. *)
  - execution_step. { constructor. } apply le_singleton. assumption.
  (* Case [E_Continue]. *)
  - execution_step. { constructor. } apply le_singleton. assumption.

  (* Case [E_Propagate] *)
  - specialize (IHHeval _ Hle). destruct IHHeval as (Bl & ? & ?).
    execution_step.
    { apply E_Seq_Propagate; eauto with spath. }
    assumption.

  (* Case [E_Seq_Unit_Propagate] *)
  - specialize (IHHeval1 _ Hle). destruct IHHeval1 as (B1l & Hle1 & ?).
    eapply lookup_token_cases in Hle1; [ | exact H_unit].
    destruct Hle1 as [(? & ?) | (S1l & ? & Hle1 & ?)].
    (* Case 1: the state after the execution of the first statement ([B1_l]) does not contain
        a [rUnit] token, we simply propagate. *)
    + execution_step. { apply E_Seq_Propagate; eassumption. }
      etransitivity; eauto with spath.
    (* Case 2. *)
    + specialize (IHHeval2 _ Hle1). destruct IHHeval2 as (B_unit_l & Hle2 & Heval2_l).
      execution_join_state.
      { eapply E_Seq_Unit_Propagate; eassumption. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }

  (* Case [E_Assign] *)
  - destruct vS' as (vr & S'r).
    assert (not_contains_bot vr). { eapply eval_rvalue_no_bot. eassumption. }
    assert (not_contains_loan vr). { eapply eval_rvalue_no_loan. eassumption. }
    apply rvalue_preserves_le in eval_rv. specialize (eval_rv _ Hle).
    destruct eval_rv as ((v'l & S'l) & ? & ?).
    eapply store_preserves_LLBC_plus_rel in Hstore; [ | eassumption..].
    destruct Hstore as (S''l & Hstore & ?).
    execution_step. { econstructor; eassumption. }
    apply le_singleton. assumption.

  (* Case [E_IfThenElse_T] *)
  - apply operand_preserves_le in eval_cond. apply eval_cond in Hle.
    destruct Hle as ((v' & S'l) & Hle' & eval_cond').
    apply le_val_state_boolean in Hle'. destruct Hle' as (-> & Hle').
    apply IHHeval in Hle'. destruct Hle' as (S''l & Hle'' & eval_if).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [E_IfThenElse_F] *)
  - apply operand_preserves_le in eval_cond. apply eval_cond in Hle.
    destruct Hle as ((v' & S'l) & Hle' & eval_cond').
    apply le_val_state_boolean in Hle'. destruct Hle' as (-> & Hle').
    apply IHHeval in Hle'. destruct Hle' as (S''l & Hle'' & eval_else).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [E_IfThenElse_Symbolic] *)
  - apply operand_preserves_le in eval_cond. apply eval_cond in Hle.
    destruct Hle as ((v' & S'l) & Hle' & eval_cond').
    apply le_val_state_symbolic_boolean in Hle'.
    destruct Hle' as ([([ | ] & ->) | ->] & Hle').
    (* Case 1: the symbolic value abstracts the boolean true. We apply the rule [E_IfThenElse_T]. *)
    + apply IHHeval1 in Hle'. destruct Hle' as (B''l & Hle'' & eval_if).
      execution_step. { econstructor; eassumption. }
      transitivity B_if; eauto using le_is_join_l.
    (* Case 2: the symbolic value abstracts the boolean false. We apply the rule [E_IfThenElse_F]. *)
    + apply IHHeval2 in Hle'. destruct Hle' as (B''l & Hle'' & eval_else).
      execution_step. { econstructor; eassumption. }
      transitivity B_else; eauto using le_is_join_r.
    (* Case 3: the symbolic value abstracts a symbolic value. *)
    + specialize (IHHeval1 _ Hle'). destruct IHHeval1 as (Bl_if & Hle'_l & eval_if).
      specialize (IHHeval2 _ Hle'). destruct IHHeval2 as (Bl_else & Hle'_r & eval_else).
      execution_join_state.
      { eapply E_IfThenElse_Symbolic; eassumption. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }

  (* Case [E_Reorg] *)
  - eapply reorg_preserves_LLBC_plus_rel in Hreorg. specialize (Hreorg _ Hle).
    destruct Hreorg as (S'l & Hle' & ?).
    specialize (IHHeval _ Hle'). destruct IHHeval as (? & ? & ?).
    execution_step. { econstructor; eassumption. } assumption.

  (* Case [E_Loop_Stop] *)
  - apply IHHeval in Hle. destruct Hle as (B1l & Hle' & Heval').
    execution_step.
    { apply E_Loop_Stop; eauto with spath. }
    auto with spath.

  (* Case [E_Loop_Continue] *)
  - apply IHHeval1 in Hle. destruct Hle as (B1_l & Hle' & Heval').
    eapply lookup_token_cases in Hcontinue; [ | exact Hle'].
    destruct Hcontinue as [(? & ?) | (S1_l & ? & Hle_S1 & ?)].
    + execution_step.
      { eapply E_Loop_Stop; eauto with spath. }
      etransitivity; [eauto with spath | ].
      rewrite end_loop_delete_rContinue. eauto with spath.
    + apply IHHeval2 in Hle_S1. destruct Hle_S1 as (B2_l & Hle'' & Heval2_l).
      execution_join_state.
      { eapply E_Loop_Continue; eauto with spath. }
      { etransitivity; eauto with spath. }
      { etransitivity; eauto with spath. }
Qed.
