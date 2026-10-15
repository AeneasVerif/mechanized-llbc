(** * Mechanized_LLBC.simulations.Simulation_HLPL_plus : Simulation proofs for HLPL+. *)
Require Import lang.
Require Import base.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree.
From rustc Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import HLPL_plus.
Require Import SimulationUtils.

(** * Well-formedness property. *)
Record well_formed (S : state) : Prop := {
  at_most_one_mut_borrow l : at_most_one_node (nborrow^m(l)) S;
  at_most_one_mut_loan l : at_most_one_node (nloan^m(l)) S;
  no_mut_loan_ptr l p : get_node (S.[p]) = nloan^m(l) -> not_state_contains (eq nptr(l)) S;
  no_mut_loan_loc l p : get_node (S.[p]) = nloan^m(l) -> not_state_contains (eq nloc(l)) S;
}.

Notation scount c S := (sweight (indicator c) S).

(** To automate well-formedness proofs, we use an equivalent linear property. *)
Record well_formed_alt (S : state) l : Prop := {
  at_most_one_mut_borrow_alt : scount (nborrow^m(l)) S <= 1;
  no_mut_loan_alt : scount (nloan^m(l)) S <= 1;
  no_mut_loan_ptr_loc_alt :
    scount (nloan^m(l)) S > 0 -> (scount (nloc(l)) S + scount (nptr(l)) S) <= 0;
}.

Lemma well_formedness_equiv S : well_formed S <-> forall l, well_formed_alt S l.
Proof.
  split.
  - intros WF l. destruct WF. split.
    + rewrite<- decide_at_most_one_node; easy.
    + rewrite<- decide_at_most_one_node; easy.
    + intros (p & _ & H%indicator_non_zero)%sweight_non_zero.
      symmetry in H. specialize (no_mut_loan_loc0 _ _ H). specialize (no_mut_loan_ptr0 _ _ H).
      rewrite Nat.le_0_r, Nat.eq_add_0.
      split; eapply not_state_contains_implies_weight_zero;
        try apply indicator_non_zero; assumption.
  - intros WF. split; intros l; destruct (WF l).
    + apply decide_at_most_one_node; [discriminate | ]. assumption.
    + apply decide_at_most_one_node; [discriminate | ]. assumption.
    + intros p Hp.
      assert (valid_p : valid_spath S p) by validity.
      apply weight_sget_node_le with (weight := indicator (nloan^m(l))) in valid_p.
      rewrite Hp in valid_p. autorewrite with weight in valid_p.
      intros q valid_q Hq.
      apply weight_sget_node_le with (weight := indicator (nptr(l))) in valid_q.
      rewrite <-Hq in valid_q. autorewrite with weight in valid_q.
      lia.
    + intros p H.
      assert (valid_p : valid_spath S p) by validity.
      apply weight_sget_node_le with (weight := indicator (nloan^m(l))) in valid_p.
      rewrite H, indicator_same in valid_p.
      assert (scount (nloc(l)) S = 0) by lia.
      intros q valid_q Hq.
      apply weight_sget_node_le with (weight := indicator (nloc(l))) in valid_q.
      autorewrite with weight in valid_q. lia.
Qed.

(** Rewriting lemmas for weight computation. *)
(* Note: would it be possible to use [cbn [weight]] instead? *)
Lemma vweight_loc weight l v :
  vweight weight (loc(l, v)) = weight (nloc(l)) + vweight weight v.
Proof. reflexivity. Qed.

Lemma vweight_ptr weight l : vweight weight (ptr(l)) = weight (nptr(l)).
Proof. reflexivity. Qed.

Lemma vweight_int weight n :
  vweight weight (VInt n) = weight (NInt n).
Proof. reflexivity. Qed.

Lemma vweight_bool weight b :
  vweight weight (VBool b) = weight (NBool b).
Proof. reflexivity. Qed.

Lemma vweight_bot weight : vweight weight bot = weight (nbot).
Proof. reflexivity. Qed.

Hint Rewrite vweight_loc : weight.
Hint Rewrite vweight_ptr : weight.
Hint Rewrite vweight_int : weight.
Hint Rewrite vweight_bool : weight.
Hint Rewrite vweight_bot : weight.

Lemma le_base_preserves_wf_r Sl Sr : well_formed Sr -> le_base Sl Sr -> well_formed Sl.
Proof.
  rewrite !well_formedness_equiv.
  intros H G l0. specialize (H l0). destruct H. destruct G.
  - destruct (decide (l0 = l)) as [<- | ]; split; weight_inequality.
Qed.

(** * Automation. *)
(** A tactic to prove that a value or state does not contain some node (ex: loan, loc, bot).
    This tactic tries to solve this by applying the relevant lemmas, and never fails. *)
(* Note: Can we remove the automatic rewriting out of this tactic? *)
(* TODO: precise the "workflow" of this tactic. *)
Ltac not_contains0 :=
  try assumption;
  match goal with
  | |- True => auto
  | |- not_state_contains ?P (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset;
      not_contains0
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset_disj;
        [auto with spath; fail | not_contains0]
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset;
       [ not_contains0 | not_contains0 | validity0]
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget _ S p H);
      validity0
  | |- not_value_contains ?P (?v.[[?p <- ?w]]) =>
      simple apply not_value_contains_vset; not_contains0
  | |- not_value_contains ?P (?S.[?p]) => idtac

  | |- not_value_contains ?P ?v =>
      simple apply not_value_contains_zeroary; [reflexivity | ]
  | |- not_value_contains ?P ?v =>
      simple eapply not_value_contains_unary; [reflexivity | | not_contains0]
  | |- not_value_contains ?P ?v =>
      simple eapply not_value_contains_nary; [reflexivity | | not_contains0]
  | |- _ => idtac
  end.
Ltac not_contains := not_contains0; eauto with spath.

Ltac not_contains_outer :=
  (* The values we use this tactic on are of the form
     (S,, Anon |-> v) (.[ sp <- v])* .[sp]
     where the path sp we read is a path of S. We first do some rewritings to commute
     the read with the writes and the addition of the anonymous value. *)
  autorewrite with spath;
  try assumption;
  match goal with
  | |- not_contains_outer _ ?P (?v.[[?p <- ?w]]) =>
      let H := fresh "H" in
      assert (H : not_value_contains P w) by auto with spath;
      eapply not_contains_implies_not_contains_outer in H;
      apply not_contains_outer_vset;
        [not_contains_outer | exact H]
  | no_outer_loan : not_contains_outer_loan (?S.[?q]),
    loan_at_q : get_node (?S.[?q +++ ?p]) = nloan^m(?l)
    |- not_contains_outer _ ?P (?S.[?q].[[?p <- ?w]]) =>
    apply not_contains_outer_vset_in_borrow;
     [ not_contains_outer |
       apply no_outer_loan;
         [ validity | rewrite<- (sget_app S q p), loan_at_q; constructor] ]
  | |- not_contains_outer _ _ _ =>
      idtac
  end.

(** * Simulation proofs for place evaluation. *)
Lemma eval_path_app S perm P Q p q r :
  eval_path S perm P p q -> eval_path S perm Q q r -> eval_path S perm (P ++ Q) p r.
Proof.
  induction 1.
  - auto.
  - intros ?. cbn. eapply E_Path_Proj; eauto.
  - intros ?. eapply E_Path_Loc; eauto.
Qed.

Lemma eval_path_preservation Sl Sr perm P R
  (proj_sim : forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_path Sl perm [proj]))
  (eval_loc_sim : forward_simulation R R (eval_loc Sr perm) (eval_loc Sl perm)) :
  forward_simulation R R (eval_path Sr perm P) (eval_path Sl perm P).
Proof.
  intros ? ? Heval_path. induction Heval_path.
  - intros ? ?. eexists. split; [eassumption | constructor].
  - intros pi_l HR.
    edestruct proj_sim as (pi_l' & ? & ?); [eassumption.. | ].
    edestruct IHHeval_path as (pi_l'' & ? & ?); [eassumption | ].
    exists pi_l''. split.
    + eassumption.
    + replace (proj :: P) with ([proj] ++ P) by reflexivity.
      eapply eval_path_app; eassumption.
  - intros pi_l HR.
    edestruct eval_loc_sim as (pi_l' & ? & ?); [eassumption.. | ].
    edestruct IHHeval_path as (pi_l'' & ? & ?); [eassumption | ].
    exists pi_l''. split.
    + eassumption.
    + eapply E_Path_Loc; eassumption.
Qed.

(* This lemma is use to prove preservation of place evaluation for a relation rule Sl < Sr.
 * We prove that if p evaluates to a spath pi_r on Sr, then it also evaluates for a spath
 * pi_l on the left, with R pi_l pi_r.
 * The relation R depends on the rule, but for most rules it is simply going to be the equality. *)
Lemma eval_place_preservation Sl Sr perm p (R : spath -> spath -> Prop)
  (* Initial case: the relation R must be preserved for all spath corresponding to a variable. *)
  (R_nil : forall x, R (encode_var x, []) (encode_var x, []))
  (* All of the variables of Sr are variables of Sl.
   * Since most of the time, Sr is Sl with alterations on anonymous variables or by sset, this is
   * always true. *)
  (dom_eq : dom (vars Sl) = dom (vars Sr))
  (proj_sim : forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_path Sl perm [proj]))
  (eval_loc_sim : forward_simulation R R (eval_loc Sr perm) (eval_loc Sl perm))
  :
  forall pi_r, eval_place Sr perm p pi_r -> exists pi_l, R pi_l pi_r /\ eval_place Sl perm p pi_l.
Proof.
  intros pi_r ((? & G%mk_is_Some & _) & Heval_path).
  cbn in G. unfold encode_var in G. rewrite sum_maps_lookup_l in G.
  rewrite <-elem_of_dom, <-dom_eq, elem_of_dom, <-get_at_var in G. destruct G as (? & ?).
  eapply eval_path_preservation in Heval_path; [ | eassumption..].
  edestruct Heval_path as (pi_l' & ? & ?); [apply R_nil | ].
  exists pi_l'. split; [assumption | ]. split; [ | assumption].
  eexists. split; [eassumption | constructor].
Qed.

Lemma sset_preserves_vars_dom S sp v : dom (vars (S.[sp <- v])) = dom (vars S).
Proof.
  unfold sset. unfold alter_at_accessor. cbn. repeat autodestruct.
  intros. apply dom_alter_L.
Qed.

(* Note: instead of defining a relation between a left spath p and a right path q, I could define
 * the left spath q as a function of p. *)
Definition rel_MutBorrow_to_Ptr sp_loan sp_borrow p q :=
  (exists r, p = sp_loan +++ [0] ++ r /\ q = sp_borrow +++ [0] ++ r) \/
  (p = q /\ ~strict_prefix sp_borrow p).

Lemma eval_place_mut_borrow_to_ptr perm p S_r l0 sp_loan sp_borrow :
  let S_l := (S_r.[sp_loan <- loc(l0, S_r.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l0)]) in
  disj sp_loan sp_borrow ->
  get_node (S_r.[sp_loan]) = nloan^m(l0) ->
  get_node (S_r.[sp_borrow]) = nborrow^m(l0) ->
  forall pi_r, eval_place S_r perm p pi_r ->
  exists pi_l, rel_MutBorrow_to_Ptr sp_loan sp_borrow pi_l pi_r /\
    eval_place S_l perm p pi_l.
Proof.
  intros S_l Hdisj Hsp_loan Hsp_borrow. unfold S_l.
  apply eval_place_preservation.
  - right. eauto with spath.
  - rewrite !sset_preserves_vars_dom. reflexivity.
  - intros ? pi_r ? eval_pi_r. destruct eval_pi_r.
    (* Case E_Deref_MutBorrow: *)
    + intros ? [(r & -> & ->) | (-> & ?) ].
      (* pi_r is in the mutable loan and pi_l is in the loc *)
      * execution_step.
        { eapply E_Path_Proj.
          { eapply E_Deref_MutBorrow; autorewrite with spath; eassumption. }
          apply E_Path_Nil. }
        left. exists (r ++ [0]). autorewrite with spath. split; reflexivity.
      * destruct (decidable_spath_eq sp_borrow q) as [<- | ].
        -- execution_step.
           ++ eapply E_Path_Proj.
              { eapply E_Deref_Ptr_Loc with (q' := sp_loan).
                assumption. all: autorewrite with spath; reflexivity. }
              eapply E_Path_Loc.
              { econstructor; autorewrite with spath; easy. }
              apply E_Path_Nil.
           ++ left. exists []. split; reflexivity.
        -- assert (~prefix sp_borrow q) by solve_comp.
           execution_step.
           ++ eapply E_Path_Proj.
              { eapply E_Deref_MutBorrow; autorewrite with spath; eassumption. }
              apply E_Path_Nil.
           ++ right. split; [reflexivity | solve_comp].
    (* Case E_Deref_Ptr_Loc: *)
    + intros q_l H.
      assert (get_at_q_l : get_node (S_l.[q_l]) = nptr(l)).
      { unfold S_l. destruct H as [(r & -> & ->) | (-> & ?)]; autorewrite with spath; assumption. }
      destruct (decidable_prefix (sp_borrow +++ [0]) q') as [(r & <-) | ].
      * autorewrite with spath in *. exists (sp_loan +++ [0] ++ r). split.
        -- left. eexists. eauto.
        -- eapply E_Path_Proj.
           ++ eapply E_Deref_Ptr_Loc with (q' := sp_loan +++ [0] ++ r);
                [assumption | exact get_at_q_l | ].
              autorewrite with spath. assumption.
           ++ apply E_Path_Nil.
      * exists q'. split.
        -- right. split; [reflexivity | solve_comp].
        -- eapply E_Path_Proj.
           { eapply E_Deref_Ptr_Loc with (q' := q'); [assumption | exact get_at_q_l | ].
             autorewrite with spath. assumption. }
           apply E_Path_Nil.
  - intros pi_r ? eval_pi_r. destruct eval_pi_r. intros ? [(r & -> & ->) | (-> & ?)].
    + execution_step.
      * econstructor; autorewrite with spath; eassumption.
      * autorewrite with spath. left. eexists. split; reflexivity.
    + exists (q +++ [0]). split.
      * right. split; [reflexivity | solve_comp].
      * econstructor; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_mut_borrow_to_ptr_Mov p S_r l0 sp_loan sp_borrow :
  let S_l := (S_r.[sp_loan <- loc(l0, S_r.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l0)]) in
  forall pi, eval_place S_r Mov p pi -> eval_place S_l Mov p pi /\ ~strict_prefix sp_borrow pi.
Proof.
  intros S_l pi H. unfold S_l.
  eapply eval_place_preservation
    with (R := (fun pi_l pi_r => pi_l = pi_r /\ ~strict_prefix sp_borrow pi_r)) in H.
  - destruct H as (? & (-> & ?) & ?). split; eassumption.
  - split; eauto with spath.
  - rewrite !sset_preserves_vars_dom. reflexivity.
  (* Evaluating a projection cannot be performed in mode Mov. *)
  - intros ? ? ? eval_pi_r. destruct eval_pi_r; contradiction.
  (* Going under a loc cannot be performed in move Mov. *)
  - intros ? ? eval_pi_r. destruct eval_pi_r; contradiction.
Qed.

(** Take a store operation [store p (vr, Sr) S'r]. It is possible to apply
   the rule [Le_MutBorrow_To_Ptr] where the mutable borrow is in [vr], and the mutable loan in [Sr].
   In this case, we have to relate place evaluation [Sr] to place evaluation in [Sr.[sp_loan <- loc(l0, v)]]
   with [v] the value in the mutable borrow in [vr].
   We prove a special lemma for this case. *)
Lemma eval_place_mut_loan_to_loc p S_r l0 sp_loan v :
  let S_l := (S_r.[sp_loan <- loc(l0, v)]) in
  get_node (S_r.[sp_loan]) = nloan^m(l0) ->
  forall pi, eval_place S_r Mut p pi -> eval_place S_l Mut p pi /\ ~strict_prefix sp_loan pi.
Proof.
  intros S_l Hsp_loan pi H. unfold S_l.
  eapply eval_place_preservation
    with (R := (fun pi_l pi_r => pi_l = pi_r /\ ~strict_prefix sp_loan pi_r)) in H.
  - destruct H as (? & (-> & ?) & ?). split; eassumption.
  - split; eauto with spath.
  - rewrite !sset_preserves_vars_dom. reflexivity.
  - intros ? ? ? eval_pi_r ? (-> & ?). destruct eval_pi_r.
    (* Case E_Deref_MutBorrow: *)
    + eexists. split. { split; [reflexivity | solve_comp]. }
      eapply E_Path_Proj.
      { eapply E_Deref_MutBorrow; autorewrite with spath; eassumption. }
      apply E_Path_Nil.
    (* Case E_Deref_Ptr_Loc: *)
    + eexists. split. { eauto with spath. }
      eapply E_Path_Proj.
      { eapply E_Deref_Ptr_Loc with (q' := q'); autorewrite with spath; eassumption. }
      apply E_Path_Nil.
  - intros pi_r ? eval_pi_r ? (-> & ?). destruct eval_pi_r.
    eexists. split. { eauto with spath. }
    econstructor; [discriminate | autorewrite with spath; eassumption].
Qed.

(** This tactic is used to prove a goal of the form [?vSl < (vr, Sr)] without
    exhibiting the existential variable [?vSl]. *)
Ltac le_step_right :=
  lazymatch goal with
  (** When proving a goal [le ?vSl (vr, Sr)], this tactic creates three subgoals:
      - [le_base ?vSm (Sr,, a |-> v)]
      - [?vSm = ?Sm,, a |-> ?vm]
      - [le ?vSl (?vm, ?Sm)] *)
  | |- ?le_star ?vSl (?vr, ?Sr) =>
      let a := fresh "a" in
      let H := fresh "H" in
      eapply prove_le_val_state_right_to_left;
        [intros a H; rewrite <-?fresh_anon_sset in H; eexists; split | ]
  | |- ?le_star ?Sl ?Sr => eapply le_step_right
  end.

(** Suppose that [Sl < Sr], and that p evaluates to a spath [pi] in [Sr]
   ([Sr |-{p} p =>^{perm} pi]).
    This tactic chooses the right lemmas to apply in order to prove that [p] reduces to a spath pi' in Sl, and generates facts about pi'.
   Finally, it proves that [pi] is valid in [Sr], and clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  lazymatch goal with
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{Mov} ?pi,
    _ : get_node (?Sr.[?sp_loan]) = nloan^m (?l),
    _ : get_node (?Sr.[?sp_borrow]) = nborrow^m(?l) |- _ =>
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let sp_borrow_not_prefix := fresh "sp_borrow_not_prefix" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_valid in valid_p;
      apply eval_place_mut_borrow_to_ptr_Mov
        with (sp_loan := sp_loan) (sp_borrow := sp_borrow) (l0 := l)
        in eval_p_in_Sr;
      destruct eval_p_in_Sr as (eval_p_in_Sl & sp_borrow_not_prefix)
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{ _ } ?pi_r,
    Hdisj : disj ?sp_loan ?sp_borrow,
    HSr_loan : get_node (?Sr.[?sp_loan]) = nloan^m (?l),
    HSr_borrow : get_node (?Sr.[?sp_borrow]) = nborrow^m(?l) |- _ =>
      let pi_l := fresh "pi_l" in
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_valid in valid_p;
      apply (eval_place_mut_borrow_to_ptr _ _ _ _ _ _ Hdisj HSr_loan HSr_borrow)
        in eval_p_in_Sr;
      destruct eval_p_in_Sr as (pi_l & rel_pi_l_pi_r & eval_p_in_Sl)
  end.

(** * Simulation proofs for operand evaluation. *)
Lemma copy_val_no_mut_loan v w : copy_val v w -> not_contains_loan v.
Proof.
  induction 1.
  - apply not_value_contains_zeroary; easy.
  - apply not_value_contains_zeroary; easy.
  - apply not_value_contains_zeroary; easy.
  - eapply not_value_contains_unary; [reflexivity | easy | assumption].
Qed.

Lemma copy_val_no_mut_borrow v w : copy_val v w -> not_value_contains is_mut_borrow v.
Proof.
  induction 1.
  - apply not_value_contains_zeroary; easy.
  - apply not_value_contains_zeroary; easy.
  - apply not_value_contains_zeroary; easy.
  - eapply not_value_contains_unary; [reflexivity | easy | assumption].
Qed.

Definition forward_simulation_eval_operand :=
  forall op, forward_simulation le_base^* (le_val_state_base le_base)^* (eval_operand op) (eval_operand op).

Lemma operand_preserves_HLPL_plus_rel op :
  forward_simulation le_base^* (le_val_state_base le_base)^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr vrS'r Heval Sl Hle.
  induction Heval.

  (* op = Const (IntConst n) *)
  - destruct Hle.
    + execution_step. { constructor. }
      le_step_right.
      { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

  (* op = Const (BoolConst b) *)
  - destruct Hle.
    + execution_step. { constructor. }
      le_step_right.
      { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

  (* op = Copy p *)
  - destruct Hle.
    + eval_place_preservation.
      assert (~prefix pi sp_loan).
      { eapply not_value_contains_not_prefix.
        - eapply copy_val_no_mut_loan. eassumption.
        - rewrite HS_loan. constructor.
        - validity. }
      assert (disj pi sp_loan) by solve_comp.
      assert (~prefix pi sp_borrow).
      { eapply not_value_contains_not_prefix.
        - eapply copy_val_no_mut_borrow. eassumption.
        - rewrite HS_borrow. constructor.
        - validity. }
      destruct rel_pi_l_pi_r as [(r & -> & ->) | (-> & ?)].
      * execution_step.
        { econstructor. eassumption. autorewrite with spath. eassumption. }
        le_step_right.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * assert (disj pi sp_borrow) by solve_comp.
        execution_step.
        { econstructor. eassumption. autorewrite with spath. eassumption. }
        le_step_right.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.

  (* op = Move p *)
  - destruct Hle.
    eval_place_preservation.
    assert (disj pi sp_loan) by solve_comp.
    destruct (decidable_prefix pi sp_borrow) as [(q & <-) | ].
    (* Case 1: the mutable borrow we're transforming to a pointer is in the moved value. *)
    * execution_step.
      { constructor. eassumption. all: autounfold with spath; not_contains. }
      le_step_right.
      { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                        (sp_borrow := (anon_accessor a, q)).
        eauto with spath. all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      states_eq.
    (* Case 2: the mutable borrow is disjoint from the moved value. *)
    * assert (disj pi sp_borrow) by solve_comp.
      execution_step.
      { constructor. eassumption. all: autorewrite with spath; assumption. }
      le_step_right.
      { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      states_eq.
Qed.

(* TODO: move in base.v *)
Inductive well_formed_state_value : value * state -> Prop :=
  | WF_vS v S (WF : forall a, fresh_anon S a -> well_formed (S,, a |-> v)) :
      well_formed_state_value (v, S).

Inductive well_formed_alt_state_value : value * state -> loan_id -> Prop :=
  | WF_alt_vS v S l (WF : forall a, fresh_anon S a -> well_formed_alt (S,, a |-> v) l) :
      well_formed_alt_state_value (v, S) l.

Lemma well_formedness_state_value_equiv vS :
  well_formed_state_value vS <-> forall l, well_formed_alt_state_value vS l.
Proof.
  split.
  - intros []. setoid_rewrite well_formedness_equiv in WF. constructor. auto.
  - intros H. destruct vS. constructor. intros ? ?. rewrite well_formedness_equiv.
    intros l. specialize (H l). inversion H. auto.
Qed.

Lemma copy_preserves_well_formedness S p v w :
  copy_val v w -> S.[p] = v -> well_formed S -> well_formed_state_value (w, S).
Proof.
  rewrite well_formedness_equiv, well_formedness_state_value_equiv.
  intros eval_copy get_S_p WF. revert p get_S_p.
  induction eval_copy; intros p get_S_p l0; constructor; intros a.
  + specialize (WF l0). destruct WF. split; weight_inequality.
  + specialize (WF l0). destruct WF. split; weight_inequality.
  + specialize (WF l0). destruct WF. split.
    * weight_inequality.
    * weight_inequality.
    * assert (valid_p : valid_spath S p) by validity.
      pose proof (weight_sget_node_le (indicator (nptr(l))) _ _ valid_p) as G.
      rewrite get_S_p in G. cbn in G. autorewrite with weight in G.
      destruct (decide (l = l0)) as [<- | ]; weight_inequality.
  + apply (f_equal (vget [0])) in get_S_p. autorewrite with spath in get_S_p.
    specialize (IHeval_copy _ get_S_p l0). inversion IHeval_copy. auto.
Qed.

Lemma operand_preserves_well_formedness op S vS :
  S |-{op} op => vS -> well_formed S -> well_formed_state_value vS.
Proof.
  intros eval_op WF. destruct eval_op. (* TODO: induction here *)
  - constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l. specialize (WF l). destruct WF. split; weight_inequality.
  - constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l. specialize (WF l). destruct WF. split; weight_inequality.
  - eauto using copy_preserves_well_formedness.
  - constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l. specialize (WF l). destruct WF.
    split; weight_inequality.
Qed.

(** * Simulation proofs for rvalue evaluation. *)
Lemma le_val_state_constant vl vr Sl Sr
  (vr_no_loan : not_contains_loan vr) (vr_no_borrow : not_contains_borrow vr) :
  (le_val_state_base le_base)^* (vl, Sl) (vr, Sr) ->
  vl = vr /\ le_base^* Sl Sr.
Proof.
  intros H.
  remember (vl, Sl) as vSl eqn:EQN_l. remember (vr, Sr) as vSr eqn:EQN_r.
  revert vl vr vr_no_loan vr_no_borrow Sl Sr EQN_l EQN_r.
  induction H as [? ? H | | ? (vm & Sm) ? ? IHl ? IHr];
    intros vl vr no_loan no_borrow Sl Sr EQN_l EQN_r; subst.
  - destruct (exists_fresh_anon2 Sl Sr) as (a & fresh_a_l & fresh_a_r).
    specialize (H a fresh_a_l fresh_a_r). rewrite !fst_pair, !snd_pair in H.
    remember (Sl,, a |-> vl) eqn:EQN. remember (Sr,, a |-> vr).
    destruct H; subst.
    + assert (fst sp_borrow <> anon_accessor a).
      { intros ?. autorewrite with spath in HS_borrow.
        eapply no_borrow; [ | now rewrite HS_borrow]. validity. }
      assert (fst sp_loan <> anon_accessor a).
      { intros ?. autorewrite with spath in HS_loan.
        eapply no_loan; [ | now rewrite HS_loan]. validity. }
      autorewrite with spath in * |-.
      apply states_add_anon_eq in EQN; auto with spath. destruct EQN as (<- & ?).
      split; [congruence | ]. constructor. constructor; assumption.
  - inversion EQN_r. subst. split; reflexivity.
  - edestruct IHr; [eassumption | eassumption | reflexivity | reflexivity | ]. subst.
    edestruct IHl; [eassumption | eassumption | reflexivity | reflexivity | ]. subst.
    split; [reflexivity | ]. etransitivity; eassumption.
Qed.

Corollary le_val_state_integer vl n Sl Sr :
  (le_val_state_base le_base)^* (vl, Sl) (VInt n, Sr) ->
  vl = VInt n /\ le_base^* Sl Sr.
Proof. apply le_val_state_constant; autounfold with spath; not_contains. Qed.

Corollary le_val_state_bool vl b Sl Sr :
  (le_val_state_base le_base)^* (vl, Sl) (VBool b, Sr) ->
  vl = VBool b /\ le_base^* Sl Sr.
Proof. apply le_val_state_constant; autounfold with spath; not_contains. Qed.

Lemma le_base_implies_le_val_state_base Sl Sr v :
  le_base^* Sl Sr -> (le_val_state_base le_base)^* (v, Sl) (v, Sr).
Proof.
  induction 1 as [Sl Sr H | | ].
  - constructor. intros a fresh_a_l fresh_a_r. rewrite !fst_pair, !snd_pair in *.
    destruct H.
    + rewrite <-!sset_add_anon by eauto with spath. erewrite <-sget_add_anon by eauto with spath.
      constructor. assumption. all: autorewrite with spath; assumption.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Lemma rvalue_preserves_HLPL_plus_rel rv :
  forward_simulation le_base^* (le_val_state_base le_base)^* (eval_rvalue rv) (eval_rvalue rv).
Proof.
  apply preservation_by_base_case.
  intros ? ? Heval. destruct Heval.
  (* rv = just op *)
  - apply operand_preserves_HLPL_plus_rel in Heval_op. intros ? ?%rt_step.
    firstorder using E_Use.

  - intros Sl Hle. apply operand_preserves_HLPL_plus_rel in eval_op_0, eval_op_1.
    destruct Hbinop.
    (* rv = op + op *)
    + edestruct eval_op_0 as ((v0l & S'l) & le_S'l_S' & H); [constructor; eassumption | ].
      apply le_val_state_integer in le_S'l_S'. destruct le_S'l_S' as (-> & le_S'l_S').
      edestruct eval_op_1 as ((v1l & S''l) & le_S''l_S'' & ?); [exact le_S'l_S' | ].
      apply le_val_state_integer in le_S''l_S''. destruct le_S''l_S'' as (-> & le_S''l_S'').
      execution_step. { econstructor; [eassumption.. | constructor]. }
      apply le_base_implies_le_val_state_base. assumption.
    (* rv = op <= op *)
    + edestruct eval_op_0 as ((v0l & S'l) & le_S'l_S' & H); [constructor; eassumption | ].
      apply le_val_state_integer in le_S'l_S'. destruct le_S'l_S' as (-> & le_S'l_S').
      edestruct eval_op_1 as ((v1l & S''l) & le_S''l_S'' & ?); [exact le_S'l_S' | ].
      apply le_val_state_integer in le_S''l_S''. destruct le_S''l_S'' as (-> & le_S''l_S'').
      execution_step. { econstructor; [eassumption.. | constructor]. }
      apply le_base_implies_le_val_state_base. assumption.

  (* rv = &mut p *)
  (* The place p evaluates to a spath under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      (* Case 1: the place p is under the borrow. *)
      * execution_step.
        { eapply E_Pointer_Loc. eassumption. autorewrite with spath. eassumption. }
        le_step_right.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      (* Case 2: the place p is not under the borrow. *)
      * execution_step.
        { eapply E_Pointer_Loc. eassumption. autorewrite with spath. eassumption. }
        le_step_right.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
  (* rv = &mut p *)
  (* The place p evaluates to a spath that is not under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      (* Case 1: the place p is under sp_borrow. *)
      * execution_step.
        { apply E_Pointer_Fresh with (l := l). eassumption.
          all: autorewrite with spath. assumption. not_contains. }
        le_step_right.
         { apply Le_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
         { autorewrite with spath. reflexivity. }
        states_eq.
      (* Case 2: *)
      * assert (disj pi sp_loan) by solve_comp.
        destruct (decidable_prefix pi sp_borrow) as [(r & <-) | ].
        -- execution_step.
           { apply E_Pointer_Fresh with (l := l). eassumption.
             autorewrite with spath. all: autounfold with spath; not_contains. }
           le_step_right.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := pi +++ [0] ++ r).
             solve_comp. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           states_eq.
        -- assert (disj pi sp_borrow) by solve_comp.
           execution_step.
           { apply E_Pointer_Fresh with (l := l). eassumption.
             autorewrite with spath. assumption. all: autounfold with spath; not_contains. }
           le_step_right.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           states_eq.
Qed.

Lemma well_formed_state_value_implies_well_formed_state v S :
  not_contains_loc v -> well_formed_state_value (v, S) -> well_formed S.
Proof.
  rewrite well_formedness_state_value_equiv, well_formedness_equiv.
  intros no_loc WF l.
  specialize (WF l). inversion WF as [? ? ? WF'].
  destruct (exists_fresh_anon S) as (a & a_fresh).
  destruct (WF' a a_fresh). autorewrite with weight in * |-.
  apply not_value_contains_weight with (weight := indicator (nloc(l))) in no_loc;
    [ | intros ? <-%indicator_non_zero; constructor].
  split; weight_inequality.
Qed.

Hint Extern 0 (not_value_contains _ _) => not_contains0 : spath.
Lemma eval_operand_no_loc (S : state) (op : operand) (vS' : value * state) :
  S |-{op} op => vS' -> not_contains_loc (fst vS').
Proof.
  intros eval_op ; induction eval_op.
  - not_contains.
  - not_contains.
  - induction Hcopy_val; not_contains.
  - not_contains.
Qed.

Corollary operand_preserves_well_formedness' op S v S' :
  S |-{op} op => (v, S') -> well_formed S -> well_formed S'.
Proof.
  intros eval_op WF. eapply operand_preserves_well_formedness in WF; [ | eassumption].
  inversion WF.
  eapply well_formed_state_value_implies_well_formed_state; [ | eassumption].
  apply eval_operand_no_loc in eval_op. exact eval_op.
Qed.

Lemma rvalue_preserves_well_formedness rv S vS :
  S |-{rv} rv => vS -> well_formed S -> well_formed_state_value vS.
Proof.
  intros eval_rv WF. destruct eval_rv.
  - eauto using operand_preserves_well_formedness.
  - apply operand_preserves_well_formedness' in eval_op_0; [ | assumption].
    apply operand_preserves_well_formedness' in eval_op_1; [ | assumption].
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (eval_op_1 l0). destruct eval_op_1.
    destruct Hbinop; split; weight_inequality.
  - apply eval_place_valid in Heval_place.
    apply weight_sget_node_le with (weight := indicator (nloc(l))) in Heval_place.
    rewrite Hloc, indicator_same in Heval_place.
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (WF l0). destruct WF. split.
    + weight_inequality.
    + weight_inequality.
    + destruct (decide (l = l0)) as [<- | ]; weight_inequality.
  - apply eval_place_valid in Heval_place.
    assert (scount (nloc(l)) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | exact H].
      intros ? <-%indicator_non_zero. constructor. }
    assert (scount (nloan^m(l)) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | exact H].
      intros ? <-%indicator_non_zero. constructor. }
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (WF l0). destruct WF. split.
    + weight_inequality.
    + destruct (decide (l = l0)) as [<- | ]; weight_inequality.
    + destruct (decide (l = l0)) as [<- | ]; weight_inequality.
Qed.

(** * Simulation proofs for the store operation. *)
(** We only store values that come from rvalue evaluations, and these values do not contain loans or
    locations. This can be used to prune cases. *)

Lemma eval_operand_no_loan (S : state) (op : operand) (vS' : value * state) :
  S |-{op} op => vS' -> not_contains_loan (fst vS').
Proof.
  intros eval_op ; induction eval_op.
  - not_contains.
  - not_contains.
  - induction Hcopy_val; not_contains.
  - not_contains.
Qed.

Lemma eval_rvalue_no_loan S rv vS' : S |-{rv} rv => vS' -> not_contains_loan (fst vS').
Proof.
  induction 1.
  - eapply eval_operand_no_loan. eassumption.
  - destruct Hbinop; auto with spath.
  - auto with spath.
  - auto with spath.
Qed.

(** Suppose that [(v0, S0) <^* (vn, Sn)], and that [vr] does not contain any loan.
    Let us take [(v1, S1)], ..., [(v_{n-1}, S_{n-1})] the intermediate pairs such that
    [(v0, S0) < (v1, S1) < ... < (vn, Sn)].
    Then, we prove that for each [(vi, Si)], the value [vi] does not contain any loan. *)
(* TODO: the name is really similar to le_val_state_base. *)
Definition le_val_state_base' (vSl vSr : value * state) : Prop :=
  le_val_state_base le_base vSl vSr /\ not_contains_loan (fst vSr).

Lemma le_base_does_not_insert_loan vSl vSr :
  le_val_state_base' vSl vSr -> not_contains_loan (fst vSl).
Proof.
  intros (Hle & Hno_loan).
  edestruct exists_fresh_anon2 as (a & fresh_a_l & fresh_a_r).
  specialize (Hle a fresh_a_l fresh_a_r).
  remember ((vSl.2),, a |-> vSl.1) eqn:EQN.
  remember ((vSr.2),, a |-> vSr.1).
  destruct Hle; subst.
  - assert (valid_spath (snd vSr) sp_loan).
    (* TODO: this piece of reasonning is used several times. Automate it. *)
    { assert (valid_spath ((snd vSr),, a |-> fst vSr) sp_loan)
        as [(_ & ?) | (? & _)]%valid_spath_add_anon_cases
        by validity.
      - assumption.
      - autorewrite with spath in HS_loan. exfalso.
        eapply Hno_loan; [ | rewrite HS_loan; constructor]. validity.
    }
    assert (valid_spath ((snd vSr),, a |-> fst vSr) sp_borrow)
      as [(_ & ?) | (? & _)]%valid_spath_add_anon_cases
      by validity.
    + autorewrite with spath in EQN.
      apply states_add_anon_eq in EQN; [ | auto with spath..].
      destruct EQN as (_ & <-). auto.
    + autorewrite with spath in EQN.
      apply states_add_anon_eq in EQN; [ | auto with spath..].
      destruct EQN as (_ & <-). auto with spath.
Qed.

Lemma le_val_state_no_loan_right (vSl vSr : value * state) :
  (le_val_state_base le_base)^* vSl vSr -> not_contains_loan (fst vSr)
  -> le_val_state_base'^* vSl vSr.
Proof.
  intros Hle Hno_loan.
  apply proj1 with (B := not_contains_loan (fst vSl)).
  induction Hle as [vSl vSr | | x y z].
  - assert (le_val_state_base' vSl vSr) by (constructor; auto).
    split.
    + constructor. assumption.
    + eapply le_base_does_not_insert_loan. eassumption.
  - split; [reflexivity | auto].
  - split; [transitivity y | ]; tauto.
Qed.

Lemma fresh_anon_le_base_left Sl Sr a (fresh_a : fresh_anon Sr a) :
  le_base Sl Sr -> fresh_anon Sl a.
Proof.
  intros Hle. inversion Hle.
  - auto with spath.
Qed.

Lemma le_val_state_base_specialize_anon a vl Sl vr Sr :
  fresh_anon Sr a -> le_val_state_base le_base (vl, Sl) (vr, Sr) ->
  le_base (Sl,, a |-> vl) (Sr,, a |-> vr).
Proof.
  intros fresh_a H. apply H; [ | exact fresh_a].
  destruct (exists_fresh_anon2 Sl (Sr,, a |-> vr))
    as (b & fresh_b_l & (fresh_b_r & ?)%fresh_anon_add_anon).
  specialize (H b fresh_b_l fresh_b_r).
  apply fresh_anon_le_base_left with (a := a) in H;
    [ | rewrite fresh_anon_add_anon; auto].
  rewrite fresh_anon_add_anon in H. destruct H. assumption.
Qed.

Lemma fresh_anon_le_val_state_base_left vl Sl vr Sr a (fresh_a : fresh_anon Sr a) :
  le_val_state_base le_base (vl, Sl) (vr, Sr) -> fresh_anon Sl a.
Proof.
  intros H.
  destruct (exists_fresh_anon2 Sl (Sr,, a |-> vr))
    as (b & fresh_b_l & (fresh_b_r & ?)%fresh_anon_add_anon).
  specialize (H b fresh_b_l fresh_b_r).
  eapply fresh_anon_le_base_left in H.
  - rewrite fresh_anon_add_anon in H. destruct H. eassumption.
  - rewrite fresh_anon_add_anon. auto.
Qed.

Lemma store_preserves_HLPL_plus_rel p :
  forward_simulation le_val_state_base'^* le_base^* (store p) (store p).
Proof.
  eapply preservation_by_base_case.
  intros vSr S'r Hstore (vl & Sl) (Hle & val_no_loan).
  destruct Hstore as [vr Sr sp_store a ? ? ? fresh_a]. cbn in val_no_loan.
  assert (fresh_anon Sl a) by eauto using fresh_anon_le_val_state_base_left.
  apply (le_val_state_base_specialize_anon a) in Hle; [ | assumption].
  remember (Sl,, a |-> vl) eqn:HeqvSl. remember (Sr,, a |-> vr).
  destruct Hle; subst.
  - assert (valid_sp_loan : valid_spath (Sr,, a |-> vr) sp_loan) by validity.
    apply valid_spath_add_anon_cases in valid_sp_loan.
    destruct valid_sp_loan as [(_ & ?) | (? & _)].
    2: { autorewrite with spath in HS_loan. exfalso.
      eapply val_no_loan; [ | rewrite HS_loan ]. validity. constructor. }
    autorewrite with spath in HS_loan.
    destruct (decide (fst sp_borrow = anon_accessor a)).
    (* Case 1: the borrow is inside the evaluated value. *)
    + autorewrite with spath in HeqvSl, HS_borrow |-.
      apply states_add_anon_eq in HeqvSl; [ | auto with spath..].
      destruct HeqvSl. subst.
      assert (valid_spath Sr sp_store) by validity.
      eapply eval_place_mut_loan_to_loc in eval_p; [ | exact HS_loan].
      destruct eval_p as (eval_p & ?).
      destruct (decidable_prefix sp_store sp_loan) as [(r & <-) | ].
      (* Case 1a: the loan is in the place we write in. *)
      * execution_step.
        { constructor. eassumption. not_contains_outer. not_contains_outer. eassumption. }
        le_step_right.
        { eapply Le_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r))
                                           (sp_borrow := sp_store +++ snd sp_borrow).
          eauto with spath. all: autorewrite with spath; eassumption. }
        autorewrite with spath. reflexivity.
      (* Case 1b: the loan is disjoint to the place we write in. *)
      * assert (disj sp_store sp_loan) by solve_comp.
        execution_step.
        { constructor. eassumption. not_contains_outer. not_contains_outer. eassumption. }
        le_step_right.
        { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                           (sp_borrow := sp_store +++ snd sp_borrow).
          solve_comp. all: autorewrite with spath; eassumption. }
        states_eq.
    + autorewrite with spath in HeqvSl, HS_borrow |-.
      apply states_add_anon_eq in HeqvSl; [ | auto with spath..].
      destruct HeqvSl. subst. eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      (* Case 2: the place sp where we write is inside the borrow. *)
      * execution_step.
        { constructor. eassumption. all: autorewrite with spath; eassumption. }
        le_step_right.
        { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        states_eq.
      * destruct (decidable_prefix sp_store sp_borrow) as [(r_borrow & <-) | ].
        (* Case 3: the borrow is inside the place we write in. *)
        -- destruct (decidable_prefix sp_store sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ execution_step.
              { constructor. eassumption.
                autorewrite with spath. not_contains_outer. not_contains_outer. eassumption. }
              le_step_right.
              { eapply Le_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r_loan))
                                                (sp_borrow := (anon_accessor a, r_borrow)).
                 (* TODO: long *)
                 solve_comp. all: autorewrite with spath; eassumption. }
              autorewrite with spath. reflexivity.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp_store sp_loan) by solve_comp.
              execution_step.
              { constructor. eassumption. not_contains_outer. not_contains_outer. eassumption. }
              le_step_right.
              { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                (sp_borrow := (anon_accessor a, r_borrow)).
                eauto with spath. all: autorewrite with spath; eassumption. }
              states_eq.
        (* Case 4: the borrow is disjoint from the place we write in. *)
        -- assert (disj sp_store sp_borrow) by solve_comp.
           destruct (decidable_prefix sp_store sp_loan) as [(r_loan & <-) | ].
           (* Case 4a: the loan is in the place we write in. *)
           ++ execution_step.
              { constructor.
                eassumption. not_contains_outer. not_contains_outer. eauto with spath. }
              le_step_right.
              { eapply Le_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r_loan))
                                                (sp_borrow := sp_borrow).
                eauto with spath. all: autorewrite with spath; eassumption. }
              states_eq.
          (* Case 4b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp_store sp_loan) by solve_comp.
              execution_step.
              { constructor. eassumption. not_contains_outer. not_contains_outer. eassumption. }
              le_step_right.
              { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                (sp_borrow := sp_borrow).
                auto with spath. all: autorewrite with spath; eassumption. }
              states_eq.
Qed.

Lemma store_preserves_well_formedness p vS S' :
  store p vS S' -> well_formed_state_value vS -> well_formed S'.
Proof.
  rewrite well_formedness_equiv, well_formedness_state_value_equiv.
  intros Hstore WF l. destruct Hstore as [? ? ? a ? ? ? fresh_a].
  specialize (WF l). inversion WF as [? ? ? WF']. destruct (WF' a fresh_a).
  autorewrite with weight in * |-.
  split; weight_inequality.
Qed.

(** * Simulation proofs for reorganizations. *)
Lemma reorg_preserves_well_formedness S S' :
  reorg S S' -> well_formed S -> well_formed S'.
Proof.
  rewrite !well_formedness_equiv. intros Hreorg WF l. specialize (WF l). destruct WF.
  destruct Hreorg.
  - split; weight_inequality.
  - split.
    + weight_inequality.
    + weight_inequality.
    + destruct (decide (l = l0)); weight_inequality.
  - split.
    + weight_inequality.
    + weight_inequality.
    + apply not_state_contains_implies_weight_zero with (weight := (indicator nptr(l0))) in H0;
       [ | intro; apply indicator_non_zero].
       destruct (decide (l = l0)) as [<- | ]; weight_inequality.
Qed.

Corollary reorgs_preserve_well_formedness S S' :
  reorg^* S S' -> well_formed S -> well_formed S'.
Proof. intro Hreorg. induction Hreorg; eauto using reorg_preserves_well_formedness. Qed.

(** The decreasing measure on HLPL+ states. Here is why it is decreasing:
    - Each borrow, loan, pointer or location has a positive measure. Because a reorganization ends at least one node of this kind, the measure decreases.
   - The measure of a pair of mutable loan and a borrow is 3. The measure of a pair of pointer and location is 2. Thus, the rule [Le_MutBorrow_To_Ptr] makes the measure decrease by 1.
 *)
Definition measure_node c :=
  match c with
  | nloan^m(_) => 2
  | nborrow^m(_) => 1
  | nloc(_) => 1
  | nptr(_) => 1
  | _ => 0
  end.

Lemma measure_mut_loan l : measure_node nloan^m(l) = 2. Proof. reflexivity. Qed.
Hint Rewrite measure_mut_loan : weight.
Lemma measure_mut_borrow l : measure_node nborrow^m(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_mut_borrow : weight.
Lemma measure_loc l : measure_node nloc(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_loc : weight.
Lemma measure_ptr l : measure_node nptr(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_ptr : weight.
Lemma measure_bot : vweight measure_node bot = 0. Proof. reflexivity. Qed.
Hint Rewrite measure_bot : weight.

Lemma prove_reorg_step {S} {reorg le : relation S} S0 S1 Sr:
  reorg S0 S1 -> (exists Sl, le Sl Sr /\ reorg^* S1 Sl) ->
  exists Sl, le Sl Sr /\ reorg^* S0 Sl.
Proof.
  intros ? (Sl & ? & ?). exists Sl. split; [assumption | ].
  etransitivity; [constructor | ]; eassumption.
Qed.

Ltac reorg_step := eapply prove_reorg_step.
Ltac reorg_done := eexists; split; [ | reflexivity].

Lemma reorg_preserves_HLPL_plus_rel :
  well_formed_forward_simulation_r well_formed le_base^* le_base^* reorg^* reorg^*.
Proof.
  eapply preservation_reorg_r with (measure := sweight measure_node).
  { apply le_base_preserves_wf_r. }
  { apply reorg_preserves_well_formedness. }
  { intros Sl Sr Hle. destruct Hle; weight_inequality. }
  { intros ? ? Hreorg. destruct Hreorg; weight_inequality. }
  intros Sr Sr' WF_Sr reorg_Sr_Sr'. destruct reorg_Sr_Sr'.
  (* Case Reorg_End_MutBorrow: *)
  - intros ? Hle. destruct Hle.
    + destruct (decide (l = l0)) as [<- | ].
      (* Case 1: l = l0. By well-formedness, that means that the loan that we end at p is the loan
         that we turn into a loc at sp_loan, and that the borrow that we end at q is the
         borrow we turn into a pointer at sp_borrow. *)
      * assert (p = sp_loan) as ->.
        { eapply at_most_one_mut_loan. eassumption.
          rewrite H0. reflexivity. rewrite HS_loan. reflexivity. }
        assert (q = sp_borrow) as ->.
        { eapply at_most_one_mut_borrow. eassumption.
          rewrite H1. reflexivity. assumption. }
        reorg_step.
        { eapply Reorg_End_Ptr with (p := sp_borrow). autorewrite with spath. reflexivity. }
        reorg_step.
        { eapply Reorg_End_Loc with (p := sp_loan).
          autorewrite with spath. reflexivity.
          assert (not_state_contains (eq nptr(l)) S).
          { eapply no_mut_loan_ptr. eassumption. rewrite HS_loan. reflexivity. }
          autorewrite with spath. not_contains. }
        reorg_done.
        states_eq.
      * assert (~strict_prefix sp_borrow q). { apply H3. rewrite HS_borrow. constructor. }
        assert (disj p sp_loan) by solve_comp.
        assert (disj q sp_loan) by solve_comp.
        destruct (decidable_prefix q sp_borrow).
        (* Case 2: the borrow we turn into a pointer is inside the borrow we end. *)
        -- assert (prefix (q +++ [0]) sp_borrow) as (r & <-) by solve_comp.
           autorewrite with spath in *.
           reorg_step.
           { eapply Reorg_End_MutBorrow with (p := p) (q := q).
             assumption. all: autorewrite with spath. eassumption. assumption.
             not_contains. auto with spath. }
           reorg_done.
           le_step_right.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ r).
             solve_comp. all: autorewrite with spath; eassumption. }
           states_eq.
        -- assert (disj q sp_borrow) by solve_comp.
           destruct (decidable_prefix sp_borrow p).
           (* Case 3: the loan that we end is is the borrow that we turn into a pointer. *)
           ++ assert (prefix (sp_borrow +++ [0]) p) as (r & <-) by solve_comp.
              rewrite<- (app_spath_vpath_assoc sp_borrow [0] r) in * |-.
              reorg_step.
              { eapply Reorg_End_MutBorrow with (p := sp_loan +++ [0] ++ r) (q := q).
                solve_comp. all: autorewrite with spath. eassumption.
                assumption. assumption. auto with spath. }
              reorg_done.
              le_step_right.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                assumption. all: autorewrite with spath; eassumption. }
              states_eq.
           (* Case 4: the loan that we end is disjoint from the borrow that we turn into a pointer.
           *)
           ++ assert (disj sp_borrow p) by solve_comp.
              reorg_step.
              { eapply Reorg_End_MutBorrow with (p := p) (q := q).
                assumption. all: autorewrite with spath. eassumption.
                assumption. assumption. auto with spath. }
              reorg_done.
              le_step_right.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                assumption. all: autorewrite with spath; eassumption. }
              states_eq.
  - intros ? Hle. destruct Hle.
    + destruct (decidable_prefix sp_borrow p).
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by solve_comp.
        rewrite<- (app_spath_vpath_assoc sp_borrow [0] q) in *.
        reorg_step.
        { eapply Reorg_End_Ptr with (p := sp_loan +++ [0] ++ q).
          autorewrite with spath. eassumption. }
        reorg_done.
        le_step_right.
        { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        states_eq.
      * assert (disj sp_borrow p) by solve_comp.
        assert (disj sp_loan p) by solve_comp.
        reorg_step.
        { eapply Reorg_End_Ptr with (p := p). autorewrite with spath. eassumption. }
        reorg_done.
        le_step_right.
         { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption. }
        states_eq.
  - intros ? Hle. destruct Hle.
    + assert (l <> l0).
      { intros <-. eapply no_mut_loan_loc; [ eassumption.. | | symmetry; eassumption].
        validity. }
      destruct (decidable_prefix sp_borrow p).
      (* Case 1: the loc we end is is the borrow we turn into a pointer. *)
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by solve_comp.
        autorewrite with spath in *.
        reorg_step.
        { eapply Reorg_End_Loc with (p := sp_loan +++ [0] ++ q).
          autorewrite with spath. eassumption. not_contains. cbn. congruence. }
        reorg_done.
        le_step_right.
        { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        states_eq.
      * destruct (decidable_prefix p sp_borrow).
        -- assert (prefix (p +++ [0]) sp_borrow) as (q & <-) by solve_comp.
           destruct (decidable_prefix p sp_loan).
           (* Case 2: the loan and the borrow we turn into a location and a pointer are in the loc
            * we end. *)
           ++ assert (prefix (p +++ [0]) sp_loan) as (r & <-) by solve_comp.
              assert (vdisj q r) by solve_comp.
              autorewrite with spath in *.
              reorg_step.
              { eapply Reorg_End_Loc with (p := p).
                autorewrite with spath; eassumption.
                repeat apply not_state_contains_sset.
                assumption. all: not_contains.
                cbn. congruence. }
              reorg_done.
              le_step_right.
              { eapply Le_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := p +++ q).
                solve_comp. all: autorewrite with spath; eassumption. }
              autorewrite with spath. reflexivity.
           (* Case 3: the borrow we turn into a pointer is in the location we end, but the loan we
            * turn into a location is disjoint. *)
           ++ assert (disj p sp_loan) by solve_comp.
              autorewrite with spath in *.
              reorg_step.
              { eapply Reorg_End_Loc with (p := p).
                autorewrite with spath; eassumption.
                repeat apply not_state_contains_sset.
                assumption. all: not_contains. cbn. congruence. }
                reorg_done.
                le_step_right.
                { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ q).
                    solve_comp. all: autorewrite with spath; eassumption. }
                states_eq.
            -- assert (disj p sp_borrow) by solve_comp.
            destruct (decidable_prefix p sp_loan).
            (* Case 4: the loan we turn into a location is in the location we end, but the borrow we
                * turn into a pointer is disjoint. *)
            ++ assert (prefix (p +++ [0]) sp_loan) as (r & <-) by solve_comp.
                rewrite<- app_spath_vpath_assoc in *.
                reorg_step.
                { eapply Reorg_End_Loc with (p := p).
                    autorewrite with spath; eassumption.
                    repeat apply not_state_contains_sset.
                    assumption. all: not_contains. cbn. congruence. }
                reorg_done.
                le_step_right.
                { eapply Le_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := sp_borrow).
                    solve_comp. all: autorewrite with spath; eassumption. }
                states_eq.
            (* Case 5: the loan and the borrow we turn into a location and a pointer are in the loc
                * we end. *)
            ++ assert (disj p sp_loan) by solve_comp.
                reorg_step.
                { eapply Reorg_End_Loc with (p := p).
                    autorewrite with spath; eassumption.
                    repeat apply not_state_contains_sset.
                    assumption. all: not_contains. cbn. congruence. }
                reorg_done.
                le_step_right.
                { eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                    assumption. all: autorewrite with spath; eassumption. }
                states_eq.
Qed.

(** * Simulation proofs for statement evaluation. *)
Lemma stmt_preserves_well_formedness n S s R :
  S |-{stmt} s ~>{n} R -> forall r S', R = Some (r, S') -> well_formed S -> well_formed S'.
Proof.
  induction 1; try congruence; eauto.
  - intros ? ? [=<- <-] ?. eapply store_preserves_well_formedness; [eassumption | ].
    eapply rvalue_preserves_well_formedness; eassumption.
  - intros r S'' -> ?.
    apply operand_preserves_well_formedness in eval_cond; [ | assumption].
    apply well_formed_state_value_implies_well_formed_state in eval_cond; [ | not_contains].
    eauto.
  - intros r S'' -> ?.
    apply operand_preserves_well_formedness in eval_cond; [ | assumption].
    apply well_formed_state_value_implies_well_formed_state in eval_cond; [ | not_contains].
    eauto.
  - intros r S -> ?. eauto using reorgs_preserve_well_formedness.
  - intros ? ? [=<- <-]. eauto.
Qed.

Variant le_result : option (flow_token * state) -> option (flow_token * state) -> Prop :=
  | Le_Termination r Sl Sh : le_base^* Sl Sh -> le_result (Some (r, Sl)) (Some (r, Sh))
  | Le_Interruption : le_result None None
.

Lemma no_loan_in_bool b : not_contains_loan (VBool b).
Proof. not_contains. Qed.

Lemma no_borrow_in_bool b : not_contains_borrow (VBool b).
Proof. not_contains. Qed.

Lemma _le_val_state_boolean vl Sl Sh b :
  le_val_state_base le_base (vl, Sl) (VBool b, Sh) -> vl = VBool b /\ le_base Sl Sh.
Proof.
  destruct (exists_fresh_anon2 Sl Sh) as (a & fresh_a_l & fresh_a_h).
  intros H. specialize (H a fresh_a_l fresh_a_h). cbn [fst snd] in H.
  remember (Sl,, a |-> vl) eqn:EQN_l. remember (Sh,, a |-> VBool b) eqn:EQN_h.
  destruct H; subst.
  - assert (fst sp_loan <> anon_accessor a).
    { intros ?. autorewrite with spath in HS_loan.
      eapply no_loan_in_bool; [ | rewrite HS_loan; constructor]. validity. }
    assert (fst sp_borrow <> anon_accessor a).
    { intros ?. autorewrite with spath in HS_borrow.
      eapply no_borrow_in_bool; [ | rewrite HS_borrow; constructor]. validity. }
    autorewrite with spath in *.
    apply states_add_anon_eq in EQN_l; [ | auto with spath..].
    destruct EQN_l as (<- & <-). split; [reflexivity | ].
    eapply Le_MutBorrow_To_Ptr; eassumption.
Qed.

Lemma le_val_state_boolean vl Sl Sh b :
  (le_val_state_base le_base)^* (vl, Sl) (VBool b, Sh) ->
  vl = VBool b /\ le_base^* Sl Sh.
Proof.
  intros H.
  remember (vl, Sl) eqn:EQN_l. remember (VBool b, Sh) eqn:EQN_h.
  revert vl Sl Sh EQN_l EQN_h.
  induction H as [ | | ? (vm & Sm) ? _ IH_l _ IH_r]; intros vl Sl Sh -> EQN_h; subst.
  - apply _le_val_state_boolean in H. destruct H. split; [ | constructor]; assumption.
  - inversion EQN_h. split; reflexivity.
  - edestruct IH_r as (? & ?); [reflexivity.. | ]. subst.
    edestruct IH_l as (? & ?); [reflexivity.. | ].
    split; [assumption | ]. etransitivity; eassumption.
Qed.

Lemma stmt_preserves_HLPL_plus_rel n s :
  well_formed_forward_simulation_r well_formed le_base^* le_result (eval_stmt n s) (eval_stmt n s).
Proof.
  intros Sr Sr' WF_Sr Heval Sl Hle. revert Sl Hle. induction Heval; intros Sl Hle.
  - execution_step; constructor.
  - execution_step. { constructor. } { constructor. assumption. }
  - execution_step. { constructor. } { constructor. assumption. }
  - execution_step. { constructor. } { constructor. assumption. }
  - execution_step. { constructor. } { constructor. assumption. }
  - specialize (IHHeval1 WF_Sr _ Hle). destruct IHHeval1 as (? & Hle_1 & ?).
    inversion Hle_1. subst.
    edestruct IHHeval2 as (Rl & ? & ?);
      [eauto using stmt_preserves_well_formedness | eassumption | ].
    execution_step. { eapply E_Seq_Unit; eassumption. } { assumption. }
  - specialize (IHHeval WF_Sr _ Hle). destruct IHHeval as (? & Hle_1 & ?).
    inversion Hle_1. subst.
    execution_step. { apply E_Seq_Propagate; eassumption. } constructor. assumption.
  - specialize (IHHeval WF_Sr _ Hle). destruct IHHeval as (? & Hle_1 & ?).
    inversion Hle_1. subst.
    execution_step. { apply E_Seq_Interrupt. assumption. } constructor.
  - pose proof (_eval_rv := eval_rv). apply rvalue_preserves_HLPL_plus_rel in _eval_rv.
    destruct (_eval_rv _ Hle) as (vSl' & le_vSl_vS' & eval_Sl).
    apply store_preserves_HLPL_plus_rel in Hstore.
    apply le_val_state_no_loan_right in le_vSl_vS';
      [ | eapply eval_rvalue_no_loan; exact eval_rv..].
    destruct (Hstore _ le_vSl_vS') as (Sl'' & le_Sl'' & store_vSl').
    execution_step. { eapply E_Assign; eassumption. } constructor. assumption.
  - eapply operand_preserves_well_formedness in WF_Sr; [ | exact eval_cond].
    apply well_formed_state_value_implies_well_formed_state in WF_Sr; [ | not_contains].
    apply operand_preserves_HLPL_plus_rel in eval_cond. specialize (eval_cond _ Hle).
    destruct eval_cond as ((? & S1_l) & Hle_1 & eval_cond).
    apply le_val_state_boolean in Hle_1. destruct Hle_1 as (-> & Hle_1).
    edestruct IHHeval as (Rl & Hle_2 & ?); [eassumption.. | ].
    execution_step. { eapply E_IfThenElse_T; eassumption. } assumption.
  - eapply operand_preserves_well_formedness in WF_Sr; [ | exact eval_cond].
    apply well_formed_state_value_implies_well_formed_state in WF_Sr; [ | not_contains].
    apply operand_preserves_HLPL_plus_rel in eval_cond. specialize (eval_cond _ Hle).
    destruct eval_cond as ((? & S1_l) & Hle_1 & eval_cond).
    apply le_val_state_boolean in Hle_1. destruct Hle_1 as (-> & Hle_1).
    edestruct IHHeval as (Rl & Hle_2 & ?); [eassumption.. | ].
    execution_step. { eapply E_IfThenElse_F; eassumption. } assumption.
  - assert (well_formed S1) by eauto using reorgs_preserve_well_formedness.
    apply reorg_preserves_HLPL_plus_rel in Hreorg; [ | assumption].
    destruct (Hreorg _ Hle) as (Sl1 & le_Sl1 & reorg_Sl1).
    edestruct IHHeval as (Rl & Hle_2 & eval_in_Sl2); [ assumption | eassumption | ].
    execution_step. { eapply E_Reorg; eassumption. } assumption.
  - specialize (IHHeval WF_Sr _ Hle). destruct IHHeval as (Rl & Hle_1 & Heval_1).
    inversion Hle_1. subst.
    execution_step. { eapply E_Loop_Stop; eassumption. } constructor. assumption.
  - specialize (IHHeval WF_Sr _ Hle). destruct IHHeval as (Rl & Hle_1 & Heval_1).
    inversion Hle_1. subst.
    execution_step. { eapply E_Loop_Interrupt; eassumption. } constructor.
  - specialize (IHHeval1 WF_Sr _ Hle). destruct IHHeval1 as (? & _Hle_1 & Heval_1).
    inversion _Hle_1 as [? ? ? Hle_1 | ]. subst.
    eapply stmt_preserves_well_formedness in WF_Sr; [ | eauto..].
    specialize (IHHeval2 WF_Sr _ Hle_1). destruct IHHeval2 as (Rl & Hle_2 & Heval_2).
    execution_step. { eapply E_Loop_Continue; eassumption. } assumption.
Qed.
