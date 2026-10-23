(** * Mechanized_LLBC.simulations.Symbolic_relations : Results about relations for symbolic states. *)
From stdpp Require Import pmap gmap.
From rustc Require Import OptionMonad.
Require Import base PathToSubtree lang Symbolic_states LLBC_sharp.
Require Import SimulationUtils.

Definition le_n (n : nat) := chain equiv_states (measured_closure le_state_base_n n).
Definition le_val_state := chain equiv_val_state le_val_state_base^*.

Lemma to_abs_loan_id_set v A : to_abs v A -> loan_set_val v = loan_set_abstraction A.
Proof.
  intros [ ].
  - unfold loan_set_abstraction. rewrite map_fold_insert_L; [ | set_solver | now simpl_map].
    rewrite map_fold_singleton. set_solver.
  - unfold loan_set_abstraction. rewrite map_fold_singleton.
    rewrite !loan_set_borrow. rewrite loan_set_id_empty by assumption. set_solver.
Qed.

Lemma to_abs_apply_permutation v A p q :
  is_permutation p A -> to_abs v A ->
  to_abs (rename_value q v) (apply_permutation p (fmap (rename_value q) A)).
Proof.
  intros (inj_p & dom_p) H. destruct H.
  - destruct (dom_p kb) as (_ & (kb' & ?)); [simpl_map; auto | ].
    destruct (dom_p kl) as (_ & (kl' & ?)); [simpl_map; auto | ].
    rewrite fmap_insert, map_fmap_singleton.
    erewrite apply_permutation_insert by (simpl_map; eauto).
    erewrite <-insert_empty, apply_permutation_insert;
      [ | now apply map_inj_delete | simpl_map; reflexivity..].
    constructor. intros ?. eapply Hk, inj_p; eassumption.
  - specialize (dom_p k). simpl_map. destruct dom_p as (_ & (k' & ?)); [auto | ].
    (* TODO: lemma apply_permutation_singleton. *)
    rewrite map_fmap_singleton.
    erewrite <-insert_empty, apply_permutation_insert by (simpl_map; auto).
    rewrite !rename_loan_id_borrow. constructor; eauto with spath.
Qed.

Ltac process_state_equivalence :=
  let p := fresh "p" in
  let G := fresh "G" in
  let perm_A := fresh "perm_A" in
  let b := fresh "b" in
  let fresh_b := fresh "fresh_b" in
  let S0 := fresh "S0" in
  let B := fresh "B" in
  let Hloan_set := fresh "Hloan_set" in
  lazymatch goal with
  (* First: the hypothesis contains a goal "is_state_equivalence perm S_r".
   * While Sr is an expression E_r[S], we break it down until we obtain a property about the
   * validity of S, the common denominator between S_l and S_r. *)
  | valid_perm : is_state_equivalence ?perm (?S.[?sp <- ?v]) |- _ =>
      apply is_state_equivalence_sset_rev in valid_perm; [ | eauto with spath]
  | valid_perm : is_state_equivalence ?perm (?S,,, ?i |-> ?A) |- _ =>
      apply remove_abstraction_perm_equivalence in valid_perm; [ | eassumption];
      destruct valid_perm as (valid_perm & p & perm_A & G & Hloan_set);
      rewrite G; clear G
  | valid_perm : is_state_equivalence ?perm (?S,, ?a |-> ?v) |- _ =>
      apply remove_anon_perm_equivalence in valid_perm; [ | eauto with spath; fail];
      destruct valid_perm as (valid_perm & b & G & fresh_b & Hloan_set);
      rewrite G; clear G
  end.

Lemma loan_set_no_loan_borrow v (perm : loan_id_map) :
  not_contains_loan v -> not_contains_borrow v -> subseteq (loan_set_val v) (dom perm).
Proof. intros. rewrite loan_set_id_empty by assumption. apply empty_subseteq. Qed.
Hint Resolve loan_set_no_loan_borrow : spath.

Lemma loan_set_symbolic_subseteq ty (perm : loan_id_map) :
  subseteq (loan_set_val (VSymbolic ty)) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_symbolic_subseteq : spath.

Lemma loan_set_bot_subseteq (perm : loan_id_map) : subseteq (loan_set_val bot) (dom perm).
Proof. apply empty_subseteq. Qed.
Hint Resolve loan_set_bot_subseteq : spath.

Lemma vsize_rename_value m v : vweight (fun _ => 1) (rename_value m v) = vweight (fun _ => 1) v.
Proof. induction v; cbn in *; congruence. Qed.

Lemma abs_measure_rename_set p (A : Pmap _) : abs_measure (rename_set p A) = abs_measure A.
Proof.
  induction A using map_first_key_ind.
  - reflexivity.
  - rewrite fmap_insert. rewrite !map_sum_insert by (simpl_map; rewrite ?fmap_None; assumption).
    rewrite vsize_rename_value. congruence.
Qed.

Lemma le_n_equiv_states_commute n :
  forward_simulation (le_state_base_n n) (le_state_base_n n) equiv_states equiv_states.
Proof.
  intros Sl Sr (perm & valid_perm & ->) ? Hle. destruct Hle; destruct Hle.
  (* TODO: automation *)
  - process_state_equivalence. rewrite permutation_sset by eauto with spath.
    execution_step.
    { exists perm. eauto. }
    eapply prove_rel_n.
    { constructor. apply Le_ToSymbolic. all: rewrite permutation_sget; eauto with spath. }
    { autorewrite with spath. apply vsize_rename_value. }
    reflexivity.

  - process_state_equivalence. autorewrite with spath.
    erewrite <-to_abs_loan_id_set in * |- by eassumption.
    destruct (exists_fresh_anon (apply_state_permutation (remove_abstraction_perm perm i) S))
      as (b & fresh_b).
    execution_step.
    { eexists. split; eauto with spath. }
    eapply prove_rel_n.
    { autorewrite with spath. constructor. apply Le_ToAbs; eauto with spath.
      apply to_abs_apply_permutation; eassumption. }
    { apply vsize_rename_value. }
    reflexivity.

  - destruct (exists_fresh_anon (apply_state_permutation perm S)) as (b & fresh_b).
    pose proof (loan_set_id_empty v no_loan no_borrow).
    execution_step.
    { eexists. split; eauto with spath. }
    autorewrite with spath. rewrite rename_value_no_loan_id by assumption.
    constructor. apply Le_RemoveAnon; assumption.

  - repeat process_state_equivalence. autorewrite with spath in *.
    execution_step. { eexists. eauto. }
    eapply prove_rel.
    { constructor. apply Le_MoveValue; rewrite ?permutation_sget; eauto with spath. }
    autorewrite with spath. reflexivity.

  - apply (extend_state_permutation (union (loan_set_abstraction A) (loan_set_abstraction B)))
      in valid_perm.
      destruct valid_perm as (perm' & valid_perm & ? & ->). clear perm.
    process_state_equivalence. autorewrite with spath.
    eapply merge_abstractions_equiv in Hmerge; [ | eassumption].
    destruct Hmerge as (pA & pB & perm_pA & perm_pB & Hmerge).
    execution_step.
    { eexists.
      pose proof valid_perm as G.
      apply (add_abstraction_perm_equivalence _ _ i A pA) in G; [ | set_solver..].
      split.
      - apply add_abstraction_perm_equivalence; [set_solver.. | eauto with spath].
      - autorewrite with spath; [reflexivity | set_solver..]. }
    rewrite pkmap_fmap by apply map_inj_equiv, perm_pA.
    rewrite pkmap_fmap by apply map_inj_equiv, perm_pB.
    eapply prove_rel_n.
    { constructor. apply Le_MergeAbs; eauto with spath.
      apply merge_abstraction_rename_value, Hmerge. }
    { rewrite !abs_measure_rename_set, !map_sum_permutation by assumption. reflexivity. }
    rewrite pkmap_fmap by apply map_inj_equiv, perm_A. reflexivity.

  - apply (extend_state_permutation (loan_set_val v)) in valid_perm.
    destruct valid_perm as (perm' & valid_perm & ? & ->). clear perm.
    process_state_equivalence. autorewrite with spath.
    destruct (exist_fresh (map_img (SA := Pset) p)) as (j' & fresh_j').
    assert (lookup j p = None).
    { destruct perm_A as (_ & Hdom). now rewrite eq_None_not_Some, Hdom, <-eq_None_not_Some. }
    rewrite not_elem_of_map_img in fresh_j'.
    eapply is_permutation_insert in perm_A; [ | eassumption..].
    assert (subseteq (loan_set_abstraction (insert j v A)) (dom (loan_id_names (remove_abstraction_perm perm' i)))).
    { unfold loan_set_abstraction. rewrite map_fold_insert_L; set_solver. }
    execution_step.
    { eexists. split; [ | reflexivity]. apply add_abstraction_perm_equivalence; eassumption. }
    autorewrite with spath. (* TODO: hints *) rewrite fmap_insert.
    erewrite apply_permutation_insert;
      [ | apply perm_A | now rewrite lookup_fmap, fresh_j | now simpl_map].
    rewrite delete_insert_id by assumption.
    erewrite <-vsize_rename_value.
    constructor. apply Le_Abs_ClearValue; eauto with spath. apply lookup_pkmap_None. assumption.

  - process_state_equivalence.
    execution_step. { eexists. split; [exact valid_perm | reflexivity]. }
    autorewrite with spath. constructor. apply Le_AnonValue. auto with spath.

  - process_state_equivalence.
    pose proof Hloan_set as ?. rewrite loan_set_borrow, union_subseteq in Hloan_set.
    destruct Hloan_set as (Hl' & ?).
    process_state_equivalence.
    autorewrite with spath in fresh_b.
    execution_step. { eexists. split; [eassumption | reflexivity]. }
    autorewrite with spath; [ | autorewrite with spath; eauto with spath].
    apply singleton_subseteq_l, elem_of_dom in Hl'. destruct Hl' as (l & Hl).
    eapply prove_rel.
    { eapply Le_FreshLoan_n, Le_Fresh_MutLoan; eauto with spath.
      autorewrite with spath. eauto with spath.
      eapply is_fresh_apply_permutation; eassumption. }
    autorewrite with spath.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl. reflexivity.

  - process_state_equivalence.
    pose proof Hloan_set as ?. rewrite loan_set_borrow, union_subseteq in Hloan_set.
    destruct Hloan_set as (Hl0 & Hl1).
    (* TODO: lemma? *)
    assert (subseteq (loan_set_val (S.[sp +++ [0] ])) (dom (loan_id_names perm))).
    { destruct valid_perm as (_ & (_ & ?)).
      pose proof (loan_set_sget (rename_mut_borrow S sp l1) (sp +++ [0])) as G.
      autorewrite with spath in G. set_solver. }
    process_state_equivalence.
    (* TODO: lemma? *)
    2: { destruct (S.[sp]) eqn:EQN; inversion get_borrow_l0. subst. rewrite loan_set_borrow.
      apply (f_equal (vget [0])) in EQN. autorewrite with spath in EQN. subst. set_solver. }
    autorewrite with spath in fresh_b; [ | rewrite loan_set_borrow; set_solver].
    execution_step. { eexists. split; [exact valid_perm | reflexivity]. }
    assert (subseteq (loan_set_val borrow^m(l1, S.[sp +++ [0] ])) (dom (loan_id_names perm)))
      by set_solver.
    autorewrite with spath; [ | autorewrite with spath; eauto with spath].
    apply singleton_subseteq_l, elem_of_dom in Hl0. destruct Hl0 as (l0' & Hl0').
    cbn in Hl1. apply singleton_subseteq_l, elem_of_dom in Hl1.
    destruct Hl1 as (l1' & Hl1').
    eapply prove_rel.
    { eapply Le_FreshLoan_n, Le_Reborrow_MutBorrow with (sp := permutation_spath _ sp).
      all: eauto with spath.
      rewrite permutation_sget by eauto with spath. rewrite get_node_rename_value, get_borrow_l0.
      reflexivity. autorewrite with spath. eauto with spath.
      eapply is_fresh_apply_permutation; eassumption. }
    autorewrite with spath.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite Hl0'. setoid_rewrite Hl1'.
    reflexivity.

  (* Case [Le_Borrow_Abstraction] *)
  - process_state_equivalence.
    clear Hloan_set. revert fresh_b. process_state_equivalence. intros fresh_b.
    (* TODO: automatize *)
    pose proof Hloan_set as Hloan_set'.
    rewrite loan_set_abstraction_insert, union_subseteq in Hloan_set' |- by assumption.
    destruct Hloan_set' as (Hl' & ?).
    edestruct (is_permutation_delete _ _ _ _ fresh_j perm_A) as (j' & ? & ? & ?).
    execution_step.
    { eexists. split; [eauto with spath | reflexivity]. }
    (* TODO: fix automated rewrite. *)
    autorewrite with spath in *; [ | set_solver].
    cbn in Hl'. rewrite singleton_subseteq_l in Hl'. setoid_rewrite elem_of_dom in Hl'.
    destruct Hl' as (l & Hl).
    eapply is_fresh_apply_permutation in fresh_l'; [ | eauto with spath | exact Hl].
    autorewrite with spath in fresh_l'. rewrite fmap_insert.
    erewrite apply_permutation_insert;
      [ | apply perm_A | simpl_map; now rewrite fresh_j | eassumption].
    eapply Le_FreshLoan_n, Le_Borrow_Abstraction.
    + auto with spath.
    + apply lookup_pkmap_None. assumption.
    + assumption.
    + cbn. unfold rename_loan_id. setoid_rewrite Hl. assumption.
Qed.

Corollary le_equiv_states_commute :
  forward_simulation le_state_base le_state_base equiv_states equiv_states.
Proof.
  intros ? ? ? ? (? & ?)%le_state_base_n_is_le_state_base.
  edestruct le_n_equiv_states_commute as (S' & ? & ?); [eassumption.. | ].
  exists S'. split; [ | assumption].
  eapply le_state_base_n_is_le_state_base. eexists. eassumption.
Qed.

Instance le_symbolic_preorder : PreOrder le_symbolic.
Proof.
  split.
  - apply reflexive_chain; intros S; reflexivity.
  - apply transitive_le, le_equiv_states_commute.
Qed.

(** The following section is here to prove the commutation between the relation
   [le_val_state_base] and equivalence up to loan renaming.
   The reason why we don't prove this for equivalence is that the actual definition is not
   suitable. If we have [(S,, a |-> v) < (S',, a |-> v')] and a permutation perm on [S,, a |-> v],
   by applying [le_equiv_states_commute], we only know that there exists a permutation
   [perm'] such that perm [(S,, a |-> v) < perm'(S',, a |-> v')]. But there is no reason why we
   would have perm(a) = perm'(a).
   This is the case with rename_state, but this property is not specific to equivalence up to loan
   renaming. And the theorem [le_equiv_states_up_to_loan_renaming_commute] is very redundant
   with [le_equiv_states_commute].
   In order to avoid doing twice a similar tedious proof, a solution is just to change the
   definition of is_state_equivalence and the statement of [le_equiv_states_commute].
   The idea is to have a single permutation perm such that
   perm(S,, a |-> v) < perm(S',, a |-> v')$. This is not currently possible as the states
   [S,, a |-> v] and [S',, a |-> v'] do not have the same anonymous variables and
   abstraction regions. But if we change the definition on is_state_equivalence so that a
   the domain of a the anonymous and abstractions permutations are superset (and not just equal)
   of the the respective maps, we could prove this.
   TODO: do these changes and remove this entire section.
 *)
Lemma fresh_anon_rename_state S a r : fresh_anon S a -> fresh_anon (rename_state r S) a.
Proof. unfold fresh_anon. rewrite !get_at_anon. cbn. simpl_map. intros ->. reflexivity. Qed.
Hint Resolve fresh_anon_rename_state : spath.

Lemma fresh_abstraction_rename_state S i r :
  fresh_abstraction S i -> fresh_abstraction (rename_state r S) i.
Proof. unfold fresh_abstraction. cbn. simpl_map. intros ->. reflexivity. Qed.
Hint Resolve fresh_abstraction_rename_state : spath.

Hint Resolve-> rename_state_valid_spath : spath.

Lemma is_fresh_rename_val perm v l l' :
  map_inj perm -> subseteq (loan_set_val v) (dom perm) -> lookup l perm = Some l' ->
  is_fresh_val l v -> is_fresh_val l' (rename_value perm v).
Proof.
  intros inj_perm dom_perm H fresh_l p valid_p.
  rewrite <-vget_rename_value, get_node_rename_value.
  unfold is_loan_id. rewrite get_loan_id_rename_node.
  destruct (get_loan_id _) as [l0 | ] eqn:EQN; [ | discriminate]. cbn.
  assert (elem_of l0 (dom perm)) as (l'0 & get_l'0)%elem_of_dom.
  { eapply elem_of_weaken; [ | exact dom_perm]. rewrite elem_of_loan_set_val. eauto. }
  unfold rename_loan_id. setoid_rewrite get_l'0. injection as Hdiff.
  eapply inj_perm in Hdiff; [ | eassumption..]. subst.
  eapply fresh_l; [ | exact EQN].
  apply valid_get_node_vget_not_bot. intros G. rewrite G in EQN. discriminate.
Qed.

Lemma is_fresh_rename_state perm S l l' :
  valid_loan_id_names perm S -> lookup l perm = Some l' ->
  is_fresh l S -> is_fresh l' (rename_state perm S).
Proof.
  intros (inj_perm & dom_perm) get_l' fresh_l p (v & get_v & valid_v_p).
  unfold sget. rewrite get_v. rewrite get_map_rename_state, lookup_fmap in get_v.
  apply fmap_Some_1 in get_v. destruct get_v as (w & get_w & ->).
  eapply is_fresh_rename_val; eauto.
  - transitivity (loan_set_state S); [ | assumption].
    eapply loan_set_val_subset_eq_loan_set_state. eassumption.
  - rewrite not_state_contains_map_Forall in fresh_l. eapply fresh_l, get_w.
Qed.

Lemma le_no_fresh_anon_equiv_states_up_to_loan_renaming_commute n S S' perm :
  valid_loan_id_names perm S -> valid_loan_id_names perm S' ->
  le_no_fresh_loan n S' S ->
  le_no_fresh_loan n (rename_state perm S') (rename_state perm S).
Proof.
  intros H G. destruct (H) as (inj_perm & perm_dom_S). destruct (G) as (_ & perm_dom_S').
  intros Hle. destruct Hle.
  - rewrite rename_state_sset by eauto with spath.
    erewrite <-vsize_rename_value, <-rename_state_sget. apply Le_ToSymbolic.
    all: rewrite rename_state_sget; eauto with spath.
  - rewrite rename_state_add_abstraction by assumption.
    rewrite loan_set_add_anon, loan_set_add_abstraction in * |- by assumption.
    rewrite rename_state_add_anon by (try split; set_solver).
    erewrite <-vsize_rename_value. apply Le_ToAbs; auto with spath.
    rewrite <-apply_id_permutation. apply to_abs_apply_permutation; [ | assumption].
    eapply is_permutation_dom_eq; [apply dom_fmap_L | apply id_permutation_is_permutation].
  - rewrite loan_set_add_anon in * |- by assumption.
    rewrite rename_state_add_anon by (try split; set_solver).
    erewrite <-vsize_rename_value. apply Le_RemoveAnon; auto with spath.
  - pose proof (loan_set_sget S sp).
    clear H perm_dom_S.
    rewrite rename_state_add_anon. 2: etransitivity; eassumption.
    2: apply valid_loan_id_names_sset; auto with spath.
    rewrite <-rename_state_sget, rename_state_sset by auto with spath.
    apply Le_MoveValue; auto with spath.
    + rewrite rename_state_sget. not_contains.
    + intros p. rewrite rename_state_sget, get_node_rename_value.
      intros K. apply sp_not_in_borrow. destruct (get_node _); inversion K. constructor.
  - rewrite !rename_state_add_abstraction by auto with spath.
    erewrite <-(abs_measure_rename_set _ A), <-(abs_measure_rename_set _ B).
    erewrite <-(abs_measure_rename_set _ C). apply Le_MergeAbs; auto with spath.
    apply merge_abstraction_rename_value. assumption.
  - rewrite !rename_state_add_abstraction, fmap_insert by assumption.
    erewrite <-vsize_rename_value. apply Le_Abs_ClearValue; auto with spath.
    rewrite lookup_fmap, fresh_j. reflexivity.
  - rewrite rename_state_add_anon by auto with spath.
    apply Le_AnonValue. auto with spath.
Qed.

Lemma le_equiv_states_up_to_loan_renaming_commute S S' perm l' l'' :
  valid_loan_id_names perm S -> valid_loan_id_names perm S' -> lookup l' perm = Some l'' ->
  le_fresh_loan l' S' S ->
  le_fresh_loan l'' (rename_state perm S') (rename_state perm S).
Proof.
  intros H G get_l''. destruct (H) as (inj_perm & perm_dom_S). destruct (G) as (_ & perm_dom_S').
  intros Hle. destruct Hle.
  - rewrite loan_set_add_anon, loan_set_borrow in perm_dom_S by auto with spath.
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (? & perm_dom_S).
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (l'_in_dom & ?).
    rewrite rename_state_add_anon.
    2: rewrite loan_set_borrow; set_solver. 2: split; assumption.
    rewrite rename_state_sset by set_solver. rewrite rename_loan_id_borrow, <-rename_state_sget.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite get_l''.
    eapply Le_Fresh_MutLoan; auto with spath.
    + rewrite rename_state_sget. eauto with spath.
    + apply singleton_subseteq_l, elem_of_dom in l'_in_dom. destruct l'_in_dom as (l & get_l).
      eapply is_fresh_rename_state; eauto.
  - rewrite loan_set_add_anon, loan_set_borrow in perm_dom_S by auto with spath.
    rewrite union_subseteq in perm_dom_S. destruct perm_dom_S as (? & l0_l1_in_dom).
    pose proof l0_l1_in_dom. rewrite union_subseteq in l0_l1_in_dom.
    destruct l0_l1_in_dom as (l0_in_dom & l1_in_dom).
    pose proof (loan_set_sget S (sp +++ [0])).
    rewrite rename_state_add_anon; [ | assumption | ].
    2: { apply valid_loan_id_names_sset; [ | assumption]. rewrite loan_set_borrow.
      set_solver. }
    rewrite rename_state_sset by (rewrite loan_set_borrow; set_solver).
    rewrite !rename_loan_id_borrow. rewrite <-rename_state_sget.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite get_l''.
    apply Le_Reborrow_MutBorrow.
    + auto with spath.
    + rewrite rename_state_sget, get_node_rename_value, get_borrow_l0. reflexivity.
    + assumption.
    + rewrite rename_state_sget. eauto with spath.
    + eapply is_fresh_rename_state; eauto.
  - rewrite loan_set_add_anon, loan_set_add_abstraction in perm_dom_S by auto with spath.
    cbn [loan_set_val] in perm_dom_S.
    assert (valid_loan_id_names perm (S,,, i |-> insert j (loan^m (ty', l')) A)).
    { split; [assumption | ]. rewrite loan_set_add_abstraction by assumption. set_solver. }
    rewrite rename_state_add_anon by set_solver.
    rewrite !rename_state_add_abstraction by assumption. rewrite fmap_insert.
    cbn [rename_value]. unfold rename_loan_id. setoid_rewrite get_l''.
    apply Le_Borrow_Abstraction; auto with spath.
    + simpl_map. rewrite fresh_j. reflexivity.
    + rewrite <-rename_state_add_abstraction by assumption.
      assert (is_Some (lookup l' perm)) as (l & Hl). { apply elem_of_dom. set_solver. }
      eapply is_fresh_rename_state; eassumption.
Qed.

Definition equiv_val_state_up_to_loan_renaming (vS0 vS1 : value * state) :=
  let (v0, S0) := vS0 in
  let (v1, S1) := vS1 in
  exists perm, valid_loan_id_names perm S0 /\
               subseteq (loan_set_val v0) (dom perm) /\
               S1 = rename_state perm S0 /\ v1 = rename_value perm v0.

Definition le_val_state_ut := chain equiv_val_state_up_to_loan_renaming le_val_state_base^*.

Lemma equiv_val_state_up_to_loan_renaming_implies_equiv_val_state :
  forall vSl vSr, equiv_val_state_up_to_loan_renaming vSl vSr -> equiv_val_state vSl vSr.
Proof.
  intros (v & S) (? & ?) (r & ? & ? & -> & ->).
  exists {|accessor_perm := id_state_permutation S; loan_id_names := r|}.
  cbn. split.
  - split.
    + apply id_state_permutation_is_valid_accessor_permutation.
    + assumption.
  - split; [assumption | ]. split; [ | reflexivity].
    rewrite apply_state_permutation_alt
      by apply id_state_permutation_is_valid_accessor_permutation.
     cbn. rewrite apply_id_state_permutation. reflexivity.
Qed.

Instance transitive_equiv_val_state_up_to_loan_renaming :
  Transitive equiv_val_state_up_to_loan_renaming.
Proof.
  intros (v & S) (? & ?) (? & ?) (p0 & ? & H & -> & ->) (p1 & ? & G & -> & ->).
  exists (map_compose p1 p0). split. { apply valid_loan_id_names_compose; assumption. }
  rewrite rename_state_compose, rename_value_compose by assumption. split; [ | auto].
  intros l Hl. specialize (H l Hl).
  apply elem_of_dom. setoid_rewrite map_lookup_compose. apply elem_of_dom in H.
  destruct H as (l' & Hl'). rewrite Hl'. cbn.
  apply elem_of_dom, G.
  apply elem_of_loan_set_val in Hl. destruct Hl as (p & get_l).
  rewrite elem_of_loan_set_val. exists p.
  rewrite <-vget_rename_value, get_node_rename_value, get_loan_id_rename_node.
  rewrite get_l. cbn. unfold rename_loan_id. setoid_rewrite Hl'. reflexivity.
Qed.

Instance reflexive_equiv_val_state_up_to_loan_renaming :
  Reflexive equiv_val_state_up_to_loan_renaming.
Proof.
  intros (v & S). exists (id_loan_map (union (loan_set_state S) (loan_set_val v))). repeat split.
  - apply id_loan_map_inj.
  - rewrite dom_id_loan_map. set_solver.
  - rewrite dom_id_loan_map. set_solver.
  - symmetry. apply rename_state_identity.
  - symmetry. apply rename_value_id. apply lookup_id_loan_map.
Qed.

Instance reflexive_le_val_state_ut : Reflexive le_val_state_ut.
Proof. intros (v & S). exists (v, S). split; reflexivity. Qed.

Instance transitive_le_val_state_ut : Transitive le_val_state_ut.
Proof.
  apply transitive_le.
  intros vSl vSh Hperm vS'h Hle. revert Hperm. revert vSh.
  destruct Hle; intros vSh Hperm.
  - destruct vSh. destruct Hperm as (perm & Hperm & ? & -> & ->).
    pose proof Hperm as Hperm'.
    apply extend_loan_id_names with (L := loan_set_state Sl) in Hperm'.
    destruct Hperm' as (perm' & Hperm' & ? & ? & ->).
    assert (valid_loan_id_names perm' Sl). { split; [apply Hperm' | assumption]. }
    eexists. split.
    { econstructor.
      apply le_no_fresh_anon_equiv_states_up_to_loan_renaming_commute; [ | | eassumption].
      all: assumption. }
    exists perm'. split; [assumption | ]. erewrite rename_value_subseteq by eassumption.
    split; [ | auto]. etransitivity; [ | apply subseteq_dom]; eassumption.
  - destruct vSh. destruct Hperm as (perm & Hperm & ? & -> & ->).
    pose proof Hperm as Hperm'.
    (* Note: actually, we could prove that [perm] already contains the loan identifiers
       of [Sl], as well as l'. *)
    apply extend_loan_id_names with (L := union (loan_set_state Sl) {[l']}) in Hperm'.
    destruct Hperm' as (perm' & Hperm' & ? & G%union_subseteq & ->).
    destruct G as (? & (l'' & ?)%singleton_subseteq_l%elem_of_dom).
    assert (valid_loan_id_names perm' Sl). { split; [apply Hperm' | assumption]. }
    erewrite rename_value_subseteq by eassumption.
    assert (subseteq (loan_set_val v) (dom perm')).
    { etransitivity; [eassumption | ]. apply subseteq_dom. eassumption. }
    eexists. split.
    { eapply Le_ValState_FreshLoan.
      eapply le_equiv_states_up_to_loan_renaming_commute; try eassumption.
      eapply is_fresh_rename_val; try eassumption. apply Hperm'. }
    exists perm'. auto.
  - destruct vSh. destruct Hperm as (perm & Hperm & ? & -> & ->).
    eexists. split.
    { rewrite vset_rename_value. apply Le_ToSymbolic_Val.
      all: rewrite <-vget_rename_value; auto with spath. }
    exists perm. split; [assumption | ]. split; [ | auto].
    rewrite <-(vset_same v vp). rewrite <-vset_twice_equal with (x := VSymbolic ty).
    etransitivity. { apply loan_set_vset. apply vset_same_valid. validity. }
    rewrite (loan_set_id_empty (v.[[vp]])) by assumption. set_solver.
  - destruct vSh. destruct Hperm as (perm & Hperm & ? & -> & ->).
    destruct Hperm as (inj_perm & loans_S). rewrite loan_set_add_anon in loans_S by assumption.
    rewrite union_subseteq in loans_S. destruct loans_S as (loans_S & G).
    assert (valid_loan_id_names perm S) by now split.
    rewrite rename_state_add_anon by assumption.
    rewrite vset_rename_value. cbn [rename_value]. rewrite vget_rename_value.
    cbn [loan_set_val] in G. assert (elem_of l1 (dom perm)) as K by set_solver.
    setoid_rewrite elem_of_dom in K. destruct K as (l'1 & K).
    assert (subseteq (loan_set_val v) (dom perm)).
    { rewrite <-(vset_same v vp). erewrite <-vset_twice_equal.
      etransitivity. { apply loan_set_vset. apply vset_same_valid. validity. }
      rewrite union_subseteq. split; [eassumption | ].
      replace (v.[[vp]]) with (borrow^m(l0, v.[[vp ++ [0] ]])).
      { cbn [loan_set_val]. rewrite union_subseteq. split; [set_solver | ].
        etransitivity; [ | exact H].
        etransitivity; [ | apply (loan_set_vget _ (vp ++ [0]))].
        autorewrite with spath. reflexivity.
        rewrite valid_vpath_app. split. apply vset_same_valid. validity.
        econstructor; [ | constructor]. autorewrite with spath. reflexivity. }
      { rewrite vget_app. destruct (v.[[vp]]); inversion get_borrow_l0. reflexivity. } }
    eexists. split.
    { apply Le_Reborrow_MutBorrow_Val.
      auto with spath.
      rewrite <-vget_rename_value, get_node_rename_value, get_borrow_l0; reflexivity.
      rewrite <-vget_rename_value. auto with spath.
      eapply is_fresh_rename_state. assumption.
      unfold rename_loan_id. setoid_rewrite K. reflexivity. assumption.
      eapply is_fresh_rename_val; try eassumption.
      unfold rename_loan_id. setoid_rewrite K. reflexivity.
    }
    exists perm. auto.
Qed.

(** Derived rules of [le_state_base]. *)
Lemma Le_Reborrow_MutBorrow_Abs S sp l0 l1 i kb kl ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_i : fresh_abstraction S i)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
    (Hk : kb <> kl)
    (Htype : is_of_type ty (S.[sp +++ [0] ])):
    le_state_base^* S (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],,,
                        i |-> {[kb := (borrow^m(l0, VSymbolic ty));
                                kl := loan^m(ty, l1)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. eapply Le_FreshLoan, Le_Reborrow_MutBorrow; eassumption. }
  constructor. econstructor. eapply Le_ToAbs with (a := a).
  - eauto with spath.
  - repeat apply fresh_abstraction_sset. eassumption.
  - autorewrite with spath. constructor. assumption.
Qed.

Lemma Le_Fresh_MutLoan_Abs S sp l' i k ty
    (fresh_l' : is_fresh l' S)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (fresh_i : fresh_abstraction S i)
    (no_loan : not_contains_loan (S.[sp]))
    (no_borrow : not_contains_borrow (S.[sp]))
    (Htype : is_of_type ty (S.[sp])) :
    le_state_base^* S (S.[sp <- loan^m(ty, l')],,,
                        i |-> {[k := borrow^m(l', VSymbolic ty)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. econstructor. eapply Le_ToSymbolic; eassumption. }
  etransitivity.
  { constructor. eapply Le_FreshLoan, Le_Fresh_MutLoan with (sp := sp).
    - apply fresh_anon_sset. eassumption.
    - validity.
    - assumption.
    - autorewrite with spath. constructor.
    - not_contains. }
  etransitivity.
  { constructor. econstructor. eapply Le_ToAbs with (a := a) (i := i).
    - eauto with spath.
    - repeat apply fresh_abstraction_sset. assumption.
    - autorewrite with spath. constructor; [constructor | not_contains..]. }
  autorewrite with spath. reflexivity.
Qed.

Lemma le_uninitialize_value S sp
  (no_loan : not_contains_loan (S.[sp]))
  (no_borrow : not_contains_borrow (S.[sp]))
  (valid_sp : valid_spath S sp)
  (sp_not_in_borrow : not_in_borrow S sp)
  (sp_in_abstraction : not_in_abstraction sp) :
  le_state_base^* S (S.[sp <- bot]).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity; constructor; econstructor.
  { apply Le_MoveValue with (sp := sp) (a := a); try assumption. not_contains_outer. }
  { apply Le_RemoveAnon; auto with spath. }
Qed.

(* TODO: name *)
Lemma le_borrow_abs S ia ib ja jb A B l ty :
  ia <> ib -> lookup ja A = None -> lookup jb B = None ->
  is_fresh l (S,,, ia |-> A,,, ib |-> B) ->
  le_state_base^* (S,,, ia |-> A,,, ib |-> B)
                   (S,,, ia |-> insert ja (loan^m(ty, l)) A,,, ib |-> insert jb (borrow^m(l, VSymbolic ty)) B).
Proof.
  intros ? ? ?.
  setoid_rewrite <-(add_remove_add_abstraction S ia).
  rewrite !(add_abstraction_commute _ ia ib) by congruence.
  setoid_rewrite <-(add_remove_add_abstraction _ ib).
  set (S' := remove_abstraction ib (remove_abstraction ia S)).
  assert (fresh_abstraction S' ia).
  { unfold S', remove_abstraction, fresh_abstraction. cbn. simpl_map. reflexivity. }
  assert (fresh_abstraction S' ib) by apply remove_abstraction_fresh.
  destruct (exists_fresh_anon S') as (a & fresh_a).
  etransitivity; [constructor | ].
  { eapply Le_FreshLoan, Le_Borrow_Abstraction with (j := ja) (l' := l) (ty' := ty) (a := a).
    all: auto with spath. }
  destruct (exist_fresh (dom (abstractions (S',,, ib |-> B,,, ia |-> insert ja (loan^m (ty, l)) A))))
      as (k & fresh_k%not_elem_of_dom).
  etransitivity; constructor; econstructor.
  { apply Le_ToAbs with (i := k); auto with spath.
    eapply ToAbs_MutBorrow with (k := jb); [constructor | not_contains..]. }
  { rewrite <-!(add_abstraction_commute _ ia) by congruence.
    apply fresh_abstraction_add_abstraction_rev in fresh_k. destruct fresh_k as (fresh_k & ?).
    apply fresh_abstraction_add_abstraction_rev in fresh_k. destruct fresh_k as (fresh_k & ?).
    apply Le_MergeAbs; auto with spath.
    eexists _, _. split; [apply Remove_nothing | ].
    apply UnionInsert with (j := jb); [assumption | now simpl_map | ].
    apply UnionEmpty. }
Qed.

(** * Results about the simulation relation on branching states. *)
Lemma le_branching_alt Bl Br :
  le_branching Bl Br <-> map_included (fun _ => le_symbolic) Bl Br.
Proof.
  split. all: intros H r; specialize (H r); revert H.
  all: remember (lookup r Bl) as Sl eqn:EQN_l; setoid_rewrite <-EQN_l.
  all: remember (lookup r Br) as Sr eqn:EQN_r; setoid_rewrite <-EQN_r.
  - intros [ ]; cbn.
    + autodestruct.
    + assumption.
  - destruct Sl, Sr; cbn; try constructor; easy.
Qed.

(* Because [le_symbolic] is a pre-order, [map_included (fun _ => le_symbolic)] also is. We use this to prove that the equivalent relation [le_branching] is a pre-order. *)
Instance le_symbolic_branching : PreOrder le_branching.
Proof.
  split.
  - intros ?. rewrite le_branching_alt. reflexivity.
  - intros Bl Bm Br. rewrite !le_branching_alt. transitivity Bm; assumption.
Qed.

(** Lemmas about [le_branching] and [is_join] *)
Lemma le_singleton S r B :
  match lookup r B with
  | Some Sr => le_symbolic S Sr
  | None => False
  end ->
  le_branching {[r := S]} B.
Proof.
  intros H. destruct (lookup r B) as [Sr | ] eqn:get_Sr; [ | contradiction].
  intros r'. destruct (decide (r = r')) as [<- | ]; unfold branching_state in *.
  - simpl_map. constructor. assumption.
  - simpl_map. constructor.
Qed.

Lemma le_branching_delete r0 Sl Sr :
  le_branching Sl Sr -> le_branching (delete r0 Sl) (delete r0 Sr).
Proof.
  intros H r. specialize (H r). unfold branching_state.
  destruct (decide (r0 = r)) as [<- | ]; simpl_map; [constructor | assumption].
Qed.

Lemma le_is_join_l Bl Br Bjoin : is_join Bl Br Bjoin -> le_branching Bl Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.
Hint Resolve le_is_join_l : spath.

Lemma le_is_join_r Bl Br Bjoin : is_join Bl Br Bjoin -> le_branching Br Bjoin.
Proof. intros H r. specialize (H r). inversion H; constructor; [reflexivity | assumption]. Qed.
Hint Resolve le_is_join_r : spath.

(** If [Bup] is an upper bound of two states [B0] and [B1], it is not necessarily a join. Indeed, there may exist tokens [r] such that [lookup r B0] (respectively [lookup r B1]) is None, but [lookup r Bup] is different from [lookup r B1] (respectively [lookup r B0]).

   We need to "compute" a join by choosing for each tag [r] a value among [lookup r B0],  [lookup r B1] and [lookup r Bup]. *)
Definition compute_option_join (oSl oSr : option state) default :=
  match oSl, oSr with
  | None, _ => oSr
  | _, None => oSl
  | _, _ => Some default
  end.

Definition compute_join (B0 B1 Bup : branching_state) : branching_state :=
  map_imap (fun r => compute_option_join (lookup r B0) (lookup r B1)) Bup.

Lemma exists_join_state B0 B1 Bup
  (Hle_0 : le_branching B0 Bup) (Hle_1 : le_branching B1 Bup) :
  let Bjoin := compute_join B0 B1 Bup in
  is_join B0 B1 Bjoin /\ le_branching Bjoin Bup.
Proof.
  intros Bjoin. unfold Bjoin. split.
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hle_0 r). specialize (Hle_1 r).
    destruct Hle_0 as [oSr | ]; inversion Hle_1; subst.
    all: try destruct oSr; constructor; assumption.
  - intros r. setoid_rewrite map_lookup_imap. fold branching_state.
    specialize (Hle_0 r). specialize (Hle_1 r).
    unfold compute_option_join.
    destruct Hle_0 as [oSr | ]; inversion Hle_1; subst.
    all: try destruct oSr; constructor; assumption || reflexivity.
Qed.
