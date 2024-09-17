Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Import ListNotations.

Inductive HLPL_plus_val :=
| HLPL_plus_bot
| HLPL_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| HLPL_plus_mut_loan (l : loan_id)
| HLPL_plus_mut_borrow (l : loan_id) (v : HLPL_plus_val)
(*
| HLPL_plus_shr_loan (l : loan_id) (v : HLPL_plus_val)
| HLPL_plus_shr_borrow (l : loan_id)
 *)
| HLPL_plus_loc (l : loan_id) (v : HLPL_plus_val)
| HLPL_plus_ptr (l : loan_id)
(* | HLPL_plus_pair (v0 : HLPL_plus_val) (v1 : HLPL_plus_val) *)
.

Variant HLPL_plus_binder :=
| Var (v : var)
(* | Box (l : nat) *)
| Anon.

Program Global Instance EqDec_binder : EqDec HLPL_plus_binder.
Next Obligation. repeat decide equality. Qed.

Variant HLPL_plus_constructor :=
| HLPL_plus_botC
| HLPL_plus_intC (n : nat)
| HLPL_plus_mut_loanC (l : loan_id)
| HLPL_plus_mut_borrowC (l : loan_id)
| HLPL_plus_locC (l : loan_id)
| HLPL_plus_ptrC (l : loan_id)
.

Definition HLPL_plus_arity c := match c with
| HLPL_plus_botC => 0
| HLPL_plus_intC _ => 0
| HLPL_plus_mut_loanC _ => 0
| HLPL_plus_mut_borrowC _ => 1
| HLPL_plus_locC _ => 1
| HLPL_plus_ptrC _ => 0
end.

Definition HLPL_plus_get_constructor v := match v with
| HLPL_plus_bot => HLPL_plus_botC
| HLPL_plus_int n => HLPL_plus_intC n
| HLPL_plus_mut_loan l => HLPL_plus_mut_loanC l
| HLPL_plus_mut_borrow l _ => HLPL_plus_mut_borrowC l
| HLPL_plus_loc l _ => HLPL_plus_locC l
| HLPL_plus_ptr l => HLPL_plus_ptrC l
end.

Definition HLPL_plus_subvalues v := match v with
| HLPL_plus_bot => []
| HLPL_plus_int _ => []
| HLPL_plus_mut_loan _ => []
| HLPL_plus_mut_borrow _ v => [v]
| HLPL_plus_loc _ v => [v]
| HLPL_plus_ptr l => []
end.

Definition HLPL_plus_fold c vs := match c, vs with
| HLPL_plus_intC n, [] => HLPL_plus_int n
| HLPL_plus_mut_loanC l, [] => HLPL_plus_mut_loan l
| HLPL_plus_mut_borrowC l, [v] => HLPL_plus_mut_borrow l v
| HLPL_plus_locC l, [v] => HLPL_plus_loc l v
| HLPL_plus_ptrC l, [] => HLPL_plus_ptr l
| _, _ => HLPL_plus_bot
end.

Program Instance ValueHLPL : Value HLPL_plus_val := {
  constructors := HLPL_plus_constructor;
  arity := HLPL_plus_arity;
  get_constructor := HLPL_plus_get_constructor;
  subvalues := HLPL_plus_subvalues;
  fold_value := HLPL_plus_fold;
  bot := HLPL_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
destruct v; destruct w; inversion eq_constructor; inversion eq_subvalues; reflexivity.
Qed.

Next Obligation.
  destruct c; (rewrite length_zero_iff_nil in H; rewrite H) ||
              destruct (length_1_is_singleton H) as [? ->];
              reflexivity.
Qed.
Next Obligation.
  destruct c; (rewrite length_zero_iff_nil in H; rewrite H) ||
              destruct (length_1_is_singleton H) as [? ->];
              reflexivity.
Qed.

Definition HLPL_plus_state := state HLPL_plus_binder HLPL_plus_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: move in lang.v *)
(* TODO: set every priority to 0 ?)
Reserved Notation "'bot'" (at level 50).
Reserved Notation "'loan^m' l" (at level 50).
Reserved Notation "'borrow^m' ( l , v )" (at level 50, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 50, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 50).

Notation "'bot'" := HLPL_plus_bot: hlpl_plus_scope.
Notation "'loan^m' l" := (HLPL_plus_mut_loan l) : hlpl_plus_scope.
Notation "'borrow^m' ( l  , v )" := (HLPL_plus_mut_borrow l v) : hlpl_plus_scope.
Notation "'loc' ( l , v )" := (HLPL_plus_loc l v) : hlpl_plus_scope.
Notation "'ptr' ( l )" := (HLPL_plus_ptr l) : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with HLPL_plus_val. *)
Open Scope hlpl_plus_scope.

Inductive eval_proj (S : HLPL_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l v
    (imm_or_mut : perm <> Mov)
    (get_q : S.[q] = borrow^m(l, v)) :
    eval_proj S perm Deref q (q +++ [0])
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| Eval_Deref_Ptr_Locs q q' l w (imm_or_mut : perm <> Mov)
    (get_q : S.[q] = ptr(l)) (get_q' : S.[q'] = loc(l, w)) :
    eval_proj S perm Deref q q'
(* Coresponds to R-Loc and W-Loc in the article. *)
| Eval_Loc proj q q' l v (imm_or_mut : perm <> Mov) (get_q : sget q S = loc(l, v)) :
    eval_proj S perm proj (q +++ [0]) q' -> eval_proj S perm proj q q'
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : HLPL_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r: eval_proj S perm proj p q -> eval_path S perm P q r ->
    eval_path S perm (proj :: P) p r.

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. rewrite get_q. discriminate.
    + rewrite get_q. econstructor; reflexivity || constructor.
  - apply get_not_bot_valid_spath. rewrite get_q'. discriminate.
  - apply IHeval_proj.
Qed.

Lemma eval_path_valid (s : HLPL_plus_state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Notation eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof.
  destruct H as (? & ? & ?). eapply eval_path_valid; try eassumption.
  eapply find_binder_valid. eassumption.
Qed.

(* Setting up the definitions for judgements like "loan \notin v" or
   "l is fresh". *)
Definition state_contains (H : HLPL_plus_val -> Prop) (S : HLPL_plus_state) :=
  exists p, valid_spath S p /\ H (S.[p]).

Definition value_contains (H : HLPL_plus_val -> Prop) (v : HLPL_plus_val) :=
  exists p, valid_vpath v p /\ H (v.[[p]]).

Definition is_loan (v : HLPL_plus_val) :=
  exists l, v = loan^m(l).
Definition contains_loan := value_contains is_loan.

Definition is_mut_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition contains_outer_loan v :=
  exists l p, v.[[p]] = loan^m(l) /\ (forall q, vprefix q p -> ~is_mut_borrow (v.[[q]])).

Definition contains_outer_loc (v : HLPL_plus_val) :=
  exists l w p, v.[[p]] = loc(l, w) /\ (forall q, vprefix q p -> ~is_mut_borrow (v.[[q]])).

Definition is_loc (v : HLPL_plus_val) := exists l w, v = loc(l, w).
Definition contains_loc := value_contains is_loc.

Variant is_loan_id (l : loan_id) : HLPL_plus_val -> Prop  :=
| Is_loan_id_loan : is_loan_id l (loan^m(l))
| Is_loan_id_borrow w : is_loan_id l (borrow^m(l, w))
| Is_loan_id_ptr : is_loan_id l (ptr(l))
| Is_loan_id_loc w : is_loan_id l (loc(l, w)).

Definition is_fresh l S := ~state_contains (is_loan_id l) S.

Definition is_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition not_in_borrow (S : HLPL_plus_state) p :=
  forall q, prefix q p /\ is_borrow (S.[q]) -> q = p.

Definition contains_bot (v : HLPL_plus_val) :=
  value_contains (fun w => w = bot) v.

Inductive copy_val : HLPL_plus_val -> HLPL_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_plus_int n) (HLPL_plus_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

Variant eval_op (S : HLPL_plus_state) : operand -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
| Eval_IntConst n : eval_op S (IntConst n) (HLPL_plus_int n) S
| Eval_copy (p : place) pi v : eval_place S Imm p pi -> copy_val (S.[pi]) v ->
    eval_op S (Copy p) v S
| Eval_move (p : place) pi : eval_place S Mov p pi -> ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
  eval_op S (Move p) (S.[pi]) (S.[pi <- bot]).

Variant eval_rvalue (S : HLPL_plus_state) : rvalue -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
| Eval_just op v S' : eval_op S op v S' -> eval_rvalue S (Just op) v S'
(* For the moment, the only operation is the natural sum. *)
| Eval_bin_op S' S'' op_l op_r m n : eval_op S op_l (HLPL_plus_int m) S' ->
   eval_op S' op_r (HLPL_plus_int n) S'' ->
   eval_rvalue S (BinOp op_l op_r) (HLPL_plus_int (m + n)) S''
| Eval_pointer_loc p pi l v : eval_place S Mut p pi -> S.[pi] = loc(l, v) ->
    ~contains_loan v -> ~contains_bot v ->
    eval_rvalue S (&mut p) (ptr(l)) S
| Eval_pointer p pi l : eval_place S Mut p pi -> ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
    is_fresh l S -> ~is_loc (S.[pi]) ->
    eval_rvalue S (&mut p) (ptr(l)) (S.[pi <- loc(l, S.[pi])]).

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_refl S : reorg S S
| Reorg_trans S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    ~contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_plus_state -> statement -> nat -> Option (statement_result * HLPL_plus_state) -> Prop
*)
Inductive eval_stmt : HLPL_plus_state -> statement -> statement_result -> HLPL_plus_state -> Prop :=
| Eval_nop S : eval_stmt S Nop rUnit S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : eval_stmt S0 stmt_l rUnit S1)
    (eval_stmt_r : eval_stmt S1 stmt_r r S2) : eval_stmt S0 (stmt_l ;; stmt_r) r S2
| Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : eval_stmt S0 stmt_l rPanic S1) :
    eval_stmt S0 (stmt_l ;; stmt_r) rPanic S1
| Eval_assign S S' p rv v sp : eval_rvalue S rv v S' -> eval_place S' Mut p sp ->
    ~contains_outer_loc (S'.[sp]) -> ~contains_outer_loan (S'.[sp]) ->
    eval_stmt S (ASSIGN p <- rv) rUnit ((Anon, S'.[sp]) :: S'.[sp <- v])
.

(* TODO: introduce well-formedness judgement. *)
Variant le_state_base : HLPL_plus_state -> HLPL_plus_state -> Prop :=
(*
| Le_refl S : le_state S S
| Le_trans S0 S1 S2 : le_state S0 S1 -> le_state S1 S2 -> le_state S0 S2
*)
| Le_MutBorrow_To_Ptr S l p q v : disj p q -> S{{p}} = vZero (HLPL_plus_loan l) ->
    S{{q}} = vUnit (HLPL_plus_borrow l) v ->
    le_state_base (S{{p <- vUnit (HLPL_plus_loc l) v}}{{q <- vZero (HLPL_plus_ptr l)}}) S.

Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| Cl_base x y : R x y -> refl_trans_closure R x y
| Cl_refl x : refl_trans_closure R x x
| Cl_trans x y z : refl_trans_closure R x y -> refl_trans_closure R y z -> refl_trans_closure R x z.

Definition le_state := refl_trans_closure le_state_base.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l : loan_id).
  Context (v : HLPL_plus_val).
  Context (sp_loan sp_borrow : spath).
  Context (valid_sp_loan : valid_spath S_r sp_loan).
  Context (valid_sp_borrow : valid_spath S_r sp_borrow).
  Context (Hdisj : disj sp_loan sp_borrow).
  Context (HS_r_loan : S_r{{sp_loan}} = vZero (HLPL_plus_loan l)).
  Context (HS_r_borrow : S_r{{sp_borrow}} = vUnit (HLPL_plus_borrow l) v).
  Notation S_l := (S_r{{sp_loan <- vUnit (HLPL_plus_loc l) v}}{{sp_borrow <- vZero (HLPL_plus_ptr l)}}).

  Notation "sp_l ~ sp_r" :=
    ((sp_l = sp_r) \/
     (exists vp_tail, sp_l = sp_loan +++ [0] ++ vp_tail /\ sp_r = sp_borrow +++ [0] ++ vp_tail))
  (at level 1).

  Lemma rel_prefix_sp_borrow sp_l sp_r (H : sp_l ~ sp_r)
    (pref : strict_prefix sp_r sp_borrow) : sp_l = sp_r.
  Proof.
    destruct H as [ | H].
    - assumption.
    - exfalso. eapply strict_prefix_antisym.
      + exact pref.
      + destruct H as (vp_tail & _ & ?). exists 0, vp_tail. auto.
  Qed.

  Lemma rel_sp_borrow sp_l : sp_l ~ sp_borrow -> sp_l = sp_borrow.
  Proof.
    intros [? | H].
    - assumption.
    - exfalso. apply (strict_prefix_irrefl sp_borrow).
      destruct H as (vp_tail & _ & ?). exists 0, vp_tail. auto.
  Qed.

  (* TODO: General property of paths *)
  Lemma strict_prefix_sp_borrow q : strict_prefix q sp_borrow ->
    strict_prefix q sp_loan \/ disj q sp_loan.
  Admitted.

  Lemma strict_prefix_sp_borrow_same_constructor q :
    valid_spath S_r q -> strict_prefix q sp_borrow ->
    same_constructor (S_l{{q}}) (S_r{{q}}).
  Proof.
    intros ? H. etransitivity.
    - symmetry. apply same_constructor_subst_strict_prefix. admit. assumption.
    - apply strict_prefix_sp_borrow in H. destruct H.
      + symmetry. apply same_constructor_subst_strict_prefix; assumption.
      + symmetry. apply same_constructor_subst_disj. assumption. assumption. symmetry. assumption.
  Admitted.

  (* TODO: only true for perm >= Mut, not for perm = Imm *)
  Lemma eval_path_mut_borrow_to_ptr p sp_r sp_r' (H : eval_path S_r p Mut sp_r sp_r') :
    valid_spath S_r sp_r -> forall sp_l, valid_spath S_l sp_l -> sp_l ~ sp_r ->
      exists sp_l', sp_l' ~ sp_r' /\ eval_path S_l p Mut sp_l sp_l'.
  Proof.
    induction H as [ | | |]. Print eval_path. Check eval_path_ind.
    - intros _ sp_l _ [ | (vp_tail & -> & ->)].
      + exists sp_l. split; auto || constructor.
      + eexists. split. right. exists vp_tail. split; reflexivity. constructor. 
    - intros valid_sp_r sp_l valid_sp_l rel.
      destruct (strict_comparable_spaths q sp_borrow) as [ Hprefix | | | ].
      + apply rel_prefix_sp_borrow in rel; try assumption. rewrite rel.
        assert (same_cons : same_constructor (S_l{{q}}) (S_r{{q}})).
        { apply strict_prefix_sp_borrow_same_constructor. assumption. assumption. }
        rewrite extract_q in same_cons.
        destruct IHeval_path with (sp_l := q +++ [0]).
        * admit. (* Validity argument, should be automatic. *)
        * admit. (* Validity argument. *)
        * auto.
        * destruct H0. exists x. split; try assumption. eapply Eval_Deref_MutBorrow. admit. assumption.
  Admitted.

Lemma eval_place_mut_borrow_to_ptr p sp_r (H : eval_place S_r p Mut sp_r) :
  exists sp_l, sp_l ~ sp_r /\ eval_place S_l p Mut sp_l.
Proof.
  destruct H as (i & ? & H).
  apply eval_path_mut_borrow_to_ptr with (sp_l := (i, [])) in H.
  - destruct H as (sp_l & ? & ?). exists sp_l. split; try assumption.
    exists i. split. (* Need a lemma that says that substitution doesn't affect find_index. *)
    admit. assumption.
  - eapply find_index_valid_spath. eassumption.
  - apply find_index_valid_spath with (b := Var (fst p)). admit. (* same. *)
  - auto.
Admitted.
End MutBorrow_to_Ptr.

(* TODO: simulation for eval_op *)
Lemma eval_rvalue_sim S_l S_r S'_r rv v_r (Hle : le_state_base S_l S_r)
  (Heval_rv : eval_rvalue S_r rv v_r S'_r) :
  exists v_l S'_l, eval_rvalue S_l rv v_l S'_l /\ le_state ((Anon, v_l) :: S'_l) ((Anon, v_r) :: S'_r).
Proof.
  induction Heval_rv.
  - admit. (* TODO: lemma for operands. *)
  - admit. (* Same. *)
  - destruct Hle as [S_r l' sp_loan sp_borrow].
    eapply eval_place_mut_borrow_to_ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow) in H.
    + admit.
    + admit. (* missing validity condition. *)
    + admit. (* same *)
    + assumption.
    + eassumption.
    + eassumption.
Admitted.
