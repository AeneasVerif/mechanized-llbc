Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Import ListNotations.
Require Import PeanoNat.

Inductive LLBC_val :=
| LLBC_bot
| LLBC_int (n : nat) (* TODO: use Aeneas integer types? *)
| LLBC_mut_loan (l : loan_id)
| LLBC_mut_borrow (l : loan_id) (v : LLBC_val)
(*
| LLBC_shr_loan (l : loan_id) (v : LLBC_val)
| LLBC_shr_borrow (l : loan_id)
 *)
(* | LLBC_pair (v0 : LLBC_val) (v1 : LLBC_val) *)
.

Variant LLBC_binder :=
| Var (v : var)
(* | Box (l : nat) *)
| Anon.

Program Global Instance EqDec_binder : EqDec LLBC_binder.
Next Obligation. repeat decide equality. Defined.

Variant LLBC_constructor :=
| LLBC_botC
| LLBC_intC (n : nat)
| LLBC_mut_loanC (l : loan_id)
| LLBC_mut_borrowC (l : loan_id)
.

Definition LLBC_arity c := match c with
| LLBC_botC => 0
| LLBC_intC _ => 0
| LLBC_mut_loanC _ => 0
| LLBC_mut_borrowC _ => 1
end.

Definition LLBC_get_constructor v := match v with
| LLBC_bot => LLBC_botC
| LLBC_int n => LLBC_intC n
| LLBC_mut_loan l => LLBC_mut_loanC l
| LLBC_mut_borrow l _ => LLBC_mut_borrowC l
end.

Definition LLBC_subvalues v := match v with
| LLBC_bot => []
| LLBC_int _ => []
| LLBC_mut_loan _ => []
| LLBC_mut_borrow _ v => [v]
end.

Definition LLBC_fold c vs := match c, vs with
| LLBC_intC n, [] => LLBC_int n
| LLBC_mut_loanC l, [] => LLBC_mut_loan l
| LLBC_mut_borrowC l, [v] => LLBC_mut_borrow l v
| _, _ => LLBC_bot
end.

Fixpoint LLBC_height v := match v with
| LLBC_bot => 0
| LLBC_int _ => 0
| LLBC_mut_loan _ => 0
| LLBC_mut_borrow _ v => 1 + LLBC_height v
end.

Program Instance ValueHLPL : Value LLBC_val := {
  constructors := LLBC_constructor;
  arity := LLBC_arity;
  get_constructor := LLBC_get_constructor;
  subvalues := LLBC_subvalues;
  fold_value := LLBC_fold;
  height := LLBC_height;
  bot := LLBC_bot;
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
Next Obligation.
  apply nth_error_In in H.
  destruct v; cbn in *; try destruct H as [-> | ]; try contradiction; constructor.
Qed.

Definition LLBC_state := state LLBC_binder LLBC_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: move in lang.v *)
Reserved Notation "'bot'" (at level 0).
Reserved Notation "'loan^m' l" (at level 50).
Reserved Notation "'borrow^m' ( l , v )" (at level 50, l at next level, v at next level).

Notation "'bot'" := LLBC_bot: hlpl_plus_scope.
Notation "'loan^m' l" := (LLBC_mut_loan l) : hlpl_plus_scope.
Notation "'borrow^m' ( l  , v )" := (LLBC_mut_borrow l v) : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with LLBC_val. *)
Open Scope hlpl_plus_scope.

Inductive eval_proj (S : LLBC_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l v
    (imm_or_mut : perm <> Mov)
    (get_q : S.[q] = borrow^m(l, v)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : LLBC_state) perm : path -> spath -> spath -> Prop :=
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
Qed.

Lemma eval_path_valid (s : LLBC_state) P perm q r
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
Definition state_contains (H : LLBC_val -> Prop) (S : LLBC_state) :=
  exists p, valid_spath S p /\ H (S.[p]).

Definition value_contains (H : LLBC_val -> Prop) (v : LLBC_val) :=
  exists p, valid_vpath v p /\ H (v.[[p]]).

Definition is_loan (v : LLBC_val) :=
  exists l, v = loan^m(l).
Definition contains_loan := value_contains is_loan.

Definition is_mut_borrow (v : LLBC_val) := exists l w, v = borrow^m(l, w).

Definition contains_outer_loan v :=
  exists l p, v.[[p]] = loan^m(l) /\ (forall q, vprefix q p -> ~is_mut_borrow (v.[[q]])).

Variant is_loan_id (l : loan_id) : LLBC_val -> Prop  :=
| Is_loan_id_loan : is_loan_id l (loan^m(l))
| Is_loan_id_borrow w : is_loan_id l (borrow^m(l, w))
.

Definition is_fresh l S := ~state_contains (is_loan_id l) S.

Definition is_borrow (v : LLBC_val) := exists l w, v = borrow^m(l, w).

Definition not_in_borrow (S : LLBC_state) p :=
  forall q, prefix q p /\ is_borrow (S.[q]) -> q = p.

Definition contains_bot (v : LLBC_val) :=
  value_contains (fun w => w = bot) v.

Inductive copy_val : LLBC_val -> LLBC_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (LLBC_int n) (LLBC_int n)
.

Variant eval_op (S : LLBC_state) : operand -> LLBC_val -> LLBC_state -> Prop :=
| Eval_IntConst n : eval_op S (IntConst n) (LLBC_int n) S
| Eval_copy (p : place) pi v : eval_place S Imm p pi -> copy_val (S.[pi]) v ->
    eval_op S (Copy p) v S
| Eval_move (p : place) pi : eval_place S Mov p pi -> ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
  eval_op S (Move p) (S.[pi]) (S.[pi <- bot]).

Variant eval_rvalue (S : LLBC_state) : rvalue -> LLBC_val -> LLBC_state -> Prop :=
| Eval_just op v S' : eval_op S op v S' -> eval_rvalue S (Just op) v S'
(* For the moment, the only operation is the natural sum. *)
| Eval_bin_op S' S'' op_l op_r m n : eval_op S op_l (LLBC_int m) S' ->
   eval_op S' op_r (LLBC_int n) S'' ->
   eval_rvalue S (BinOp op_l op_r) (LLBC_int (m + n)) S''
| Eval_mut_borrow p pi l : eval_place S Mut p pi ->
    ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) -> is_fresh l S ->
    eval_rvalue S (&mut p) (borrow^m(l, S.[pi])) (S.[pi <- loan^m(l)]).

Inductive reorg : LLBC_state -> LLBC_state -> Prop :=
| Reorg_none S : reorg S S
| Reorg_seq S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    disj p q -> S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    ~contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   LLBC_state -> statement -> nat -> Option (statement_result * LLBC_state) -> Prop
*)
Inductive eval_stmt : LLBC_state -> statement -> statement_result -> LLBC_state -> Prop :=
| Eval_nop S : eval_stmt S Nop rUnit S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : eval_stmt S0 stmt_l rUnit S1)
    (eval_stmt_r : eval_stmt S1 stmt_r r S2) : eval_stmt S0 (stmt_l ;; stmt_r) r S2
| Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : eval_stmt S0 stmt_l rPanic S1) :
    eval_stmt S0 (stmt_l ;; stmt_r) rPanic S1
| Eval_assign S S' p rv v sp : eval_rvalue S rv v S' -> eval_place S' Mut p sp ->
    ~contains_outer_loan (S'.[sp]) ->
    eval_stmt S (ASSIGN p <- rv) rUnit ((Anon, S'.[sp]) :: S'.[sp <- v])
| Eval_reorg S0 S1 S2 stmt r : reorg S0 S1 -> eval_stmt S1 stmt r S2 -> eval_stmt S0 stmt r S2.

Require Import Bool.
Local Open Scope option_monad_scope.
(* Can we prove that the following proram terminates? *)
(*
fn main() {
    let mut a = 1983;
    let mut b = 1986;
    let mut c = &mut a;
    let d = &mut *c;
    c = &mut b;
    *d = 58;
}
 *)
Definition a : var := 0.
Definition b : var := 1.
Definition c : var := 2.
Definition d : var := 3.
Definition main : statement :=
  ASSIGN (a, []) <- Just (IntConst 1983) ;;
  ASSIGN (b, []) <- Just (IntConst 1986) ;;
  ASSIGN (c, []) <- &mut (a, []) ;;
  ASSIGN (d, []) <- &mut (c, [Deref]) ;;
  ASSIGN (c, []) <- &mut (b, []) ;;
  ASSIGN (d, [Deref]) <- Just (IntConst 58) ;;
  Nop
.
(* Important note: the line `c = &mut b` overwrites a loan, but as it is an outer loan, it doesn't
 * cause any problem. This is a check that the overwriting of outer loans is supported. *)
(* Also, the last `Nop` statement was added so that we could perform reorganization operations
 * before the end, and but back the value 58 in the variable a. *)

Notation init_state := [(Var a, bot); (Var b, bot); (Var c, bot); (Var d, bot)].

Definition decide_contains_outer_loan v :=
  match v with
  | loan^m(l) => true
  | _ => false
  end.

(* TODO: move in PathToSubtree.v *)
Lemma valid_vpath_no_subvalues v p (valid_p : valid_vpath v p) (H : subvalues v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

(* For the moment, the type of values is so restricted that a value contains an outer loan if and
 * only if it is a mutable loan. *)
Lemma decide_contains_outer_loan_correct v :
  contains_outer_loan v -> is_true (decide_contains_outer_loan v).
Proof.
  intros (l & p & H & G).
  assert (valid_p : valid_vpath v p). { apply get_not_bot_valid_vpath. rewrite H. discriminate. }
  destruct v.
  - rewrite (valid_vpath_no_subvalues bot p) in H by auto. inversion H.
  - erewrite (valid_vpath_no_subvalues _ p) in H by eauto. inversion H.
  - auto.
  - exfalso. apply (G []).
    + exists p. reflexivity.
    + repeat eexists.
Qed.

Definition decide_is_bot v := match v with bot => true | _ => false end.
Definition decide_is_loan v := match v with loan^m(l) => true | _ => false end.
Definition decide_is_loan_id l v :=
  match v with
  | borrow^m(l', _) | loan^m(l') => l =? l'
  | _ => false
  end.

Fixpoint decide_value_contains (P : LLBC_val -> bool) v :=
  P v || match v with borrow^m(l, w) => decide_value_contains P w | _ => false end.

Lemma decide_value_contains_subval P v w i
  (H : nth_error (subvalues v) i = Some w) (G : decide_value_contains P w = true) :
  decide_value_contains P v = true.
Proof.
  apply nth_error_In in H.
  destruct v; cbn in H; repeat destruct H as [<- | H] || destruct H.
  cbn. rewrite G. apply orb_true_r.
Qed.

(* split in two lemmas. *)
Lemma decide_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  value_contains H v -> decide_value_contains P v = true.
Proof.
  intros (p & valid_p & H_v). induction valid_p as [ | ? ? ? ? G].
  - apply H_implies_P in H_v. destruct v; cbn in *; rewrite H_v; reflexivity.
  - apply (decide_value_contains_subval _ _ _ _ G). cbn in *. rewrite G in H_v. auto.
Qed.

Corollary decide_contains_bot v (H : contains_bot v) :
  decide_value_contains decide_is_bot v = true.
Proof. eapply decide_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Corollary decide_contains_loan v (H : contains_loan v) :
  decide_value_contains decide_is_loan v = true.
Proof. eapply decide_value_contains_correct; try exact H. intros ? (? & ->). reflexivity. Qed.

Definition decide_state_contains (P : LLBC_val -> bool) (S : LLBC_state) :=
  existsb (fun bv => decide_value_contains P (snd bv)) S.

Lemma decide_state_contains_correct H P S (H_implies_P : forall v, H v -> P v = true) :
  state_contains H S -> decide_state_contains P S = true.
Proof.
  intros (p & (v & G & valid_p_v) & ?). apply existsb_exists.
  unfold sget in *. destruct (nth_error S (fst p)) as [bv | ] eqn:EQN; inversion G.
  exists bv. split.
  - eapply nth_error_In. exact EQN.
  - apply (decide_value_contains_correct _ _ _ H_implies_P). exists (snd p). subst. auto.
Qed.

Corollary decide_not_is_fresh S l (H : state_contains (is_loan_id l) S) :
  decide_state_contains (decide_is_loan_id l) S = true.
Proof.
  eapply decide_state_contains_correct; try eassumption.
  intros ? [ | ]; apply Nat.eqb_refl.
Qed.

(* TODO: move in PathToSubtree.v? *)
Lemma prefix_nil p i : prefix p (i, []) -> p = (i, []).
Proof.
  destruct p as (j & q). intros (r & H). unfold app_spath_vpath in H. cbn in H.
  apply pair_equal_spec in H. destruct H as (-> & H).
  apply app_eq_nil in H. destruct H as (-> & _). reflexivity.
Qed.
  
Lemma safe_main :
  exists end_state, eval_stmt init_state main rUnit end_state /\
    exists pi, eval_place end_state Imm ((a, []) : place) pi /\ end_state.[pi] = LLBC_int 58.
Proof.
  eexists. split. {
    eapply Eval_seq_unit.
    { apply Eval_assign.
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || econstructor.
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_seq_unit.
    { apply Eval_assign.
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || econstructor.
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_seq_unit.
    { apply Eval_assign.
      - apply Eval_mut_borrow with (l := 0).
        + eexists. split; reflexivity || econstructor.
        + cbn. intro H. apply decide_contains_loan in H. discriminate H.
        + cbn. intro H. apply decide_contains_bot in H. discriminate H.
        + cbn. intro H. apply decide_not_is_fresh in H. discriminate H. 
      - eexists. split; reflexivity || econstructor.
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_seq_unit.
    { apply Eval_assign.
      - apply Eval_mut_borrow with (pi := (5, [0])) (l := 1).
        + eexists. split; reflexivity || (repeat econstructor || discriminate). 
        + cbn. intro H. apply decide_contains_loan in H. discriminate H.
        + cbn. intro H. apply decide_contains_bot in H. discriminate H.
        + cbn. intro H. apply decide_not_is_fresh in H. discriminate H.
      - eexists. split; reflexivity || econstructor.
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_seq_unit.
    { apply Eval_assign.
      - apply Eval_mut_borrow with (pi := (5, [])) (l := 2).
        + eexists. split; reflexivity || (repeat econstructor || discriminate). 
        + cbn. intro H. apply decide_contains_loan in H. discriminate H.
        + cbn. intro H. apply decide_contains_bot in H. discriminate H.
        + cbn. intro H. apply decide_not_is_fresh in H. discriminate H.
      - eexists. split; reflexivity || econstructor.
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign.
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || (repeat econstructor || discriminate).
      - cbn. intro H. apply decide_contains_outer_loan_correct in H. inversion H.
    }
    cbn. eapply Eval_reorg.
    { eapply Reorg_seq.
      - apply Reorg_end_borrow_m with (p := (1, [0])) (q := (9, [])) (l := 1).
        + left. discriminate.
        + reflexivity.
        + reflexivity.
        + intros (p & valid_p & is_loan).
          apply valid_vpath_no_subvalues in valid_p; try reflexivity. subst.
          destruct is_loan as (? & H). inversion H.
        + intros q (? & _). apply prefix_nil. assumption.
      - cbn. apply Reorg_end_borrow_m with (l := 0) (p := (6, [])) (q := (1, [])).
        + left. discriminate.
        + reflexivity.
        + reflexivity.
        + intros (p & valid_p & is_loan).
          apply valid_vpath_no_subvalues in valid_p; try reflexivity. subst.
          destruct is_loan as (? & H). inversion H.
        + intros q (? & _). apply prefix_nil. assumption.
    }
    cbn. apply Eval_nop.
  }
  eexists. split.
  - eexists. split; reflexivity || constructor.
  - cbn. reflexivity.
Qed.
