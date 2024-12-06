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

Program Instance ValueLLBC : Value LLBC_val := {
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

Declare Scope llbc_scope.
Delimit Scope llbc_scope with llbc.

(* TODO: move? *)
(* TODO: set every priority to 0? *)
Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level). (* TODO: unused in LLBC.v *)
Reserved Notation "'ptr' ( l )" (at level 0). (* TODO: unused in LLBC.v *)

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level). (* TODO: unused in LLBC.v *)
Reserved Notation "'ptrC' ( l )" (at level 0). (* TODO: unused in LLBC.v *)

(* Notation "'bot'" := LLBC_bot: llbc_scope. *)
Notation "'loan^m' ( l )" := (LLBC_mut_loan l) : llbc_scope.
Notation "'borrow^m' ( l  , v )" := (LLBC_mut_borrow l v) : llbc_scope.

Notation "'botC'" := LLBC_botC: llbc_scope.
Notation "'loanC^m' ( l )" := (LLBC_mut_loanC l) : llbc_scope.
Notation "'borrowC^m' ( l )" := (LLBC_mut_borrowC l) : llbc_scope.

(* Bind Scope llbc_scope with LLBC_val. *)
Open Scope llbc_scope.

Inductive eval_proj (S : LLBC_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_constructor (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : LLBC_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : LLBC_state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof.
  destruct H as (? & ? & ?). eapply eval_path_valid; try eassumption.
  eapply find_binder_valid. eassumption.
Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loan : LLBC_constructor -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Variant is_mut_borrow : LLBC_constructor -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).

Lemma loan_is_not_bot x : is_loan x -> x <> botC. Proof. intros [ ]; discriminate. Qed.

Inductive copy_val : LLBC_val -> LLBC_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (LLBC_int n) (LLBC_int n)
.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> LLBC_state -> (LLBC_val * LLBC_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (LLBC_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Definition get_loan_id c :=
  match c with
  | loanC^m(l) => Some l
  | borrowC^m(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).
Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> LLBC_state -> (LLBC_val * LLBC_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => (LLBC_int m, S')) ->
      (S' |-{op} op_r => (LLBC_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => ((LLBC_int (m + n)), S'')
  | Eval_mut_borrow S p pi l : S |-{p} p =>^{Mut} pi ->
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) -> is_fresh l S ->
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Definition not_in_borrow (S : LLBC_state) p :=
  forall q, prefix q p -> is_mut_borrow (get_constructor (S.[q])) -> q = p.

Inductive reorg : LLBC_state -> LLBC_state -> Prop :=
| Reorg_none S : reorg S S
| Reorg_seq S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    disj p q -> S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    not_contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : LLBC_val * LLBC_state -> LLBC_state -> Prop :=
| Store v S sp (eval_p : (S,, Anon |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  store p (v, S) (S.[sp <- v],, Anon |-> S.[sp])
.

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   LLBC_state -> statement -> nat -> Option (statement_result * LLBC_state) -> Prop
*)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).
Inductive eval_stmt : statement -> statement_result -> LLBC_state -> LLBC_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => rUnit, S
  | Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | Eval_assign S vS' S'' p rv : (S |-{rv} rv => vS') -> store p vS' S'' ->
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | Eval_reorg S0 S1 S2 stmt r : reorg S0 S1 -> S1 |-{stmt} stmt => r, S2 -> S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

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

Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(l) => false
  | _ => true
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
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Definition decide_is_bot v := match v with botC => true | _ => false end.
Definition decide_is_loan v := match v with loanC^m(l) => true | _ => false end.
Definition decide_is_loan_id l v :=
  match v with
  | borrowC^m(l') | loanC^m(l') => l =? l'
  | _ => false
  end.

Fixpoint decide_not_value_contains (P : constructors -> bool) v :=
  negb (P (get_constructor v)) && match v with borrow^m(l, w) => decide_not_value_contains P w | _ => true end.

(*
Lemma decide_value_contains_subval P v w i
  (H : nth_error (subvalues v) i = Some w) (G : decide_not_value_contains P v = true) :
  decide_not_value_contains P w = true.
Proof.
  apply nth_error_In in H.
  destruct v; cbn in H; repeat destruct H as [<- | H] || destruct H.
  cbn. rewrite G. apply orb_true_r.
Qed.
 *)

(* split in two lemmas. *)
Lemma decide_not_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  decide_not_value_contains P v = true -> not_value_contains H v.
Proof.
  intro decide_is_true. induction v.
  - intros p valid_p. apply valid_vpath_no_subvalues in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_subvalues in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_subvalues in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *. intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + cbn in *. rewrite nth_error_cons in * |-. destruct i.
      * cbn in *. apply IHv. eapply andb_prop. eassumption. inversion H0. assumption.
      * rewrite nth_error_nil in * |-. discriminate.
Qed.

Corollary decide_contains_bot v (H : decide_not_value_contains decide_is_bot v = true) :
  not_contains_bot v.
Proof. eapply decide_not_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Corollary decide_contains_loan v (H : decide_not_value_contains decide_is_loan v = true) :
  not_contains_loan v.
Proof.
  eapply decide_not_value_contains_correct; try exact H.
  intros ? G. destruct G. reflexivity.
Qed.

Definition decide_not_state_contains (P : constructors -> bool) (S : LLBC_state) :=
  forallb (fun bv => decide_not_value_contains P (snd bv)) S.

Lemma decide_state_contains_correct H P S (H_implies_P : forall v, H v -> P v = true) :
  decide_not_state_contains P S = true -> not_state_contains H S.
Proof.
  intros G p. unfold sget. intros (? & getval_S & ?). rewrite getval_S.
  unfold decide_not_state_contains in G. rewrite forallb_forall in G.
  destruct (nth_error S (fst p)) as [bv | ] eqn:?; simplify_eq getval_S. intros <-.
  assert (HIn : In bv S) by (eapply nth_error_In; eassumption).
  specialize (G bv HIn).
  apply decide_not_value_contains_correct with (H := H) in G; [ | assumption]. eauto.
Qed.

Corollary decide_not_is_fresh S l (H : decide_not_state_contains (decide_is_loan_id l) S = true) :
  is_fresh l S.
Proof.
  eapply decide_state_contains_correct; try eassumption.
  intros c G. destruct c; inversion G; apply Nat.eqb_refl.
Qed.

(* TODO: move in PathToSubtree.v? *)
Lemma prefix_nil p i : prefix p (i, []) -> p = (i, []).
Proof.
  destruct p as (j & q). intros (r & H). unfold app_spath_vpath in H. cbn in H.
  apply pair_equal_spec in H. destruct H as (-> & H).
  apply app_eq_nil in H. destruct H as (-> & _). reflexivity.
Qed.
  
Lemma safe_main :
  exists end_state, eval_stmt main rUnit init_state end_state /\
    exists pi, eval_place end_state Imm ((a, []) : place) pi /\ end_state.[pi] = LLBC_int 58.
Proof.
  eexists. split. {
    eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || econstructor.
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || econstructor.
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_mut_borrow with (l := 0).
        + eexists. split; reflexivity || econstructor.
        + cbn. apply decide_contains_loan. reflexivity.
        + cbn. apply decide_contains_bot. reflexivity.
        + cbn. apply decide_not_is_fresh. reflexivity.
      - eexists. split; reflexivity || econstructor.
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_mut_borrow with (pi := (2, [0])) (l := 1).
        + eexists. split; reflexivity || (repeat econstructor || discriminate). 
        + cbn. apply decide_contains_loan. reflexivity.
        + cbn. apply decide_contains_bot. reflexivity.
        + cbn. apply decide_not_is_fresh. reflexivity.
      - eexists. split; reflexivity || econstructor.
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_mut_borrow with (pi := (1, [])) (l := 2).
        + eexists. split; reflexivity || (repeat econstructor || discriminate). 
        + cbn. apply decide_contains_loan. reflexivity.
        + cbn. apply decide_contains_bot. reflexivity.
        + cbn. apply decide_not_is_fresh. reflexivity.
      - eexists. split; reflexivity || econstructor.
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_seq_unit.
    { eapply Eval_assign; [ | constructor].
      - apply Eval_just, Eval_IntConst.
      - eexists. split; reflexivity || (repeat econstructor || discriminate).
      - cbn. apply decide_contains_outer_loan_correct. reflexivity.
    }
    cbn. eapply Eval_reorg.
    { eapply Reorg_seq.
      - apply Reorg_end_borrow_m with (p := (8, [0])) (q := (3, [])) (l := 1).
        + left. discriminate.
        + reflexivity.
        + reflexivity.
        + apply decide_contains_loan. reflexivity.
        + intros ? ->%prefix_nil. reflexivity.
      - cbn. apply Reorg_end_borrow_m with (l := 0) (p := (0, [])) (q := (8, [])).
        + left. discriminate.
        + reflexivity.
        + reflexivity.
        + apply decide_contains_loan. reflexivity.
        + intros ? ->%prefix_nil. reflexivity.
    }
    cbn. apply Eval_nop.
  }
  eexists. split.
  - eexists. split; reflexivity || constructor.
  - cbn. reflexivity.
Qed.
