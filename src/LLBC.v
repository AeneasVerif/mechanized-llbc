Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Import ListNotations.
Require Import PeanoNat.

Variant LLBC_zero :=
| LLBC_bot
| LLBC_int (n : nat) (* TODO: use Aeneas integer types? *)
| LLBC_loan (l : loan_id).

Variant LLBC_unit :=
| LLBC_borrow (l : loan_id).

Variant LLBC_bin := .

Notation LLBC_val := (value LLBC_zero LLBC_unit LLBC_bin).

Variant LLBC_binder :=
| Var (v : var)
(* | Box (l : nat) *)
| Anon.

Program Global Instance EqDec_binder : EqDec LLBC_binder.
Next Obligation. repeat decide equality. Qed.

Notation LLBC_state := (state LLBC_zero LLBC_unit LLBC_bin LLBC_binder).

Declare Scope llbc_scope.
Delimit Scope llbc_scope with llbc.

(* TODO: move these reserved notations in a separate files, maybe something like semantics-base. *)
   
Reserved Notation "'bot'" (at level 50).
Reserved Notation "'loan^m' l" (at level 50).
Reserved Notation "'borrow^m' l v" (at level 50).
Reserved Notation "'loc' l v" (at level 50).
Reserved Notation "'ptr' l" (at level 50).

Notation "'bot'" := (@vZero LLBC_zero LLBC_unit LLBC_bin LLBC_bot): llbc_scope.
Notation "'loan^m' l" := (@vZero LLBC_zero LLBC_unit LLBC_bin (LLBC_loan l))
  : llbc_scope.
Notation "'borrow^m' l v" := (@vUnit LLBC_zero LLBC_unit LLBC_bin (LLBC_borrow l) v)
  : llbc_scope.

(* Bind Scope llbc_scope with LLBC_val. *)
Open Scope llbc_scope.

Global Instance Inhabited_LLBC_val : Inhabited LLBC_val := { default := bot }.

Inductive eval_path : LLBC_state -> path -> permission -> spath -> spath -> Prop :=
| Eval_nil s perm pi : eval_path s [] perm pi pi
| Eval_deref_borrow_mut s p q l v r
    (extract_q : s{{q}} = vUnit (LLBC_borrow l) v)
    (eval_q : eval_path s p Mut (q +++ [0]) r) :
    eval_path s (Deref :: p) Mut q r.

Lemma eval_path_valid (s : LLBC_state) p perm q r (valid_q : valid_spath s q) (eval_q_r : eval_path s p perm q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. rewrite valid_spath_app. split; try assumption. rewrite extract_q.
    constructor. constructor.
Qed.

Definition eval_place (s : LLBC_state) (p : place) (perm : permission) (r : spath) :=
  exists i, find_index s (Var (fst p)) = Some i /\ eval_path s (snd p) perm (i, []) r.

Lemma eval_place_valid s p perm r (H : eval_place s p perm r) : valid_spath s r.
Proof.
  destruct H as (? & ? & ?). eapply eval_path_valid; try eassumption.
  eapply find_index_valid_spath. eassumption.
Qed.

(* Setting up the definitions for judgements like "loan \notin v" or
   "l is free". *)
Definition state_contains (f : LLBC_val -> bool) (s : LLBC_state) :=
  exists v, valid_spath s v /\ is_true (f (s{{v}})).

Definition value_contains (f : LLBC_val -> bool) (s : LLBC_val) :=
  exists v, valid_vpath s v /\ is_true (f (s{{v}})).

Definition is_loan (v : LLBC_val) := match v with
| vZero (LLBC_loan l) => true
| _ => false
end.
Definition contains_loan := value_contains is_loan.

Definition is_loan_id (l : loan_id) (v : LLBC_val)  := match v with
| vZero (LLBC_loan l') => l' =? l
| vUnit (LLBC_borrow l') w => l' =? l
| _ => false
end.
(* TODO: rename "is_fresh" *)
Definition is_free l s := ~state_contains (is_loan_id l) s.

Definition is_borrow (v : LLBC_val) := match v with
| vUnit (LLBC_borrow l) w => true
| _ => false
end.

Definition not_in_borrow (s : LLBC_state) p :=
  forall q, prefix q p /\ is_true (is_borrow (s{{q}})) -> q = p.

Inductive copy_val : LLBC_val -> LLBC_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (vZero (LLBC_int n)) (vZero (LLBC_int n)).

Variant eval_op : LLBC_state -> operand -> LLBC_val -> LLBC_state -> Prop :=
| Eval_IntConst s n : eval_op s (IntConst n) (vZero (LLBC_int n)) s
(* TODO: place should be read in Imm mode. *)
| Eval_copy s (p : place) q v : eval_place s p Mut q -> copy_val (s{{q}}) v ->
    eval_op s (Copy p) v s
(* TODO: s{{q}} cannot contain bot *)
| Eval_move s (p : place) q : eval_place s p Mov q -> ~contains_loan (s{{q}}) ->
    eval_op s (Move p) (s{{q}}) (s{{q <- bot}}).

Variant eval_rvalue : LLBC_state -> rvalue -> LLBC_val -> LLBC_state -> Prop :=
| Eval_just s op v s' : eval_op s op v s' -> eval_rvalue s (Just op) v s'
(* For the moment, the only operation is the natural sum. *)
| Eval_bin_op s s' s'' op_l op_r m n : eval_op s op_l (vZero (LLBC_int m)) s' ->
   eval_op s' op_r (vZero (LLBC_int n)) s'' ->
   eval_rvalue s (BinOp op_l op_r) (vZero (LLBC_int (m + n))) s''
| Eval_borrow_m s p q l : eval_place s p Mut q -> ~contains_loan (s{{q}}) -> is_free l s ->
    eval_rvalue s (&mut p) (vUnit (LLBC_borrow l) (s{{q}})) (s{{q <- vZero (LLBC_loan l)}}).

Inductive reorg : LLBC_state -> LLBC_state -> Prop :=
| Reorg_refl s : reorg s s
| Reorg_trans s0 s1 s2 : reorg s0 s1 -> reorg s1 s2 -> reorg s0 s2
| Reorg_end_borrow_m s (p q : spath) l v : valid_spath s p -> valid_spath s q ->
    s{{p}} = (vZero (LLBC_loan l)) -> s{{q}} = (vUnit (LLBC_borrow l) v) ->
    ~contains_loan v -> not_in_borrow s q ->
    reorg s (s{{p <- v}}{{q <- bot}}).

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   LLBC_state -> statement -> nat -> Option (statement_result * LLBC_state) -> Prop
*)
Inductive eval_stmt : LLBC_state -> statement -> statement_result -> LLBC_state -> Prop :=
| Eval_nop s : eval_stmt s Nop rUnit s
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : eval_stmt S0 stmt_l rUnit S1)
    (eval_stmt_r : eval_stmt S1 stmt_r r S2) : eval_stmt S0 (stmt_l ;; stmt_r) r S2
| Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : eval_stmt S0 stmt_l rPanic S1) :
    eval_stmt S0 (stmt_l ;; stmt_r) rPanic S1.

(* Can we actually relate the inductive properties to computable functions, in order to help
   proving the evaluation of actual LLBC programs. *)
Fixpoint eval_path_fun (s : LLBC_state) (p : path) perm (q : spath) : option spath :=
match p with
| [] => Some q
| Deref :: p' => match s{{q}}, perm with
  | vUnit (LLBC_borrow l) v, Mut => eval_path_fun s p' Mut (q +++ [0])
  | _, _ => None
  end
| _ => None
end.

Lemma eval_path_fun_is_eval_path s p perm r : forall q,
  eval_path_fun s p perm q = Some r -> eval_path s p perm q r.
Proof.
  induction p as [ | proj]; intros q H.
  - injection H. intros <-. constructor.
  - destruct proj.
    + simpl in H. destruct (extract_state Inhabited_LLBC_val s q) eqn:EQN; try easy. destruct l.
      destruct perm; try easy. econstructor. exact EQN. auto.
    + inversion H.
Qed.