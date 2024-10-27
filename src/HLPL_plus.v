Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Import ListNotations.

(* TODO: move this in a separate file. *)
Create HintDb spath.
(* Automatically solving a comparison C p q using the hypotheses. *)
Lemma not_disj_strict_prefix p q : disj p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. eapply not_prefix_disj; eassumption. Qed.
Hint Resolve not_disj_strict_prefix : spath.
Hint Immediate symmetric_disj : spath.

Lemma not_prefix_implies_not_strict_prefix p q : ~prefix p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. auto. Qed.
Hint Resolve not_prefix_implies_not_strict_prefix : spath.

Lemma neq_implies_not_prefix p q : ~prefix p q -> p <> q.
Proof. intros H <-. apply H. reflexivity. Qed.
Hint Resolve neq_implies_not_prefix : spath.

Lemma disj_if_left_disj_prefix p q r : disj p q -> disj p (q +++ r).
Proof.
  intros [ | (? & (x & p' & q' & H))].
  - left. assumption.
  - right. split; [assumption | ]. exists x, p', (q' ++ r).
    decompose [ex and] H. repeat eexists; try eassumption. cbn.
    rewrite app_comm_cons, app_assoc. apply<- app_inv_tail_iff. assumption.
Qed.
Hint Resolve disj_if_left_disj_prefix : spath.

Corollary disj_if_right_disj_prefix p q r : disj p q -> disj (p +++ r) q.
Proof. intro. symmetry. apply disj_if_left_disj_prefix. symmetry. assumption. Qed.
Hint Resolve disj_if_right_disj_prefix : spath.

Hint Resolve<- strict_prefix_app_last.

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

Fixpoint HLPL_plus_height v := match v with
| HLPL_plus_bot => 0
| HLPL_plus_int _ => 0
| HLPL_plus_mut_loan _ => 0
| HLPL_plus_mut_borrow _ v => 1 + HLPL_plus_height v
| HLPL_plus_loc _ v =>  1 + HLPL_plus_height v
| HLPL_plus_ptr _ => 0
end.

Program Instance ValueHLPL : Value HLPL_plus_val := {
  constructors := HLPL_plus_constructor;
  arity := HLPL_plus_arity;
  get_constructor := HLPL_plus_get_constructor;
  subvalues := HLPL_plus_subvalues;
  fold_value := HLPL_plus_fold;
  height := HLPL_plus_height;
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
Next Obligation.
  apply nth_error_In in H.
  destruct v; cbn in *; try destruct H as [-> | ]; try contradiction; constructor.
Qed.

Definition HLPL_plus_state := state HLPL_plus_binder HLPL_plus_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: move in lang.v *)
(* TODO: set every priority to 0? *)
(* Reserved Notation "'bot'" (at level 0). *)
Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level).
Reserved Notation "'ptrC' ( l )" (at level 0).

(* Notation "'bot'" := HLPL_plus_bot: hlpl_plus_scope. *)
Notation "'loan^m' ( l )" := (HLPL_plus_mut_loan l) : hlpl_plus_scope.
Notation "'borrow^m' ( l  , v )" := (HLPL_plus_mut_borrow l v) : hlpl_plus_scope.
Notation "'loc' ( l , v )" := (HLPL_plus_loc l v) : hlpl_plus_scope.
Notation "'ptr' ( l )" := (HLPL_plus_ptr l) : hlpl_plus_scope.

Notation "'botC'" := HLPL_plus_botC: hlpl_plus_scope.
Notation "'loanC^m' ( l )" := (HLPL_plus_mut_loanC l) : hlpl_plus_scope.
Notation "'borrowC^m' ( l )" := (HLPL_plus_mut_borrowC l) : hlpl_plus_scope.
Notation "'locC' ( l )" := (HLPL_plus_locC l) : hlpl_plus_scope.
Notation "'ptrC' ( l )" := (HLPL_plus_ptrC l) : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with HLPL_plus_val. *)
Open Scope hlpl_plus_scope.

Inductive eval_proj (S : HLPL_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_constructor (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| Eval_Deref_Ptr_Locs q q' l
    (Hperm : perm <> Mov)
    (get_q : get_constructor (S.[q]) = ptrC(l)) (get_q' : get_constructor (S.[q']) = locC(l)) :
    eval_proj S perm Deref q (q' +++ [0])
(* Coresponds to R-Loc and W-Loc in the article. *)
| Eval_Loc proj q q' l
    (Hperm : perm = Imm)
    (get_q : get_constructor (S.[q]) = locC(l))
    (eval_proj_rec : eval_proj S perm proj (q +++ [0]) q') : eval_proj S perm proj q q'
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : HLPL_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Notation eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

(* TODO: replace the notation by a definition, with Hint Unfold. *)
Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
  - apply valid_spath_app. destruct (S.[q']) eqn:EQN; try discriminate. split.
    + apply get_not_bot_valid_spath. rewrite EQN. discriminate.
    + eapply valid_cons; reflexivity || apply valid_nil.
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

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof.
  destruct H as (? & ? & ?). eapply eval_path_valid; try eassumption.
  eapply find_binder_valid. eassumption.
Qed.


(* Setting up the definitions for judgements like "loan \notin v" or
   "l is fresh". *)
Definition not_state_contains (P : HLPL_plus_constructor -> Prop) (S : HLPL_plus_state) :=
  forall p, valid_spath S p -> ~P (get_constructor (S.[p])).

(* TODO: move *)
Definition not_value_contains (P : HLPL_plus_constructor -> Prop) (v : HLPL_plus_val) :=
  forall p, valid_vpath v p -> ~P (get_constructor (v.[[p]])).

Lemma not_value_contains_not_prefix P (S : HLPL_plus_state) p q
  (Hnot_contains : not_value_contains P (S.[p])) (HP : P (get_constructor (S.[q]))) (Hvalid : valid_spath S q) :
  ~prefix p q.
Proof.
  intros (r & <-). apply valid_spath_app in Hvalid. apply Hnot_contains with (p := r); [easy | ].
  rewrite<- sget_app. assumption.
Qed.

Lemma not_value_contains_vset P v w p : not_value_contains P v -> not_value_contains P w ->
  not_value_contains P (v.[[p <- w]]).
Proof.
  intros H G q valid_q. destruct (decidable_vprefix p q) as [(? & <-) | ].
  - apply valid_vpath_app in valid_q. destruct valid_q as (?%vset_same_valid_rev & validity_w).
    rewrite vget_vset_equal in validity_w by assumption.
    rewrite vget_vset_prefix_right by assumption. apply G. assumption.
  - rewrite constructor_vset_vget_not_prefix by assumption. apply H.
    eapply vset_not_prefix_valid_rev; [ | eassumption].
    intros ?%vstrict_prefix_is_vprefix. auto.
Qed.
Hint Resolve not_value_contains_vset : spath.

Lemma not_value_contains_sset P (S : HLPL_plus_state) v p q
  (not_in_Sp : not_value_contains P (S.[p]))
  (not_in_v : not_value_contains P v)
  (valid_p : valid_spath (S.[q <- v]) p) :
  not_value_contains P (S.[q <- v].[p]).
Proof.
  intros r valid_r. rewrite<- sget_app.
  assert (valid_pr : valid_spath (S.[q <- v]) (p +++ r)).
  { apply valid_spath_app. split; assumption. }
  destruct (decidable_prefix q (p +++ r)) as [(? & eq) | ].
  - rewrite <-eq in *. rewrite valid_spath_app in valid_pr.
    destruct valid_pr as (valid_q & valid_v_r).
    apply sset_not_prefix_valid in valid_q; [ | apply strict_prefix_irrefl].
    rewrite sset_sget_equal in valid_v_r by assumption.
    rewrite sset_sget_prefix_right by assumption. apply not_in_v. exact valid_v_r.
  - rewrite constructor_sset_sget_not_prefix by assumption. rewrite sget_app. apply not_in_Sp.
    apply sset_not_prefix_valid in valid_pr; [ | auto with spath].
    apply valid_spath_app in valid_pr as (_ & ?). assumption.
Qed.
Hint Resolve not_value_contains_sset : spath.

Lemma not_value_contains_sset_disj P (S : HLPL_plus_state) v p q
  (not_in_Sp : not_value_contains P (S.[p]))
  (Hdisj : disj q p) :
  not_value_contains P (S.[q <- v].[p]).
Proof.
  intros r valid_r. rewrite<- sget_app. rewrite sset_sget_disj by auto with spath.
  rewrite sget_app. apply not_in_Sp.
  rewrite sset_sget_disj in valid_r; assumption.
Qed.
Hint Resolve not_value_contains_sset_disj : spath.

Lemma not_value_contains_zeroary P v :
  subvalues v = [] -> ~P (get_constructor v) -> not_value_contains P v.
Proof.
  intros H ? p valid_p. destruct valid_p; [assumption | ].
  rewrite H, nth_error_nil in * |-. discriminate.
Qed.
Hint Extern 0 (not_value_contains _ _) =>
  simple apply not_value_contains_zeroary; [reflexivity | easy] : spath.

Require Import OptionMonad.
Lemma not_value_contains_unary P v w :
  subvalues v = [w] -> ~P (get_constructor v) -> not_value_contains P w -> not_value_contains P v.
Proof.
  intros H ? ? p valid_p. destruct valid_p; [assumption | ].
  rewrite H, nth_error_cons in * |-. destruct i; [ | rewrite nth_error_nil in * |-; discriminate].
  rewrite vget_cons, H. simplify_option.
Qed.
Hint Extern 0 (not_value_contains _ _) =>
  simple eapply not_value_contains_unary; [reflexivity | easy | ] : spath.

Variant is_loan : HLPL_plus_constructor -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Constructors is_loan : spath.

(* TODO: delete *)
Goal is_loan (get_constructor (loan^m(0))).
Proof. cbn. auto with spath. Qed.

Variant is_loc : HLPL_plus_constructor -> Prop :=
| IsLoc_Loc l : is_loc (locC(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.

(*
Variant is_mut_borrow : HLPL_plus_constructor -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
 *)
(* Hint Constructors is_mut_borrow : spath. *)

Definition not_contains_outer_loan v :=
  forall l p, v.[[p]] = loan^m(l) -> exists q l w, vprefix q p /\ v.[[q]] = borrow^m(l, w).

Definition not_contains_outer_loc v :=
  forall p, is_loc (get_constructor (v.[[p]])) -> exists q l w, vprefix q p /\ v.[[q]] = borrow^m(l, w).

Variant is_loan_id (l : loan_id) : HLPL_plus_constructor -> Prop  :=
| Is_loan_id_loan : is_loan_id l (loanC^m(l))
| Is_loan_id_borrow : is_loan_id l (borrowC^m(l))
| Is_loan_id_ptr : is_loan_id l (ptrC(l))
| Is_loan_id_loc : is_loan_id l (locC(l)).
(* Hint Constructors is_loan_id : spath. *)
Definition is_fresh l S := not_state_contains (is_loan_id l) S.
Hint Unfold is_fresh : spath.

Definition is_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition not_in_borrow (S : HLPL_plus_state) p :=
  forall q, prefix q p -> is_borrow (S.[q]) -> q = p.

Definition not_contains_bot (v : HLPL_plus_val) :=
  not_value_contains (fun c => c = botC) v.
Hint Unfold not_contains_bot : spath.

Inductive copy_val : HLPL_plus_val -> HLPL_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_plus_int n) (HLPL_plus_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

(* TODO: rename `eval_operand` *)
Local Reserved Notation "S  |-{op}  op  =>  v , S'" (at level 60).

Variant eval_op : operand -> HLPL_plus_state -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => HLPL_plus_int n, S
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => v, S
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => S.[pi], S.[pi <- bot]
where "S |-{op} op => v , S'" := (eval_op op S v S').

Definition spath_pred (p : spath) : option spath :=
  match snd p with
  | [] => None
  | _ => Some (fst p, removelast (snd p))
  end.

Lemma spath_pred_app_last p i : spath_pred (p +++ [i]) = Some p.
Proof.
  unfold spath_pred, app_spath_vpath. 
  cbn. autodestruct.
  - intro H. exfalso. eapply app_cons_not_nil. eauto.
  - intros <-. rewrite removelast_last, <-surjective_pairing. reflexivity.
Qed.

Lemma spath_pred_is_Some p q : spath_pred p = Some q -> exists i, p = q +++ [i].
Proof.
  unfold spath_pred. intro.
  assert (snd p <> []) by now destruct (snd p).
  assert ((fst p, removelast (snd p)) = q) as <-.
  { destruct (snd p); [discriminate | injection H; easy]. }
  exists (last (snd p) 0). unfold app_spath_vpath. cbn.
  rewrite<- app_removelast_last by assumption.
  apply surjective_pairing.
Qed.

Local Open Scope option_monad_scope.
Definition ancestor (S : HLPL_plus_state) p : HLPL_plus_constructor :=
  match spath_pred p with
  | None => botC
  | Some q => get_constructor (S.[q])
  end.

Lemma ancestor_app_last S p i : ancestor S (p +++ [i]) = get_constructor (S.[p]).
Proof. unfold ancestor. rewrite spath_pred_app_last. reflexivity. Qed.

Lemma ancestor_not_strict_prefix S p q v :
  ~strict_prefix q p -> ancestor (S.[q <- v]) p = ancestor S p.
Proof.
  unfold ancestor. intro. autodestruct.
  intros (? & ?)%spath_pred_is_Some. subst.
  rewrite constructor_sset_sget_not_prefix by auto with spath. reflexivity.
Qed.

Lemma ancestor_is_not_bot S p c :
  ancestor S p = c -> c <> botC -> exists q i, p = q +++ [i] /\ get_constructor (S.[q]) = c.
Proof.
  unfold ancestor. autodestruct. intros (i & ->)%spath_pred_is_Some.
  intros. eexists _, _. eauto.
Qed.

Local Reserved Notation "S  |-{rv}  rv  =>  v , S'" (at level 50).

Variant eval_rvalue : rvalue -> HLPL_plus_state -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
  | Eval_just op v S S' (Heval_op : S |-{op} op => v, S') : S |-{rv} (Just op) => v, S'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => HLPL_plus_int m, S') ->
      (S' |-{op} op_r => HLPL_plus_int n, S'') ->
      S |-{rv} (BinOp op_l op_r) => (HLPL_plus_int (m + n)), S''
  | Eval_pointer_loc S p pi l
      (Heval_place : eval_place S Mut p pi)
      (Hancestor_loc : ancestor S pi = locC(l)) :
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
      S |-{rv} &mut p => ptr(l), S
  | Eval_pointer S p pi l
      (Heval_place : eval_place S Mut p pi)
      (Hancestor_no_loc : ~is_loc (ancestor S pi)) :
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
      is_fresh l S ->
      S |-{rv} (&mut p) => ptr(l), (S.[pi <- loc(l, S.[pi])])
where "S |-{rv} rv => v , S'" := (eval_rvalue rv S v S').

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_refl S : reorg S S
| Reorg_trans S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    disj p q -> S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    not_contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_plus_state -> statement -> nat -> Option (statement_result * HLPL_plus_state) -> Prop
*)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).
Inductive eval_stmt : statement -> statement_result -> HLPL_plus_state -> HLPL_plus_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => rUnit, S
  | Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | Eval_assign S S' p rv v sp : (S |-{rv} rv => v, S') -> eval_place S' Mut p sp ->
      not_contains_outer_loc (S'.[sp]) -> not_contains_outer_loan (S'.[sp]) ->
      S |-{stmt} ASSIGN p <- rv => rUnit, (S' .[ sp <- v]),, Anon |-> S' .[ sp]
  | Eval_reorg S0 S1 S2 stmt r : reorg S0 S1 -> S1 |-{stmt} stmt => r, S2 -> S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(* TODO: introduce well-formedness judgement. *)

Inductive le_state_base : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Le_MutBorrow_To_Ptr S l sp_loan sp_borrow v (Hdisj : disj sp_loan sp_borrow)
    (HS_loan :S.[sp_loan] = loan^m(l)) (HS_borrow : S.[sp_borrow] = borrow^m(l, v)) :
    le_state_base (S.[sp_loan <- loc(l, v)].[sp_borrow <- ptr(l)]) S.

Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| Cl_base x y : R x y -> refl_trans_closure R x y
| Cl_refl x : refl_trans_closure R x x
| Cl_trans x y z : refl_trans_closure R x y -> refl_trans_closure R y z -> refl_trans_closure R x z.

Definition le_state := refl_trans_closure le_state_base.

(* With le_state, we are generally going to prove preservation properties, of the following forms:
 *)
(* Let R be a transition relation. For example:
   - R = reorg
   - R = eval_stmt s r
   The following definition states that R is preserved by le_state, which means that if we have
   Sr >= Sl and a transition from Sr to Sr' (with R), then there exists a state S'l that complete
   the following square:

    Sr >=  Sl

    |      |
    R      R
    |      |
    v      v

   Sr' >= S'l

 *)
Definition preserves_le_state (R : HLPL_plus_state -> HLPL_plus_state -> Prop) :=
  (forall Sl Sr, le_state Sl Sr ->
   forall S'r, R Sr S'r  -> exists S'l, R Sl S'l /\ le_state S'l S'r).

(* TODO harmonization: change the type of R to "val -> state -> state" *)
(* Let R be a transition relation that produced a value. For example:
   - R = eval_op op
   - R = eval_rv rv
   The following definition states that R is preserved by le_state, which means that if we have
   Sr >= Sl and a transition from Sr to Sr' producing a value vr (with R), then there exists a state
   S'l and a value vl that complete the following square:

      Sr   >=    Sl

      |          |
      R          R
      |          |
      v          v

   Sr', vr >= S'l, vl

 *)
Definition preserves_le_state_val (R : HLPL_plus_state -> HLPL_plus_val -> HLPL_plus_state -> Prop) :=
  (forall Sl Sr, le_state Sl Sr ->
   forall vr S'r, R Sr vr S'r ->
   exists vl S'l, R Sl vl S'l /\ le_state (S'l ++ [(Anon, vl)]) (S'r ++ [(Anon, vr)])).

(* To prove a preservation result, we are proving it on the base cases, and using the lemmas to
 * skip the reflexivity and transitivity cases: *)
Lemma preserves_le_state_if_preserves_le_state_base R
  (H : forall Sl Sr, le_state_base Sl Sr ->
       forall S'r, R Sr S'r  -> exists S'l, R Sl S'l /\ le_state S'l S'r) :
  preserves_le_state R.
Proof.
  intros Sl Sr Hle_state. induction Hle_state as [ | Sr | Sl Smid Sr _ IHl _ IHr].
  - intros. eapply H; eassumption.
  - intros S'r ?. exists S'r. split. assumption. apply Cl_refl.
  - intros S'r HRr.
    destruct (IHr S'r HRr) as (S'mid & HRmid & ?). destruct (IHl S'mid HRmid) as (S'l & ? & ?).
    exists S'l. split; try assumption. eapply Cl_trans; eassumption.
Qed.

Lemma preserves_le_state_val_if_preserves_le_state_base R
  (H : forall Sl Sr, le_state_base Sl Sr ->
       forall vr S'r, R Sr vr S'r ->
       exists vl S'l, R Sl vl S'l /\ le_state (S'l ++ [(Anon, vl)]) (S'r ++ [(Anon, vr)])) :
  preserves_le_state_val R.
Proof.
  intros Sl Sr Hle_state. induction Hle_state as [ | Sr | Sl Smid Sr _ IHl _ IHr].
  - intros. eapply H; eassumption.
  - intros vr S'r ?. exists vr, S'r. split. assumption. apply Cl_refl.
  - intros vr S'r HRr.
    destruct (IHr vr S'r HRr) as (vmid & S'mid & HRmid & ?).
    destruct (IHl vmid S'mid HRmid) as (vl & S'l & ? & ?).
    exists vl, S'l. split; try assumption. eapply Cl_trans; eassumption.
Qed.

(* The previous definition is not really handy to prove the square diagram. Indeed, it requires
 * exhibiting a well-chosen environment S'l (as well as a value vl) that can be reduced from Sl and
 * that satisfies the relation <=.
 * Using this lemma, we can avoid exhibiting states as much as possible:
 * - We prove that Sl reduces to some environement S'l and a value vl.
 * - We prove that Sr, Anon |-> vr >= S''l for some environment S''l.
 * - We prove that S'l, Anon |-> vl = S''l
 * The first two goals should be proven by applying the constructors (for the R relation and for le)
 * without exhibiting a single state. The equality should be proven automatically.
 *)
Lemma prove_square_diagram_le_state_val R (Sl Sr S'l S''l : HLPL_plus_state) vr vl
  (Hstep : R Sl vl S'l)
  (Hrel : le_state S''l (Sr ++ [(Anon, vr)]))
  (Heq : (S'l ++ [(Anon, vl)]) = S''l) :
  exists vl S'l, R Sl vl S'l /\ le_state (S'l ++ [(Anon, vl)]) (Sr ++ [(Anon, vr)]).
Proof. exists vl, S'l. subst. split; assumption. Qed.

Lemma prove_square_diagram_le_state R (Sl Sr S'l S''l : HLPL_plus_state)
  (Hstep : R Sl S'l)
  (Hrel : le_state S''l Sr)
  (Heq : S'l = S''l) :
  exists S'l, R Sl S'l /\ le_state S'l Sr.
Proof. exists S'l. subst. split; assumption. Qed.

(* Just a shorthand *)
Ltac square_diagram :=
  lazymatch goal with
  | |- exists v S, _ /\ le_state (S ++ [(Anon, v)]) _ =>
      eapply prove_square_diagram_le_state_val
  | |- exists S, _ /\ le_state S _ =>
      eapply prove_square_diagram_le_state
  end.

(* Proving a comparison between p and q using information from the environment S. *)
Lemma spath_neq_by_value_constructor (S : HLPL_plus_state) p q v c :
  S.[p] = v -> get_constructor (S.[q]) = c -> get_constructor v <> c -> p <> q.
Proof. intros H G diff_cons EQ. apply diff_cons. rewrite <-H, <-G, EQ. reflexivity. Qed.
Hint Extern 5 (?p <> ?q) =>
  match goal with
  | H : ?S.[?p] = ?v, G : get_constructor (?S.[?q]) = ?c |- _ =>
      simple apply (spath_neq_by_value_constructor S p q v c); [exact H | exact G | discriminate]
  end : spath.

Lemma get_nil_prefix_right'  {V : Type} {IsValue : Value V} {B : Type} (S : state B V)
  (p q : spath) :
subvalues (S .[ p]) = [] -> valid_spath S q -> ~strict_prefix p q.
Proof.
  intros H G K. assert (q = p) as ->.
  { eapply get_nil_prefix_right; try eassumption. apply strict_prefix_is_prefix. assumption. }
  eapply strict_prefix_irrefl. eassumption.
Qed.

(* TODO: move in PathToSubtree.v *)
(* TODO: counterpart of get_nil_prefix_right' *)
Lemma strict_prefix_one_subvalue (S : HLPL_plus_state) p q (H : length (subvalues (S.[p])) = 1) :
  strict_prefix p q -> valid_spath S q -> prefix (p +++ [0]) q.
Proof.
  intros (i & r & <-) (_ & G)%valid_spath_app.
  assert (i = 0) as ->.
  { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
    inversion G. destruct (nth_error (subvalues (S.[p]))); easy. }
  exists r. rewrite<- app_spath_vpath_assoc. reflexivity.
Qed.
Corollary not_prefix_one_subvalue (S : HLPL_plus_state) p q :
  length (subvalues (S.[p])) = 1 -> valid_spath S q -> ~prefix (p +++ [0]) q -> ~strict_prefix p q.
Proof. intros ? ? H ?. eapply H, strict_prefix_one_subvalue; eassumption. Qed.

Hint Resolve not_prefix_one_subvalue : spath.
Hint Extern 5 (length (subvalues ?v) = _) =>
  match goal with
  | H : get_constructor (?S.[?p]) = _ |- _ =>
      rewrite length_subvalues_is_arity, H; reflexivity
  end : spath.

(* Try to automatically solve a validity goal validity S pi. Here is how the procedure should
 * work:
 * - If the state S is of the form S'.[q <- v], reduce to valid S' pi provided that
     ~strict_prefix q pi.
 * - If the state S is of the form S,, b |-> v
 *   - If pi = (length S, q), meaning that pi refers to the last binding, reduce to valid v q
 *   - Otherwise, reduce to valid S pi
 * - Search the proof that pi is the evaluation of a place.
 * - Search for a proof that S.[p] <> bot in the hypotheses.
 * - Search for a proof that the constructor of S.[p] is not bot in the hypotheses.
 *)
Lemma valid_get_constructor_sget_not_bot (S : HLPL_plus_state) p :
  get_constructor (S.[p]) <> get_constructor bot -> valid_spath S p.
Proof. intros G. apply get_not_bot_valid_spath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_app_last_get_constructor_not_zeoray (S : HLPL_plus_state) p :
  arity (get_constructor (S.[p])) > 0 -> valid_spath S (p +++ [0]).
Proof.
  intro. apply valid_spath_app. split.
  - apply get_not_bot_valid_spath. intro G. rewrite G in H. cbn in H. inversion H.
  - rewrite<- length_subvalues_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Ltac solve_validity0 :=
  lazymatch goal with
  | H : ?S |-{p} _ =>^{ _ } ?pi |- valid_spath ?S ?pi =>
      simple eapply eval_place_valid;
      exact H
  | |- valid_spath (?S.[?p <- ?v]) ?q =>
      apply sset_not_prefix_valid; [ | solve_validity0]
  | |- valid_spath (?S ++ _) (length ?S, ?q) =>
      apply valid_spath_last;
      solve_validity0
  | |- valid_spath (?S ++ ?S') ?p =>
      simple apply valid_app_spath;
      solve_validity0
  | H : ?S.[?p] = ?v |- valid_spath ?S ?p =>
      simple apply get_not_bot_valid_spath;
      rewrite H;
      discriminate
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S ?p =>
      apply (valid_get_constructor_sget_not_bot S p);
      rewrite H;
      discriminate
  | H : ?S.[?p +++ ?q] = _ |- valid_vpath (?S.[?p]) ?q =>
      simple apply get_not_bot_valid_vpath;
      rewrite <-sget_app, H;
      discriminate
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S (?p +++ [0]) =>
      simple apply valid_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | |- valid_spath ?S ?p => idtac
  | |- valid_vpath ?v ?p => idtac
  end.
Hint Extern 5 (valid_spath _ _) => solve_validity0.
Ltac solve_validity := solve_validity0; eauto with spath.

(* Testing that I can automatically prove validity: *)
Goal forall (S : HLPL_plus_state) p l, S.[p] = ptr(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) p l, get_constructor (S.[p]) = locC(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) v w p q r l, disj p r -> ~strict_prefix q r -> S.[r] = loan^m(l)
  -> valid_spath (S.[p <- v].[q <- w]) r.
Proof. intros. solve_validity. Qed.

(* TODO: rework this hint. *)
Hint Extern 5 (~strict_prefix ?p ?q) =>
  match goal with
  | H : ?S.[?p] = _ |- _ =>
      simple apply (get_nil_prefix_right' S); [rewrite H | ]
  end : spath.

(* Adding a hint to reslove a relation ~prefix p q using the facts that:
 * - S.[p] does not contain a constructor c.
 * - S.[q] starts by the constructor c.
 * To solve the second goal, we need to help auto. When we are using this lemma, there should be a
 * hypothesis S.[q] = v. We are giving the instruction to rewrite S.[q] into v, and then to reduce
 * the expression (get_value v) produced, so that it can be solved automatically.
 *)
Hint Extern 3 (~prefix ?p ?q) =>
  match goal with
  | H : ?S.[?q] = _ |- _ =>
    simple eapply not_value_contains_not_prefix; [ | rewrite H; cbn | solve_validity]
  end : spath.

Hint Extern 2 (disj ?p (length ?S, ?q)) =>
  simple apply (disj_spath_to_last S); [solve_validity | ] : spath.
Hint Extern 2 (disj (length ?S, ?q) ?p) =>
  symmetry; simple apply (disj_spath_to_last S); [solve_validity | ] : spath.

(* Try to rewrite sset_sget_equal (S.[p <- v].[p] = v if p is valid), and try to automatically
 * solve the validity hypothesis by proving that S.[p] <> bot. *)
Hint Rewrite @sset_sget_equal using solve_validity : spath.
Hint Rewrite @sset_sget_prefix using solve_validity : spath.
(* Try to rewrite sset_sget_disj (S.[p <- v].[q] = S.[q] if p and q are disjoint), only if it can
 * automatically prove it. *)
Hint Rewrite @sset_sget_disj using eauto with spath; fail : spath.
Hint Rewrite @sset_twice_prefix_right : spath.
Hint Rewrite<- @sset_app_state using solve_validity; fail : spath.
Hint Rewrite<- @sset_app_last_state using rewrite !length_sset; reflexivity : spath.
Hint Rewrite @sget_app_state using solve_validity; fail : spath.
Hint Rewrite @sget_app_last_state using rewrite !length_sset; reflexivity : spath.
Hint Rewrite @constructor_sset_sget_not_prefix using eauto with spath; fail : spath.
(* Hint Rewrite <- @sget_app : spath. *)

(* Automatically solve equality between two states that are sets of a state S, ie solves goals of
 * the form:
 * S.[p0 <- v0] ... .[pm <- vm] = S.[q0 <- w0] ... .[qn <- vn]
 *
 * Strategy: it's easy to compute values that are a get of a sequence of sets, i.e:
 * S.[p0 <- v0] ... .[pm <- vm] .[q]
 * This works when we know the relation between the state q we get and the states p0, ..., pk we
 * set.
 * Let's denote Sl := S.[p0 <- v0] ... .[pm <- vm] and Sr := S.[q0 <- w0] ... .[qn <- vn]. To prove
 * that Sl = Sr, we are going to prove that Sl.[q] = Sr.[q] for q = p0, ..., pm. For the spaths q
 * that are not prefix of p0, ..., pm, we are going to prove that Sl.[q] and Sr.[q] have the same
 * constructor.
 * Finally, we also need to prove that Sl and Sr have the binders, which is an easy consequence of
 * the fact that they are sets of the same state S.
 *)
Ltac prove_states_eq :=
  let q := fresh "q" in
  (* autorewrite with spath; *)
  cbn;
  lazymatch goal with
  | |- _ ++ [ _ ] = _ ++ [ _ ] =>
      f_equal; prove_states_eq
  | |- ?S.[?p0 <- _].[?p1 <- _].[?p2 <- _] = _ =>
        apply get_constructor_sget_ext; [intro; rewrite !get_binder_sset; reflexivity | ];
        intro q;
        destruct (decidable_prefix p0 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        destruct (decidable_prefix p1 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        destruct (decidable_prefix p2 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        autorewrite with spath; reflexivity
  | |- ?S.[?p0 <- _].[?p1 <- _] = _ =>
        apply get_constructor_sget_ext; [intro; rewrite !get_binder_sset; reflexivity | ];
        intro q;
        destruct (decidable_prefix p0 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        destruct (decidable_prefix p1 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        autorewrite with spath; reflexivity
  end.

(* A _comparison_ `C p q` between is one of those relation:
   - `p = q` or `p <> q`
   - `prefix p q` or `~prefix p q`
   - `strict_prefix p q` or `~strict_prefix p q`
   - `disj p q` or `~disj p q`
 *)
(* We are going to define a tactic called "reduce_comp" to assist the proof of comparisons between
 * two paths p and q, using comparisons in the hypotheses as much as possible.
 *
 * The key idea is that there are four possible "atomic" comparisons: p = q, strict_prefix p q,
 * strict_prefix q p and disj p q. These comparisons are atomic in the sense that for any p and q,
 * exactly one of those is true.
 *
 * Every comparison C p q is equivalent to a disjunction of atomic comparisons. By contraposition,
 * this means that every comparison C p q is equivalent to the conjuction of the negation of
 * atomas. For example:
 * - prefix p q <-> (p = q \/ strict_prefix p q) <-> (~strict_prefix q p /\ ~disj p q)
 * - ~prefix p q <-> (strict_prefix q p \/ ~disj p q) <-> (p <> q /\ ~strict_prefix p q)
 * - disj p q <-> disj p q <-> (p <> q /\ ~strict_prefix p q /\ ~strict_prefix q p)
 *
 * Thus, to prove a comparison C p q in the goal, reduce_comp works the following way:
 * - It generates the negative atomic relations necessary to prove C p q
 * - For each negative atomic relation, it tries to prove it automatically using the hypotheses.
 * The negative atomic relations that could not be automatically proven are left as subgoals. This
 * tactic never fails (as long as the goal is a comparison).
 *
 * Note: this tactic is not complete yet, more comparisons have to be added. It's also subject to
 * change.
 *)

(* TODO: move *)
(* TODO: automate proofs for more comparisons. *)
Lemma prefix_if_equal_or_strict_prefix p q : prefix p q -> p = q \/ strict_prefix p q.
Proof.
  intros ([ | i r] & <-).
  - left. symmetry. apply app_spath_vpath_nil_r.
  - right. exists i, r. reflexivity.
Qed.

Corollary prove_not_prefix p q : p <> q -> ~strict_prefix p q -> ~prefix p q.
Proof. intros ? ? [ | ]%prefix_if_equal_or_strict_prefix; auto. Qed.

Lemma prove_disj p q : p <> q -> ~strict_prefix p q -> ~strict_prefix q p -> disj p q.
Proof. destruct (comparable_spaths p q); easy. Qed.

(* TODO: replace by eauto with spath? *)
Ltac prove_not_atom :=
  match goal with
  (* Trying to automatically prove p <> q *)
  | H : ?p <> ?q |- ?p <> ?q => exact H
  | H : ?q <> ?p |- ?p <> ?q => symmetry; exact H
  | H : ~prefix ?p ?q |- ?p <> ?q => intros ->; apply H; reflexivity
  | H : ?S.[?p] = ?v, G : get_constructor (?S.[?q]) = ?c |- ?p <> ?q =>
      let EQ := fresh "EQ" in
      intro EQ;
      rewrite EQ in H;
      rewrite H in G;
      discriminate

  (* Trying to automatically prove ~strict_prefix p q *)
  | H : ~strict_prefix ?p ?q |- ~strict_prefix ?p ?q => exact H
  | H : ~prefix ?p ?q |- ~strict_prefix ?p ?q => intro; apply H, strict_prefix_is_prefix; assumption
  (* When we have a hypotheses H : S.[p] = v with v a 0-ary value (for example, v = loan^m(l)),
     we try to prove that p cannot be a strict prefix of q by using the validity of q: *)
  | H : ?S.[?p] = ?v |- ~strict_prefix ?p ?q =>
      let G := fresh "G" in
      (* Trying to automatically prove that p has no subvalues, this branch fails if we can't. *)
      assert (G : subvalues (S.[p]) = []) by (rewrite H; reflexivity);
      apply (get_nil_prefix_right' S p q G);
      solve_validity
  | _ => idtac
  end.

Goal forall (S : HLPL_plus_state) p q l, S.[p] = loan^m(l) -> S.[q] = HLPL_plus_int 3 -> ~strict_prefix p q.
Proof. intros. prove_not_atom. Qed.

Ltac reduce_comp :=
  unfold not; (* Used to prove both negations of the form ~C p q and C p q -> False *)
  match goal with
  | |- prefix ?p ?q -> False => apply prove_not_prefix
  | |- disj ?p ?q => apply prove_disj
  end;
  eauto with spath.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l0 : loan_id).
  Context (v : HLPL_plus_val).
  Context (sp_loan sp_borrow : spath).
  Context (Hdisj : disj sp_loan sp_borrow).
  Context (HS_r_loan : S_r.[sp_loan] = loan^m(l0)).
  Context (HS_r_borrow : S_r.[sp_borrow] = borrow^m(l0, v)).
  Notation S_l := (S_r.[sp_loan <- loc(l0, v)].[sp_borrow <- ptr(l0)]).
  Context (perm : permission).

  Hint Rewrite HS_r_borrow : spath.
  Hint Rewrite HS_r_loan : spath.

  (* TODO: name *)
  Inductive rel : spath -> spath -> Prop :=
  | Rel_sp_borrow_strict_prefix q : rel (sp_loan +++ 0 :: q) (sp_borrow +++ 0 :: q)
  | Rel_other q : ~strict_prefix sp_borrow q -> rel q q.

  (* An equivalent (and more usable I hope) version of rel. *)
  Definition rel' p q :=
    (exists r, p = sp_loan +++ 0 :: r /\ q = sp_borrow +++ 0 :: r) \/
    (p = q /\ ~strict_prefix sp_borrow p).
  Definition rel_implies_rel' p q : rel p q -> rel' p q.
  Proof.
    intros [r | ].
    - left. exists r. auto.
    - right. auto.
  Qed.

  (* TODO: name *)
  Lemma get_loc_rel q l (H : get_constructor (S_r.[q]) = locC(l)) :
    exists q', rel (q' +++ [0]) (q +++ [0]) /\ get_constructor (S_l.[q']) = locC(l).
  Proof.
    destruct (decidable_prefix sp_borrow q) as [([ | i r] & <-) | sp_borrow_not_prefix].
    (* Case 1: q = sp_borrow. We are eliminating this case. *)
    - rewrite app_spath_vpath_nil_r in H. rewrite HS_r_borrow in H. discriminate.
    (* Case 2: sp_borrow is a strict_prefix of q. *)
    - rewrite sget_app in H. autorewrite with spath in H.
      assert (i = 0) as ->.
      { eapply (get_arity_0 (borrow^m(l0, v)) i).
        - reflexivity.
        - intros G. rewrite G in H. discriminate.
      }
      exists (sp_loan +++ 0 :: r). split. { rewrite<- !app_spath_vpath_assoc. constructor. }
      rewrite sget_app. autorewrite with spath. exact H.
    - exists q. split.
      (* comparison reasonning: *)
      + apply Rel_other. intros ?%strict_prefix_app_last. auto.
      + rewrite constructor_sset_sget_not_prefix by assumption.
        rewrite constructor_sset_sget_not_prefix by reduce_comp. assumption.
  Qed.

  Lemma eval_proj_mut_sp_borrow_strict_prefix proj r q
    (H : eval_proj S_r perm proj (sp_borrow +++ 0 :: r) q) :
    exists q', rel q' q /\ eval_proj S_l perm proj (sp_loan +++ 0 :: r) q'.
  Proof.
    remember (sp_borrow +++ 0 :: r) as p. revert r Heqp. induction H; intros r ->.
    - exists ((sp_loan +++ 0 :: r) +++ [0]). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + apply Eval_Deref_MutBorrow with (l := l); try assumption.
        rewrite sget_app in *. autorewrite with spath in *. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try assumption.
      rewrite sget_app in *. autorewrite with spath in *. assumption.
    - specialize (IHeval_proj (r ++ [0])). destruct IHeval_proj as (q'' & ? & ?).
      + rewrite<- app_spath_vpath_assoc. reflexivity.
      + exists q''. split; try assumption.
        apply Eval_Loc with (l := l).
        * assumption.
        * rewrite sget_app in *. autorewrite with spath in *. assumption.
        * rewrite<- app_spath_vpath_assoc. assumption.
  Qed.

  Lemma eval_proj_mut_not_prefix_sp_borrow proj q r
    (not_prefix : ~strict_prefix sp_borrow q) (H : eval_proj S_r perm proj q r) :
    exists r', rel r' r /\ eval_proj S_l perm proj q r'.
  Proof.
    induction H.
    - destruct (decidable_spath_eq q sp_borrow) as [-> | ].
      + exists (sp_loan +++ [0]). split. { constructor. }
        apply Eval_Deref_Ptr_Locs with (l := l0); autorewrite with spath; easy.
      + exists (q +++ [0]). split.
        { apply Rel_other. enough (~prefix sp_borrow q) by (intros K%strict_prefix_app_last; easy). reduce_comp. }
        apply Eval_Deref_MutBorrow with (l := l); try assumption.
        rewrite constructor_sset_sget_not_prefix by reduce_comp.
        rewrite constructor_sset_sget_not_prefix by reduce_comp.
        assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try auto.
      rewrite constructor_sset_sget_not_prefix by reduce_comp.
      rewrite constructor_sset_sget_not_prefix by reduce_comp.
      assumption.
    - destruct IHeval_proj as (r' & ? & ?).
      { intros G%strict_prefix_app_last; revert G. reduce_comp. }
      exists r'. split; try assumption. apply Eval_Loc with (l := l); try easy.
      rewrite constructor_sset_sget_not_prefix by reduce_comp.
      rewrite constructor_sset_sget_not_prefix by reduce_comp.
      assumption.
  Qed.

  Lemma eval_proj_mut_borrow_to_ptr proj q_l q_r q'_r :
    rel q_l q_r -> eval_proj S_r perm proj q_r q'_r ->
    exists q'_l, rel q'_l q'_r /\ eval_proj S_l perm proj q_l q'_l.
  Proof.
    intros [ r | q G] H.
    - apply eval_proj_mut_sp_borrow_strict_prefix. assumption.
    - apply eval_proj_mut_not_prefix_sp_borrow; assumption.
  Qed.

  Corollary eval_path_mut_borrow_to_ptr P q_r q'_r :
    eval_path S_r perm P q_r q'_r -> forall q_l, rel q_l q_r ->
    exists q'_l, rel q'_l q'_r /\ eval_path S_l perm P q_l q'_l.
  Proof.
    intros H. induction H.
    - eexists. split. eassumption. constructor.
    - intros q_l ?.
      apply eval_proj_mut_borrow_to_ptr with (q_l := q_l) in Heval_proj; try assumption.
      destruct Heval_proj as (q'_l & rel_q'_l & ?).
      destruct (IHeval_path q'_l rel_q'_l) as (q''_l & ? & ?).
      exists q''_l. split. { assumption. }
      apply Eval_cons with (q := q'_l); assumption.
  Qed.

  Lemma eval_path_mut_borrow_to_ptr_Mov P q q' :
    eval_path S_r Mov P q q' -> eval_path S_l Mov P q q'.
  Proof.
    intro H. induction H.
    - constructor.
    - destruct Heval_proj; easy.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr p pi_r :
    eval_place S_r perm p pi_r ->
    exists pi_l, rel pi_l pi_r /\ eval_place S_l perm p pi_l.
  Proof.
    intros (i & ? & H). apply eval_path_mut_borrow_to_ptr with (q_l := (i, [])) in H.
    - destruct H as (q'_l & rel & ?). exists q'_l. split. { assumption. }
      exists i. split. { rewrite! find_binder_sset. assumption. }
      assumption.
    - apply Rel_other. apply not_strict_prefix_nil.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr_Mov p pi :
    eval_place S_r Mov p pi -> eval_place S_l Mov p pi.
  Proof.
    intros (i & ? & H). apply eval_path_mut_borrow_to_ptr_Mov with (q := (i, [])) in H.
    exists i. split; try assumption. rewrite! find_binder_sset. assumption.
  Qed.

  Lemma eval_place_mut_borrow_to_ptr_Mov_comp p pi :
    eval_place S_r Mov p pi -> ~strict_prefix sp_borrow pi.
  Proof.
    intros (i & ? & H). remember (i, []) as pi0. induction H.
    - rewrite Heqpi0. apply not_strict_prefix_nil.
    - destruct Heval_proj; easy.
  Qed.
End MutBorrow_to_Ptr.

Lemma le_state_app_last S_l S_r v0 (H : le_state S_l S_r) :
  le_state (S_l ++ [(Anon, v0)]) (S_r ++ [(Anon, v0)]).
Proof.
  induction H as [? ? H | | ].
  - destruct H. rewrite !sset_app_state by solve_validity.
    apply Cl_base, Le_MutBorrow_To_Ptr; try assumption.
    all: rewrite sget_app_state by solve_validity; assumption.
  - apply Cl_refl.
  - eapply Cl_trans; eassumption.
Qed.

(* This lemma is useful for evaluations that do not change the universe and return the same
   values, i.e:
   - evaluation of constants
   - evaluation of copies (when the copied value is not affected by >= )
   - evaluation binary operations
   - evaluation of pointers, when the borrowed value is under a loc.
   This corresponds to the following square diagram:
     Sr  >=   Sl

     |        |
     R        R
     |        |
     v        v

   Sr, v >= Sl, v

   The stategy to complete the square diagram is to just prove that Sl evaluates to (v, Sl),
   with v the same value Sr evaluates to, and then use the relation Sr >= Sl in the context.
 *)
(* TODO: confusing name, as it does not only apply to constants. *)
Lemma prove_square_diagram_constant_evaluation R (Sl Sr : HLPL_plus_state) v
  (Hstep : R Sl v Sl)
  (Hrel : le_state Sl Sr) :
  exists vl S'l, R Sl vl S'l /\ le_state (S'l ++ [(Anon, vl)]) (Sr ++ [(Anon, v)]).
Proof.
  exists v, Sl. split.
  - assumption.
  - apply le_state_app_last. assumption.
Qed.

Lemma operand_preserves_HLPL_plus_rel op : preserves_le_state_val (eval_op op).
Proof.
  apply preserves_le_state_val_if_preserves_le_state_base.
  intros Sl Sr Hle vr S'r Heval. destruct Heval.
  - exists (HLPL_plus_int n), Sl. split.
    + constructor.
    + apply le_state_app_last. constructor. assumption.
  - admit.
  - destruct Hle.
    assert (~strict_prefix sp_borrow pi).
    { eapply eval_place_mut_borrow_to_ptr_Mov_comp. eassumption. }
    assert (disj pi sp_loan) by reduce_comp.
    destruct (decidable_prefix pi sp_borrow) as [(q & <-) | ].
    + square_diagram.
      * constructor. { apply eval_place_mut_borrow_to_ptr_Mov. eassumption. }
        all: autorewrite with spath; auto with spath.
      * constructor.
        apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := (length S, q)).
        all: autorewrite with spath; eauto with spath.
        (* TODO: should be solved automatically. *)
        rewrite sget_app in * |-. eassumption.
      * autorewrite with spath. prove_states_eq.
    + assert (disj pi sp_borrow) by reduce_comp.
      square_diagram.
      * constructor. { apply eval_place_mut_borrow_to_ptr_Mov. eassumption. }
        all: autorewrite with spath; auto with spath.
      * constructor.
        apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        all: autorewrite with spath; eauto with spath.
      * autorewrite with spath. prove_states_eq.
Admitted.

Lemma rvalue_preserves_HLPL_plus_rel rv : preserves_le_state_val (eval_rvalue rv).
Admitted.

Lemma eval_rvalue_no_loc S rv v S' : S |-{rv} rv => v, S' -> not_contains_loc v.
Proof.
  intro H. destruct H; [destruct Heval_op | ..]; auto with spath.
  induction Hcopy_val; auto with spath.
Qed.

Lemma eval_rvalue_no_loan S rv v S' : S |-{rv} rv => v, S' -> not_contains_loan v.
Proof.
  intro H. destruct H; [destruct Heval_op | ..]; auto with spath.
  induction Hcopy_val; auto with spath.
Qed.

Lemma eval_path_app_last S p k pi S' : S |-{p} p =>^{k} pi -> (S ++ S') |-{p} p =>^{k} pi.
Proof.
Admitted.

Lemma eval_path_app_last' S v p k pi :
  not_contains_loc v -> (S,, Anon |-> v) |-{p} p =>^{k} pi -> S |-{p} p =>^{k} pi.
Proof.
Admitted.
