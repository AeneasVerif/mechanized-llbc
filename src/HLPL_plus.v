Require Import base.
Require Import lang.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
Require Import Lia ZArith.

Require Import PathToSubtree.
Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import SimulationUtils.

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

Program Instance EqDec_HLPL_plus_constructor : EqDec HLPL_plus_constructor.
Next Obligation. decide equality; decide equality. Qed.


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

Fixpoint HLPL_plus_weight node_weight v :=
  match v with
  | HLPL_plus_mut_borrow l v => node_weight (HLPL_plus_mut_borrowC l) + HLPL_plus_weight node_weight v
  | HLPL_plus_loc l v => node_weight (HLPL_plus_locC l) + HLPL_plus_weight node_weight v
  | v => node_weight (HLPL_plus_get_constructor v)
end.

Program Instance ValueHLPL : Value HLPL_plus_val := {
  constructors := HLPL_plus_constructor;
  arity := HLPL_plus_arity;
  get_constructor := HLPL_plus_get_constructor;
  subvalues := HLPL_plus_subvalues;
  fold_value := HLPL_plus_fold;
  total_weight := HLPL_plus_weight;
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
Next Obligation. destruct v; reflexivity. Qed.

Definition HLPL_plus_state := state HLPL_plus_binder HLPL_plus_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: set every priority to 0? *)
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

Lemma sget_loc l v p : (loc(l, v)).[[ [0] ++  p]] = v.[[p]].
Proof. reflexivity. Qed.
Hint Rewrite sget_loc : spath.
Lemma sget_loc' l v : (loc(l, v)).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite sget_loc' : spath.

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

Definition eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

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
Hint Resolve eval_place_valid : spath.

Variant is_loan : HLPL_plus_constructor -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Variant is_loc : HLPL_plus_constructor -> Prop :=
| IsLoc_Loc l : is_loc (locC(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.
Hint Extern 0 (~is_loc _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Variant is_mut_borrow : HLPL_plus_constructor -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).
Notation not_contains_outer_loc := (not_contains_outer is_mut_borrow is_loc).

Definition not_in_borrow (S : HLPL_plus_state) p :=
  forall q, is_mut_borrow (get_constructor (S.[q])) -> ~strict_prefix q p.

Lemma not_in_borrow_sset S p q v : not_in_borrow S p -> ~strict_prefix q p ->
  not_in_borrow (S.[q <- v]) p.
Proof.
  intros H ? r G ?.
  assert (~prefix q r) by eauto with spath.
  autorewrite with spath in G. eapply H; eassumption.
Qed.
Hint Resolve not_in_borrow_sset : spath.

Lemma loc_is_not_bot x : is_loc x -> x <> botC. Proof. intros [ ]; discriminate. Qed.
Lemma loan_is_not_bot x : is_loan x -> x <> botC. Proof. intros [ ]; discriminate. Qed.
Ltac prove_not_contains_outer :=
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
      apply not_contains_outer_sset_no_contains;
        [prove_not_contains_outer | exact H | exact loc_is_not_bot || exact loan_is_not_bot]
  | no_outer_loan : not_contains_outer_loan (?S.[?q]),
    loan_at_q : get_constructor (?S.[?q +++ ?p]) = loanC^m(?l)
    |- not_contains_outer _ ?P (?S.[?q].[[?p <- ?w]]) =>
    apply not_contains_outer_sset_in_borrow;
     [ prove_not_contains_outer |
       apply no_outer_loan; rewrite<- (sget_app S q p), loan_at_q; constructor ]
  | |- not_contains_outer _ _ _ =>
      idtac
  end.

Definition get_loan_id c :=
  match c with
  | loanC^m(l) => Some l
  | borrowC^m(l) => Some l
  | locC(l) => Some l
  | ptrC(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).

Lemma is_fresh_loan_id_neq (S : HLPL_plus_state) l0 l1 p :
  get_loan_id (get_constructor (S.[p])) = Some l0 -> is_fresh l1 S -> l0 <> l1.
Proof.
  intros get_p Hfresh <-. eapply Hfresh; [ | exact get_p].
  apply get_not_bot_valid_spath. intro H. rewrite H in get_p. inversion get_p.
Qed.

Hint Extern 0 (get_loan_id _ <> Some ?l) =>
  lazymatch goal with
  | Hfresh : is_fresh ?l ?S, get_p : get_constructor (?S.[?p]) = ?v |- _ =>
      injection;
      refine (is_fresh_loan_id_neq S _ l p _ Hfresh);
      rewrite get_p;
      reflexivity
   end : spath.

Inductive copy_val : HLPL_plus_val -> HLPL_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_plus_int n) (HLPL_plus_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> HLPL_plus_state -> (HLPL_plus_val * HLPL_plus_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (HLPL_plus_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

(* TODO: move in PathToSubtree.v *)
Definition vpath_pred (p : vpath) : option vpath :=
  match p with
  | [] => None
  | _ => Some (removelast p)
  end.

Definition spath_pred (p : spath) : option spath :=
  SOME q <- vpath_pred (snd p) IN Some (fst p, q).

Lemma vpath_pred_app_last p i : vpath_pred (p ++ [i]) = Some p.
Proof.
  transitivity (Some (removelast (p ++ [i]))).
  - destruct (p ++ [i]) eqn:?.
    + exfalso. eapply app_cons_not_nil. eauto.
    + reflexivity.
  - f_equal. apply removelast_last.
Qed.

Lemma spath_pred_app_last p i : spath_pred (p +++ [i]) = Some p.
Proof.
  unfold spath_pred, app_spath_vpath. cbn. rewrite vpath_pred_app_last.
  rewrite<- surjective_pairing. reflexivity.
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

Definition vancestor (v : HLPL_plus_val) p : HLPL_plus_constructor :=
  match vpath_pred p with
  | None => botC
  | Some q => get_constructor (v.[[q]])
  end.

Definition ancestor (S : HLPL_plus_state) p : HLPL_plus_constructor :=
  match spath_pred p with
  | None => botC
  | Some q => get_constructor (S.[q])
  end.

Lemma vancestor_singleton v i : vancestor v [i] = get_constructor v.
Proof. reflexivity. Qed.
Hint Rewrite vancestor_singleton : spath.

(* TODO: unused. delete? *)
Lemma ancestor_app_last S p i : ancestor S (p +++ [i]) = get_constructor (S.[p]).
Proof. unfold ancestor. rewrite spath_pred_app_last. reflexivity. Qed.

Lemma ancestor_sset_not_strict_prefix S p q v :
  ~strict_prefix q p -> ancestor (S.[q <- v]) p = ancestor S p.
Proof.
  unfold ancestor. intro. autodestruct.
  intros (? & ->)%spath_pred_is_Some.
  rewrite constructor_sset_sget_not_prefix by auto with spath. reflexivity.
Qed.
Hint Rewrite ancestor_sset_not_strict_prefix using auto with spath; fail : spath.

Lemma ancestor_is_not_bot S p c :
  ancestor S p = c -> c <> botC -> exists q i, p = q +++ [i] /\ get_constructor (S.[q]) = c.
Proof.
  unfold ancestor. autodestruct. intros (i & ->)%spath_pred_is_Some.
  intros. eexists _, _. eauto.
Qed.

Lemma vancestor_app v p q : q <> [] -> vancestor v (p ++ q) = vancestor (v.[[p]]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold vancestor. rewrite app_assoc, !vpath_pred_app_last, vget_app.
  reflexivity.
Qed.

Lemma ancestor_app S p q : q <> [] -> ancestor S (p +++ q) = vancestor (S.[p]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold ancestor, vancestor.
  rewrite app_spath_vpath_assoc, spath_pred_app_last, vpath_pred_app_last, sget_app.
  reflexivity.
Qed.

Hint Rewrite vancestor_app using easy : spath.
Hint Rewrite ancestor_app using easy : spath.

Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> HLPL_plus_state -> (HLPL_plus_val * HLPL_plus_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => (HLPL_plus_int m, S')) ->
      (S' |-{op} op_r => (HLPL_plus_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => ((HLPL_plus_int (m + n)), S'')
  | Eval_pointer_loc S p pi l
      (Heval_place : S |-{p} p =>^{Mut} pi)
      (Hancestor_loc : ancestor S pi = locC(l)) : S |-{rv} &mut p => (ptr(l), S)
  | Eval_pointer_no_loc S p pi l
      (Heval_place : S |-{p} p =>^{Mut} pi)
      (Hancestor_no_loc : ~is_loc (ancestor S pi))
      (* This hypothesis is not necessary for the proof of preservation of HLPL+, but it is
         useful in that it can help us eliminate cases. *)
      (Hno_loan : not_contains_loan (S.[pi])) :
      is_fresh l S ->
      S |-{rv} (&mut p) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_end_borrow_m S (p q : spath) l :
    disj p q -> get_constructor (S.[p]) = loanC^m(l) -> get_constructor (S.[q]) = borrowC^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
| Reorg_end_ptr S (p : spath) l :
    get_constructor (S.[p]) = ptrC(l) -> (*not_in_borrow S p ->*) reorg S (S.[p <- bot])
| Reorg_end_loc S (p : spath) l :
    get_constructor (S.[p]) = locC(l) -> not_state_contains (eq ptrC(l)) S ->
    reorg S (S.[p <- S.[p +++ [0] ] ])
.

(* Automatically resolving the goals of the form `ptrC(l) <> _`, used to prove the condition
   `not_state_contains (eq ptrC(l)) S` of the rule Reorg_end_loc. *)
Hint Extern 0 (ptrC( _ ) <> _) => discriminate : spath.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : HLPL_plus_val * HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Store v S sp (eval_p : (S,, Anon |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loc : not_contains_outer_loc (S.[sp]))
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  store p (v, S) (S.[sp <- v],, Anon |-> S.[sp])
.

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
  | Eval_assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | Eval_reorg S0 S1 S2 stmt r (Hreorg : refl_trans_closure reorg S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

Inductive le_state_base : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Le_MutBorrow_To_Ptr S l sp_loan sp_borrow (Hdisj : disj sp_loan sp_borrow)
    (HS_loan : get_constructor (S.[sp_loan]) = loanC^m(l))
    (HS_borrow : get_constructor (S.[sp_borrow]) = borrowC^m(l)) :
    le_state_base (S.[sp_loan <- loc(l, S.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l)]) S.

Record HLPL_plus_well_formed (S : HLPL_plus_state) : Prop := {
  unique_borrow_mut l p q : get_constructor (S.[p]) = borrowC^m(l) ->
                            get_constructor (S.[q]) = borrowC^m(l) -> p = q;
  unique_loan_mut l p q : get_constructor (S.[p]) = loanC^m(l) ->
                          get_constructor (S.[q]) = loanC^m(l) -> p = q;
  no_mut_loan_ptr l p : get_constructor (S.[p]) = loanC^m(l) ->
                        not_state_contains (eq ptrC(l)) S;
  no_mut_loan_loc l p : get_constructor (S.[p]) = loanC^m(l) ->
                        not_state_contains (eq locC(l)) S;
}.

Notation scount c S := (sweight (identify c) S).

Record HLPL_plus_well_formed_alt (S : HLPL_plus_state) l : Prop := {
  unique_borrow_mut_alt : scount (borrowC^m(l)) S <= 1;
  no_mut_loan_loc_alt : scount (loanC^m(l)) S + scount (locC(l)) S <= 1;
  no_mut_loan_ptr_alt : scount (loanC^m(l)) S <= 0 \/ scount (ptrC(l)) S <= 0;
}.

Lemma well_formedness_equiv S : HLPL_plus_well_formed S <-> forall l, HLPL_plus_well_formed_alt S l.
Admitted.

(* TODO: move *)
(* Rewriting weight_arity_0 and weight_arity_1 using goals of the form "get_constructor S.[p] = c".
   I couldn't do it with autorewrite, so I'm using this strang tactic instead. *)
Ltac weight_given_constructor :=
  lazymatch goal with
  | H : get_constructor (?S.[?p]) = _ |- context [total_weight _ (?S.[?p])] =>
    let G := fresh in
    pose proof (G := H);
    apply (f_equal arity) in G;
    (eapply weight_arity_0 in G || eapply weight_arity_1 in G);
    rewrite G, H;
    clear G
  end.

Lemma total_weight_loc weight l v :
  total_weight weight (loc(l, v)) = weight (locC(l)) + total_weight weight v.
Proof. reflexivity. Qed.
Hint Rewrite total_weight_loc : weight.

Lemma total_weight_ptr weight l : total_weight weight (ptr(l)) = weight (ptrC(l)).
Proof. reflexivity. Qed.
Hint Rewrite total_weight_ptr : weight.

Ltac prove_weight_inequality :=
  (* Translate the inequality into relatives, and repeatedly rewrite sweight_sset. *)
  autorewrite with weight spath;
  (* Use the hypotheses "get_constructor S.[p] = c" to further rewrite the formula. *)
  repeat weight_given_constructor;
  (* Final rewriting. *)
  autorewrite with weight spath;
  lia
.
(* TODO: give names to hypotheses. *)
Global Program Instance HLPL_plus_state_le_base : LeBase HLPL_plus_binder HLPL_plus_val :=
{ le_base := le_state_base;
  anon := Anon;
  well_formed := HLPL_plus_well_formed;
}.
Next Obligation.
  rewrite well_formedness_equiv. rewrite well_formedness_equiv in H.
  intro l0. specialize (H l0). destruct H. destruct H0.
  - destruct (Nat.eq_dec l0 l) as [<- | ]; split; prove_weight_inequality.
Qed.

(* TODO: move *)
(* Proving a comparison between p and q using information from the environment S. *)
Lemma spath_neq_by_value_constructor (S : HLPL_plus_state) p q v c :
  S.[p] = v -> get_constructor (S.[q]) = c -> get_constructor v <> c -> p <> q.
Proof. congruence. Qed.
Hint Extern 3 (~ (@eq spath _ _)) =>
  simple eapply spath_neq_by_value_constructor; [eassumption | eassumption | discriminate] : spath.

Hint Extern 0 (~ (@eq spath _ _)) => congruence : spath.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l0 : loan_id).
  Context (sp_loan sp_borrow : spath).
  Context (Hdisj : disj sp_loan sp_borrow).
  Hypothesis (HS_r_loan : get_constructor (S_r.[sp_loan]) = loanC^m(l0)).
  Hypothesis (HS_r_borrow : get_constructor (S_r.[sp_borrow]) = borrowC^m(l0)).
  Notation v := (S_r.[sp_borrow +++ [0] ]).
  Notation S_l := (S_r.[sp_loan <- loc(l0, v)].[sp_borrow <- ptr(l0)]).
  Context (perm : permission).

  (* TODO: name *)
  Inductive rel : spath -> spath -> Prop :=
    | Rel_sp_borrow_strict_prefix q : rel (sp_loan +++ [0] ++ q) (sp_borrow +++ [0] ++ q)
  | Rel_other q : ~strict_prefix sp_borrow q -> rel q q.

  (* An equivalent (and more usable I hope) version of rel. *)
  Definition rel' p q :=
    (exists r, p = sp_loan +++ [0] ++ r /\ q = sp_borrow +++ [0] ++ r) \/
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
    destruct (decidable_prefix sp_borrow q) as [ | ].
    - assert (prefix (sp_borrow +++ [0]) q) as (r & <-) by eauto with spath.
      autorewrite with spath in H.
      exists (sp_loan +++ [0] ++ r). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + autorewrite with spath. assumption.
    - exists q. split.
      (* comparison reasonning: *)
      + apply Rel_other. auto with spath.
      + autorewrite with spath.
        assert (~strict_prefix sp_loan q). eauto with spath.
        assumption.
  Qed.

  Lemma eval_proj_mut_sp_borrow_strict_prefix proj r q
    (H : eval_proj S_r perm proj (sp_borrow +++ [0] ++ r) q) :
    exists q', rel q' q /\ eval_proj S_l perm proj (sp_loan +++ [0] ++ r) q'.
  Proof.
    remember (sp_borrow +++ [0] ++ r) as p. revert r Heqp. induction H; intros r ->.
    - exists ((sp_loan +++ [0] ++ r) +++ [0]). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + apply Eval_Deref_MutBorrow with (l := l); try assumption.
        autorewrite with spath. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try assumption.
      rewrite sget_app in *. autorewrite with spath in *. assumption.
    - specialize (IHeval_proj (r ++ [0])). destruct IHeval_proj as (q'' & ? & ?).
      + rewrite<- app_spath_vpath_assoc. reflexivity.
      + exists q''. split; try assumption.
        apply Eval_Loc with (l := l).
        * assumption.
        * autorewrite with spath. assumption.
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
        autorewrite with spath. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try auto.
      autorewrite with spath. assumption.
    - destruct IHeval_proj as (r' & ? & ?).
      { intros G%strict_prefix_app_last; revert G. reduce_comp. }
      exists r'. split; try assumption. apply Eval_Loc with (l := l); try easy.
      autorewrite with spath. assumption.
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

(* Suppose that Sl <= Sr (with a base case), and that p evaluates to a spath pi in Sr
   (Sr |-{p} p =>^{perm} pi).
   This tactic chooses the right lemmas to apply in order to prove that p reduces to a spath pi' in Sl, and generates facts about pi'.
   Finally, it proves that pi is valid in Sr, and clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  lazymatch goal with
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{Mov} ?pi,
    _ : get_constructor (?Sr.[?sp_loan]) = loanC^m (?l),
    _ : get_constructor (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let sp_borrow_not_prefix := fresh "sp_borrow_not_prefix" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as eval_p_in_Sl;
      pose proof eval_p_in_Sr as sp_borrow_not_prefix;
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_mut_borrow_to_ptr_Mov
        with (sp_loan := sp_loan) (sp_borrow := sp_borrow) (l0 := l)
        in eval_p_in_Sl;
      apply eval_place_mut_borrow_to_ptr_Mov_comp with (sp_borrow := sp_borrow)
        in sp_borrow_not_prefix;
      apply eval_place_valid in valid_p;
      clear eval_p_in_Sr
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{ _ } ?pi_r,
    Hdisj : disj ?sp_loan ?sp_borrow,
    HSr_loan : get_constructor (?Sr.[?sp_loan]) = loanC^m (?l),
    HSr_borrow : get_constructor (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
      let pi_l := fresh "pi_l" in
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_valid in valid_p;
      apply (eval_place_mut_borrow_to_ptr Sr l sp_loan sp_borrow Hdisj HSr_loan HSr_borrow)
        in eval_p_in_Sr;
      destruct eval_p_in_Sr as (pi_l & rel_pi_l_pi_r%rel_implies_rel' & eval_p_in_Sl)
  end.

Lemma operand_preserves_HLPL_plus_rel op : preservation (eval_operand op).
Proof.
  preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = const n *)
  - destruct Hle.
    + eapply complete_square_diagram.
      * eapply prove_le_state_val.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * constructor.
      * reflexivity.
  (* op = copy p *)
  - admit.
  (* op = move p *)
  - destruct Hle.
    (* Le-MutBorrow-To-Ptr *)
    + eval_place_preservation.
      assert (disj pi sp_loan) by reduce_comp.
      destruct (decidable_prefix pi sp_borrow) as [(q & <-) | ].
      (* Case 1: the mutable borrow we're transforming to a pointer is in the moved value. *)
      * eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := (length S, q)).
             (*auto with spath.*) admit. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: autounfold with spath; prove_not_contains.
        -- autorewrite with spath. f_equal. prove_states_eq.
      (* Case 2: the mutable borrow we're transforming to a pointer is disjoint to the moved value.
       *)
      * assert (disj pi sp_borrow) by reduce_comp.
        eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: autorewrite with spath; assumption.
        -- autorewrite with spath. f_equal. prove_states_eq.
Admitted.

Lemma le_base_implies_le S0 S1 : le_base S0 S1 -> le S0 S1.
Proof. now constructor. Qed.

Lemma rvalue_preserves_HLPL_plus_rel rv : preservation (eval_rvalue rv).
Proof.
  preservation_by_base_case.
  intros ? ? Heval. destruct Heval.
  (* rv = just op *)
  - apply operand_preserves_HLPL_plus_rel in Heval_op.
    intros ? ?%le_base_implies_le.
    firstorder using Eval_just.
  (* rv = op + op *)
  - apply operand_preserves_HLPL_plus_rel in H, H0.
    intros S0 Hle%le_base_implies_le.
    admit.
  (* rv = &mut p *)
  (* The place p evaluates to a spath under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      (* Case 1: the place p is under the borrow. *)
      * destruct r; autorewrite with spath in Hancestor_loc.
        (* The place p cannot be just under the borrow, because its ancestor is a loc, it cannot be
         * the mutable borrow. *)
        { congruence. }
        eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- eapply Eval_pointer_loc. eassumption. autorewrite with spath. exact Hancestor_loc.
        -- reflexivity.
      (* Case 2: the place p is not under the borrow. *)
      * eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- eapply Eval_pointer_loc. eassumption. autorewrite with spath. exact Hancestor_loc.
        -- reflexivity.
  (* rv = &mut p *)
  (* The place p evaluates to a spath that is not under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      * destruct r.
        (* Case 1: the place p is just under sp_borrow. *)
        -- rewrite app_nil_r in *. eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              (* This requires to apply the rule Le-Merge-Locs, that we have not defined yet. *)
              admit.
           ++ apply Eval_pointer_loc with (pi := sp_loan +++ [0]).
              assumption. autorewrite with spath. reflexivity.
           ++ admit.
        (* Case 2: the place p is just under sp_borrow, but not just under. *)
        -- eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              all: autorewrite with spath. autorewrite with spath in Hancestor_no_loc.
              exact Hancestor_no_loc. assumption. prove_not_contains.
           ++ f_equal. prove_states_eq.
      (* Case 3: *)
      * assert (disj sp_loan pi) by reduce_comp.
        destruct (decidable_prefix pi sp_borrow) as [(r & <-) | ].
        -- eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := pi +++ [0] ++ r).
                auto with spath. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. assumption. all: autounfold with spath; prove_not_contains.
           ++ f_equal. autorewrite with spath. prove_states_eq.
        -- assert (disj sp_borrow pi) by reduce_comp.
           eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                assumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. assumption. all: autounfold with spath; prove_not_contains.
           ++ f_equal. autorewrite with spath. prove_states_eq.
Admitted.

Hint Extern 0 (not_value_contains _ _) => prove_not_contains0 : spath.
Lemma eval_rvalue_no_loan_loc S rv vS' : S |-{rv} rv => vS' ->
  not_contains_loan (fst vS') /\ not_contains_loc (fst vS').
Proof.
  intro H. destruct H; [destruct Heval_op | ..].
  all: auto with spath.
  induction Hcopy_val; auto with spath.
Qed.

Lemma eval_path_app_last S v p k pi :
  not_contains_loc v -> (S,, Anon |-> v) |-{p} p =>^{k} pi -> S |-{p} p =>^{k} pi.
Proof.
  destruct p as (x & q). intros no_loc (i & H & G). exists i. cbn.
  assert (find_binder S (Var x) = Some i).
  { apply find_binder_Some in H. destruct H as (Hi & Hi_min).
    destruct (Nat.lt_ge_cases i (length S)) as [ |  ].
    + apply find_binder_Some.
      rewrite nth_error_app1 in Hi by assumption. split; [exact Hi | ].
      intros j j_lt_i. specialize (Hi_min j j_lt_i).
      rewrite nth_error_app1 in Hi_min by (etransitivity; eassumption).
      assumption.
    + rewrite nth_error_app2 in Hi by auto using Nat.lt_le_incl.
      destruct (i - length S).
      * discriminate.
      * cbn in Hi. rewrite nth_error_nil in Hi. discriminate.
  }
  split; [assumption | ].
  cbn in *. assert (valid_pi0 : valid_spath S (i, [])) by eauto using find_binder_valid.
  apply proj1 with (B := valid_spath S (i, [])). induction G.
  + split. constructor. exact valid_pi0.
  + assert (eval_proj S k proj p q).
    { clear IHG. induction Heval_proj; autorewrite with spath in get_q.
      - eapply Eval_Deref_MutBorrow; eassumption.
      - eapply Eval_Deref_Ptr_Locs; [eassumption.. | ].
        assert (valid_q' : valid_spath (S,, Anon |-> v) q') by solve_validity.
        apply valid_spath_app_last_cases in valid_q'.
        destruct valid_q'; autorewrite with spath in get_q'.
        + exact get_q'.
        + exfalso. apply no_loc with (p := snd q'); [solve_validity | ].
          rewrite get_q'. constructor.
      - eapply Eval_Loc; eauto with spath.
    }
    destruct IHG.
    { eapply eval_proj_valid. eassumption. }
    split; [ econstructor | ]; eassumption.
Qed.

Lemma state_app_last_eq (Sl Sr : HLPL_plus_state) bl br vl vr :
  (Sl,, bl |-> vl) = (Sr,, br |-> vr) -> Sl = Sr /\ vl = vr.
Proof. intros (? & ?)%app_inj_tail. split; congruence. Qed.

(* Suppose that (v0, S0) <= (vn, Sn), and that vr does not contain any loan.
   Let us take (v1, S1), ..., (v_{n-1}, S_{n-1}) the intermediate pairs such that
   (v0, S0) <= (v1, S1) <= ... <= (vn, Sn).
   Then, we are going to prove that for each (vi, Si), the value vi does not contain any loan. *)
Definition le_val_state_base' (vSl vSr : HLPL_plus_val * HLPL_plus_state) : Prop :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  le_base (Sl,, Anon |-> vl) (Sr,, Anon |-> vr) /\ not_contains_loan vr /\ not_contains_loc vr.
Notation le_val_state' := (refl_trans_closure le_val_state_base').

Lemma le_base_does_not_insert_loan_loc vl Sl vr Sr :
  le_base (Sl,, Anon |-> vl) (Sr,, Anon |-> vr) -> not_contains_loan vr -> not_contains_loc vr
  -> not_contains_loan vl /\ not_contains_loc vl.
Proof.
  remember (Sl,, Anon |-> vl) as vSl. remember (Sr,, Anon |-> vr) as vSr.
  intros Hle Hno_loan Hno_loc. destruct Hle; subst.
  - assert (valid_spath Sr sp_loan).
    (* TODO: this piec of reasonning is used several times. Automate it. *)
    { assert (valid_sp_loan : valid_spath (Sr,, Anon |-> vr) sp_loan) by solve_validity.
      apply valid_spath_app_last_cases in valid_sp_loan. destruct valid_sp_loan.
      - assumption.
      - autorewrite with spath in HS_loan. exfalso.
        eapply Hno_loan; [ | rewrite HS_loan; constructor]. solve_validity.
    }
    assert (valid_sp_borrow : valid_spath (Sr,, Anon |-> vr) sp_borrow) by solve_validity.
    apply valid_spath_app_last_cases in valid_sp_borrow. destruct valid_sp_borrow.
    + autorewrite with spath in HeqvSl.
      apply state_app_last_eq in HeqvSl. destruct HeqvSl as (_ & <-). auto.
    + autorewrite with spath in HeqvSl.
      apply state_app_last_eq in HeqvSl. destruct HeqvSl as (_ & <-).
      auto with spath.
Qed.

Lemma le_val_state_no_loan_right (vSl vSr : HLPL_plus_val * HLPL_plus_state) :
  le vSl vSr -> not_contains_loan (fst vSr) -> not_contains_loc (fst vSr)
  -> le_val_state' vSl vSr.
Proof.
  intros Hle Hno_loan Hno_loc.
  apply proj1 with (B := (not_contains_loan (fst vSl)) /\ (not_contains_loc (fst vSl))).
  induction Hle as [vSl vSr | | x y z].
  - split.
    + constructor. destruct vSl, vSr. cbn. auto.
    + destruct vSl. destruct vSr. eapply le_base_does_not_insert_loan_loc; eauto.
  - split; [reflexivity | auto].
  - split; [transitivity y | ]; tauto.
Qed.

Lemma store_preserves_HLPL_plus_rel p :
  forward_simulation le_val_state' le (store p) (store p).
Proof.
  apply preservation_by_base_case.
  intros vSr Sr' Hstore vSl Hle.
  destruct vSl as (vl, Sl) eqn:?. destruct vSr as (vr, Sr) eqn:?.
  destruct Hle as (Hle & no_loan & no_loc). inversion Hstore. subst. clear Hstore.
  assert (valid_spath Sr sp).
  { eapply eval_path_app_last in eval_p; eauto with spath. }
  remember (Sl,, Anon |-> vl) eqn:HeqvSl. remember (Sr,, Anon |-> vr).
  destruct Hle; subst.
  - eval_place_preservation. clear valid_p.
    assert (valid_sp_loan : valid_spath (Sr,, Anon |-> vr) sp_loan) by solve_validity.
    apply valid_spath_app_last_cases in valid_sp_loan.
    destruct valid_sp_loan.
    2: { autorewrite with spath in HS_loan. exfalso.
      eapply no_loan; [ | rewrite HS_loan ]. solve_validity. constructor. }
    autorewrite with spath in HS_loan |-.
    destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
    (* Case 1: the place sp where we write is inside the borrow. *)
    + assert (valid_spath Sr sp_borrow) by (eapply valid_spath_app; eassumption).
      autorewrite with spath in HS_borrow, HeqvSl. apply state_app_last_eq in HeqvSl.
      destruct HeqvSl as (<- & ->). autorewrite with spath in eval_p_in_Sl.
      eapply complete_square_diagram.
      * constructor.
        eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption.
      * constructor. eassumption.
        all: autorewrite with spath; assumption.
      * autorewrite with spath. f_equal. prove_states_eq.
    + assert (valid_sp_borrow : valid_spath (Sr,, Anon |-> vr) sp_borrow) by solve_validity.
      apply valid_spath_app_last_cases in valid_sp_borrow.
      destruct valid_sp_borrow as [valid_sp_borrw | ]; autorewrite with spath in HS_borrow.
      * autorewrite with spath in HeqvSl. apply state_app_last_eq in HeqvSl.
        destruct HeqvSl. subst.
        autorewrite with spath in eval_p_in_Sl.
        destruct (decidable_prefix sp sp_borrow) as [(r_borrow & <-) | ].
        (* Case 2: the borrow is inside the place we write in. *)
        -- destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r_loan))
                                                 (sp_borrow := (length Sr, r_borrow)).
                  eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption.
                 all: prove_not_contains_outer.
              ** autorewrite with spath. reflexivity.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := (length Sr, r_borrow)).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
        (* Case 3: the borrow is disjoint from the place we write in. *)
        -- assert (disj sp sp_borrow) by reduce_comp.
           destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r_loan))
                                                 (sp_borrow := sp_borrow).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := sp_borrow).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
      (* Case 4: the borrow is inside the evaluated value. *)
      * destruct sp_borrow as (i & q). cbn in H2. subst i.
        autorewrite with spath in HS_borrow.
        autorewrite with spath in eval_p_in_Sl.
        autorewrite with spath in HeqvSl. apply state_app_last_eq in HeqvSl.
        destruct HeqvSl. subst.
        destruct (decidable_prefix sp sp_loan) as [(r & <-) | ].
        (* Case 4a: the loan is in the place we write in. *)
        -- eapply complete_square_diagram.
           ++ constructor.
              eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r))
                                              (sp_borrow := sp +++ q).
              eauto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eassumption. all: prove_not_contains_outer.
           ++ autorewrite with spath. reflexivity.
        (* Case 4b: the loan is disjoint to the place we write in. *)
        -- assert (disj sp sp_loan) by reduce_comp.
           eapply complete_square_diagram.
           ++ constructor.
              eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp +++ q).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eassumption. all: prove_not_contains_outer.
           ++ autorewrite with spath. f_equal. prove_states_eq.
Qed.

Definition measure_node c :=
  match c with
  | loanC^m(_) => 2
  | borrowC^m(_) => 1
  | locC(_) => 1
  | ptrC(_) => 1
  | _ => 0
  end.

Lemma measure_mut_loan l : measure_node loanC^m(l) = 2. Proof. reflexivity. Qed.
Hint Rewrite measure_mut_loan : weight.
Lemma measure_mut_borrow l : measure_node borrowC^m(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_mut_borrow : weight.
Lemma measure_loc l : measure_node locC(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_loc : weight.
Lemma measure_ptr l : measure_node ptrC(l) = 1. Proof. reflexivity. Qed.
Hint Rewrite measure_ptr : weight.
Lemma measure_bot : total_weight measure_node bot = 0. Proof. reflexivity. Qed.
Hint Rewrite measure_bot : weight.

Lemma reorg_preserves_HLPL_plus_rel : well_formed_preservation (refl_trans_closure reorg).
Proof.
  eapply preservation_reorg with (measure := @sweight _ ValueHLPL _ measure_node).
  { intros Sl Sr Hle. destruct Hle; prove_weight_inequality. }
  { intros ? ? Hreorg. destruct Hreorg; prove_weight_inequality. }
  { admit. }
  intros Sr Sr' WF_Sr reorg_Sr_Sr'. destruct reorg_Sr_Sr'.
  (* Case Reorg_end_borrow_m: *)
  - intros ? Hle. destruct Hle.
    + destruct (Nat.eq_dec l l0) as [<- | ].
      (* Case 1: l = l0. By well-formedness, that means that the loan that we end at p is the loan
         that we turn into a loc at sp_loan, and that the borrow that we end at q is the
         borrow we turn into a pointer at sp_borrow. *)
      * assert (p = sp_loan) as ->.
        { eapply unique_loan_mut. eassumption.
          rewrite H0. reflexivity. rewrite HS_loan. reflexivity. }
        assert (q = sp_borrow) as ->.
        { eapply unique_borrow_mut. eassumption.
          rewrite H1. reflexivity. assumption. }
        eapply complete_square_diagram.
        -- reflexivity.
        -- etransitivity.
           { constructor. eapply Reorg_end_ptr with (p := sp_borrow).
             autorewrite with spath. reflexivity. }
           { constructor. eapply Reorg_end_loc with (p := sp_loan).
             autorewrite with spath. reflexivity.
             assert (not_state_contains (eq ptrC(l)) S).
             { eapply no_mut_loan_ptr. eassumption. rewrite HS_loan. reflexivity. }        rewrite sset_twice_equal. (* TODO: automatic rewriting. *)
             prove_not_contains. }
        -- prove_states_eq.
      * assert (q <> sp_borrow) by congruence.
        assert (~strict_prefix sp_borrow q). { apply H3. rewrite HS_borrow. constructor. }
        assert (disj p sp_loan) by reduce_comp.
        assert (disj q sp_loan) by reduce_comp.
        destruct (decidable_prefix q sp_borrow).
        (* Case 2: the borrow we turn into a pointer is inside the borrow we end. *)
        -- assert (strict_prefix q sp_borrow) by auto with spath.
           assert (prefix (q +++ [0]) sp_borrow) as (r & <-) by eauto with spath.
           autorewrite with spath in *.
           eapply complete_square_diagram.
           ++ constructor.
              apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ r).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eapply Reorg_end_borrow_m with (p := p) (q := q).
              assumption. all: autorewrite with spath. eassumption. assumption.
              prove_not_contains. auto with spath.
           ++ autorewrite with spath. prove_states_eq.
        -- assert (disj q sp_borrow) by reduce_comp.
           destruct (decidable_prefix sp_borrow p).
           (* Case 3: the loan that we end is is the borrow that we turn into a pointer. *)
           ++ assert (strict_prefix sp_borrow p)  by auto with spath.
              assert (prefix (sp_borrow +++ [0]) p) as (r & <-) by eauto with spath.
              rewrite<- (app_spath_vpath_assoc sp_borrow [0] r) in * |-.
              eapply complete_square_diagram.
              ** constructor.
                 apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_borrow_m with (p := sp_loan +++ [0] ++ r) (q := q).
                 auto with spath. all: autorewrite with spath. eassumption.
                 assumption. assumption. auto with spath.
              ** autorewrite with spath. prove_states_eq.
           (* Case 4: the loan that we end is disjoint from the borrow that we turn into a pointer. 
           *)
           ++ assert (disj sp_borrow p) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_borrow_m with (p := p) (q := q).
                 assumption. all: autorewrite with spath. eassumption.
                 assumption. assumption. auto with spath.
              ** autorewrite with spath. prove_states_eq.
  - intros ? Hle. destruct Hle.
    + destruct (decidable_prefix sp_borrow p).
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by eauto with spath.
        rewrite<- (app_spath_vpath_assoc sp_borrow [0] q) in *.
        eapply complete_square_diagram.
        -- constructor.
           eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_ptr with (p := sp_loan +++ [0] ++ q).
           autorewrite with spath. eassumption.
        -- autorewrite with spath. prove_states_eq.
      * assert (disj sp_borrow p) by reduce_comp.
        assert (disj sp_loan p) by reduce_comp.
        eapply complete_square_diagram.
        -- constructor.
           eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_ptr with (p := p). autorewrite with spath. eassumption.
        -- autorewrite with spath. prove_states_eq.
  - intros ? Hle. destruct Hle.
    + assert (l <> l0).
      { intros <-. eapply no_mut_loan_loc; [ eassumption.. | | symmetry; eassumption].
        solve_validity. }
      destruct (decidable_prefix sp_borrow p).
      (* Case 1: the loc we end is is the borrow we turn into a pointer. *)
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by eauto with spath.
        autorewrite with spath in *.
        eapply complete_square_diagram.
        -- constructor.
           eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_loc with (p := sp_loan +++ [0] ++ q).
           autorewrite with spath. eassumption. prove_not_contains. cbn. congruence.
        -- autorewrite with spath. prove_states_eq.
      * destruct (decidable_prefix p sp_borrow).
        -- assert (prefix (p +++ [0]) sp_borrow) as (q & <-) by eauto with spath.
           destruct (decidable_prefix p sp_loan).
           (* Case 2: the loan and the borrow we turn into a location and a pointer are in the loc
            * we end. *)
           ++ assert (prefix (p +++ [0]) sp_loan) as (r & <-) by eauto with spath.
              assert (vdisj q r) by eauto with spath.
              autorewrite with spath in *.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := p +++ q).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: prove_not_contains. cbn. congruence.
              ** autorewrite with spath. reflexivity.
           (* Case 3: the borrow we turn into a pointer is in the location we end, but the loan we
            * turn into a location is disjoint. *)
           ++ assert (disj p sp_loan) by reduce_comp.
              autorewrite with spath in *.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ q).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: prove_not_contains. cbn. congruence.
              ** autorewrite with spath. prove_states_eq.
        -- assert (disj p sp_borrow) by reduce_comp.
           destruct (decidable_prefix p sp_loan).
           (* Case 4: the loan we turn into a location is in the location we end, but the borrow we
            * turn into a pointer is disjoint. *)
           ++ assert (prefix (p +++ [0]) sp_loan) as (r & <-) by eauto with spath.
              rewrite<- app_spath_vpath_assoc in *.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := sp_borrow).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: prove_not_contains. cbn. congruence.
              ** autorewrite with spath. prove_states_eq.
           (* Case 5: the loan and the borrow we turn into a location and a pointer are in the loc
            * we end. *)
           ++ assert (disj p sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: prove_not_contains. cbn. congruence.
              ** autorewrite with spath. prove_states_eq.
Admitted.

Lemma stmt_preserves_HLPL_plus_rel s r : well_formed_preservation (eval_stmt s r).
Proof.
  intros Sr Sr' WF_Sr Heval Sl Hle. revert Sl Hle. induction Heval; intros Sl Hle.
  - eexists. split; [eassumption | constructor].
  - specialize (IHHeval1 WF_Sr _ Hle).
    destruct IHHeval1 as (Sl' & ? & ?).
    edestruct IHHeval2 as (Sl'' & ? & ?); [ | eassumption | ].
    { admit. }
    exists Sl''. split; [assumption | ]. eapply Eval_seq_unit; eassumption.
  - specialize (IHHeval WF_Sr _ Hle).
    destruct IHHeval as (Sl' & ? & ?).
    exists Sl'. split; [assumption | ].
    apply Eval_seq_panic. assumption.
  - pose proof (_eval_rv := eval_rv). apply rvalue_preserves_HLPL_plus_rel in _eval_rv.
    destruct (_eval_rv _ Hle) as (vSl' & le_vSl_vS' & eval_Sl).
    apply store_preserves_HLPL_plus_rel in Hstore.
    apply le_val_state_no_loan_right in le_vSl_vS';
      [ | eapply eval_rvalue_no_loan_loc; exact eval_rv..].
    destruct (Hstore _ le_vSl_vS') as (Sl'' & le_Sl'' & store_vSl').
    exists Sl''. split; [assumption | ]. econstructor; eassumption.
  - apply reorg_preserves_HLPL_plus_rel in Hreorg; [ | assumption].
    destruct (Hreorg _ Hle) as (Sl1 & le_Sl1 & reorg_Sl1).
    edestruct IHHeval as (Sl2 & le_Sl2 & eval_in_Sl2); [ | eassumption | ].
    { admit. }
    exists Sl2. split; [assumption | ].
    apply Eval_reorg with (S1 := Sl1); assumption.
Admitted.
