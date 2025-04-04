Require Import lang.
Require Import base.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
Require Import Lia ZArith.
Require Import Relations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

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

Variant HLPL_plus_nodes :=
| HLPL_plus_botC
| HLPL_plus_intC (n : nat)
| HLPL_plus_mut_loanC (l : loan_id)
| HLPL_plus_mut_borrowC (l : loan_id)
| HLPL_plus_locC (l : loan_id)
| HLPL_plus_ptrC (l : loan_id)
.

Instance EqDec_HLPL_plus_nodes : EqDecision HLPL_plus_nodes.
Proof. unfold EqDecision, Decision. repeat decide equality. Qed.

Definition HLPL_plus_arity c := match c with
| HLPL_plus_botC => 0
| HLPL_plus_intC _ => 0
| HLPL_plus_mut_loanC _ => 0
| HLPL_plus_mut_borrowC _ => 1
| HLPL_plus_locC _ => 1
| HLPL_plus_ptrC _ => 0
end.

Definition HLPL_plus_get_node v := match v with
| HLPL_plus_bot => HLPL_plus_botC
| HLPL_plus_int n => HLPL_plus_intC n
| HLPL_plus_mut_loan l => HLPL_plus_mut_loanC l
| HLPL_plus_mut_borrow l _ => HLPL_plus_mut_borrowC l
| HLPL_plus_loc l _ => HLPL_plus_locC l
| HLPL_plus_ptr l => HLPL_plus_ptrC l
end.

Definition HLPL_plus_children v := match v with
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
  | v => node_weight (HLPL_plus_get_node v)
end.

Program Instance ValueHLPL : Value HLPL_plus_val HLPL_plus_nodes := {
  arity := HLPL_plus_arity;
  get_node := HLPL_plus_get_node;
  children := HLPL_plus_children;
  fold_value := HLPL_plus_fold;
  vweight := HLPL_plus_weight;
  bot := HLPL_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_node eq_children; inversion eq_node; inversion eq_children; reflexivity.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] ];
  reflexivity.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] ];
  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; unfold HLPL_plus_children; cbn; lia. Qed.

Record HLPL_plus_state := {
  vars : Pmap HLPL_plus_val;
  anons : Pmap HLPL_plus_val;
}.

Definition encode_var (x : var) := encode (A := var + anon) (inl x).
Definition encode_anon (a : positive) := encode (A := var + anon) (inr a).

Program Instance IsState : State HLPL_plus_state HLPL_plus_val (H := ValueHLPL) := {
  extra := unit;
  get_map S := sum_maps (vars S) (anons S);
  get_extra _ := ();
  alter_at_accessor f a S :=
    match decode' (A := var + anon) a with
    | Some (inl x) => {| vars := alter f x (vars S); anons := anons S|}
    | Some (inr a) => {| vars := vars S; anons := alter f a (anons S)|}
    | None => S
    end;
  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := var + anon) x with
    | Some (inr a) => Some a
    | _ => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
}.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? i. cbn. destruct (decode' i) eqn:H.
  - rewrite decode'_is_Some in H.
    destruct s; cbn; rewrite <-H; symmetry;
      first [apply sum_maps_alter_inl | apply sum_maps_alter_inr].
  - symmetry. apply map_alter_not_in_domain, sum_maps_lookup_None. assumption.
Qed.
Next Obligation. intros [? ?] [? ?]. cbn. intros (-> & ->)%sum_maps_eq _. reflexivity. Qed.
(* What are the two following obligations? *)
Next Obligation. discriminate. Qed.
Next Obligation. discriminate. Qed.
Next Obligation. intros. cbn. symmetry. apply sum_maps_insert_inr. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. unfold encode_anon. rewrite decode_encode. reflexivity. Qed.


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

(* This property represents the application of a projection p (such as a pointer dereference or a
 * field access) on spath pi0, on a state S and given a permission perm.
 * If this projection is successful, then we have eval_proj S perm p pi0 pi1.
 *)
Inductive eval_proj (S : HLPL_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : @get_node HLPL_plus_val HLPL_plus_nodes _ _ (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| Eval_Deref_Ptr_Locs q q' l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = ptrC(l)) (get_q' : get_node (S.[q']) = locC(l)) :
    eval_proj S perm Deref q (q' +++ [0])
(* Coresponds to R-Loc and W-Loc in the article. *)
| Eval_Loc proj q q' l
    (Hperm : perm = Imm)
    (get_q : get_node (S.[q]) = locC(l))
    (eval_proj_rec : eval_proj S perm proj (q +++ [0]) q') : eval_proj S perm proj q q'
.

(* Let pi0 be a spath. If by successfully applying the projections in P (with permission perm) we
   obtain a spath pi1, then we have the proprety eval_path S perm P pi0 pi1. *)
Inductive eval_path (S : HLPL_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd p) (encode_var (fst p), []) pi.

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
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loan : HLPL_plus_nodes -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Variant is_loc : HLPL_plus_nodes -> Prop :=
| IsLoc_Loc l : is_loc (locC(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.
Hint Extern 0 (~is_loc _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Variant is_mut_borrow : HLPL_plus_nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).
Notation not_contains_outer_loc := (not_contains_outer is_mut_borrow is_loc).

Definition not_in_borrow S (p : spath) :=
  forall q, is_mut_borrow (get_node (S.[q])) -> ~strict_prefix q p.

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
      apply not_contains_outer_sset_no_contains;
        [not_contains_outer | exact H | exact loc_is_not_bot || exact loan_is_not_bot]
  | no_outer_loan : not_contains_outer_loan (?S.[?q]),
    loan_at_q : get_node (?S.[?q +++ ?p]) = loanC^m(?l)
    |- not_contains_outer _ ?P (?S.[?q].[[?p <- ?w]]) =>
    apply not_contains_outer_sset_in_borrow;
     [ not_contains_outer |
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

Lemma is_fresh_loan_id_neq (S : HLPL_plus_state) l0 l1 (p : spath) :
  get_loan_id (get_node (S.[p])) = Some l0 -> is_fresh l1 S -> l0 <> l1.
Proof.
  intros get_p Hfresh <-. eapply Hfresh; [ | exact get_p].
  apply get_not_bot_valid_spath. intro H. rewrite H in get_p. inversion get_p.
Qed.

Hint Extern 0 (get_loan_id _ <> Some ?l) =>
  lazymatch goal with
  | Hfresh : is_fresh ?l ?S, get_p : get_node (?S.[?p]) = ?v |- _ =>
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

(* Note: these functions are used when borrowing a spath that is already under a location without
 * introducing a new location. spath_pred pi given the node about pi (and botC if this node doesn't
 * exist).
 * However, I should maybe rewrite it with a proposition instead of a function. *)
(* TODO: if I keep it, move in PathToSubtree.v *)
Definition vpath_pred (p : vpath) : option vpath :=
  match p with
  | [] => None
  | _ => Some (removelast p)
  end.

Definition spath_pred (p : spath) : option spath :=
  SOME q <- vpath_pred (snd p) IN Some (fst p, q).

Lemma vpath_pred_add_anon p i : vpath_pred (p ++ [i]) = Some p.
Proof.
  transitivity (Some (removelast (p ++ [i]))).
  - destruct (p ++ [i]) eqn:?.
    + exfalso. eapply app_cons_not_nil. eauto.
    + reflexivity.
  - f_equal. apply removelast_last.
Qed.

Lemma spath_pred_add_anon (p : spath) i : spath_pred (p +++ [i]) = Some p.
Proof.
  unfold spath_pred, app_spath_vpath. cbn. rewrite vpath_pred_add_anon.
  rewrite<- surjective_pairing. reflexivity.
Qed.

Lemma spath_pred_is_Some (p q : spath) : spath_pred p = Some q -> exists i, p = q +++ [i].
Proof.
  unfold spath_pred. intro.
  assert (snd p <> []) by now destruct (snd p).
  assert ((fst p, removelast (snd p)) = q) as <-.
  { destruct (snd p); [discriminate | injection H; easy]. }
  exists (List.last (snd p) 0). unfold app_spath_vpath. cbn.
  rewrite<- app_removelast_last by assumption.
  apply surjective_pairing.
Qed.

Definition vancestor (v : HLPL_plus_val) p : HLPL_plus_nodes :=
  match vpath_pred p with
  | None => botC
  | Some q => get_node (v.[[q]])
  end.

Definition ancestor (S : HLPL_plus_state) (p : spath) : HLPL_plus_nodes :=
  match spath_pred p with
  | None => botC
  | Some q => get_node (S.[q])
  end.

Lemma vancestor_singleton v i : vancestor v [i] = get_node v.
Proof. reflexivity. Qed.
Hint Rewrite vancestor_singleton : spath.

Lemma ancestor_sset_not_strict_prefix S p q v :
  ~strict_prefix q p -> ancestor (S.[q <- v]) p = ancestor S p.
Proof.
  unfold ancestor. intro. autodestruct.
  intros (? & ->)%spath_pred_is_Some.
  rewrite get_node_sset_sget_not_prefix by auto with spath. reflexivity.
Qed.
Hint Rewrite ancestor_sset_not_strict_prefix using auto with spath; fail : spath.

Lemma ancestor_is_not_bot S p c :
  ancestor S p = c -> c <> botC -> exists q i, p = q +++ [i] /\ get_node (S.[q]) = c.
Proof.
  unfold ancestor. autodestruct. intros (i & ->)%spath_pred_is_Some.
  intros. eexists _, _. eauto.
Qed.

Lemma vancestor_app v p q : q <> [] -> vancestor v (p ++ q) = vancestor (v.[[p]]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold vancestor. rewrite app_assoc, !vpath_pred_add_anon, vget_app.
  reflexivity.
Qed.

Lemma ancestor_app S p q : q <> [] -> ancestor S (p +++ q) = vancestor (S.[p]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold ancestor, vancestor.
  rewrite app_spath_vpath_assoc, spath_pred_add_anon, vpath_pred_add_anon, sget_app.
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
      (* This hypothesis is not necessary for the proof of preservation of HLPL+, but it is
         useful in that it can help us eliminate cases. *)
      (Hno_loan : not_contains_loan (S.[pi])) :
      is_fresh l S ->
      S |-{rv} (&mut p) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_end_borrow_m S (p q : spath) l :
    disj p q -> get_node (S.[p]) = loanC^m(l) -> get_node (S.[q]) = borrowC^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
| Reorg_end_ptr S (p : spath) l :
    get_node (S.[p]) = ptrC(l) -> (*not_in_borrow S p ->*) reorg S (S.[p <- bot])
| Reorg_end_loc S (p : spath) l :
    get_node (S.[p]) = locC(l) -> not_state_contains (eq ptrC(l)) S ->
    reorg S (S.[p <- S.[p +++ [0] ] ])
.

(* Automatically resolving the goals of the form `ptrC(l) <> _`, used to prove the condition
   `not_state_contains (eq ptrC(l)) S` of the rule Reorg_end_loc. *)
Hint Extern 0 (ptrC( _ ) <> _) => discriminate : spath.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : HLPL_plus_val * HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : (S,, a |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loc : not_contains_outer_loc (S.[sp]))
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
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
  | Eval_reorg S0 S1 S2 stmt r (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

Inductive leq_state_base : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Leq_MutBorrow_To_Ptr S l sp_loan sp_borrow (Hdisj : disj sp_loan sp_borrow)
    (HS_loan : get_node (S.[sp_loan]) = loanC^m(l))
    (HS_borrow : get_node (S.[sp_borrow]) = borrowC^m(l)) :
    leq_state_base (S.[sp_loan <- loc(l, S.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l)]) S.

Record HLPL_plus_well_formed (S : HLPL_plus_state) : Prop := {
  at_most_one_borrow_mut l : at_most_one_node (borrowC^m(l)) S;
  at_most_one_loan_mut l : at_most_one_node (loanC^m(l)) S;
  at_most_one_loc l : at_most_one_node (locC(l)) S;
  no_mut_loan_ptr l p : get_node (S.[p]) = loanC^m(l) -> not_state_contains (eq ptrC(l)) S;
  no_mut_loan_loc l p : get_node (S.[p]) = loanC^m(l) -> not_state_contains (eq locC(l)) S;
}.

Notation scount c S := (sweight (indicator c) S).

Record HLPL_plus_well_formed_alt (S : HLPL_plus_state) l : Prop := {
  at_most_one_borrow_mut_alt : scount (borrowC^m(l)) S <= 1;
  no_mut_loan_loc_alt : scount (loanC^m(l)) S + scount (locC(l)) S <= 1;
  no_mut_loan_ptr_alt : scount (loanC^m(l)) S > 0 -> scount (ptrC(l)) S <= 0;
}.

Lemma well_formedness_equiv S : HLPL_plus_well_formed S <-> forall l, HLPL_plus_well_formed_alt S l.
Proof.
  split.
  - intros WF l. destruct WF. split.
    + rewrite<- decide_at_most_one_node; easy.
    + specialize (at_most_one_loan_mut0 l).
      rewrite decide_at_most_one_node in at_most_one_loan_mut0; [ | discriminate].
      specialize (at_most_one_loc0 l).
      rewrite decide_at_most_one_node in at_most_one_loc0; [ | discriminate ].
      apply Nat.le_1_r in at_most_one_loan_mut0. destruct (at_most_one_loan_mut0).
      * lia.
      * assert (scount loanC^m(l) S > 0) as (p & ? & ?%indicator_non_zero)%sweight_non_zero by lia.
        specialize (no_mut_loan_loc0 l p).
        apply not_state_contains_implies_weight_zero
          with (weight := indicator (locC(l))) in no_mut_loan_loc0;
          [lia | apply indicator_non_zero | auto].
    + intros (p & _ & H%indicator_non_zero)%sweight_non_zero.
      symmetry in H. specialize (no_mut_loan_ptr0 _ _ H).
      rewrite Nat.le_0_r. eapply not_state_contains_implies_weight_zero; [ | eassumption].
      intros ?. apply indicator_non_zero.
  - intros WF. split; intros l; destruct (WF l).
    + apply decide_at_most_one_node; [discriminate | ]. assumption.
    + apply decide_at_most_one_node; [discriminate | ]. lia.
    + apply decide_at_most_one_node; [discriminate | ]. lia.
    + intros p Hp.
      assert (valid_p : valid_spath S p) by validity.
      apply weight_sget_node_le with (weight := indicator (loanC^m(l))) in valid_p.
      rewrite Hp in valid_p. autorewrite with weight in valid_p.
      intros q valid_q Hq.
      apply weight_sget_node_le with (weight := indicator (ptrC(l))) in valid_q.
      rewrite <-Hq in valid_q. autorewrite with weight in valid_q.
      lia.
    + intros p H.
      assert (valid_p : valid_spath S p) by validity.
      apply weight_sget_node_le with (weight := indicator (loanC^m(l))) in valid_p.
      rewrite H, indicator_same in valid_p.
      assert (scount (locC(l)) S = 0) by lia.
      intros q valid_q Hq.
      apply weight_sget_node_le with (weight := indicator (locC(l))) in valid_q.
      autorewrite with weight in valid_q. lia.
Qed.

Lemma vweight_loc weight l v :
  vweight weight (loc(l, v)) = weight (locC(l)) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_loc : weight.

Lemma vweight_ptr weight l : vweight weight (ptr(l)) = weight (ptrC(l)).
Proof. reflexivity. Qed.
Hint Rewrite vweight_ptr : weight.

Lemma vweight_int weight n :
  vweight weight (HLPL_plus_int n) = weight (HLPL_plus_intC n).
Proof. reflexivity. Qed.
Hint Rewrite vweight_int : weight.

Lemma vweight_bot weight : vweight weight bot = weight (botC).
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.

Global Program Instance HLPL_plus_state_leq_base : LeqBase HLPL_plus_state :=
{ leq_base := leq_state_base; }.

Global Instance HLPL_plus_WellFormed : WellFormed HLPL_plus_state :=
{ well_formed := HLPL_plus_well_formed }.

Lemma leq_base_preserves_wf_r Sl Sr : well_formed Sr -> leq_base Sl Sr -> well_formed Sl.
Proof.
  rewrite !well_formedness_equiv.
  intros H G l0. specialize (H l0). destruct H. destruct G.
  - destruct (Nat.eq_dec l0 l) as [<- | ]; split; weight_inequality.
Qed.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l0 : loan_id).
  Context (sp_loan sp_borrow : spath).
  Context (Hdisj : disj sp_loan sp_borrow).
  Hypothesis (HS_r_loan : get_node (S_r.[sp_loan]) = loanC^m(l0)).
  Hypothesis (HS_r_borrow : get_node (S_r.[sp_borrow]) = borrowC^m(l0)).
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
  Lemma get_loc_rel q l (H : get_node (S_r.[q]) = locC(l)) :
    exists q', rel (q' +++ [0]) (q +++ [0]) /\ get_node (S_l.[q']) = locC(l).
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
      autorewrite with spath. assumption.
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
    intros (? & H).
    eapply eval_path_mut_borrow_to_ptr in H.
    - destruct H as (q'_l & rel & ?). exists q'_l.
      repeat split; [assumption | validity | eassumption].
    - apply Rel_other. apply not_strict_prefix_nil.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr_Mov p pi :
    eval_place S_r Mov p pi -> eval_place S_l Mov p pi.
  Proof.
    intros (? & H). eapply eval_path_mut_borrow_to_ptr_Mov in H. split; [validity | assumption].
  Qed.

  Lemma eval_place_mut_borrow_to_ptr_Mov_comp p pi :
    eval_place S_r Mov p pi -> ~strict_prefix sp_borrow pi.
  Proof.
    intros (? & H). remember (_, []) as pi0. induction H.
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
    _ : get_node (?Sr.[?sp_loan]) = loanC^m (?l),
    _ : get_node (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
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
    HSr_loan : get_node (?Sr.[?sp_loan]) = loanC^m (?l),
    HSr_borrow : get_node (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
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

Lemma operand_preserves_HLPL_plus_rel op :
  forward_simulation leq_base^* leq_val_state_base^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = const n *)
  - destruct Hle.
    + eapply complete_square_diagram.
      * leq_val_state_step.
        { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
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
        --  leq_val_state_step.
           { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                            (sp_borrow := (anon_accessor a, q)).
             eauto with spath.
             rewrite sget_add_anon. autorewrite with spath. eassumption.
             validity. assumption.
             autorewrite with spath. eassumption.
             all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: autounfold with spath; not_contains.
        -- states_eq.
      (* Case 2: the mutable borrow we're transforming to a pointer is disjoint to the moved value.
       *)
      * assert (disj pi sp_borrow) by reduce_comp.
        eapply complete_square_diagram.
        -- leq_val_state_step.
           { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: autorewrite with spath; assumption.
        -- states_eq.
Admitted.

(* TODO: move in base.v *)
Inductive well_formed_state_value : HLPL_plus_val * HLPL_plus_state -> Prop :=
  | WF_vS v S (WF : forall a, fresh_anon S a -> HLPL_plus_well_formed (S,, a |-> v)) :
      well_formed_state_value (v, S).

Inductive well_formed_alt_state_value : HLPL_plus_val * HLPL_plus_state -> loan_id -> Prop :=
  | WF_alt_vS v S l (WF : forall a, fresh_anon S a -> HLPL_plus_well_formed_alt (S,, a |-> v) l) :
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
  + specialize (WF l0). destruct WF. split.
    * weight_inequality.
    * weight_inequality.
    * assert (valid_p : valid_spath S p) by validity.
      pose proof (weight_sget_node_le (indicator (ptrC(l))) _ _ valid_p) as G.
      rewrite get_S_p in G. cbn in G. autorewrite with weight in G.
      destruct (Nat.eq_dec l l0) as [<- | ]; weight_inequality.
  + apply (f_equal (vget [0])) in get_S_p. autorewrite with spath in get_S_p.
    specialize (IHeval_copy _ get_S_p l0). inversion IHeval_copy. auto.
Qed.

Lemma operand_preserves_well_formedness op S vS :
  S |-{op} op => vS -> HLPL_plus_well_formed S -> well_formed_state_value vS.
Proof.
  intros eval_op WF. destruct eval_op.
  - constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l. specialize (WF l). destruct WF. split; weight_inequality.
  - eauto using copy_preserves_well_formedness.
  - constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l. specialize (WF l). destruct WF.
    split; weight_inequality.
Qed.

Lemma rvalue_preserves_HLPL_plus_rel rv :
  forward_simulation leq_base^* leq_val_state_base^* (eval_rvalue rv) (eval_rvalue rv).
Proof.
  apply preservation_by_base_case.
  intros ? ? Heval. destruct Heval.
  (* rv = just op *)
  - apply operand_preserves_HLPL_plus_rel in Heval_op. intros ? ?%rt_step.
    firstorder using Eval_just.
  (* rv = op + op *)
  - apply operand_preserves_HLPL_plus_rel in H, H0.
    intros S0 Hle%rt_step.
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
        -- leq_val_state_step.
           { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- eapply Eval_pointer_loc. eassumption. autorewrite with spath. exact Hancestor_loc.
        -- reflexivity.
      (* Case 2: the place p is not under the borrow. *)
      * eapply complete_square_diagram.
        -- leq_val_state_step.
           { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
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
      (* Case 1: the place p is under sp_borrow. *)
      * eapply complete_square_diagram.
        -- leq_val_state_step.
            { apply Leq_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
            { autorewrite with spath. reflexivity. }
            reflexivity.
        -- apply Eval_pointer_no_loc with (l := l). eassumption.
            all: autorewrite with spath. assumption. not_contains.
        -- states_eq.
      (* Case 2: *)
      * assert (disj sp_loan pi) by reduce_comp.
        destruct (decidable_prefix pi sp_borrow) as [(r & <-) | ].
        -- eapply complete_square_diagram.
           ++ leq_val_state_step.
              { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := pi +++ [0] ++ r).
                auto with spath. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. all: autounfold with spath; not_contains.
           ++ states_eq.
        -- assert (disj sp_borrow pi) by reduce_comp.
           eapply complete_square_diagram.
           ++ leq_val_state_step.
              { apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                assumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. assumption. all: autounfold with spath; not_contains.
           ++ states_eq.
Admitted.

Lemma well_formed_state_value_implies_well_formed_state v S :
  not_contains_loc v -> well_formed_state_value (v, S) -> well_formed S.
Proof.
  rewrite well_formedness_state_value_equiv, well_formedness_equiv.
  intros no_loc WF l.
  specialize (WF l). inversion WF as [? ? ? WF'].
  destruct (exists_fresh_anon S) as (a & a_fresh).
  destruct (WF' a a_fresh). autorewrite with weight in * |-.
  apply not_value_contains_weight with (weight := indicator (locC(l))) in no_loc;
    [ | intros ? <-%indicator_non_zero; constructor].
  split; weight_inequality.
Qed.

Lemma eval_operand_no_loc op S vS : S |-{op} op => vS -> not_contains_loc (fst vS).
Proof.
  intros eval_op. unfold not_contains_loc. destruct eval_op.
  - not_contains.
  - clear Heval_place. cbn. induction Hcopy_val; not_contains.
  - not_contains.
Qed.

Corollary operand_preserves_well_formedness' op S v S' :
  S |-{op} op => (v, S') -> HLPL_plus_well_formed S -> HLPL_plus_well_formed S'.
Proof.
  intros eval_op WF. eapply operand_preserves_well_formedness in WF; [ | eassumption].
  inversion WF.
  eapply well_formed_state_value_implies_well_formed_state; [ | eassumption].
  apply eval_operand_no_loc in eval_op. exact eval_op.
Qed.

Lemma rvalue_preserves_well_formedness rv S vS :
  S |-{rv} rv => vS -> HLPL_plus_well_formed S -> well_formed_state_value vS.
Proof.
  intros eval_rv WF. destruct eval_rv.
  - eauto using operand_preserves_well_formedness.
  - apply operand_preserves_well_formedness' in H; [ | assumption].
    apply operand_preserves_well_formedness' in H0; [ | assumption].
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (H0 l0). destruct H0. split; weight_inequality.
  - apply ancestor_is_not_bot in Hancestor_loc; [ | discriminate].
    destruct Hancestor_loc as (q & ? & -> & ?).
    assert (valid_q : valid_spath S q) by validity.
    apply weight_sget_node_le with (weight := indicator (locC(l))) in valid_q.
    rewrite H, indicator_same in valid_q.
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (WF l0). destruct WF. split.
    + weight_inequality.
    + weight_inequality.
    + destruct (Nat.eq_dec l l0) as [<- | ]; weight_inequality.
  - apply eval_place_valid in Heval_place.
    assert (scount (locC(l)) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | exact H].
      intros ? <-%indicator_non_zero. constructor. }
    assert (scount (loanC^m(l)) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | exact H].
      intros ? <-%indicator_non_zero. constructor. }
    constructor. intros ? ?. rewrite well_formedness_equiv in *.
    intros l0. specialize (WF l0). destruct WF. split.
    + weight_inequality.
    + destruct (Nat.eq_dec l l0) as [<- | ]; weight_inequality.
    + destruct (Nat.eq_dec l l0) as [<- | ]; weight_inequality.
Qed.

Hint Extern 0 (not_value_contains _ _) => not_contains0 : spath.
Lemma eval_rvalue_no_loan_loc S rv vS' : S |-{rv} rv => vS' ->
  not_contains_loan (fst vS') /\ not_contains_loc (fst vS').
Proof.
  intro H. destruct H; [destruct Heval_op | ..].
  all: auto with spath.
  induction Hcopy_val; auto with spath.
Qed.

Lemma eval_path_add_anon S v p k pi a (a_fresh : fresh_anon S a) :
  not_contains_loc v -> (S,, a |-> v) |-{p} p =>^{k} pi -> S |-{p} p =>^{k} pi.
Proof.
 intros no_loc ((y & H & _) & G).
  remember (encode_var (fst p), []) as q eqn:EQN.
  assert (valid_spath S q).
  { rewrite EQN in *. exists y. split; [ | constructor].
    rewrite get_map_add_anon, lookup_insert_ne in H; easy. }
  split; rewrite<- EQN; [assumption | ].
  clear H EQN. induction G as [ | proj P q q' r ? ? IH].
  - constructor.
  - assert (eval_proj S k proj q q'). {
    - induction Heval_proj; autorewrite with spath in * |-.
      + econstructor; eassumption.
      + assert (valid_spath (S,, a |-> v) q') as [ | ]%valid_spath_add_anon_cases by validity.
        * autorewrite with spath in * |-. econstructor; eassumption.
        * autorewrite with spath in * |-. exfalso. apply no_loc with (p := snd q').
          -- validity.
          -- rewrite get_q'. constructor.
      + econstructor; eauto with spath. }
    econstructor; [ | eapply IH, eval_proj_valid]; eassumption.
Qed.

(* Suppose that (v0, S0) <= (vn, Sn), and that vr does not contain any loan.
   Let us take (v1, S1), ..., (v_{n-1}, S_{n-1}) the intermediate pairs such that
   (v0, S0) <= (v1, S1) <= ... <= (vn, Sn).
   Then, we are going to prove that for each (vi, Si), the value vi does not contain any loan. *)
(* TODO: the name is really similar to leq_val_state_base. *)
Definition leq_val_state_base' (vSl vSr : HLPL_plus_val * HLPL_plus_state) : Prop :=
  leq_val_state_base vSl vSr /\ not_contains_loan (fst vSr) /\ not_contains_loc (fst vSr).

Lemma leq_base_does_not_insert_loan_loc vSl vSr :
  leq_val_state_base' vSl vSr -> not_contains_loan (fst vSl) /\ not_contains_loc (fst vSl).
Proof.
  intros (Hle & Hno_loan & Hno_loc).
  edestruct exists_fresh_anon2 as (a & fresh_a_l & fresh_a_r).
  specialize (Hle a fresh_a_l fresh_a_r).
  remember ((vSl.2),, a |-> vSl.1) eqn:EQN.
  remember ((vSr.2),, a |-> vSr.1).
  destruct Hle; subst.
  - assert (valid_spath (snd vSr) sp_loan).
    (* TODO: this piece of reasonning is used several times. Automate it. *)
    { assert (valid_spath ((snd vSr),, a |-> fst vSr) sp_loan)
        as [ | ]%valid_spath_add_anon_cases
        by validity.
      - assumption.
      - autorewrite with spath in HS_loan. exfalso.
        eapply Hno_loan; [ | rewrite HS_loan; constructor]. validity.
    }
    assert (valid_spath ((snd vSr),, a |-> fst vSr) sp_borrow)
      as [ | ]%valid_spath_add_anon_cases
      by validity.
    + autorewrite with spath in EQN.
      apply states_add_anon_eq in EQN; [ | auto using fresh_anon_sset..].
      destruct EQN as (_ & <-). auto.
    + autorewrite with spath in EQN.
      apply states_add_anon_eq in EQN; [ | auto using fresh_anon_sset..].
      destruct EQN as (_ & <-). auto with spath.
Qed.

Lemma leq_val_state_no_loan_right (vSl vSr : HLPL_plus_val * HLPL_plus_state) :
  leq_val_state_base^* vSl vSr -> not_contains_loan (fst vSr) -> not_contains_loc (fst vSr)
  -> leq_val_state_base'^* vSl vSr.
Proof.
  intros Hle Hno_loan Hno_loc.
  apply proj1 with (B := (not_contains_loan (fst vSl)) /\ (not_contains_loc (fst vSl))).
  induction Hle as [vSl vSr | | x y z].
  - assert (leq_val_state_base' vSl vSr) by (constructor; auto).
    split.
    + constructor. assumption.
    + eapply leq_base_does_not_insert_loan_loc. eassumption.
  - split; [reflexivity | auto].
  - split; [transitivity y | ]; tauto.
Qed.

Lemma fresh_anon_leq_state_base_left Sl Sr a (fresh_a : fresh_anon Sr a) :
  leq_base Sl Sr -> fresh_anon Sl a.
Proof.
  intros Hle. inversion Hle.
  - auto using fresh_anon_sset.
Qed.

Lemma fresh_anon_add_anon S a v b :
  fresh_anon (S,, a |-> v) b  <-> fresh_anon S b /\ anon_accessor a <> anon_accessor b.
Proof.
  unfold fresh_anon. rewrite get_map_add_anon. split.
  - intros H. assert (anon_accessor a <> anon_accessor b).
    { intros G. rewrite <-G, lookup_insert in H. discriminate. }
    split; [ | assumption]. rewrite lookup_insert_ne in H; assumption.
  - intros (? & ?). rewrite lookup_insert_ne; assumption.
Qed.

Lemma leq_val_state_base_specialize_anon a vl Sl vr Sr :
  fresh_anon Sr a -> leq_val_state_base (vl, Sl) (vr, Sr) ->
  leq_base (Sl,, a |-> vl) (Sr,, a |-> vr).
Proof.
  intros fresh_a H. apply H; [ | exact fresh_a].
  destruct (exists_fresh_anon2 Sl (Sr,, a |-> vr))
    as (b & fresh_b_l & (fresh_b_r & ?)%fresh_anon_add_anon).
  specialize (H b fresh_b_l fresh_b_r).
  apply fresh_anon_leq_state_base_left with (a := a) in H;
    [ | rewrite fresh_anon_add_anon; auto].
  rewrite fresh_anon_add_anon in H. destruct H. assumption.
Qed.

Lemma fresh_anon_leq_val_state_base_left vl Sl vr Sr a (fresh_a : fresh_anon Sr a) :
  leq_val_state_base (vl, Sl) (vr, Sr) -> fresh_anon Sl a.
Proof.
  intros H.
  destruct (exists_fresh_anon2 Sl (Sr,, a |-> vr))
    as (b & fresh_b_l & (fresh_b_r & ?)%fresh_anon_add_anon).
  specialize (H b fresh_b_l fresh_b_r).
  eapply fresh_anon_leq_state_base_left in H.
  - rewrite fresh_anon_add_anon in H. destruct H. eassumption.
  - rewrite fresh_anon_add_anon. auto.
Qed.

Lemma store_preserves_HLPL_plus_rel p :
  forward_simulation leq_val_state_base'^* leq_base^* (store p) (store p).
Proof.
  apply preservation_by_base_case.
  intros vSr Sr' Hstore vSl Hle.
  destruct vSl as (vl, Sl) eqn:?. destruct vSr as (vr, Sr) eqn:?.
  destruct Hle as (Hle & no_loan & no_loc). cbn in * |-. inversion Hstore. subst. clear Hstore.
  assert (valid_spath Sr sp).
  { apply eval_path_add_anon in eval_p; [validity | assumption..]. }
  assert (fresh_anon Sl a) by eauto using fresh_anon_leq_val_state_base_left.
  apply (leq_val_state_base_specialize_anon a) in Hle; [ | assumption].
  remember (Sl,, a |-> vl) eqn:HeqvSl. remember (Sr,, a |-> vr).
  destruct Hle; subst.
  - eval_place_preservation. clear valid_p.
    assert (valid_sp_loan : valid_spath (Sr,, a |-> vr) sp_loan) by validity.
    apply valid_spath_add_anon_cases in valid_sp_loan.
    destruct valid_sp_loan.
    2: { autorewrite with spath in HS_loan. exfalso.
      eapply no_loan; [ | rewrite HS_loan ]. validity. constructor. }
    autorewrite with spath in HS_loan |-.
    destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
    (* Case 1: the place sp where we write is inside the borrow. *)
    + assert (valid_spath Sr sp_borrow) by (eapply valid_spath_app; eassumption).
      autorewrite with spath in HS_borrow, HeqvSl.
      apply states_add_anon_eq in HeqvSl; [ | auto using fresh_anon_sset..].
      destruct HeqvSl as (<- & ->). autorewrite with spath in eval_p_in_Sl.
      eapply complete_square_diagram.
      * constructor.
        eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption.
      * constructor. eassumption. all: autorewrite with spath; assumption.
      * states_eq.
    + assert (valid_sp_borrow : valid_spath (Sr,, a |-> vr) sp_borrow) by validity.
      apply valid_spath_add_anon_cases in valid_sp_borrow.
      destruct valid_sp_borrow as [valid_sp_borrw | ]; autorewrite with spath in HS_borrow.
      * autorewrite with spath in HeqvSl.
        apply states_add_anon_eq in HeqvSl; [ | auto using fresh_anon_sset..].
        destruct HeqvSl. subst.
        autorewrite with spath in eval_p_in_Sl.
        destruct (decidable_prefix sp sp_borrow) as [(r_borrow & <-) | ].
        (* Case 2: the borrow is inside the place we write in. *)
        -- destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r_loan))
                                                 (sp_borrow := (anon_accessor a, r_borrow)).
                  eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption.
                 autorewrite with spath.
                 not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
              ** autorewrite with spath. reflexivity.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := (anon_accessor a, r_borrow)).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor.
                 eassumption. not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
              ** states_eq.
        (* Case 3: the borrow is disjoint from the place we write in. *)
        -- assert (disj sp sp_borrow) by reduce_comp.
           destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r_loan))
                                                 (sp_borrow := sp_borrow).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor.
                 eassumption. not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
              ** states_eq.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := sp_borrow).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor.
                 eassumption. not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
              ** states_eq.
      (* Case 4: the borrow is inside the evaluated value. *)
      * destruct sp_borrow as (i & q). replace (fst (i, q)) with i in * |- by reflexivity. subst i.
        autorewrite with spath in HS_borrow.
        autorewrite with spath in eval_p_in_Sl.
        autorewrite with spath in HeqvSl.
        apply states_add_anon_eq in HeqvSl; [ | auto using fresh_anon_sset..].
        destruct HeqvSl. subst.
        destruct (decidable_prefix sp sp_loan) as [(r & <-) | ].
        (* Case 4a: the loan is in the place we write in. *)
        -- eapply complete_square_diagram.
           ++ constructor.
              eapply Leq_MutBorrow_To_Ptr with (sp_loan := (anon_accessor a, r))
                                              (sp_borrow := sp +++ q).
              eauto with spath. all: autorewrite with spath; eassumption.
           ++ constructor.
              eassumption. not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
           ++ autorewrite with spath. reflexivity.
        (* Case 4b: the loan is disjoint to the place we write in. *)
        -- assert (disj sp sp_loan) by reduce_comp.
           eapply complete_square_diagram.
           ++ constructor.
              eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp +++ q).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor.
              eassumption. not_contains_outer. not_contains_outer. auto using fresh_anon_sset.
           ++ states_eq.
Qed.

Lemma store_preserves_well_formedness p vS S' :
  not_contains_loc (fst vS) -> store p vS S' -> well_formed_state_value vS -> well_formed S'.
Proof.
  rewrite well_formedness_equiv, well_formedness_state_value_equiv.
  intros ? Hstore WF l. destruct Hstore as [? ? ? a ? ? ? fresh_a].
  specialize (WF l). inversion WF as [? ? ? WF']. destruct (WF' a fresh_a).
  autorewrite with weight in * |-.
  assert (valid_spath S sp).
  { eapply eval_path_add_anon in eval_p; eauto with spath. }
  split; weight_inequality.
Qed.

Lemma reorg_preserves_well_formedness S S' :
  reorg S S' -> well_formed S -> well_formed S'.
Proof.
  rewrite !well_formedness_equiv. intros Hreorg WF l. specialize (WF l). destruct WF.
  destruct Hreorg.
  - split; weight_inequality.
  - split.
    + weight_inequality.
    + weight_inequality.
    + destruct (Nat.eq_dec l l0); weight_inequality.
  - split.
    + weight_inequality.
    + weight_inequality.
    + apply not_state_contains_implies_weight_zero with (weight := (indicator ptrC(l0))) in H0;
       [ | intro; apply indicator_non_zero].
       destruct (Nat.eq_dec l l0) as [<- | ]; weight_inequality.
Qed.

Corollary reorgs_preserve_well_formedness S S' :
  reorg^* S S' -> well_formed S -> well_formed S'.
Proof. intro Hreorg. induction Hreorg; eauto using reorg_preserves_well_formedness. Qed.

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
Lemma measure_bot : vweight measure_node bot = 0. Proof. reflexivity. Qed.
Hint Rewrite measure_bot : weight.

Lemma reorg_preserves_HLPL_plus_rel :
  well_formed_forward_simulation_r leq_base^* leq_base^* reorg^* reorg^*.
Proof.
  eapply preservation_reorg_r with (measure := sweight measure_node).
  { intros Sl Sr Hle. destruct Hle; weight_inequality. }
  { intros ? ? Hreorg. destruct Hreorg; weight_inequality. }
  { apply leq_base_preserves_wf_r. }
  { apply reorg_preserves_well_formedness. }
  intros Sr Sr' WF_Sr reorg_Sr_Sr'. destruct reorg_Sr_Sr'.
  (* Case Reorg_end_borrow_m: *)
  - intros ? Hle. destruct Hle.
    + destruct (Nat.eq_dec l l0) as [<- | ].
      (* Case 1: l = l0. By well-formedness, that means that the loan that we end at p is the loan
         that we turn into a loc at sp_loan, and that the borrow that we end at q is the
         borrow we turn into a pointer at sp_borrow. *)
      * assert (p = sp_loan) as ->.
        { eapply at_most_one_loan_mut. eassumption.
          rewrite H0. reflexivity. rewrite HS_loan. reflexivity. }
        assert (q = sp_borrow) as ->.
        { eapply at_most_one_borrow_mut. eassumption.
          rewrite H1. reflexivity. assumption. }
        eapply complete_square_diagram.
        -- reflexivity.
        -- etransitivity.
           { constructor. eapply Reorg_end_ptr with (p := sp_borrow).
             autorewrite with spath. reflexivity. }
           { constructor. eapply Reorg_end_loc with (p := sp_loan).
             autorewrite with spath. reflexivity.
             assert (not_state_contains (eq ptrC(l)) S).
             { eapply no_mut_loan_ptr. eassumption. rewrite HS_loan. reflexivity. }
             autorewrite with spath. not_contains. }
        -- states_eq.
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
              apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ r).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eapply Reorg_end_borrow_m with (p := p) (q := q).
              assumption. all: autorewrite with spath. eassumption. assumption.
              not_contains. auto with spath.
           ++ states_eq.
        -- assert (disj q sp_borrow) by reduce_comp.
           destruct (decidable_prefix sp_borrow p).
           (* Case 3: the loan that we end is is the borrow that we turn into a pointer. *)
           ++ assert (strict_prefix sp_borrow p)  by auto with spath.
              assert (prefix (sp_borrow +++ [0]) p) as (r & <-) by eauto with spath.
              rewrite<- (app_spath_vpath_assoc sp_borrow [0] r) in * |-.
              eapply complete_square_diagram.
              ** constructor.
                 apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_borrow_m with (p := sp_loan +++ [0] ++ r) (q := q).
                 auto with spath. all: autorewrite with spath. eassumption.
                 assumption. assumption. auto with spath.
              ** states_eq.
           (* Case 4: the loan that we end is disjoint from the borrow that we turn into a pointer.
           *)
           ++ assert (disj sp_borrow p) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 apply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_borrow_m with (p := p) (q := q).
                 assumption. all: autorewrite with spath. eassumption.
                 assumption. assumption. auto with spath.
              ** states_eq.
  - intros ? Hle. destruct Hle.
    + destruct (decidable_prefix sp_borrow p).
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by eauto with spath.
        rewrite<- (app_spath_vpath_assoc sp_borrow [0] q) in *.
        eapply complete_square_diagram.
        -- constructor.
           eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_ptr with (p := sp_loan +++ [0] ++ q).
           autorewrite with spath. eassumption.
        -- states_eq.
      * assert (disj sp_borrow p) by reduce_comp.
        assert (disj sp_loan p) by reduce_comp.
        eapply complete_square_diagram.
        -- constructor.
           eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_ptr with (p := p). autorewrite with spath. eassumption.
        -- states_eq.
  - intros ? Hle. destruct Hle.
    + assert (l <> l0).
      { intros <-. eapply no_mut_loan_loc; [ eassumption.. | | symmetry; eassumption].
        validity. }
      destruct (decidable_prefix sp_borrow p).
      (* Case 1: the loc we end is is the borrow we turn into a pointer. *)
      * assert (prefix (sp_borrow +++ [0]) p) as (q & <-) by eauto with spath.
        autorewrite with spath in *.
        eapply complete_square_diagram.
        -- constructor.
           eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
           assumption. all: autorewrite with spath; eassumption.
        -- constructor. eapply Reorg_end_loc with (p := sp_loan +++ [0] ++ q).
           autorewrite with spath. eassumption. not_contains. cbn. congruence.
        -- states_eq.
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
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := p +++ q).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: not_contains. cbn. congruence.
              ** autorewrite with spath. reflexivity.
           (* Case 3: the borrow we turn into a pointer is in the location we end, but the loan we
            * turn into a location is disjoint. *)
           ++ assert (disj p sp_loan) by reduce_comp.
              autorewrite with spath in *.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := p +++ q).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: not_contains. cbn. congruence.
              ** states_eq.
        -- assert (disj p sp_borrow) by reduce_comp.
           destruct (decidable_prefix p sp_loan).
           (* Case 4: the loan we turn into a location is in the location we end, but the borrow we
            * turn into a pointer is disjoint. *)
           ++ assert (prefix (p +++ [0]) sp_loan) as (r & <-) by eauto with spath.
              rewrite<- app_spath_vpath_assoc in *.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := p +++ r) (sp_borrow := sp_borrow).
                 eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: not_contains. cbn. congruence.
              ** states_eq.
           (* Case 5: the loan and the borrow we turn into a location and a pointer are in the loc
            * we end. *)
           ++ assert (disj p sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Leq_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                 assumption. all: autorewrite with spath; eassumption.
              ** constructor. eapply Reorg_end_loc with (p := p).
                 autorewrite with spath; eassumption.
                 repeat apply not_state_contains_sset.
                 assumption. all: not_contains. cbn. congruence.
              ** states_eq.
Qed.

Lemma stmt_preserves_well_formedness S s r S' :
  S |-{stmt} s => r, S' -> well_formed S -> well_formed S'.
Proof.
  intros eval_s. induction eval_s.
  - auto.
  - auto.
  - auto.
  - intros.
    assert (well_formed_state_value vS') by eauto using rvalue_preserves_well_formedness.
    apply eval_rvalue_no_loan_loc in eval_rv. destruct eval_rv as (_ & ?).
    eauto using store_preserves_well_formedness.
  - intros. apply IHeval_s. eauto using reorgs_preserve_well_formedness.
Qed.

Lemma stmt_preserves_HLPL_plus_rel s r :
  well_formed_forward_simulation_r leq_base^* leq_base^* (eval_stmt s r) (eval_stmt s r).
Proof.
  intros Sr Sr' WF_Sr Heval Sl Hle. revert Sl Hle. induction Heval; intros Sl Hle.
  - eexists. split; [eassumption | constructor].
  - specialize (IHHeval1 WF_Sr _ Hle).
    destruct IHHeval1 as (Sl' & ? & ?).
    edestruct IHHeval2 as (Sl'' & ? & ?);
      [eauto using stmt_preserves_well_formedness | eassumption | ].
    exists Sl''. split; [assumption | ]. eapply Eval_seq_unit; eassumption.
  - specialize (IHHeval WF_Sr _ Hle).
    destruct IHHeval as (Sl' & ? & ?).
    exists Sl'. split; [assumption | ].
    apply Eval_seq_panic. assumption.
  - pose proof (_eval_rv := eval_rv). apply rvalue_preserves_HLPL_plus_rel in _eval_rv.
    destruct (_eval_rv _ Hle) as (vSl' & leq_vSl_vS' & eval_Sl).
    apply store_preserves_HLPL_plus_rel in Hstore.
    apply leq_val_state_no_loan_right in leq_vSl_vS';
      [ | eapply eval_rvalue_no_loan_loc; exact eval_rv..].
    destruct (Hstore _ leq_vSl_vS') as (Sl'' & leq_Sl'' & store_vSl').
    exists Sl''. split; [assumption | ]. econstructor; eassumption.
  - assert (well_formed S1) by eauto using reorgs_preserve_well_formedness.
    apply reorg_preserves_HLPL_plus_rel in Hreorg; [ | assumption].
    destruct (Hreorg _ Hle) as (Sl1 & leq_Sl1 & reorg_Sl1).
    edestruct IHHeval as (Sl2 & leq_Sl2 & eval_in_Sl2); [ assumption | eassumption | ].
    exists Sl2. split; [assumption | ].
    apply Eval_reorg with (S1 := Sl1); assumption.
Qed.
