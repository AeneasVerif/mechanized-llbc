(** * Mechanized_LLBC.HLPL_plus : Semantics of HLPL+. *)
Require Import lang.
Require Import base.
From Stdlib Require Import List.
Import ListNotations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree.

(** * Definition of HLPL+ values and states. *)
Inductive value :=
| VBottom
| VInt (n : nat) (* TODO: use Aeneas integer types? *)
| VBool (b : bool)
| VMutLoan (l : loan_id)
| VMutBorrow (l : loan_id) (v : value)
| VLoc (l : loan_id) (v : value)
| VPtr (l : loan_id)
| VTuple (t : value_list)
with value_list :=
| VNil
| VCons (v : value) (vl : value_list)
.

Module ValueList.
  Fixpoint length (vl : value_list) : nat :=
    match vl with
    | VNil => 0
    | VCons _ vl' => S (length vl')
    end.

  Fixpoint from_list (vl : list value) : value_list :=
    match vl with
    | [] => VNil
    | t :: tl => VCons t (from_list tl)
    end.

  Fixpoint to_list (vl : value_list) : list value :=
    match vl with
    | VNil => []
    | VCons t tl => t :: (to_list tl)
    end.

  Lemma from_list_to_list_inv (vl : value_list) :
    from_list (to_list vl) = vl.
  Proof. induction vl ; simpl ; congruence. Qed.

  Lemma to_list_from_list_inv (vl : list value) :
    to_list (from_list vl) = vl.
  Proof. induction vl ; simpl ; congruence. Qed.

  Lemma to_list_inj (vl0 vl1 : value_list) :
    to_list vl0 = to_list vl1 -> vl0 = vl1.
  Proof.
    intros. apply f_equal with (f := from_list) in H.
    by rewrite !from_list_to_list_inv in H.
  Qed.

  Lemma from_list_inj (vl0 vl1 : list value) :
    from_list vl0 = from_list vl1 -> vl0 = vl1.
  Proof.
    intros. apply f_equal with (f := to_list) in H.
    by rewrite !to_list_from_list_inv in H.
  Qed.

  Lemma length_from_list (vl : list value) :
    List.length vl = length (from_list vl).
  Proof. induction vl; simpl ; congruence. Qed.

  Lemma length_to_list (vl : value_list) :
    length vl = List.length (to_list vl).
  Proof. induction vl; simpl ; congruence. Qed.

  Definition Forall (P : value -> Prop) (vl : value_list) : Prop :=
    List.Forall P (to_list vl).
End ValueList
.

Variant nodes :=
| NBottom
| NInt (n : nat)
| NBool (b : bool)
| NMutLoan (l : loan_id)
| NMutBorrow (l : loan_id)
| NLoc (l : loan_id)
| NPtr (l : loan_id)
| NTuple (n : nat)
.

Instance EqDec_nodes : EqDecision nodes.
Proof. unfold EqDecision, Decision. repeat decide equality. Qed.

Definition HLPL_plus_arity c := match c with
| NBottom => 0
| NInt _ => 0
| NBool _ => 0
| NMutLoan _ => 0
| NMutBorrow _ => 1
| NLoc _ => 1
| NPtr _ => 0
| NTuple n => n
end.

Definition HLPL_plus_get_node v := match v with
| VBottom => NBottom
| VInt n => NInt n
| VBool b => NBool b
| VMutLoan l => NMutLoan l
| VMutBorrow l _ => NMutBorrow l
| VLoc l _ => NLoc l
| VPtr l => NPtr l
| VTuple l => NTuple (ValueList.length l)
end.

Definition HLPL_plus_children v := match v with
| VBottom => []
| VInt _ => []
| VBool _ => []
| VMutLoan _ => []
| VMutBorrow _ v => [v]
| VLoc _ v => [v]
| VPtr l => []
| VTuple l => ValueList.to_list l
end.

Definition HLPL_plus_fold c vs := match c, vs with
| NInt n, [] => VInt n
| NBool b, [] => VBool b
| NMutLoan l, [] => VMutLoan l
| NMutBorrow l, [v] => VMutBorrow l v
| NLoc l, [v] => VLoc l v
| NPtr l, [] => VPtr l
| NTuple _, l => VTuple (ValueList.from_list l)
| _, _ => VBottom
end.

Fixpoint HLPL_plus_weight node_weight v :=
  match v with
  | VMutBorrow l v => node_weight (NMutBorrow l) + HLPL_plus_weight node_weight v
  | VLoc l v => node_weight (NLoc l) + HLPL_plus_weight node_weight v
  | VTuple t =>
      node_weight (NTuple (ValueList.length t)) + HLPL_plus_tuple_weight node_weight t
  | v => node_weight (HLPL_plus_get_node v)
end with HLPL_plus_tuple_weight node_weight vl :=
  match vl with
  | VNil => 0
  | VCons v vl => (HLPL_plus_weight node_weight v) + (HLPL_plus_tuple_weight node_weight vl)
  end
.

Program Instance ValueHLPL : Value value nodes := {
  arity := HLPL_plus_arity;
  get_node := HLPL_plus_get_node;
  children := HLPL_plus_children;
  fold_value := HLPL_plus_fold;
  vweight := HLPL_plus_weight;
  bot := VBottom;
}.
Next Obligation.
  destruct v; try reflexivity.
  induction t ; simpl ; [reflexivity | by f_equal].
Qed.
Next Obligation.
  intros [] [] eq_node eq_children; inversion eq_node; inversion eq_children;
    simpl in * ; try congruence.
  by apply ValueList.to_list_inj in H1 as ->.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] | idtac ];
   simpl in * ; try congruence.
 by rewrite <- ValueList.length_from_list, H.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] | idtac ];
  try reflexivity.
 generalize dependent n. induction vs ; simpl in * ; intros. reflexivity.
 apply f_equal with (f := pred) in H. simpl in H.
 apply f_equal, (IHvs (pred n)). congruence.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? []; unfold HLPL_plus_children; cbn; try lia.
  induction t ;  simpl ; lia.
Qed.

Record state := {
  vars : Pmap value;
  anons : Pmap value;
}.

Definition encode_var (x : var) := encode (A := var + anon) (inl x).
Definition encode_anon (a : positive) := encode (A := var + anon) (inr a).

Program Instance IsState : State state value (H := ValueHLPL) := {
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
Next Obligation. intros [? ?] [? ?]. cbn. intros (-> & ->)%sum_maps_eq _. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? i. cbn. destruct (decode' i) eqn:H.
  - rewrite decode'_is_Some in H.
    destruct s; cbn; rewrite <-H; symmetry;
      first [apply sum_maps_alter_inl | apply sum_maps_alter_inr].
  - symmetry. apply alter_id', sum_maps_lookup_None. assumption.
Qed.
(* What are the two following obligations? *)
Next Obligation. discriminate. Qed.
Next Obligation. discriminate. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. cbn. symmetry. apply sum_maps_insert_inr. Qed.
Next Obligation. reflexivity. Qed.

Lemma get_at_var S x : get_at_accessor S (encode_var x) = lookup x (vars S).
Proof. unfold get_map, encode_var. cbn. apply sum_maps_lookup_l. Qed.


Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* Notation "'bot'" := VBottom: hlpl_plus_scope. *)
Notation "'loan^m' ( l )" := (VMutLoan l) : hlpl_plus_scope.
Notation "'borrow^m' ( l  , v )" := (VMutBorrow l v) : hlpl_plus_scope.
Notation "'loc' ( l , v )" := (VLoc l v) : hlpl_plus_scope.
Notation "'ptr' ( l )" := (VPtr l) : hlpl_plus_scope.

Notation "'nbot'" := NBottom: hlpl_plus_scope.
Notation "'nloan^m' ( l )" := (NMutLoan l) : hlpl_plus_scope.
Notation "'nborrow^m' ( l )" := (NMutBorrow l) : hlpl_plus_scope.
Notation "'nloc' ( l )" := (NLoc l) : hlpl_plus_scope.
Notation "'nptr' ( l )" := (NPtr l) : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with value. *)
Open Scope hlpl_plus_scope.

Lemma sget_loc l v p : (loc(l, v)).[[ [0] ++  p]] = v.[[p]].
Proof. reflexivity. Qed.
Hint Rewrite sget_loc : spath.
Lemma sget_loc' l v : (loc(l, v)).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite sget_loc' : spath.

(** * Semantics of HLPL+ *)
(* This property represents the application of a projection p (such as a pointer dereference or a
 * field access) on spath pi0, on a state S and given a permission perm.
 * If this projection is successful, then we have eval_proj S perm p pi0 pi1.
 *)
Variant eval_proj (S : state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| E_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = nborrow^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| E_Deref_Ptr_Loc q q' l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = nptr(l)) (get_q' : get_node (S.[q']) = nloc(l)) :
    eval_proj S perm Deref q q'
.

Variant eval_loc (S : state) perm : spath -> spath -> Prop :=
(* Coresponds to R-Loc and W-Loc in the article. *)
| E_Loc q l
    (Hperm : perm <> Mov) (get_q : get_node (S.[q]) = nloc(l)) :
    eval_loc S perm q (q +++ [0])
.

(* Let pi0 be a spath. If by successfully applying the projections in P (with permission perm) we
   obtain a spath pi1, then we have the proprety eval_path S perm P pi0 pi1. *)
Inductive eval_path (S : state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| E_Path_Nil pi : eval_path S perm [] pi pi
| E_Path_Proj proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r
| E_Path_Loc P p q r
    (Heval_loc : eval_loc S perm  p q) (Heval_path_rec : eval_path S perm P q r) :
    eval_path S perm P p r
.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst (fst p)), []) in
  valid_spath S pi_0 /\ eval_path S perm p.1.2 (encode_var p.1.1, []) pi.

Global Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof. destruct H; validity. Qed.

Lemma eval_path_valid (s : state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
  - apply IHeval_q_r. destruct Heval_loc. validity.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loan : nodes -> Prop :=
| IsLoan_MutLoan l : is_loan (nloan^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Variant is_loc : nodes -> Prop :=
| IsLoc_Loc l : is_loc (nloc(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.
Hint Extern 0 (~is_loc _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = nbot) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> nbot) => discriminate : spath.

Variant is_mut_borrow : nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (nborrow^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).
Notation not_contains_outer_loc := (not_contains_outer is_mut_borrow is_loc).

Notation not_in_borrow := (no_ancestor is_mut_borrow).

Variant is_borrow : nodes -> Prop :=
| IsBorrow_MutBorrow l : is_borrow (nborrow^m(l)).
Definition not_contains_borrow := not_value_contains is_borrow.
Hint Unfold not_contains_borrow : spath.
Hint Extern 0 (~is_borrow _) => intro; easy : spath.

Definition get_loan_id c :=
  match c with
  | nloan^m(l) => Some l
  | nborrow^m(l) => Some l
  | nloc(l) => Some l
  | nptr(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).

Lemma is_fresh_loan_id_neq (S : state) l0 l1 (p : spath) :
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

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

Inductive eval_operand : operand -> state -> (value * state) -> Prop :=
| E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_BoolConst S b : S |-{op} Const (BoolConst b) => (VBool b, S)
| E_Copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| E_Move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
| E_Tuple S S' opl vl
    (H : eval_tuple opl S (vl, S')) :
  S |-{op} Tuple opl => (VTuple vl, S')
where "S |-{op} op => r" := (eval_operand op S r)
with eval_tuple : list operand -> state -> (value_list * state) -> Prop :=
| E_Tuple_Nil S : eval_tuple [] S (VNil, S)
| E_Tuple_Cons S S' S'' op opl v v'
    (Hop : eval_operand op S (v, S'))
    (Hrec : eval_tuple opl S' (v', S'')) :
  eval_tuple (op :: opl) S (VCons v v', S'')
.
Scheme eval_operand_mut := Minimality for eval_operand Sort Prop
with   eval_tuple_mut   := Minimality for eval_tuple   Sort Prop.

Combined Scheme eval_operand_tuple_mutind from eval_operand_mut, eval_tuple_mut.

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Le m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | E_BinOp S S' S'' binop op_0 op_1 v0 v1 w
      (eval_op_0 : S |-{op} op_0 => (v0, S'))
      (eval_op_1 : S' |-{op} op_1 => (v1, S''))
      (Hbinop : eval_binary_op binop v0 v1 w) :
      S |-{rv} (BinaryOp binop op_0 op_1) => (w, S'')
  | E_Pointer_Loc S p pi l
      (Heval_place : S |-{p} p =>^{Mut} pi)
      (Hloc : get_node (S.[pi]) = nloc(l)) : S |-{rv} &mut p => (ptr(l), S)
  | E_Pointer_Fresh S p pi l
      (Heval_place : S |-{p} p =>^{Mut} pi)
      (* This hypothesis is not necessary for the proof of preservation of HLPL+, but it is
         useful in that it can help us eliminate cases. *)
      (Hno_loan : not_contains_loan (S.[pi])) :
      is_fresh l S ->
      S |-{rv} (&mut p) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Inductive reorg : state -> state -> Prop :=
| Reorg_End_MutBorrow S (p q : spath) l :
    disj p q -> get_node (S.[p]) = nloan^m(l) -> get_node (S.[q]) = nborrow^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
| Reorg_end_ptr S (p : spath) l :
    get_node (S.[p]) = nptr(l) -> (*not_in_borrow S p ->*) reorg S (S.[p <- bot])
| Reorg_end_loc S (p : spath) l :
    get_node (S.[p]) = nloc(l) -> not_state_contains (eq nptr(l)) S ->
    reorg S (S.[p <- S.[p +++ [0] ] ])
.

(* Automatically resolving the goals of the form `nptr(l) <> _`, used to prove the condition
   `not_state_contains (eq nptr(l)) S` of the rule Reorg_end_loc. *)
Hint Extern 0 (nptr( _ ) <> _) => discriminate : spath.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : S |-{p} p =>^{Mut} sp)
  (no_outer_loc : not_contains_outer_loc (S.[sp]))
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(* TODO: take fuel into account and delete this notation. *)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> flow_token -> state -> state -> Prop :=
  | E_Nop S : S |-{stmt} Nop => rUnit, S
  | E_Seq_Unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | E_Seq_Propagate S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | E_Assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | E_Reorg S0 S1 S2 stmt r (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
  | E_IfThenElse_T S S' S'' cond stmt_if stmt_else r
      (eval_cond : S |-{op} cond => (VBool true, S')) :
      S' |-{stmt} stmt_if => r, S'' ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => r, S''
  | E_IfThenElse_F S S' S'' cond stmt_if stmt_else r
      (eval_cond : S |-{op} cond => (VBool false, S')) :
      S' |-{stmt} stmt_else => r, S'' ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) => r, S''
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

Inductive leq_base : state -> state -> Prop :=
| Leq_MutBorrow_To_Ptr S l sp_loan sp_borrow (Hdisj : disj sp_loan sp_borrow)
    (HS_loan : get_node (S.[sp_loan]) = nloan^m(l))
    (HS_borrow : get_node (S.[sp_borrow]) = nborrow^m(l)) :
    leq_base (S.[sp_loan <- loc(l, S.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l)]) S.
