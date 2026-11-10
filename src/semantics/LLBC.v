(** * Mechanized_LLBC.LLBC : definition of LLBC states. *)
Require Import base.
Require Import lang.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.
(* Notation conflict between stdpp's `+++` and our `+++`. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.
From Stdlib Require Bool.

(** * Definition of LLBC values and states. *)
Inductive value :=
| VBottom
| VInt (n : nat) (* TODO: use Aeneas integer types? *)
| VBool (b : bool)
| VMutLoan (l : loan_id)
| VMutBorrow (l : loan_id) (v : value)
.

Variant nodes :=
| NBottom
| NInt (n : nat)
| NBool (b : bool)
| NMutLoan (l : loan_id)
| NMutBorrow (l : loan_id)
.

Instance EqDecision_nodes : EqDecision nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Defined.

Definition LLBC_arity c := match c with
| NBottom => 0
| NInt _ => 0
| NBool _ => 0
| NMutLoan _ => 0
| NMutBorrow _ => 1
end.

Definition LLBC_get_node v := match v with
| VBottom => NBottom
| VInt n => NInt n
| VBool b => NBool b
| VMutLoan l => NMutLoan l
| VMutBorrow l _ => NMutBorrow l
end.

Definition LLBC_children v := match v with
| VBottom => []
| VInt _ => []
| VBool _ => []
| VMutLoan _ => []
| VMutBorrow _ v => [v]
end.

Definition LLBC_fold c vs := match c, vs with
| NInt n, [] => VInt n
| NBool b, [] => VBool b
| NMutLoan l, [] => VMutLoan l
| NMutBorrow l, [v] => VMutBorrow l v
| _, _ => VBottom
end.

Fixpoint LLBC_weight node_weight v :=
  match v with
  | VMutBorrow l v => node_weight (NMutBorrow l) + LLBC_weight node_weight v
  | v => node_weight (LLBC_get_node v)
end.

Program Instance ValueLLBC : Value value nodes := {
  arity := LLBC_arity;
  get_node := LLBC_get_node;
  children := LLBC_children;
  fold_value := LLBC_fold;
  vweight := LLBC_weight;
  bot := VBottom;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_nodes eq_children; inversion eq_nodes; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; cbn; lia. Qed.

Record state := {
  vars : Pmap value;
  anons : Pmap value;
}.

Variant Acc :=
  | Acc_var (x : var)
  | Acc_anon (a : anon)
.

Global Instance EqDecision_Acc : EqDecision Acc.
Proof. unfold EqDecision, Decision. repeat decide equality. Defined.

Instance Injection_Acc_var : Inj eq eq Acc_var.
Proof. intros ? ? [=]. assumption. Qed.
Instance Injection_Acc_anon : Inj eq eq Acc_anon.
Proof. intros ? ? [=]. assumption. Qed.

Program Global Instance Countable_Acc : Countable Acc := {
  encode acc := match acc with
                | Acc_var x => xO x
                | Acc_anon a => xI a
                end;
  decode p := match p with
              | xO x => Some (Acc_var x)
              | xI a => Some (Acc_anon a)
              | _ => None
              end;
}.
Next Obligation. repeat split; discriminate. Qed.
Next Obligation. intros [ | ]; reflexivity. Qed.

Definition get_map S : gmap Acc value := union (kmap Acc_var (vars S)) (kmap Acc_anon (anons S)).

Lemma map_disjoint_vars_anons S :
  map_disjoint (M := gmap _) (kmap Acc_var (vars S)) (kmap Acc_anon (anons S)).
Proof.
  apply map_disjoint_spec. setoid_rewrite lookup_kmap_Some; [ | typeclasses eauto..].
  intros acc ? ? (x & ? & _) (a & ? & _). congruence.
Qed.

Lemma get_at_var x S : lookup (Acc_var x) (get_map S) = lookup x (vars S).
Proof.
  unfold get_map. rewrite lookup_union_l.
  - apply lookup_kmap. typeclasses eauto.
  - rewrite lookup_kmap_None by typeclasses eauto. intros ? [=].
Qed.
Lemma get_at_anon a S : lookup (Acc_anon a) (get_map S) = lookup a (anons S).
Proof.
  unfold get_map. rewrite lookup_union_r.
  - apply lookup_kmap. typeclasses eauto.
  - rewrite lookup_kmap_None by typeclasses eauto. intros ? [=].
Qed.

Program Instance IsState : State state value Acc  := {
  extra := unit;
  get_map := get_map;
  get_extra _ := ();
  alter_at_accessor f acc S :=
  match acc with
  | Acc_var x => {|vars := alter f x (vars S); anons := anons S|}
  | Acc_anon a => {|vars := vars S; anons := alter f a (anons S)|}
  end;
  anon_accessor := Acc_anon;
  accessor_anon acc :=
    match acc with
    | Acc_anon a => Some a
    | _ => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
}.
Next Obligation.
  intros [vars anons] [vars' anons'] eq_maps _. f_equal.
  - apply map_eq. intros x. apply (f_equal (lookup (Acc_var x))) in eq_maps.
    rewrite !get_at_var in eq_maps. exact eq_maps.
  - apply map_eq. intros a. apply (f_equal (lookup (Acc_anon a))) in eq_maps.
    rewrite !get_at_anon in eq_maps. exact eq_maps.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? [x | a]; cbn.
  - apply map_eq. intros [y | ].
    + rewrite get_at_var. cbn. destruct (decide (x = y)) as [<- | ].
      * rewrite !lookup_alter_eq. rewrite get_at_var. reflexivity.
      * rewrite !lookup_alter_ne by congruence. rewrite get_at_var. reflexivity.
    + rewrite lookup_alter_ne by discriminate. rewrite !get_at_anon. reflexivity.
  - apply map_eq. intros [ | b].
    + rewrite lookup_alter_ne by discriminate. rewrite !get_at_var. reflexivity.
    + rewrite get_at_anon. cbn. destruct (decide (a = b)) as [<- | ].
      * rewrite !lookup_alter_eq. rewrite get_at_anon. reflexivity.
      * rewrite !lookup_alter_ne by congruence. rewrite get_at_anon. reflexivity.
Qed.
(* What are the two following obligations? *)
Next Obligation. discriminate. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros a v S. cbn. apply map_eq. intros [ | b].
  - rewrite lookup_insert_ne by discriminate. rewrite !get_at_var. reflexivity.
  - rewrite get_at_anon. cbn. destruct (decide (a = b)) as [<- | ].
    + rewrite !lookup_insert_eq. reflexivity.
    + rewrite !lookup_insert_ne by congruence. symmetry. apply get_at_anon.
Qed.
Next Obligation. reflexivity. Qed.

Declare Scope llbc_scope.
Delimit Scope llbc_scope with llbc.

(* Notation "'bot'" := VBottom: llbc_scope. *)
Notation "'loan^m' ( l )" := (VMutLoan l) : llbc_scope.
Notation "'borrow^m' ( l  , v )" := (VMutBorrow l v) : llbc_scope.

Notation "'nbot'" := NBottom: llbc_scope.
Notation "'nloan^m' ( l )" := (NMutLoan l) : llbc_scope.
Notation "'nborrow^m' ( l )" := (NMutBorrow l) : llbc_scope.

(* Bind Scope llbc_scope with value. *)
Open Scope llbc_scope.

(** * Semantics of LLBC *)
Inductive eval_proj (S : state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| E_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = nborrow^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| E_Path_Nil pi : eval_path S perm [] pi pi
| E_Path_Proj proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  is_Some (get_at_accessor S (Acc_var (fst (fst p))))  /\
  eval_path S perm (snd (fst p)) (Acc_var (fst (fst p)), []) pi.

Global Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Variant is_loan : nodes -> Prop :=
| IsLoan_MutLoan l : is_loan (nloan^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = nbot) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> nbot) => discriminate : spath.

Variant is_mut_borrow : nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (nborrow^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).

Lemma loan_is_not_bot x : is_loan x -> x <> nbot. Proof. intros [ ]; discriminate. Qed.

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
.

Variant eval_operand : operand -> state -> (value * state) -> Prop :=
| E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_BoolConst S b : S |-{op} Const (BoolConst b) => (VBool b, S)
| E_Copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| E_Move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Definition get_loan_id c :=
  match c with
  | nloan^m(l) => Some l
  | nborrow^m(l) => Some l
  | _ => None
  end.

Global Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Le m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | E_BinOp S S' S'' binop op_l op_r vl vr w :
      (S |-{op} op_l => (vl, S')) ->
      (S' |-{op} op_r => (vr, S'')) ->
      eval_binary_op binop vl vr w ->
      S |-{rv} (BinaryOp binop op_l op_r) => (w, S'')
  | E_MutBorrow S p pi l : S |-{p} p =>^{Mut} pi ->
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) -> is_fresh l S ->
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Notation not_in_borrow := (no_ancestor is_mut_borrow).

Inductive reorg : state -> state -> Prop :=
| Reorg_End_MutBorrow S (p q : spath) l :
    disj p q -> get_node (S.[p]) = nloan^m(l) -> get_node (S.[q]) = nborrow^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : S |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

Inductive eval_stmt : nat -> statement -> state -> option (flow_token * state) -> Prop :=
  | E_Step_Zero s S : S |-{stmt} s ~>{0} None
  | E_Nop n S : S |-{stmt} Nop ~>{1 + n} Some (rUnit, S)
  | E_Panic n S : S |-{stmt} Panic ~>{1 + n} Some (rPanic, S)
  | E_Break n S : S |-{stmt} Break ~>{1 + n} Some (rBreak, S)
  | E_Continue n S : S |-{stmt} Continue ~>{1 + n} Some (rContinue, S)
  | E_Seq_Unit n S0 S1 R stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l ~>{1 + n} Some (rUnit, S1))
      (eval_stmt_r : S1 |-{stmt} stmt_r ~>{1 + n} R) :  S0 |-{stmt} stmt_l;; stmt_r ~>{1 + n} R
  | E_Seq_Propagate n S0 S1 r stmt_l stmt_r (no_unit : r <> rUnit)
      (eval_stmt_l : S0 |-{stmt} stmt_l ~>{1 + n} Some (r, S1)) :
      S0 |-{stmt} stmt_l;; stmt_r ~>{1 + n} Some (r, S1)
  | E_Seq_Interrupt n S0 stmt_l stmt_r
      (eval_stmt_l : S0 |-{stmt} stmt_l ~>{1 + n} None) :
      S0 |-{stmt} stmt_l;; stmt_r ~>{1 + n} None
  | E_Assign n S vS' S'' p rv
      (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv ~>{1 + n} Some (rUnit, S'')
  | E_IfThenElse_T n S S' R cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool true, S')) :
      S' |-{stmt} stmt_if ~>{1 + n} R ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} R
  | E_IfThenElse_F n S S' R cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool false, S')) :
      S' |-{stmt} stmt_else ~>{1 + n} R ->
      S |-{stmt} (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~>{1 + n} R
  | E_Reorg n S0 S1 R stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt ~>{1 + n} R) :
      S0 |-{stmt} stmt ~>{1 + n} R
  | E_Loop_Stop n S body r r' S1
      (eval_body : S |-{stmt} body ~>{1 + n} Some (r, S1))
      (next_tag : end_loop_tag r = Some r') :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} Some (r', S1)
  | E_Loop_Interrupt n S body
      (eval_body : S |-{stmt} body ~>{1 + n} None) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} None
  | E_Loop_Continue n S body S1 R2
      (eval_body : S |-{stmt} body ~>{1 + n} Some (rContinue, S1))
      (Heval2 : S1 |-{stmt} (LOOP {{ body }}) ~>{n} R2) :
      S |-{stmt} (LOOP {{ body }}) ~>{1 + n} R2
where "S |-{stmt} stmt ~>{ n } R" := (eval_stmt n stmt S R) : llbc_scope.
