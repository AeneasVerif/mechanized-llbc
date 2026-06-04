Require Import lang.
Require Import base.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree.
Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import SimulationUtils.

(** * Definition of HLPL values and states. *)
Inductive value :=
| VBottom
| VInt (n : nat) (* TODO: use Aeneas integer types? *)
| VBool (b : bool)
| VLoc (l : loan_id) (v : value)
| VPtr (l : loan_id)
| VTuple (t : list value)
.

Fixpoint value_ind'
  (P : value -> Type)
  (fbot : P VBottom)
  (fint : forall n, P (VInt n))
  (fbool: forall b, P (VBool b))
  (floc : ∀ l v, P v → P (VLoc l v))
  (fptr : forall l, P (VPtr l))
  (ftuple : ∀ vl : list value, ForallT P vl -> P (VTuple vl))
  (v : value)
  : P v :=
  match v with
  | VBottom => fbot
  | VInt n => fint n
  | VBool b => fbool b
  | VLoc l v' => floc l v' (value_ind' P fbot fint fbool floc fptr ftuple v')
  | VPtr l => fptr l
  | VTuple vl =>
      ftuple vl 
      ((fix F vl :=
        match vl as vl0 return ForallT P vl0 with
        | [] => @ForallT_nil value P
        | v' :: vl' =>
            @ForallT_cons value P v' vl'
              (value_ind' P fbot fint fbool floc fptr ftuple v')
              (F vl')
        end) vl)
  end.

Variant nodes :=
| NBottom
| NInt (n : nat)
| NBool (b : bool)
| NLoc (l : loan_id)
| NPtr (l : loan_id)
| NTuple (n : nat)
.

Instance EqDec_HLPL_nodes : EqDecision nodes.
Proof. unfold EqDecision, Decision. repeat decide equality. Qed.

Definition HLPL_arity c := match c with
| NBottom => 0
| NInt _ => 0
| NBool _ => 0
| NLoc _ => 1
| NPtr _ => 0
| NTuple n => n
end.

Definition HLPL_get_node v := match v with
| VBottom => NBottom
| VInt n => NInt n
| VBool b => NBool b
| VLoc l _ => NLoc l
| VPtr l => NPtr l
| VTuple t => NTuple (List.length t)
end.

Definition HLPL_children v := match v with
| VBottom => []
| VInt _ => []
| VBool _ => []
| VLoc _ v => [v]
| VPtr l => []
| VTuple t => t
end.

Definition HLPL_fold c vs := match c, vs with
| NInt n, [] => VInt n
| NBool b, [] => VBool b
| NLoc l, [v] => VLoc l v
| NPtr l, [] => VPtr l
| NTuple n, t => VTuple t
| _, _ => VBottom
end.

Fixpoint HLPL_weight node_weight v :=
  match v with
  | VLoc l v => node_weight (NLoc l) + HLPL_weight node_weight v
  | VTuple t => node_weight (HLPL_get_node (VTuple t)) +
                 sum (map (HLPL_weight node_weight) t)
  | v => node_weight (HLPL_get_node v)
end.

Program Instance ValueHLPL : Value value nodes := {
  arity := HLPL_arity;
  get_node := HLPL_get_node;
  children := HLPL_children;
  fold_value := HLPL_fold;
  vweight := HLPL_weight;
  bot := VBottom;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_node eq_children; inversion eq_node; inversion eq_children;
    simpl in *; congruence. 
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] | idtac ];
   simpl in * ; congruence.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] | idtac ];
  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; unfold HLPL_children; cbn ; try lia.
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

Declare Scope hlpl_scope.
Delimit Scope hlpl_scope with hlpl.

(* Notation "'bot'" := VBottom: hlpl_plus_scope. *)
Notation "'loc' ( l , v )" := (VLoc l v) : hlpl_scope.
Notation "'ptr' ( l )" := (VPtr l) : hlpl_scope.

Notation "'nbot'" := NBottom: hlpl_scope.
Notation "'nloc' ( l )" := (NLoc l) : hlpl_scope.
Notation "'nptr' ( l )" := (NPtr l) : hlpl_scope.

(* Bind Scope hlpl_scope with HLPL_val. *)
Open Scope hlpl_scope.

Lemma sget_loc l v p : (loc (l, v)).[[ [0] ++  p]] = v.[[p]].
Proof. reflexivity. Qed.
Hint Rewrite sget_loc : spath.
Lemma sget_loc' l v : (loc(l, v)).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite sget_loc' : spath.

Lemma valid_vpath_loc (vp : vpath) (v : value) : 
  forall l,
  valid_vpath (loc (l, v)) vp ->
  (vp = []) \/ (exists vp', vp = 0 :: vp' ).
Proof.
  intros ? Hvp. destruct vp as [ | [ | n' ] vp' ].
  - left; reflexivity.
  - right. exists vp'; reflexivity.
  - inversion Hvp ; subst. simpl in H2. rewrite nth_error_nil in H2. easy.
Qed.

Lemma not_value_contains_struct_loc (v : value) (f : nodes -> Prop) :
  forall l,
  not_value_contains f (loc (l, v))
  <-> not_value_contains f v /\ ~ f (nloc (l)).
Proof.
  split.
  {
    intros H. split.
    - intros p Hvp. apply (H (0 :: p)). eapply valid_cons ; auto.
    - apply (H []). apply valid_nil.
  }
  {
    intros [H1 Hp ] p Hvp.
    simpl. 
    destruct (valid_vpath_loc p v l) as [ Hempty | [vp' ?] ] ; subst ; simpl ; auto.
    apply H1. inversion Hvp ; subst. simpl in H3. congruence.
  }
Qed.

(* This property represents the application of a projection p (such as a pointer dereference or a
 * field access) on spath pi0, on a state S.
 * If this projection is successful, then we have eval_proj S p pi0 pi1.
 *)
Variant eval_proj (S : state) : proj -> spath -> spath -> Prop :=
  (* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
  | E_Deref_Ptr_Locs q q' l
      (get_q : get_node (S.[q]) = nptr(l)) (get_q' : get_node (S.[q']) = nloc(l)) :
    eval_proj S Deref q q'
  | E_Field q n k
      (get_q : get_node (S.[q]) = NTuple n) (index: k < n) :
    eval_proj S (Field k) q (q +++ [k])
.

Variant eval_loc (S : state) : spath -> spath -> Prop :=
  (* Coresponds to R-Loc and W-Loc in the article. *)
  | E_Loc q l
      (get_q : get_node (S.[q]) = nloc(l)) :
    eval_loc S q (q +++ [0])
.

(* Let pi0 be a spath. If by successfully applying the projections in P we
   obtain a spath pi1, then we have the proprety eval_path S P pi0 pi1. *)
Inductive eval_path (S : state) : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S proj p q) (Heval_path : eval_path S P q r) :
    eval_path S (proj :: P) p r
| Eval_path_loc P p q r
    (Heval_loc : eval_loc S p q) (Heval_path_rec : eval_path S P q r) :
    eval_path S P p r
.

Definition eval_place S (p : place) pi :=
  let pi_0 := (encode_var (fst (fst p)), []) in
  valid_spath S pi_0 /\ eval_path S (snd (fst p)) (encode_var (fst (fst p)), []) pi.

Notation "S  |-{p}  p => pi" := (eval_place S p pi) (at level 50).

Lemma eval_proj_valid S proj q r (H : eval_proj S proj q r) : valid_spath S r.
Proof.
  destruct H ; validity.
Qed.

Lemma eval_loc_valid S q r (H : eval_loc S q r) : valid_spath S r.
Proof.
  destruct H ; validity.
Qed.

Lemma eval_path_valid (s : state) P q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
  - apply IHeval_q_r. destruct Heval_loc. validity.
Qed.

Lemma eval_place_valid s p pi (H : eval_place s p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loc : nodes -> Prop :=
| IsLoc_Loc l : is_loc (nloc(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.
Hint Extern 0 (~is_loc _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = nbot) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> nbot) => discriminate : spath.

Definition get_loc_id c :=
  match c with
  | nloc(l) => Some l
  | nptr(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loc_id c = Some l) S).

Lemma is_fresh_loc_id_neq (S : state) l0 l1 (p : spath) :
  get_loc_id (get_node (S.[p])) = Some l0 -> is_fresh l1 S -> l0 <> l1.
Proof.
  intros get_p Hfresh <-. eapply Hfresh; [ | exact get_p].
  apply get_not_bot_valid_spath. intro H. rewrite H in get_p. inversion get_p.
Qed.


Hint Extern 0 (get_loc_id _ <> Some ?l) =>
  lazymatch goal with
  | Hfresh : is_fresh ?l ?S, get_p : get_node (?S.[?p]) = ?v |- _ =>
      injection;
      refine (is_fresh_loc_id_neq S _ l p _ Hfresh);
      rewrite get_p;
      reflexivity
   end : spath.

(** ** Automation. *)
(** A tactic to prove that a value or state does not contain some node (ex: loan, loc, bot).
    This tactic tries to solve this by applying the relevant lemmas, and never fails. *)
(* Note: Can we remove the automatic rewriting out of this tactic? *)
(* TODO: precise the "workflow" of this tactic. *)
Ltac not_contains0 :=
  try assumption;
  match goal with
  | |- True => auto
  | |- not_state_contains ?P (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset;
      not_contains0
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset_disj;
        [auto with spath; fail | not_contains0]
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset;
       [ not_contains0 | not_contains0 | validity0]
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget _ S p H);
      validity0
  | |- not_value_contains ?P (?v.[[?p <- ?w]]) =>
      simple apply not_value_contains_vset; not_contains0
  | |- not_value_contains ?P (?S.[?p]) => idtac

  | |- not_value_contains ?P ?v =>
      simple apply not_value_contains_zeroary; [reflexivity | ]
  | |- not_value_contains ?P ?v =>
      simple eapply not_value_contains_unary; [reflexivity | | not_contains0]
  | |- not_value_contains ?P ?v =>
      simple eapply not_value_contains_nary; [reflexivity | | not_contains0]
  | |- _ => idtac
  end.
Ltac not_contains := not_contains0; eauto with spath.

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w
with copy_tuple_val : list value -> list value -> Prop :=
| Copy_tuple_nil : copy_tuple_val [] []
| Copy_tuple_cons vl1 vl2 v1 v2
    (Hcopy : copy_val v1 v2)
    (Hcopy_tuple : copy_tuple_val vl1 vl2) :
  copy_tuple_val (v1 :: vl1) (v2 :: vl2).

Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Inductive eval_operand : operand -> state -> (value * state) -> Prop :=
  | E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
  | E_BoolConst S b : S |-{op} Const (BoolConst b) => (VBool b, S)
  | E_Copy S (p : place) pi v
      (Heval_place : eval_place S p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
  | E_Move S (p : place) pi :
    eval_place S p pi ->
    not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
  | E_Tuple S S' opl vl
      (H : eval_tuple opl S (vl, S')) :
    S |-{op} Tuple opl => (VTuple vl, S')
where "S |-{op} op => r" := (eval_operand op S r)
  with eval_tuple : list operand -> state -> (list value * state) -> Prop :=
  | E_Tuple_Nil S : eval_tuple [] S ([], S)
  | E_Tuple_Cons S S' S'' op opl v v'
      (Hop : eval_operand op S (v, S'))
      (Hrec : eval_tuple opl S' (v', S'')) :
    eval_tuple (op :: opl) S (v :: v', S'')
.

Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Le m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  | E_BinOp S S' S'' binop op_0 op_1 v0 v1 w
      (eval_op_0 : S |-{op} op_0 => (v0, S'))
      (eval_op_1 : S' |-{op} op_1 => (v1, S''))
      (Hbinop : eval_binary_op binop v0 v1 w) :
      S |-{rv} (BinaryOp binop op_0 op_1) => (w, S'')
   | E_Pointer_Loc S p pi l
      (Heval_place : S |-{p} p => pi)
      (Hloc : get_node (S.[pi]) = nloc(l)) : S |-{rv} &mut p => (ptr(l), S)
  | E_Pointer_Fresh S p pi l
      (Heval_place : S |-{p} p => pi) :
      is_fresh l S ->
      S |-{rv} (&mut p) => (VPtr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).
(* TODO: add rule for pairs *)

Lemma copy_no_loc (v v' : value) :
  copy_val v v' -> not_contains_loc v'
with copy_tuple_no_loc (vl vl' : list value) :
  copy_tuple_val vl vl' -> Forall not_contains_loc vl'.
Proof.
  { intros copy. induction copy ; unfold not_contains_loc ; not_contains. }
  { intros copy. induction copy ; constructor ; eauto. }
Qed.

Lemma eval_operand_no_loc (S : state) (op : operand) (vS' : value * state) :
  S |-{op} op => vS' -> not_contains_loc vS'.1
with  eval_tuple_no_loc (S : state) (opl : list operand) (vlS' : list value * state) :
  eval_tuple opl S vlS' -> Forall (not_contains_loc) vlS'.1.
Proof.
  {
    intros eval_op ; induction eval_op ;
    try (unfold not_contains_loc ; not_contains).
  + simpl. by apply copy_no_loc with (v := S.[ pi ]).
  + simple eapply not_value_contains_nary ; [ easy |].
    remember (vl, S') as vlS'. replace vl with (vlS'.1) by (subst ; reflexivity).
    clear HeqvlS'. induction H.
    - constructor.
    - simpl in *. constructor ; [ | assumption].
       replace v with ((v, S'0).1) by (simpl ; reflexivity).
       apply eval_operand_no_loc with (S := S) (op := op) ; auto.
  }
  {
    intros eval_t. induction eval_t ; [ constructor | ].
    simpl. constructor ; [ | assumption ]. replace v with ((v, S').1) by reflexivity.
    apply eval_operand_no_loc with (S := S) (op := op) ; auto.
  }
Qed.

Lemma eval_rvalue_no_loc (S: state) (rv : rvalue) (vS : value * state) :
  S |-{rv} rv => vS -> not_contains_loc vS.1.
Proof.
  intros Hrv ; induction Hrv ; try (unfold not_contains_loc ; not_contains).
  - eapply eval_operand_no_loc, Heval_op.
  - induction Hbinop ; simpl ; not_contains.
Qed.

Inductive reorg : state -> state -> Prop :=
| Reorg_end_ptr S (p : spath) l :
    get_node (S.[p]) = NPtr(l) -> reorg S (S.[p <- bot])
| Reorg_end_loc S (p : spath) l :
    get_node (S.[p]) = NLoc(l) -> not_state_contains (eq (NPtr l)) S ->
    reorg S (S.[p <- S.[p +++ [0] ] ])
.

(* Automatically resolving the goals of the form `ptrC(l) <> _`, used to prove the condition
   `not_state_contains (eq ptrC(l)) S` of the rule Reorg_end_loc. *)
Hint Extern 0 (NPtr( _ ) <> _) => discriminate : spath.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : (S,, a |-> v) |-{p} p => sp):
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_state -> statement -> nat -> Option (statement_result * HLPL_state) -> Prop
*)
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
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(* Test the semantics *)

Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

Fixpoint decide_not_value_contains (P : nodes -> bool) v :=
  negb (P (get_node v)) &&
    match v with
      loc(l, w) => decide_not_value_contains P w
    | VTuple vl =>
        forallb (decide_not_value_contains P) vl
    | _ => true end.

Lemma decide_not_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  decide_not_value_contains P v = true -> not_value_contains H v.
Proof.
  intro decide_is_true. induction v using value_ind'.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    * cbn in *. intros G%H_implies_P.
      apply andb_prop in decide_is_true as (? & _). rewrite G in H0. discriminate.
    * rewrite nth_error_nil in H0. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *.
      intros G%H_implies_P. rewrite G in decide_is_true. inversion decide_is_true.
    + destruct i.
      * cbn in *; subst. apply IHv. eapply andb_prop, decide_is_true.
        inversion H0. auto.
      * simpl in H0. rewrite nth_error_nil in H0; discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *. intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + cbn in *. rewrite nth_error_nil in * |-. discriminate.
  - intros p valid_p. inversion valid_p; subst ; cbn in *.
    + intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + rewrite H1. apply (ForallT_nth _ vl i w) in H0 ; [ | assumption ].
      apply H0 ; [ | assumption ].
      apply andb_prop in decide_is_true as (_ & dit).
      apply nth_error_In in H1.
      apply forallb_forall with (x := w) in dit ; auto.
Qed.

Definition decide_is_bot v := match v with NBottom => true | _ => false end.

Corollary decide_not_contains_bot v (H : decide_not_value_contains decide_is_bot v = true) :
  not_contains_bot v.
Proof. eapply decide_not_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Definition decide_not_state_contains (P : nodes -> bool) (S : state) :=
  map_fold (fun k v b => decide_not_value_contains P v && b) true (get_map S).

Lemma decide_state_contains_correct H P S (H_implies_P : forall v, H v -> P v = true) :
  decide_not_state_contains P S = true -> not_state_contains H S.
Proof.
  intros G p. unfold sget. intros (v & getval_S & ?). rewrite getval_S.
  intros H_in_v.
  unfold decide_not_state_contains in G.
  erewrite map_fold_delete_L in G; [ | intros; ring | eassumption].
  destruct (decide_not_value_contains P v) eqn:EQN.
  - eapply decide_not_value_contains_correct in EQN; [ | eassumption].
    eapply EQN; eassumption.
  - rewrite andb_false_l in G. discriminate.
Qed.

Definition decide_is_loc v := match v with nloc(l) => true | _ => false end.
Definition decide_is_loc_id l v :=
  match v with
  | nloc(l') | nptr(l') => Pos.eqb l l'
  | _ => false
  end.


Lemma decide_is_fresh S l (H : decide_not_state_contains (decide_is_loc_id l) S = true) :
  is_fresh l S.
  Proof.
    eapply decide_state_contains_correct; try eassumption.
    intros c G. destruct c; inversion G; apply Pos.eqb_refl.
  Qed.


Notation x := 1%positive.
Notation y := 2%positive.
Notation z := 3%positive.
Notation a := 1%positive.
Notation b := 2%positive.
Notation c := 3%positive.
Notation d := 4%positive.
Notation a1 := 1%positive.
Notation a2 := 2%positive.
Notation a3 := 3%positive.
Notation a4 := 4%positive.
Notation a5 := 5%positive.
Notation a6 := 6%positive.
Notation l1 := 1%positive.
Notation l2 := 2%positive.

Definition prog :=
  ASSIGN (x, nil, TInt) <- Use (INT 3) ;;
  ASSIGN (y, nil, TInt) <- &mut (1%positive, nil, TInt).

Definition main : statement :=
  ASSIGN (a, [], TInt) <- Use (INT 1983) ;;
  ASSIGN (b, [], TInt) <- Use (INT 1986) ;;
  ASSIGN (c, [], TInt) <- &mut (a, [], TInt);;
  ASSIGN (d, [], TInt) <- &mut (c, [Deref], TInt);;
  ASSIGN (c, [], TInt) <- &mut (b, [], TInt);;
  ASSIGN (d, [Deref], TInt) <- Use (INT 58) ;;
  Nop
.

Definition main_pair : statement :=
  ASSIGN (a, [], TTuple [TInt ; TInt]) <- Use (Tuple [ INT 667 ; INT 1986 ]) ;;
  ASSIGN (b, [], TInt) <- Use (Move (a, [ Field (0)], TInt)) ;;
  ASSIGN (c, [], TRef TInt) <- &mut (a, [Field (1)], TInt);;
  Nop
.

Section SemTest.

  Local Open Scope positive.
  Local Open Scope stdpp.

  Hint Rewrite (@alter_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singleton];
    autorewrite with core.

  Definition empty_state : state :=
    {| vars := {[ x := VInt 0; y := VInt 0 ]} ; anons := PEmpty |}.
  Definition empty_state' : state :=
    {|
      vars := {[ a := bot; b := bot; c := bot; d := bot ]} ;
      anons := PEmpty
    |}.


(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
  Ltac eval_var :=
    split; [eexists; split; [reflexivity | constructor] | ].


  Goal exists final_state, empty_state |-{stmt} prog => rUnit, final_state. 
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      + repeat constructor.
      + apply Store with (a := a1).
        * eval_var; constructor.
        * reflexivity.
    }
    {
      eapply E_Assign.
      + simpl. eapply E_Pointer_Fresh with (l := l1).
        * eval_var; constructor.
        * apply decide_is_fresh. easy.
      + apply Store with (a := a2).
        * eval_var; constructor. 
        * reflexivity.
    }
  Qed.

  Goal exists final_state, empty_state' |-{stmt} main => rUnit, final_state.
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store with (a := a1) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store with (a := a2) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - eapply E_Pointer_Fresh with (l := l1); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store with (a := a3) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Loc with (pi := (encode_var 1, [])).
        * repeat econstructor; try easy.
        * reflexivity.
      - apply Store with (a := a4) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Fresh with (l := l2); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store with (a := a5) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store with (a := a6).
        * repeat constructor.
          ** eexists; split; constructor.
          ** simpl. apply Eval_cons with (q := (encode_var 1, []));
             repeat econstructor; easy.
        * reflexivity.
    }
    apply E_Nop.
    Qed.

  Goal exists final_state, empty_state' |-{stmt} main_pair => rUnit, final_state.
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat econstructor.
      - apply Store with (a := a1) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat econstructor. 
        * apply decide_not_value_contains_correct with (P := decide_is_loc).
          ** intros. inversion H; subst; reflexivity.
          ** reflexivity.
        * apply decide_not_contains_bot; reflexivity.
      - apply Store with (a := a2) ; [eval_var | ] ; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Fresh with (l := l1).
        * repeat econstructor.
        * apply decide_is_fresh; reflexivity.
      - apply Store with (a := a3) ; [eval_var | ] ; constructor.
    }
    apply E_Nop.
    Qed.
End SemTest.


Record HLPL_well_formed (S : state) : Prop := {
  at_most_one_loc l : at_most_one_node (nloc(l)) S;
}.

Notation scount c S := (sweight (indicator c) S).

Record HLPL_well_formed_alt (S : state) l : Prop := {
  at_most_one_loc_alt : scount (nloc(l)) S <= 1;
}.

Lemma well_formedness_equiv S : HLPL_well_formed S <-> forall l, HLPL_well_formed_alt S l.
Proof.
  split.
  - intros WF l. destruct WF. split.
    rewrite<- decide_at_most_one_node; easy.
  - intros WF. split; intros l; destruct (WF l).
    apply decide_at_most_one_node; [discriminate | ]. assumption.
Qed.

Lemma vweight_loc weight l v :
  vweight weight (loc(l, v)) = weight (nloc(l)) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_loc : weight.

Lemma vweight_ptr weight l : vweight weight (ptr(l)) = weight (nptr(l)).
Proof. reflexivity. Qed.
Hint Rewrite vweight_ptr : weight.

Lemma vweight_int weight n :
  vweight weight (VInt n) = weight (NInt n).
Proof. reflexivity. Qed.
Hint Rewrite vweight_int : weight.

Lemma vweight_bot weight : vweight weight bot = weight (nbot).
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.
