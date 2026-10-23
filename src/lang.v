(** * Mechanized_LLBC.lang : Syntax of LLBC and general definitions. *)
Require Import base.
Require Import PathToSubtree.
From Stdlib Require Import PArith.
From stdpp Require Import pmap gmap.

Definition var := positive.

Variant proj :=
| Deref
| Field (f : nat).

(* Places are the syntactic way of denoting and accessing memory locations. Formally,
   a place is the combination of a variable, and a list of projections called a
   "path". Projections are ordered from the first to the last to be applied.

   Example: the place ( *x ).1 is represented the following way: (x, [*, .1])

   Do not mix paths (syntactical constructs of the language) with vpaths and spaths (the
   canonical way to denotes sub-values in a value of the state.)
*)
Inductive type :=
| TInt
| TRef (t : type)
| TTuple (tl : type_list)
with type_list :=
| TNil
| TCons (t : type) (tl : type_list).

Module TypeList.
  Fixpoint length (tl : type_list) : nat :=
    match tl with
    | TNil => 0
    | TCons _ tl' => S (length tl')
    end.

  Fixpoint to_list (tl : type_list) : list type :=
    match tl with
    | TNil => []
    | TCons t tl => t :: to_list tl
    end.

  Fixpoint from_list (tl : list type) : type_list :=
    match tl with
    | [] => TNil
    | t :: tl => TCons t (from_list tl)
    end.

  Lemma length_from_list (tl : list type) :
    List.length tl = length (from_list tl).
  Proof. induction tl; simpl ; congruence. Qed.

  Lemma length_to_list (tl : type_list) :
    length tl = List.length (to_list tl).
  Proof. induction tl; simpl ; congruence. Qed.

  Fixpoint nth_error (tl : type_list) (n : nat) : option type :=
    match tl, n with
    | TCons t tl, 0 => Some t
    | TCons t tl, S n => nth_error tl n
    | TNil, _ => None
    end.

  Lemma nth_valid_access (tl : type_list) (n : nat) :
    (exists v, nth_error tl n = Some v) <-> n < length tl.
  Proof.
    generalize dependent n. induction tl ; split.
    - intros (? & [=]).
    - intros ?%Nat.nlt_0_r. by exfalso.
    - destruct n ; cbn. lia. intros ?%IHtl. lia.
    - destruct n ; cbn. repeat econstructor. by intros ?%Nat.succ_lt_mono%IHtl.
  Qed.

  Lemma nth_error_type_list_list_equiv tl n :
    nth_error tl n = List.nth_error (to_list tl) n.
  Proof.
    generalize dependent n. induction tl ; intro.
    - rewrite nth_error_nil. reflexivity.
    - destruct n.
      * reflexivity.
      * cbn. rewrite IHtl. reflexivity.
  Qed.

  Fixpoint map {A : Type} (f : type -> A) (tl : type_list) : list A :=
    match tl with
    | TNil => []
    | TCons t tl' => (f t) :: map f tl'
    end.

  Fixpoint mapi_rec {A : Type} (f : nat -> type -> A) (tl : type_list) (n : nat) : list A :=
    match tl with
    | TNil => []
    | TCons t tl' => (f n t) :: mapi_rec f tl' (S n)
    end.

  Definition mapi {A : Type} (f : nat -> type -> A) (tl : type_list) : list A :=
    mapi_rec f tl 0.

  Lemma mapi_rec_length {A : Type} (f : nat -> type -> A) tl n :
    length tl = List.length (mapi_rec f tl n).
  Proof. generalize dependent n. induction tl ; intros ; cbn in * ; auto. Qed.

  Lemma mapi_length {A : Type} (f : nat -> type -> A) tl :
    length tl = List.length (mapi f tl).
  Proof. apply mapi_rec_length. Qed.

  Lemma mapi_rec_nth_error {A : Type} (f : nat -> type -> A) t tl m n :
    nth_error tl n = Some t ->
    List.nth_error (mapi_rec f tl m) n = Some (f (m + n) t).
  Proof.
    intros H. generalize dependent n. generalize dependent m. induction tl ; intros.
    - cbn in H. discriminate.
    - cbn. destruct n.
      * rewrite Nat.add_0_r. cbn. injection H as ->. reflexivity.
      * cbn. rewrite IHtl ; auto. rewrite Nat.add_succ_comm. reflexivity.
  Qed.

  Lemma mapi_nth_error {A : Type} (f : nat -> type -> A) t tl n :
    nth_error tl n = Some t ->
    List.nth_error (mapi f tl) n = Some (f n t).
  Proof.
    intros. unfold mapi. rewrite mapi_rec_nth_error with (t := t) ; auto.
  Qed.
    
  Lemma mapi_rec_shift {A : Type}
    (f : nat -> type -> A) (tl : type_list) (n : nat) :
    mapi_rec f tl (S n) =  mapi_rec (fun n t => f (S n) t) tl n.
  Proof.
    generalize dependent n. induction tl ; intros.
    - reflexivity.
    - cbn in *. f_equal. rewrite IHtl. reflexivity.
  Qed.

  Lemma mapi_rec_unfold {A : Type}
    (f : nat -> type -> A) (t : type) (tl : type_list) (n : nat) :
    mapi_rec f (TCons t tl) n = f n t :: mapi_rec (fun n t => f (S n) t) tl n.
  Proof.
    generalize dependent t. generalize dependent n. induction tl ; intros.
    - reflexivity.
    - cbn in *. f_equal. rewrite IHtl. reflexivity.
  Qed.

  Lemma mapi_unfold {A : Type} (f : nat -> type -> A) (t : type) (tl : type_list) :
    mapi f (TCons t tl) = f 0 t :: mapi (fun n t => f (S n) t) tl.
  Proof.
    unfold mapi. rewrite <- mapi_rec_unfold. reflexivity.
  Qed.

  Lemma mapi_rec_exten {A : Type} (f : nat -> type -> A) (g : nat -> type -> A) tl n :
   (forall n t, f n t = g n t) -> mapi_rec f tl n = mapi_rec g tl n.
  Proof.
    generalize dependent n. induction tl ; intros ; [ reflexivity | ].
    cbn. rewrite IHtl, H ; auto.
  Qed.

  Lemma mapi_exten {A : Type} (f : nat -> type -> A) (g : nat -> type -> A) tl :
   (forall n t, f n t = g n t) -> mapi f tl = mapi g tl.
  Proof. intro. unfold mapi. rewrite mapi_rec_exten with (g := g) ; auto. Qed.

  Lemma typelist_map_is_map {A : Type} (f : type -> A) (tl : type_list) :
    map f tl = List.map f (to_list tl).
  Proof. induction tl ; cbn ; congruence. Qed.
End TypeList.

Declare Scope rtype_scope.
Notation "'t[' ']'" := (TTuple TNil) : rtype_scope.
Notation "'t[' x ']'" := (TTuple (TCons x TNil)) : rtype_scope.
Notation "'t[' x ; y ; .. ; z ']'" :=
  (TTuple (TCons x (TCons y .. (TCons z TNil) ..))) : rtype_scope.

Scheme type_ind' := Induction for type Sort Prop
with type_list_ind' := Induction for type_list Sort Prop.

Fixpoint type_eq_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}
with type_list_eq_dec (l1 l2 : type_list) : {l1 = l2} + {l1 <> l2}.
Proof.
  - decide equality.
  - decide equality.
Defined.

Instance EqDec_type : EqDecision type := type_eq_dec.
Instance EqDec_type_list : EqDecision type_list := type_list_eq_dec.

(* TODO: notation *)
Definition path := list proj.
Definition place : Set := var * path * type.

Variant const :=
| IntConst (n : nat) (* TODO: use Aeneas integer types? *)
| BoolConst (b : bool).

Inductive operand :=
| Const (c : const)
| Move (p : place)
| Copy (p : place)
| Tuple (opl : list operand).

Variant BinOp :=
| BAdd
| BLe.

Variant rvalue :=
| Use (op : operand)
| BinaryOp (b : BinOp) (op_l : operand) (op_r : operand)
| BorrowMut (p : place).

Inductive statement :=
| Nop
| Assign (p : place) (rv : rvalue)
| Seq (stmt_0 : statement) (stmt_1 : statement)
(* Note: this should be generalized to match any enumerations, as booleans should only be a
 * particular type of enumeration. *)
| SwitchBool (op : operand) (stmt_if : statement) (stmt_else : statement)
| Loop (body : statement)
| Panic
| Break
| Continue
.


(* These definitions are not part of the grammar, but they are common for several (all?) semantics of the LLBC. *)
Definition loan_id := positive.

Variant permission := Imm | Mut | Mov.

(* TODO: notation scope. *)
(* TODO: this notation conflicts with a stdpp notation. *)
Notation "s0 ;; s1" := (Seq s0 s1)
  (at level 100, s1 at level 200, only parsing, right associativity).
Notation "&mut p" := (BorrowMut p) (at level 80).
Notation "'ASSIGN' p <- rv" := (Assign p rv) (at level 90).
Notation "'IF'  op  {{  stmt_if  }}  'ELSE'  {{  stmt_else  }}" := (SwitchBool op stmt_if stmt_else)
  (at level 90).
Notation "'LOOP'  {{  body  }}" := (Loop body) (at level 90).
Notation "'INT'  n" := (Const (IntConst n)) (at level 80).
Notation "'BOOL' b" := (Const (BoolConst b)) (at level 80).

Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'loan^m' ( ty , l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'nbot'" (at level 0).
Reserved Notation "'nloan^m'( ty , l )" (at level 0).
Reserved Notation "'nloan^m'( l )" (at level 0).
Reserved Notation "'nborrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'nloc' ( l )" (at level 0, l at next level).
Reserved Notation "'nptr' ( l )" (at level 0).

(* TODO: reserved notation for place evaluation. *)
Reserved Notation "S  |-{op}  op  =>  r" (at level 60).
Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).
Reserved Notation "S  |-{stmt}  stmt  ~>{ n }  B" (at level 50).
Global Reserved Notation "S  |-#  stmt  ~>  B" (at level 50).

(** LLBC is a langage with non-local control-flow management, with the << break >>, << continue >>, << panic >> and << return >> keywords. As such, statements yield a *control-flow token*, that determines the continuation of the computation. *)
Variant flow_token : Set :=
| rPanic
| rUnit (* Panicless termination. TODO: rename. *)
| rBreak
| rContinue
.

(** Control-flow tags can be keys for [gmap]. *)
Global Instance flow_token_eq_dec : EqDecision flow_token.
Proof. unfold EqDecision, Decision. decide equality. Qed.

Definition encode_flow_token r :=
  match r with
  | rPanic => 1%positive
  | rUnit => 2%positive
  | rBreak => 3%positive
  | rContinue => 4%positive
  end.

Definition decode_flow_token r :=
  match r with
  | 1%positive => Some rPanic
  | 2%positive => Some rUnit
  | 3%positive => Some rBreak
  | 4%positive => Some rContinue
  | _ => None
  end.

Program Global Instance flow_token_countable : Countable flow_token := {
  encode := encode_flow_token;
  decode := decode_flow_token
}.
Next Obligation. intros [ ]; reflexivity. Qed.

(** If the execution of the loop body ends on a token [r <> rContinue], computes the tag of the state after the loop. *)
Definition end_loop_tag r : option flow_token :=
  match r with
  (** If the loop ends on a break, the program continues as usual. *)
  | rBreak => Some rUnit
  (** Panics are propagated through the loop. *)
  | rPanic => Some rPanic
  (** Note that [end_loop_tag] is not defined for [rContinue] and [rUnit].
     - If the body ends on [rContinue], it loops back.
     - If the body ends on [rUnit], the behavior is not defined, the program gets stuck. *)
  | _ => None
  end.

Lemma partial_inj_end_loop_tag : partial_inj end_loop_tag.
Proof. intros r0 (? & H) r1. destruct r0; destruct r1; easy. Qed.
