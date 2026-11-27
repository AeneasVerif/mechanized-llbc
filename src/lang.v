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
Scheme All for list.

Inductive type :=
| TInt
| TBool
| TRef (t : type)
| TTuple (tl : list type).

Definition type_eq_dec : EqDecision type.
Proof.
  intros t. induction t as [| | t IHt | tl IH]; intros [| | t' | tl'];
    try (right; discriminate); try (left; reflexivity).
  - destruct (IHt t') as [e|n]; [left; f_equal; exact e | right; congruence].
  - revert tl'.
    induction IH as [|a l Ha _ IHl]; intros [|b l'];
      try (right; congruence); try (left; reflexivity).
    destruct (l b) as [e1|n1]; [|right; congruence].
    destruct (IHl l') as [e2|n2]; [|right; congruence].
    left; congruence.
Defined.

Global Instance EqDecision_type : EqDecision type := type_eq_dec.

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

Lemma operand_ind' (P : operand -> Prop)
  (Hconst : forall c, P (Const c))
  (Hmove  : forall p, P (Move p))
  (Hcopy  : forall p, P (Copy p))
  (Htuple : forall opl, Forall P opl -> P (Tuple opl)) :
  forall op, P op.
Proof.
  fix IH 1.
  intros [c | p | p | opl].
  - apply Hconst.
  - apply Hmove.
  - apply Hcopy.
  - apply Htuple.
    induction opl as [| op opl IHl].
    + constructor.
    + constructor.
      * apply IH.
      * exact IHl.
Qed.

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
