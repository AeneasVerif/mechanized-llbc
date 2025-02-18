Require Import base.
Require Import PathToSubtree.
Require Import PArith.

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
(* TODO: notation *)
Definition path := list proj.
Definition place : Set := var * path.

Variant operand :=
| IntConst (n : nat) (* TODO: use Aeneas integer types? *)
| Move (p : place)
| Copy (p : place).

Variant rvalue :=
| Just (op : operand)
| BinOp (op_l : operand) (op_r : operand)
| BorrowMut (p : place).

Inductive statement :=
| Nop
| Assign (p : place) (rv : rvalue)
| Seq (stmt_0 : statement) (stmt_1 : statement)
| Panic.


(* TODO: notation scope. *)
Notation "s0 ;; s1" := (Seq s0 s1)
  (at level 100, s1 at level 200, only parsing, right associativity).
Notation "&mut p" := (BorrowMut p) (at level 80).
Notation "'ASSIGN' p <- rv" := (Assign p rv) (at level 90).

Local Open Scope positive_scope.
Check (&mut (1, nil)).
Check (ASSIGN (2, nil) <- &mut (1, nil)).
Check (ASSIGN (1, nil) <- Just (IntConst 3)).
Check (ASSIGN (1, nil) <- Just (IntConst 3) ;; ((ASSIGN (2, nil) <- &mut (1, nil)) ;; Panic)).

(* These definitions are not part of the grammar, but they are common for several (all?) semantics of the LLBC. *)
Definition loan_id := nat.

Variant permission := Imm | Mut | Mov.

Variant statement_result : Set :=
| rPanic
| rUnit. (* Panicless termination. *)
