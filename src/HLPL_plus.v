Require Import base.
Require Import PathToSubtree.
Require Import lang.

Variant HLPL_plus_zero :=
| HLPL_plus_bot
| HLPL_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| HLPL_plus_loan (l : loc)
| HLPL_plus_ptr (l : loc).

Variant HLPL_plus_unit :=
| HLPL_plus_borrow (l : loc)
| HLPL_plus_loc (l : loc).

Variant HLPL_plus_bin := .

Definition HLPL_plus_val := value HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin.

Variant HLPL_plus_binder :=
| Var (v : var)
(* | Box (l : nat) *)
| Anon.

Program Global Instance EqDec_binder : EqDec HLPL_plus_binder.
Next Obligation. repeat decide equality. Qed.

Definition HLPL_plus_state := state HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin HLPL_plus_binder.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

Reserved Notation "'bot'" (at level 50).
Reserved Notation "'loan^m' l" (at level 50).
Reserved Notation "'borrow^m' l v" (at level 50).
Reserved Notation "'loc' l v" (at level 50).
Reserved Notation "'ptr' l" (at level 50).

Notation "'bot'" := (@vZero HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin HLPL_plus_bot): hlpl_plus_scope.
Notation "'loan^m' l" := (@vZero HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin (HLPL_plus_loan l))
  : hlpl_plus_scope.
Notation "'ptr' l" := (@vZero HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin (HLPL_plus_ptr l))
  : hlpl_plus_scope.
Notation "'borrow^m' l v" := (@vUnit HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin (HLPL_plus_borrow l) v)
  : hlpl_plus_scope.
Notation "'loc' l v" := (@vUnit HLPL_plus_zero HLPL_plus_unit HLPL_plus_bin (HLPL_plus_loc l) v)
  : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with HLPL_plus_val. *)
Open Scope hlpl_plus_scope.

(* TODO: add a permission parameter. *)
Inductive eval_path : HLPL_plus_state -> path -> permission -> spath -> spath -> Prop :=
| Eval_nil s perm pi : eval_path s nil perm pi pi
| Eval_deref_borrow_mut s p q : eval_path s (Deref :: p) Mut p (0 :: q)
