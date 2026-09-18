(** Extension of Coq language with some IO and exception-handling operators.

TODO: integration with http://coq.io/ ?

*)

Require Export ImpPrelude.

Import Notations.
Local Open Scope impure.

(** Printing functions *)

Axiom print: pstring -> ?? unit.
From Stdlib Require Extraction.
Extract Constant print => "ImpIOOracles.print".

Axiom println: pstring -> ?? unit.
Extract Constant println => "ImpIOOracles.println".

Axiom read_line: unit -> ?? pstring.
Extract Constant read_line => "ImpIOOracles.read_line".

Axiom string_of_bool: bool -> ?? pstring.
Extract Constant string_of_bool => "ImpIOOracles.string_of_bool".

Require Import ZArith.
Axiom string_of_Z: Z -> ?? pstring.
Extract Constant string_of_Z => "ImpIOOracles.string_of_Z".

(** timer *)

Axiom timer: forall {A B}, (A -> ?? B)*A -> ?? B.
Extract Constant timer => "ImpIOOracles.timer".

(** Exception Handling *)

Axiom exit_observer: Type.
Extract Constant exit_observer => "((unit -> unit) ref)".

Axiom new_exit_observer: (unit -> ??unit) -> ??exit_observer.
Extract Constant new_exit_observer => "ImpIOOracles.new_exit_observer".

Axiom set_exit_observer: exit_observer * (unit -> ??unit) -> ??unit.
Extract Constant set_exit_observer => "ImpIOOracles.set_exit_observer".

Axiom exn: Type.
Extract Inlined Constant exn => "exn".

Axiom raise: forall {A}, exn -> ?? A.
Extract Constant raise => "raise".

Axiom exn2string: exn -> ?? pstring.
Extract Constant exn2string => "ImpIOOracles.exn2string".

Axiom fail: forall {A}, pstring -> ?? A.
Extract Constant fail => "ImpIOOracles.fail".

Axiom try_with_fail: forall {A}, (unit -> ?? A) * (pstring -> exn -> ??A) -> ??A.
Extract Constant try_with_fail => "ImpIOOracles.try_with_fail".

Axiom try_with_any: forall {A}, (unit -> ?? A) * (exn -> ??A) -> ??A.
Extract Constant try_with_any => "ImpIOOracles.try_with_any".

Notation "'RAISE' e" := (DO r <~ raise (A:=False) e ;; RET (match r with end)) (at level 0): impure_scope.
Notation "'FAILWITH' msg" := (DO r <~ fail (A:=False) msg ;; RET (match r with end)) (at level 0): impure_scope.

Definition _FAILWITH {A:Type} msg: ?? A := FAILWITH msg.

Example _FAILWITH_correct A msg (P: A -> Prop):
  WHEN _FAILWITH msg ~> r THEN P r.
Proof.
  wlp_simplify.
Qed.

Definition assert_k (k: ?? bool) (msg: pstring): ?? unit
  := DO b <~ k;; if b then RET tt else FAILWITH msg.
Extraction Inline assert_k.

Lemma assert_k_correct (k: ?? bool) (msg: pstring):
  WHEN assert_k k msg ~> _ THEN k ~~> true.
Proof.
  wlp_simplify.
Qed.

Definition safe_coerce (k: ?? bool) (msg: pstring): bool
  := has_returned (assert_k k msg).
Extraction Inline safe_coerce.

Lemma safe_coerce_correct (k: ?? bool) (msg: pstring):
  safe_coerce k msg = true -> k ~~> true.
Proof.
  unfold safe_coerce. intros; exploit has_returned_correct; eauto.
  intros (r & X); eapply assert_k_correct; eauto.
Qed.


Notation "'TRY' k1 'WITH_FAIL' s ',' e '=>' k2" := (try_with_fail (fun _ => k1, fun s e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Notation "'TRY' k1 'WITH_ANY' e '=>' k2" := (try_with_any (fun _ => k1, fun e => k2))
    (at level 55, k1 at level 53, right associativity): impure_scope.


Program Definition assert_b (b: bool) (msg: pstring): ?? b=true :=
  match b with
  | true => RET _
  | false => FAILWITH msg
  end.

Lemma assert_wlp_true msg b: WHEN assert_b b msg ~> _ THEN b=true.
Proof.
  wlp_simplify.
Qed.

Lemma assert_false_wlp msg (P: Prop): WHEN assert_b false msg ~> _ THEN P.
Proof.
  simpl; wlp_simplify.
Qed.

Program Definition try_catch_fail_ensure {A} (k1: unit -> ?? A) (k2: pstring -> exn -> ??A) (P: A -> Prop | wlp (k1 tt) P /\ (forall s e, wlp (k2 s e) P)): ?? { r | P r }
  := TRY
        DO r <~ mk_annot (k1 tt);; 
        RET (exist P r _)
     WITH_FAIL s, e => 
        DO r <~ mk_annot (k2 s e);;
        RET (exist P r _).
Obligation 2.
  unfold wlp in * |- *; eauto.
Qed.

Notation "'TRY' k1 'CATCH_FAIL' s ',' e '=>' k2 'ENSURE' P" := (try_catch_fail_ensure (fun _ => k1) (fun s e => k2) (exist _ P _))
    (at level 55, k1 at level 53, right associativity): impure_scope.

Definition is_try_post {A} (P: A -> Prop) k1 k2 : Prop := 
  wlp (k1 ()) P /\ forall (e:exn), wlp (k2 e) P.

Program Definition try_catch_ensure {A} k1 k2 (P:A->Prop|is_try_post P k1 k2): ?? { r | P r }
  := TRY
        DO r <~ mk_annot (k1 ());; 
        RET (exist P r _)
     WITH_ANY e => 
        DO r <~ mk_annot (k2 e);;
        RET (exist P r _).
Obligation 1.
  unfold is_try_post, wlp in * |- *; intuition eauto.
Qed.
Obligation 2.
  unfold is_try_post, wlp in * |- *; intuition eauto.
Qed.

Notation "'TRY' k1 'CATCH' e '=>' k2 'ENSURE' P" := (try_catch_ensure (fun _ => k1) (fun e => k2) (exist _ P _))
    (at level 55, k1 at level 53, right associativity): impure_scope.


Program Example tryex {A} (x y:A) := 
  TRY (RET x)
  CATCH _ => (RET y)
  ENSURE (fun r => r = x \/ r = y).
Obligation 1.
  split; wlp_simplify.
Qed.

Program Example tryex_test {A} (x y:A): 
  WHEN tryex x y ~> r THEN `r <> x -> `r = y.
Proof.
  wlp_simplify. destruct exta as [r [X|X]]; intuition.
Qed.


Program Example try_branch1 {A} (x:A): ?? { r | r = x} := 
  TRY (RET x)
  CATCH e => (FAILWITH "!")
  ENSURE _.
Obligation 1.
  split; wlp_simplify.
Qed.

Program Example try_branch2 {A} (x:A): ?? { r | r = x} := 
  TRY (FAILWITH "!")
  CATCH e => (RET x)
  ENSURE _.
Obligation 1.
  split; wlp_simplify.
Qed.
