(** Impure monad for interface with impure code

*)

Require Export Program.
Require Export ImpConfig.

Definition wlp {A:Type} (k: t A) (P: A -> Prop): Prop
  := forall a, mayRet k a -> P a.

(* Notations *)

(* Print Grammar constr. *)

Module Notations.

  Declare Scope impure_scope.
  Bind Scope impure_scope with t.
  Delimit Scope impure_scope with impure.

  Notation "?? A" := (t A) (at level 0, A at level 95): impure_scope.

  Notation "k '~~>' a" := (mayRet k a) (at level 75, no associativity): impure_scope. 

  Notation "'RET' a" := (ret a) (at level 0): impure_scope.

  Notation "'DO' x '<~' k1 ';;' k2" := (bind k1 (fun x => k2))
    (at level 55, k1 at level 53, x at level 99, right associativity): impure_scope.

  Notation "k1 ';;'  k2" := (bind k1 (fun _ => k2))
    (at level 55, right associativity): impure_scope.

  Notation "'WHEN' k '~>' a 'THEN' R" := (wlp k (fun a => R))
    (at level 73, R at level 100, right associativity): impure_scope.

  Notation "'ASSERT' P" := (ret (A:=P) _) (at level 0, only parsing): impure_scope.

End Notations.

Import Notations.
Local Open Scope impure.

Goal ( (?? list nat * ??nat -> nat) = (?? ((list nat) * ?? nat) -> nat) )%type.
Proof.
  apply refl_equal.
Qed.

(* mayRet tactics *)

Ltac mayRet_decompose :=
  match goal with
  | H:mayRet (ret _) _ |- _ => apply mayRet_ret in H; subst
  | H:mayRet (bind _ _) _ |- _ => apply mayRet_bind in H as (?&?EQ&?EQ); subst
  end.

(* wlp lemmas for tactics *)

Lemma wlp_unfold A (k:??A)(P: A -> Prop):
   (forall a, k ~~> a -> P a)
    -> wlp k P.
Proof.
  auto.
Qed.

Lemma wlp_monotone A (k:?? A) (P1 P2: A -> Prop):
    wlp k P1
    -> (forall a, k ~~> a -> P1 a -> P2 a)
    -> wlp k P2.
Proof.
  unfold wlp; eauto.
Qed.

Lemma wlp_forall A B (k:?? A) (P: B -> A -> Prop):
   (forall x, wlp k (P x))
    -> wlp k (fun a => forall x, P x a).
Proof.
  unfold wlp; auto.
Qed.

Lemma wlp_ret A (P: A -> Prop) a:
   P a -> wlp (ret a) P.
Proof.
    unfold wlp.
    intros H b H0.
    rewrite <- (mayRet_ret _ a b H0).
    auto.
Qed.

Lemma wlp_bind A B (k1:??A) (k2: A -> ??B) (P: B -> Prop):
  wlp k1 (fun a => wlp (k2 a) P) -> wlp (bind k1 k2) P.
Proof.
    unfold wlp.
    intros H a H0.
    case (mayRet_bind _ _ _ _ _ H0); clear H0.
    intuition eauto.
Qed.

Lemma wlp_ifbool A (cond: bool) (k1 k2: ?? A) (P: A -> Prop):
 (cond=true -> wlp k1 P) -> (cond=false -> wlp k2 P) -> wlp (if cond then k1 else k2) P.
Proof.
  destruct cond; auto.
Qed.

Lemma wlp_letprod (A B C: Type) (p: A*B) (k: A -> B -> ??C) (P: C -> Prop):
  (wlp (k (fst p) (snd p)) P)
    -> (wlp (let (x,y):=p in (k x y)) P).
Proof.
  destruct p; simpl; auto.
Qed.

Lemma wlp_sum (A B C: Type) (x: A+B) (k1: A -> ??C) (k2: B -> ??C)  (P: C -> Prop):
  (forall a, x=inl a -> wlp (k1 a) P) -> 
  (forall b, x=inr b -> wlp (k2 b) P) -> 
     (wlp (match x with inl a => k1 a | inr b => k2 b end) P).
Proof.
  destruct x; simpl; auto.
Qed.

Lemma wlp_sumbool (A B:Prop) (C: Type) (x: {A}+{B}) (k1: A -> ??C) (k2: B -> ??C)  (P: C -> Prop):
  (forall a, x=left a -> wlp (k1 a) P) -> 
  (forall b, x=right b -> wlp (k2 b) P) -> 
     (wlp (match x with left a => k1 a | right b => k2 b end) P).
Proof.
  destruct x; simpl; auto.
Qed.

Lemma wlp_option (A B: Type) (x: option A) (k1: A -> ??B) (k2: ??B)  (P: B -> Prop):
  (forall a, x=Some a -> wlp (k1 a) P) -> 
  (x=None -> wlp k2 P) -> 
     (wlp (match x with Some a => k1 a | None => k2 end) P).
Proof.
  destruct x; simpl; auto.
Qed.

Lemma revert_wlp_0 [A : Type] [k : ?? A] [P : A -> Prop]:
  wlp k P -> forall (a : A), (k ~~> a) -> P a.
Proof.
  auto.
Qed.

Lemma revert_wlp_1 [A : Type] [k : ?? A] [a : A] [P : Prop]
  (H0 : wlp k (fun b => b = a -> P)) (H1 : k ~~> a): P.
Proof.
  apply H0 in H1; auto.
Qed.


(* Tactics 

MAIN tactics:  
  - xtsimplify "base": simplification using from hints in "base" database (in particular "wlp" lemmas).
  - xtstep "base": only one step of simplification.

For good performance, it is recommanded to have several databases.

*)

Ltac introcomp :=
  let a:= fresh "exta" in
  let H:= fresh "Hexta" in
  intros a H.

(* decompose the current wlp goal using "introduction" rules *)
Ltac wlp_decompose :=
    apply wlp_ret
 || apply wlp_bind
 || apply wlp_ifbool
 || apply wlp_letprod
 || apply wlp_sum
 || apply wlp_sumbool
 || apply wlp_option
 .

(* this tactic simplifies the current "wlp" goal using any hint found via tactic "hint". *) 
Ltac apply_wlp_hint hint :=
    eapply wlp_monotone;
      [ hint; fail | idtac ] ;
      simpl; introcomp.

(* one step of wlp_xsimplify 
*)
Ltac wlp_step hint :=
    match goal with
      | |- (wlp _ _) => 
        wlp_decompose
        || apply_wlp_hint hint
        || (apply wlp_unfold; introcomp)
    end.

(* decompose a sequence of binds into hypotheses that can be introduced with [intros] *)
Ltac wlp_seq :=
  match goal with
  | |- wlp (ret _) _ =>
      apply wlp_ret
  | |- wlp (bind _ _) _ =>
      apply wlp_bind;
      let x := fresh "x" in
      let H := fresh "H" in
      intros x H;
      try wlp_seq;
      revert x H
  end.

(* Produce a goal [WHEN f ~> b THEN b = a -> GOAL] using an hypothesis [f ~~> a] *)
Ltac revert_wlp H :=
  revert H; refine (revert_wlp_1 _).


(* main general tactic 
WARNING: for the good behavior of "wlp_xsimplify", "hint" must at least perform a "eauto".

Example of use:
  wlp_xsimplify (intuition eauto with base).
*)
Ltac wlp_xsimplify hint := 
    repeat (intros; subst; wlp_step hint; simpl; (tauto || hint)).

Ltac wlp_ssimplify hint := 
    repeat (intros; subst; wlp_step hint; simpl; hint).

Create HintDb wlp discriminated.

Ltac wlp_simplify := wlp_xsimplify ltac:(intuition eauto with wlp).
