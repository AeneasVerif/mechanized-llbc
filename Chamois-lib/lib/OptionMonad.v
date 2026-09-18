Require Import List Coqlib.

Declare Scope option_monad_scope.

Notation "'SOME' X <- A 'IN' B" := (match A with Some X => B | None => None end)
         (at level 200, X name, A at level 100, B at level 200)
         : option_monad_scope.

Notation "'ASSERT' A 'IN' B" := (if A then B else None)
         (at level 200, A at level 100, B at level 200)
         : option_monad_scope.

Local Open Scope option_monad_scope.


(** Simple tactics for option-monad *)

Ltac deepest_match exp := 
  match exp with
  | context f [match ?expr with | _ => _ end] => ltac: (deepest_match expr)
  | _ => exp
  end.

Ltac autodestruct :=
  let EQ := fresh "EQ" in 
  match goal with
  | |- context f [match ?expr with | _ => _ end] => 
    let t := ltac: (deepest_match expr) in
    destruct t eqn:EQ; generalize EQ; clear EQ; congruence || trivial
  end.

Ltac simplify_someHyp :=
  match goal with
  | H: None = Some _ |- _  => inversion H
  | H: Some _ = None |- _  => inversion H
  | H: false = true |- _  => inversion H
  | H: true = false |- _  => inversion H
  | H: ?t = ?t |- _ => clear H
  | H: Some _ = Some _ |- _  => inversion H; clear H; subst
  | H: Some _ <> None |- _ => clear H
  | H: None <> Some _ |- _ => clear H
  | H: true <> false |- _ => clear H
  | H: false <> true |- _ => clear H
  | H: _ = Some _ |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = None |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = true |- _ => (try rewrite !H in * |- *); generalize H; clear H
  | H: _ = false |- _ => (try rewrite !H in * |- *); generalize H; clear H
  end.

Ltac simplify_someHyps := 
  repeat (simplify_someHyp; simpl in * |- *).

Ltac try_simplify_someHyps := 
  try (intros; simplify_someHyps; eauto).

Ltac simplify_option := repeat (try_simplify_someHyps; autodestruct); try_simplify_someHyps.

(** Related operations *)

Section MapOpt.
Local Set Implicit Arguments.

Record map_opt_inst (T : Type -> Type) (m : forall [A B : Type] (f : A -> option B), T A -> option (T B))
  : Prop := {
    map_opt_inst_id:
      forall A (a : T A), m Some a = Some a;
    map_opt_inst_bind:
      forall A B C (f : A -> option B) (g : B -> option C) (a : T A),
        m (fun x => SOME y <- f x IN g y) a = (SOME b <- m f a IN m g b);
    map_opt_inst_ext1:
      forall A B (f0 f1 : A -> option B)
        (E : forall x y (F0 : f0 x = Some y), f1 x = Some y)
        (a : T A) (b : T B)
        (M0 : m f0 a = Some b),
        m f1 a = Some b
  }.
Global Arguments map_opt_inst_id   [_ _] _ [_].
Global Arguments map_opt_inst_bind [_ _] _ [_ _ _].
Global Arguments map_opt_inst_ext1 [_ _] _ [_ _].

Section Properties.
  Variables (T : Type -> Type) (m : forall [A B : Type] (f : A -> option B), T A -> option (T B))
            (inst : map_opt_inst T m).
  
Lemma map_opt_inst_bind1 [A B C] [f : A -> option B] [g : B -> option C] [a : T A] [b : T B]
  (F : m f a = Some b):
  m g b = m (fun x => SOME y <- f x IN g y) a.
Proof.
  rewrite (map_opt_inst_bind inst), F. reflexivity.
Qed.

Lemma map_opt_inst_ext [A B] (f0 f1 : A -> option B)
  (E : forall x, f0 x = f1 x) (a : T A):
  m f0 a = m f1 a.
Proof.
  destruct (m f0 a) eqn:M0.
  - eapply (map_opt_inst_ext1 inst) in M0 as ->. reflexivity.
    intros; rewrite <- E; congruence.
  - destruct (m f1 a) eqn:M1; [exfalso; revert M0|reflexivity].
    eapply (map_opt_inst_ext1 inst) in M1 as ->. congruence.
    intros; rewrite E; congruence.
Qed.

Lemma map_opt_inst_alive_annot [A B] (f : A -> option B) (a : T A) (b : T B)
  (ALIVE : m f a = Some b):
  {a' : T {x : A | f x <> None}
      | m (fun x => Some (proj1_sig x)) a' = Some a}.
Proof.
  eassert (f0 : forall (x : A), {x0 : A | x0 = x /\ f x0 <> None}+{f x = None}). {
    intro; case (f x) eqn:F.
    - left; exists x; split; congruence.
    - right; reflexivity.
  }
  unshelve epose (f1 (x : A) := _ : option {x : A | f x <> None}). {
    case (f0 x) as [(x0 & _ & p)|].
    - left. exists x0. exact p.
    - right.
  }
  apply (map_opt_inst_ext1 inst) with (f1 := fun x => SOME y <- f1 x IN f (proj1_sig y)) in ALIVE.
    2:{ intros; unfold f1. case f0 as [(? & X & ?)|D]; simpl; congruence. }
  rewrite (map_opt_inst_bind inst) in ALIVE.
  destruct (m f1 a) as [a'|] eqn:M0 in ALIVE; [|discriminate ALIVE].
  exists a'.
  rewrite (map_opt_inst_bind inst) with (f := fun x => Some (proj1_sig x)) in ALIVE.
  destruct m eqn:M1 in ALIVE; [rewrite M1|discriminate ALIVE].
  rewrite (map_opt_inst_bind1 M0) in M1.
  eapply (map_opt_inst_ext1 inst) in M1.
    erewrite (map_opt_inst_id inst) in M1; congruence.
  unfold f1; do 2 intro.
  case f0 as [(? & X & ?)|]; simpl; inversion 1; congruence.
Qed.

End Properties.

(** Instances *)

(* Composition *)

Lemma map_opt_inst_comp [T U : Type -> Type] (mT mU : forall [A B], _)
  (iT : map_opt_inst T mT)
  (iU : map_opt_inst U mU):
  map_opt_inst (fun X => T (U X)) (fun A B f => mT (mU f)).
Proof.
  split; intros.
  - eapply (map_opt_inst_ext1 iT) with (f0 := Some).
    + injection 1 as <-. apply iU.
    + apply iT.
  - erewrite (map_opt_inst_ext iT) by apply (map_opt_inst_bind iU).
    apply (map_opt_inst_bind iT).
  - eapply iT in M0. exact M0.
    apply iU, E.
Qed.

(* list *)

Fixpoint map_opt {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | nil       => Some nil
  | cons x xs => SOME y  <- f x          IN
                 SOME ys <- map_opt f xs IN
                 Some (cons y ys)
  end.

Lemma map_opt_iff_forall2 [A B] (f : A -> option B) l l':
  map_opt f l = Some l' <-> list_forall2 (fun x y => f x = Some y) l l'.
Proof.
  revert l'; induction l; simpl.
  - split.
    + injection 1 as <-. constructor.
    + inversion 1. reflexivity.
  - split.
    + do 2 autodestruct; injection 3 as <-.
      constructor; auto.
      apply IHl; reflexivity.
    + inversion 1. erewrite H2, (proj2 (IHl _)); eauto.
Qed.

Lemma map_opt_length [A B] (f : A -> option B) l l'
  (MAP : map_opt f l = Some l'):
  length l' = length l.
Proof.
  apply map_opt_iff_forall2 in MAP.
  apply list_forall2_length in MAP as ->.
  reflexivity.
Qed.

Lemma map_opt_tot A B (f : A -> option B) (g : A -> B) (l : list A)
  (F : forall x, In x l -> f x = Some (g x)):
  map_opt f l = Some (map g l).
Proof.
  revert F; induction l; simpl; intro. reflexivity.
  rewrite F, IHl by auto. reflexivity.
Qed.

Lemma map_opt_map [A B C] (f : A -> B) (g : B -> option C) (l : list A):
  map_opt g (map f l) = map_opt (fun x => g (f x)) l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl; autodestruct.
Qed.

Lemma map_list_opt_inst: map_opt_inst list (@map_opt).
Proof.
  split.
  - induction a; simpl; rewrite ?IHa; reflexivity.
  - induction a; simpl; rewrite ?IHa; repeat (simpl; autodestruct); reflexivity.
  - induction a; intros b M0; simpl in M0; revert M0; repeat autodestruct;
    simpl; intros;
    erewrite ?E, ?IHa by first [eassumption|reflexivity];
    exact M0.
Qed.

End MapOpt.

(** Simple lemmas *)

Inductive elim_SOME_someT [A B] (a : option A) (f : A -> option B) (y : B) : Prop :=
  | Elim_SOME_someT (x : A) (SOME_x : a = Some x) (SOME_y : f x = Some y).

Lemma elim_SOME_Some [A B] [a : option A] [f : A -> option B] [y : B]:
  (SOME x <- a IN f x) = Some y ->
  elim_SOME_someT a f y.
Proof.
  autodestruct; econstructor; eauto.
Qed.

