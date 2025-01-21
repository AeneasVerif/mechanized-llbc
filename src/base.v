Require Import List.
Require Import PeanoNat.
Require Import OptionMonad.
Import ListNotations.

Local Open Scope option_monad_scope.

Class EqDec (A : Type) := {
  eq_dec (a b : A) : {a = b} + {a <> b};
}.

Definition identify {A : Type} `{EqDec A} a b :=
  if eq_dec a b then 1 else 0.

Lemma identify_same {A} `{EqDec A} (a : A) : identify a a = 1.
Proof. unfold identify. destruct (eq_dec a a); congruence. Qed.

Lemma identify_diff {A} `{EqDec A} (a b : A) : a <> b -> identify a b = 0.
Proof. unfold identify. destruct (eq_dec a b); congruence. Qed.

Lemma length_1_is_singleton [A : Type] [l : list A] : length l = 1 -> exists a, l = [a].
Proof.
  intro H. destruct l as [ | a l'].
  - inversion H.
  - exists a. f_equal. apply length_zero_iff_nil. inversion H. auto.
Qed.

(* A variant of the lemma `nth_error_Some` that is more convenient to use.
   Indeed, it let us perform an inversion on the result. *)
Lemma nth_error_Some' [A : Type] (l : list A) n :
  n < length l -> Is_Some (nth_error l n).
Proof.
  intros ?%nth_error_Some. destruct (nth_error l n); [eexists; reflexivity | contradiction].
Qed.

(* TODO: move in a separate file? *)
Section Map_nth.
  Context {A : Type}.

  (* Returns the list where the n-th element has been set to `a`. If n is out of bound,
     returns the list l unchanged. *)
  Fixpoint map_nth (l : list A) n (f : A -> A) :=
  match l, n with
  | nil, _ => nil
  | a :: l', 0 => (f a) :: l'
  | a :: l', S m => a :: (map_nth l' m f)
  end.

  Lemma map_nth_length l f : forall n, length (map_nth l n f) = length l.
  Proof. induction l; intros [ | ]; cbn; auto. Qed.

  Lemma nth_error_map_nth_eq l f :
    forall n, nth_error (map_nth l n f) n = SOME x <- nth_error l n IN Some (f x).
  Proof.
    induction l; intros; try rewrite !nth_error_nil; cbn; simplify_option.
  Qed.

  Corollary nth_error_map_nth_eq_some l f n a (H : nth_error l n = Some a) :
    nth_error (map_nth l n f) n = Some (f a).
  Proof. rewrite nth_error_map_nth_eq, H. reflexivity. Qed.

  Lemma nth_error_map_nth_lt l a :
    forall m n, m < n -> nth_error (map_nth l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct n; try easy. destruct m; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Lemma nth_error_map_nth_gt l a :
    forall m n, m > n -> nth_error (map_nth l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct m; try easy. destruct n; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Corollary nth_error_map_nth_neq l a m n (H : m <> n) :
    nth_error (map_nth l m a) n = nth_error l n.
  Proof.
    rewrite Nat.lt_gt_cases in H. destruct H.
    - apply nth_error_map_nth_lt. assumption.
    - apply nth_error_map_nth_gt. assumption.
   Qed.

  Lemma map_nth_neq_commute l m n f g (H : m <> n) :
    map_nth (map_nth l m f) n g = map_nth (map_nth l n g) m f.
  Proof.
    apply nth_error_ext. intro i.
    destruct (Nat.eq_dec m i) as [-> | ]; destruct (Nat.eq_dec n i) as [-> | ];
      repeat rewrite nth_error_map_nth_eq || rewrite nth_error_map_nth_neq by auto; easy.
  Qed.

  Lemma map_nth_invariant (l : list A) n x f
    (Hx : nth_error l n = Some x) (Hf : f x = x) : map_nth l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite nth_error_map_nth_eq. autodestruct.
    - rewrite nth_error_map_nth_neq; auto.
  Qed.

  Lemma map_nth_equal_Some (l : list A) n x f g
    (Hx : nth_error l n = Some x) (Hfg : f x = g x) : map_nth l n f = map_nth l n g.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_map_nth_eq. autodestruct.
    - rewrite !nth_error_map_nth_neq; auto.
  Qed.

  Lemma map_nth_equal_None (l : list A) n f
    (Hx : nth_error l n = None) : map_nth l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_map_nth_eq. autodestruct.
    - rewrite !nth_error_map_nth_neq; auto.
  Qed.

  Lemma map_nth_compose (l : list A) n f g :
    map_nth (map_nth l n g) n f = map_nth l n (fun x => f (g x)).
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_map_nth_eq. autodestruct.
    - rewrite !nth_error_map_nth_neq; auto.
  Qed.

  Lemma map_nth_equiv (l : list A) n f g
    (Hfg : forall x, f x = g x) : map_nth l n f = map_nth l n g.
  Proof.
    destruct (nth_error l n) eqn:EQN.
    - eapply map_nth_equal_Some; eauto.
    - rewrite !map_nth_equal_None; auto.
  Qed.
End Map_nth.
