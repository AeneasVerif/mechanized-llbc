Require Import List.
Require Import PeanoNat.
Require Import OptionMonad.

Local Open Scope option_monad_scope.

Class EqDec (A : Type) := {
  eq_dec (a b : A) : {a = b} + {a <> b};
}.

Class Inhabited (A : Type) := {
  default : A
}.

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

  Lemma map_nth_eq_commute l n f g (H : forall x, nth_error l n = Some x -> g (f x) = f (g x)) :
    map_nth (map_nth l n f) n g = map_nth (map_nth l n g) n f.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_map_nth_eq. autodestruct. rewrite H; reflexivity.
    - rewrite !nth_error_map_nth_neq; auto.
  Qed.
End Map_nth.