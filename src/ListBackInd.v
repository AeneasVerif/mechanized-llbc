From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Theorem list_back_ind : forall (A : Type) (P : list A -> Prop) (Hnil : P []) (Hrec : (forall (a : A) (l : list A), P l -> P (l ++ [a]))), forall (l : list A), P l.
Proof.
  intros A P Hnil Hrec l. 
  remember (length l) as len. generalize dependent l.
  induction len ; intros l Heqlen.
  - symmetry in Heqlen. apply length_zero_iff_nil in Heqlen. subst ; auto.
  - destruct l ; simpl in Heqlen.
    * discriminate.
    * injection Heqlen as Heqlen.
      remember (rev (a :: l)) as alrev.
      destruct alrev as [ | b l'].
    + apply f_equal with (f := @length A) in Heqalrev.
      simpl in Heqalrev. rewrite length_app, Nat.add_comm in Heqalrev.
      simpl in Heqalrev. congruence.
    + specialize (Hrec b (rev l')).
      assert (H : len = length (rev l')).
      {
        apply f_equal with (f := @length A) in Heqalrev.
        simpl in Heqalrev. rewrite length_app, Nat.add_comm in Heqalrev.
        simpl in Heqalrev. injection Heqalrev ; intros ; auto.
        rewrite length_rev. rewrite length_rev in H. congruence.
      }
      specialize (IHlen (rev l') H). specialize (Hrec IHlen).
      assert (H' : rev (b :: l') = rev (rev (a :: l))) by congruence.
      rewrite rev_involutive in H'. rewrite <- H'. simpl. auto.
Qed.
