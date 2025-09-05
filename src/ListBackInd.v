From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.
Import ListNotations.

Require Import PathToSubtree.
Require Import HLPL.


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

Theorem state_path_back_ind : forall (P : spath -> Prop) (Hbase : forall enc_x, P (enc_x, [])) (Hrec : (forall (n : nat) (sp : spath), P sp -> P (sp +++ [n]))), forall (sp : spath), P sp.
Proof.
  intros P Hbase Hrec sp. rewrite surjective_pairing with (p := sp).
  remember (snd sp) as vp. generalize dependent sp.
  induction vp using list_back_ind ; intros sp Hsnd.
  - apply Hbase.
  - remember (fst sp, vp) as sp'.
    rewrite Hsnd, <- surjective_pairing.
    replace sp with (sp' +++ [a]).
    * apply Hrec. rewrite surjective_pairing with (p := sp') in Heqsp'.
      apply base.pair_eq in Heqsp'. destruct Heqsp' as [H1 H2].
      rewrite surjective_pairing. rewrite <- H2 in IHvp.
      apply IHvp ; auto.
    * subst. unfold "+++". simpl. rewrite Hsnd, surjective_pairing. reflexivity.
Qed.
