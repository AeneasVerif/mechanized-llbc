From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.
Import ListNotations.

Require Import PathToSubtree.

Theorem state_path_back_ind {A}
  (P : @spath A -> Prop)
  (Hbase : forall enc_x, P (enc_x, []))
  (Hrec : (forall (n : nat) (sp : spath), P sp -> P (sp +++ [n])))
  (sp : spath) :
  P sp.
Proof.
  rewrite surjective_pairing with (p := sp).
  remember (snd sp) as vp. generalize dependent sp.
  induction vp using rev_ind ; intros sp Hsnd.
  - apply Hbase.
  - remember (fst sp, vp) as sp'.
    rewrite Hsnd, <- surjective_pairing.
    replace sp with (sp' +++ [x]).
    * apply Hrec. rewrite surjective_pairing with (p := sp') in Heqsp'.
      apply base.pair_eq in Heqsp'. destruct Heqsp' as [H1 H2].
      rewrite surjective_pairing. rewrite <- H2 in IHvp.
      apply IHvp ; auto.
    * subst. unfold "+++". simpl. rewrite Hsnd, surjective_pairing. reflexivity.
Qed.
