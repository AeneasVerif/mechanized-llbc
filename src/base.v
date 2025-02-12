Require Import List.
Require Import PeanoNat Lia ZArith.
Require Import OptionMonad.
Import ListNotations.

From stdpp Require Import fin_maps.

Local Open Scope option_monad_scope.

Class EqDec (A : Type) := {
  eq_dec (a b : A) : {a = b} + {a <> b};
}.

Definition indicator {A : Type} `{EqDec A} a b :=
  if eq_dec a b then 1 else 0.

Lemma indicator_same {A} `{EqDec A} (a : A) : indicator a a = 1.
Proof. unfold indicator. destruct (eq_dec a a); congruence. Qed.

Lemma indicator_eq {A} `{EqDec A} (a b : A) : a = b -> indicator a b = 1.
Proof. intros <-. apply indicator_same. Qed.

Lemma indicator_non_zero {A} `{EqDec A} (a b : A) : indicator a b > 0 -> a = b.
Proof. unfold indicator. destruct (eq_dec a b); easy. Qed.

Lemma indicator_diff {A} `{EqDec A} (a b : A) : a <> b -> indicator a b = 0.
Proof. unfold indicator. destruct (eq_dec a b); congruence. Qed.

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

Lemma nth_error_length [A] (l : list A) n x : nth_error l n = Some x -> n < length l.
Proof. intro H. apply nth_error_Some. rewrite H. discriminate. Qed.
Local Hint Resolve nth_error_length : core.

(* TODO: move in a separate file? *)
Section Alter_list.
  Context {A : Type}.

  (* Returns the list where the n-th element has been set to `a`. If n is out of bound,
     returns the list l unchanged. *)
  Fixpoint alter_list (l : list A) n (f : A -> A) :=
  match l, n with
  | nil, _ => nil
  | a :: l', 0 => (f a) :: l'
  | a :: l', S m => a :: (alter_list l' m f)
  end.

  Lemma alter_list_length l f : forall n, length (alter_list l n f) = length l.
  Proof. induction l; intros [ | ]; cbn; auto. Qed.

  Lemma nth_error_alter_list_eq l f :
    forall n, nth_error (alter_list l n f) n = SOME x <- nth_error l n IN Some (f x).
  Proof.
    induction l; intros; try rewrite !nth_error_nil; cbn; simplify_option.
  Qed.

  Corollary nth_error_alter_list_eq_some l f n a (H : nth_error l n = Some a) :
    nth_error (alter_list l n f) n = Some (f a).
  Proof. rewrite nth_error_alter_list_eq, H. reflexivity. Qed.

  Lemma nth_error_alter_list_lt l a :
    forall m n, m < n -> nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct n; try easy. destruct m; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Lemma nth_error_alter_list_gt l a :
    forall m n, m > n -> nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    induction l as [ | b l' IH]; try easy.
    intros m n H. destruct m; try easy. destruct n; try easy.
    apply PeanoNat.lt_S_n in H. cbn. auto.
  Qed.

  Corollary nth_error_alter_list_neq l a m n (H : m <> n) :
    nth_error (alter_list l m a) n = nth_error l n.
  Proof.
    rewrite Nat.lt_gt_cases in H. destruct H.
    - apply nth_error_alter_list_lt. assumption.
    - apply nth_error_alter_list_gt. assumption.
   Qed.

  Lemma alter_list_neq_commute l m n f g (H : m <> n) :
    alter_list (alter_list l m f) n g = alter_list (alter_list l n g) m f.
  Proof.
    apply nth_error_ext. intro i.
    destruct (Nat.eq_dec m i) as [-> | ]; destruct (Nat.eq_dec n i) as [-> | ];
      repeat rewrite nth_error_alter_list_eq || rewrite nth_error_alter_list_neq by auto; easy.
  Qed.

  Lemma alter_list_invariant (l : list A) n x f
    (Hx : nth_error l n = Some x) (Hf : f x = x) : alter_list l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite nth_error_alter_list_eq. autodestruct.
    - rewrite nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equal_Some (l : list A) n x f g
    (Hx : nth_error l n = Some x) (Hfg : f x = g x) : alter_list l n f = alter_list l n g.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equal_None (l : list A) n f
    (Hx : nth_error l n = None) : alter_list l n f = l.
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_compose (l : list A) n f g :
    alter_list (alter_list l n g) n f = alter_list l n (fun x => f (g x)).
  Proof.
    apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
    - rewrite !nth_error_alter_list_eq. autodestruct.
    - rewrite !nth_error_alter_list_neq; auto.
  Qed.

  Lemma alter_list_equiv (l : list A) n f g
    (Hfg : forall x, f x = g x) : alter_list l n f = alter_list l n g.
  Proof.
    destruct (nth_error l n) eqn:EQN.
    - eapply alter_list_equal_Some; eauto.
    - rewrite !alter_list_equal_None; auto.
  Qed.
End Alter_list.

Lemma map_alter_list [A B] l (f : A -> B) g n x : nth_error l n = Some x ->
  map f (alter_list l n g) = alter_list (map f l) n (fun _ => f (g x)).
Proof.
  intro. apply nth_error_ext. intro i. destruct (Nat.eq_dec n i) as [-> | ].
  - rewrite nth_error_map.
    rewrite !nth_error_alter_list_eq.
    rewrite nth_error_map. simplify_option.
  - rewrite nth_error_map.
    rewrite !nth_error_alter_list_neq by assumption.
    rewrite nth_error_map. reflexivity.
Qed.

Definition sum (l : list nat) := fold_right Nat.add 0 l.

Lemma sum_alter_list l n f x : nth_error l n = Some x ->
  (Z.of_nat (sum (alter_list l n f))) = ((Z.of_nat (sum l)) - (Z.of_nat x) + (Z.of_nat (f x)))%Z.
Proof.
  revert l. induction n.
  - intros [ | ? l] [=->]. cbn. lia.
  - intros [ | y l] [=H]. specialize (IHn _ H). cbn. unfold sum in IHn. lia.
Qed.

Lemma sum_ge_element l n x : nth_error l n = Some x -> sum l >= x.
Proof.
  revert l. induction n.
  - intros [ | ? l] [=->]. cbn. lia.
  - intros [ | y l] [=H]. specialize (IHn _ H). cbn. unfold sum in IHn. lia.
Qed.

Lemma sum_non_zero l :
  sum l > 0 -> (exists i x, nth_error l i = Some (S x)).
Proof.
  induction l as [ | y l IH].
  - cbn. lia.
  - intro H. destruct y as [ | z]; cbn in H.
    + specialize (IH H). destruct IH as (i & x & ?). exists (S i), x. assumption.
    + exists 0, z. reflexivity.
Qed.

Lemma sum_zero l : sum l = 0 <-> (forall i, i < length l -> nth_error l i = Some 0).
Proof.
  split.
  - intros ? i Hi. apply nth_error_Some' in Hi. destruct Hi as (x & Hi). rewrite Hi.
    apply sum_ge_element in Hi. f_equal. lia.
  - intros ?. destruct (sum l) eqn:?; [reflexivity | ].
    assert (sum l > 0) as (? & ? & G)%sum_non_zero by lia. rewrite H in G; [discriminate | eauto].
Qed.

Lemma sum_le_one l :
  sum l <= 1 -> (forall i j x y, nth_error l i = Some x -> nth_error l j = Some y -> x > 0 -> y > 0 -> i = j).
Proof.
  intros H. induction l as [ | n l IH].
  - intros i ? x ? G. rewrite nth_error_nil in G. congruence.
  - cbn in H. destruct n.
    + intros [ | i] [ | j] ? ?; [rewrite nth_error_cons_0; simplify_option; lia.. | ].
      rewrite !nth_error_cons_succ.
      assert (sum l <= 1) as G by (unfold sum; lia). specialize (IH G).
      intros. f_equal. eauto.
    + intros i j [ | ] [ | ] Hi Hj Hx Hy; [lia.. | ].
      assert (sum l = 0) as G by (unfold sum; lia).
      destruct i. 2: { cbn in Hi. apply sum_ge_element in Hi. lia. }
      destruct j. 2: { cbn in Hj. apply sum_ge_element in Hj. lia. }
      reflexivity.
Qed.

Lemma sum_unique_one l (H : forall i x, nth_error l i = Some x -> x <= 1)
  (G : forall i j, nth_error l i = Some 1 -> nth_error l j = Some 1 -> i = j) :
  sum l <= 1.
Proof.
  induction l as [ | [ | [ | x]] l IH].
  - cbn. lia.
  - apply IH.
    + intros i. specialize (H (S i)). rewrite nth_error_cons_succ in H. exact H.
    + intros i j ? ?. specialize (G (S i) (S j)). rewrite !nth_error_cons_succ in G.
      injection G; auto.
  - transitivity (1 + sum l); [reflexivity | ].
    destruct (sum l) eqn:?.
    + rewrite Nat.add_0_r. reflexivity.
    + assert (sum l > 0) as (i & x & Hi)%sum_non_zero by lia.
      specialize (H (S i) _ Hi). replace (S x) with 1 in Hi by lia.
      specialize (G (S i) 0 Hi). discriminate G. reflexivity.
  - specialize (H 0 (2 + x)). rewrite nth_error_cons_0 in H.
    assert (2 + x <= 1) by auto. lia.
Qed.

Lemma sum_app l0 l1 : sum (l0 ++ l1) = sum l0 + sum l1.
Proof. unfold sum. induction l0; cbn in *; lia. Qed.

Section Map_sum.
  Context {K : Type}.
  Context {M : Type -> Type}.
  Context `{FinMap K M}.

  (* Contrary to the sum of a list, the sum of a map is defined over a map with in arbitrary value
     type A, and a weight function. *)
  Context {A : Type}.
  Context (weight : A -> nat).

  Definition map_sum : M A -> nat := map_fold (fun _ x n => weight x + n) 0.

  Lemma map_sum_insert m k x : lookup k m = None -> map_sum (insert k x m) = weight x + map_sum m.
  Proof. intros. unfold map_sum. rewrite map_fold_insert_L; [reflexivity | lia | assumption]. Qed.

  Corollary map_sum_delete m k x : lookup k m = Some x -> map_sum m = weight x + map_sum (delete k m).
  Proof. intros G%insert_delete. rewrite<- G at 1. apply map_sum_insert, lookup_delete. Qed.

  Lemma map_sum_non_zero m : map_sum m > 0 -> exists k x, lookup k m = Some x /\ weight x > 0.
  Proof.
    unfold map_sum. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
    - rewrite map_fold_empty. lia.
    - rewrite map_sum_insert by assumption. destruct (weight x) eqn:?.
      + intros (k' & y & ? & ?)%IHm. exists k', y. rewrite lookup_insert_ne by congruence. auto.
      + eexists k, _. rewrite lookup_insert. split; [reflexivity | lia].
  Qed.

  Corollary map_sum_zero m : (forall k x, lookup k m = Some x -> weight x = 0) -> map_sum m = 0.
  Proof.
    intros elems_zero. destruct (map_sum m) eqn:?; [reflexivity | ].
    assert (map_sum m > 0) as (? & ? & get_m & ?)%map_sum_non_zero by lia.
    specialize (elems_zero _ _ get_m). lia.
  Qed.

  Lemma map_sum_le_one m :
    map_sum m <= 1 ->
    forall i j x y, lookup i m = Some x -> lookup j m = Some y -> weight x > 0 -> weight y > 0 -> i = j.
  Proof.
    intros sum_one i j. destruct (decide (i = j)); [auto | ].
    intros ? ? delete_i%insert_delete. rewrite <-delete_i in *.
    rewrite lookup_insert_ne by assumption. intros delete_j%insert_delete.
    rewrite <-delete_j, !map_sum_insert in sum_one
     by (rewrite ?lookup_insert_ne, ?lookup_delete_ne by auto; apply lookup_delete).
    lia.
  Qed.

  Lemma map_sum_unique_one m (elems_at_most_one : forall i x, lookup i m = Some x -> weight x <= 1) :
    (forall i j x y, lookup i m = Some x -> lookup j m = Some y -> weight x > 0 -> weight y > 0 -> i = j) ->
    map_sum m <= 1.
  Proof.
    intros ?. destruct (map_sum m) eqn:?; [lia | ].
    assert (map_sum m > 0) as (k & x & get_m_k & ?)%map_sum_non_zero by lia.
    assert (weight x <= 1) by (eapply elems_at_most_one; eassumption).
    pose proof (sum_m_delete := get_m_k).
    apply map_sum_delete in sum_m_delete. rewrite (map_sum_zero (delete k m)) in sum_m_delete.
    - lia.
    - intros k' y (? & ?)%lookup_delete_Some.
      destruct (weight y) eqn:?.
      + reflexivity.
      + assert (weight y > 0) by lia. exfalso. eauto.
  Qed.
End Map_sum.
