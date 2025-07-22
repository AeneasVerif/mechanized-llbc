From Stdlib Require Import List.
From Stdlib Require Import PeanoNat Lia ZArith.
Require Import OptionMonad.
Import ListNotations.

From stdpp Require Import fin_maps pmap gmap.

Local Open Scope option_monad_scope.

Definition indicator {A : Type} `{EqDecision A} (a b : A) :=
  if decide (a = b) then 1 else 0.

Lemma indicator_same {A} `{EqDecision A} (a : A) : indicator a a = 1.
Proof. unfold indicator. destruct (decide (a = a)); congruence. Qed.

Lemma indicator_eq {A} `{EqDecision A} (a b : A) : a = b -> indicator a b = 1.
Proof. intros <-. apply indicator_same. Qed.

Lemma indicator_non_zero {A} `{EqDecision A} (a b : A) : indicator a b > 0 -> a = b.
Proof. unfold indicator. destruct (decide (a = b)); easy. Qed.

Lemma indicator_diff {A} `{EqDecision A} (a b : A) : a <> b -> indicator a b = 0.
Proof. unfold indicator. destruct (decide (a = b)); congruence. Qed.

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

(* TODO: could be removed, to use "list_alter" from stdpp. *)
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

(* TODO: delete *)
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

  Lemma map_sum_empty : map_sum empty = 0.
  Proof. apply map_fold_empty. Qed.

  Lemma map_sum_union m0 m1 : map_disjoint m0 m1 -> map_sum (union m0 m1) = map_sum m0 + map_sum m1.
  Proof.
    intros disj. induction m1 as [ | k x m1 ? _ IHm] using map_first_key_ind.
    - rewrite map_union_empty, !map_sum_empty. lia.
    - rewrite map_disjoint_insert_r in disj. destruct disj as (? & disj).
      specialize (IHm disj).
      rewrite<- insert_union_r by assumption.
      rewrite !map_sum_insert by now rewrite ?lookup_union_None_2.
      lia.
  Qed.
End Map_sum.

Lemma map_sum_kmap {M0 M1 K0 K1 A} `{FinMap K0 M0} `{FinMap K1 M1} (f : K0 -> K1) (m : M0 A) weight :
  Inj eq eq f -> map_sum (M := M1) weight (kmap f m) = map_sum weight m.
Proof.
  intros ?. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - rewrite kmap_empty, !map_sum_empty. reflexivity.
  - rewrite kmap_insert by assumption.
    rewrite !map_sum_insert by (rewrite ?lookup_kmap by assumption; assumption).
    congruence.
Qed.

Definition decode' {A} `{Countable A} (x : positive) :=
  match decode x with
  | Some y => if (decide (encode (A := A) y = x)) then Some y else None
  | None => None
  end.

Lemma decode'_encode {A} `{Countable A} (a : A) : decode' (encode a) = Some a.
Proof. unfold decode'. rewrite decode_encode. destruct decide; easy. Qed.

Lemma decode'_is_Some {A} `{Countable A} x (y : A) : decode' x = Some y <-> encode y = x.
Proof.
  unfold decode'. split.
  - simplify_option.
  - intros G. assert (decode x = Some y). { pose proof (decode_encode y). congruence. }
    simplify_option.
Qed.

Lemma map_alter_not_in_domain `{FinMap K M} `(m : M V) k f :
  lookup k m = None -> alter f k m = m.
Proof.
  intros ?. apply map_eq. intros k'.
  destruct (decide (k = k')) as [<- | ]; simplify_map_eq; reflexivity.
Qed.

Lemma size_kmap `{FinMap K1 M1} `{FinMap K2 M2} {A} f (m : M1 A) :
  Inj eq eq f -> size (kmap (M2 := M2) f m) = size m.
Proof.
  intros ?. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - rewrite kmap_empty, !map_size_empty. reflexivity.
  - rewrite kmap_insert by assumption. rewrite !map_size_insert_None.
    + congruence.
    + assumption.
    + now rewrite lookup_kmap.
Qed.

(* TODO: name similar to "sum_map", could be confusing *)
Section SumMaps.
  Context {V K0 K1 : Type}.
  Context `{FinMap K0 M0}.
  Context `{FinMap K1 M1}.
  Context `{Countable (K0 + K1)}.

  Let encode_inl k := encode (A := K0 + K1) (inl k).
  Let encode_inr k := encode (A := K0 + K1) (inr k).

  Definition sum_maps (m0 : M0 V) (m1 : M1 V) : Pmap V :=
    union (kmap encode_inl m0) (kmap encode_inr m1).

  Local Instance encode_inl_inj : Inj eq eq encode_inl.
  Proof. eapply compose_inj; typeclasses eauto. Qed.

  Local Instance encode_inr_inj : Inj eq eq encode_inl.
  Proof. eapply compose_inj; typeclasses eauto. Qed.

  Lemma lookup_inl_kmap_inr (m1 : M1 V) k :
    kmap (M2 := Pmap) encode_inr m1 !! encode_inl k = None.
  Proof.
    unfold encode_inl, encode_inr. apply lookup_kmap_None.
    - typeclasses eauto.
    - intros ? ?%encode_inj. discriminate.
  Qed.

  Lemma lookup_inr_kmap_inl (m0 : M0 V) k :
    kmap (M2 := Pmap) encode_inl m0 !! encode_inr k = None.
  Proof.
    unfold encode_inl, encode_inr. apply lookup_kmap_None.
    - typeclasses eauto.
    - intros ? ?%encode_inj. discriminate.
  Qed.

  Hint Rewrite lookup_inl_kmap_inr : core.
  Hint Rewrite lookup_inr_kmap_inl : core.

  Lemma sum_maps_lookup_l m0 m1 k :
    lookup (encode_inl k) (sum_maps m0 m1) = lookup k m0.
  Proof.
    unfold sum_maps. rewrite lookup_union_l.
    - apply lookup_kmap. typeclasses eauto.
    - autorewrite with core. reflexivity.
  Qed.

  Lemma sum_maps_lookup_r m0 m1 k :
    lookup (encode_inr k) (sum_maps m0 m1) = lookup k m1.
  Proof.
    unfold sum_maps. rewrite lookup_union_r.
    - apply lookup_kmap. typeclasses eauto.
    - autorewrite with core. reflexivity.
  Qed.

  Lemma sum_maps_alter_inl m0 m1 f k :
    alter f (encode_inl k) (sum_maps m0 m1) = sum_maps (alter f k m0) m1.
  Proof.
    unfold sum_maps, union, map_union.
    rewrite alter_union_with_l; autorewrite with core; try easy.
    rewrite kmap_alter by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_alter_inr m0 m1 f k :
    alter f (encode_inr k) (sum_maps m0 m1) = sum_maps m0 (alter f k m1).
  Proof.
    unfold sum_maps, union, map_union.
    rewrite alter_union_with_r; autorewrite with core; try easy.
    rewrite kmap_alter by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_insert_inl m0 m1 k v :
    insert (encode_inl k) v (sum_maps m0 m1) = sum_maps (insert k v m0) m1.
  Proof.
    unfold sum_maps. rewrite insert_union_l by now autorewrite with core.
    rewrite kmap_insert by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_insert_inr m0 m1 k v :
    insert (encode_inr k) v (sum_maps m0 m1) = sum_maps m0 (insert k v m1).
  Proof.
    unfold sum_maps. rewrite insert_union_r by now autorewrite with core.
    rewrite kmap_insert by typeclasses eauto. reflexivity.
  Qed.

  Lemma sum_maps_eq m0 m1 m0' m1' : sum_maps m0 m1 = sum_maps m0' m1' -> m0 = m0' /\ m1 = m1'.
  Proof.
    intros eq_sums. split; apply map_eq; intros k.
    - erewrite<- !sum_maps_lookup_l, eq_sums. reflexivity.
    - erewrite<- !sum_maps_lookup_r, eq_sums. reflexivity.
  Qed.

  Lemma sum_maps_lookup_None (m0 : M0 V) (m1 : M1 V) k (G : decode' (A := K0 + K1) k = None) :
    lookup k (sum_maps m0 m1) = None.
  Proof.
    apply lookup_union_None_2.
    - rewrite lookup_kmap_None by typeclasses eauto.
      intros ? ->. unfold encode_inl in G. rewrite decode'_encode in G. discriminate.
    - rewrite lookup_kmap_None by typeclasses eauto.
      intros ? ->. unfold encode_inr in G. rewrite decode'_encode in G. discriminate.
  Qed.

  Lemma sum_maps_union m0 m1 m2 :
    sum_maps m0 (union m1 m2) = union (sum_maps m0 m1) (kmap encode_inr m2).
  Proof.
    unfold sum_maps. rewrite kmap_union by typeclasses eauto.
    apply map_union_assoc.
  Qed.

  Lemma sum_maps_delete_inr m0 m1 k :
    delete (encode_inr k) (sum_maps m0 m1) = sum_maps m0 (delete k m1).
  Proof.
    unfold sum_maps. rewrite delete_union. f_equal.
    - apply delete_notin. autorewrite with core. reflexivity.
    - symmetry. apply kmap_delete. typeclasses eauto.
  Qed.

  Lemma size_sum_maps m0 m1 : size (sum_maps m0 m1) = size m0 + size m1.
  Proof.
    unfold sum_maps. rewrite map_size_disj_union.
    - rewrite !size_kmap by typeclasses eauto. reflexivity.
    - rewrite map_disjoint_spec.
      intros ? ? ? (? & -> & _)%lookup_kmap_Some; [ | typeclasses eauto].
      rewrite lookup_inl_kmap_inr. easy.
  Qed.

  Lemma sum_maps_is_Some m0 m1 k : is_Some (lookup k (sum_maps m0 m1)) ->
    (exists i, k = encode_inl i /\ is_Some (lookup i m0)) \/
    (exists i, k = encode_inr i /\ is_Some (lookup i m1)).
  Proof.
    intros get_k. destruct (decode' (A := K0 + K1) k) as [decode_k | ] eqn:EQN.
    - apply decode'_is_Some in EQN. rewrite <-!EQN in *. destruct decode_k as [i | i].
      + left. exists i. replace (encode (inl i)) with (encode_inl i) in * by reflexivity.
        rewrite sum_maps_lookup_l in get_k. auto.
      + right. exists i. replace (encode (inr i)) with (encode_inr i) in * by reflexivity.
        rewrite sum_maps_lookup_r in get_k. auto.
    - rewrite sum_maps_lookup_None in get_k by assumption. inversion get_k. discriminate.
  Qed.
End SumMaps.

(* Collapse the 2-dimensional map of regions into a 1-dimensional map. *)
Section Flatten.
  Context {V : Type}.

  Definition flatten : Pmap (Pmap V) -> gmap (positive * positive) V :=
    map_fold (fun i m Ms => union (kmap (fun j => (i, j)) m) Ms) empty.

  Lemma flatten_insert Ms i m (G : lookup i Ms = None) :
    flatten (insert i m Ms) = union (kmap (fun j => (i, j)) m) (flatten Ms).
  Proof.
    unfold flatten. rewrite map_fold_insert_L.
    - reflexivity.
    - intros. rewrite !map_union_assoc. f_equal. apply map_union_comm.
      apply map_disjoint_spec.
      intros ? ? ? (? & ? & _)%lookup_kmap_Some (? & ? & _)%lookup_kmap_Some. congruence.
      all: typeclasses eauto.
    - assumption.
  Qed.

  Lemma lookup_flatten Ms i j : lookup (i, j) (flatten Ms) = mbind (lookup j) (lookup i Ms).
  Proof.
    induction Ms as [ | k x Ms ? _ IHm] using map_first_key_ind.
    - unfold flatten. rewrite map_fold_empty. simpl_map. reflexivity.
    - rewrite flatten_insert by assumption. destruct (decide (i = k)) as [-> | ].
      + simpl_map. rewrite lookup_union. rewrite lookup_kmap by typeclasses eauto.
        rewrite IHm, H. apply option_union_right_id.
      + simpl_map. rewrite lookup_union_r; [exact IHm | ].
        rewrite lookup_kmap_None by typeclasses eauto. congruence.
  Qed.

  Lemma lookup_None_flatten Ms i j : lookup i Ms = None -> lookup (i, j) (flatten Ms) = None.
  Proof. intros H. rewrite lookup_flatten, H. reflexivity. Qed.

  Lemma lookup_Some_flatten Ms i j m :
    lookup i Ms = Some m -> lookup (i, j) (flatten Ms) = lookup j m.
  Proof. intros H. rewrite lookup_flatten, H. reflexivity. Qed.

  Lemma disj_kmap_flatten Ms i (m : Pmap V) :
    lookup i Ms = None -> map_disjoint (kmap (fun j => (i, j)) m) (flatten Ms).
  Proof.
    intros ?. apply map_disjoint_spec. intros ? ? ? (? & -> & ?)%lookup_kmap_Some.
    - rewrite lookup_None_flatten by assumption. discriminate.
    - typeclasses eauto.
  Qed.

  Lemma flatten_insert' Ms i m (G : lookup i Ms = None) :
    flatten (insert i m Ms) = union (flatten Ms) (kmap (fun j => (i, j)) m).
  Proof. rewrite flatten_insert by assumption. apply map_union_comm, disj_kmap_flatten, G. Qed.

  Lemma alter_flatten f i j Ms :
    alter f (i, j) (flatten Ms) = flatten (alter (alter f j) i Ms).
  Proof.
    induction Ms as [ | k x Ms ? _ IHm] using map_first_key_ind.
    - rewrite !map_alter_not_in_domain by now simpl_map. reflexivity.
    - destruct (decide (i = k)) as [<- | ].
      + rewrite alter_insert.
        rewrite !flatten_insert by assumption.
        unfold union, map_union. rewrite alter_union_with_l.
        * now rewrite kmap_alter by typeclasses eauto.
        * reflexivity.
        * intros ? ?. rewrite lookup_None_flatten; easy.
      + rewrite alter_insert_ne by assumption. rewrite !flatten_insert by now simpl_map.
        unfold union, map_union. rewrite alter_union_with by reflexivity. rewrite IHm.
        rewrite map_alter_not_in_domain.
        * reflexivity.
        * rewrite eq_None_not_Some.
          intros (? & ? & _)%lookup_kmap_is_Some; [congruence | typeclasses eauto].
  Qed.

  Lemma size_flatten M M' :
    map_Forall2 (fun _ m m' => size m = size m') M M' -> size (flatten M) = size (flatten M').
  Proof.
    revert M'. induction M as [ | k x M H _ IHM] using map_first_key_ind.
    - intros ? ->%map_Forall2_empty_inv_l. reflexivity.
    - intros _M' G. apply map_Forall2_insert_inv_l in G; [ | assumption].
      destruct G as (p & M' & -> & ? & ? & ?).
      rewrite !flatten_insert by assumption.
      rewrite !map_size_disj_union by now apply disj_kmap_flatten.
      rewrite !size_kmap by typeclasses eauto.
      erewrite IHM by eassumption. lia.
  Qed.
End Flatten.

(* We need to reason about the permutations of keys of a map m.
 * We can't really use the function kmap f m, because f must be a total injective permutation.
 * Thus, we are going to introduce pkmap f m ("partial key map"), where "f" is a partial function.
 *)

Definition insert_permuted_key {A}
  (f : positive -> option positive) (i : positive) (a : A) (m : Pmap A) :=
  match f i with
  | Some j => insert j a m
  | None => m
  end.

Definition pkmap {A} f : Pmap A -> Pmap A := map_fold (insert_permuted_key f) empty.

(* A permutation needs to be injective for the operation to be sound. *)
Definition partial_inj (f : positive -> option positive) :=
  forall i, is_Some (f i) -> forall j, f i = f j -> i = j.

Lemma pkmap_insert {A} p i x (m : Pmap A) :
  partial_inj p -> lookup i m = None ->
  pkmap p (insert i x m) = insert_permuted_key p i x (pkmap p m).
Proof.
  intros H ?. unfold pkmap. apply map_fold_insert_L.
  - unfold insert_permuted_key. intros j1 j2 ? ? ? diff_j. autodestruct. autodestruct. intros.
    apply insert_commute. intros ?. apply diff_j. eapply H; [auto | congruence].
  - assumption.
Qed.

Lemma lookup_pkmap {A} f i j (m : Pmap A) :
  partial_inj f -> f i = Some j -> lookup j (pkmap f m) = lookup i m.
Proof.
  intros inj_p H. unfold pkmap.
  induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - rewrite map_fold_empty. simpl_map. reflexivity.
  - destruct (decide (i = k)) as [<- | n].
    + rewrite map_fold_insert_first_key by assumption.
      unfold insert_permuted_key. rewrite H. simpl_map. reflexivity.
    + simpl_map. rewrite map_fold_insert_first_key by assumption.
      unfold insert_permuted_key. destruct (f k) eqn:EQN.
      * rewrite lookup_insert_ne.
        -- exact IHm.
       (* By injectivity, we can prove that i = k, which is a contradiction. *)
        -- intros ->. apply n, inj_p; [auto | congruence].
      * exact IHm.
Qed.

Lemma pkmap_delete {A} f i j (m : Pmap A) :
  partial_inj f -> f i = Some j -> pkmap f (delete i m) = delete j (pkmap f m).
Proof.
  intros H G. destruct (lookup i m) as [x | ] eqn:EQN.
  - apply insert_delete in EQN. rewrite <-EQN at 2. rewrite pkmap_insert by now simpl_map.
    unfold insert_permuted_key. rewrite G. symmetry. apply delete_insert.
    erewrite lookup_pkmap by eassumption. simpl_map. reflexivity.
  - rewrite delete_notin by assumption. symmetry. apply delete_notin.
    erewrite lookup_pkmap; eassumption.
Qed.

Lemma lookup_pkmap_rev {A} f j (m : Pmap A) :
  partial_inj f -> is_Some (lookup j (pkmap f m)) -> exists i, f i = Some j.
Proof.
  intros inj_f H. unfold pkmap. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - inversion H. discriminate.
  - rewrite pkmap_insert in H by assumption.
    unfold insert_permuted_key in H. destruct (f k) as [j' | ] eqn:?; [ | auto].
    destruct (decide (j = j')) as [<- | ]; simpl_map.
    + exists k. assumption.
    + apply IHm. assumption.
Qed.

Definition is_equivalence {A} f (m : Pmap A) :=
  partial_inj f /\ forall i, is_Some (lookup i m) -> is_Some (f i).

Lemma size_pkmap {A} f m (H : @is_equivalence A f m) : size (pkmap f m) = size m.
Proof.
  destruct H as (inj_f & dom_f).
  induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite map_size_insert_None by assumption.
    rewrite pkmap_insert by assumption.
    unfold insert_permuted_key. destruct (dom_f k) as (v & Hv); [now simpl_map | ].
    rewrite Hv. rewrite map_size_insert_None, IHm.
    + reflexivity.
    + intros ? (? & ?). apply dom_f. now rewrite lookup_insert_ne by congruence.
    + erewrite lookup_pkmap; eassumption.
Qed.

Lemma pkmap_eq {A} f (m0 m1 : Pmap A) :
  is_equivalence f m0 ->
  (forall i j, f i = Some j -> lookup i m0 = lookup j m1) ->
  size m0 = size m1 ->
  pkmap f m0 = m1.
Proof.
  intros equiv_f H size_eq. apply map_subseteq_size_eq.
  - intros j.
    destruct (lookup j (pkmap f m0)) eqn:EQN; cbn; [ | autodestruct].
    destruct (lookup_pkmap_rev f j m0) as (i & Hi); [apply equiv_f | auto | ].
    erewrite <-H by eassumption.
    erewrite lookup_pkmap in EQN; [ | apply equiv_f | eassumption].
    rewrite EQN. reflexivity.
  - rewrite size_pkmap by assumption. rewrite size_eq. reflexivity.
Qed.

(* When the functions f and g are equal on the domain of m, we can prove equality without any
 * injectivity hypothesis. *)
Lemma pkmap_fun_eq {A} f g (m : Pmap A) (H : forall i, elem_of i (dom m) -> f i = g i) :
  pkmap f m = pkmap g m.
Proof.
  unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
  - reflexivity.
  - rewrite !map_fold_insert_first_key by assumption.
    rewrite IHm.
    + unfold insert_permuted_key. rewrite H; [reflexivity | ]. set_solver.
    + intros i ?. apply H. set_solver.
Qed.

Lemma alter_pkmap {A} f g i j (m : Pmap A) (H : is_equivalence f m) (G : f i = Some j) :
  pkmap f (alter g i m) = alter g j (pkmap f m).
Proof.
  destruct H as (inj_f & H). apply pkmap_eq.
  - split; [assumption | ]. intros ?. rewrite lookup_alter_is_Some. auto.
  - intros i' j' G'. destruct (decide (i = i')) as [<- | n].
    + replace j' with j in * by congruence. simpl_map.
      symmetry. f_equal. apply lookup_pkmap; assumption.
    + simpl_map. rewrite lookup_alter_ne.
      * symmetry. apply lookup_pkmap; assumption.
      * intros <-. apply n. apply inj_f. auto. congruence.
  - rewrite <-!size_dom, !dom_alter, !size_dom. symmetry. apply size_pkmap. split; assumption.
Qed.

Definition equiv_map {A} (m0 m1 : Pmap A) :=
  exists f, is_equivalence f m0 /\ m1 = pkmap f m0.

Global Instance reflexive_equiv_map A : Reflexive (@equiv_map A).
Proof.
  intros m. exists Some. split; [split | ].
  - intros ? _ ? [=]. assumption.
  - auto.
  - unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    + reflexivity.
    + rewrite map_fold_insert_first_key by assumption. rewrite <-IHm. reflexivity.
Qed.

Definition partial_compose {A B C} (f : B -> option C) (g : A -> option B) a :=
  mbind f (g a).

Lemma injective_compose f g :
  partial_inj f -> partial_inj g -> partial_inj (partial_compose f g).
Proof.
  unfold partial_compose. intros inj_f inj_g. intros i (k & H) j ?.
  destruct (g i) eqn:eqn_i; cbn in *; [ | discriminate].
  destruct (g j) eqn:eqn_j; cbn in *; [ | congruence].
  apply inj_g. auto. rewrite eqn_i, eqn_j. f_equal. auto.
Qed.

Global Instance transitive_equiv_map A : Transitive (@equiv_map A).
Proof.
  intros m ? ? (g & ((inj_g & dom_g) & ->)) (f & ((inj_f & dom_f) & ->)).
  assert (is_equivalence (partial_compose f g) m).
  { split.
    - apply injective_compose; assumption.
    - intros i H. unfold partial_compose. specialize (dom_g i H). destruct dom_g as (v & Hv).
      rewrite Hv. apply dom_f. erewrite lookup_pkmap; eassumption. }
  exists (partial_compose f g). split; [assumption | ].
  symmetry. apply pkmap_eq.
  - assumption.
  - unfold partial_compose. intros i j (k & ? & ?)%bind_Some.
    erewrite !lookup_pkmap by eassumption. reflexivity.
  - rewrite !size_pkmap; repeat split; assumption.
Qed.

(* Defining a computable equivalent notion of map equivalence. *)
Definition map_inj {A} (p : Pmap A) :=
  map_Forall (fun i x => map_Forall (fun j y => x = y -> i = j) p) p.

Lemma map_inj_equiv (p : Pmap positive) :
  map_inj p <-> partial_inj (fun i => lookup i p).
Proof.
  split.
  - intros inj_p i (? & pi) j ?. eapply inj_p; [eassumption | | reflexivity]. congruence.
  - intros inj_p i ? pi j ? pj <-. apply inj_p; [auto | congruence].
Qed.

Definition is_permutation {A} (p : Pmap positive) (m : Pmap A) := map_inj p /\ dom p = dom m.

Lemma permutation_is_equivalence {A} p m :
  @is_permutation A p m -> is_equivalence (fun i => lookup i p) m.
Proof.
  intros (inj_p & dom_p). split.
  - rewrite <-map_inj_equiv. assumption.
  - intros ?. rewrite <-!elem_of_dom, dom_p. auto.
Qed.

Global Notation apply_permutation p := (pkmap (fun i => lookup i p)).

Lemma equiv_map_alt {A} (m0 m1 : Pmap A) :
  equiv_map m0 m1 <-> exists p, is_permutation p m0 /\ m1 = apply_permutation p m0.
Proof.
  split.
  - intros (f & equiv_f & ->).
    assert (map_inj (map_imap (fun i _ => f i) m0)). {
      destruct equiv_f as (inj_f & _).
      rewrite map_inj_equiv. intros i Hi j G. rewrite !map_lookup_imap in *.
      destruct (lookup i m0) eqn:eqn_i; cbn in *. 2: { inversion Hi. discriminate. }
      destruct (lookup j m0) eqn:eqn_j; cbn in *. 2: { rewrite G in Hi. inversion Hi. discriminate. }
      apply inj_f; assumption. }
    exists (map_imap (fun i _ => f i) m0). split; [split | ].
    + assumption.
    + destruct equiv_f as (_ & ?). apply dom_imap_L. intros i. rewrite elem_of_dom. firstorder.
    + apply pkmap_fun_eq. setoid_rewrite map_lookup_imap. intros i (? & ->)%elem_of_dom. reflexivity.
  - intros (p & H%permutation_is_equivalence & ->). eexists. split; [exact H | reflexivity].
Qed.

Lemma map_inj_insert {A} p x (y : A) (H : forall i, lookup i p <> Some y) :
  map_inj p -> map_inj (insert x y p).
Proof.
  intros inj_p i j. destruct (decide (i = x)) as [-> | ]; simpl_map.
  - intros [=<-]. intros ? ? ? <-. apply dec_stable. intros ?. simpl_map. eapply H. eassumption.
  - intros ? i' ? ? ?.
    assert (i' <> x). { intros <-. simpl_map. congruence. }
    simpl_map. eapply inj_p; eassumption.
Qed.

Definition id_permutation {A} (m : Pmap A) : Pmap positive := map_imap (fun k _ => Some k) m.

Lemma lookup_id_permutation {A} (m : Pmap A) i :
  is_Some (lookup i m) -> lookup i (id_permutation m) = Some i.
Proof. unfold id_permutation. rewrite map_lookup_imap. intros (? & ->). reflexivity. Qed.

Lemma lookup_id_permutation_is_Some {A} (m : Pmap A) i j :
  lookup i (id_permutation m) = Some j -> i = j.
Proof.
  intros H. destruct (lookup i m) eqn:EQN.
  - rewrite lookup_id_permutation in H by auto. congruence.
  - unfold id_permutation in H. rewrite map_lookup_imap, EQN in H. discriminate.
Qed.

Lemma id_permutation_is_permutation {A} m : @is_permutation A (id_permutation m) m.
Proof.
  split.
  - intros ? ? H ? ? G <-. apply lookup_id_permutation_is_Some in H, G. congruence.
  - apply dom_imap_L. intros ?. rewrite elem_of_dom. firstorder.
Qed.

Lemma apply_id_permutation {A} (m : Pmap A) : apply_permutation (id_permutation m) m = m.
Proof.
  apply pkmap_eq.
  - apply permutation_is_equivalence, id_permutation_is_permutation.
  - intros ? ? ?%lookup_id_permutation_is_Some. congruence.
  - reflexivity.
Qed.
