(* TODO: documentation. *)
From Stdlib Require Import Relations.

From stdpp Require Import fin_maps pmap gmap.

From rustc Require Import OptionMonad.

Local Open Scope option_monad_scope.

Arguments clos_refl_trans {_}.
(* TODO: give a scope. *)
Global Notation "R ^*" := (clos_refl_trans R).

(** Chaining two relations. *)
Definition chain {A B C} (RAB : A -> B -> Prop) (RBC : B -> C -> Prop) a c :=
  exists b, RAB a b /\ RBC b c.

Global Instance reflexive_chain {A} (R S : relation A) `{Reflexive A R} `{Reflexive A S} :
  Reflexive (chain R S).
Proof. intros x. exists x. split; reflexivity. Qed.

Lemma fst_pair {A B} (a : A) (b : B) : fst (a, b) = a. Proof. reflexivity. Qed.

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

Lemma nth_error_singleton {A} (a b : A) i : nth_error [a] i = Some b -> a = b /\ i = 0.
Proof. destruct i; cbn; rewrite ?nth_error_nil; split; congruence. Qed.

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
  Proof. intros G%insert_delete_id. rewrite<- G at 1. apply map_sum_insert, lookup_delete_eq. Qed.

  Lemma map_sum_non_zero m : map_sum m > 0 -> exists k x, lookup k m = Some x /\ weight x > 0.
  Proof.
    unfold map_sum. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
    - rewrite map_fold_empty. lia.
    - rewrite map_sum_insert by assumption. destruct (weight x) eqn:?.
      + intros (k' & y & ? & ?)%IHm. exists k', y. rewrite lookup_insert_ne by congruence. auto.
      + eexists k, _. rewrite lookup_insert_eq. split; [reflexivity | lia].
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
    intros ? ? delete_i%insert_delete_id. rewrite <-delete_i in *.
    rewrite lookup_insert_ne by assumption. intros delete_j%insert_delete_id.
    rewrite <-delete_j, !map_sum_insert in sum_one
     by (rewrite ?lookup_insert_ne, ?lookup_delete_ne by auto; apply lookup_delete_eq).
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

(* TODO: when std++ 1.14 is released, remove this lemma. *)
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
    - apply delete_id. autorewrite with core. reflexivity.
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
    - rewrite !alter_id' by now simpl_map. reflexivity.
    - destruct (decide (i = k)) as [<- | ].
      + rewrite alter_insert_eq.
        rewrite !flatten_insert by assumption.
        unfold union, map_union. rewrite alter_union_with_l.
        * now rewrite kmap_alter by typeclasses eauto.
        * reflexivity.
        * intros ? ?. rewrite lookup_None_flatten; easy.
      + rewrite alter_insert_ne by assumption. rewrite !flatten_insert by now simpl_map.
        unfold union, map_union. rewrite alter_union_with by reflexivity. rewrite IHm.
        rewrite alter_id'.
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

(* TODO: when std++ is released, delete this function. *)
Lemma size_alter {K V M} `{H : FinMap K M} (m : M V) f k : size (alter f k m) = size m.
Proof.
  destruct (lookup k m) eqn:EQN.
  - apply insert_delete_id in EQN. rewrite <-EQN, alter_insert_eq.
    rewrite !map_size_insert_None by now simpl_map. reflexivity.
  - rewrite alter_id' by assumption. reflexivity.
Qed.

(** * Partial key maps, permutations and equivalences. *)
(** The operation [pkmap f], with [f : K -> option K], changes the keys of a maps [m : M K]. It is similar to [kmap], the difference is that the function [f] is partial. The operation [pkmap f k m] is only specified when [f] is injective, and when the domain of [f] contains the domain of [m]. *)
Definition insert_permuted_key `{FinMap KA MA} `{FinMap KB MB} {V}
  (f : KA -> option KB) (i : KA) (v : V) (m : MB V) :=
  match f i with
  | Some j => insert j v m
  | None => m
  end.

(** Currently, [pkmap] only transforms a map [M A] into another map [M A] with same keys. The partial function [f] could map keys of different types ([f : KA -> option KB]), The only reason for this limitation is simplicity. *)
Definition pkmap `{FinMapDom K M} {A} f : M A -> M A := map_fold (insert_permuted_key f) empty.

Definition partial_inj {K} (f : K -> option K) :=
  forall i, is_Some (f i) -> forall j, f i = f j -> i = j.

Section PKMap.
  Context `{FinMapDom K M D}.
  Context `{!LeibnizEquiv D}.

  Lemma pkmap_empty {V} f : pkmap (A := V) (M := M) f empty = empty.
  Proof. apply map_fold_empty. Qed.

  Lemma _pkmap_insert {V} p i x (m : M V) :
    partial_inj p -> lookup i m = None ->
    pkmap p (insert i x m) = insert_permuted_key p i x (pkmap p m).
  Proof.
    intros G ?. unfold pkmap. apply map_fold_insert_L.
    - unfold insert_permuted_key. intros j1 j2 ? ? ? diff_j. autodestruct. autodestruct. intros.
      apply insert_insert_ne. intros ?. apply diff_j. eapply G; [auto | congruence].
    - assumption.
  Qed.

  Lemma pkmap_insert {V} p i j x (m : M V) :
    partial_inj p -> p i = Some j -> lookup i m = None ->
    pkmap p (insert i x m) = insert j x (pkmap p m).
  Proof.
    intros ? G ?. rewrite _pkmap_insert by assumption.
    unfold insert_permuted_key. rewrite G. reflexivity.
  Qed.

  Lemma lookup_pkmap {V} f i j (m : M V) :
    partial_inj f -> f i = Some j -> lookup j (pkmap f m) = lookup i m.
  Proof.
    intros inj_p G. unfold pkmap.
    induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    - rewrite map_fold_empty. simpl_map. reflexivity.
    - destruct (decide (i = k)) as [<- | n].
      + rewrite map_fold_insert_first_key by assumption.
        unfold insert_permuted_key. rewrite G. simpl_map. reflexivity.
      + simpl_map. rewrite map_fold_insert_first_key by assumption.
        unfold insert_permuted_key. destruct (f k) eqn:EQN.
        * rewrite lookup_insert_ne.
          -- exact IHm.
         (* By injectivity, we can prove that i = k, which is a contradiction. *)
          -- intros ->. apply n, inj_p; [auto | congruence].
        * exact IHm.
  Qed.

  Lemma lookup_pkmap_None {V} f j (m : M V) :
    (forall i, f i <> Some j) -> lookup j (pkmap f m) = None.
  Proof.
    intros G. unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    - rewrite map_fold_empty, lookup_empty. reflexivity.
    - rewrite map_fold_insert_first_key by assumption.
      unfold insert_permuted_key at 1. destruct (f k) as [j' | ] eqn:EQN.
      + rewrite lookup_insert_ne by congruence. exact IHm.
      + exact IHm.
  Qed.

  Lemma pkmap_delete {V} f i j (m : M V) :
    partial_inj f -> f i = Some j -> pkmap f (delete i m) = delete j (pkmap f m).
  Proof.
    intros ? G. destruct (lookup i m) as [x | ] eqn:EQN.
    - apply insert_delete_id in EQN. rewrite <-EQN at 2.
      erewrite pkmap_insert by first [eassumption | now simpl_map].
      symmetry. apply delete_insert_id.
      erewrite lookup_pkmap by eassumption. simpl_map. reflexivity.
    - rewrite delete_id by assumption. symmetry. apply delete_id.
      erewrite lookup_pkmap; eassumption.
  Qed.

  Lemma pkmap_fmap {V} f (g : V -> V) (m : M V) (inj_f : partial_inj f) :
    pkmap f (fmap g m) = fmap g (pkmap f m).
  Proof.
    unfold pkmap. induction m as [ | k x m k_fresh ? IHm] using map_first_key_ind.
    - rewrite fmap_empty, map_fold_empty, fmap_empty. reflexivity.
    - rewrite map_fold_insert_first_key, fmap_insert by assumption.
      rewrite map_fold_insert_L.
      * unfold insert_permuted_key. destruct (f k) eqn:EQN.
        -- rewrite fmap_insert. f_equal. exact IHm.
        -- exact IHm.
      * intros ? ? ? ? ? diff ? ?. unfold insert_permuted_key. autodestruct. autodestruct.
        intros. rewrite insert_insert_ne; [reflexivity | ].
        intros ?. apply diff, inj_f; [auto | congruence].
      * rewrite lookup_fmap, k_fresh. reflexivity.
  Qed.

  Lemma lookup_pkmap_rev {V} f j (m : M V) :
    partial_inj f -> is_Some (lookup j (pkmap f m)) -> exists i, f i = Some j.
  Proof.
    intros inj_f G. unfold pkmap. induction m as [ | k x m ? _ IHm] using map_first_key_ind.
    - rewrite pkmap_empty, lookup_empty in G. exfalso. eapply is_Some_None, G.
    - rewrite _pkmap_insert in G by assumption.
      unfold insert_permuted_key in G. destruct (f k) as [j' | ] eqn:?; [ | auto].
      destruct (decide (j = j')) as [<- | ]; simpl_map.
      + exists k. assumption.
      + apply IHm. assumption.
  Qed.

  (* TODO: rename [is_equivalence_map]. *)
  Definition is_equivalence {V} f (m : M V) :=
    partial_inj f /\ forall i, is_Some (lookup i m) -> is_Some (f i).

  (* TODO: rename [map_inj]. *)
  Definition partial_inj_map (p : M K) := partial_inj (fun k => lookup k p).
  Definition is_equivalence_map {V} (p : M K) := is_equivalence (V := V) (fun k => lookup k p).

  Lemma size_pkmap {V} f (m : M V) : is_equivalence f m -> size (pkmap f m) = size m.
  Proof.
    intros (inj_f & dom_f). induction m as [ | k x m ? _ IHm] using map_first_key_ind.
    - rewrite pkmap_empty. reflexivity.
    - rewrite map_size_insert_None by assumption.
      destruct (dom_f k) as (v & Hv); [now simpl_map | ].
      erewrite pkmap_insert by eassumption. rewrite map_size_insert_None, IHm.
      + reflexivity.
      + intros ? (? & ?). apply dom_f. now rewrite lookup_insert_ne by congruence.
      + erewrite lookup_pkmap; eassumption.
  Qed.

  Lemma pkmap_eq {V} f (m0 m1 : M V) :
    is_equivalence f m0 ->
    (forall i j, f i = Some j -> lookup i m0 = lookup j m1) ->
    size m0 = size m1 ->
    pkmap f m0 = m1.
  Proof.
    intros equiv_f G size_eq. apply map_subseteq_size_eq.
    - intros j.
      destruct (lookup j (pkmap f m0)) eqn:EQN; cbn; [ | autodestruct].
      destruct (lookup_pkmap_rev f j m0) as (i & Gi); [apply equiv_f | auto | ].
      erewrite <-G by eassumption.
      erewrite lookup_pkmap in EQN; [ | apply equiv_f | eassumption].
      rewrite EQN. reflexivity.
    - rewrite size_pkmap by assumption. rewrite size_eq. reflexivity.
  Qed.

  (* When the functions f and g are equal on the domain of m, we can prove equality without any
   * injectivity hypothesis. *)
  Lemma pkmap_fun_eq {V} f g (m : M V) (G : forall i, is_Some (lookup i m) -> f i = g i) :
    pkmap f m = pkmap g m.
  Proof.
    unfold pkmap. induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    - rewrite !map_fold_empty. reflexivity.
    - rewrite !map_fold_insert_first_key by assumption.
      rewrite IHm.
      + unfold insert_permuted_key. rewrite G; [reflexivity | ]. simpl_map. auto.
      + intros i ?. apply G. apply lookup_insert_is_Some'. auto.
  Qed.

  Lemma alter_pkmap {V} f g i j (m : M V)
    (f_equiv : is_equivalence f m) (get_j : f i = Some j) :
    pkmap f (alter g i m) = alter g j (pkmap f m).
  Proof.
    destruct f_equiv as (inj_f & G). apply pkmap_eq.
    - split; [assumption | ]. intros ?. rewrite lookup_alter_is_Some. auto.
    - intros i' j' K'. destruct (decide (i = i')) as [<- | n].
      + replace j' with j in * by congruence. simpl_map.
        symmetry. f_equal. apply lookup_pkmap; assumption.
      + simpl_map. rewrite lookup_alter_ne.
        * symmetry. apply lookup_pkmap; assumption.
        * intros <-. apply n. apply inj_f. auto. congruence.

    - rewrite !size_alter. symmetry. apply size_pkmap. split; assumption.
  Qed.

  (* The computable equivalent notion of map equivalence. *)
  (* TODO: move it in src/executions. *)
  (*
  Definition map_inj (p : M K) :=
    map_Forall (fun i x => map_Forall (fun j y => x = y -> i = j) p) p.
   *)

  Lemma is_equivalence_map_dom_eq {V} p (m0 m1 : M V) :
    dom m0 = dom m1 -> is_equivalence_map p m0 -> is_equivalence_map p m1.
  Proof.
    unfold is_equivalence_map, is_equivalence. setoid_rewrite <-elem_of_dom. intros <- ?. auto.
  Qed.

  Corollary is_equivalence_map_fmap {V} p (f : V -> V) (m : M V) :
    is_equivalence_map p m -> is_equivalence_map p (fmap f m).
  Proof. apply is_equivalence_map_dom_eq. symmetry. apply dom_fmap_L. Qed.

  Notation apply_permutation p := (pkmap (fun i => lookup i p)).

  Lemma apply_permutation_insert {V} (p : M K) i j (v : V) m :
    partial_inj_map (insert i j p) -> lookup i m = None ->
    apply_permutation (insert i j p) (insert i v m) = insert j v (apply_permutation p m).
  Proof.
    intros. erewrite pkmap_insert by first [eassumption | now simpl_map].
    f_equal. apply pkmap_fun_eq. intros i' (? & ?). apply lookup_insert_ne. congruence.
  Qed.

  Definition equiv_map {V} (m0 m1 : M V) :=
    exists p, is_equivalence_map p m0 /\ m1 = apply_permutation p m0.

  Lemma lookup_apply_permutation {V} (p : M K) i j (m : M V) :
    partial_inj (fun k => lookup k p) -> lookup i p = Some j ->
    apply_permutation p m !! j = m !! i.
  Proof. intros ? ?. apply lookup_pkmap; assumption. Qed.

  Lemma prove_eq_dom {A B} (m : M A) (m' : M B) :
    dom m = dom m' -> (forall i, is_Some (lookup i m) <-> is_Some (lookup i m')).
  Proof. setoid_rewrite <-elem_of_dom. intros ->. auto. Qed.

  Lemma partial_inj_map_insert p x (y : K) (G : forall i, lookup i p <> Some y) :
    partial_inj_map p -> partial_inj_map (insert x y p).
  Proof.
    intros inj_p i j. destruct (decide (i = x)) as [-> | ]; simpl_map.
    - intros ? ?. apply dec_stable. intros ?. simpl_map. eapply G. eauto.
    - intros i' ?. assert (i' <> x). { intros <-. simpl_map. congruence. }
      simpl_map. eapply inj_p; eassumption.
  Qed.

  Definition id_permutation {A} (m : M A) : M K := map_imap (fun k _ => Some k) m.

  Lemma id_permutation_empty {A} : @id_permutation A empty = empty.
  Proof. apply map_imap_empty. Qed.

  Lemma lookup_id_permutation {V} (m : M V) i :
    is_Some (lookup i m) -> lookup i (id_permutation m) = Some i.
  Proof. unfold id_permutation. rewrite map_lookup_imap. intros (? & ->). reflexivity. Qed.

  Lemma lookup_id_permutation_is_Some {V} (m : M V) i j :
    lookup i (id_permutation m) = Some j -> i = j.
  Proof.
    intros G. destruct (lookup i m) eqn:EQN.
    - rewrite lookup_id_permutation in G by auto. congruence.
    - unfold id_permutation in G. rewrite map_lookup_imap, EQN in G. discriminate.
  Qed.

  Lemma id_permutation_is_equivalence {V} (m : M V) : is_equivalence_map (id_permutation m) m.
  Proof.
    split.
    - intros ? (x & G) ? G'. rewrite G in G'. symmetry in G'.
      apply lookup_id_permutation_is_Some in G, G'. congruence.
    - apply prove_eq_dom, dom_imap_L. intros ?. rewrite elem_of_dom. firstorder.
  Qed.

  Lemma apply_id_permutation {U V} (m : M U) (n : M V)
    (subset_dom : forall k, is_Some (lookup k n) -> is_Some (lookup k m)) :
    apply_permutation (id_permutation m) n = n.
  Proof.
    apply map_eq. intros k. destruct (lookup k m) eqn:EQN.
    - erewrite lookup_pkmap.
      + reflexivity.
      + apply id_permutation_is_equivalence.
      + apply lookup_id_permutation. auto.
    - rewrite lookup_pkmap_None.
      + symmetry. rewrite eq_None_not_Some. rewrite eq_None_not_Some in EQN. auto.
      + intros ? G. rewrite (lookup_id_permutation_is_Some _ _ _ G) in G.
        unfold id_permutation in G. rewrite map_lookup_imap, EQN in G. discriminate.
  Qed.

  Global Instance reflexive_equiv_map V : Reflexive (@equiv_map V).
  Proof.
    intros m. exists (id_permutation m). split.
    - apply id_permutation_is_equivalence.
    - symmetry. apply apply_id_permutation. auto.
  Qed.

  Lemma injective_compose (p q : M K) :
    partial_inj_map p -> partial_inj_map q -> partial_inj_map (map_compose q p).
  Proof.
    intros inj_p inj_q.
    intros ? (? & (? & EQ & ?)%map_lookup_compose_Some_1) ? G.
    rewrite !map_lookup_compose, EQ in G.
    apply inj_p; [auto | ]. destruct (lookup j p); cbn in G; [ | congruence].
    rewrite EQ. f_equal. apply inj_q; auto.
  Qed.

  Lemma compose_permutation {V} p q (m : M V) :
    is_equivalence_map p m -> is_equivalence_map q (apply_permutation p m) ->
    is_equivalence_map (map_compose q p) m.
  Proof.
    intros (inj_p & dom_p) (inj_q & dom_q). split.
    - apply injective_compose; assumption.
    - intros i G. specialize (dom_p _ G). rewrite map_lookup_compose.
      destruct dom_p as (? & get_p_i). rewrite get_p_i. cbn.
      apply dom_q. erewrite lookup_pkmap; eassumption.
  Qed.

  Lemma apply_permutation_compose {V} p q (m : M V) :
    is_equivalence_map p m -> is_equivalence_map q (apply_permutation p m) ->
    apply_permutation (map_compose q p) m = apply_permutation q (apply_permutation p m).
  Proof.
    intros perm_p perm_q. apply pkmap_eq.
    - apply compose_permutation; assumption.
    - intros i j (? & ? & ?)%map_lookup_compose_Some_1.
      erewrite lookup_pkmap; [ | eapply perm_q | eassumption].
      symmetry. apply lookup_pkmap; [ | assumption]. apply perm_p.
    - rewrite !size_pkmap; auto.
  Qed.

  Global Instance transitive_equiv_map V : Transitive (@equiv_map V).
  Proof.
    intros ? ? ? (p & ? & ->) (q & ? & ->). exists (map_compose q p). split.
    - apply compose_permutation; assumption.
    - symmetry. apply apply_permutation_compose; assumption.
  Qed.

  Lemma is_equivalence_map_insert {V} p i (v : V) m :
    is_equivalence p (insert i v m) -> is_equivalence p m.
  Proof.
    intros (inj_p & dom_p). split.
    - exact inj_p.
    - intros k k_in_dom. apply dom_p. rewrite lookup_insert. destruct (decide _); auto.
  Qed.

  Lemma equiv_map_delete {V} m0 m1 i (v : V) :
    lookup i m0 = None -> equiv_map (insert i v m0) m1 ->
    exists j, lookup j m1 = Some v /\ equiv_map m0 (delete j m1).
  Proof.
    intros ? (p & equiv_p & ->). destruct (equiv_p) as (inj_p & dom_p).
    assert (is_Some (lookup i p)) as (j & get_j). { apply dom_p. simpl_map. auto. }
    exists j. split.
    - erewrite pkmap_insert by eassumption. simpl_map. reflexivity.
    - exists p. split.
      + eapply is_equivalence_map_insert. eassumption.
      + erewrite pkmap_insert by eassumption. apply delete_insert_id.
        erewrite lookup_pkmap; eassumption.
  Qed.

  Context `{!Elements K D}.
  Context `{!FinSet K D}.
  Context `{Infinite K}.

  (* An injective map can always be extended so that its domain contains the set s. *)
  Lemma extend_inj_map s m (G : partial_inj_map m) :
    exists m', subseteq m m' /\ subseteq s (dom m') /\ partial_inj_map m'.
  Proof.
    induction s as [ | i ? ? (m' & ? & ? & ?)] using set_ind_L.
    - exists m. set_solver.
    - destruct (lookup i m') as [ | ] eqn:EQN.
      + apply mk_is_Some, elem_of_dom in EQN. exists m'. set_solver.
      + destruct (exist_fresh (map_img (SA := D) m')) as (j & ?).
        exists (insert i j m'). repeat split.
        * transitivity m'; [ | apply insert_subseteq]; assumption.
        * set_solver.
        * apply partial_inj_map_insert; [ | assumption].
          intros ?. apply (not_elem_of_map_img_1 (SA := D)). assumption.
  Qed.

  Lemma extend_permutation {V} s (m : M V) p (G : is_equivalence_map p m) :
    exists p', subseteq p p' /\ subseteq s (dom p') /\ is_equivalence_map p' m.
  Proof.
    destruct G as (inj_p & dom_p).
    apply (extend_inj_map s) in inj_p. destruct inj_p as (p' & dom_p' & ? & ?).
    exists p'. split; [assumption | ]. split; [assumption | ]. split; [assumption | ].
    intros k get_m_k. eapply lookup_weaken_is_Some; eauto.
  Qed.

  Lemma apply_permutation_extend {V} (p q : M K) (m : M V)
    (dom_m_p : forall k, is_Some (lookup k m) -> is_Some (lookup k p))
    (subset_p_q : subseteq p q) :
    apply_permutation q m = apply_permutation p m.
  Proof.
    apply pkmap_fun_eq. intros k (x & get_x)%dom_m_p. rewrite get_x.
    eapply lookup_weaken; eassumption.
  Qed.

  Lemma equiv_map_insert_1 {V} m i j (v : V) :
    lookup i m = None -> lookup j m = None ->
    equiv_map (insert i v m) (insert j v m).
  Proof.
    intros m_i m_j. exists (insert i j (id_permutation m)).
    assert (partial_inj_map (insert i j (id_permutation m))).
    { apply partial_inj_map_insert.
      - intros k get_k.
        replace j with k in * by eauto using lookup_id_permutation_is_Some.
        rewrite <-not_elem_of_dom in m_j.
        apply mk_is_Some in get_k. rewrite <-elem_of_dom in get_k.
        unfold id_permutation in get_k. rewrite dom_imap_L with (X := dom m) in get_k.
        + auto.
        + intros ?. rewrite elem_of_dom. firstorder.
      - apply id_permutation_is_equivalence. }
    split; [split | ].
    - assumption.
    - intros ? [<- | (? & ?)]%lookup_insert_is_Some.
      + simpl_map. auto.
      + simpl_map. apply id_permutation_is_equivalence. auto.
    - rewrite apply_permutation_insert, apply_id_permutation; auto.
  Qed.

  Lemma equiv_map_insert_2 {V} m0 m1 i j (v : V) :
    lookup i m0 = None -> lookup j m1 = None ->
    equiv_map m0 m1 -> equiv_map (insert i v m0) (insert j v m1).
  Proof.
    intros m0_i m1_j equiv_m0_m1.
    (* Without loss of generality, there exists a permutation that sends [m0] to
       [m1] that contains [i] in its domain. *)
    assert (exists p, is_equivalence_map p m0 /\ m1 = apply_permutation p m0 /\
                      is_Some (lookup i p)) as (p & equiv_p & -> & (j' & ?)).
    { destruct equiv_m0_m1 as (p & equiv_p & ?). destruct (equiv_p) as (_ & dom_p).
      apply (extend_permutation (singleton i)) in equiv_p.
      destruct equiv_p as (q & dom_q & ? & equiv_q).
      exists q. split; [assumption | ]. split.
      - erewrite apply_permutation_extend; eassumption.
      - rewrite <-elem_of_dom. set_solver. }
    destruct (equiv_p) as (inj_p & dom_p).
    (* We prove that [insert i v m0] is equivalent to [insert j' v m1] *)
    transitivity (apply_permutation p (insert i v m0)).
    - exists p. split; [ | reflexivity]. split; [assumption | ].
      intros ? [<- | ]%lookup_insert_is_Some'; auto.
    (* Finally, we rename [j'] to [j]. *)
    - erewrite pkmap_insert by eassumption. apply equiv_map_insert_1; [ | exact m1_j].
      erewrite lookup_pkmap; eassumption.
  Qed.

  Lemma equiv_map_empty {V} (m : M V) (Hequiv : equiv_map empty m) : m = empty.
  Proof. destruct Hequiv as (p & _ & ->). apply pkmap_empty. Qed.

  Lemma equiv_map_singleton {V} i (v : V) m (Hequiv : equiv_map {[i := v]} m) :
    exists j, m = {[j := v]}.
  Proof.
    destruct Hequiv as (p & (? & dom_p) & ->).
    specialize (dom_p i). simpl_map. destruct dom_p as (j & ?); [auto | ].
    exists j. unfold singletonM, map_singleton.
    erewrite pkmap_insert by first [eassumption | apply lookup_empty].
    rewrite pkmap_empty. reflexivity.
  Qed.

  (* A permutation can be inverted. *)
  Definition invert_permutation : M K -> M K := map_fold (fun i j m => insert j i m) empty.

  Lemma invert_permutation_empty : invert_permutation empty = empty.
  Proof. apply map_fold_empty. Qed.

  Lemma invert_permutation_lookup_Some p i j :
    lookup i (invert_permutation p) = Some j -> is_Some (lookup j p).
  Proof.
    induction p as [ | k x p ? ? IHp] using map_first_key_ind.
    - unfold invert_permutation. rewrite map_fold_empty, lookup_empty. discriminate.
    - unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
      destruct (decide (x = i)) as [-> | ].
      + simpl_map. intros [=->]. simpl_map. auto.
      + simpl_map. destruct (decide (j = k)) as [-> | ]; simpl_map; auto.
  Qed.

  Lemma lookup_Some_invert_permutation p i j (inj_p : partial_inj_map p) :
    lookup i p = Some j -> lookup j (invert_permutation p) = Some i.
  Proof.
    intros G%insert_delete_id. unfold invert_permutation. rewrite <-G.
    rewrite map_fold_insert_L.
    - simpl_map. reflexivity.
    - rewrite G. intros ? ? ? ? ? diff. intros. apply insert_insert_ne. intros ->. apply diff.
      eapply inj_p; [auto | congruence].
    - simpl_map. reflexivity.
  Qed.

  Lemma partial_inj_map_delete m i j :
    lookup i m = None -> partial_inj_map (insert i j m) -> partial_inj_map m.
  Proof.
    intros ? Hinj k (? & ?) k' ?.
    assert (i <> k) by congruence. assert (i <> k') by congruence.
    eapply Hinj; simpl_map; [auto | congruence].
  Qed.


  Lemma invert_permutation_inj : forall m, partial_inj_map m -> partial_inj_map (invert_permutation m).
  Proof.
    induction m as [ | k x m k_fresh ? IHm] using map_first_key_ind.
    - rewrite invert_permutation_empty. auto.
    - intros Hinj. unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
      apply partial_inj_map_insert.
      + intros i G. apply invert_permutation_lookup_Some in G.
        rewrite k_fresh in G. eapply is_Some_None, G.
      + apply IHm. eapply partial_inj_map_delete; eassumption.
  Qed.

  Lemma dom_invert_permutation : forall m, partial_inj_map m -> dom (invert_permutation m) = map_img m.
  Proof.
    induction m as [ | k x m ? ? IHm] using map_first_key_ind.
    - rewrite invert_permutation_empty, dom_empty_L, map_img_empty_L. reflexivity.
    - intros inj_m. unfold invert_permutation. rewrite map_fold_insert_first_key by assumption.
      rewrite dom_insert_L. rewrite map_img_insert_notin_L by assumption. f_equal.
      + apply IHm. eapply partial_inj_map_delete; eassumption.
  Qed.

  Lemma invert_permutation_is_equivalence_map {V} perm (m : M V) :
    is_equivalence_map perm m ->
    is_equivalence_map (invert_permutation perm) (apply_permutation perm m).
  Proof.
    intros (inj_perm & dom_perm). split.
    - apply invert_permutation_inj. exact inj_perm.
    - intros k ?. rewrite <-elem_of_dom. rewrite dom_invert_permutation by assumption.
      rewrite elem_of_map_img. eapply lookup_pkmap_rev; eassumption.
  Qed.

  Lemma map_compose_notin {A B C} `{FinMap A MA} `{FinMap B MB} (m : MB C) (n : MA B) (c : C) (b : B) :
    (forall a, lookup a n <> Some b) -> map_compose (insert b c m) n = map_compose m n.
  Proof.
    intros G. apply omap_ext. intros ? ? get_b.
    apply lookup_insert_ne. intros <-. eapply G, get_b.
  Qed.

  Lemma compose_invert_permutation p :
    partial_inj_map p -> map_compose (invert_permutation p) p = id_permutation p.
  Proof.
    induction p as [ | k x p ? ? IHp] using map_first_key_ind.
    - rewrite map_compose_empty_r, id_permutation_empty. reflexivity.
    - intros p_inj.
      unfold invert_permutation, id_permutation.
      rewrite map_fold_insert_first_key by assumption.
      erewrite map_imap_insert_Some by reflexivity.
      erewrite map_compose_insert_Some by (simpl_map; reflexivity). f_equal.
      rewrite map_compose_notin.
      + apply IHp. apply (partial_inj_map_delete _ k) in p_inj; assumption.
      + intros i ?. replace i with k in *; [congruence | ].
        apply p_inj; simpl_map; [auto | ].
        destruct (decide (i = k)) as [<- | ]; simpl_map; reflexivity.
  Qed.

  Global Instance equiv_map_sym V : Symmetric (@equiv_map V).
  Proof.
    intros ? ? (p & G & ->). exists (invert_permutation p).
    pose proof (invert_permutation_is_equivalence_map _ _ G).
    split; [assumption | ]. rewrite <-apply_permutation_compose by assumption.
    rewrite compose_invert_permutation by apply G.
    symmetry. apply apply_id_permutation. apply G.
  Qed.
End PKMap.

Global Notation apply_permutation p := (pkmap (fun i => lookup i p)).

Lemma map_sum_permutation {A} weight (m : Pmap A) p (perm_p : is_equivalence_map p m) :
  map_sum weight (apply_permutation p m) = map_sum weight m.
Proof.
  induction m as [ | k x m ? _ IHm] using map_first_key_ind.
  - unfold apply_permutation. rewrite map_fold_empty. reflexivity.
  - destruct (perm_p) as (inj_p & dom_p).
    assert (is_Some (lookup k p)) as (k' & Hk'). { apply dom_p. simpl_map. auto. }
    erewrite pkmap_insert by eassumption.
    rewrite !map_sum_insert.
    + rewrite IHm; [reflexivity | ]. eapply is_equivalence_map_insert. eassumption.
    + assumption.
    + erewrite lookup_pkmap; eassumption.
Qed.

Lemma permutation_forall {A} (P : A -> Prop) p (m : Pmap A) :
  is_equivalence_map p m -> map_Forall (fun _ => P) m -> map_Forall (fun _ => P) (apply_permutation p m).
Proof.
  intros (inj_p & dom_p). intros H i a G.
  pose proof (mk_is_Some _ _ G) as K.
  apply lookup_pkmap_rev in K; [ | assumption]. destruct K.
  erewrite lookup_apply_permutation in G by eassumption.
  eapply H, G.
Qed.

(* TODO: when std++ 1.14 is released, delete this function. *)
Lemma kmap_compose {A B C V} `{FinMap A MA} `{FinMap B MB} `{FinMap C MC}
  (m : MA V) (f : A -> B) (g : B -> C) :
  Inj eq eq f -> Inj eq eq g -> kmap (M2 := MC) g (kmap (M2 := MB) f m) = kmap (compose g f) m.
Proof.
  intros. apply map_eq. intros c. destruct (lookup c (kmap (compose g f) m)) eqn:EQN.
  - rewrite lookup_kmap_Some in EQN by typeclasses eauto. rewrite lookup_kmap_Some by assumption.
    destruct EQN as (a & -> & ?). exists (f a). split; [reflexivity | ].
    rewrite lookup_kmap_Some by assumption. exists a. eauto.
  - rewrite lookup_kmap_None in EQN by typeclasses eauto. rewrite lookup_kmap_None by assumption.
    intros b ->. rewrite lookup_kmap_None by assumption. intros a ->. apply EQN. reflexivity.
Qed.

Lemma prove_rel A B (R : A -> B -> Prop) x y z : R x y -> y = z -> R x z.
Proof. congruence. Qed.

Lemma prove_rel_n A B (R : nat -> A -> B -> Prop) x y z m n : R m x y -> m = n -> y = z -> R n x z.
Proof. congruence. Qed.
