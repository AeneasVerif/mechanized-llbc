Require Import base.
Require Import lang.
Require Import List.
Import ListNotations.
Require Import PeanoNat Lia.
(* Notation conflict between stdpp's `+++` and our `+++`. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.

Inductive LLBC_plus_val :=
| LLBC_plus_bot
| LLBC_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| LLBC_plus_mut_loan (l : loan_id)
| LLBC_plus_mut_borrow (l : loan_id) (v : LLBC_plus_val)
(*
| LLBC_plus_shr_loan (l : loan_id) (v : LLBC_plus_val)
| LLBC_plus_shr_borrow (l : loan_id)
 *)
(* | LLBC_plus_pair (v0 : LLBC_plus_val) (v1 : LLBC_plus_val) *)
(* Note: symbolic values should be parameterized by a type, when we introduce other datatypes than
   integers. *)
| LLBC_plus_symbolic
.

Variant LLBC_plus_nodes :=
| LLBC_plus_botC
| LLBC_plus_intC (n : nat)
| LLBC_plus_mut_loanC (l : loan_id)
| LLBC_plus_mut_borrowC (l : loan_id)
| LLBC_plus_symbolicC
.

Instance EqDecision_LLBC_plus_nodes : EqDecision LLBC_plus_nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Qed.

Definition LLBC_plus_arity c := match c with
| LLBC_plus_botC => 0
| LLBC_plus_intC _ => 0
| LLBC_plus_mut_loanC _ => 0
| LLBC_plus_mut_borrowC _ => 1
| LLBC_plus_symbolicC => 0
end.

Definition LLBC_plus_get_node v := match v with
| LLBC_plus_bot => LLBC_plus_botC
| LLBC_plus_int n => LLBC_plus_intC n
| LLBC_plus_mut_loan l => LLBC_plus_mut_loanC l
| LLBC_plus_mut_borrow l _ => LLBC_plus_mut_borrowC l
| LLBC_plus_symbolic => LLBC_plus_symbolicC
end.

Definition LLBC_plus_children v := match v with
| LLBC_plus_bot => []
| LLBC_plus_int _ => []
| LLBC_plus_mut_loan _ => []
| LLBC_plus_mut_borrow _ v => [v]
| LLBC_plus_symbolic => []
end.

Definition LLBC_plus_fold c vs := match c, vs with
| LLBC_plus_intC n, [] => LLBC_plus_int n
| LLBC_plus_mut_loanC l, [] => LLBC_plus_mut_loan l
| LLBC_plus_mut_borrowC l, [v] => LLBC_plus_mut_borrow l v
| LLBC_plus_symbolicC, [] => LLBC_plus_symbolic
| _, _ => LLBC_plus_bot
end.

Fixpoint LLBC_plus_weight node_weight v :=
  match v with
  | LLBC_plus_mut_borrow l v => node_weight (LLBC_plus_mut_borrowC l) + LLBC_plus_weight node_weight v
  | v => node_weight (LLBC_plus_get_node v)
end.

Program Instance ValueLLBC_plus : Value LLBC_plus_val LLBC_plus_nodes := {
  arity := LLBC_plus_arity;
  get_node := LLBC_plus_get_node;
  children := LLBC_plus_children;
  fold_value := LLBC_plus_fold;
  vweight := LLBC_plus_weight;
  bot := LLBC_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_nodes eq_children; inversion eq_nodes; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; cbn; lia. Qed.

Record LLBC_plus_state := {
  vars : Pmap LLBC_plus_val;
  anons : Pmap LLBC_plus_val;
  regions : Pmap (Pmap LLBC_plus_val);
}.

Definition encode_var (x : var) :=
  encode (A := _ + positive * positive) (inl (encode (A := _ + anon) (inl x))).
Definition encode_anon (a : anon) :=
  encode (A := _ + positive * positive) (inl (encode (A := var + _) (inr a))).
Definition encode_region (x : positive * positive) := encode (A := var + anon + _) (inr x).

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

  Lemma lookup_None_flatten Ms i j : lookup i Ms = None -> lookup (i, j) (flatten Ms) = None.
  Proof.
    intros ?.
    induction Ms as [ | k x Ms ? _ IHm] using map_first_key_ind.
    - unfold flatten. rewrite map_fold_empty, lookup_empty. reflexivity.
    - assert (i <> k). { intros <-. simpl_map. congruence. }
      simpl_map.
      rewrite flatten_insert by assumption. apply lookup_union_None_2.
      + apply eq_None_ne_Some_2.
        intros ? (? & ? & _)%lookup_kmap_Some; [congruence | typeclasses eauto].
      + auto.
  Qed.

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
End Flatten.

(* TODO: move in base.v *)
Lemma alter_map_union {V} `{FinMap K M} (m0 m1 : M V) f k :
  alter f k (union m0 m1) = union (alter f k m0) (alter f k m1).
Proof.
  apply map_eq. intros i. destruct (decide (i = k)) as [-> | ].
  - simpl_map. rewrite !lookup_union. simpl_map.
Admitted.

Program Instance IsState : State LLBC_plus_state LLBC_plus_val := {
  extra := unit;
  get_map S := sum_maps (sum_maps (vars S) (anons S)) (flatten (regions S));
  get_extra _ := ();
  alter_at_accessor f a S :=
    match decode' (A := positive + positive * positive) a with
    | Some (inl a) =>
        match decode' (A := var + anon) a with
        | Some (inl x) => {| vars := alter f x (vars S); anons := anons S; regions := regions S|}
        | Some (inr a) => {| vars := vars S; anons := alter f a (anons S); regions := regions S|}
        | None => S
        end
    | Some (inr (i, j)) => {| vars := vars S; anons := anons S;
                              regions := alter (fun r => alter f j r) i (regions S)|}
    | None => S
    end;
  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := var + positive) x with
    | Some (inr a) => Some a
    | _ => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
}.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? y. cbn. destruct (decode' y) as [[z | (i & j)] | ] eqn:H.
  - rewrite decode'_is_Some in H.
    destruct (decode' z) as [[x | a] | ] eqn:G.
    + cbn. rewrite decode'_is_Some in G. rewrite <-H, <-G, <- !sum_maps_alter_inl.
      reflexivity.
    + cbn. rewrite decode'_is_Some in G.
      rewrite <-H, <-G, <-sum_maps_alter_inr, <-sum_maps_alter_inl. reflexivity.
    + symmetry. apply map_alter_not_in_domain. rewrite <-H, sum_maps_lookup_l.
      now apply sum_maps_lookup_None.
  - cbn. rewrite decode'_is_Some in H. rewrite <-H,  sum_maps_alter_inr, alter_flatten. reflexivity.
  - symmetry. apply map_alter_not_in_domain, sum_maps_lookup_None. assumption.
Qed.
