(** * Mechanized_LLBC.HLPL_state : definition of HLPL and HLPL+ states. *)
Require Import lang.
Require Import PathToSubtree.
From stdpp Require Import pmap gmap.

Variant Acc :=
  | Acc_var (x : var)
  | Acc_anon (a : anon)
.

Global Instance EqDecision_Acc : EqDecision Acc.
Proof. unfold EqDecision, Decision. repeat decide equality. Defined.

Instance Injection_Acc_var : Inj eq eq Acc_var.
Proof. intros ? ? [=]. assumption. Qed.
Instance Injection_Acc_anon : Inj eq eq Acc_anon.
Proof. intros ? ? [=]. assumption. Qed.

Program Global Instance Countable_Acc : Countable Acc := {
  encode acc := match acc with
                | Acc_var x => xO x
                | Acc_anon a => xI a
                end;
  decode p := match p with
              | xO x => Some (Acc_var x)
              | xI a => Some (Acc_anon a)
              | _ => None
              end;
}.
Next Obligation. repeat split; discriminate. Qed.
Next Obligation. intros [ | ]; reflexivity. Qed.

Section state.
  Context {V : Set}.
  Context {nodes : Set}.
  Context `{Value V nodes}.

  Record state : Set := {
    vars : Pmap V;
    anons : Pmap V;
  }.

  Definition get_map S : gmap Acc V := union (kmap Acc_var (vars S)) (kmap Acc_anon (anons S)).

  Lemma map_disjoint_vars_anons S :
    map_disjoint (M := gmap _) (kmap Acc_var (vars S)) (kmap Acc_anon (anons S)).
  Proof.
    apply map_disjoint_spec. setoid_rewrite lookup_kmap_Some; [ | typeclasses eauto..].
    intros acc ? ? (x & ? & _) (a & ? & _). congruence.
  Qed.

  Lemma get_at_var x S : lookup (Acc_var x) (get_map S) = lookup x (vars S).
  Proof.
    unfold get_map. rewrite lookup_union_l.
    - apply lookup_kmap. typeclasses eauto.
    - rewrite lookup_kmap_None by typeclasses eauto. intros ? [=].
  Qed.
  Lemma get_at_anon a S : lookup (Acc_anon a) (get_map S) = lookup a (anons S).
  Proof.
    unfold get_map. rewrite lookup_union_r.
    - apply lookup_kmap. typeclasses eauto.
    - rewrite lookup_kmap_None by typeclasses eauto. intros ? [=].
  Qed.

  Program Global Instance IsState : State state V Acc  := {
    extra := unit;
    get_map := get_map;
    get_extra _ := ();
    alter_at_accessor f acc S :=
    match acc with
    | Acc_var x => {|vars := alter f x (vars S); anons := anons S|}
    | Acc_anon a => {|vars := vars S; anons := alter f a (anons S)|}
    end;
    anon_accessor := Acc_anon;
    accessor_anon acc :=
      match acc with
      | Acc_anon a => Some a
      | _ => None
      end;
    add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
  }.
  Next Obligation.
    intros [vars anons] [vars' anons'] eq_maps _. f_equal.
    - apply map_eq. intros x. apply (f_equal (lookup (Acc_var x))) in eq_maps.
      rewrite !get_at_var in eq_maps. exact eq_maps.
    - apply map_eq. intros a. apply (f_equal (lookup (Acc_anon a))) in eq_maps.
      rewrite !get_at_anon in eq_maps. exact eq_maps.
  Qed.
  Next Obligation. reflexivity. Qed.
  Next Obligation.
    intros ? ? [x | a]; cbn.
    - apply map_eq. intros [y | ].
      + rewrite get_at_var. cbn. destruct (decide (x = y)) as [<- | ].
        * rewrite !lookup_alter_eq. rewrite get_at_var. reflexivity.
        * rewrite !lookup_alter_ne by congruence. rewrite get_at_var. reflexivity.
      + rewrite lookup_alter_ne by discriminate. rewrite !get_at_anon. reflexivity.
    - apply map_eq. intros [ | b].
      + rewrite lookup_alter_ne by discriminate. rewrite !get_at_var. reflexivity.
      + rewrite get_at_anon. cbn. destruct (decide (a = b)) as [<- | ].
        * rewrite !lookup_alter_eq. rewrite get_at_anon. reflexivity.
        * rewrite !lookup_alter_ne by congruence. rewrite get_at_anon. reflexivity.
  Qed.
  (* What are the two following obligations? *)
  Next Obligation. discriminate. Qed.
  Next Obligation. reflexivity. Qed.
  Next Obligation.
    intros a v S. cbn. apply map_eq. intros [ | b].
    - rewrite lookup_insert_ne by discriminate. rewrite !get_at_var. reflexivity.
    - rewrite get_at_anon. cbn. destruct (decide (a = b)) as [<- | ].
      + rewrite !lookup_insert_eq. reflexivity.
      + rewrite !lookup_insert_ne by congruence. symmetry. apply get_at_anon.
  Qed.
  Next Obligation. reflexivity. Qed.
End state.
