Require Import List.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.

Local Open Scope option_monad_scope.

(* Chemins, préfixes, chemins disjoints *)

(* Un vpath est une liste d'entiers naturels, caractérisant une sous-valeur dans une valeur (vue
   en tant qu'arbre). Il s'agit d'une liste d'entiers [i_0, i_1, ...], où i_0, i_1, ...
   correspondent aux indices des branches des arbres que l'on prend lorsqu'on descend dans l'arbre
   en partant de la racine. *)
Definition vpath := list nat.

(* Un `spath` est un chemin vers une valeur dans l'état. Il s'agit d'une paire (i, p) avec i
   un indice de de Bruijn, et p est un chemin vers cette sous-valeur dans la valeur stockée à
   l'indice i. TODO: incompréhensible. *)
Definition spath : Set := nat * vpath.

Definition app_spath_vpath (p : spath) (q : vpath) := (fst p, snd p ++ q).
Notation "p +++ q" := (app_spath_vpath p q) (right associativity, at level 60).

Lemma app_spath_vpath_nil_r p : p +++ nil = p.
Proof. apply injective_projections; cbn; reflexivity || apply app_nil_r. Qed.

Lemma app_spath_vpath_assoc p q r : p +++ q ++ r = (p +++ q) +++ r.
Proof. unfold app_spath_vpath. rewrite app_assoc. reflexivity. Qed.

Definition vprefix (p q : vpath) := exists r, p ++ r = q.

Definition vdisj (p q : vpath) :=
  exists (r p' q' : vpath) i j, i <> j /\ p = r ++ (i :: p') /\ q = r ++ (j :: q').

Global Instance vdisj_symmetric : Symmetric vdisj.
Proof. intros ? ? (v & p & q & i & j & ? & ? & ?). exists v, q, p, j, i. auto. Qed.

Variant vComparable (p q : vpath) : Prop :=
| vCompPrefixLeft (H : vprefix p q)
| vCompPrefixRight (H : vprefix q p)
| vCompDisj (H : vdisj p q).

Lemma comparable_cons p q i (H : vComparable p q) : vComparable (i :: p) (i :: q).
Proof.
  destruct H as [[r <-] | [r <-] | (r & ? & ? & ? & ? & ? & -> & ->)].
  - apply vCompPrefixLeft. exists r. cbn. reflexivity.
  - apply vCompPrefixRight. exists r. cbn. reflexivity.
  - apply vCompDisj. exists (i :: r). repeat eexists. assumption.
Qed.

Lemma comparable_vpaths p : forall q, vComparable p q.
Proof.
  induction p as [ | i p' IH]; intro q.
  - apply vCompPrefixLeft. eexists. reflexivity.
  - destruct q as [ | j q'].
    + apply vCompPrefixRight. eexists. reflexivity.
    + destruct (Nat.eq_dec i j) as [<- | diff].
      * apply comparable_cons, IH.
      * apply vCompDisj. exists nil. repeat eexists. assumption.
Qed.

(* Prefixness and disjointness for spaths: *)
Definition prefix p q := exists r, p +++ r = q.

Definition strict_prefix p q := exists i r, p +++ (i :: r) = q.

Lemma strict_prefix_is_prefix p q : strict_prefix p q -> prefix p q.
Proof. intros (? & ? & ?). eexists. eassumption. Qed.

Definition disj (p q : spath) :=
(fst p <> fst q) \/ (fst p = fst q /\ vdisj (snd p) (snd q)).

Global Instance symmetric_disj : Symmetric disj.
Proof.
intros p q [? | [? ?]].
+ left. auto.
+ right. split; symmetry; assumption.
Qed.

Variant Comparable (p q : spath) : Prop :=
| CompPrefixLeft (H : prefix p q)
| CompPrefixRight (H : prefix q p)
| CompDisj (H : disj p q).

Lemma comparable_spaths p q : Comparable p q.
Proof.
rewrite (surjective_pairing p), (surjective_pairing q).
destruct (Nat.eq_dec (fst p) (fst q)) as [<- | ].
- destruct (comparable_vpaths (snd p) (snd q)).
  + apply CompPrefixLeft. destruct H as [v ?]. exists v.
    unfold app_spath_vpath. cbn. rewrite H. reflexivity.
  + apply CompPrefixRight. destruct H as [v ?]. exists v.
    unfold app_spath_vpath. cbn. rewrite H. reflexivity.
  + apply CompDisj. right. auto.
- apply CompDisj. unfold disj. auto.
Qed.

Variant StrictComparable (p q : spath) : Prop :=
| StrictCompPrefixLeft (H : strict_prefix p q)
| StrictCompPrefixRight (H : strict_prefix q p)
| StrictCompEq (H : p = q)
| StrictCompDisj (H : disj p q).

Lemma strict_comparable_spaths p q : StrictComparable p q.
Proof.
Admitted.

Lemma app_same_nil {A : Type} (x y : list A) (H :x ++ y = x) : y = nil.
Proof. eapply app_inv_head. rewrite H, app_nil_r. reflexivity. Qed.

Lemma prefix_antisym p q (H : prefix p q) (G : prefix q p) : p = q.
Proof.
  destruct H as [r <-]. destruct G as [r' G]. unfold app_spath_vpath in G.
  apply (f_equal snd) in G; cbn in G. rewrite <-app_assoc in G.
  apply app_same_nil, app_eq_nil in G. destruct G as [-> _].
  rewrite app_spath_vpath_nil_r. reflexivity.
Qed.

Lemma strict_prefix_irrefl p : ~strict_prefix p p.
Proof.
  intros (? & ? & ?). apply (f_equal snd) in H. unfold app_spath_vpath in H.
  apply app_same_nil in H. inversion H.
Qed.

Corollary strict_prefix_antisym p q (H : strict_prefix p q) (G : strict_prefix q p) : False.
Proof.
  destruct (prefix_antisym p q).
  - apply strict_prefix_is_prefix. assumption.
  - apply strict_prefix_is_prefix. assumption.
  - eapply strict_prefix_irrefl. exact H.
Qed.

Lemma disj_l_prefix p q r : disj p q -> prefix p r -> disj r q.
Proof.
  intros [ | (? & ? & ? & ? & ? & ? & ? & Hsnd_p & ?) ] [? <-].
  - left. assumption.
  - right.  split; try assumption. simpl. repeat eexists.
    + eassumption.
    + rewrite Hsnd_p. rewrite <-app_assoc. reflexivity.
    + eassumption.
Qed.

(* We introduce this class in order to define overloadable notations for extraction and substitution.
   It is parameterized by three types:
   - C: the "carrier". Either state or value. *)
Class ExtractSubst {C P V : Type} := {
  extract : C -> P -> V;
  substitute : C -> P -> V -> C;
  (* valid : S -> P -> Prop; *)
}.

Declare Scope ExtractSubst_scope.
Notation "t {{ p }}" := (extract t p) (left associativity, at level 50) : ExtractSubst_scope.
Notation "t {{ p <- v }}" := (substitute t p v) (left associativity, at level 50) : ExtractSubst_scope.

Open Scope ExtractSubst_scope.

Section ExtractSubst.
  Context {Z : Type}.
  Context {U : Type}.
  Context {B : Type}.

  Inductive value :=
  | vZero : Z -> value
  | vUnit : U -> value -> value
  | vBin : B -> value -> value -> value.

  (* Un chemin p est valide s'il est bien possible de descendre dans l'arbre T en suivant ce chemin.
     Les opérations que l'on défini par la suite : T ; p et T[p <- t], n'ont de sens que si p est
     valide pour T. La propriété valid_vpath défini le domaine des fonctions de sous-terme et de
     substitution. *)
  Inductive valid_vpath : value -> vpath -> Prop :=
  | Valid_nil v : valid_vpath v nil
  | Valid_unit u v0 p : valid_vpath v0 p -> valid_vpath (vUnit u v0) (0 :: p)
  | Valid_bin_0 b v0 v1 p : valid_vpath v0 p -> valid_vpath (vBin b v0 v1) (0 :: p)
  | Valid_bin_1 b v0 v1 p : valid_vpath v1 p -> valid_vpath (vBin b v0 v1) (1 :: p).

  (* Nous allons maintenant définir deux instances de référence pour les classes Extract et
     Substitute. Ces implémentations requièrent l'indication d'une valeur spéciale ("err") qui est
     utilisée pour définir les opérations lorsque l'on évalue un chemin invalide. *)
  Definition extract_once (v : value) (i : nat) : value :=
    match v, i with
    | vUnit u v0, 0 => v0
    | vBin b v0 v1, 0 => v0
    | vBin b v0 v1, 1 => v1
    | _, _ => v
    end.

  Definition extract_value v p := fold_left extract_once p v.

  Fixpoint substitute_value (v : value) (p : vpath) (t : value) : value :=
  match v, p with
  | _, nil => t
  | vUnit u v0, 0 :: p => vUnit u (substitute_value v0 p t)
  | vBin b v0 v1, 0 :: p => vBin b (substitute_value v0 p t) v1
  | vBin b v0 v1, 1 :: p => vBin b v0 (substitute_value v1 p t)
  | _, _ => v
  end.

  Global Instance ExtractValue : @ExtractSubst value vpath value := {
    extract := extract_value;
    substitute := substitute_value;
  }.

  Lemma substitute_nil (v w : value) : substitute v nil w = w.
  Proof. destruct v; reflexivity. Qed.

  (* Relations entre la validité et l'extraction/substitution : *)
  Lemma valid_vpath_app v (p q : vpath) :
    valid_vpath v (p ++ q) <-> valid_vpath v p /\ valid_vpath (v{{p}}) q.
  Proof.
    split.
    - intro H. split; revert H; revert v; induction p as [ | ? ? IHp].
      + constructor.
      + intros ? H. inversion H; constructor; auto.
      + auto.
      + intros ? H. inversion H; apply IHp; assumption.
    - intros [H G]. revert G. induction H;  try constructor; auto.
  Qed.

  Lemma subst_valid v p w (H : valid_vpath v p) : valid_vpath (v{{p <- w}}) p.
  Proof. induction H; constructor; auto. Qed.

  (* Relations entre substitution et extraction *)
  Lemma extract_app v (p q : vpath) : v{{p ++ q}} = v{{p}}{{q}}.
  Proof. simpl. unfold extract_value. rewrite fold_left_app. reflexivity. Qed.

  Lemma subst_extract_vprefix (v w : value) (p q : vpath) (H : valid_vpath v p) :
    extract (substitute v (p ++ q) w) p = substitute (extract v p) q w.
  Proof. induction H; auto. Qed.

  Corollary subst_extract (v w : value) (p : vpath) (H : valid_vpath v p) :
    extract (substitute v p w) p = w.
  Proof.
    rewrite<- (app_nil_r p) at 1.
    rewrite subst_extract_vprefix; apply substitute_nil || assumption.
  Qed.

  Corollary subst_extract_suffix (v w : value) (p q : vpath) (H : valid_vpath v p) :
    extract (substitute v p w) (p ++ q) = extract w q.
  Proof. rewrite extract_app, subst_extract; try apply subst_valid; auto. Qed.

  Lemma subst_extract_disj_aux v i j p q w (diff : i <> j)
    (H : valid_vpath v (j :: q)) (G : valid_vpath v (i :: p)) :
    v {{i :: p <- w}} {{j :: q}} = v {{j :: q}}.
  Proof. inversion H; subst v; inversion G; subst i j; easy. Qed.

  Lemma subst_extract_vdisj (v w : value) (p q : vpath)
    (Hvdisj : vdisj p q) (Hval_p : valid_vpath v p) (Hval_q : valid_vpath v q) :
    extract (substitute v p w) q = extract v q.
  Proof.
    destruct Hvdisj as (r & p' & q' & i & j & diff & -> & ->).
    (* On montre qu'en toute généralité, on peut ne considérer que le cas r = nil, en prenant
       v' = extract v r. *)
    rewrite extract_app by (eapply valid_vpath_app; apply subst_valid; assumption).
    rewrite extract_app by (eapply valid_vpath_app; eassumption).
    rewrite valid_vpath_app in Hval_p. destruct Hval_p as [_ Hval_p'].
    rewrite valid_vpath_app in Hval_q. destruct Hval_q as [? Hval_q'].
    rewrite subst_extract_vprefix by assumption.
    apply subst_extract_disj_aux; assumption.
  Qed.

  (* Résultats sur la composition de deux substitutions v{{p <- x}}{{q <- y}},
     selon si p est un préfix de q, q est un préfixe de p, ou si p et q sont vdisjoints. *)
  (* Remark: we could prove all the lemmas about the commutation of substitutions *without*
     the validity hypethesis. Indeed, if p is not a valid path, then v{{p <- x}} = v. This
     could ease the use of these lemmas.
   *)
  Lemma subst_same v p x y (H : valid_vpath v p) :
    substitute (substitute v p x) p y = substitute v p y.
  Proof. induction H; cbn; try rewrite !substitute_nil; f_equal; auto. Qed.

  Lemma subst_app_split v p q w (H : valid_vpath v p) :
    substitute v (p ++ q) w = substitute v p (substitute (extract v p) q w).
  Proof. induction H; cbn; try rewrite substitute_nil; f_equal; assumption. Qed.

  Lemma subst_disj_valid v p q w (Hdisj : vdisj p q)
    (valid_p : valid_vpath v p) (valid_q : valid_vpath v q) : valid_vpath (substitute v p w) q.
  Proof.
    destruct Hdisj as (r & p' & q' & i & j & ? & -> & ->). apply valid_vpath_app.
    apply valid_vpath_app in valid_p. destruct valid_p as [? valid_ip'].
    apply valid_vpath_app in valid_q. destruct valid_q as [_ valid_jq']. split.
    - rewrite subst_app_split by assumption. apply subst_valid. assumption.
    - rewrite subst_extract_vprefix by assumption.
      revert valid_ip' valid_jq'. generalize (extract v r). intros v' valid_ip' valid_iq'.
      inversion valid_ip'; subst v'; inversion valid_iq'; subst i j; easy || constructor; assumption.
  Qed.

  Lemma subst_twice_app_split v p q r x y
    (H : valid_vpath v p) :
    substitute (substitute v (p ++ q) x) (p ++ r) y =
    substitute v p (substitute (substitute (extract v p) q x) r y).
  Proof.
    rewrite (subst_app_split v p q) by assumption.
    rewrite subst_app_split by (apply subst_valid; assumption).
    rewrite subst_same, subst_extract by assumption. reflexivity.
  Qed.

  Lemma subst_vprefix v p q x y (H : valid_vpath v p) (pref : vprefix q p) :
    substitute (substitute v p x) q y = substitute v q y.
  Proof.
    destruct pref as [? <-]. rewrite valid_vpath_app in H. destruct H.
    rewrite subst_app_split, subst_same by assumption. reflexivity.
  Qed.

  Corollary subst_suffix v p q x y (H : valid_vpath v p) :
    substitute (substitute v p x) (p ++ q) y = substitute v p (substitute x q y).
  Proof.
    rewrite<- (app_nil_r p) at 1. rewrite subst_twice_app_split by assumption.
    rewrite substitute_nil. reflexivity.
  Qed.

  Lemma subst_vdisj_commute v p q x y
    (Hvdisj : vdisj p q) (Hval_p : valid_vpath v p) (Hval_q : valid_vpath v q) :
    substitute (substitute v p x) q y = substitute (substitute v q y) p x.
  Proof.
    destruct Hvdisj as (r & p' & q' & i & j & diff & -> & ->).
    rewrite valid_vpath_app in Hval_p. destruct Hval_p as [? Hval_p'].
    rewrite valid_vpath_app in Hval_q. destruct Hval_q as [_ Hval_q'].
    rewrite !subst_twice_app_split by assumption.
    f_equal.
    revert Hval_p' Hval_q'. generalize (extract v r). intros w Hval_q' Hval_p'.
    inversion Hval_p'; subst w; inversion Hval_q'; subst i j; easy.
  Qed.

  Definition maximal_valid_vpath v p : Prop := forall q, vprefix p q -> valid_vpath v q -> p = q.

  Lemma vpath_zero_maximal v p z : extract v p = vZero z -> maximal_valid_vpath v p.
  Proof.
    intros H q [r <-] G. rewrite valid_vpath_app in G. destruct G as [_ G]. rewrite H in G.
    inversion G. rewrite app_nil_r. reflexivity.
  Qed.

  Context {binder : Type}.
  Context `{eq_dec_binder : EqDec binder}.

  Definition state := list (binder * value).

  Notation get_val S i := (SOME c <- nth_error S i IN Some (snd c)).

  Definition valid_spath (S : state) (p : spath) :=
    exists v, get_val S (fst p) = Some v /\ valid_vpath v (snd p).

  Fixpoint find_index (S : state) (b:binder) : option nat := match S with
  | nil => None
  | (b', _) :: S' => if eq_dec b b' then Some 0 else SOME i <- find_index S' b IN Some (1 + i)
  end.

  Lemma find_index_some S b :
    forall i, find_index S b = Some i -> exists v, nth_error S i = Some (b, v).
  Proof.
    induction S as [ | bv S' IH]; simplify_option. congruence.
  Qed.

  (* Maybe it's more useful in this form? *)
  Corollary find_index_valid_spath S b i (H : find_index S b = Some i) : valid_spath S (i, nil).
  Proof.
    apply find_index_some in H. destruct H as [v Hv]. exists v.
    cbn. rewrite Hv; split; reflexivity || constructor.
  Qed.

  Context `(ValueInhabited : Inhabited value).

  Definition substitute_binding p w (bv : binder * value) :=
    (fst bv, substitute (snd bv) p w).

  Definition extract_state (S : state) (p : spath) := match nth_error S (fst p) with
  | Some bv => extract (snd bv) (snd p)
  | None => default
  end.

  Definition substitute_state S p v := (map_nth S (fst p) (substitute_binding (snd p) v)).

  Global Instance ExtractSubst_state : ExtractSubst := {
    extract := extract_state;
    substitute := substitute_state;
  }.

  Lemma get_val_extract (S : state) (p : spath) (v : value) (H : get_val S (fst p) = Some v) :
    S{{p}} = v{{snd p}}.
  Proof. cbn. unfold extract_state. simplify_option. Qed.

  Lemma substitute_state_valid S p v (H : valid_spath S p) :
    valid_spath (S{{p <- v}}) p.
  Proof.
    destruct H as (w & H & ?). exists (substitute w (snd p) v). split.
    - simpl. unfold substitute_state. rewrite nth_error_map_nth_eq. simplify_option.
    - apply subst_valid. assumption.
  Qed.

  Lemma substitute_state_disj_valid S p q v (Hdisj : disj p q)
    (valid_p : valid_spath S p) (valid_q : valid_spath S q) :
    valid_spath (S{{p <- v}}) q.
  Proof.
    destruct valid_q as (w & get_S_q & ?).
    destruct Hdisj as [? | [eq_fst disj_snd]].
    - exists w. split; try assumption. rewrite<- get_S_q.
      simpl. unfold substitute_state. rewrite nth_error_map_nth_neq by assumption. reflexivity.
    - exists (substitute w (snd p) v). destruct valid_p as (w' & get_S_q' & ?).
      unfold substitute; simpl. unfold substitute_state. rewrite eq_fst in *.
      try_simplify_someHyps.
      split.
      + rewrite nth_error_map_nth_eq; simplify_option.
      + apply subst_disj_valid; assumption.
  Qed.

  Local Hint Resolve subst_extract: core.

  Lemma extract_substitute_state_same S p v (H : valid_spath S p) :
    S{{p <- v}}{{p}} = v.
  Proof.
    simpl. unfold extract_state, substitute_state. rewrite nth_error_map_nth_eq.
    destruct H as (? & H' & ?). simplify_option.
  Qed.

  Opaque ExtractValue.
  Local Hint Resolve extract_app : core.
  Lemma extract_state_app S p q (H : valid_spath S p) :
    S{{p +++ q}} = S{{p}}{{q}}.
  Proof.
    simpl. unfold extract_state, app_spath_vpath. destruct H as (? & ? & ?). simplify_option.
  Qed.

  Lemma valid_spath_app S p q :
    valid_spath S (p +++ q) <-> valid_spath S p /\ valid_vpath (S{{p}}) q.
  Proof.
    split.
    - intros (v & Hget_v & Hvalid_v). unfold app_spath_vpath in *. cbn in *.
      apply valid_vpath_app in Hvalid_v. destruct Hvalid_v.
      split. exists v. auto. erewrite get_val_extract; eassumption.
    - intros [(v & ? & ?) ?].
      exists v. unfold app_spath_vpath. split; try easy. apply valid_vpath_app.
      rewrite <- get_val_extract with (S := S); auto.
  Qed.

  Lemma subst_disj_commute S p q v w (Hdisj : disj p q)
    (valid_p : valid_spath S p) (valid_q : valid_spath S q) :
    S{{p <- v}}{{q <- w}} = S{{q <- w}}{{p <- v}}.
  Proof.
    destruct valid_p as (? & ? & ?). destruct valid_q as (? & ? & ?).
    simpl. unfold substitute_state.
    destruct Hdisj as [ | [eq_i ?]].
    - apply map_nth_neq_commute. assumption.
    - rewrite eq_i in *.
      apply map_nth_eq_commute. intros [? ?] ?. unfold substitute_binding. simpl. f_equal.
      apply subst_vdisj_commute; simplify_option.
  Qed.

  Lemma subst_extract_disj S p q v (H : disj p q)
    (valid_p : valid_spath S p) (valid_q : valid_spath S q) :
    S{{p <- v}}{{q}} = S{{q}}.
  Proof.
    destruct valid_p as (? & ? & ?). destruct valid_q as (? & ? & ?). simpl.
     unfold extract_state, substitute_state. destruct H as [ | [e ?]].
    - rewrite nth_error_map_nth_neq by assumption. reflexivity.
    - rewrite e in *. rewrite nth_error_map_nth_eq. simplify_option.
      rewrite subst_extract_vdisj; auto.
  Qed.

  Lemma subst_extract_prefix S p q v (H : valid_spath S p) :
    S{{p +++ q <- v}}{{p}} = S{{p}}{{q <- v}}.
  Admitted.

  Variant same_constructor : value -> value -> Prop :=
  | SameZero z : same_constructor (vZero z) (vZero z)
  | SameUnit u v w : same_constructor (vUnit u v) (vUnit u w)
  | SameBin b v0 v1 w0 w1 : same_constructor (vBin b v0 v1) (vBin b w0 w1).

  Global Instance refl_same_constructor : Reflexive same_constructor.
  Proof. intros [ | | ]; constructor. Qed.

  Global Instance sym_same_constructor : Symmetric same_constructor.
  Proof. intros ? ? [ | | ]; constructor. Qed.

  Global Instance trans_same_constructor : Transitive same_constructor.
  Proof. intros ? ? ? [ | | ] H; inversion H; constructor. Qed.

  Lemma same_constructor_subst (v w : value) i p : same_constructor v (v{{i :: p <- w}}).
  Proof. destruct v; repeat (constructor || destruct i as [ | i]). Qed.

  Lemma same_constructor_subst_disj S sp sq v :
    valid_spath S sp -> valid_spath S sq -> disj sq sp ->
    same_constructor (S{{sp}}) (S{{sq <- v}}{{sp}}).
  Proof. intros. rewrite subst_extract_disj; reflexivity || assumption. Qed.

  Lemma same_constructor_subst_strict_prefix S sp sq v :
    valid_spath S sp -> strict_prefix sp sq ->
    same_constructor (S{{sp}}) (S{{sq <- v}}{{sp}}).
  Proof.
    intros ? (? & ? & <-). rewrite subst_extract_prefix by assumption.
    apply same_constructor_subst.
  Qed.
End ExtractSubst.

Arguments value : clear implicits.
Arguments state : clear implicits.