Require Import List.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Local Open Scope option_monad_scope.

Create HintDb spath.

(* Paths, prefixes and disjointness *)

(* A vpath ("value path") is the data structure used to uniquely represent nodes in a tree. The
 * integers in the list are the indices of the subvalues we take, going down from the root to the
 * node in the tree. It is called "vpath" because it will mostly be used by values in
 * intermediate languages between LLBC# and HLPL.
 * The vpaths are used to:
 * - Get the subvalue at a node.
 * - Set a subvalue at a node.
 * TODO: motivate the comparison between vpaths (prefix, equal, disjoint).
 *)
Definition vpath := list nat.

(* A spath ("state path") is the data structure used to uniquely represent nodes in a memory state,
 * represented as a list of pairs (b, v) where b is a binder and v a value. A spath is a pair
 * (i, p) where i is the index of a pair (b, v) in the state, and p is a vpath in the value v. *)
Definition spath : Set := nat * vpath.

(* The concatenation of a spath and a vpath. *)
Definition app_spath_vpath (p : spath) (q : vpath) := (fst p, snd p ++ q).
(* TODO: place the notation in a scope? *)
Notation "p +++ q" := (app_spath_vpath p q) (right associativity, at level 60).

Lemma app_spath_vpath_nil_r p : p +++ nil = p.
Proof. apply injective_projections; reflexivity || apply app_nil_r. Qed.

Lemma app_spath_vpath_assoc p q r : p +++ q ++ r = (p +++ q) +++ r.
Proof. unfold app_spath_vpath. rewrite app_assoc. reflexivity. Qed.

(* The large and strict prefix relations between two paths. *)
Definition vprefix (p q : vpath) := exists r, p ++ r = q.
Definition vstrict_prefix (p q : vpath) := exists i r, p ++ i :: r = q.

(* Two paths p and q are disjoint if neither is the prefix of the other. The most useful
 * characterization, that we are defining here, is that p and q are of the form
 * r ++ [i] ++ p' and r ++ [i] ++ q', where r is the longest common prefix, and where i <> j are
 * the first indices where p and q differ.
 *)
Definition vdisj (p q : vpath) :=
  exists (r p' q' : vpath) i j, i <> j /\ p = r ++ (i :: p') /\ q = r ++ (j :: q').

Global Instance vdisj_symmetric : Symmetric vdisj.
Proof. intros ? ? (v & p & q & i & j & ? & ? & ?). exists v, q, p, j, i. auto. Qed.

(* Showing that every two paths are comparable.
 * TODO: an alternative is to define a function comp p q that returns a result (Eq, StrictLeft,
 * StrictRight, Disj), and show that the result of the function is equivalent to on of the
 * relations we defined earlier.
 *)
Variant vComparable (p q : vpath) : Prop :=
| vCompEq (H : p = q)
| vCompStrictPrefixLeft (H : vstrict_prefix p q)
| vCompStrictPrefixRight (H : vstrict_prefix q p)
| vCompDisj (H : vdisj p q).

Lemma comparable_cons p q i (H : vComparable p q) : vComparable (i :: p) (i :: q).
Proof.
  destruct H as [ <- | (j & r & <-) | (j & r & <-) | (r & ? & ? & ? & ? & ? & -> & ->)].
  - apply vCompEq. reflexivity.
  - apply vCompStrictPrefixLeft. exists j, r. reflexivity.
  - apply vCompStrictPrefixRight. exists j, r. reflexivity.
  - apply vCompDisj. exists (i :: r). repeat eexists. assumption.
Qed.

Lemma comparable_vpaths p : forall q, vComparable p q.
Proof.
  induction p as [ | i p' IH]; intro q; destruct q as [ | j q'].
  - apply vCompEq. reflexivity.
  - apply vCompStrictPrefixLeft. exists j, q'. reflexivity.
  - apply vCompStrictPrefixRight. exists i, p'. reflexivity.
  - destruct (Nat.eq_dec i j) as [<- | diff].
    + apply comparable_cons, IH.
    + apply vCompDisj. exists nil. repeat eexists. assumption.
Qed.


(* Another try for comparison. *)
(* Let r be the longest common prefix of p and q. Let p' and q' be the vpaths such that p = r ++ p'
 * and q = r ++ q'. p' and q' are called the "common suffixes".
 * TODO: search if there is already a terminology in the literature. *)
Fixpoint longest_common_suffixes (p q : vpath) :=
  match p, q with
  | nil, _ => (p, q)
  | _, nil => (p, q)
  | i :: p', j :: q' => if Nat.eq_dec i j then longest_common_suffixes p' q' else (p, q)
  end.

Lemma longest_common_suffixes_prefix p p' q' :
  forall q, longest_common_suffixes p q = (p', q') -> exists r, p = r ++ p' /\ q = r ++ q'.
Proof.
  induction p as [ | i p].
  - intros q H. exists nil. inversion H. auto.
  - intros [ | j q] H.
    + exists nil. inversion H. auto.
    + cbn in H. destruct (Nat.eq_dec i j) as [<- | ].
      * specialize (IHp _ H). destruct IHp as (r & -> & ->). exists (i :: r). auto.
      * exists nil. inversion H. auto.
Qed.

Lemma longest_common_suffixes_head_diff p q i j p' q' :
  longest_common_suffixes p q = (i :: p', j :: q') -> i <> j.
Proof.
  revert q. induction p as [ | p0 p IH]; intros q H; try discriminate H.
  destruct q as [ | q0]; try discriminate H.
  cbn in H. destruct (Nat.eq_dec p0 q0) as [-> | ].
  - eapply IH. exact H.
  - inversion H. subst. assumption.
Qed.

Lemma longest_common_suffixes_strip p q r :
  longest_common_suffixes (p ++ q) (p ++ r) = longest_common_suffixes q r.
Proof.
  induction p as [ | i ]; try reflexivity. cbn. destruct (Nat.eq_dec i i); easy.
Qed.

Variant CompResult :=  CompEqR | CompStrictPrefixLeftR | CompStrictPrefixRightR | CompDisjR.

Definition decide_vcomparison p q :=
  match longest_common_suffixes p q with
  | (nil, nil) => CompEqR
  | (nil, _ :: _) => CompStrictPrefixLeftR
  | (_ :: _, nil) => CompStrictPrefixRightR
  | (_ :: _, _ :: _) => CompDisjR
  end.

(* Prefixness and disjointness for spaths: *)
Definition prefix p q := exists r, p +++ r = q.

Definition strict_prefix p q := exists i r, p +++ (i :: r) = q.

Lemma vstrict_prefix_is_vprefix p q : vstrict_prefix p q -> vprefix p q.
Proof. intros (? & ? & ?). eexists. eassumption. Qed.

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
| CompEq (H : p = q)
| CompStrictPrefixLeft (H : strict_prefix p q)
| CompStrictPrefixRight (H : strict_prefix q p)
| CompDisj (H : disj p q).

Definition decide_comparison (p q : spath) :=
  if (Nat.eq_dec (fst p) (fst q))
  then match longest_common_suffixes (snd p) (snd q) with
    | (nil, nil) => CompEqR
    | (nil, _ :: _) => CompStrictPrefixLeftR
    | (_ :: _, nil) => CompStrictPrefixRightR
    | (_ :: _, _ :: _) => CompDisjR
  end
  else CompDisjR.

Lemma decide_comparison_eq p q : decide_comparison p q = CompEqR <-> p = q.
Proof.
  unfold decide_comparison. split.
  - intro H. rewrite (surjective_pairing p), (surjective_pairing q).
    destruct (Nat.eq_dec (fst p) (fst q)) as [<- | ]; try discriminate H.
    destruct (longest_common_suffixes (snd p) (snd q)) as (p' & q') eqn:G.
    apply longest_common_suffixes_prefix in G. destruct G as (r & -> & ->).
    destruct p'; destruct q'; easy.
  - intros <-. destruct (Nat.eq_dec (fst p) (fst p)); try easy.
    rewrite<- (app_nil_r (snd p)). rewrite longest_common_suffixes_strip. reflexivity.
Qed.

Lemma decide_strict_prefix_left p q :
  decide_comparison p q = CompStrictPrefixLeftR <-> strict_prefix p q.
Proof.
  unfold decide_comparison. split.
  - intro H. rewrite (surjective_pairing p), (surjective_pairing q).
    destruct (Nat.eq_dec (fst p) (fst q)) as [<-| ]; try discriminate H.
    destruct (longest_common_suffixes (snd p) (snd q)) as (p' & q') eqn:G.
    apply longest_common_suffixes_prefix in G. destruct G as (r & -> & ->).
    destruct p'; destruct q' as [ | i q']; try discriminate H.
    exists i, q'. unfold app_spath_vpath. rewrite app_nil_r. reflexivity.
  - intros (i & r & <-). destruct (Nat.eq_dec (fst p) _); try easy.
    rewrite<- (app_nil_r (snd p)). cbn. rewrite longest_common_suffixes_strip.
    reflexivity.
Qed.


Lemma comparable_spaths p q : Comparable p q.
Proof.
rewrite (surjective_pairing p), (surjective_pairing q).
destruct (Nat.eq_dec (fst p) (fst q)) as [<- | ].
- destruct (comparable_vpaths (snd p) (snd q)) as [ <- | (i & r & <-) | (i & r & <-) | ].
  + apply CompEq. reflexivity.
  + apply CompStrictPrefixLeft. exists i, r. unfold app_spath_vpath. cbn. reflexivity.
  + apply CompStrictPrefixRight. exists i, r. unfold app_spath_vpath. cbn. reflexivity.
  + apply CompDisj. right. auto.
- apply CompDisj. left. cbn. assumption.
Qed.

Lemma app_same_nil {A : Type} (x y : list A) (H : x ++ y = x) : y = nil.
Proof. eapply app_inv_head. rewrite H, app_nil_r. reflexivity. Qed.

Lemma prefix_antisym p q (H : prefix p q) (G : prefix q p) : p = q.
Proof.
  destruct H as [r <-]. destruct G as [r' G]. unfold app_spath_vpath in G.
  apply (f_equal snd) in G; cbn in G. rewrite <-app_assoc in G.
  apply app_same_nil, app_eq_nil in G. destruct G as [-> _].
  rewrite app_spath_vpath_nil_r. reflexivity.
Qed.

Lemma vstrict_prefix_irrefl p : ~vstrict_prefix p p.
Proof. intros (? & ? & ?).  apply app_same_nil in H. discriminate. Qed.

Lemma vdisj_irrefl p : ~vdisj p p.
Proof.
  intros (? & ? & ? & ? & ? & ? & H & G). rewrite G in H. apply app_inv_head in H.
  congruence.
Qed.

Lemma strict_prefix_irrefl p : ~strict_prefix p p.
Proof.
  intros (? & ? & ?). apply (f_equal snd) in H. unfold app_spath_vpath in H.
  apply app_same_nil in H. discriminate.
Qed.

Corollary not_prefix_left_strict_prefix_right p q : strict_prefix q p -> ~ prefix p q.
Proof.
  intros ? ?. destruct (prefix_antisym p q).
  - assumption.
  - apply strict_prefix_is_prefix. assumption.
  - apply (strict_prefix_irrefl p). assumption.
Qed.

Lemma not_vprefix_left_vstrict_prefix_right p q : vstrict_prefix q p -> ~vprefix p q.
Proof.
  intros (? & ? & H) (q' & G). rewrite <-(app_nil_r p), <-G, <-app_assoc in H.
  apply app_inv_head in H. destruct q'; discriminate.
Qed.

Lemma not_prefix_implies_not_strict_prefix p q : ~prefix p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. auto. Qed.

Local Instance : Reflexive vprefix.
Proof. intro p. exists nil. apply app_nil_r. Qed.

Global Instance vprefix_trans : Transitive vprefix.
Proof. intros x ? ? (? & <-) (? & <-). rewrite<- app_assoc. eexists. reflexivity. Qed.

Global Instance : Reflexive prefix.
Proof. intro p. exists nil. apply app_spath_vpath_nil_r. Qed.

(* TODO: do I need this lemma? *)
Corollary strict_prefix_antisym p q (H : strict_prefix p q) (G : strict_prefix q p) : False.
Proof.
  destruct (prefix_antisym p q).
  - apply strict_prefix_is_prefix. assumption.
  - apply strict_prefix_is_prefix. assumption.
  - eapply strict_prefix_irrefl. exact H.
Qed.

(* TODO: do I need this lemma? *)
Lemma disj_l_prefix p q r : disj p q -> prefix p r -> disj r q.
Proof.
  intros [ | (? & ? & ? & ? & ? & ? & ? & Hsnd_p & ?) ] [? <-].
  - left. assumption.
  - right.  split; try assumption. simpl. repeat eexists.
    + eassumption.
    + rewrite Hsnd_p. rewrite <-app_assoc. reflexivity.
    + eassumption.
Qed.

(* TODO: check that it doesn't break anything. *)
(* TODO: move *)
Local Hint Unfold app_spath_vpath : core.

Lemma not_vprefix_vdisj p q : vdisj p q -> ~vprefix p q.
Proof.
  intros (r' & p' & q' & i & j & diff & H & G) (r & <-). rewrite H, <-app_assoc in G.
  apply app_inv_head_iff in G. injection G. auto.
Qed.

Lemma not_prefix_disj p q : disj p q -> ~prefix p q.
Proof.
  intros [ | (? & ?)] (? & <-).
  - auto.
  - eapply (not_vprefix_vdisj (snd p) (snd _)); [eassumption | ]. eexists. reflexivity.
Qed.

Lemma not_disj_strict_prefix p q : disj p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. eapply not_prefix_disj; eassumption. Qed.

Lemma vdisj_common_prefix p q r : vdisj (p ++ q) (p ++ r) <-> vdisj q r.
Proof.
  split.
  - intro H. induction p as [ | x p IH].
    + assumption.
    + apply IH. cbn in H.
      destruct H as (p' & q' & r' & i & j & diff & Hqq' & Hrr').
      destruct p' as [ | y p'].
      * apply (f_equal (@hd_error _)) in Hqq', Hrr'. inversion Hqq'. inversion Hrr'.
        congruence.
      * inversion Hqq'. subst y. inversion Hrr'.
        exists p', q', r', i, j. auto.
  - intros (p' & q' & r' & i & j & ? & -> & ->).
    exists (p ++ p'), q', r', i, j. rewrite<- !app_assoc. auto.
Qed.

Corollary disj_common_prefix p q r : disj (p +++ q) (p +++ r) <-> vdisj q r.
Proof.
  split.
  - intros [H | (_ & H) ].
    + cbn in H. congruence.
    + eapply vdisj_common_prefix. exact H.
  - intro. right. split.
    + reflexivity.
    + apply vdisj_common_prefix. assumption.
Qed.

Lemma disj_common_index i p q : disj (i, p) (i, q) <-> vdisj p q.
Proof.
  split.
  - intros [H | (_ & ?)].
    + cbn in H. congruence.
    + assumption.
  - intro. right. auto.
Qed.

Lemma not_vprefix_implies_not_vstrict_prefix p q : ~vprefix p q -> ~vstrict_prefix p q.
Proof. intros ? ?%vstrict_prefix_is_vprefix. auto. Qed.

Lemma neq_implies_not_prefix p q : ~prefix p q -> p <> q.
Proof. intros H <-. apply H. reflexivity. Qed.

Lemma neq_implies_not_prefix' p q : ~prefix p q -> q <> p.
Proof. intro. symmetry. apply neq_implies_not_prefix. assumption. Qed.

Lemma disj_if_left_disj_prefix p q r : disj p q -> disj p (q +++ r).
Proof.
  intros [ | (? & (x & p' & q' & H))].
  - left. assumption.
  - right. split; [assumption | ]. exists x, p', (q' ++ r).
    decompose [ex and] H. repeat eexists; try eassumption. cbn.
    rewrite app_comm_cons, app_assoc. apply<- app_inv_tail_iff. assumption.
Qed.

Lemma prefix_trans p q r : prefix (p +++ q) r -> prefix p r.
Proof. intros (z & <-). rewrite<- app_spath_vpath_assoc. eexists. reflexivity. Qed.

Lemma prefix_and_neq_implies_strict_prefix p q : prefix p q -> p <> q -> strict_prefix p q.
Proof.
  intros ([ | ] & <-) H.
  - rewrite app_spath_vpath_nil_r in H. easy.
  - eexists _, _. reflexivity.
Qed.

Lemma not_prefix_left_strict_prefix_right' p q : prefix p q -> ~strict_prefix q p.
Proof. intros ? ?. eapply not_prefix_left_strict_prefix_right; eassumption. Qed.
Hint Resolve not_prefix_left_strict_prefix_right' : spath.

Corollary disj_if_right_disj_prefix p q r : disj p q -> disj (p +++ r) q.
Proof. intro. symmetry. apply disj_if_left_disj_prefix. symmetry. assumption. Qed.

Lemma decidable_vpath_eq (p q : vpath) : p = q \/ p <> q.
Proof.
  destruct (comparable_vpaths p q) as [ | | | ].
  - left. assumption.
  - right. intros <-. eapply vstrict_prefix_irrefl. eassumption.
  - right. intros <-. eapply vstrict_prefix_irrefl. eassumption.
  - right. intros <-. eapply vdisj_irrefl. eassumption.
Qed.

Lemma decidable_spath_eq (p q : spath) : p = q \/ p <> q.
Proof.
  destruct p as (i & p'). destruct q as (j & q').
  destruct (Nat.eq_dec i j); destruct (decidable_vpath_eq p' q'); intuition congruence.
Qed.

Lemma decidable_vprefix p q : vprefix p q \/ ~vprefix p q.
Proof.
  destruct (comparable_vpaths p q) as [<- | | | ].
  - left. reflexivity.
  - left. apply vstrict_prefix_is_vprefix. assumption.
  - right. apply not_vprefix_left_vstrict_prefix_right. assumption.
  - right. apply not_vprefix_vdisj. assumption.
Qed.

Lemma decidable_prefix p q : prefix p q \/ ~prefix p q.
Proof.
  destruct (comparable_spaths p q) as [<- | | | ].
  - left. reflexivity.
  - left. apply strict_prefix_is_prefix. assumption.
  - right. apply not_prefix_left_strict_prefix_right. assumption.
  - right. apply not_prefix_disj. assumption.
Qed.

Lemma vstrict_prefix_app_last p q i : vstrict_prefix p (q ++ i :: nil) -> vprefix p q.
Proof.
  intros (j & r & ?).
  destruct exists_last with (l := j :: r) as (r' & j' & G). { symmetry. apply nil_cons. }
  rewrite G in H. apply f_equal with (f := @removelast _) in H.
  rewrite app_assoc in H. rewrite !removelast_last in H. exists r'. exact H.
Qed.

Corollary strict_prefix_app_last p q i : strict_prefix p (q +++ [i]) <-> prefix p q.
Proof.
  split.
  - intros (j & r & H). inversion H.
    destruct (vstrict_prefix_app_last (snd p) (snd q) i) as (r' & ?).
    + exists j, r. assumption.
    + exists r'. apply injective_projections; assumption.
  - intros (r & <-). rewrite<- app_spath_vpath_assoc. destruct (r ++ [i]) eqn:EQN.
    + symmetry in EQN. apply app_cons_not_nil in EQN. destruct EQN.
    + eexists _, _. reflexivity.
Qed.

Corollary not_strict_prefix_app_last p q i : ~strict_prefix p (q +++ [i]) <-> ~prefix p q.
Proof. split; intros H ?; eapply H, strict_prefix_app_last; eassumption. Qed.

Lemma not_strict_prefix_nil (p : spath) i : ~strict_prefix p (i, []).
Proof.
  intros (? & ? & H). apply (f_equal snd) in H. eapply app_cons_not_nil. symmetry. exact H.
Qed.

(* Automatically solving a comparison C p q using the hypotheses. *)
Hint Resolve-> disj_common_prefix : spath.
Hint Resolve<- disj_common_index : spath.
Hint Immediate vstrict_prefix_is_vprefix : spath.
Hint Immediate not_vprefix_left_vstrict_prefix_right : spath.
Hint Resolve strict_prefix_irrefl : spath.
Hint Resolve not_disj_strict_prefix : spath.
Hint Immediate symmetric_disj : spath.
Hint Resolve not_prefix_implies_not_strict_prefix : spath.
Hint Immediate not_vprefix_implies_not_vstrict_prefix : spath.
Hint Resolve neq_implies_not_prefix : spath.
Hint Resolve neq_implies_not_prefix' : spath.
Hint Resolve disj_if_left_disj_prefix : spath.
Hint Resolve disj_if_right_disj_prefix : spath.
Hint Resolve<- strict_prefix_app_last : spath.
Hint Resolve not_strict_prefix_nil : spath.
Hint Extern 0 (prefix ?p (?p +++ ?q)) => exists q; reflexivity : spath.
Hint Extern 0 (prefix (?p +++ ?q) (?p +++ ?q ++ ?r)) =>
    exists r; symmetry; apply app_spath_vpath_assoc : spath.
Hint Resolve prefix_trans : spath.
Hint Resolve prefix_and_neq_implies_strict_prefix : spath.
Hint Resolve<- not_strict_prefix_app_last : spath.

Declare Scope GetSetPath_scope.
Open Scope GetSetPath_scope.

Class Value (V : Type) := {
  constructors : Type; (* a `constructor` type *)
  arity : constructors -> nat;
  subvalues : V -> list V;
  get_constructor : V -> constructors;
  fold_value : constructors -> list V -> V;
  (* A quantity decreasing as we traverse the value down. *)
  height : V -> nat;
  bot : V;

  length_subvalues_is_arity v : length (subvalues v) = arity (get_constructor v);
  constructor_subvalues_inj v w (eq_constructor : get_constructor v = get_constructor w)
                                (eq_subvalues : subvalues v = subvalues w) : v = w;
  get_constructor_fold_value c vs (H : length vs = arity c) : get_constructor (fold_value c vs) = c;
  subvalues_fold_value c vs (H : length vs = arity c) : subvalues (fold_value c vs) = vs;
  subvalues_bot : subvalues bot = nil;
  height_subvalue v i w : nth_error (subvalues v) i = Some w -> height w < height v;
}.

Notation get_subval_or_bot w i :=
  (match nth_error (subvalues w) i with
    | Some u => u
    | None => bot
  end).
Definition vget {V} `{Value V} : vpath -> V -> V :=
  fold_left (fun w i => get_subval_or_bot w i).
Notation "v .[[ p ]]" := (vget p v) (left associativity, at level 50) : GetSetPath_scope.

Fixpoint vset {V} `{Value V} (p : vpath) (w : V) (v : V) :=
  match p with
  | nil => w
  | i :: q => fold_value (get_constructor v) (map_nth (subvalues v) i (vset q w))
  end.
Notation "v .[[ p <- w ]]" := (vset p w v) (left associativity, at level 50).

Notation get_val S i := (SOME c <- nth_error S i IN Some (snd c)).

Notation get_binder S i := (SOME c <- nth_error S i IN Some (fst c)).

Notation "S ,, b |-> v" := (S ++ [(b, v)]) (at level 1, v at level 61).

Definition state B V := list (B * V).

Definition sget {V B} `{Value V} (p : spath) (S : state B V) : V :=
  match get_val S (fst p) with
  | Some v => v.[[snd p]]
  | None => bot
  end.
Notation "S .[ p ]" := (sget p S) (left associativity, at level 50) : GetSetPath_scope.

Definition sset {V B} `{Value V} (p : spath) (v : V) (S : state B V) :=
  map_nth S (fst p) (fun c => (fst c, (snd c).[[snd p <- v]])).
Notation "S .[ p <- v ]" := (sset p v S) (left associativity, at level 50).

Section GetSetPath.
  Context {V : Type}.
  Context {IsValue : Value V}.
  Context {B : Type}.

  Lemma vget_app v p q : v.[[p ++ q]] = v.[[p]].[[q]].
  Proof. unfold vget. apply fold_left_app. Qed.

  (* A vpath p is valid with regards to a value v if we can follow its indices down the value v
   * interpreted as a tree. *)
  Inductive valid_vpath : V -> vpath -> Prop :=
    | valid_nil v : valid_vpath v nil
    | valid_cons v i p w :
        nth_error (subvalues v) i = Some w -> valid_vpath w p -> valid_vpath v (i :: p).

  Lemma valid_vpath_app v p q :
    valid_vpath v (p ++ q) <-> valid_vpath v p /\ valid_vpath (v.[[p]]) q.
  Proof.
    split.
    - revert v. induction p as [ | i p IHp].
      + split. constructor. assumption.
      + intros v H. inversion H. subst. split.
        * econstructor; try apply IHp; eassumption.
        * apply IHp. simplify_option.
    - intros (valid_p & valid_q). induction valid_p.
      + exact valid_q.
      + cbn. econstructor.
        * eassumption.
        * cbn in valid_q. simplify_option.
  Qed.

  (* We characterize invalid path by their longest prefix q. It means that the next index i is
   * such that [...] *)
  Definition invalid_vpath v p :=
    exists q i r, p = q ++ i :: r /\ valid_vpath v q /\ nth_error (subvalues (v.[[q]])) i = None.

  Lemma valid_or_invalid p : forall v, valid_vpath v p \/ invalid_vpath v p.
  Proof.
    induction p as [ | i p IHp].
    - left. constructor.
    - intro v. destruct (nth_error (subvalues v) i) as [w | ] eqn:EQN.
      + destruct (IHp w) as [ | (q & j & r & -> & valid_q & G)].
        * left. econstructor; eassumption.
        * right. exists (i :: q), j, r. repeat split.
          -- econstructor; eassumption.
          -- cbn. rewrite EQN. exact G.
      + right. exists nil, i, p. repeat split; constructor || assumption.
  Qed.

  Lemma not_valid_and_invalid v p : valid_vpath v p -> invalid_vpath v p -> False.
  Proof.
    intros H (q & i & r & -> & valid_p & G). apply valid_vpath_app in H.
    destruct H as [_ H]. inversion H. simplify_option.
  Qed.

  Lemma vget_bot p : bot.[[p]] = bot.
  Proof.
     induction p.
    - reflexivity.
    - cbn. rewrite subvalues_bot, nth_error_nil. assumption.
  Qed.
  (* The vget function is defined in such a way that for any invalid path p, v.[[p]] = bot.
   * This relies on two design choices:
   * - For a value v, if the index i is the index of a subvalue, then v.[[i :: r]] = bot.[[r]].
   * - `bot` has 0 subvalues (`subvalues_bot` axiom), so bot.[[r]] = r.
   *)
  Lemma vget_invalid v p : invalid_vpath v p -> v.[[p]] = bot.
  Proof. intros (q & i & r & -> & _ & H). rewrite vget_app. cbn. rewrite H. apply vget_bot. Qed.

  (* A useful criterion for validity: if v.[[p]] <> bot, then p is a valid path for v.
     This is going to be the main way of proving validity. *)
  Corollary get_not_bot_valid_vpath v p (H : v.[[p]] <> bot) : valid_vpath v p.
  Proof.
    destruct (valid_or_invalid p v).
    - assumption.
    - exfalso. apply H. apply vget_invalid. assumption.
  Qed.

  Lemma invalid_prefix v p q : invalid_vpath v p -> invalid_vpath v (p ++ q).
  Proof.
    intros (p' & i & r & -> & ?). exists p', i, (r ++ q). split.
    - rewrite <-app_assoc. reflexivity.
    - assumption.
  Qed.

  Lemma constructor_vset_cons v p w :
    p <> [] -> get_constructor (v.[[p <- w]]) = get_constructor v.
  Proof. 
    intro. destruct p; [congruence | ].
    apply get_constructor_fold_value. rewrite map_nth_length. apply length_subvalues_is_arity.
  Qed.

  Lemma subvalues_vset_cons v i p w :
    subvalues (v.[[i :: p <- w]]) = map_nth (subvalues v) i (vset p w).
  Proof. apply subvalues_fold_value. rewrite map_nth_length. apply length_subvalues_is_arity. Qed.

  Lemma vget_cons v i p : v.[[i :: p]] = (get_subval_or_bot v i).[[p]].
  Proof. reflexivity. Qed.

  Lemma vstrict_prefix_one_subvalue v p q (H : length (subvalues (v.[[p]])) = 1) :
    vstrict_prefix p q -> valid_vpath v q -> vprefix (p ++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_vpath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
      inversion G. destruct (nth_error (subvalues (v.[[p]]))); easy. }
    exists r. rewrite<- app_assoc. reflexivity.
  Qed.

  Corollary not_vprefix_one_subvalue v p q :
    length (subvalues (v.[[p]])) = 1 -> valid_vpath v q -> ~vprefix (p ++ [0]) q
    -> ~vstrict_prefix p q.
  Proof. intros ? ? H ?. eapply H, vstrict_prefix_one_subvalue; eassumption. Qed.

  (* All of the lemmas to reduce an expression of the form v.[[q <- w]].[[p]], depending on the
   * following cases:
   * - p = q
   * - p is a prefix of q
   * - q is a prefix of p
   * - p and q are disjoint
   *)
  Lemma vset_vget_prefix v w p q (H : valid_vpath v p) :
    v.[[p ++ q <- w]].[[p]] = v.[[p]].[[q <- w]].
  Proof.
    induction H as [ | v i p u subval_v_i valid_u_p IH].
    - reflexivity.
    - rewrite vget_cons, <-app_comm_cons, subvalues_vset_cons, nth_error_map_nth_eq.
      simplify_option.
  Qed.

  Corollary vset_vget_equal v w p : valid_vpath v p -> v.[[p <- w]].[[p]] = w.
  Proof. intro. rewrite<- (app_nil_r p) at 2. rewrite vset_vget_prefix; auto. Qed.

  Lemma vset_same_valid v w p (H : valid_vpath v p) : valid_vpath (v.[[p <- w]]) p.
  Proof.
    induction H as [ | ? ? ? ? H].
    - constructor.
    - econstructor.
      + rewrite subvalues_vset_cons, nth_error_map_nth_eq, H. reflexivity.
      + assumption.
  Qed.

  Corollary vset_vget_prefix_right v w p q (H : valid_vpath v p) :
    v.[[p <- w]].[[p ++ q]] = w.[[q]].
  Proof. rewrite vget_app, vset_vget_equal; try apply vset_same_valid; auto. Qed.

  Lemma _vset_app_split v p q w (H : valid_vpath v p) :
    v.[[p ++ q <- w]] = v.[[p <- v.[[p]].[[q <- w]]]].
  Proof.
    induction H.
    - reflexivity.
    - cbn. f_equal. eapply map_nth_equal_Some; simplify_option.
  Qed.

  Lemma _vset_same v p (H : valid_vpath v p) : v.[[p <- v.[[p]]]] = v.
  Proof.
    induction H.
    - reflexivity.
    - apply constructor_subvalues_inj.
      + apply constructor_vset_cons. discriminate.
      + rewrite subvalues_vset_cons. eapply map_nth_invariant; simplify_option.
  Qed.

  (* vset is defined in such a way that v.[[p <- w]] is v when p is invalid.
   * To understand why, take v.[[i :: r <- w]] when i >= length (subvalues v):
   * - The constructor of v.[[i :: r <- w]] is the same constructor as v.
   * - The vset function is recursively applied in the i-th subvalue of v. But because the list
   *   of subvalues does not contained an i-th subvalue, because of the definiton of map_nth, the
   *   list of subvalues of v.[[i :: r <- w]] is the same as for v.
   * This trick allows us to omit validity hypotheses in some lemmas.
   *)
  Lemma vset_invalid v p w : invalid_vpath v p -> v.[[p <- w]] = v.
  Proof.
    intros (q & i & r & -> & valid_q & H). rewrite<- (_vset_same v q) at 2 by assumption.
    rewrite _vset_app_split by assumption. f_equal.
    apply constructor_subvalues_inj.
    - apply constructor_vset_cons. discriminate.
    - rewrite subvalues_vset_cons. apply map_nth_equal_None. assumption.
  Qed.

  Lemma vset_vget_disj_aux v i j p q w :
    i <> j -> v.[[i :: p <- w]].[[j :: q]] = v.[[j :: q]].
  Proof. intro. rewrite vget_cons, subvalues_vset_cons, nth_error_map_nth_neq; auto. Qed.

  Lemma vset_vget_disj v w p q (Hvdisj : vdisj p q) :
    v.[[p <- w]].[[q]] = v.[[q]].
  Proof.
    destruct (valid_or_invalid p v) as [H | ].
    - destruct Hvdisj as (r & p' & q' & i & j & diff & -> & ->).
      apply valid_vpath_app in H. destruct H as [H _].
      rewrite !vget_app, vset_vget_prefix by assumption. apply vset_vget_disj_aux. assumption.
    - rewrite vset_invalid; auto.
  Qed.

  Lemma vset_twice_equal p x y : forall v, v.[[p <- x]].[[p <- y]] = v.[[p <- y]].
  Proof.
    induction p; intro v.
    - reflexivity.
    - apply constructor_subvalues_inj.
      + rewrite !constructor_vset_cons by discriminate. reflexivity.
      + rewrite !subvalues_vset_cons, map_nth_compose. apply map_nth_equiv. assumption.
  Qed.

  Lemma vset_same v p : v.[[p <- v.[[p]]]] = v.
  Proof.
    destruct (valid_or_invalid p v).
    - now apply _vset_same.
    - rewrite vset_invalid; [reflexivity | assumption].
  Qed.

  (* Now the we proved that v.[[p <- w]] = v when p in invalid, we can remove the validity
   * hypothesis from the theorem _vset_app_split. *)
  Lemma vset_app_split v p q w : v.[[p ++ q <- w]] = v.[[p <- v.[[p]].[[q <- w]]]].
  Proof.
    destruct (valid_or_invalid p v) as [ | ].
    - apply _vset_app_split. assumption.
    - rewrite !vset_invalid; try auto. apply invalid_prefix. assumption.
  Qed.

  Lemma vset_twice_prefix_right v p q x y : vprefix q p -> v.[[p <- x]].[[q <- y]] = v.[[q <- y]].
  Proof. intros (? & <-). rewrite vset_app_split, vset_twice_equal. reflexivity. Qed.

  Lemma vset_twice_prefix_left v p q x y : v.[[p <- x]].[[p ++ q <- y]] = v.[[p <- x.[[q <- y]]]].
  Proof.
    rewrite vset_app_split, vset_twice_equal. destruct (valid_or_invalid p v).
    - rewrite vset_vget_equal; auto.
    - rewrite !vset_invalid; auto.
  Qed.

  Lemma vset_twice_disj_commute_aux v p q i j x y :
    i <> j -> v.[[i :: p <- x]].[[j :: q <- y]] = v.[[j :: q <- y]].[[i :: p <- x]].
  Proof.
    intro. apply constructor_subvalues_inj.
    - rewrite !constructor_vset_cons by discriminate. reflexivity.
    - rewrite !subvalues_vset_cons. apply map_nth_neq_commute. assumption.
  Qed.

  Lemma vset_twice_disj_commute v p q x y :
    vdisj p q -> v.[[p <- x]].[[q <- y]] = v.[[q <- y]].[[p <- x]].
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->).
    rewrite !(vset_app_split v). rewrite !vset_twice_prefix_left.
    rewrite vset_twice_disj_commute_aux; auto.
  Qed.

  Lemma get_arity_0 v i p : length (subvalues v) = 1 -> v.[[i :: p]] <> bot -> i = 0.
  Proof.
    intros H G. apply get_not_bot_valid_vpath in G. inversion G.
    apply length_1_is_singleton in H. destruct H as (? & H). rewrite H in *. destruct i.
    - reflexivity.
    - rewrite nth_error_cons, nth_error_nil in *. simplify_option.
  Qed.

  (* Two values are equal if they have the same constructors everywhere. *)
  Lemma get_constructor_vget_ext v w :
    (forall p, get_constructor (v.[[p]]) = get_constructor (w.[[p]])) -> v = w.
  Proof.
    remember (height v) as n. revert v w Heqn.
    induction n as [n IH] using lt_wf_ind. intros v w -> H.
    assert (get_constructor v = get_constructor w) by exact (H []).
    assert (eq_length : length (subvalues v) = length (subvalues w)).
    { rewrite !length_subvalues_is_arity. f_equal. assumption. }
    apply constructor_subvalues_inj; [assumption | ].
    apply nth_error_ext. intro i. destruct (nth_error (subvalues v) i) eqn:EQN.
    - assert (i < length (subvalues w)).
      { rewrite <-eq_length. apply nth_error_Some. rewrite EQN. discriminate. }
      assert (nth_error (subvalues w) i <> None) by now apply nth_error_Some.
      destruct (nth_error (subvalues w) i) eqn:EQN'; [ | contradiction].
      f_equal. eapply IH; [ | reflexivity | ].
      + eapply height_subvalue. eassumption.
      + intro p. specialize (H (i :: p)). cbn in H. rewrite EQN, EQN' in H. exact H.
    - symmetry. apply nth_error_None. rewrite <-eq_length. apply nth_error_None. assumption.
    Qed.

  Lemma length_sset (S : state B V) p v : length (S.[p <- v]) = length S.
  Proof. apply map_nth_length. Qed.

  (* Proving the same with sget and sset: *)
  Lemma sget_app (S : state B V) p q : S.[p +++ q] = S.[p].[[q]].
  Proof.
    unfold sget, app_spath_vpath. cbn. destruct (get_val S (fst p)).
    - apply vget_app.
    - rewrite vget_bot. reflexivity.
  Qed.

  (* Lemmas about validity of spaths. *)
  Definition valid_spath (S : state B V) (p : spath) :=
    exists v, get_val S (fst p) = Some v /\ valid_vpath v (snd p).

  Lemma valid_spath_app (S : state B V) p q :
    valid_spath S (p +++ q) <-> valid_spath S p /\ valid_vpath (S.[p]) q.
  Proof.
    split.
    - intros (v & H & G). cbn in *. rewrite valid_vpath_app in G. destruct G.
      split.
      + exists v. auto.
      + unfold sget. simplify_option.
    - intros [(v & H & ?) G]. exists v. cbn. split.
      + assumption.
      + apply valid_vpath_app. unfold sget in G. rewrite H in G. auto.
  Qed.

  Lemma get_not_bot_valid_spath (S : state B V) p (H : S.[p] <> bot) : valid_spath S p.
  Proof.
    unfold sget in H. destruct (get_val S (fst p)) as [v | ] eqn:EQN.
    - exists v. split. { assumption. } apply get_not_bot_valid_vpath. assumption.
    - exfalso. apply H. reflexivity.
  Qed.

  Lemma strict_prefix_one_subvalue S p q (H : length (subvalues (S.[p])) = 1) :
    strict_prefix p q -> valid_spath S q -> prefix (p +++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_spath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
      inversion G. destruct (nth_error (subvalues (S.[p]))); easy. }
    exists r. rewrite<- app_spath_vpath_assoc. reflexivity.
  Qed.

  Corollary not_prefix_one_subvalue S p q :
    length (subvalues (S.[p])) = 1 -> valid_spath S q -> ~prefix (p +++ [0]) q -> ~strict_prefix p q.
  Proof. intros ? ? H ?. eapply H, strict_prefix_one_subvalue; eassumption. Qed.

  Lemma sset_sget_prefix (S : state B V) v p q :
    valid_spath S p -> S.[p +++ q <- v].[p] = S.[p].[[q <- v]].
  Proof.
    intros (w & Hget & Hvalid). unfold sget, sset.
    rewrite nth_error_map_nth_eq. simplify_option. rewrite vset_vget_prefix; auto.
  Qed.

  Lemma sset_sget_equal S p v : valid_spath S p -> S.[p <- v].[p] = v.
  Proof.
    intro. rewrite <-(app_spath_vpath_nil_r p) at 2.
    rewrite sset_sget_prefix; auto.
  Qed.

  Lemma sset_sget_prefix_right S v p q (H : valid_spath S p) :
    S.[p <- v].[p +++ q] = v.[[q]].
  Proof. rewrite sget_app, sset_sget_equal; auto. Qed.

  Lemma sset_sget_common_prefix S p q r v :
    valid_spath S p -> S.[p +++ q <- v].[p +++ r] = S.[p].[[q <- v]].[[r]].
  Proof. intro. rewrite sget_app. rewrite sset_sget_prefix by assumption. reflexivity. Qed.

  Lemma sset_sget_disj (S : state B V) p v q : disj p q -> S.[p <- v].[q] = S.[q].
  Proof.
    unfold sset, sget. intros [ | (<- & Hdisj)].
    - rewrite nth_error_map_nth_neq by assumption. reflexivity.
    - rewrite nth_error_map_nth_eq. autodestruct. intro. apply vset_vget_disj. assumption.
  Qed.

  Lemma constructor_vset_vget_strict_prefix v p q w :
    vstrict_prefix p q -> get_constructor (v.[[q <- w]].[[p]]) = get_constructor (v.[[p]]).
  Proof.
     intros (i & r & <-). destruct (valid_or_invalid p v).
     - rewrite vset_vget_prefix by assumption. apply constructor_vset_cons. discriminate.
     - assert (invalid_vpath v (p ++ i :: r)) by now apply invalid_prefix.
       now rewrite vset_invalid.
  Qed.

  (* During the proof of this theorem, we implicitely use the fact that if the spath p is
   * invalid, then the spath q is invalid, and S.[q <- w] = S. *)
  Lemma constructor_sset_sget_strict_prefix (S : state B V) p q w :
    strict_prefix p q -> get_constructor (S.[q <- w].[p]) = get_constructor (S.[p]).
  Proof.
    unfold sset, sget. intro H.
    assert (fst p = fst q) as ->. { destruct H as (? & ? & <-). reflexivity. }
    rewrite nth_error_map_nth_eq. simplify_option.
    intro. apply constructor_vset_vget_strict_prefix.
    destruct H as (? & ? & <-). eexists _, _. reflexivity.
  Qed.

  Lemma constructor_vset_vget_not_prefix v p q w (H : ~vprefix q p) :
    get_constructor (v.[[q <- w]].[[p]]) = get_constructor (v.[[p]]).
  Proof.
    destruct (comparable_vpaths p q) as [<- | | (? & ? & ?) | ].
    - destruct H. exists nil. apply app_nil_r. (* TODO: reflexivity lemma? *)
    - apply constructor_vset_vget_strict_prefix. assumption.
    - destruct H. eexists. eassumption. (* TODO: vstrict_prefix -> vprefix ? *)
    - rewrite vset_vget_disj; [reflexivity | symmetry; assumption].
  Qed.

  Lemma constructor_sset_sget_not_prefix (S : state B V) p q w (H : ~prefix q p) :
    get_constructor (S.[q <- w].[p]) = get_constructor (S.[p]).
  Proof.
    destruct (comparable_spaths p q) as [<- | | | ].
    - destruct H. reflexivity.
    - apply constructor_sset_sget_strict_prefix. assumption.
    - destruct H. apply strict_prefix_is_prefix. assumption.
    - rewrite sset_sget_disj; reflexivity || symmetry; assumption.
  Qed.

  Lemma sset_twice_prefix_right (S : state B V) p q x y :
    S.[p +++ q <- x].[p <- y] = S.[p <- y].
  Proof.
    unfold sset. cbn. rewrite map_nth_compose. cbn. apply map_nth_equiv.
    intro. rewrite vset_twice_prefix_right.
    - reflexivity.
    - exists q. reflexivity.
  Qed.

  Corollary sset_twice_equal (S : state B V) p x y : S.[p <- x].[p <- y] = S.[p <- y].
  Proof. rewrite<- (app_spath_vpath_nil_r p) at 2. apply sset_twice_prefix_right. Qed.

  Lemma sset_twice_preix_left (S : state B V) p q x y :
    S.[p <- x].[p +++ q <- y] = S.[p <- x.[[q <- y]]].
  Proof.
    unfold sset. cbn. rewrite map_nth_compose. cbn. apply map_nth_equiv.
    intro. rewrite vset_twice_prefix_left. reflexivity.
  Qed.

  Lemma sset_twice_disj_commute (S : state B V) p q v w :
    disj p q -> S.[p <- v].[q <- w] = S.[q <- w].[p <- v].
  Proof.
    unfold sset. intros [ | (<- & ?)].
    - apply map_nth_neq_commute. assumption.
    - rewrite !map_nth_compose. apply map_nth_equiv. intro. cbn. f_equal.
      apply vset_twice_disj_commute. assumption.
  Qed.

  (* Interaction between validity and sset.
     Goal: if q is not a prefix of p, then p in valid in S iff p is valid in S.[q <- w].
     In other words, setting q does not affect the validity of p. *)
  Lemma vset_prefix_right_valid v p q w : valid_vpath v p -> valid_vpath (v.[[p ++ q <- w]]) p.
  Proof.
    intro. destruct (valid_or_invalid (p ++ q) v) as [G | ].
    - apply vset_same_valid with (w := w) in G. apply valid_vpath_app in G. destruct G. assumption.
    - rewrite vset_invalid; assumption.
  Qed.

  Lemma vset_disj_valid_aux v i j p q w :
    i <> j -> valid_vpath v (i :: p) -> valid_vpath (v.[[j :: q <- w]]) (i :: p).
  Proof.
    intros ? H. inversion H. subst.
    econstructor; [ | eassumption]. rewrite subvalues_vset_cons, nth_error_map_nth_neq; auto.
  Qed.

  Lemma vset_disj_valid v p q w :
    vdisj p q -> valid_vpath v p -> valid_vpath (v.[[q <- w]]) p.
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->) (? & ?)%valid_vpath_app.
    apply valid_vpath_app. split.
    - apply vset_prefix_right_valid. assumption.
    - rewrite vset_vget_prefix by assumption. apply vset_disj_valid_aux; assumption.
  Qed.

  Lemma vset_same_valid_rev v p w : valid_vpath (v.[[p <- w]]) p -> valid_vpath v p.
  Proof.
    intro. rewrite <-(vset_same v p). rewrite <-(vset_twice_equal p w _ v).
    apply vset_same_valid. assumption.
  Qed.

  Lemma vset_not_prefix_valid_rev v p q w (H : ~vstrict_prefix q p) :
    valid_vpath (v.[[q <- w]]) p -> valid_vpath v p.
  Proof.
    intro G. destruct (comparable_vpaths p q) as [<- |(? & ? & <-) | | ].
    - eapply vset_same_valid_rev; exact G.
    - rewrite vset_app_split in G. eapply vset_same_valid_rev; exact G.
    - contradiction.
    - rewrite <-(vset_same v q). rewrite <-(vset_twice_equal q w _ v).
      apply vset_disj_valid; assumption.
  Qed.

  Lemma sset_prefix_right_valid (S : state B V) p q v :
    prefix p q -> valid_spath S p -> valid_spath (S.[q <- v]) p.
  Proof.
    intros (r & <-) (w & ? & ?). exists (w.[[snd p ++ r <- v]]). split.
    - unfold sset. rewrite nth_error_map_nth_eq. simplify_option.
    - apply vset_prefix_right_valid. assumption.
  Qed.

  Lemma _sset_not_prefix_valid (S : state B V) p q v :
    ~strict_prefix q p -> valid_spath S p -> valid_spath (S.[q <- v]) p.
  Proof.
    intros ? H.
    destruct (comparable_spaths p q) as [<- | (i & r & <-) | | Hdisj ].
    - apply sset_prefix_right_valid; [reflexivity | assumption].
    - apply sset_prefix_right_valid; [ | assumption]. eexists. reflexivity.
    - contradiction.
    - destruct H as (w & ? & ?). unfold sset. destruct Hdisj as [ | (<- & ?)].
      + exists w. split; [ | assumption]. rewrite nth_error_map_nth_neq; auto.
      + exists (w.[[snd q <- v]]). split.
        * rewrite nth_error_map_nth_eq. simplify_option.
        * apply vset_disj_valid; assumption.
  Qed.

  Lemma sset_same (S : state B V) p : S.[p <- S.[p] ] = S.
  Proof.
    unfold sget, sset. apply nth_error_ext. intro i. destruct (Nat.eq_dec (fst p) i) as [<- | ].
    - rewrite nth_error_map_nth_eq. autodestruct.
      rewrite vset_same, <-surjective_pairing. reflexivity.
    - rewrite nth_error_map_nth_neq by assumption. reflexivity.
  Qed.

  Lemma sset_not_prefix_valid (S : state B V) p q v :
    ~strict_prefix q p -> valid_spath S p <-> valid_spath (S.[q <- v]) p.
  Proof.
    intros ?. split.
    - apply _sset_not_prefix_valid. assumption.
    - intro.
      assert (valid_spath (S.[q <- v].[q <- S.[q] ]) p) by now apply _sset_not_prefix_valid.
      rewrite sset_twice_equal, sset_same in * |-. assumption.
  Qed.

  Corollary sset_prefix_valid S p q v :
    valid_spath S p -> valid_vpath v q -> valid_spath (S.[p <- v]) (p +++ q).
  Proof.
    intros. apply valid_spath_app. split.
    - apply sset_not_prefix_valid; [ apply strict_prefix_irrefl | assumption].
    - rewrite sset_sget_equal; assumption.
  Qed.

  Lemma sget_app_state (S S' : state B V) p : valid_spath S p -> (S ++ S').[p] = S.[p].
  Proof.
    intros (w & (? & _)). unfold sget. rewrite nth_error_app1. { reflexivity. }
    apply nth_error_Some. simplify_option.
  Qed.

  (* TODO: switch directions? *)
  Lemma sset_app_state (S S' : state B V) p v :
    valid_spath S p -> (S ++ S').[p <- v] = S.[p <- v] ++ S'.
  Proof.
    intros (w & (? & ?)). unfold sset. apply nth_error_ext. intro i.
    destruct (Nat.lt_ge_cases i (length S)) as [ | ].
    - destruct (Nat.eq_dec (fst p) i) as [-> | ].
      + rewrite nth_error_map_nth_eq.
        rewrite !nth_error_app1 by (try rewrite map_nth_length; assumption).
        symmetry. apply nth_error_map_nth_eq.
      + rewrite nth_error_map_nth_neq by assumption.
        rewrite !nth_error_app1 by (try rewrite map_nth_length; assumption).
        symmetry. apply nth_error_map_nth_neq. assumption.
    - rewrite nth_error_map_nth_neq.
      { rewrite !nth_error_app2; try rewrite map_nth_length; auto. }
      apply Nat.lt_neq. unfold lt. transitivity (length S); try assumption.
      apply nth_error_Some. simplify_option.
  Qed.

  (* TODO: switch directions? *)
  Lemma sset_app_last_state (S : state B V) b p v w :
    fst p = length S -> (S,, b |-> v).[p <- w] = S,, b |-> v.[[snd p <- w]].
  Proof.
    destruct p. cbn. intros ->. apply nth_error_ext. intro i.
    destruct (Nat.lt_trichotomy i (length S)) as [ | [-> | ] ]; unfold sset.
    - rewrite nth_error_map_nth_gt by assumption.
      rewrite !nth_error_app1 by assumption. reflexivity.
    - rewrite nth_error_map_nth_eq.
      rewrite !nth_error_app2, Nat.sub_diag by auto. reflexivity.
    - rewrite nth_error_map_nth_lt by assumption.
      etransitivity; [ | symmetry].
      all: apply nth_error_None; rewrite app_length, Nat.add_1_r; assumption.
  Qed.

  Lemma sget_app_last_state (S : state B V) b p v :
    fst p = length S -> (S,, b |-> v).[p] = v.[[snd p]].
  Proof.
    destruct p. cbn. intros ->.
    unfold sget. rewrite nth_error_app2 by auto. rewrite Nat.sub_diag. reflexivity.
  Qed.

  (* This lemma is used to prove that in an environment S ,, Anon |-> v, a spath p
     relating to a value in S and a spath q relating to a value in (Anon |-> v) are disjoint.
   *)
  Lemma disj_spath_to_last S p q : valid_spath S p -> disj p (length S, q).
  Proof.
    intros (? & ? & _). left. apply Nat.lt_neq. apply nth_error_Some.
    destruct (nth_error S (fst p)); easy.
  Qed.

  Lemma disj_spath_to_last' S p q : valid_spath S p -> disj (length S, q) p.
  Proof. symmetry. apply disj_spath_to_last. assumption. Qed.

  Lemma valid_app_spath S S' p : valid_spath S p -> valid_spath (S ++ S') p.
  Proof.
    intros (v & ? & ?). exists v. split; [ | assumption].
    rewrite nth_error_app1 by (apply nth_error_Some; simplify_option). assumption.
  Qed.

  Lemma valid_spath_last S b v p : valid_vpath v p -> valid_spath (S,, b |-> v) (length S, p).
  Proof.
    intro. exists v. split; [ | assumption]. rewrite nth_error_app2, Nat.sub_diag; reflexivity.
  Qed.

  Lemma valid_spath_app_last_cases S b v p :
    valid_spath (S,, b |-> v) p -> valid_spath S p \/ fst p = length S.
  Proof.
    intros (w & H & ?). destruct (Nat.lt_ge_cases (fst p) (length S)).
    - left. exists w. split; [ | assumption].
      rewrite nth_error_app1 in H by assumption. exact H.
    - right. apply Nat.le_antisymm; try assumption.
      assert (G : fst p < length (S,, b |-> v)).
      { apply nth_error_Some. simplify_option. }
      rewrite app_length in G. cbn in G. lia.
  Qed.

  (* TODO: move up *)
  Lemma decidable_valid_spath S p : valid_spath S p \/ ~valid_spath S p.
  Proof.
    destruct p as (i & q). unfold valid_spath. cbn. destruct (nth_error S i) as [(? & v) | ].
    - destruct (valid_or_invalid q v).
      + left. exists v. auto.
      + right. intros (? & [=->] & ?). eapply not_valid_and_invalid; eassumption.
    - right. intros (? & [=] & ?).
  Qed.

  Lemma valid_spath_app_last S b v p :
    valid_spath (S,, b |-> v) p -> ~valid_spath S p -> fst p = length S.
  Proof.
    destruct p as (i & q). intros (? & H & ?) not_valid_S_p.
    destruct (Nat.lt_trichotomy i (length S)) as [ | [-> | Hgt] ].
    - exfalso. apply not_valid_S_p. rewrite nth_error_app1 in H by assumption.
      eexists. eauto.
    - reflexivity.
    - rewrite nth_error_app2 in H by now apply Nat.lt_le_incl. cbn in H.
      apply Nat.sub_gt in Hgt.
      destruct (i - length S).
      + easy.
      + cbn in H. rewrite nth_error_nil in H. easy.
  Qed.

  (*
  Lemma valid_spath_app_last S b v p : valid_spath (S,, b |-> v) p ->
      (valid_spath S p \/ fst p = length S /\ valid_vpath v (snd p)).
  Proof.
    intros (w & ? & ?). destruct 
   *)
  (* Two states are equal if they have the same constructors everywhere. *)
  Lemma get_constructor_sget_ext (S S' : state B V) :
    (forall i, get_binder S i = get_binder S' i) -> (forall p, get_constructor (S.[p]) = get_constructor (S'.[p])) -> S = S'.
  Proof.
    intros eq_binders eq_constructors.
    apply nth_error_ext. intro i. specialize (eq_binders i). destruct (nth_error S i) eqn:EQN.
    - destruct (nth_error S' i) eqn:EQN'; [ | discriminate].
      f_equal. apply injective_projections; [simplify_option | ].
      apply get_constructor_vget_ext. intro q.
      specialize (eq_constructors (i, q)). unfold sget in eq_constructors. cbn in eq_constructors.
      rewrite EQN, EQN' in eq_constructors. exact eq_constructors.
    - destruct (nth_error S' i); easy.
  Qed.

  Context `{EqDecBinder : EqDec B}.

  Fixpoint find_binder (S : state B V) (b : B) : option nat := match S with
  | nil => None
  | (b', _) :: S' => if eq_dec b b' then Some 0 else SOME i <- find_binder S' b IN Some (1 + i)
  end.

  Lemma find_binder_Some S b i :
    find_binder S b = Some i <-> get_binder S i = Some b /\ forall j, j < i -> get_binder S j <> Some b.
  Proof.
    split.
    - revert i. induction S as [ | (b' & v) S' IH].
      + discriminate.
      + intros i H. cbn in H. destruct (eq_dec b b') as [<- | neq ].
        * simplify_option. easy.
        * destruct (find_binder S' b) as [n | ]; try discriminate.
          injection H. intros <-. destruct (IH n) as (IH0 & IH1). { reflexivity. }
          split; try assumption.
          intros j ?. rewrite nth_error_cons. destruct j.
          -- simplify_option.
          -- apply IH1, Nat.succ_lt_mono. assumption.
    - revert i. induction S as [ | (b' & v) S' IH]; intros i (get_i & get_j).
      + rewrite nth_error_nil in get_i. discriminate.
      + cbn. destruct (eq_dec b b') as [<- | ].
        * destruct i; try reflexivity. exfalso. apply (get_j 0); try reflexivity.
          apply Nat.lt_0_succ.
        * destruct i as [ | i'].
          -- simplify_option.
          -- rewrite (IH i'). { reflexivity. } split; try assumption.
             intros j ?. apply (get_j (1 + j)). apply Nat.succ_lt_mono in H. exact H.
  Qed.

  Lemma find_binder_None S b :
    find_binder S b = None <-> forall i, get_binder S i <> Some b.
  Proof.
    split.
    - intro H. induction S as [ | (b' & v) S' IH].
      + intro. rewrite nth_error_nil. discriminate.
      + intros [ | i'].
        * intros [=->]. cbn in H. destruct (eq_dec b b); easy.
        * apply IH. cbn in H. destruct (eq_dec b b'); simplify_option.
    - induction S as [ | (b' & v) S' IH].
      + reflexivity.
      + intro. cbn. destruct (eq_dec b b') as [<- | ].
        * exfalso. apply (H 0). reflexivity.
        * rewrite IH. { reflexivity. } intro i. specialize (H (1 + i)). apply H.
  Qed.

  Lemma get_binder_sset (S : state B V) i p v : get_binder (S.[p <- v]) i = get_binder S i.
  Proof.
    unfold sset. destruct (Nat.eq_dec (fst p) i) as [-> | ].
    - rewrite nth_error_map_nth_eq. simplify_option.
    - rewrite nth_error_map_nth_neq; auto.
  Qed.

  Corollary find_binder_sset S b p v : find_binder (S.[p <- v]) b = find_binder S b.
  Proof.
    destruct (find_binder S b) eqn:H.
    - apply find_binder_Some. setoid_rewrite get_binder_sset. apply find_binder_Some, H.
    - apply find_binder_None. setoid_rewrite get_binder_sset. apply find_binder_None, H.
  Qed.

  Lemma find_binder_prop S b :
    forall i, find_binder S b = Some i -> exists v, nth_error S i = Some (b, v).
  Proof. induction S as [ | bv S' IH]; simplify_option. congruence. Qed.

  Corollary find_binder_valid S b i (H : find_binder S b = Some i) : valid_spath S (i, nil).
  Proof.
    apply find_binder_prop in H. destruct H as (v & ?). exists v. split.
    - cbn. rewrite H. reflexivity.
    - apply valid_nil.
  Qed.

  Lemma get_nil_prefix_right S p q :
  subvalues (S .[ p]) = [] -> valid_spath S q -> ~strict_prefix p q.
  Proof.
    intros H valid_q (i & r & <-). apply valid_spath_app in valid_q. 
    destruct valid_q as (_ & valid_i_r). inversion valid_i_r.
    rewrite H, nth_error_nil in * |-. discriminate.
  Qed.

  (* Setting up the definitions for judgements like "loan \notin v" or
     "l is fresh". *)
  Definition not_value_contains (P : constructors -> Prop) (v : V) :=
    forall p, valid_vpath v p -> ~P (get_constructor (v.[[p]])).

  Definition not_state_contains (P : constructors -> Prop) (S : state B V) :=
    forall p, valid_spath S p -> ~P (get_constructor (S.[p])).

  Definition not_contains_outer (is_mut_borrow P : constructors -> Prop) v :=
    forall p, P (get_constructor (v.[[p]]))
    -> exists q, vstrict_prefix q p /\ is_mut_borrow (get_constructor (v.[[q]])).

  Lemma not_value_contains_not_prefix P (S : state B V) p q
    (Hnot_contains : not_value_contains P (S.[p])) (HP : P (get_constructor (S.[q]))) (Hvalid : valid_spath S q) :
    ~prefix p q.
  Proof.
    intros (r & <-). apply valid_spath_app in Hvalid. apply Hnot_contains with (p := r); [easy | ].
    rewrite<- sget_app. assumption.
  Qed.

  Lemma not_value_contains_vset P v w p : not_value_contains P v -> not_value_contains P w ->
    not_value_contains P (v.[[p <- w]]).
  Proof.
    intros H G q valid_q. destruct (decidable_vprefix p q) as [(? & <-) | ].
    - apply valid_vpath_app in valid_q. destruct valid_q as (?%vset_same_valid_rev & validity_w).
      rewrite vset_vget_equal in validity_w by assumption.
      rewrite vset_vget_prefix_right by assumption. apply G. assumption.
    - rewrite constructor_vset_vget_not_prefix by assumption. apply H.
      eapply vset_not_prefix_valid_rev; [ | eassumption].
      intros ?%vstrict_prefix_is_vprefix. auto.
  Qed.

  Lemma not_state_contains_sset P S v p
    (not_in_S : not_state_contains P S)
    (not_in_v : not_value_contains P v) :
    not_state_contains P (S.[p <- v]).
  Proof.
    intros q valid_q.
    destruct (decidable_prefix p q) as [(r & <-) | ].
    - apply valid_spath_app in valid_q.
      destruct valid_q as (?%sset_not_prefix_valid & H); [ |  apply strict_prefix_irrefl].
      rewrite sset_sget_equal in H by assumption.
      rewrite sset_sget_prefix_right by assumption. apply not_in_v. assumption.
    - rewrite constructor_sset_sget_not_prefix by assumption.
      apply not_in_S. eapply sset_not_prefix_valid; [ | exact valid_q]. auto with spath.
  Qed.

  Lemma not_value_contains_sset P S v p q
    (not_in_Sp : not_value_contains P (S.[p]))
    (not_in_v : not_value_contains P v)
    (valid_p : valid_spath (S.[q <- v]) p) :
    not_value_contains P (S.[q <- v].[p]).
  Proof.
    intros r valid_r. rewrite<- sget_app.
    assert (valid_pr : valid_spath (S.[q <- v]) (p +++ r)).
    { apply valid_spath_app. split; assumption. }
    destruct (decidable_prefix q (p +++ r)) as [(? & eq) | ].
    - rewrite <-eq in *. rewrite valid_spath_app in valid_pr.
      destruct valid_pr as (valid_q & valid_v_r).
      apply sset_not_prefix_valid in valid_q; [ | apply strict_prefix_irrefl].
      rewrite sset_sget_equal in valid_v_r by assumption.
      rewrite sset_sget_prefix_right by assumption. apply not_in_v. exact valid_v_r.
    - rewrite constructor_sset_sget_not_prefix by assumption. rewrite sget_app. apply not_in_Sp.
      apply sset_not_prefix_valid in valid_pr; [ | auto with spath].
      apply valid_spath_app in valid_pr as (_ & ?). assumption.
  Qed.

  Lemma not_value_contains_sset_disj P (S : state B V) v p q
    (Hdisj : disj q p)
    (not_in_Sp : not_value_contains P (S.[p])) :
    not_value_contains P (S.[q <- v].[p]).
  Proof.
    intros r valid_r. rewrite<- sget_app. rewrite sset_sget_disj by auto with spath.
    rewrite sget_app. apply not_in_Sp.
    rewrite sset_sget_disj in valid_r; assumption.
  Qed.

  Lemma not_value_contains_zeroary P v :
    subvalues v = [] -> ~P (get_constructor v) -> not_value_contains P v.
  Proof.
    intros H ? p valid_p. destruct valid_p; [assumption | ].
    rewrite H, nth_error_nil in * |-. discriminate.
  Qed.

  Lemma not_value_contains_unary P v w :
    subvalues v = [w] -> ~P (get_constructor v) -> not_value_contains P w -> not_value_contains P v.
  Proof.
    intros H ? ? p valid_p. destruct valid_p; [assumption | ].
    rewrite H, nth_error_cons in * |-. destruct i; [ | rewrite nth_error_nil in * |-; discriminate].
    rewrite vget_cons, H. simplify_option.
  Qed.

  Lemma not_state_contains_implies_not_value_contains_sget P S p :
    not_state_contains P S -> valid_spath S p -> not_value_contains P (S.[p]).
  Proof.
    intros H valid_p q valid_q G. rewrite<- sget_app in G. eapply H; [ | exact G].
    apply valid_spath_app. split; assumption.
  Qed.

  Lemma not_value_contains_by_decomposition P v (H : ~P (get_constructor v))
    (G : match subvalues v with
         | [] => True
         | [w] => not_value_contains P w
         | _ => False
         end) :
    not_value_contains P v.
  Proof.
    destruct (subvalues v) as [ | ? [ | ] ] eqn:?.
    - apply not_value_contains_zeroary; assumption.
    - eapply not_value_contains_unary; eassumption.
    - contradiction.
  Qed.

  Lemma not_contains_outer_sset_no_contains is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v -> not_value_contains P w
    -> (forall v, P v -> v <> get_constructor bot)
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv Hw ?. destruct (valid_or_invalid p v).
    - intros q Hq. destruct (decidable_vprefix p q) as [(r & <-) | not_prefix].
      + exfalso.
        rewrite vset_vget_prefix_right in Hq by assumption. eapply Hw; [ | eassumption].
        apply get_not_bot_valid_vpath. intro wr. apply (H _ Hq). rewrite wr. reflexivity.
      + destruct (Hv q) as (r & ? & ?).
        * rewrite constructor_vset_vget_not_prefix in Hq; assumption.
        * exists r. split; [assumption | ]. rewrite constructor_vset_vget_not_prefix.
          assumption. intro. apply not_prefix. transitivity r; auto with spath.
    - rewrite vset_invalid by assumption. assumption.
  Qed.

  Lemma not_contains_outer_sset_in_borrow is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v
    -> (exists q, vstrict_prefix q p /\ is_mut_borrow (get_constructor (v.[[q]])))
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv (q & H & ?). destruct (valid_or_invalid p v).
    - intros r Hr. destruct (decidable_vprefix p r) as [(r' & <-) | not_prefix].
      + exists q.
        split.
        * destruct H as (i & ? & <-). eexists i, _. rewrite<- app_assoc. reflexivity.
        * rewrite constructor_vset_vget_not_prefix by auto with spath. assumption.
      + destruct (Hv r) as (q' & ? & ?).
        * rewrite constructor_vset_vget_not_prefix in Hr; assumption.
        * exists q'. split; [assumption | ]. rewrite constructor_vset_vget_not_prefix.
          assumption. intro. apply not_prefix. transitivity q'; auto with spath.
    - rewrite vset_invalid by assumption. assumption.
  Qed.
End GetSetPath.

(* Automatically solving comparisons using environment information. *)
Hint Resolve strict_prefix_one_subvalue : spath.
Hint Resolve not_vprefix_one_subvalue : spath.
Hint Resolve not_prefix_one_subvalue : spath. (* TODO: delete? *)
Hint Extern 5 (length (subvalues ?v) = _) =>
  match goal with
  | H : get_constructor (?S.[?p]) = _ |- _ =>
      rewrite length_subvalues_is_arity, H; reflexivity
  end : spath.
Hint Extern 5 (~strict_prefix ?p ?q) =>
  match goal with
  | H : ?S.[?p] = _ |- _ =>
      simple apply (get_nil_prefix_right S); [rewrite H | ]
  end : spath.
Hint Resolve disj_spath_to_last : spath.
Hint Resolve disj_spath_to_last' : spath.

(* Try to automatically solve a validity goal validity S pi. Here is how the procedure should
 * work:
 * - If the state S is of the form S'.[q <- v], reduce to valid S' pi provided that
     ~strict_prefix q pi.
 * - If the state S is of the form S,, b |-> v
 *   - If pi = (length S, q), meaning that pi refers to the last binding, reduce to valid v q
 *   - Otherwise, reduce to valid S pi
 * - Search the proof that pi is the evaluation of a place.
 * - Search for a proof that S.[p] <> bot in the hypotheses.
 * - Search for a proof that the constructor of S.[p] is not bot in the hypotheses.
 *)
Lemma valid_get_constructor_sget_not_bot {B V} `{IsValue : Value V} (S : state B V) p :
  get_constructor (S.[p]) <> get_constructor bot -> valid_spath S p.
Proof. intros G. apply get_not_bot_valid_spath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_get_constructor_vget_not_bot {V} `{IsValue : Value V} v p :
  get_constructor (v.[[p]]) <> get_constructor bot -> valid_vpath v p.
Proof. intros G. apply get_not_bot_valid_vpath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_vpath_app_last_get_constructor_not_zeoray {V} `{IsValue : Value V} v p :
  arity (get_constructor (v.[[p]])) > 0 -> valid_vpath v (p ++ [0]).
Proof.
  intro. apply valid_vpath_app. split.
  - apply get_not_bot_valid_vpath. intro G. rewrite G in H.
    rewrite <-length_subvalues_is_arity, subvalues_bot in H. inversion H.
  - rewrite<- length_subvalues_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Lemma valid_spath_app_last_get_constructor_not_zeoray {B V} `{IsValue : Value V} (S : state B V) p :
  arity (get_constructor (S.[p])) > 0 -> valid_spath S (p +++ [0]).
Proof.
  intro. apply valid_spath_app. split.
  - apply get_not_bot_valid_spath. intro G. rewrite G in H.
    rewrite <-length_subvalues_is_arity, subvalues_bot in H. inversion H.
  - rewrite<- length_subvalues_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Ltac solve_validity0 :=
  lazymatch goal with
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S ?p =>
      apply (valid_get_constructor_sget_not_bot S p);
      rewrite H;
      discriminate
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S (?p +++ [0]) =>
      simple apply valid_spath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : get_constructor (?S.[?p +++ ?q]) = _ |- valid_spath ?S (?p +++ ?q ++ [0]) =>
      rewrite (app_spath_vpath_assoc p q [0]);
      simple apply valid_spath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : ?S.[?p] = ?v |- valid_spath ?S ?p =>
      simple apply get_not_bot_valid_spath;
      rewrite H;
      discriminate
  | |- valid_spath (?S.[?p <- ?v]) (?p +++ ?q) =>
      simple apply sset_prefix_valid;
      solve_validity0
  | |- valid_spath (?S.[?p <- ?v]) ?q =>
      apply sset_not_prefix_valid; [ | solve_validity0]
  | |- valid_spath (?S ++ _) (length ?S, ?q) =>
      apply valid_spath_last;
      solve_validity0
  | |- valid_spath (?S ++ ?S') ?p =>
      simple apply valid_app_spath;
      solve_validity0
  | |- valid_spath ?S ?p => idtac

  (* Solving valid_vpath: *)
  | |- valid_vpath (?S.[?p]) ?q =>
      apply (valid_spath_app S p q);
      (* In case p is of the form p0 +++ p1, we rewrite (p0 +++ p1) +++ q into
         p0 +++ (p1 ++ q) *)
      repeat rewrite<-app_spath_vpath_assoc;
      solve_validity0
  | |- valid_vpath _ ([_] ++ _) =>
      econstructor; [reflexivity | solve_validity0]
  | H : get_constructor (?v.[[?p]]) = _ |- valid_vpath ?v (?p ++ [0]) =>
      simple apply valid_vpath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : ?v.[[?p]] = _ |- valid_vpath ?v ?p =>
      apply (valid_get_constructor_vget_not_bot v p);
      rewrite H;
      discriminate
  | H : get_constructor (?v.[[?p]]) = _ |- valid_vpath ?v ?p =>
      apply (valid_get_constructor_vget_not_bot v p);
      rewrite H;
      discriminate
  | |- valid_vpath ?v ?p => idtac
  end.
Hint Extern 0 (valid_spath _ _) => solve_validity0 : spath.
Ltac solve_validity := solve_validity0; eauto with spath.

(* Testing that I can automatically prove validity: *)
(* TODO: rewrite or delete. *)
(*
Goal forall (S : HLPL_plus_state) p l, S.[p] = ptr(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) p l, get_constructor (S.[p]) = locC(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) v w p q r l, disj p r -> ~strict_prefix q r -> S.[r] = loan^m(l)
  -> valid_spath (S.[p <- v].[q <- w]) r.
Proof. intros. solve_validity. Qed.
 *)

(* Automatically solve equality between two states that are sets of a state S, ie solves goals of
 * the form:
 * S.[p0 <- v0] ... .[pm <- vm] = S.[q0 <- w0] ... .[qn <- vn]
 *
 * Strategy: it's easy to compute values that are a get of a sequence of sets, i.e:
 * S.[p0 <- v0] ... .[pm <- vm] .[q]
 * This works when we know the relation between the state q we get and the states p0, ..., pk we
 * set.
 * Let's denote Sl := S.[p0 <- v0] ... .[pm <- vm] and Sr := S.[q0 <- w0] ... .[qn <- vn]. To prove
 * that Sl = Sr, we are going to prove that Sl.[q] = Sr.[q] for q = p0, ..., pm. For the spaths q
 * that are not prefix of p0, ..., pm, we are going to prove that Sl.[q] and Sr.[q] have the same
 * constructor.
 * Finally, we also need to prove that Sl and Sr have the binders, which is an easy consequence of
 * the fact that they are sets of the same state S.
 *)
Lemma prove_states_eq_3 {B V} `{IsValue : Value V} (S S' : state B V) p0 p1 p2 :
  (forall i, SOME c <- nth_error S i IN Some (fst c) = SOME c <- nth_error S' i IN Some (fst c)) ->
  S.[p0] = S'.[p0] -> (S.[p1] = S'.[p1]) -> (S.[p2] = S'.[p2]) ->
  (forall q, ~prefix p0 q -> ~prefix p1 q -> ~prefix p2 q ->
    get_constructor (S.[q]) = get_constructor (S'.[q])) ->
  S = S'.
Proof.
  intros. apply get_constructor_sget_ext; [assumption | ].
  intro q.
  destruct (decidable_prefix p0 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
  destruct (decidable_prefix p1 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
  destruct (decidable_prefix p2 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
   auto.
Qed.

Lemma prove_states_eq_2 {B V} `{IsValue : Value V} (S S' : state B V) p0 p1 :
  (forall i, SOME c <- nth_error S i IN Some (fst c) = SOME c <- nth_error S' i IN Some (fst c)) ->
  S.[p0] = S'.[p0] -> (S.[p1] = S'.[p1]) ->
  (forall q, ~prefix p0 q -> ~prefix p1 q ->
    get_constructor (S.[q]) = get_constructor (S'.[q])) ->
  S = S'.
Proof.
  intros. apply get_constructor_sget_ext; [assumption | ].
  intro q.
  destruct (decidable_prefix p0 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
  destruct (decidable_prefix p1 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
   auto.
Qed.

Ltac prove_states_eq :=
  let q := fresh "q" in
  (* autorewrite with spath; *)
  lazymatch goal with
  | |- ?S.[?p0 <- _].[?p1 <- _].[?p2 <- _] = ?S' =>
    simple apply (prove_states_eq_3 _ S' p0 p1 p2);
    intros;
    [rewrite !get_binder_sset; reflexivity | autorewrite with spath; try reflexivity..]
  | |- ?S.[?p0 <- _].[?p1 <- _] = ?S' =>
    simple apply (prove_states_eq_2 _ S' p0 p1);
    intros;
    [rewrite !get_binder_sset; reflexivity | autorewrite with spath; try reflexivity..]
  end.

(* Note: not really maintained. *)
(* A _comparison_ `C p q` between is one of those relation:
   - `p = q` or `p <> q`
   - `prefix p q` or `~prefix p q`
   - `strict_prefix p q` or `~strict_prefix p q`
   - `disj p q` or `~disj p q`
 *)
(* We are going to define a tactic called "reduce_comp" to assist the proof of comparisons between
 * two paths p and q, using comparisons in the hypotheses as much as possible.
 *
 * The key idea is that there are four possible "atomic" comparisons: p = q, strict_prefix p q,
 * strict_prefix q p and disj p q. These comparisons are atomic in the sense that for any p and q,
 * exactly one of those is true.
 *
 * Every comparison C p q is equivalent to a disjunction of atomic comparisons. By contraposition,
 * this means that every comparison C p q is equivalent to the conjuction of the negation of
 * atomas. For example:
 * - prefix p q <-> (p = q \/ strict_prefix p q) <-> (~strict_prefix q p /\ ~disj p q)
 * - ~prefix p q <-> (strict_prefix q p \/ ~disj p q) <-> (p <> q /\ ~strict_prefix p q)
 * - disj p q <-> disj p q <-> (p <> q /\ ~strict_prefix p q /\ ~strict_prefix q p)
 *
 * Thus, to prove a comparison C p q in the goal, reduce_comp works the following way:
 * - It generates the negative atomic relations necessary to prove C p q
 * - For each negative atomic relation, it tries to prove it automatically using the hypotheses.
 * The negative atomic relations that could not be automatically proven are left as subgoals. This
 * tactic never fails (as long as the goal is a comparison).
 *
 * Note: this tactic is not complete yet, more comparisons have to be added. It's also subject to
 * change.
 *)

Lemma prefix_if_equal_or_strict_prefix p q : prefix p q -> p = q \/ strict_prefix p q.
Proof.
  intros ([ | i r] & <-).
  - left. symmetry. apply app_spath_vpath_nil_r.
  - right. exists i, r. reflexivity.
Qed.

Lemma prove_not_prefix p q : p <> q -> ~strict_prefix p q -> ~prefix p q.
Proof. intros ? ? [ | ]%prefix_if_equal_or_strict_prefix; auto. Qed.
Hint Resolve prove_not_prefix : spath.

Lemma prove_disj p q : p <> q -> ~strict_prefix p q -> ~strict_prefix q p -> disj p q.
Proof. destruct (comparable_spaths p q); easy. Qed.

Ltac reduce_comp :=
  unfold not; (* Used to prove both negations of the form ~C p q and C p q -> False *)
  match goal with
  | |- prefix ?p ?q -> False => apply prove_not_prefix
  | |- disj ?p ?q => apply prove_disj
  end;
  eauto with spath.

(* Automatic rewriting. *)
(* Informally, here are the normal forms for the main objects: *)
(* Normal form for vpaths : p ++ (p ++ ...) *)
(* Normal form for spaths : p +++ (p ++ ...) *)
(* Normal form for values : v.[[p]].[[p <- v]].[[p <- v]] ... or S.[p].[[p <- v]].[[p <- v]] *)
(* Normal form for states : (S.[p <- v].[p <- v] ...), Anon |-> v *)

(* Simple simplifications: *)
Hint Rewrite app_nil_r : spath.
Lemma snd_pair [A B] (a : A) (b : B) : snd (a, b) = b. Proof. reflexivity. Qed.
Hint Rewrite snd_pair : spath.
Lemma snd_app v w : snd (v +++ w) = (snd v) ++ w. Proof. reflexivity. Qed.
Hint Rewrite snd_app : spath.

(* Re-parenthizing spaths and vpaths. *)
Hint Rewrite <- app_assoc : spath.
Hint Rewrite <- app_spath_vpath_assoc : spath.

(* When the term to rewrite contains a subterm of the form S.[q <- v].[v], it is not in normal
   form. We apply one of the following rewrite rules to commute the get and the set, or to
   remove the set operation entirely. *)
Hint Rewrite @constructor_sset_sget_not_prefix using eauto with spath; fail : spath.
Hint Rewrite @sset_sget_equal using solve_validity : spath.
Hint Rewrite @sset_sget_prefix using solve_validity : spath.
Hint Rewrite @sset_sget_prefix_right using solve_validity : spath.
Hint Rewrite @sset_sget_common_prefix using solve_validity : spath.
Hint Rewrite @sset_sget_disj using eauto with spath; fail : spath.

(* Idem for vpaths: *)
Hint Rewrite @vset_vget_equal using solve_validity : spath.
Hint Rewrite @vset_vget_prefix using solve_validity : spath.
Hint Rewrite @vset_vget_prefix_right using solve_validity : spath.

Hint Rewrite @constructor_vset_cons using discriminate : spath.

Hint Rewrite @sset_twice_prefix_right : spath.

(* When the term to rewrite contains a subterm of the form (S,, Anon |-> v).[p] or
   (S,, Anon |-> v).[p <- w], it is not in normal form.
   Depending on whether p is a path in S, or a path in the last binding Anon |-> v, we use
   one of the following rewrite rules. *)
Hint Rewrite @sset_app_state using solve_validity; fail : spath.
Hint Rewrite @sset_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite @sget_app_state using solve_validity; fail : spath.
Hint Rewrite @sget_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite<- @sget_app : spath.
Hint Rewrite<- @vget_app : spath.

(* Adding a hint to reslove a relation ~prefix p q using the facts that:
 * - S.[p] does not contain a constructor c.
 * - S.[q] starts by the constructor c.
 * To solve the second goal, we need to help auto. When we are using this lemma, there should be a
 * hypothesis S.[q] = v. We are giving the instruction to rewrite S.[q] into v, and then to reduce
 * the expression (get_value v) produced, so that it can be solved automatically.
 *)
Hint Extern 3 (~prefix ?p ?q) =>
  match goal with
  | H : ?S.[?q] = _ |- _ =>
    simple eapply not_value_contains_not_prefix; [ | rewrite H; cbn | solve_validity]
  end : spath.

(* Trying to prove that a value doesn't contain a constructor (ex: loan, loc, bot).
   This tactic tries to solve this by applying the relevant lemmas, and never fails. *)
Ltac prove_not_contains0 :=
  try assumption;
  match goal with
  | |- True => auto
  | |- not_state_contains ?P (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset;
      prove_not_contains0
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset_disj;
        [auto with spath; fail | prove_not_contains0]
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset;
       [ prove_not_contains0 | prove_not_contains0 | solve_validity0]
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget P S p H);
      solve_validity0
  | |- not_value_contains ?P (?v.[[?p <- ?w]]) =>
      simple apply not_value_contains_vset; prove_not_contains0
  | |- not_value_contains ?P (?S.[?p]) => idtac
  | |- not_value_contains ?P ?v =>
      simple apply not_value_contains_by_decomposition;
      [ | cbn; prove_not_contains0]
  | |- _ => idtac
  end.
Ltac prove_not_contains := prove_not_contains0; auto with spath.
