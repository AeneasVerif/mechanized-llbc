Require Import List.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Local Open Scope option_monad_scope.

(* As a hint database, "spath" is used to solve common goals, in particular, proving comparisons
 * between paths.
 * As a rewriting database, "spath" is used to reduce computations on paths, values and states, and
 * to put them in normal form. *)
Create HintDb spath.

(* This is a hint database used to reduce weight computations. *)
Create HintDb weight.

Coercion Z.of_nat : nat >-> Z.

(* Paths, prefixes and disjointness *)

(* A vpath ("value path") is the data structure used to uniquely represent nodes in a tree. The
 * integers in the list are the indices of the children we take, going down from the root to the
 * node in the tree. It is called "vpath" because it will mostly be used by values in
 * intermediate languages between LLBC# and HLPL.
 * The vpaths are used to:
 * - Get the child at a node.
 * - Set a child at a node.
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
Hint Immediate vdisj_symmetric : spath.

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
Hint Resolve strict_prefix_is_prefix : spath.

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
Hint Resolve not_prefix_left_strict_prefix_right : spath.

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
Proof. intros ? ? ? (? & <-) (? & <-). rewrite<- app_assoc. eexists. reflexivity. Qed.

Global Instance prefix_trans : Transitive prefix.
Proof.
  intros ? ? ? (? & <-) (? & <-). rewrite<- app_spath_vpath_assoc. eexists. reflexivity.
Qed.

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

Lemma prefix_and_strict_prefix_implies_strict_prefix p q r :
  prefix p q -> strict_prefix q r -> strict_prefix p r.
Proof.
  intros (x & <-) (i & y & <-). rewrite<- app_spath_vpath_assoc.
  destruct (x ++ i :: y) eqn:?.
  - exfalso. eapply app_cons_not_nil. symmetry. eassumption.
  - eexists _, _. reflexivity.
Qed.
Hint Resolve prefix_and_strict_prefix_implies_strict_prefix : spath.

Lemma prefix_trans' p q r : prefix (p +++ q) r -> prefix p r.
Proof. transitivity (p +++ q); [ | assumption]. exists q. reflexivity. Qed.

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

Lemma prefix_of_disj_implies_not_prefix p q r : prefix p q -> disj q r -> ~prefix r p.
Proof.
  intros ? ? ?. assert (prefix r q) by (transitivity p; assumption).
  eapply not_prefix_disj; [symmetry | ]; eassumption.
Qed.
Hint Resolve prefix_of_disj_implies_not_prefix : spath.

(* Automatically solving a comparison C p q using the hypotheses. *)
Hint Resolve-> disj_common_prefix : spath.
Hint Resolve<- disj_common_prefix : spath.
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
Hint Resolve prefix_trans' : spath.
Hint Resolve prefix_and_neq_implies_strict_prefix : spath.
Hint Resolve<- not_strict_prefix_app_last : spath.

Declare Scope GetSetPath_scope.
Open Scope GetSetPath_scope.

Class Value (V : Type) := {
  nodes : Type; (* a `node` type *)
  arity : nodes -> nat;
  children : V -> list V;
  get_node : V -> nodes;
  fold_value : nodes -> list V -> V;
  (* The sum of some quantity for each node of the tree. *)
  total_weight : (nodes -> nat) -> V -> nat;
  bot : V;

  length_children_is_arity v : length (children v) = arity (get_node v);
  get_nodes_children_inj v w (eq_node : get_node v = get_node w)
                                (eq_children : children v = children w) : v = w;
  get_node_fold_value c vs (H : length vs = arity c) : get_node (fold_value c vs) = c;
  children_fold_value c vs (H : length vs = arity c) : children (fold_value c vs) = vs;
  children_bot : children bot = nil;
  total_weight_prop weight v :
    total_weight weight v = sum (map (total_weight weight) (children v)) + (weight (get_node v))
}.

Notation get_subval_or_bot w i :=
  (match nth_error (children w) i with
    | Some u => u
    | None => bot
  end).
Definition vget {V} `{Value V} : vpath -> V -> V :=
  fold_left (fun w i => get_subval_or_bot w i).
Notation "v .[[ p ]]" := (vget p v) (left associativity, at level 50) : GetSetPath_scope.

Fixpoint vset {V} `{Value V} (p : vpath) (w : V) (v : V) :=
  match p with
  | nil => w
  | i :: q => fold_value (get_node v) (map_nth (children v) i (vset q w))
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
  Context `{IsValue : Value V}.
  Context {B : Type}.

  Lemma vget_app v p q : v.[[p ++ q]] = v.[[p]].[[q]].
  Proof. unfold vget. apply fold_left_app. Qed.

  (* A vpath p is valid with regards to a value v if we can follow its indices down the value v
   * interpreted as a tree. *)
  Inductive valid_vpath : V -> vpath -> Prop :=
    | valid_nil v : valid_vpath v nil
    | valid_cons v i p w :
        nth_error (children v) i = Some w -> valid_vpath w p -> valid_vpath v (i :: p).

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
    exists q i r, p = q ++ i :: r /\ valid_vpath v q /\ nth_error (children (v.[[q]])) i = None.

  Lemma valid_or_invalid p : forall v, valid_vpath v p \/ invalid_vpath v p.
  Proof.
    induction p as [ | i p IHp].
    - left. constructor.
    - intro v. destruct (nth_error (children v) i) as [w | ] eqn:EQN.
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
    - cbn. rewrite children_bot, nth_error_nil. assumption.
  Qed.
  (* The vget function is defined in such a way that for any invalid path p, v.[[p]] = bot.
   * This relies on two design choices:
   * - For a value v, if the index i is the index of a child, then v.[[i :: r]] = bot.[[r]].
   * - `bot` has 0 children (`children_bot` axiom), so bot.[[r]] = r.
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

  Lemma get_node_vset_cons v p w :
    p <> [] -> get_node (v.[[p <- w]]) = get_node v.
  Proof.
    intro. destruct p; [congruence | ].
    apply get_node_fold_value. rewrite map_nth_length. apply length_children_is_arity.
  Qed.

  Lemma children_vset_cons v i p w :
    children (v.[[i :: p <- w]]) = map_nth (children v) i (vset p w).
  Proof. apply children_fold_value. rewrite map_nth_length. apply length_children_is_arity. Qed.

  Lemma vget_cons v i p : v.[[i :: p]] = (get_subval_or_bot v i).[[p]].
  Proof. reflexivity. Qed.

  Lemma vstrict_prefix_one_child v p q (H : length (children (v.[[p]])) = 1) :
    vstrict_prefix p q -> valid_vpath v q -> vprefix (p ++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_vpath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
      inversion G. destruct (nth_error (children (v.[[p]]))); easy. }
    exists r. rewrite<- app_assoc. reflexivity.
  Qed.

  Corollary not_vprefix_one_child v p q :
    length (children (v.[[p]])) = 1 -> valid_vpath v q -> ~vprefix (p ++ [0]) q
    -> ~vstrict_prefix p q.
  Proof. intros ? ? H ?. eapply H, vstrict_prefix_one_child; eassumption. Qed.

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
    - rewrite vget_cons, <-app_comm_cons, children_vset_cons, nth_error_map_nth_eq.
      simplify_option.
  Qed.

  Corollary vset_vget_equal v w p : valid_vpath v p -> v.[[p <- w]].[[p]] = w.
  Proof. intro. rewrite<- (app_nil_r p) at 2. rewrite vset_vget_prefix; auto. Qed.

  Lemma vset_same_valid v w p (H : valid_vpath v p) : valid_vpath (v.[[p <- w]]) p.
  Proof.
    induction H as [ | ? ? ? ? H].
    - constructor.
    - econstructor.
      + rewrite children_vset_cons, nth_error_map_nth_eq, H. reflexivity.
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
    - apply get_nodes_children_inj.
      + apply get_node_vset_cons. discriminate.
      + rewrite children_vset_cons. eapply map_nth_invariant; simplify_option.
  Qed.

  (* vset is defined in such a way that v.[[p <- w]] is v when p is invalid.
   * To understand why, take v.[[i :: r <- w]] when i >= length (children v):
   * - The node of v.[[i :: r <- w]] is the same node as v.
   * - The vset function is recursively applied in the i-th child of v. But because the list
   *   of children does not contained an i-th child, because of the definiton of map_nth, the
   *   list of children of v.[[i :: r <- w]] is the same as for v.
   * This trick allows us to omit validity hypotheses in some lemmas.
   *)
  Lemma vset_invalid v p w : invalid_vpath v p -> v.[[p <- w]] = v.
  Proof.
    intros (q & i & r & -> & valid_q & H). rewrite<- (_vset_same v q) at 2 by assumption.
    rewrite _vset_app_split by assumption. f_equal.
    apply get_nodes_children_inj.
    - apply get_node_vset_cons. discriminate.
    - rewrite children_vset_cons. apply map_nth_equal_None. assumption.
  Qed.

  Lemma vset_vget_disj_aux v i j p q w :
    i <> j -> v.[[i :: p <- w]].[[j :: q]] = v.[[j :: q]].
  Proof. intro. rewrite vget_cons, children_vset_cons, nth_error_map_nth_neq; auto. Qed.

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
    - apply get_nodes_children_inj.
      + rewrite !get_node_vset_cons by discriminate. reflexivity.
      + rewrite !children_vset_cons, map_nth_compose. apply map_nth_equiv. assumption.
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
    intro. apply get_nodes_children_inj.
    - rewrite !get_node_vset_cons by discriminate. reflexivity.
    - rewrite !children_vset_cons. apply map_nth_neq_commute. assumption.
  Qed.

  Lemma vset_twice_disj_commute v p q x y :
    vdisj p q -> v.[[p <- x]].[[q <- y]] = v.[[q <- y]].[[p <- x]].
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->).
    rewrite !(vset_app_split v). rewrite !vset_twice_prefix_left.
    rewrite vset_twice_disj_commute_aux; auto.
  Qed.

  Lemma get_arity_0 v i p : length (children v) = 1 -> v.[[i :: p]] <> bot -> i = 0.
  Proof.
    intros H G. apply get_not_bot_valid_vpath in G. inversion G.
    apply length_1_is_singleton in H. destruct H as (? & H). rewrite H in *. destruct i.
    - reflexivity.
    - rewrite nth_error_cons, nth_error_nil in *. simplify_option.
  Qed.

  Notation size v := (total_weight (fun _ => 1) v).
  Lemma size_decreasing (v w : V) i : nth_error (children v) i = Some w -> size w < size v.
  Proof.
    intro H. rewrite (total_weight_prop _ v).
    apply map_nth_error with (f := total_weight (fun _ => 1)) in H.
    apply sum_ge_element in H.
    lia.
  Qed.

  Hint Resolve nth_error_length : core.

  Lemma length_sset (S : state B V) p v : length (S.[p <- v]) = length S.
  Proof. apply map_nth_length. Qed.

  Context (weight : nodes -> nat).

  (* The theorems of weight of sets are the following:
     weight v.[[p <- w]] = weight v - weight v.[[p]] + weight.[[w]]
     weight S.[p <- v] = weight S - weight S.[p] + weight v
     As you can notice, these involve a substraction. Proving (in)equalities with natural
     substraction is awkard, because is requires proving at each time that the weight of v (resp. S)
     is greater than the weight of v.[[p]] (resp. S.[p]).
     This is why we are going to go on relatives to avoid these complications. *)
  Notation vweight := (total_weight weight).

  Lemma total_weight_vget v p w
    (H : valid_vpath v p) :
    Z.of_nat (vweight (v.[[p <- w]])) = (vweight v - vweight (v.[[p]]) + vweight w)%Z.
  Proof.
    induction H as [ | u i p v].
    - cbn. lia.
    - rewrite (total_weight_prop _ u).
      rewrite (total_weight_prop _ (u.[[i :: p <- w]])).
      rewrite get_node_vset_cons by discriminate.
      rewrite children_vset_cons.
      erewrite map_map_nth by eassumption.
      rewrite Nat2Z.inj_add.
      erewrite sum_map_nth by (erewrite map_nth_error by eassumption; reflexivity).
      replace (u.[[i :: p]]) with (v.[[p]]) by (cbn; rewrite H; reflexivity).
      lia.
  Qed.

  Lemma weight_vget_le v p (H : valid_vpath v p) : vweight (v.[[p]]) <= vweight v.
  Proof.
    induction H as [ | ? ? ? ? H].
    - reflexivity.
    - rewrite (total_weight_prop _ v). cbn. rewrite H.
      apply (map_nth_error vweight) in H. apply sum_ge_element in H. lia.
  Qed.

  Lemma weight_arity_0 (v : V) :
    arity (get_node v) = 0 -> total_weight weight v = weight (get_node v).
  Proof.
    intros H. rewrite total_weight_prop.
    rewrite<- length_children_is_arity in H. apply length_zero_iff_nil in H. rewrite H.
    reflexivity.
  Qed.

  Lemma weight_arity_1 (v : V) (H : arity (get_node v) = 1) :
    total_weight weight v = weight (get_node v) + total_weight weight (v.[[ [0] ]]).
  Proof.
    rewrite total_weight_prop. cbn.
    rewrite<- length_children_is_arity in H. apply length_1_is_singleton in H.
    destruct H as (? & ->). cbn. lia.
  Qed.

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

  Lemma strict_prefix_one_child S p q (H : length (children (S.[p])) = 1) :
    strict_prefix p q -> valid_spath S q -> prefix (p +++ [0]) q.
  Proof.
    intros (i & r & <-) (_ & G)%valid_spath_app.
    assert (i = 0) as ->.
    { apply PeanoNat.Nat.lt_1_r. rewrite<- H. inversion G. eauto.  }
    exists r. rewrite<- app_spath_vpath_assoc. reflexivity.
  Qed.

  Corollary not_prefix_one_child S p q :
    length (children (S.[p])) = 1 -> valid_spath S q -> ~prefix (p +++ [0]) q -> ~strict_prefix p q.
  Proof. intros ? ? H ?. eapply H, strict_prefix_one_child; eassumption. Qed.

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

  Lemma get_node_vset_vget_strict_prefix v p q w :
    vstrict_prefix p q -> get_node (v.[[q <- w]].[[p]]) = get_node (v.[[p]]).
  Proof.
     intros (i & r & <-). destruct (valid_or_invalid p v).
     - rewrite vset_vget_prefix by assumption. apply get_node_vset_cons. discriminate.
     - assert (invalid_vpath v (p ++ i :: r)) by now apply invalid_prefix.
       now rewrite vset_invalid.
  Qed.

  (* During the proof of this theorem, we implicitely use the fact that if the spath p is
   * invalid, then the spath q is invalid, and S.[q <- w] = S. *)
  Lemma get_node_sset_sget_strict_prefix (S : state B V) p q w :
    strict_prefix p q -> get_node (S.[q <- w].[p]) = get_node (S.[p]).
  Proof.
    unfold sset, sget. intro H.
    assert (fst p = fst q) as ->. { destruct H as (? & ? & <-). reflexivity. }
    rewrite nth_error_map_nth_eq. simplify_option.
    intro. apply get_node_vset_vget_strict_prefix.
    destruct H as (? & ? & <-). eexists _, _. reflexivity.
  Qed.

  Lemma get_node_vset_vget_not_prefix v p q w (H : ~vprefix q p) :
    get_node (v.[[q <- w]].[[p]]) = get_node (v.[[p]]).
  Proof.
    destruct (comparable_vpaths p q) as [<- | | (? & ? & ?) | ].
    - destruct H. exists nil. apply app_nil_r. (* TODO: reflexivity lemma? *)
    - apply get_node_vset_vget_strict_prefix. assumption.
    - destruct H. eexists. eassumption. (* TODO: vstrict_prefix -> vprefix ? *)
    - rewrite vset_vget_disj; [reflexivity | symmetry; assumption].
  Qed.

  Lemma get_node_sset_sget_not_prefix (S : state B V) p q w (H : ~prefix q p) :
    get_node (S.[q <- w].[p]) = get_node (S.[p]).
  Proof.
    destruct (comparable_spaths p q) as [<- | | | ].
    - destruct H. reflexivity.
    - apply get_node_sset_sget_strict_prefix. assumption.
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

  Lemma sset_twice_prefix_left (S : state B V) p q x y :
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
    econstructor; [ | eassumption]. rewrite children_vset_cons, nth_error_map_nth_neq; auto.
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
      all: apply nth_error_None; rewrite length_app, Nat.add_1_r; assumption.
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
      rewrite length_app in G. cbn in G. lia.
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
  arity (get_node (S .[ p])) = 0 -> valid_spath S q -> ~strict_prefix p q.
  Proof.
    intros H valid_q (i & r & <-). apply valid_spath_app in valid_q.
    destruct valid_q as (_ & valid_i_r). inversion valid_i_r.
    rewrite<- length_children_is_arity in H. apply length_zero_iff_nil in H.
    rewrite H, nth_error_nil in * |-. discriminate.
  Qed.

  (* Setting up the definitions for judgements like "loan \notin v" or
     "l is fresh". *)
  Definition not_value_contains (P : nodes -> Prop) (v : V) :=
    forall p, valid_vpath v p -> ~P (get_node (v.[[p]])).

  Definition not_state_contains (P : nodes -> Prop) (S : state B V) :=
    forall p, valid_spath S p -> ~P (get_node (S.[p])).

  Definition not_contains_outer (is_mut_borrow P : nodes -> Prop) v :=
    forall p, P (get_node (v.[[p]]))
    -> exists q, vstrict_prefix q p /\ is_mut_borrow (get_node (v.[[q]])).

  Lemma not_value_contains_not_prefix P (S : state B V) p q
    (Hnot_contains : not_value_contains P (S.[p])) (HP : P (get_node (S.[q]))) (Hvalid : valid_spath S q) :
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
    - rewrite get_node_vset_vget_not_prefix by assumption. apply H.
      eapply vset_not_prefix_valid_rev; [ | eassumption].
      intros ?%vstrict_prefix_is_vprefix. auto.
  Qed.

  Lemma weight_non_zero v :
    vweight v > 0 -> exists p, valid_vpath v p /\ weight (get_node (v.[[p]])) > 0.
  Proof.
    remember (size v) as n eqn:Heqn. revert v Heqn.
    induction n as [n IH] using lt_wf_ind. intros v -> weight_non_zero.
    rewrite total_weight_prop in weight_non_zero.
    destruct (weight (get_node v)) eqn:?.
    - rewrite Nat.add_0_r in weight_non_zero. apply sum_non_zero in weight_non_zero.
      destruct weight_non_zero as (i & ? & H). rewrite nth_error_map in H.
      destruct (nth_error (children v) i) as [w | ] eqn:G; [ | discriminate].
      injection H as ?.
      edestruct IH as (p & ? & ?).
      + eapply size_decreasing. eassumption.
      + reflexivity.
      + lia.
      + exists (i :: p). split.
        * econstructor; eassumption.
        * cbn. rewrite G. assumption.
    - exists []. cbn. split; [constructor | lia].
  Qed.

  Lemma not_value_contains_weight (P : nodes -> Prop) v
    (H : forall c, weight c > 0 -> P c) :
    not_value_contains P v -> vweight v = 0.
  Proof.
    intro not_contains. destruct (vweight v) eqn:?; [reflexivity | ].
    exfalso. assert (non_zero: vweight v > 0) by lia.
    apply weight_non_zero in non_zero. destruct non_zero as (p & ? & ?).
    eapply not_contains; eauto.
  Qed.

  Lemma weight_zero_not_value_contains (P : nodes -> Prop) v
    (H : forall c, P c -> weight c > 0) :
    vweight v = 0 -> not_value_contains P v.
  Proof.
    intros ? p valid_p P_p. specialize (H _ P_p). pose proof (weight_vget_le _ _ valid_p) as G.
    rewrite (total_weight_prop _ (v.[[p]])) in G. lia.
  Qed.

  (* There is at most one path that satisfies a predicate P. *)
  Definition value_at_most_one P v :=
    forall p q, valid_vpath v p -> valid_vpath v q ->
                P (get_node (v.[[p]])) -> P (get_node (v.[[q]])) ->
                p = q.

  Definition vpath_unique  P v p :=
    valid_vpath v p /\ P (get_node (v.[[p]])) /\
    forall q, valid_vpath v q -> P (get_node (v.[[q]])) -> p = q.

  Lemma weight_at_most_one v :
    vweight v = 1 -> exists p, vpath_unique (fun c => weight c > 0) v p.
  Proof.
    intro weight_1.
    assert (vweight v > 0) as (p & valid_p & P_p)%weight_non_zero by lia.
    exists p. repeat split; [assumption.. | ].
    induction valid_p as [ | v i p w H valid_p IH].
      rewrite total_weight_prop in weight_1.
      intros q valid_q. destruct valid_q as [ | ? ? ? ? H valid_rec]; [reflexivity | ].
      cbn in *. rewrite H.
      apply (map_nth_error vweight) in H. apply sum_ge_element in H.
      pose proof (weight_vget_le _ _ valid_rec) as G.
      rewrite total_weight_prop in G. lia.
    - rewrite total_weight_prop in weight_1.
      cbn in P_p. rewrite H in P_p.
      pose proof (weight_vget_le _ _ valid_p) as weight_w_p.
      rewrite total_weight_prop in weight_w_p.
      pose proof (map_nth_error vweight _ _ H) as weight_children.
      apply sum_ge_element in weight_children.
      intros ? valid_q. destruct valid_q as [ | v j q w' G valid_q].
      + cbn. lia.
      + intros P_q. cbn in P_q. rewrite G in P_q. replace j with i in *.
        * replace w' with w in * by congruence.
          f_equal. apply IH; [ | assumption..]. lia.
        * pose proof (weight_vget_le _ _ valid_q) as weight_w'_q.
          rewrite total_weight_prop in weight_w'_q.
          apply (map_nth_error vweight) in H, G.
          eapply sum_le_one; [ | exact H | exact G | | ]; lia.
  Qed.

  Lemma weight_one_at_most_one_vpath v
    (weight_le_1 : forall c, weight c <= 1) :
    value_at_most_one (fun c => weight c > 0) v -> vweight v <= 1.
  Proof.
    remember (size v) as n eqn:Heqn. revert v Heqn.
    induction n as [n IH] using lt_wf_ind. intros v -> at_most_one.
    rewrite total_weight_prop.
    pose proof (weight_le_1 (get_node v)) as [-> | weight_node]%Nat.le_1_r.
    - rewrite Nat.add_0_r. apply sum_unique_one.
      + intros i x H. rewrite nth_error_map in H.
        destruct (nth_error (children v) i) as [w | ] eqn:Hw; [ | discriminate].
        injection H as <-.
        eapply IH.
        * eapply size_decreasing. exact Hw.
        * reflexivity.
        * intros p q valid_p valid_q Hp Hq.
          injection (at_most_one (i :: p) (i :: q)).
          -- auto.
          -- econstructor; eassumption.
          -- econstructor; eassumption.
          -- cbn. rewrite Hw. assumption.
          -- cbn. rewrite Hw. assumption.
      + intros i j. rewrite !nth_error_map. intros Hi Hj.
        destruct (nth_error (children v) i) as [wi | ] eqn:Hwi; [ | discriminate].
        destruct (nth_error (children v) j) as [wj | ] eqn:Hwj; [ | discriminate].
        injection Hi as ?. injection Hj as ?.
        destruct (weight_non_zero wi) as (p & ? & ?); [lia | ].
        destruct (weight_non_zero wj) as (q & ? & ?); [lia | ].
        assert (i :: p = j :: q) as eq_path; [ | injection eq_path; auto].
        apply at_most_one.
        * econstructor; eassumption.
        * econstructor; eassumption.
        * cbn. rewrite Hwi. assumption.
        * cbn. rewrite Hwj. assumption.
    - assert (sum (map vweight (children v)) = 0); [ | lia].
      apply sum_zero. intros i H.
      rewrite nth_error_map.
      rewrite length_map in H. apply nth_error_Some' in H.
      destruct H as (w & H). rewrite H. cbn. f_equal.
      replace w with (v.[[ [i] ]]) by (cbn; rewrite H; reflexivity).
      eapply not_value_contains_weight; [intros ? G; exact G | ].
      intros p q. rewrite<- vget_app.
      intros ?. specialize (at_most_one ([i] ++ p) []).
      discriminate at_most_one.
      + apply valid_vpath_app. split; repeat (econstructor || eassumption).
      + constructor.
      + assumption.
      + cbn. lia.
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
    - rewrite get_node_sset_sget_not_prefix by assumption.
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
    - rewrite get_node_sset_sget_not_prefix by assumption. rewrite sget_app. apply not_in_Sp.
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
    children v = [] -> ~P (get_node v) -> not_value_contains P v.
  Proof.
    intros H ? p valid_p. destruct valid_p; [assumption | ].
    rewrite H, nth_error_nil in * |-. discriminate.
  Qed.

  Lemma not_value_contains_unary P v w :
    children v = [w] -> ~P (get_node v) -> not_value_contains P w -> not_value_contains P v.
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

  Lemma not_contains_outer_sset_no_contains is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v -> not_value_contains P w
    -> (forall v, P v -> v <> get_node bot)
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv Hw ?. destruct (valid_or_invalid p v).
    - intros q Hq. destruct (decidable_vprefix p q) as [(r & <-) | not_prefix].
      + exfalso.
        rewrite vset_vget_prefix_right in Hq by assumption. eapply Hw; [ | eassumption].
        apply get_not_bot_valid_vpath. intro wr. apply (H _ Hq). rewrite wr. reflexivity.
      + destruct (Hv q) as (r & ? & ?).
        * rewrite get_node_vset_vget_not_prefix in Hq; assumption.
        * exists r. split; [assumption | ]. rewrite get_node_vset_vget_not_prefix.
          assumption. intro. apply not_prefix. transitivity r; auto with spath.
    - rewrite vset_invalid by assumption. assumption.
  Qed.

  Lemma not_contains_outer_sset_in_borrow is_mut_borrow P v p w :
    not_contains_outer is_mut_borrow P v
    -> (exists q, vstrict_prefix q p /\ is_mut_borrow (get_node (v.[[q]])))
    -> not_contains_outer is_mut_borrow P (v.[[p <- w]]).
  Proof.
    intros Hv (q & H & ?). destruct (valid_or_invalid p v).
    - intros r Hr. destruct (decidable_vprefix p r) as [(r' & <-) | not_prefix].
      + exists q.
        split.
        * destruct H as (i & ? & <-). eexists i, _. rewrite<- app_assoc. reflexivity.
        * rewrite get_node_vset_vget_not_prefix by auto with spath. assumption.
      + destruct (Hv r) as (q' & ? & ?).
        * rewrite get_node_vset_vget_not_prefix in Hr; assumption.
        * exists q'. split; [assumption | ]. rewrite get_node_vset_vget_not_prefix.
          assumption. intro. apply not_prefix. transitivity q'; auto with spath.
    - rewrite vset_invalid by assumption. assumption.
  Qed.

  Definition sweight (S : state B V) := sum (map (fun bv => vweight (snd bv)) S).

  Lemma sweight_sset S p v (H : valid_spath S p) :
    Z.of_nat (sweight (S.[p <- v])) = (sweight S - vweight (S.[p]) + vweight v)%Z.
  Proof.
    destruct H as (w & H & G).
    simplify_option; intro H.
    unfold sweight, sset. erewrite map_map_nth; [ | exact H].
    erewrite sum_map_nth; [ | rewrite nth_error_map, H; reflexivity].
    cbn. rewrite total_weight_vget by assumption.
    unfold sget. rewrite H. lia.
  Qed.

  Lemma weight_sget_le S p : valid_spath S p -> vweight (S.[p]) <= sweight S.
  Proof.
    intros (w & H & G). unfold sget. rewrite H.
    unfold sweight.
    simplify_option. intro H.
    etransitivity.
    2: { eapply sum_ge_element with (n := fst p). rewrite nth_error_map, H. reflexivity. }
    apply weight_vget_le. assumption.
  Qed.

  Corollary weight_sget_node_le S p : valid_spath S p -> weight (get_node (S.[p])) <= sweight S.
  Proof. intros H%weight_sget_le. rewrite total_weight_prop in H. lia. Qed.

  Lemma sweight_add_anon S b v : sweight (S,, b |-> v) = sweight S + vweight v.
  Proof. unfold sweight. rewrite map_app, sum_app. cbn. lia. Qed.

  Lemma sweight_non_zero S : sweight S > 0 ->
    exists p, valid_spath S p /\ weight (get_node (S.[p])) > 0.
  Proof.
    intros (i & ? & H)%sum_non_zero. rewrite nth_error_map in H.
    destruct (nth_error S i) as [bv | ] eqn:Hbv; [ | discriminate].
    injection H as ?.
    assert (vweight (snd bv) > 0) as (p & ? & ?)%weight_non_zero by lia.
    exists (i, p). split.
    - unfold valid_spath. exists (snd bv). cbn. rewrite Hbv. auto.
    - unfold sget. cbn. rewrite Hbv. assumption.
  Qed.

  Lemma not_state_contains_implies_weight_zero P S (H : forall c, weight c > 0 -> P c) :
    not_state_contains P S -> sweight S = 0.
  Proof.
    intros not_contains. assert (~(sweight S > 0)); [ | lia].
    intros (? & ? & ?)%sweight_non_zero. eapply not_contains; eauto.
  Qed.
End GetSetPath.

Section StateUniqueConstructor.
  Context {V : Type}.
  Context `{IsValue : Value V}.
  Context `{ConstructorEqDec : EqDec nodes}.
  Context {B : Type}.
  Context `{EqDecBinder : EqDec B}.

  Definition at_most_one_node c (S : state B V) :=
    forall p q, get_node (S.[p]) = c -> get_node (S.[q]) = c -> p = q.

  Definition at_most_one_node_alt c (S : state B V) :=
    exists p, forall q, get_node (S.[q]) = c -> p = q.

  Lemma not_contains_implies_at_most_one_node c S :
    c <> get_node bot -> not_state_contains (eq c) S -> at_most_one_node c S.
  Proof.
    intros not_bot not_contains p ? Hp. exfalso. eapply not_contains; [ | eauto].
    apply get_not_bot_valid_spath. congruence.
  Qed.

  Lemma at_most_one_node_alt_implies_at_most_one_node c S :
    at_most_one_node_alt c S -> at_most_one_node c S.
  Proof.
    intros (p & H) q r Hq Hr. rewrite <-(H _ Hq), <-(H _ Hr). reflexivity.
  Qed.

  Lemma unique_node_implies_at_most_one_node c S :
    c <> get_node bot -> not_state_contains (eq c) S -> at_most_one_node c S.
  Proof.
    intros not_bot not_contains p ? Hp. exfalso. eapply not_contains; [ | eauto].
    apply get_not_bot_valid_spath. congruence.
  Qed.

  Lemma decide_at_most_one_node c S (not_bot : c <> get_node bot) :
    at_most_one_node c S <-> sweight (indicator c) S <= 1.
  Proof.
    split.
    - intros H. apply sum_unique_one.
      + intros i ? G. rewrite nth_error_map in G.
        destruct (nth_error S i) as [bv | ] eqn:get_S_i; [ | discriminate].
        injection G as <-. apply weight_one_at_most_one_vpath.
        * intro d. unfold indicator. destruct (eq_dec c d); lia.
        * intros p q _ _ Hp Hq.
          unfold indicator in *.
          destruct (eq_dec c (get_node ((snd bv).[[p]]))); [ | lia].
          destruct (eq_dec c (get_node ((snd bv).[[q]]))); [ | lia].
          assert ((i, p) = (i, q)) as eq_spath; [ | inversion eq_spath; auto].
          apply H; unfold sget; cbn; rewrite get_S_i; auto.
      + intros i j Hi Hj. rewrite nth_error_map in *.
        destruct (nth_error S i) as [bvi | ] eqn:get_S_i; [ | discriminate].
        destruct (nth_error S j) as [bvj | ] eqn:get_S_j; [ | discriminate].
        injection Hi as ?. injection Hj as ?.
        assert (total_weight (indicator c) (snd bvi) > 0) as (p & ? & ?)%weight_non_zero by lia.
        assert (total_weight (indicator c) (snd bvj) > 0) as (q & ? & ?)%weight_non_zero by lia.
        unfold indicator in *.
        destruct (eq_dec c (get_node ((snd bvi).[[p]]))); [ | lia].
        destruct (eq_dec c (get_node ((snd bvj).[[q]]))); [ | lia].
        assert ((i, p) = (j, q)) as eq_spath; [ | inversion eq_spath; auto].
        apply H; unfold sget; cbn; rewrite ?get_S_i, ?get_S_j; auto.
    - intros [H | H]%Nat.le_1_r.
      + apply not_contains_implies_at_most_one_node; [exact not_bot | ].
        intros p valid_p HSp.
        pose proof (weight_sget_node_le (indicator c) _ _ valid_p) as G.
        rewrite <-HSp, indicator_same in G. lia.
      + assert (sweight (indicator c) S > 0)
          as (i & ? & Hi)%sum_non_zero
          by lia.
        rewrite nth_error_map in Hi.
        destruct (nth_error S i) as [bvi | ] eqn:Hbvi; [ | discriminate].
        injection Hi as Hi.
        assert (total_weight (indicator c) (snd bvi) <= 1).
        { unfold sweight in H.
          etransitivity; [eapply sum_ge_element | rewrite H; reflexivity].
          rewrite nth_error_map, Hbvi. reflexivity. }
        assert (total_weight (indicator c) (snd bvi) = 1)
          as (p & (valid_p & ? & unique_p))%weight_at_most_one
          by lia.
        apply at_most_one_node_alt_implies_at_most_one_node.
        exists (i, p). intros (j & q) G.
        unfold sget in G. cbn in G.
        destruct (nth_error S j) as [bvj | ] eqn:Hbvj; [ | congruence].
        assert (valid_q : valid_vpath (snd bvj) q).
        { apply get_not_bot_valid_vpath. congruence. }
        replace j with i in *.
        * f_equal. replace bvj with bvi in * by congruence.
          apply unique_p; [assumption | rewrite G, indicator_same; constructor].
        * assert (sweight (indicator c) S <= 1) as unique_i by lia.
          eapply sum_le_one with (i := i) (j := j).
          -- exact unique_i.
          -- rewrite nth_error_map, Hbvi. reflexivity.
          -- rewrite nth_error_map, Hbvj. reflexivity.
          -- pose proof (weight_vget_le (indicator c) _ _ valid_p) as le_get_p.
             rewrite total_weight_prop in le_get_p. lia.
          -- pose proof (weight_vget_le (indicator c) _ _ valid_q) as le_get_q.
             rewrite total_weight_prop, G, indicator_same in le_get_q. lia.
  Qed.
End StateUniqueConstructor.

(* Automatically solving comparisons using environment information. *)
Hint Resolve strict_prefix_one_child : spath.
Hint Resolve not_vprefix_one_child : spath.
Hint Resolve not_prefix_one_child : spath. (* TODO: delete? *)
Hint Extern 5 (length (children ?v) = _) =>
  match goal with
  | H : get_node (?S.[?p]) = _ |- _ =>
      rewrite length_children_is_arity, H; reflexivity
  end : spath.
Hint Extern 5 (~strict_prefix ?p ?q) =>
  match goal with
  | H : get_node (?S.[?p]) = _ |- _ =>
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
 * - Search for a proof that the node of S.[p] is not bot in the hypotheses.
 *)
Lemma valid_get_node_sget_not_bot {B V} `{IsValue : Value V} (S : state B V) p :
  get_node (S.[p]) <> get_node bot -> valid_spath S p.
Proof. intros G. apply get_not_bot_valid_spath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_get_node_vget_not_bot {V} `{IsValue : Value V} v p :
  get_node (v.[[p]]) <> get_node bot -> valid_vpath v p.
Proof. intros G. apply get_not_bot_valid_vpath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_vpath_app_last_get_node_not_zeoray {V} `{IsValue : Value V} v p :
  arity (get_node (v.[[p]])) > 0 -> valid_vpath v (p ++ [0]).
Proof.
  intro. apply valid_vpath_app. split.
  - apply get_not_bot_valid_vpath. intro G. rewrite G in H.
    rewrite <-length_children_is_arity, children_bot in H. inversion H.
  - rewrite<- length_children_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Lemma valid_spath_app_last_get_node_not_zeoray {B V} `{IsValue : Value V} (S : state B V) p :
  arity (get_node (S.[p])) > 0 -> valid_spath S (p +++ [0]).
Proof.
  intro. apply valid_spath_app. split.
  - apply get_not_bot_valid_spath. intro G. rewrite G in H.
    rewrite <-length_children_is_arity, children_bot in H. inversion H.
  - rewrite<- length_children_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Ltac validity0 :=
  lazymatch goal with
  | H : get_node (?S.[?p]) = _ |- valid_spath ?S ?p =>
      apply (valid_get_node_sget_not_bot S p);
      rewrite H;
      discriminate
  | H : get_node (?S.[?p]) = _ |- valid_spath ?S (?p +++ [0]) =>
      simple apply valid_spath_app_last_get_node_not_zeoray;
      rewrite H;
      constructor
  | H : get_node (?S.[?p +++ ?q]) = _ |- valid_spath ?S (?p +++ ?q ++ [0]) =>
      rewrite (app_spath_vpath_assoc p q [0]);
      simple apply valid_spath_app_last_get_node_not_zeoray;
      rewrite H;
      constructor
  | H : get_node (?S.[?p +++ ?q ++ ?r]) = _ |- valid_spath ?S (?p +++ ?q ++ ?r ++ [0]) =>
      rewrite (app_assoc q r [0]);
      rewrite (app_spath_vpath_assoc p (q ++ r) [0]);
      simple apply valid_spath_app_last_get_node_not_zeoray;
      rewrite H;
      constructor
  | H : ?S.[?p] = ?v |- valid_spath ?S ?p =>
      simple apply get_not_bot_valid_spath;
      rewrite H;
      discriminate
  | |- valid_spath (?S.[?p <- ?v]) (?p +++ ?q) =>
      simple apply sset_prefix_valid;
      validity0
  | |- valid_spath (?S.[?p <- ?v]) ?q =>
      apply sset_not_prefix_valid; [ | validity0]
  | |- valid_spath (?S ++ _) (length ?S, ?q) =>
      apply valid_spath_last;
      validity0
  | |- valid_spath (?S ++ ?S') ?p =>
      simple apply valid_app_spath;
      validity0
  | |- valid_spath ?S ?p => idtac

  (* Solving valid_vpath: *)
  | |- valid_vpath (?S.[?p]) ?q =>
      apply (valid_spath_app S p q);
      (* In case p is of the form p0 +++ p1, we rewrite (p0 +++ p1) +++ q into
         p0 +++ (p1 ++ q) *)
      validity0
  | |- valid_vpath _ ([_] ++ _) =>
      econstructor; [reflexivity | validity0]
  | H : get_node (?v.[[?p]]) = _ |- valid_vpath ?v (?p ++ [0]) =>
      simple apply valid_vpath_app_last_get_node_not_zeoray;
      rewrite H;
      constructor
  | H : ?v.[[?p]] = _ |- valid_vpath ?v ?p =>
      apply (valid_get_node_vget_not_bot v p);
      rewrite H;
      discriminate
  | H : get_node (?v.[[?p]]) = _ |- valid_vpath ?v ?p =>
      apply (valid_get_node_vget_not_bot v p);
      rewrite H;
      discriminate
  (* TODO: maybe use a more general forme ?v.[[?q <- _]] ?p, at the condition that ?q
     is not a strict prefix of p. This would require an extra lemma. *)
  | |- valid_vpath (?v.[[?p ++ _ <- _]]) ?p =>
      simple apply vset_prefix_right_valid; validity0
  | |- valid_vpath ?v ?p => idtac
  end.
Hint Extern 0 (valid_spath _ _) =>
  repeat rewrite <-app_spath_vpath_assoc;
  validity0 : spath.
Ltac validity :=
  repeat rewrite <-app_spath_vpath_assoc;
  validity0;
  eauto with spath.

(* Testing that I can automatically prove validity: *)
(* TODO: rewrite or delete. *)
(*
Goal forall (S : HLPL_plus_state) p l, S.[p] = ptr(l) -> valid_spath S p.
Proof. intros. validity. Qed.

Goal forall (S : HLPL_plus_state) p l, get_node (S.[p]) = locC(l) -> valid_spath S p.
Proof. intros. validity. Qed.

Goal forall (S : HLPL_plus_state) v w p q r l, disj p r -> ~strict_prefix q r -> S.[r] = loan^m(l)
  -> valid_spath (S.[p <- v].[q <- w]) r.
Proof. intros. validity. Qed.
 *)

(* When we want to prove an equality of the form Sl = Sr.[p <- v] or Sl = Sr.[p +++ q <- v],
   we perform commutations so that all of the writes [p <- v] or [p +++ r <- v] are at the end.
 *)
Ltac commute_ssets :=
  lazymatch goal with
  | |- _ = _.[?p +++ ?q <- _] =>
    lazymatch goal with
    | |- context [ _.[p <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ p) by eauto with spath
    end
  | |- _ = _.[?p <- _] =>
    lazymatch goal with
    | |- context [ _.[p <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ p) by eauto with spath
    | |- context [ _.[p +++ ?q <- _].[_ <- _] ] =>
      rewrite (sset_twice_disj_commute _ (p +++ q)) by eauto with spath
    end
  end
.

(* Automatically solve equality between two states that are sets of a state S, ie solves goals of
 * the form:
 * S.[p0 <- v0] ... .[pm <- vm] = S.[q0 <- w0] ... .[qn <- vn]
 *)
Ltac states_eq :=
  autorewrite with spath;
  (* In case we want to prove equality between pairs (v, S), we prove the equality between the
   * values by reflexivity, and leave as a goal the proof of equality between the states. *)
  lazymatch goal with
  | |- (_, _) = (_, _) => refine (proj2 (pair_equal_spec _ _ _ _) _); split; [reflexivity | ]
  | _ => idtac
  end;
  repeat (repeat (commute_ssets; autorewrite with spath); f_equal)
.

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
Hint Rewrite @get_node_sset_sget_not_prefix using eauto with spath; fail : spath.
Hint Rewrite @sset_sget_equal using validity : spath.
Hint Rewrite @sset_sget_prefix using validity : spath.
Hint Rewrite @sset_sget_prefix_right using validity : spath.
Hint Rewrite @sset_sget_common_prefix using validity : spath.
Hint Rewrite @sset_sget_disj using eauto with spath; fail : spath.

(* Idem for vpaths: *)
Hint Rewrite @vset_vget_equal using validity : spath.
Hint Rewrite @vset_vget_prefix using validity : spath.
Hint Rewrite @vset_vget_prefix_right using validity : spath.

Hint Rewrite @get_node_vset_cons using discriminate : spath.

Hint Rewrite @sset_twice_equal : spath.
Hint Rewrite @sset_twice_prefix_left : spath.
Hint Rewrite @sset_twice_prefix_right : spath.

(* When the term to rewrite contains a subterm of the form (S,, Anon |-> v).[p] or
   (S,, Anon |-> v).[p <- w], it is not in normal form.
   Depending on whether p is a path in S, or a path in the last binding Anon |-> v, we use
   one of the following rewrite rules. *)
Hint Rewrite @sset_app_state using validity; fail : spath.
Hint Rewrite @sset_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite @sget_app_state using validity; fail : spath.
Hint Rewrite @sget_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite<- @sget_app : spath.
Hint Rewrite<- @vget_app : spath.

(* Adding a hint to reslove a relation ~prefix p q using the facts that:
 * - S.[p] does not contain a node c.
 * - S.[q] starts by the node c.
 * To solve the second goal, we need to help auto. When we are using this lemma, there should be a
 * hypothesis S.[q] = v. We are giving the instruction to rewrite S.[q] into v, and then to reduce
 * the expression (get_value v) produced, so that it can be solved automatically.
 *)
Hint Extern 3 (~prefix ?p ?q) =>
  match goal with
  | H : get_node (?S.[?q]) = _ |- _ =>
    simple eapply not_value_contains_not_prefix; [ | rewrite H; cbn | validity]
  end : spath.

(* Trying to prove that a value doesn't contain a node (ex: loan, loc, bot).
   This tactic tries to solve this by applying the relevant lemmas, and never fails. *)
Ltac not_contains0 :=
  try assumption;
  match goal with
  | |- True => auto
  | |- not_state_contains ?P (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset;
      not_contains0
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset_disj;
        [auto with spath; fail | not_contains0]
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      simple apply not_value_contains_sset;
       [ not_contains0 | not_contains0 | validity0]
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget _ S p H);
      validity0
  | |- not_value_contains ?P (?v.[[?p <- ?w]]) =>
      simple apply not_value_contains_vset; not_contains0
  | |- not_value_contains ?P (?S.[?p]) => idtac
  | |- not_value_contains ?P ?v =>
      simple apply not_value_contains_zeroary; [reflexivity | ]
  | |- not_value_contains ?P ?v =>
      simple eapply not_value_contains_unary; [reflexivity | | not_contains0]
  | |- _ => idtac
  end.
Ltac not_contains := not_contains0; auto with spath.

(* Populating the "weight" rewrite database: *)
(* These hints turn operations on naturals onto operations on relatives, so to rewrite
 * sweight_sset: *)
Hint Rewrite Nat2Z.inj_add : weight.
Hint Rewrite Nat2Z.inj_le : weight.
Hint Rewrite Nat2Z.inj_lt : weight.
Hint Rewrite Nat2Z.inj_gt : weight.

Hint Rewrite @sweight_sset using validity : weight.
Hint Rewrite @sweight_add_anon : weight.

(* When applying twice sweight_sset on a state of the form S.[p <- v].[q <- w], we end up
   with value S.[p <- v].[q], that we reduce using sset_sget_disj: *)
Hint Rewrite @sset_sget_disj using eauto with spath : weight.
Hint Rewrite<- @sget_app : weight.

Hint Rewrite @indicator_same : weight.
Hint Rewrite @indicator_diff using congruence : weight.
Hint Rewrite @indicator_eq using auto; fail : weight.
