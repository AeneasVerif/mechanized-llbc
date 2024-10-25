Require Import List.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.
Require Import Arith.
Import ListNotations.

Local Open Scope option_monad_scope.

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

Lemma strict_prefix_irrefl p : ~strict_prefix p p.
Proof.
  intros (? & ? & ?). apply (f_equal snd) in H. unfold app_spath_vpath in H.
  apply app_same_nil in H. inversion H.
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

Local Instance : Reflexive vprefix.
Proof. intro p. exists nil. apply app_nil_r. Qed.

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

Lemma decidable_spath_eq (p q : spath) : p = q \/ p <> q.
Admitted.

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

Lemma not_strict_prefix_nil (p : spath) i : ~strict_prefix p (i, nil).
Proof.
  intros (? & ? & H). apply (f_equal snd) in H. eapply app_cons_not_nil. symmetry. exact H.
Qed.

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

  Lemma constructor_vset_cons v i p w :
    get_constructor (v.[[i :: p <- w]]) = get_constructor v.
  Proof. apply get_constructor_fold_value. rewrite map_nth_length. apply length_subvalues_is_arity. Qed.

  Lemma subvalues_vset_cons v i p w :
    subvalues (v.[[i :: p <- w]]) = map_nth (subvalues v) i (vset p w).
  Proof. apply subvalues_fold_value. rewrite map_nth_length. apply length_subvalues_is_arity. Qed.

  Lemma vget_cons v i p : v.[[i :: p]] = (get_subval_or_bot v i).[[p]].
  Proof. reflexivity. Qed.

  (* All of the lemmas to reduce an expression of the form v.[[q <- w]].[[p]], depending on the
   * following cases:
   * - p = q
   * - p is a prefix of q
   * - q is a prefix of p
   * - p and q are disjoint
   *)
  Lemma vget_vset_prefix v w p q (H : valid_vpath v p) :
    v.[[p ++ q <- w]].[[p]] = v.[[p]].[[q <- w]].
  Proof.
    induction H as [ | v i p u subval_v_i valid_u_p IH].
    - reflexivity.
    - rewrite vget_cons, <-app_comm_cons, subvalues_vset_cons, nth_error_map_nth_eq.
      simplify_option.
  Qed.

  Corollary vget_vset_equal v w p : valid_vpath v p -> v.[[p <- w]].[[p]] = w.
  Proof. intro. rewrite<- (app_nil_r p) at 2. rewrite vget_vset_prefix; auto. Qed.

  Lemma vset_same_valid v w p (H : valid_vpath v p) : valid_vpath (v.[[p <- w]]) p.
  Proof.
    induction H as [ | ? ? ? ? H].
    - constructor.
    - econstructor.
      + rewrite subvalues_vset_cons, nth_error_map_nth_eq, H. reflexivity.
      + assumption.
  Qed.

  Corollary vget_vset_prefix_right v w p q (H : valid_vpath v p) :
    v.[[p <- w]].[[p ++ q]] = w.[[q]].
  Proof. rewrite vget_app, vget_vset_equal; try apply vset_same_valid; auto. Qed.

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
      + apply constructor_vset_cons.
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
    - apply constructor_vset_cons.
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
      rewrite !vget_app, vget_vset_prefix by assumption. apply vset_vget_disj_aux. assumption.
    - rewrite vset_invalid; auto.
  Qed.

  Lemma vset_twice_equal p x y : forall v, v.[[p <- x]].[[p <- y]] = v.[[p <- y]].
  Proof.
    induction p; intro v.
    - reflexivity.
    - apply constructor_subvalues_inj.
      + rewrite !constructor_vset_cons. reflexivity.
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
    - rewrite vget_vset_equal; auto.
    - rewrite !vset_invalid; auto.
  Qed.

  Lemma vset_twice_disj_commute_aux v p q i j x y :
    i <> j -> v.[[i :: p <- x]].[[j :: q <- y]] = v.[[j :: q <- y]].[[i :: p <- x]].
  Proof.
    intro. apply constructor_subvalues_inj.
    - rewrite !constructor_vset_cons. reflexivity.
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

  Lemma sset_sget_prefix (S : state B V) v p q :
    valid_spath S p -> S.[p +++ q <- v].[p] = S.[p].[[q <- v]].
  Proof.
    intros (w & Hget & Hvalid). unfold sget, sset.
    rewrite nth_error_map_nth_eq. simplify_option. rewrite vget_vset_prefix; auto.
  Qed.

  Lemma sset_sget_equal S p v : valid_spath S p -> S.[p <- v].[p] = v.
  Proof.
    intro. rewrite <-(app_spath_vpath_nil_r p) at 2.
    rewrite sset_sget_prefix; auto.
  Qed.

  Lemma sset_sget_prefix_right S v p q (H : valid_spath S p) :
    S.[p <- v].[p +++ q] = v.[[q]].
  Proof. rewrite sget_app, sset_sget_equal; auto. Qed.

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
     - rewrite vget_vset_prefix by assumption. apply constructor_vset_cons.
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
    - rewrite vget_vset_prefix by assumption. apply vset_disj_valid_aux; assumption.
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

  Lemma sget_app_state (S S' : state B V) p : valid_spath S p -> (S ++ S').[p] = S.[p].
  Proof.
    intros (w & (? & _)). unfold sget. rewrite nth_error_app1. { reflexivity. }
    apply nth_error_Some. simplify_option.
  Qed.

  (* TODO: switch directions? *)
  Lemma sset_app_state (S S' : state B V) p v :
    valid_spath S p -> S.[p <- v] ++ S' = (S ++ S').[p <- v].
  Proof.
    intros (w & (? & ?)). unfold sset. apply nth_error_ext. intro i.
    destruct (Nat.lt_ge_cases i (length S)) as [ | ].
    - destruct (Nat.eq_dec (fst p) i) as [-> | ].
      + rewrite nth_error_map_nth_eq.
        rewrite !nth_error_app1 by (try rewrite map_nth_length; assumption).
        apply nth_error_map_nth_eq.
      + rewrite nth_error_map_nth_neq by assumption.
        rewrite !nth_error_app1 by (try rewrite map_nth_length; assumption).
        apply nth_error_map_nth_neq. assumption.
    - rewrite nth_error_map_nth_neq.
      { rewrite !nth_error_app2; try rewrite map_nth_length; auto. }
      apply Nat.lt_neq. unfold lt. transitivity (length S); try assumption.
      apply nth_error_Some. simplify_option.
  Qed.

  (* TODO: switch directions? *)
  Lemma sset_app_last_state (S : state B V) b p v w :
    fst p = length S -> S,, b |-> v.[[snd p <- w]] = (S,, b |-> v).[p <- w].
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
  Lemma disj_spath_to_last S p q : valid_spath S p -> fst q = length S -> disj p q.
  Proof.
    destruct q. cbn. intros (? & ? & _) ->. left. apply Nat.lt_neq. apply nth_error_Some.
    destruct (nth_error S (fst p)); easy.
  Qed.

  Lemma valid_app_spath S S' p : valid_spath S p -> valid_spath (S ++ S') p.
  Proof.
    intros (v & ? & ?). exists v. split; [ | assumption].
    rewrite nth_error_app1 by (apply nth_error_Some; simplify_option). assumption.
  Qed.

  Lemma valid_spath_last S b v p : valid_vpath v p -> valid_spath (S,, b |-> v) (length S, p).
  Proof.
    intro. exists v. split; [ | assumption]. rewrite nth_error_app2, Nat.sub_diag; reflexivity.
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

  Lemma get_nil_prefix_right S p q (H : subvalues (S.[p]) = nil) (valid_w : valid_spath S q) :
    prefix p q -> q = p.
  Proof.
    intros (r & <-). destruct r.
    - apply app_spath_vpath_nil_r.
    - exfalso. rewrite valid_spath_app in valid_w. destruct valid_w as [_ valid_queue].
      inversion valid_queue. rewrite H, nth_error_nil in *. simplify_option.
  Qed.
End GetSetPath.
