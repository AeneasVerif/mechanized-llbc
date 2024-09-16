Require Import List.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import OptionMonad.
Require Import base.

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
| CompEq (H : p = q)
| CompStrictPrefixLeft (H : strict_prefix p q)
| CompStrictPrefixRight (H : strict_prefix q p)
| CompDisj (H : disj p q).

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

Declare Scope GetSetPath_scope.
Open Scope GetSetPath_scope.

Class GetSetPath (V : Type) := {
  constructors : Type; (* a `constructor` type *)
  arity : constructors -> nat;
  subvalues : V -> list V;
  get_constructor : V -> constructors;
  fold : constructors -> list V -> V;
  bot : V;

  length_subvalues_is_arity v : length (subvalues v) = arity (get_constructor v);
  constructor_subvalues_inj v w :
    get_constructor v = get_constructor w -> subvalues v = subvalues w -> v = w;
  constructor_fold c vs : length vs = arity c -> get_constructor (fold c vs) = c;
  subvalues_fold c vs : length vs = arity c -> subvalues (fold c vs) = vs;
  subvalues_bot : subvalues bot = nil;
}.

Notation get_subval_or_bot w i :=
  (match nth_error (subvalues w) i with
    | Some u => u
    | None => bot
  end).
Definition vget {V} `{GetSetPath V} : vpath -> V -> V := 
  fold_left (fun w i => get_subval_or_bot w i).
Notation "v [[ p ]]" := (vget p v) (left associativity, at level 50) : GetSetPath_scope.

Fixpoint vset {V} `{GetSetPath V} (p : vpath) (w : V) (v : V) :=
  match p with
  | nil => w
  | i :: q => fold (get_constructor v) (map_nth (subvalues v) i (vset q w))
  end.
Notation "v [[ p <- w ]]" := (vset p w v) (left associativity, at level 50).

Notation get_val S i := (SOME c <- nth_error S i IN Some (snd c)).

Definition sget {V B} `{GetSetPath V} (p : spath) (S : list (B * V)) : V := 
  match get_val S (fst p) with
  | Some v => v[[snd p]]
  | None => bot
  end.
Notation "v [ p ]" := (sget p v) (left associativity, at level 50) : GetSetPath_scope.

Definition sset {V B} `{GetSetPath V} (p : spath) (v : V) (S : list (B * V)) :=
  map_nth S (fst p) (fun c => (fst c, (snd c)[[snd p <- v]])).
Notation "S [ p <- v ]" := (sset p v S) (left associativity, at level 50).

Section GetSetPath.
  Context {V : Type}.
  Context {get_set_path : GetSetPath V}.
  Context {B : Type}.

  Lemma vget_app v p q : v[[p ++ q]] = v[[p]][[q]].
  Proof. unfold vget. apply fold_left_app. Qed.

  (* A vpath p is valid with regards to a value v if we can follow its indices down the value v
   * interpreted as a tree. *)
  Inductive valid_vpath : V -> vpath -> Prop :=
    | valid_nil v : valid_vpath v nil
    | valid_cons v i p w :
        nth_error (subvalues v) i = Some w -> valid_vpath w p -> valid_vpath v (i :: p).

  Lemma valid_vpath_app v p q :
    valid_vpath v (p ++ q) <-> valid_vpath v p /\ valid_vpath (v[[p]]) q.
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
    exists q i r, p = q ++ i :: r /\ valid_vpath v q /\ nth_error (subvalues (v[[q]])) i = None.

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

  Lemma vget_bot p : bot[[p]] = bot.
  Proof.
     induction p.
    - reflexivity.
    - cbn. rewrite subvalues_bot, nth_error_nil. assumption.
  Qed.
  (* The vget function is defined in such a way that for any invalid path p, v[[p]] = bot.
   * This relies on two design choices:
   * - For a value v, if the index i is the index of a subvalue, then v[[i :: r]] = bot[[r]].
   * - `bot` has 0 subvalues (`subvalues_bot` axiom), so bot[[r]] = r.
   *)
  Lemma vget_invalid v p : invalid_vpath v p -> v[[p]] = bot.
  Proof. intros (q & i & r & -> & _ & H). rewrite vget_app. cbn. rewrite H. apply vget_bot. Qed.

  (* A useful criterion for validity: if v[[p]] <> bot, then p is a valid path for v.
     This is going to be the main way of proving validity. *)
  Corollary get_not_bot_valid_vpath v p (H : v[[p]] <> bot) : valid_vpath v p.
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
    get_constructor (v[[i :: p <- w]]) = get_constructor v.
  Proof. apply constructor_fold. rewrite map_nth_length. apply length_subvalues_is_arity. Qed.

  Lemma subvalues_vset_cons v i p w :
    subvalues (v[[i :: p <- w]]) = map_nth (subvalues v) i (vset p w).
  Proof. apply subvalues_fold. rewrite map_nth_length. apply length_subvalues_is_arity. Qed.

  Lemma vget_cons v i p : v[[i :: p]] = (get_subval_or_bot v i)[[p]].
  Proof. reflexivity. Qed.

  Lemma set_get_vprefix v w p q (H : valid_vpath v p) :
    v[[p ++ q <- w]][[p]] = v[[p]][[q <- w]].
  Proof.
    induction H as [ | v i p u subval_v_i valid_u_p IH].
    - reflexivity.
    - rewrite vget_cons, <-app_comm_cons, subvalues_vset_cons, nth_error_map_nth_eq.
      simplify_option.
  Qed.

  Corollary get_set_vequal v w p : valid_vpath v p -> v[[p <- w]][[p]] = w.
  Proof. intro. rewrite<- (app_nil_r p) at 2. rewrite set_get_vprefix; auto. Qed.

  Lemma set_valid v w p (H : valid_vpath v p) : valid_vpath (v[[p <- w]]) p.
  Proof.
    induction H as [ | ? ? ? ? H].
    - constructor.
    - econstructor.
      + rewrite subvalues_vset_cons, nth_error_map_nth_eq, H. reflexivity.
      + assumption.
  Qed.

  Corollary get_set_prefix_right v w p q (H : valid_vpath v p) :
    v[[p <- w]][[p ++ q]] = w[[q]].
  Proof. rewrite vget_app, get_set_vequal; try apply set_valid; auto. Qed.

  Lemma _vset_app_split v p q w (H : valid_vpath v p) :
    v[[p ++ q <- w]] = v[[p <- v[[p]][[q <- w]]]].
  Proof.
    induction H.
    - reflexivity.
    - cbn. f_equal. eapply map_nth_equal_Some; simplify_option.
  Qed.

  (* Note: the validity hypothesis could be removed. *)
  Lemma vset_same v p (H : valid_vpath v p) : v[[p <- v[[p]]]] = v.
  Proof.
    induction H.
    - reflexivity.
    - apply constructor_subvalues_inj.
      + apply constructor_vset_cons.
      + rewrite subvalues_vset_cons. eapply map_nth_invariant; simplify_option.
  Qed.

  (* vset is defined in such a way that v[[p <- w]] is v when p is invalid.
   * To understand why, take v[[i :: r <- w]] when i >= length (subvalues v):
   * - The constructor of v[[i :: r <- w]] is the same constructor as v.
   * - The vset function is recursively applied in the i-th subvalue of v. But because the list
   *   of subvalues does not contained an i-th subvalue, because of the definiton of map_nth, the
   *   list of subvalues of v[[i :: r <- w]] is the same as for v.
   * This trick allows us to omit validity hypotheses in some lemmas.
   *)
  Lemma vset_invalid v p w : invalid_vpath v p -> v[[p <- w]] = v.
  Proof.
    intros (q & i & r & -> & valid_q & H). rewrite<- (vset_same v q) at 2 by assumption.
    rewrite _vset_app_split by assumption. f_equal.
    apply constructor_subvalues_inj.
    - apply constructor_vset_cons.
    - rewrite subvalues_vset_cons. apply map_nth_equal_None. assumption.
  Qed.

  Lemma set_get_disj_aux v i j p q w :
    i <> j -> v[[i :: p <- w]][[j :: q]] = v[[j :: q]].
  Proof. intro. rewrite vget_cons, subvalues_vset_cons, nth_error_map_nth_neq; auto. Qed.

  Lemma set_get_vdisj v w p q (Hvdisj : vdisj p q) :
    v[[p <- w]][[q]] = v[[q]].
  Proof.
    destruct (valid_or_invalid p v) as [H | ].
    - destruct Hvdisj as (r & p' & q' & i & j & diff & -> & ->).
      apply valid_vpath_app in H. destruct H as [H _].
      rewrite !vget_app, set_get_vprefix by assumption. apply set_get_disj_aux. assumption.
    - rewrite vset_invalid; auto.
  Qed.

  Lemma vset_twice_equal p x y : forall v, v[[p <- x]][[p <- y]] = v[[p <- y]].
  Proof.
    induction p; intro v.
    - reflexivity.
    - apply constructor_subvalues_inj.
      + rewrite !constructor_vset_cons. reflexivity.
      + rewrite !subvalues_vset_cons, map_nth_compose. apply map_nth_equiv. assumption.
  Qed.

  (* Now the we proved that v[[p <- w]] = v when p in invalid, we can remove the validity
   * hypothesis from the theorem _vset_app_split. *)
  Lemma vset_app_split v p q w : v[[p ++ q <- w]] = v[[p <- v[[p]][[q <- w]]]].
  Proof.
    destruct (valid_or_invalid p v) as [ | ].
    - apply _vset_app_split. assumption.
    - rewrite !vset_invalid; try auto. apply invalid_prefix. assumption.
  Qed.

  Lemma vset_twice_prefix_right v p q x y : vprefix q p -> v[[p <- x]][[q <- y]] = v[[q <- y]].
  Proof. intros (? & <-). rewrite vset_app_split, vset_twice_equal. reflexivity. Qed.

  Lemma vset_twice_prefix_left v p q x y : v[[p <- x]][[p ++ q <- y]] = v[[p <- x[[q <- y]]]].
  Proof.
    rewrite vset_app_split, vset_twice_equal. destruct (valid_or_invalid p v).
    - rewrite get_set_vequal; auto.
    - rewrite !vset_invalid; auto.
  Qed.

  Lemma vset_twice_disj_commute_aux v p q i j x y :
    i <> j -> v[[i :: p <- x]][[j :: q <- y]] = v[[j :: q <- y]][[i :: p <- x]].
  Proof.
    intro. apply constructor_subvalues_inj.
    - rewrite !constructor_vset_cons. reflexivity.
    - rewrite !subvalues_vset_cons. apply map_nth_neq_commute. assumption.
  Qed.

  Lemma vset_twice_disj_commute v p q x y :
    vdisj p q -> v[[p <- x]][[q <- y]] = v[[q <- y]][[p <- x]].
  Proof.
    intros (r & p' & q' & i & j & ? & -> & ->).
    rewrite !(vset_app_split v). rewrite !vset_twice_prefix_left.
    rewrite vset_twice_disj_commute_aux; auto.
  Qed.

  (* Similar theory for getting and setting values in a state. *)
  Lemma vset_app (S : list (B * V)) p q : S[p +++ q] = S[p][[q]].
  Proof.
    unfold sget, app_spath_vpath. cbn. destruct (get_val S (fst p)).
    - apply vget_app.
    - rewrite vget_bot. reflexivity.
  Qed.

  Definition valid_spath (S : list (B * V)) (p : spath) :=
    exists v, get_val S (fst p) = Some v /\ valid_vpath v (snd p).

  Lemma valid_spath_app (S : list (B * V)) p q :
    valid_spath S (p +++ q) <-> valid_spath S p /\ valid_vpath (S[p]) q.
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

  Lemma get_not_bot_valid_spath (S : list (B * V)) p (H : S[p] <> bot) : valid_spath S p.
  Proof.
    unfold sget in H. destruct (get_val S (fst p)) as [v | ] eqn:EQN.
    - exists v. split. { assumption. } apply get_not_bot_valid_vpath. assumption.
    - exfalso. apply H. reflexivity.
  Qed.

  Lemma sset_sget_prefix (S : list (B * V)) v p q :
    valid_spath S p -> S[p +++ q <- v][p] = S[p][[q <- v]].
  Proof.
    intros (w & Hget & Hvalid). unfold sget, sset.
    rewrite nth_error_map_nth_eq. simplify_option. rewrite set_get_vprefix; auto.
  Qed.

  Lemma sset_sget_equal S p v : valid_spath S p -> S[p <- v][p] = v.
  Proof.
    intro. rewrite <-(app_spath_vpath_nil_r p) at 2.
    rewrite sset_sget_prefix; auto.
  Qed.

  Lemma sset_valid (S : list (B * V)) p v : valid_spath S p -> valid_spath (S[p <- v]) p.
  Proof.
    intros (w & ? & ?). exists (w[[snd p <- v]]). split.
    - unfold sset. rewrite nth_error_map_nth_eq. simplify_option.
    - apply set_valid. assumption.
  Qed.

  Lemma sget_sset_prefix_right S v p q (H : valid_spath S p) :
    S[p <- v][p +++ q] = v[[q]].
  Proof. rewrite vset_app, sset_sget_equal; auto. Qed.

  (* During the proof of this theorem, we implicitely use the fact that if the spath p is
   * invalid, then the spath q is invalid, and S[q <- w] = S. *)
  Lemma constructor_sset_sget_strict_prefix (S : list (B * V)) p q w :
    strict_prefix p q -> get_constructor (S[q <- w][p]) = get_constructor (S[p]).
  Proof.
    intros (i & r & <-).
    destruct (nth_error S (fst p)) as [bv | ] eqn:EQN.
    - destruct (valid_or_invalid (snd p) (snd bv)).
      + rewrite sset_sget_prefix.
        * apply constructor_vset_cons.
        * exists (snd bv). simplify_option.
      + unfold sget, sset. rewrite nth_error_map_nth_eq. simplify_option.
        rewrite vset_invalid; try auto. apply invalid_prefix. assumption.
    - unfold sget, sset. rewrite nth_error_map_nth_eq. simplify_option.
  Qed.

  Lemma sset_sget_disj (S : list (B * V)) p v q : disj p q -> S[p <- v][q] = S[q].
  Proof.
    unfold sset, sget. intros [ | (<- & Hdisj)].
    - rewrite nth_error_map_nth_neq by assumption. reflexivity.
    - rewrite nth_error_map_nth_eq. autodestruct. intro. apply set_get_vdisj. assumption.
  Qed.

  Lemma sset_twice_prefix_right (S : list (B * V)) p q x y :
    prefix q p -> S[p <- x][q <- y] = S[q <- y].
  Proof.
    intros (r & <-). unfold sset. cbn. rewrite map_nth_compose. cbn. apply map_nth_equiv.
    intro. rewrite vset_twice_prefix_right.
    - reflexivity.
    - exists r. reflexivity.
  Qed.

  Corollary sset_twice_equal (S : list (B * V)) p x y : S[p <- x][p <- y] = S[p <- y].
  Proof. apply sset_twice_prefix_right. exists nil. apply app_spath_vpath_nil_r. Qed.

  Lemma sset_twice_preix_left (S : list (B * V)) p q x y :
    S[p <- x][p +++ q <- y] = S[p <- x[[q <- y]]].
  Proof.
    unfold sset. cbn. rewrite map_nth_compose. cbn. apply map_nth_equiv.
    intro. rewrite vset_twice_prefix_left. reflexivity.
  Qed.

  Lemma sset_twice_disj_commute (S : list (B * V)) p q v w :
    disj p q -> S[p <- v][q <- w] = S[q <- w][p <- v].
  Proof.
    unfold sset. intros [ | (<- & ?)].
    - apply map_nth_neq_commute. assumption.
    - rewrite !map_nth_compose. apply map_nth_equiv. intro. cbn. f_equal.
      apply vset_twice_disj_commute. assumption.
  Qed.

  Context `{EqDecBinder : EqDec B}.

  Fixpoint find_binder (S : list (B * V)) (b : B) : option nat := match S with
  | nil => None
  | (b', _) :: S' => if eq_dec b b' then Some 0 else SOME i <- find_binder S' b IN Some (1 + i)
  end.

  Lemma find_binder_prop S b :
    forall i, find_binder S b = Some i -> exists v, nth_error S i = Some (b, v).
  Proof. induction S as [ | bv S' IH]; simplify_option. congruence. Qed.

  Corollary find_binder_valid S b i (H : find_binder S b = Some i) : valid_spath S (i, nil).
  Proof.
    apply find_binder_prop in H. destruct H as (v & ?). exists v. split.
    - cbn. rewrite H. reflexivity.
    - apply valid_nil.
  Qed.
End GetSetPath.

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
