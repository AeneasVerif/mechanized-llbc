(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*     Xavier Leroy and Damien Doligez, INRIA Paris-Rocquencourt       *)
(*     Andrew W. Appel, Princeton University                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

From chamois Require Import OptionMonad.
Require Import Coqlib.
Require Import Impure.ImpHCons.
Import Notations.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Local Open Scope option_monad_scope.
Local Open Scope impure.

(* Auxiliary definition for [Tree.combine_mostdef] *)

Inductive p_mostdef [A : Type] (p : A -> A -> A -> Prop): option A -> option A -> option A -> Prop :=
 | PMostDef2  (x0 x1 x : A) (P : p x0 x1 x) : p_mostdef p (Some x0) (Some x1) (Some x)
 | PMostDef1L (x : A) : p_mostdef p (Some x) None (Some x)
 | PMostDef1R (x : A) : p_mostdef p None (Some x) (Some x)
 | PMostDef0  : p_mostdef p None None None.

(** * The abstract signatures of trees *)

Module Type TREE.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Parameter remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Axiom gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Axiom grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Axiom gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Axiom grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Extensional equality between trees. *)
  Parameter beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Axiom beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).

  (** Applying a function to all data of a tree. *)
  Parameter map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Parameter map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Parameter combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Axiom gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).

  (** A combine version that may fail, parametrized by a most defined function. *)
  Parameter combine_mostdef:
    forall (A: Type), (A -> A -> option A) -> t A -> t A -> option (t A).
  Parameter f_mostdef:
    forall (A: Type), (A -> A -> option A) -> option A -> option A -> option (option A).
  (* When the combination succeeds and the mostdef function is ok for an index [i],
     then the combined tree must be defined for [i]. *)
  Axiom gcombine_mostdef:
    forall (A: Type) (mostdef: A -> A -> option A) (m1 m2 m3: t A) (a: option A) (i: elt),
    combine_mostdef mostdef m1 m2 = Some m3 ->
    f_mostdef mostdef (get i m1) (get i m2) = Some a ->
    get i m3 = a.
  (* When the combination fails, the mostdef function can not succeed for all index [i]. *)
  Axiom fcombine_mostdef:
    forall (A: Type) (mostdef: A -> A -> option A) (m1 m2: t A),
    combine_mostdef mostdef m1 m2 = None ->
    (forall i a1 a2, (get i m1) = Some a1 -> (get i m2) = Some a2 ->
    mostdef a1 a2 <> None) ->
    False.
  (* When the combination succeeds and the combined tree is defined for an index [i],
     then the combine function of both source trees on that index [i] must be defined. *)
  Axiom gcombine_mostdef_ok:
    forall (A: Type) (mostdef: A -> A -> option A) (m1 m2 m3: t A) (i: elt) (a: A),
    combine_mostdef mostdef m1 m2 = Some m3 ->
    get i m3 = Some a ->
    f_mostdef mostdef (get i m1) (get i m2) = Some (Some a).
  (* Any combination with the empty tree as right source
     is valid and preserving the original left source tree. *)
  Axiom gcombine_mostdef_only_l:
    forall (A: Type) (mostdef: A -> A -> option A) (m1: t A),
     combine_mostdef mostdef m1 (empty A) = Some m1.
  (* When the combination succeeds, if we know an index [i] on which the combined tree is
     undefined, then both source trees are undefined on [i]. *)
  Axiom gcombine_mostdef_none_rev:
    forall (A: Type) (mostdef: A -> A -> option A) (m1 m2 m3: t A) (i: elt),
    combine_mostdef mostdef m1 m2 = Some m3 ->
    get i m3 = None ->
    get i m1 = None /\ get i m2 = None.

  (** An impure combine version, parametrized by a most defined function. *)
  (* Parameter combine_imp_mostdef: *)
  (*   forall (A: Type), (A -> A -> ?? A) -> t A -> t A -> ?? (t A). *)
  (* Parameter f_imp_mostdef: *)
  (*   forall (A: Type), (A -> A -> ?? A) -> option A -> option A -> ?? (option A). *)
  (* Axiom gcombine_imp_mostdef_spec: *)
  (*   forall (A: Type) (imp_mostdef : A -> A -> ?? A) (m1 m2 : t A), *)
  (*   WHEN combine_imp_mostdef imp_mostdef m1 m2 ~> m3 THEN *)
  (*   forall (i : elt), *)
  (*   p_mostdef (fun a1 a2 a3 => imp_mostdef a1 a2 ~~> a3) (get i m1) (get i m2) (get i m3). *)
  (* When one of the source trees and the combined tree are defined for an index [i],
     then the defined value of the source must be equal to the combined one. *)
  (* Axiom gcombine_imp_mostdef_or_ok: *)
  (*   forall (A: Type) (imp_mostdef: A -> A -> ?? A) (m1 m2: t A) (a1 a2: A) (i: elt), *)
  (*   WHEN combine_imp_mostdef imp_mostdef m1 m2 ~> m3 THEN *)
  (*   (forall a1 a2, WHEN f_imp_mostdef imp_mostdef (Some a1) (Some a2) ~> oa *)
  (*   THEN Some a1 = oa /\ Some a2 = oa) -> *)
  (*   get i m1 = Some a1 \/ get i m2 = Some a1 -> *)
  (*   get i m3 = Some a2 -> a1=a2. *)
  (* When both of the source trees are defined for an index [i],
     then their defined values must be equal. *)
  (* Axiom gcombine_imp_mostdef_and_ok: *)
  (*   forall (A: Type) (imp_mostdef: A -> A -> ?? A) (m1 m2: t A) (a1 a2: A) (i: elt), *)
  (*   WHEN combine_imp_mostdef imp_mostdef m1 m2 ~> m3 THEN *)
  (*   (forall a1 a2, WHEN f_imp_mostdef imp_mostdef (Some a1) (Some a2) ~> oa *)
  (*   THEN Some a1 = oa /\ Some a2 = oa) -> *)
  (*   get i m1 = Some a1 /\ get i m2 = Some a2 -> *)
  (*   a1=a2. *)
  (* When the combination succeeds, if both source trees are undefined for an index [i],
     then the combined tree is also undefined on [i]. *)
  (* Axiom gcombine_imp_mostdef_none: *)
  (*   forall  (A: Type) (imp_mostdef: A -> A -> ?? A) (m1 m2: t A) (i: elt), *)
  (*   WHEN combine_imp_mostdef imp_mostdef m1 m2 ~> m3 THEN *)
  (*   get i m1 = None /\ get i m2 = None -> *)
  (*   get i m3 = None. *)
  (* When the combination succeeds, if we know an index [i] on which the combined tree is
     undefined, then both source trees are undefined on [i]. *)
  (* Axiom gcombine_imp_mostdef_none_rev: *)
  (*   forall (A: Type) (imp_mostdef: A -> A -> ?? A), *)
  (*   forall (m1 m2: t A) (i: elt), *)
  (*   WHEN combine_imp_mostdef imp_mostdef m1 m2 ~> m3 THEN *)
  (*   get i m3 = None -> *)
  (*   get i m1 = None /\ get i m2 = None. *)

  (** Enumerating the bindings of a tree. *)
  Parameter elements:
    forall (A: Type), t A -> list (elt * A).
  Axiom elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Axiom elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Axiom elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  (* Axiom elements_extensional: *)
  (*   forall (A: Type) (m n: t A), *)
  (*   (forall i, get i m = get i n) -> *)
  (*   elements m = elements n. *)
  Axiom elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.

  (** Folding a function over all bindings of a tree. *)
  Parameter fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Axiom fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  (** Same as [fold], but the function does not receive the [elt] argument. *)
  Parameter fold1:
    forall (A B: Type), (B -> A -> B) -> t A -> B -> B.
  Axiom fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter init: forall (A: Type), A -> t A.
  Parameter get: forall (A: Type), elt -> t A -> A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

(** ** Representation of trees *)

(** The type [tree'] of nonempty trees.  Each constructor is of the form
    [NodeXYZ], where the bit [X] says whether there is a left subtree,
    [Y] whether there is a value at this node, and [Z] whether there is
    a right subtree. *)

  Inductive tree' (A: Type) : Type := 
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.

  Inductive tree (A: Type) : Type := 
  | Empty : tree A
  | Nodes: tree' A -> tree A.

  Arguments Node001 {A} _.
  Arguments Node010 {A} _.
  Arguments Node011 {A} _ _.
  Arguments Node100 {A} _.
  Arguments Node101 {A} _ _.
  Arguments Node110 {A} _ _.
  Arguments Node111 {A} _ _ _.

  Arguments Empty {A}.
  Arguments Nodes {A} _.

  Scheme tree'_ind := Induction for tree' Sort Prop.

  Definition t := tree.

  (** A smart constructor for type [tree]: given a (possibly empty)
      left subtree, a (possibly absent) value, and a (possibly empty)
      right subtree, it builds the corresponding tree. *)

  Definition Node {A} (l: tree A) (o: option A) (r: tree A) : tree A := 
    match l,o,r with
    | Empty, None, Empty => Empty
    | Empty, None, Nodes r' => Nodes (Node001 r')
    | Empty, Some x, Empty => Nodes (Node010 x)
    | Empty, Some x, Nodes r' => Nodes (Node011 x r')
    | Nodes l', None, Empty => Nodes (Node100 l')
    | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
    | Nodes l', Some x, Empty => Nodes (Node110 l' x)
    | Nodes l', Some x, Nodes r' => Nodes (Node111 l' x r')
    end.

(** ** Basic operations: [empty], [get], [set], [remove] *)

  Definition empty (A: Type) : t A := Empty.

  Fixpoint get' {A} (p: positive) (m: tree' A) : option A :=
    match p, m with
    | xH, Node001 _ => None
    | xH, Node010 x => Some x
    | xH, Node011 x _ => Some x
    | xH, Node100 _ => None
    | xH, Node101 _ _ => None
    | xH, Node110 _ x => Some x
    | xH, Node111 _ x _ => Some x
    | xO q, Node001 _ => None
    | xO q, Node010 _ => None
    | xO q, Node011 _ _ => None
    | xO q, Node100 m' => get' q m'
    | xO q, Node101 m' _ => get' q m'
    | xO q, Node110 m' _ => get' q m'
    | xO q, Node111 m' _ _ => get' q m'
    | xI q, Node001 m' => get' q m'
    | xI q, Node010 _ => None
    | xI q, Node011 _ m' => get' q m'
    | xI q, Node100 m' => None
    | xI q, Node101 _ m' => get' q m'
    | xI q, Node110 _ _ => None
    | xI q, Node111 _ _ m' => get' q m'
    end.

  Definition get {A} (p: positive) (m: tree A) : option A :=
    match m with
    | Empty => None
    | Nodes m' => get' p m'
    end.

  (** [set0 p x] constructs the singleton tree that maps [p] to [x]
      and has no other bindings. *)

  Fixpoint set0 {A} (p: positive) (x: A) : tree' A :=
  match p with
  | xH => Node010 x
  | xO q => Node100 (set0 q x)
  | xI q => Node001 (set0 q x)
  end.

  Fixpoint set' {A} (p: positive) (x: A) (m: tree' A) : tree' A :=
  match p, m with
  | xH, Node001 r => Node011 x r
  | xH, Node010 _ => Node010 x
  | xH, Node011 _ r => Node011 x r
  | xH, Node100 l => Node110 l x
  | xH, Node101 l r => Node111 l x r
  | xH, Node110 l _ => Node110 l x
  | xH, Node111 l _ r => Node111 l x r
  | xO q, Node001 r => Node101 (set0 q x) r
  | xO q, Node010 y => Node110 (set0 q x) y
  | xO q, Node011 y r => Node111 (set0 q x) y r
  | xO q, Node100 l => Node100 (set' q x l)
  | xO q, Node101 l r => Node101 (set' q x l) r
  | xO q, Node110 l y => Node110 (set' q x l) y
  | xO q, Node111 l y r => Node111 (set' q x l) y r
  | xI q, Node001 r => Node001 (set' q x r)
  | xI q, Node010 y => Node011 y (set0 q x)
  | xI q, Node011 y r => Node011 y (set' q x r)
  | xI q, Node100 l => Node101 l (set0 q x)
  | xI q, Node101 l r => Node101 l (set' q x r)
  | xI q, Node110 l y => Node111 l y (set0 q x)
  | xI q, Node111 l y r => Node111 l y (set' q x r)
  end.

  Definition set {A} (p: positive) (x: A) (m: tree A) : tree A :=
  match m with
  | Empty => Nodes (set0 p x)
  | Nodes m' => Nodes (set' p x m')
  end.

  (** Removal in a nonempty tree produces a possibly empty tree.
      To simplify the code, we use the [Node] smart constructor in the
      cases where the result can be empty or nonempty, depending on the
      results of the recursive calls. *)

  Fixpoint rem' {A} (p: positive) (m: tree' A) : tree A :=
  match p, m with
  | xH, Node001 r => Nodes m
  | xH, Node010 _ => Empty
  | xH, Node011 _ r => Nodes (Node001 r)
  | xH, Node100 l => Nodes m
  | xH, Node101 l r => Nodes m
  | xH, Node110 l _ => Nodes (Node100 l)
  | xH, Node111 l _ r => Nodes (Node101 l r)
  | xO q, Node001 r => Nodes m
  | xO q, Node010 y => Nodes m
  | xO q, Node011 y r => Nodes m
  | xO q, Node100 l => Node (rem' q l) None Empty
  | xO q, Node101 l r => Node (rem' q l) None (Nodes r)
  | xO q, Node110 l y => Node (rem' q l) (Some y) Empty
  | xO q, Node111 l y r => Node (rem' q l) (Some y) (Nodes r)
  | xI q, Node001 r => Node Empty None (rem' q r)
  | xI q, Node010 y => Nodes m
  | xI q, Node011 y r => Node Empty (Some y) (rem' q r)
  | xI q, Node100 l => Nodes m
  | xI q, Node101 l r => Node (Nodes l) None (rem' q r)
  | xI q, Node110 l y => Nodes m
  | xI q, Node111 l y r => Node (Nodes l) (Some y) (rem' q r)
  end.

  (** This use of [Node] causes some run-time overhead, which we eliminate
      by partial evaluation within Coq. *)

  Definition remove' := Eval cbv [rem' Node] in @rem'.

  Definition remove {A} (p: positive) (m: tree A) : tree A :=
  match m with
  | Empty => Empty
  | Nodes m' => remove' p m'
  end.

(** ** Good variable properties for the basic operations *)

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof. reflexivity. Qed.

  Lemma gEmpty:
    forall (A: Type) (i: positive), get i (@Empty A) = None.
  Proof. reflexivity. Qed.

  Lemma gss0: forall {A} p (x: A), get' p (set0 p x) = Some x.
  Proof. induction p; simpl; auto. Qed.

  Lemma gso0: forall {A} p q (x: A), p<>q -> get' p (set0 q x) = None.
  Proof.
    induction p; destruct q; simpl; intros; auto; try apply IHp; congruence.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: tree A), get i (set i x m) = Some x.
  Proof.
   intros. destruct m as [|m]; simpl.
   - apply gss0.
   - revert m; induction i; destruct m; simpl; intros; auto using gss0.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: tree A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
   intros. destruct m as [|m]; simpl.
   - apply gso0; auto.
   - revert m j H; induction i; destruct j,m; simpl; intros; auto;
     solve [apply IHi; congruence | apply gso0; congruence | congruence].
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Lemma gNode:
    forall {A} (i: positive) (l: tree A) (x: option A) (r: tree A),
    get i (Node l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
  Proof.
    intros. destruct l, x, r; simpl; auto; destruct i; auto.
  Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: tree A), get i (remove i m) = None.
  Proof.
    Local Opaque Node.
    destruct m as [ |m]; simpl. auto.
    change (remove' i m) with (rem' i m).
    revert m. induction i; destruct m; simpl; auto; rewrite gNode; auto.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: tree A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    Local Opaque Node.
    destruct m as [ |m]; simpl. auto.
    change (remove' j m) with (rem' j m).
    revert j m. induction i; destruct j, m; simpl; intros; auto;
    solve [ congruence
          | rewrite gNode; auto; apply IHi; congruence ].
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

(** ** Custom case analysis principles and induction principles *)

(** We can view trees as being of one of two (non-exclusive)
    cases: either [Empty] for an empty tree, or [Node l o r] for a
    nonempty tree, with [l] and [r] the left and right subtrees
    and [o] an optional value.  The [Empty] constructor and the [Node]
    smart function defined above provide one half of the view: the one
    that lets us construct values of type [tree A].

    We now define the other half of the view: the one that lets us
    inspect and recurse over values of type [tree A].  This is achieved
    by defining appropriate principles for case analysis and induction. *)

  Definition not_trivially_empty {A} (l: tree A) (o: option A) (r: tree A) :=
    match l, o, r with
    | Empty, None, Empty => False
    | _, _, _ => True
    end.

  (** A case analysis principle *)

  Section TREE_CASE.

  Context {A B: Type}
          (empty: B)
          (node: tree A -> option A -> tree A -> B).

  Definition tree_case (m: tree A) : B :=
    match m with
    | Empty => empty
    | Nodes (Node001 r) => node Empty None (Nodes r)
    | Nodes (Node010 x) => node Empty (Some x) Empty
    | Nodes (Node011 x r) => node Empty (Some x) (Nodes r)
    | Nodes (Node100 l) => node (Nodes l) None Empty
    | Nodes (Node101 l r) => node (Nodes l) None (Nodes r)
    | Nodes (Node110 l x) => node (Nodes l) (Some x) Empty
    | Nodes (Node111 l x r) => node (Nodes l) (Some x) (Nodes r)
    end.

  Lemma unroll_tree_case: forall l o r,
    not_trivially_empty l o r ->
    tree_case (Node l o r) = node l o r.
  Proof.
    destruct l, o, r; simpl; intros; auto. contradiction.
  Qed.

  End TREE_CASE.

  (** A recursion principle *)

  Section TREE_REC.

  Context {A B: Type}
          (empty: B)
          (node: tree A -> B -> option A -> tree A -> B -> B).

  Fixpoint tree_rec' (m: tree' A) : B :=
    match m with
    | Node001 r => node Empty empty None (Nodes r) (tree_rec' r)
    | Node010 x => node Empty empty (Some x) Empty empty
    | Node011 x r => node Empty empty (Some x) (Nodes r) (tree_rec' r)
    | Node100 l => node (Nodes l) (tree_rec' l) None Empty empty
    | Node101 l r => node (Nodes l) (tree_rec' l) None (Nodes r) (tree_rec' r)
    | Node110 l x => node (Nodes l) (tree_rec' l) (Some x) Empty empty
    | Node111 l x r => node (Nodes l) (tree_rec' l) (Some x) (Nodes r) (tree_rec' r)
    end.

  Definition tree_rec (m: tree A) : B :=
    match m with
    | Empty => empty
    | Nodes m' => tree_rec' m'
    end.

  Lemma unroll_tree_rec: forall l o r,
    not_trivially_empty l o r ->
    tree_rec (Node l o r) = node l (tree_rec l) o r (tree_rec r).
  Proof.
    destruct l, o, r; simpl; intros; auto. contradiction.
  Qed.

  End TREE_REC.

  (** A double recursion principle *)

  Section TREE_REC2.

  Context {A B C: Type}
          (base: C)
          (base1: tree B -> C) 
          (base2: tree A -> C)
          (nodes: forall (l1: tree A) (o1: option A) (r1: tree A)
                         (l2: tree B) (o2: option B) (r2: tree B)
                         (lrec: C) (rrec: C), C).

  Fixpoint tree_rec2' (m1: tree' A) (m2: tree' B) : C.
  Proof.
    destruct m1 as [ r1 | x1 | x1 r1 | l1 | l1 r1 | l1 x1 | l1 x1 r1 ];
    destruct m2 as [ r2 | x2 | x2 r2 | l2 | l2 r2 | l2 x2 | l2 x2 r2 ];
    (apply nodes;
    [ solve [ exact (Nodes l1) | exact Empty ]
    | solve [ exact (Some x1)  | exact None ]
    | solve [ exact (Nodes r1) | exact Empty ]
    | solve [ exact (Nodes l2) | exact Empty ]
    | solve [ exact (Some x2)  | exact None ]
    | solve [ exact (Nodes r2) | exact Empty ]
    | solve [ exact (tree_rec2' l1 l2) | exact (base2 (Nodes l1)) | exact (base1 (Nodes l2)) | exact base ]
    | solve [ exact (tree_rec2' r1 r2) | exact (base2 (Nodes r1)) | exact (base1 (Nodes r2)) | exact base ]
    ]).
  Defined.

  Definition tree_rec2 (a: tree A) (b: tree B) : C :=
    match a, b with
    | Empty, Empty => base
    | Empty, _ => base1 b
    | _, Empty => base2 a
    | Nodes a', Nodes b' => tree_rec2' a' b'
    end.

  Lemma unroll_tree_rec2_NE:
    forall l1 o1 r1,
    not_trivially_empty l1 o1 r1 ->
    tree_rec2 (Node l1 o1 r1) Empty = base2 (Node l1 o1 r1).
  Proof.
    intros. destruct l1, o1, r1; try contradiction; reflexivity.
  Qed.

  Lemma unroll_tree_rec2_EN:
    forall l2 o2 r2,
    not_trivially_empty l2 o2 r2 ->
    tree_rec2 Empty (Node l2 o2 r2) = base1 (Node l2 o2 r2).
  Proof.
    intros. destruct l2, o2, r2; try contradiction; reflexivity.
  Qed.

  Lemma unroll_tree_rec2_NN:
    forall l1 o1 r1 l2 o2 r2,
    not_trivially_empty l1 o1 r1 -> not_trivially_empty l2 o2 r2 ->
    tree_rec2 (Node l1 o1 r1) (Node l2 o2 r2) =
    nodes l1 o1 r1 l2 o2 r2 (tree_rec2 l1 l2) (tree_rec2 r1 r2).
  Proof.
    intros.
    destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction; reflexivity.
  Qed.

  End TREE_REC2.

(** An induction principle *)

  Section TREE_IND.

  Context {A: Type} (P: tree A -> Type)
          (empty: P Empty)
          (node: forall l, P l -> forall o r, P r -> not_trivially_empty l o r ->
                 P (Node l o r)).

  Program Fixpoint tree_ind' (m: tree' A) : P (Nodes m) :=
    match m with
    | Node001 r => @node Empty empty None (Nodes r) (tree_ind' r) _
    | Node010 x => @node Empty empty (Some x) Empty empty _
    | Node011 x r => @node Empty empty (Some x) (Nodes r) (tree_ind' r) _
    | Node100 l => @node (Nodes l) (tree_ind' l) None Empty empty _
    | Node101 l r => @node (Nodes l) (tree_ind' l) None (Nodes r) (tree_ind' r) _
    | Node110 l x => @node (Nodes l) (tree_ind' l) (Some x) Empty empty _
    | Node111 l x r => @node (Nodes l) (tree_ind' l) (Some x) (Nodes r) (tree_ind' r) _
    end.

  Definition tree_ind (m: tree A) : P m :=
    match m with
    | Empty => empty
    | Nodes m' => tree_ind' m'
    end.

  End TREE_IND.

(** ** Extensionality property *)

  Lemma tree'_not_empty:
    forall {A} (m: tree' A), exists i, get' i m <> None.
  Proof.
   induction m; simpl; try destruct IHm as [p H].
   - exists (xI p); auto.
   - exists xH; simpl; congruence.
   - exists xH; simpl; congruence.
   - exists (xO p); auto.
   - destruct IHm1 as [p H]; exists (xO p); auto.
   - exists xH; simpl; congruence.
   - exists xH; simpl; congruence.
  Qed.

  Corollary extensionality_empty:
    forall {A} (m: tree A),
    (forall i, get i m = None) -> m = Empty.
  Proof.
    intros. destruct m as [ | m]; auto. destruct (tree'_not_empty m) as [i GET].
    elim GET. apply H.
  Qed.

  Theorem extensionality:
    forall (A: Type) (m1 m2: tree A),
    (forall i, get i m1 = get i m2) -> m1 = m2.
  Proof.
    intros A. induction m1 using tree_ind; induction m2 using tree_ind; intros.
  - auto.
  - symmetry. apply extensionality_empty. intros; symmetry; apply H0.
  - apply extensionality_empty. apply H0.
  - f_equal.
    + apply IHm1_1. intros. specialize (H1 (xO i)); rewrite ! gNode in H1. auto.
    + specialize (H1 xH); rewrite ! gNode in H1. auto.
    + apply IHm1_2. intros. specialize (H1 (xI i)); rewrite ! gNode in H1. auto.
  Qed.

  (** Some consequences of extensionality *)

  Theorem gsident:
    forall {A} (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite gsspec. destruct (peq j i); congruence.
  Qed.

  Theorem set2:
    forall {A} (i: elt) (m: t A) (v1 v2: A),
    set i v2 (set i v1 m) = set i v2 m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite ! gsspec. destruct (peq j i); auto.
  Qed.

(** ** Boolean equality *)

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.

    Fixpoint beq' (m1 m2: tree' A) {struct m1} : bool :=
    match m1, m2 with
    | Node001 r1, Node001 r2 => beq' r1 r2
    | Node010 x1, Node010 x2 => beqA x1 x2
    | Node011 x1 r1, Node011 x2 r2 => beqA x1 x2 && beq' r1 r2
    | Node100 l1, Node100 l2 => beq' l1 l2
    | Node101 l1 r1, Node101 l2 r2 => beq' l1 l2 && beq' r1 r2
    | Node110 l1 x1, Node110 l2 x2 => beqA x1 x2 && beq' l1 l2
    | Node111 l1 x1 r1, Node111 l2 x2 r2  => beqA x1 x2 && beq' l1 l2 && beq' r1 r2
    | _, _ => false
    end.

    Definition beq (m1 m2: t A) : bool :=
    match m1, m2 with
    | Empty, Empty => true
    | Nodes m1', Nodes m2' => beq' m1' m2'
    | _, _ => false
    end.

    Let beq_optA (o1 o2: option A) : bool :=
      match o1, o2 with
      | None, None => true
      | Some a1, Some a2 => beqA a1 a2
      | _, _ => false
      end.

    Lemma beq_correct_bool:
      forall m1 m2,
      beq m1 m2 = true <-> (forall x, beq_optA (get x m1) (get x m2) = true).
    Proof.
      Local Transparent Node.
      assert (beq_NN: forall l1 o1 r1 l2 o2 r2,
              not_trivially_empty l1 o1 r1 ->
              not_trivially_empty l2 o2 r2 ->
              beq (Node l1 o1 r1) (Node l2 o2 r2) =
              beq l1 l2 && beq_optA o1 o2 && beq r1 r2).
      { intros.
        destruct l1, o1, r1; try contradiction; destruct l2, o2, r2; try contradiction;
        simpl; rewrite ? andb_true_r, ? andb_false_r; auto.
        rewrite andb_comm; auto.
        f_equal; rewrite andb_comm; auto. }
      induction m1 using tree_ind; [|induction m2 using tree_ind].
    - intros. simpl; split; intros.
      + destruct m2; try discriminate. simpl; auto.
      + replace m2 with (@Empty A); auto. apply extensionality; intros x.
        specialize (H x). destruct (get x m2); simpl; congruence.
    - split; intros.
      + destruct (Node l o r); try discriminate. simpl; auto.
      + replace (Node l o r) with (@Empty A); auto. apply extensionality; intros x.
        specialize (H0 x). destruct (get x (Node l o r)); simpl in *; congruence.
    - rewrite beq_NN by auto. split; intros.
      + InvBooleans. rewrite ! gNode. destruct x.
        * apply IHm0; auto.
        * apply IHm1; auto.
        * auto.
      + apply andb_true_intro; split; [apply andb_true_intro; split|].
        * apply IHm1. intros. specialize (H1 (xO x)); rewrite ! gNode in H1; auto.
        * specialize (H1 xH); rewrite ! gNode in H1; auto.
        * apply IHm0. intros. specialize (H1 (xI x)); rewrite ! gNode in H1; auto.
    Qed.

    Theorem beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall (x: elt),
       match get x m1, get x m2 with
       | None, None => True
       | Some y1, Some y2 => beqA y1 y2 = true
       | _, _ => False
       end).
    Proof.
      intros. rewrite beq_correct_bool. unfold beq_optA. split; intros.
    - specialize (H x). destruct (get x m1), (get x m2); intuition congruence.
    - specialize (H x). destruct (get x m1), (get x m2); intuition auto.
    Qed.

    Theorem beq_eq: forall
      (beqA_eq: forall x y, beqA x y = true <-> x=y)
      m1 m2,
         beq m1 m2 = true <-> m1=m2.
    Proof.
      intros. rewrite beq_correct.
      split. 
      + intros EQ; apply extensionality.
        intros i. generalize (EQ i); clear EQ.
        destruct (get i m1); destruct (get i m2); try (intuition congruence).
        rewrite beqA_eq; congruence.
      + intros; subst. destruct (get _ _); eauto.
        rewrite beqA_eq; auto.
    Qed.

  End BOOLEAN_EQUALITY.

  Theorem eq_dec: forall {A:Type} (eqA_dec: forall (x y:A), {x=y} + {x<>y} )
     (m1 m2: t A), { m1=m2 } + { m1<>m2 }.
  intros.
    set (beqA := fun x y => if eqA_dec x y then true else false).
    assert (beqA_eq: forall x y, beqA x y = true <-> x=y). {
      abstract (unfold beqA; intros; destruct (eqA_dec _ _); intuition congruence).
    }
    destruct (beq beqA m1 m2) eqn: X.
    - left. abstract (eapply beq_eq; eauto).
    - right. abstract (intros Y; eapply beq_eq in Y; eauto; congruence).
  Defined.

(** ** Collective operations *)

  Fixpoint prev_append (i j: positive) {struct i} : positive :=
    match i with
      | xH => j
      | xI i' => prev_append i' (xI j)
      | xO i' => prev_append i' (xO j)
    end.

  Definition prev (i: positive) : positive :=
    prev_append i xH.

  Lemma prev_append_prev i j:
    prev (prev_append i j) = prev_append j i.
  Proof.
    revert j. unfold prev.
    induction i as [i IH|i IH|]. 3: reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma prev_involutive i :
    prev (prev i) = i.
  Proof (prev_append_prev i xH).

  Lemma prev_append_inj i j j' :
    prev_append i j = prev_append i j' -> j = j'.
  Proof.
    revert j j'.
    induction i as [i Hi|i Hi|]; intros j j' H; auto;
    specialize (Hi _ _ H); congruence.
  Qed.

  Fixpoint map' {A B} (f: positive -> A -> B) (m: tree' A) (i: positive)
           {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map' f r (xI i))
    | Node010 x => Node010 (f (prev i) x)
    | Node011 x r => Node011 (f (prev i) x) (map' f r (xI i))
    | Node100 l => Node100 (map' f l (xO i))
    | Node101 l r => Node101 (map' f l (xO i)) (map' f r (xI i))
    | Node110 l x => Node110 (map' f l (xO i)) (f (prev i) x)
    | Node111 l x r => Node111 (map' f l (xO i)) (f (prev i) x) (map' f r (xI i))
    end.

  Definition map {A B} (f: positive -> A -> B) (m: tree A) :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map' f m xH)
    end.

  Lemma gmap':
    forall {A B} (f: positive -> A -> B) (i j : positive) (m: tree' A),
    get' i (map' f m j) = option_map (f (prev (prev_append i j))) (get' i m).
  Proof.
    induction i; intros; destruct m; simpl; auto.
  Qed.

  Theorem gmap:
    forall {A B} (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros; destruct m as [|m]; simpl. auto. rewrite gmap'. repeat f_equal. exact (prev_involutive i).
  Qed.

  (** [mapi_dep] is like [map], but the per-element function additionally
      receives a proof that the value being mapped is indeed the one stored
      at position [i] in the tree. *)

  Fixpoint mapi_dep' {A B} (m: tree' A) :
    (forall (i: positive) (x: A), get' i m = Some x -> B) -> tree' B :=
    match m return (forall (i: positive) (x: A), get' i m = Some x -> B)
                   -> tree' B with
    | Node001 r => fun f =>
        Node001 (mapi_dep' r (fun i x H => f (xI i) x H))
    | Node010 x => fun f =>
        Node010 (f xH x eq_refl)
    | Node011 x r => fun f =>
        Node011 (f xH x eq_refl)
                (mapi_dep' r (fun i y H => f (xI i) y H))
    | Node100 l => fun f =>
        Node100 (mapi_dep' l (fun i x H => f (xO i) x H))
    | Node101 l r => fun f =>
        Node101 (mapi_dep' l (fun i x H => f (xO i) x H))
                (mapi_dep' r (fun i x H => f (xI i) x H))
    | Node110 l x => fun f =>
        Node110 (mapi_dep' l (fun i y H => f (xO i) y H))
                (f xH x eq_refl)
    | Node111 l x r => fun f =>
        Node111 (mapi_dep' l (fun i y H => f (xO i) y H))
                (f xH x eq_refl)
                (mapi_dep' r (fun i y H => f (xI i) y H))
    end.

  Definition mapi_dep {A B} (m: tree A) :
    (forall (i: positive) (x: A), get i m = Some x -> B) -> tree B :=
    match m return (forall (i: positive) (x: A), get i m = Some x -> B)
                   -> tree B with
    | Empty => fun _ => Empty
    | Nodes m' => fun f => Nodes (mapi_dep' m' f)
    end.

  Lemma gmapi_dep':
    forall {A B} (m: tree' A)
           (f: forall (i: positive) (x: A), get' i m = Some x -> B)
           (i: positive),
      get' i (mapi_dep' m f) =
      (match get' i m as o return get' i m = o -> option B with
       | Some x => fun H => Some (f i x H)
       | None => fun _ => None
       end) eq_refl.
  Proof.
    intros A B m.
    induction m as [r IHr | x | x r IHr
                   | l IHl | l IHl r IHr | l IHl x | l IHl x r IHr];
    intros f i; destruct i; cbn; try reflexivity;
    first [apply IHl | apply IHr].
  Qed.

  Theorem gmapi_dep:
    forall {A B} (m: tree A)
           (f: forall (i: positive) (x: A), get i m = Some x -> B)
           (i: positive),
      get i (mapi_dep m f) =
      (match get i m as o return get i m = o -> option B with
       | Some x => fun H => Some (f i x H)
       | None => fun _ => None
       end) eq_refl.
  Proof.
    intros A B [|m] f i; cbn; try reflexivity.
    apply gmapi_dep'.
  Qed.

  Theorem mapi_dep_map:
    forall {A B} (f: positive -> A -> B) (m: t A),
      mapi_dep m (fun i x _ => f i x) = map f m.
  Proof.
    intros. apply extensionality; intros i.
    rewrite gmap, gmapi_dep.
    destruct (get i m); reflexivity.
  Qed.

  Fixpoint map1' {A B} (f: A -> B) (m: tree' A) {struct m} : tree' B :=
    match m with
    | Node001 r => Node001 (map1' f r)
    | Node010 x => Node010 (f x)
    | Node011 x r => Node011 (f x) (map1' f r)
    | Node100 l => Node100 (map1' f l)
    | Node101 l r => Node101 (map1' f l) (map1' f r)
    | Node110 l x => Node110 (map1' f l) (f x)
    | Node111 l x r => Node111 (map1' f l) (f x) (map1' f r)
    end.

  Definition map1 {A B} (f: A -> B) (m: t A) : t B :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map1' f m)
    end.

  Theorem gmap1:
    forall {A B} (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros. destruct m as [|m]; simpl. auto.
    revert i; induction m; destruct i; simpl; auto.
  Qed.

  Definition map_filter1_nonopt {A B} (f: A -> option B) (m: tree A) : tree B :=
    tree_rec
      Empty
      (fun l lrec o r rrec => Node lrec (match o with None => None | Some a => f a end) rrec)
      m.

  Definition may_f {A B} (o: option A) (f: A -> option (option B)): option (option B) :=
    match o with
    | None => Some None
    | Some a => SOME fa <- f a IN Some fa
    end.

  Definition may_map_filter1_nonopt {A B} (f: A -> option (option B)) (m: tree A) : option (tree B) :=
    tree_rec
      (Some Empty)
      (fun l olrec o r orrec =>
        SOME lrec <- olrec IN
        SOME rrec <- orrec IN
        SOME ob <- may_f o f IN
        Some (Node lrec ob rrec))
      m.
  
  Definition imp_f {A B} (o: option A) (f: A -> ?? (option B)): ?? (option B) :=
    match o with
    | None => RET None
    | Some a => DO fa <~ f a;; RET fa
    end.
  
  Definition imp_map_filter1_nonopt {A B} (f: A -> ?? (option B)) (m: tree A) : ?? (tree B) :=
    tree_rec
      (RET Empty)
      (fun l olrec o r orrec =>
        DO lrec <~ olrec;;
        DO rrec <~ orrec;;
        DO ob <~ imp_f o f;;
        RET (Node lrec ob rrec))
      m.

  Local Transparent Node.

  Definition map_filter1 :=
    Eval cbv [map_filter1_nonopt tree_rec tree_rec' Node] in @map_filter1_nonopt.

  Lemma gmap_filter1:
    forall {A B} (f: A -> option B) (m: tree A) (i: positive),
    get i (map_filter1 f m) = match get i m with None => None | Some a => f a end.
  Proof.
    change @map_filter1 with @map_filter1_nonopt. unfold map_filter1_nonopt.
    intros until f. induction m using tree_ind; intros.
  - auto.
  - rewrite unroll_tree_rec by auto. rewrite ! gNode; destruct i; auto.
  Qed.
  
  Definition may_map_filter1 :=
    Eval cbv [may_map_filter1_nonopt tree_rec tree_rec' Node] in @may_map_filter1_nonopt.

  Lemma gmay_map_filter1:
    forall {A B} (f: A -> option (option B)) (m: tree A) (fm: tree B) (i: positive),
    may_map_filter1 f m = Some fm ->
    get i fm = match get i m with None => None | Some a => SOME fa <- f a IN fa end.
  Proof.
    change @may_map_filter1 with @may_map_filter1_nonopt. unfold may_map_filter1_nonopt.
    intros until f. induction m using tree_ind; simpl; intros.
  - inv H; auto.
  - rewrite unroll_tree_rec in H0 by auto. generalize H0; clear H0.
    do 3 autodestruct; intros. inv H0. rewrite ! gNode; destruct i; auto.
    unfold may_f in EQ. repeat autodestruct.
  Qed.

  Lemma gmay_map_filter1_trivial:
    forall {A} (m: tree A),
    may_map_filter1 (fun a: A => Some (Some a)) m = Some m.
  Proof.
    change @may_map_filter1 with @may_map_filter1_nonopt. unfold may_map_filter1_nonopt.
    intros until A. induction m using tree_ind; simpl; intros; auto.
    rewrite unroll_tree_rec by auto.
    do 3 autodestruct; intros; [ inv IHm1; inv IHm2 |];
    generalize EQ; clear EQ; unfold may_f; autodestruct.
  Qed.

  Definition imp_map_filter1 :=
    Eval cbv [imp_map_filter1_nonopt tree_rec tree_rec' Node] in @imp_map_filter1_nonopt.

  Lemma gimp_map_filter1:
    forall {A B} (f: A -> ?? (option B)) (m: tree A) (ob: option B) (i: positive),
    WHEN imp_map_filter1 f m ~> fm THEN
    (match get i m with None => ob = None | Some a =>
        WHEN f a ~> fa THEN ob = fa end) ->
    get i fm = ob.
  Proof.
    change @imp_map_filter1 with @imp_map_filter1_nonopt. unfold imp_map_filter1_nonopt.
    intros until f. induction m using tree_ind; simpl; intros.
    - wlp_simplify.
    - rewrite unroll_tree_rec by auto; wlp_simplify.
      all:
        rewrite gNode in H2; rewrite gNode; destruct i;
        [ eapply IHm2; eauto | eapply IHm1; eauto | rewrite H2; eauto].
    Unshelve. all: eauto.
  Qed.

  Definition filter1 {A} (pred: A -> bool) (m: t A) : t A :=
    map_filter1 (fun a => if pred a then Some a else None) m.

  Theorem gfilter1:
    forall {A} (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
  Proof.
    intros. apply gmap_filter1.
  Qed.

  Fixpoint filter' {A} (f: positive -> A -> bool) (m: tree' A) (i: positive) : tree A :=
    match m with
    | Node001 r =>
        match filter' f r (xI i) with
        | Empty => Empty
        | Nodes t => Nodes (Node001 t)
        end
    | Node010 x => if f (prev i) x then Nodes m else Empty
    | Node011 x r =>
        match f (prev i) x, filter' f r (xI i) with
        | false, Empty => Empty
        | true, Empty => Nodes (Node010 x)
        | false, Nodes r => Nodes (Node001 r)
        | true, Nodes r => Nodes (Node011 x r)
        end
    | Node100 l =>
        match filter' f l (xO i) with
        | Empty => Empty
        | Nodes t => Nodes (Node100 t)
        end
    | Node101 l r =>
        match filter' f l (xO i), filter' f r (xI i) with
        | Empty, Empty => Empty
        | Nodes l, Empty => Nodes (Node100 l)
        | Empty, Nodes r => Nodes (Node001 r)
        | Nodes l, Nodes r => Nodes (Node101 l r)
        end
    | Node110 l x =>
        match filter' f l (xO i), f (prev i) x with
        | Empty, false => Empty
        | Empty, true => Nodes (Node010 x)
        | Nodes l, false => Nodes (Node100 l)
        | Nodes l, true => Nodes (Node110 l x)
        end
    | Node111 l x r =>
        match filter' f l (xO i), f (prev i) x, filter' f r (xI i) with
        | Empty, false, Empty => Empty
        | Empty, true, Empty => Nodes (Node010 x)
        | Nodes l, false, Empty => Nodes (Node100 l)
        | Nodes l, true, Empty => Nodes (Node110 l x)
        | Empty, false, Nodes r => Nodes (Node001 r)
        | Empty, true, Nodes r => Nodes (Node011 x r)
        | Nodes l, false, Nodes r => Nodes (Node101 l r)
        | Nodes l, true, Nodes r => Nodes (Node111 l x r)
        end
    end.

  Definition filter {A} (pred : positive -> A -> bool) (m: t A) : t A :=
    match m with
    | Empty => Empty
    | Nodes t => filter' pred t xH
    end.

  Section COMBINE.

  Variables A B C: Type.
  Variable f: option A -> option B -> option C.
  Hypothesis f_none_none: f None None = None.

  Let combine_l := map_filter1 (fun a => f (Some a) None).
  Let combine_r := map_filter1 (fun b => f None (Some b)).

  Let combine_nonopt (m1: tree A) (m2: tree B) : tree C :=
    tree_rec2
      Empty
      combine_r
      combine_l
      (fun l1 o1 r1 l2 o2 r2 lrec rrec =>
        Node lrec
             (match o1, o2 with None, None => None | _, _ => f o1 o2 end)
             rrec)
      m1 m2.

  Definition combine :=
    Eval cbv [combine_nonopt tree_rec2 tree_rec2'] in combine_nonopt.

  Lemma gcombine_l: forall m i, get i (combine_l m) = f (get i m) None.
  Proof.
    intros; unfold combine_l; rewrite gmap_filter1. destruct (get i m); auto.
  Qed.

  Lemma gcombine_r: forall m i, get i (combine_r m) = f None (get i m).
  Proof.
    intros; unfold combine_r; rewrite gmap_filter1. destruct (get i m); auto.
  Qed.

  Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    change combine with combine_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
  - auto.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_EN by auto. apply gcombine_r.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NE by auto. apply gcombine_l.
  - unfold combine_nonopt; rewrite unroll_tree_rec2_NN by auto.
    rewrite ! gNode; destruct i; auto. destruct o, o0; auto.
  Qed.

  End COMBINE.

  Section MOSTDEF_COMBINE.

  Variables A: Type.
  Variable mostdef: A -> A -> option A.
  Definition f_mostdef (o1 o2: option A): option (option A) :=
    match o1, o2 with
    | Some a1, Some a2 =>
        SOME a3 <- mostdef a1 a2 IN Some (Some a3)
    | Some a, None
    | None, Some a => Some (Some a)
    | None, None => Some None
    end.

  Let combine_mostdef_l := may_map_filter1 (fun a => f_mostdef (Some a) None).
  Let combine_mostdef_r := may_map_filter1 (fun a => f_mostdef None (Some a)).

  Definition may_f2 (o1 o2: option A): option (option A) :=
    match o1, o2 with
    | None, None => Some None
    | _, _ => SOME fc <- f_mostdef o1 o2 IN Some fc
    end.

  Let combine_mostdef_nonopt (m1 m2: tree A) : option (tree A) :=
    tree_rec2
      (Some Empty)
      combine_mostdef_r
      combine_mostdef_l
      (fun l1 o1 r1 l2 o2 r2 olrec orrec =>
        SOME lrec <- olrec IN
        SOME rrec <- orrec IN
        SOME oa <- may_f2 o1 o2 IN
        Some (Node lrec oa rrec))
      m1 m2.

  Definition combine_mostdef :=
    Eval cbv [combine_mostdef_nonopt tree_rec2 tree_rec2'] in combine_mostdef_nonopt.

  Lemma gcombine_mostdef_l: forall m fm oa i,
    combine_mostdef_l m = Some fm ->
    f_mostdef (get i m) None = Some oa ->
    get i fm = oa.
  Proof.
    unfold combine_mostdef_l; intros.
    erewrite gmay_map_filter1; eauto.
    repeat autodestruct. unfold f_mostdef in H0; congruence.
  Qed.

  Lemma gcombine_mostdef_r: forall m fm oa i,
    combine_mostdef_r m = Some fm ->
    f_mostdef None (get i m) = Some oa ->
    get i fm = oa.
  Proof.
    unfold combine_mostdef_r; intros.
    erewrite gmay_map_filter1; eauto.
    repeat autodestruct. unfold f_mostdef in H0; congruence.
  Qed.

  Lemma gcombine_mostdef_l_rev: forall m fm oa i,
    combine_mostdef_l m = Some fm ->
    get i fm = oa ->
    get i m = oa.
  Proof.
    unfold combine_mostdef_l; intros.
    erewrite gmay_map_filter1 in H0; eauto.
    generalize H0; clear H0; simpl; autodestruct.
  Qed.

  Lemma gcombine_mostdef_r_rev: forall m fm oa i,
    combine_mostdef_r m = Some fm ->
    get i fm = oa ->
    get i m = oa.
  Proof.
    unfold combine_mostdef_r; intros.
    erewrite gmay_map_filter1 in H0; eauto.
    generalize H0; clear H0; simpl; autodestruct.
  Qed.

  Lemma fcombine_mostdef_l: forall m fm i,
    combine_mostdef_l m = Some fm ->
    f_mostdef (get i m) None = None ->
    False.
  Proof.
    unfold combine_mostdef_l; intros.
    eapply (gmay_map_filter1 _ _ i) in H. unfold f_mostdef in *.
    generalize H; clear H; simpl; repeat autodestruct.
  Qed.

  Lemma fcombine_mostdef_r: forall m fm i,
    combine_mostdef_r m = Some fm ->
    f_mostdef None (get i m) = None ->
    False.
  Proof.
    unfold combine_mostdef_r; intros.
    eapply (gmay_map_filter1 _ _ i) in H. unfold f_mostdef in *.
    generalize H; clear H; repeat autodestruct.
  Qed.

  Lemma combine_mostdef_nonopt_decompose l l0 o o0 r r0:
    not_trivially_empty l o r ->
    not_trivially_empty l0 o0 r0 ->
    combine_mostdef_nonopt (Node l o r) (Node l0 o0 r0) = None ->
    combine_mostdef_nonopt r r0 = None
    \/ combine_mostdef_nonopt l l0 = None
    \/ may_f2 o o0 = None.
  Proof.
    intros. unfold combine_mostdef_nonopt in H1; rewrite unroll_tree_rec2_NN in H1 by auto.
    generalize H1; clear H1; autodestruct; simpl;
    [ autodestruct; simpl; [ autodestruct; simpl |]|]; intuition auto.
  Qed.

  Theorem gcombine_mostdef:
      forall (m1 m2 m3: t A) (oa: option A) (i: positive),
      combine_mostdef m1 m2 = Some m3 ->
      f_mostdef (get i m1) (get i m2) = Some oa ->
      get i m3 = oa.
  Proof.
    change combine_mostdef with combine_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - rewrite gEmpty in H0; simpl in *; inv H0; inv H; auto.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_EN in H0 by auto.
      eapply gcombine_mostdef_r; eauto.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_NE in H0 by auto.
      eapply gcombine_mostdef_l; eauto.
    - unfold combine_mostdef_nonopt in H1; rewrite unroll_tree_rec2_NN in H1 by auto.
      generalize H1; clear H1; do 3 autodestruct; intros. inv H1.
      rewrite ! gNode in H2; rewrite !gNode; destruct i.
      eapply IHm0; eauto. eapply IHm1; eauto.
      generalize EQ; clear EQ.
      unfold may_f2, f_mostdef in *; repeat autodestruct.
  Qed.

  Theorem fcombine_mostdef:
      forall (m1 m2: t A),
      combine_mostdef m1 m2 = None ->
      (forall i a1 a2, (get i m1) = Some a1 -> (get i m2) = Some a2 ->
      mostdef a1 a2 <> None) ->
      False.
  Proof.
    change combine_mostdef with combine_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - simpl in *; inv H.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_EN in H0 by auto.
      unfold combine_mostdef_r in H0; simpl in H0;
      rewrite gmay_map_filter1_trivial in H0; inv H0.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_NE in H0 by auto.
      unfold combine_mostdef_l in H0; simpl in H0;
      rewrite gmay_map_filter1_trivial in H0; inv H0.
    - apply combine_mostdef_nonopt_decompose in H1; auto.
      destruct H1 as [HR | [HL | HMID]].
      + eapply IHm0 in HR; eauto. intros.
        assert (get (xI i) (Node l o r) = Some a1) by (rewrite gNode; auto).
        assert (get (xI i) (Node l0 o0 r0) = Some a2) by (rewrite gNode; auto).
        eapply H2; eauto.
      + eapply IHm1 in HL; eauto. intros.
        assert (get (xO i) (Node l o r) = Some a1) by (rewrite gNode; auto).
        assert (get (xO i) (Node l0 o0 r0) = Some a2) by (rewrite gNode; auto).
        eapply H2; eauto.
      + generalize HMID; clear HMID.
        unfold may_f2, f_mostdef in *; repeat autodestruct; intros.
        assert (get (xH) (Node l o r) = Some a) by (rewrite gNode; auto).
        assert (get (xH) (Node l0 o0 r0) = Some a0) by (rewrite gNode; auto).
        eapply H2; eauto; [ rewrite <- !EQ1 in * | rewrite <- EQ0 in * ]; eauto.
  Qed.

  Set Apply With Renaming.
  Theorem gcombine_mostdef_ok:
      forall (m1 m2 m3: t A) (i: positive) (a: A),
      combine_mostdef m1 m2 = Some m3 ->
      get i m3 = Some a ->
      f_mostdef (get i m1) (get i m2) = Some (Some a).
  Proof.
    change combine_mostdef with combine_mostdef_nonopt.
    induction m1 using PTree.tree_ind; induction m2 using PTree.tree_ind; simpl; intros.
    - inv H; inv H0.
    - destruct (Node l o r); try (inv H0; inv H1; fail).
      unfold combine_mostdef_r in H0.
      eapply gmay_map_filter1 with (i0:=i) in H0 || (* compat hack *)
      eapply gmay_map_filter1 with (i:=i) in H0.
      generalize H0; clear H0; unfold f_mostdef; repeat autodestruct.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_NE in H0 by auto.
      unfold combine_mostdef_l in H0.
      eapply gmay_map_filter1 with (i0:=i) in H0 || (* compat hack *)
      eapply gmay_map_filter1 with (i:=i) in H0.
      generalize H0; clear H0; unfold f_mostdef; repeat autodestruct.
    - unfold combine_mostdef_nonopt in H1; rewrite unroll_tree_rec2_NN in H1 by auto.
      generalize H1; clear H1; do 3 autodestruct; intros. inv H1.
      rewrite gNode in H2; rewrite !gNode; destruct i.
      eapply IHm0; eauto. eapply IHm1; eauto.
      generalize EQ; clear EQ.
      unfold may_f2; repeat autodestruct.
  Qed.

  Theorem gcombine_mostdef_only_l:
      forall (m1: t A),
      combine_mostdef m1 Empty = Some m1.
  Proof.
    change combine_mostdef with combine_mostdef_nonopt.
    induction m1 using tree_ind; simpl; intros.
    - reflexivity.
    - unfold combine_mostdef_nonopt; rewrite unroll_tree_rec2_NE by auto.
      unfold combine_mostdef_l; simpl. apply gmay_map_filter1_trivial.
  Qed.

  Theorem gcombine_mostdef_none_rev:
      forall (m1 m2 m3: t A) (i: positive),
      combine_mostdef m1 m2 = Some m3 ->
      get i m3 = None ->
      get i m1 = None /\ get i m2 = None.
  Proof.
    change combine_mostdef with combine_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - auto.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_EN in H0 by auto.
      eapply gcombine_mostdef_r_rev in H0; eauto.
    - unfold combine_mostdef_nonopt in H0; rewrite unroll_tree_rec2_NE in H0 by auto.
      eapply gcombine_mostdef_l_rev in H0; eauto.
    - unfold combine_mostdef_nonopt in H1; rewrite unroll_tree_rec2_NN in H1 by auto.
      generalize H1; clear H1; do 3 autodestruct. intros. inv H1.
      all:
      rewrite !gNode in *; destruct i; intros; [ eapply IHm0; eauto | eapply IHm1; eauto |].
      generalize EQ; clear EQ; unfold may_f2. rewrite H2.
      destruct o, o0; auto; repeat (autodestruct; simpl); congruence.
  Qed.
  
  End MOSTDEF_COMBINE.

  Section IMPURE_MOSTDEF_COMBINE.

  Variables A: Type.
  Variable imp_mostdef: A -> A -> ?? A.

  Definition f_imp_mostdef (o1 o2: option A): ?? (option A) :=
    match o1, o2 with
    | Some a1, Some a2 =>
        DO a3 <~ imp_mostdef a1 a2;; RET (Some a3)
    | Some a, None
    | None, Some a => RET (Some a)
    | None, None => RET None
    end.

  Lemma f_imp_mostdef_none:
    WHEN f_imp_mostdef None None ~> exta THEN exta=None.
  Proof.
    wlp_simplify.
  Qed.

  Lemma f_imp_mostdef_l: forall a,
    WHEN f_imp_mostdef a None ~> a' THEN a = a'.
  Proof.
    wlp_simplify.
  Qed.
  Local Hint Resolve f_imp_mostdef_l: wlp.

  Lemma f_imp_mostdef_r: forall a,
    WHEN f_imp_mostdef None a ~> a' THEN a = a'.
  Proof.
    wlp_simplify.
  Qed.
  Local Hint Resolve f_imp_mostdef_r: wlp.

  Let combine_imp_mostdef_l := imp_map_filter1 (fun a => f_imp_mostdef (Some a) None).
  Let combine_imp_mostdef_r := imp_map_filter1 (fun a => f_imp_mostdef None (Some a)).

  Definition imp_f2 (o1 o2: option A): ?? (option A) :=
    match o1, o2 with
    | None, None => RET None
    | _, _ => DO fc <~ f_imp_mostdef o1 o2;; RET fc
    end.

  Let combine_imp_mostdef_nonopt (m1 m2: tree A) : ?? (tree A) :=
    tree_rec2
      (RET Empty)
      combine_imp_mostdef_r
      combine_imp_mostdef_l
      (fun l1 o1 r1 l2 o2 r2 olrec orrec =>
        DO lrec <~ olrec;;
        DO rrec <~ orrec;;
        DO oa <~ imp_f2 o1 o2;;
        RET (Node lrec oa rrec))
      m1 m2.

  Definition combine_imp_mostdef :=
    Eval cbv [combine_imp_mostdef_nonopt tree_rec2 tree_rec2'] in combine_imp_mostdef_nonopt.

  Lemma gcombine_imp_mostdef_l_eq: forall m i,
    WHEN combine_imp_mostdef_l m ~> fm THEN
    get i fm = get i m.
  Proof.
    unfold combine_imp_mostdef_l; intros; wlp_simplify.
    eapply gimp_map_filter1 in Hexta as ->. reflexivity.
    autodestruct; eauto with wlp.
  Qed.

  Lemma gcombine_imp_mostdef_r_eq: forall m i,
    WHEN combine_imp_mostdef_r m ~> fm THEN
    get i fm = get i m.
  Proof.
    unfold combine_imp_mostdef_r; intros; wlp_simplify.
    eapply gimp_map_filter1 in Hexta as ->. reflexivity.
    autodestruct; eauto with wlp.
  Qed.

  Lemma gcombine_imp_mostdef_l: forall m oa i,
    WHEN combine_imp_mostdef_l m ~> fm THEN
    get i m = oa ->
    get i fm = oa.
  Proof.
    repeat intro; erewrite gcombine_imp_mostdef_l_eq; eassumption.
  Qed.

  Lemma gcombine_imp_mostdef_r: forall m oa i,
    WHEN combine_imp_mostdef_r m ~> fm THEN
    get i m = oa ->
    get i fm = oa.
  Proof.
    repeat intro; erewrite gcombine_imp_mostdef_r_eq; eassumption.
  Qed.

  Lemma gcombine_imp_mostdef_l_rev: forall m oa i,
    WHEN combine_imp_mostdef_l m ~> fm THEN
    get i fm = oa ->
    get i m = oa.
  Proof.
    repeat intro; erewrite <- gcombine_imp_mostdef_l_eq; eassumption.
  Qed.

  Lemma gcombine_imp_mostdef_r_rev: forall m oa i,
    WHEN combine_imp_mostdef_r m ~> fm THEN
    get i fm = oa ->
    get i m = oa.
  Proof.
    repeat intro; erewrite <- gcombine_imp_mostdef_r_eq; eassumption.
  Qed.
  
  Theorem gcombine_imp_mostdef_spec:
    forall (m1 m2 : t A),
    WHEN combine_imp_mostdef m1 m2 ~> m3 THEN
    forall (i : elt),
    p_mostdef (fun a1 a2 a3 => imp_mostdef a1 a2 ~~> a3) (get i m1) (get i m2) (get i m3).
  Proof.
    change combine_imp_mostdef with combine_imp_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - wlp_simplify; constructor.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_EN by auto.
      wlp_simplify.
      eapply gcombine_imp_mostdef_r_eq in Hexta as ->.
      case get; constructor.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NE by auto.
      wlp_simplify.
      eapply gcombine_imp_mostdef_l_eq in Hexta as ->.
      case get; constructor.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NN by auto.
      wlp_simplify.
      all: rewrite !gNode; destruct i;
           [ eapply IHm0 | eapply IHm1 | constructor]; eauto.
  Qed.

  Hypothesis imp_mostdef_determ: forall a1 a2,
    WHEN imp_mostdef a1 a2 ~> exta1 THEN
    WHEN imp_mostdef a1 a2 ~> exta2 THEN
    exta1 = exta2.

  Lemma f_imp_mostdef_lr: forall a1 a2,
    WHEN f_imp_mostdef (Some a1) (Some a2) ~> oa3 THEN
    oa3 <> None.
  Proof.
    wlp_simplify; inv H0; auto.
  Qed.
  Local Hint Resolve f_imp_mostdef_lr: wlp.

  Lemma f_imp_mostdef_determ: forall oa1 oa2,
    WHEN f_imp_mostdef oa1 oa2 ~> exta1 THEN
    WHEN f_imp_mostdef oa1 oa2 ~> exta2 THEN
    exta1 = exta2.
  Proof.
    wlp_simplify.
  Qed.
  Opaque f_imp_mostdef.

  Theorem gcombine_imp_mostdef_or_ok:
      forall (m1 m2: t A) (a1 a2: A) (i: positive),
      WHEN combine_imp_mostdef m1 m2 ~> m3 THEN
      (forall a1 a2, WHEN f_imp_mostdef (Some a1) (Some a2) ~> oa
      THEN Some a1 = oa /\ Some a2 = oa) ->
      get i m1 = Some a1 \/ get i m2 = Some a1 ->
      get i m3 = Some a2 -> a1=a2.
  Proof.
    change combine_imp_mostdef with combine_imp_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - wlp_simplify; inv H1.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_EN by auto.
      wlp_simplify; [ inv H3 |]. eapply gcombine_imp_mostdef_r in H3; eauto.
      rewrite H2 in H3; inv H3; auto.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NE by auto.
      wlp_simplify; [| inv H3 ]. eapply gcombine_imp_mostdef_l in H3; eauto.
      rewrite H2 in H3; inv H3; auto.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NN by auto.
      wlp_simplify.
      all:
        rewrite gNode in H5; rewrite gNode in H6; destruct i;
        [ eapply IHm0; eauto | eapply IHm1; eauto | inv H6 ].
      + destruct o0.
        * exploit H3; eauto. intros (HA & _); inv HA; auto.
        * exploit f_imp_mostdef_l; eauto. intros HA; inv HA; auto.
      + exploit H3; eauto. intros (_ & HA); inv HA; auto.
      + inv H5; auto.
    Unshelve. all: eauto.
  Qed.

  Theorem gcombine_imp_mostdef_and_ok:
      forall (m1 m2: t A) (a1 a2: A) (i: positive),
      WHEN combine_imp_mostdef m1 m2 ~> m3 THEN
      (forall a1 a2, WHEN f_imp_mostdef (Some a1) (Some a2) ~> oa
      THEN Some a1 = oa /\ Some a2 = oa) ->
      get i m1 = Some a1 /\ get i m2 = Some a2 ->
      a1=a2.
  Proof.
    change combine_imp_mostdef with combine_imp_mostdef_nonopt.
    induction m1 using tree_ind; induction m2 using tree_ind; intros.
    - wlp_simplify; inv H1.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_EN by auto.
      wlp_simplify; inv H2.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NE by auto.
      wlp_simplify; inv H3.
    - unfold combine_imp_mostdef_nonopt; rewrite unroll_tree_rec2_NN by auto.
      wlp_simplify.
      all:
        rewrite gNode in H5; rewrite gNode in H6; destruct i;
        [ eapply IHm0; eauto | eapply IHm1; eauto | inv H6 ].
      + inv H5; exploit H3; eauto. intros (HL & HR); inv HL; inv H1; auto.
      + inv H5.
    Unshelve. all: eauto.
  Qed.

  Theorem gcombine_imp_mostdef_none:
      forall (m1 m2: t A) (i: positive),
      WHEN combine_imp_mostdef m1 m2 ~> m3 THEN
      get i m1 = None /\ get i m2 = None ->
      get i m3 = None.
  Proof.
    intros; intros m3 CMB (GET1 & GET2).
    apply gcombine_imp_mostdef_spec in CMB.
    specialize (CMB i); rewrite GET1, GET2 in CMB.
    inv CMB; reflexivity.
  Qed.

  Theorem gcombine_imp_mostdef_none_rev:
      forall (m1 m2: t A) (i: positive),
      WHEN combine_imp_mostdef m1 m2 ~> m3 THEN
      get i m3 = None ->
      get i m1 = None /\ get i m2 = None.
  Proof.
    intros; intros m3 CMB GET.
    apply gcombine_imp_mostdef_spec in CMB.
    specialize (CMB i); rewrite GET in CMB.
    inv CMB; auto.
  Qed.

  End IMPURE_MOSTDEF_COMBINE.

  Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    f None None = None -> g None None = None ->
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros. apply extensionality; intros i. rewrite ! gcombine by auto. auto.
  Qed.

(** ** List of all bindings *)

  Fixpoint xelements' {A} (m : tree' A) (i: positive) (k: list (positive * A))
                     {struct m} : list (positive * A) :=
    match m with
    | Node001 r => xelements' r (xI i) k
    | Node010 x => (prev i, x) :: k
    | Node011 x r => (prev i, x) :: xelements' r (xI i) k
    | Node100 l => xelements' l (xO i) k
    | Node101 l r => xelements' l (xO i) (xelements' r (xI i) k)
    | Node110 l x => xelements' l (xO i) ((prev i, x)::k)
    | Node111 l x r => xelements' l (xO i) ((prev i, x):: (xelements' r (xI i) k))
    end.

  Definition elements {A} (m : t A) : list (positive * A) := 
    match m with Empty => nil | Nodes m' => xelements' m' xH nil end.

  Definition xelements {A} (m : t A) (i: positive) : list (positive * A) := 
    match m with Empty => nil | Nodes m' => xelements' m' i nil end.

  Lemma xelements'_append:
    forall A (m: tree' A) i k1 k2,
    xelements' m i (k1 ++ k2) = xelements' m i k1 ++ k2.
  Proof.
    induction m; intros; simpl; auto.
  - f_equal; auto.
  - rewrite IHm2, IHm1. auto.
  - rewrite <- IHm. auto.
  - rewrite IHm2, <- IHm1. auto.
  Qed.

  Lemma xelements_Node:
    forall A (l: tree A) (o: option A) (r: tree A) i,
    xelements (Node l o r) i =
       xelements l (xO i)
    ++ match o with None => nil | Some v => (prev i, v) :: nil end
    ++ xelements r (xI i).
  Proof.
    Local Transparent Node.
    intros; destruct l, o, r; simpl; rewrite <- ? xelements'_append; auto.
  Qed.

  Lemma xelements_correct:
    forall A (m: tree A) i j v,
    get i m = Some v -> In (prev (prev_append i j), v) (xelements m j).
  Proof.
    intros A. induction m using tree_ind; intros.
  - discriminate.
  - rewrite xelements_Node, ! in_app. rewrite gNode in H0. destruct i.
    + right; right. apply (IHm2 i (xI j)); auto.
    + left. apply (IHm1 i (xO j)); auto.
    + right; left. subst o. rewrite prev_append_prev. auto with coqlib.
  Qed.

  Theorem elements_correct:
    forall A (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    generalize (xelements_correct m i xH H). rewrite prev_append_prev. auto.
  Qed.

  Lemma in_xelements:
    forall A (m: tree A) (i k: positive) (v: A) ,
    In (k, v) (xelements m i) ->
    exists j, k = prev (prev_append j i) /\ get j m = Some v.
  Proof.
    intros A. induction m using tree_ind; intros.
  - elim H.
  - rewrite xelements_Node, ! in_app in H0. destruct H0 as [P | [P | P]].
    + exploit IHm1; eauto. intros (j & Q & R). exists (xO j); rewrite gNode; auto.
    + destruct o; simpl in P; intuition auto. inv H0. exists xH; rewrite gNode; auto.
    + exploit IHm2; eauto. intros (j & Q & R). exists (xI j); rewrite gNode; auto.
  Qed.

  Theorem elements_complete:
    forall A (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros A m i v H. exploit in_xelements; eauto. intros (j & P & Q).
    rewrite prev_append_prev in P. change i with (prev_append 1 i) in P.
    exploit prev_append_inj; eauto. intros; congruence.
  Qed.

  Definition xkeys {A} (m: t A) (i: positive) := List.map fst (xelements m i).

  Lemma xkeys_Node:
    forall A (m1: t A) o (m2: t A) i,
    xkeys (Node m1 o m2) i =
       xkeys m1 (xO i)
    ++ match o with None => nil | Some v => prev i :: nil end
    ++ xkeys m2 (xI i).
  Proof.
    intros. unfold xkeys. rewrite xelements_Node, ! map_app. destruct o; auto.
  Qed.

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k: positive),
    In k (xkeys m i) ->
    (exists j, k = prev (prev_append j i)).
  Proof.
    unfold xkeys; intros.
    apply (list_in_map_inv) in H. destruct H as ((j, v) & -> & H).
    exploit in_xelements; eauto. intros (k & P & Q). exists k; auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive),
    list_norepet (xkeys m i).
  Proof.
    intros A; induction m using tree_ind; intros.
  - constructor.
  - assert (NOTIN1: ~ In (prev i) (xkeys l (xO i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (NOTIN2: ~ In (prev i) (xkeys r (xI i))).
    { red; intros. exploit in_xkeys; eauto. intros (j & EQ).
      rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (DISJ: forall x, In x (xkeys l (xO i)) -> In x (xkeys r (xI i)) -> False).
    { intros. exploit in_xkeys. eexact H0. intros (j1 & EQ1).
      exploit in_xkeys. eexact H1. intros (j2 & EQ2).
      rewrite prev_append_prev in *. simpl in *. rewrite EQ2 in EQ1. apply prev_append_inj in EQ1. discriminate. }
    rewrite xkeys_Node. apply list_norepet_append. auto.
    destruct o; simpl; auto. constructor; auto.
    red; intros. red; intros; subst y. destruct o; simpl in H1.
    destruct H1. subst x. tauto. eauto. eauto.
  Qed.

  Theorem elements_keys_norepet:
    forall A (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. apply (xelements_keys_norepet m xH).
  Qed.

  Remark xelements_empty:
    forall A (m: t A) i, (forall i, get i m = None) -> xelements m i = nil.
  Proof.
    intros. replace m with (@Empty A). auto.
    apply extensionality; intros. symmetry; auto.
  Qed.

  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i, option_rel R (get i m) (get i n)) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until n.
    change (elements m) with (xelements m xH). change (elements n) with (xelements n xH).
    generalize 1%positive. revert m n.
    induction m using tree_ind; [ | induction n using tree_ind]; intros until p; intros REL.
  - replace n with (@Empty B). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - replace (Node l o r) with (@Empty A). constructor.
    apply extensionality; intros. specialize (REL i). simpl in *. inv REL; auto.
  - rewrite ! xelements_Node. repeat apply list_forall2_app.
    + apply IHm. intros. specialize (REL (xO i)). rewrite ! gNode in REL; auto.
    + specialize (REL xH). rewrite ! gNode in REL. inv REL; constructor; auto using list_forall2_nil.
    + apply IHm0. intros. specialize (REL (xI i)). rewrite ! gNode in REL; auto.
  Qed.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros. apply elements_canonical_order'.
    intros. destruct (get i m) as [x|] eqn:GM.
    exploit H; eauto. intros (y & P & Q). rewrite P; constructor; auto.
    destruct (get i n) as [y|] eqn:GN.
    exploit H0; eauto. intros (x & P & Q). congruence.
    constructor.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    intros. replace n with m; auto. apply extensionality; auto.
  Qed.

  Lemma xelements_set:
    forall A v v' (m: t A) i j,
    get i m = Some v ->
    exists l1 l2,
    xelements m j = l1 ++ (prev (prev_append i j), v) :: l2
    /\ xelements (set i v' m) j = l1 ++ (prev (prev_append i j), v') :: l2.
  Proof.
    intros A; induction m using tree_ind; intros.
  - discriminate.
  - assert (SET: set i v' (Node l o r) =
                    match i with
                    | xH => Node l (Some v') r
                    | xO ii => Node (set ii v' l) o r
                    | xI ii => Node l o (set ii v' r)
                    end).
    { destruct l, o, r, i; reflexivity. }
    rewrite gNode in H0. rewrite SET. destruct i; rewrite ! xelements_Node.
    + destruct (IHm0 i (xI j) H0) as (l1 & l2 & EQ & EQ').
      exists (xelements l (xO j) ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              l1);
      exists l2; split.
      rewrite EQ, ! app_ass. auto.
      rewrite EQ', ! app_ass. auto.
    + destruct (IHm i (xO j) H0) as (l1 & l2 & EQ & EQ').
      exists l1;
      exists (l2 ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              xelements r (xI j));
      split.
      rewrite EQ, ! app_ass. auto.
      rewrite EQ', ! app_ass. auto.
    + subst o. exists (xelements l (xO j)); exists (xelements r (xI j)); split.
      rewrite prev_append_prev. auto.
      auto.
  Qed.

  Theorem elements_set:
    forall A i v v' (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (set i v' m) = l1 ++ (i,v') :: l2.
  Proof.
    intros. exploit xelements_set. eauto. instantiate (2 := xH).
    rewrite prev_append_prev. eauto.
  Qed.

  Lemma xelements_remove:
    forall A v (m: t A) i j,
    get i m = Some v ->
    exists l1 l2,
    xelements m j = l1 ++ (prev (prev_append i j), v) :: l2
    /\ xelements (remove i m) j = l1 ++ l2.
  Proof.
    intros A; induction m using tree_ind; intros.
  - discriminate.
  - assert (REMOVE: remove i (Node l o r) =
                    match i with
                    | xH => Node l None r
                    | xO ii => Node (remove ii l) o r
                    | xI ii => Node l o (remove ii r)
                    end).
    { destruct l, o, r, i; reflexivity. }
    rewrite gNode in H0. rewrite REMOVE. destruct i; rewrite ! xelements_Node.
    + destruct (IHm0 i (xI j) H0) as (l1 & l2 & EQ & EQ').
      exists (xelements l (xO j) ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              l1);
      exists l2; split.
      * rewrite EQ, ! app_assoc. auto.
      * rewrite EQ', ! app_assoc. auto.
    + destruct (IHm i (xO j) H0) as (l1 & l2 & EQ & EQ').
      exists l1;
      exists (l2 ++
              match o with None => nil | Some x => (prev j, x) :: nil end ++
              xelements r (xI j));
      split.
      * rewrite EQ, <- ! app_assoc. auto.
      * rewrite EQ', <- ! app_assoc. auto.
    + subst o. exists (xelements l (xO j)); exists (xelements r (xI j)); split.
      rewrite prev_append_prev. auto.
      auto.
  Qed.

  Theorem elements_remove:
    forall A i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
    intros. exploit xelements_remove. eauto. instantiate (1 := xH).
    rewrite prev_append_prev. auto.
  Qed.

  Lemma elements_xelements {A} : forall (m: t A),
      elements m = xelements m xH.
  Proof.
    intros []; auto.
  Qed.

  Lemma elements_filter: forall A (pred: positive -> A -> bool) (m: t A),
      elements (filter pred m) = List.filter (fun x => pred (fst x) (snd x)) (elements m).
  Proof.
    destruct m; simpl; auto. unfold elements.
    assert (List.filter (fun x => pred (fst x) (snd x)) (@nil _) = (@nil _)) as NIL by constructor.
    rewrite <-NIL. rewrite NIL at 1.
    generalize (@nil (positive * A)) as acc. generalize xH as x.
    induction t0; simpl; intros;
      repeat
        (match goal with
         | H: forall x acc, match filter' _ ?t0 _ with | _ => _ end = _
           |- context [(filter' ?pred ?t0 ?x)] =>
             let FILTER := fresh "FILTER" in
             destruct (filter' pred t0 x) eqn:FILTER;
             let H' := fresh "SPEC" in
             specialize (H x) as H'; setoid_rewrite FILTER in H'; try rewrite <-H'
         | |- context [(if (pred _ _) then _ else _)] =>
             destruct (pred _ _) eqn:P; try setoid_rewrite P
         end; simpl; eauto).
  Qed.

(** ** Folding over a tree *)

  Fixpoint fold' {A B} (f: B -> positive -> A -> B)
                 (i: positive) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold' f (xI i) r v
    | Node010 x => f v (prev i) x
    | Node011 x r => fold' f (xI i) r (f v (prev i) x)
    | Node100 l => fold' f (xO i) l v
    | Node101 l r => fold' f (xI i) r (fold' f (xO i) l v)
    | Node110 l x => f (fold' f (xO i) l v) (prev i) x
    | Node111 l x r => fold' f (xI i) r (f (fold' f (xO i) l v) (prev i) x)
    end.

  Definition fold {A B} (f: B -> positive -> A -> B) (m: t A) (v: B) :=
   match m with Empty => v | Nodes m' => fold' f xH m' v end.

  Lemma fold'_xelements':
    forall A B (f: B -> positive -> A -> B) m i v l,
    List.fold_left (fun a p => f a (fst p) (snd p)) l (fold' f i m v) =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements' m i l) v.
  Proof.
    induction m; intros; simpl; auto.
    rewrite <- IHm1, <- IHm2; auto.
    rewrite <- IHm; auto.
    rewrite <- IHm1. simpl. rewrite <- IHm2; auto.
  Qed.

  Theorem fold_spec:
    forall A B (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros. unfold fold, elements. destruct m; auto. rewrite <- fold'_xelements'. auto.
  Qed.

  Fixpoint fold1' {A B} (f: B -> A -> B) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => fold1' f r v
    | Node010 x => f v x
    | Node011 x r => fold1' f r (f v x)
    | Node100 l => fold1' f l v
    | Node101 l r => fold1' f r (fold1' f l v)
    | Node110 l x => f (fold1' f l v) x
    | Node111 l x r => fold1' f r (f (fold1' f l v) x)
    end.


  Definition fold1 {A B} (f: B -> A -> B) (m: t A) (v: B) : B :=
    match m with Empty => v | Nodes m' => fold1' f m' v end.

  Lemma fold1'_xelements':
    forall A B (f: B -> A -> B) m i v l,
    List.fold_left (fun a p => f a (snd p)) l (fold1' f m v) =
    List.fold_left (fun a p => f a (snd p)) (xelements' m i l) v.
  Proof.
    induction m; simpl; intros; auto.
    rewrite <- IHm1. rewrite <- IHm2. auto.
    rewrite <- IHm. auto. 
    rewrite <- IHm1. simpl. rewrite <- IHm2. auto.
  Qed.

  Theorem fold1_spec:
    forall A B (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. destruct m as [|m]. reflexivity.
    apply fold1'_xelements' with (l := @nil (positive * A)).
  Qed.

  Local Open Scope positive.
  Lemma set_disjoint1:
    forall (A: Type)(i d : elt) (m: t A)  (x y: A),
      set (i + d) y (set i x m) = set i x (set (i + d) y m).
  Proof.
    intros.
    apply extensionality.
    intro j.
    destruct (peq j i) as [EQ_i_j | NEQ_j_i].
    - subst i.
      rewrite gss.
      rewrite gso by lia.
      apply gss.
    - rewrite (gso _ _ NEQ_j_i).
      destruct (peq j (i + d)) as [EQ | NEQ].
      + subst j.
        rewrite gss.
        rewrite gss.
        reflexivity.
      + rewrite (gso _ _ NEQ).
        rewrite (gso _ _ NEQ).
        apply (gso _ _ NEQ_j_i).
  Qed.
  
  Local Open Scope positive.
  Lemma set_disjoint:
    forall (A: Type)(i j : elt) (m: t A)  (x y: A),
      i <> j ->
      set j y (set i x m) = set i x (set j y m).
  Proof.
    intros.
    destruct (Pos.compare_spec i j) as [Heq | Hlt | Hlt].
    { congruence. }
    {
      rewrite (Pos.lt_iff_add i j) in Hlt.
      destruct Hlt as [d Hd].
      subst j.
      apply set_disjoint1.
    }
      rewrite (Pos.lt_iff_add j i) in Hlt.
      destruct Hlt as [d Hd].
      subst i.
      symmetry.
      apply set_disjoint1.
  Qed.

  Arguments empty A : simpl never.
  Arguments get {A} p m : simpl never.
  Arguments set {A} p x m : simpl never.
  Arguments remove {A} p m : simpl never.
End PTree.

(** * An implementation trees of qualified identifiers *)

Module PTree_rec.

Fixpoint t (n:nat) (A: Type): Type :=
   match n with
   | O => unit
   | S n => PTree.t (option A * t n A)
   end.

Definition empty {A:Type} {n:nat} : t n A :=
  match n with
  | O => tt
  | S n' => @PTree.empty _
  end.

Fixpoint get {A:Type} {n:nat} (key: list positive): (t n A) -> option A :=
   match n with
   | O => fun _ => None
   | S n' =>
     fun map => match key with
     | nil => None
     | cons p k => SOME m <- PTree.get p map IN
                   match k with
                   | nil => fst m
                   | _ => get k (snd m)
                   end
     end
   end.

Fixpoint set {A:Type} {n:nat} (key: list positive) (v: A): (t n A) -> (t n A) :=
   match n return (t n A) -> (t n A) with
   | O => fun t => t
   | S n' =>
     fun map => match key with
             | nil => map
             | cons p k =>
                 let prev := match PTree.get p map with
                             | None => (None, empty)
                             | Some prev => prev
                             end in
                 PTree.set p (match k with
                              | nil => (Some v, snd prev)
                              | _ => (fst prev, set k v (snd prev))
                              end)
                           map
             end
   end.

Open Scope nat.

Fact get_length :
  forall A n i (m: t n A) v, get i m = Some v -> 0 < length i <= n.
Proof.
  induction n; intros * GET; simpl in *; [inv GET|].
  destruct i as [|?[|]]; simpl in *; try congruence; try lia.
  destruct (PTree.get p m) eqn:GET'; setoid_rewrite GET' in GET; [|inv GET].
  apply IHn in GET. simpl in *. lia.
Qed.

Lemma gempty : forall A n i, get i (@empty A n) = None.
Proof.
  induction n; intros; simpl; auto.
  destruct i as [|?[|]]; auto.
Qed.

Lemma gss : forall A n i x (m: t n A),
    0 < length i <= n ->
    get i (set i x m) = Some x.
Proof.
  induction n; intros; simpl.
  - lia.
  - destruct i as [|?[|]]; simpl in *; auto.
    + lia.
    + rewrite PTree.gss; simpl; auto.
    + rewrite PTree.gss; simpl.
      rewrite IHn; auto. simpl. lia.
Qed.

Lemma gso : forall A n i j x (m: t n A),
    i <> j ->
    get i (set j x m) = get i m.
Proof.
  induction n; intros; simpl; auto.
  destruct i as [|?[|]], j as [|?[|]]; simpl in *; try congruence.
  all:rewrite PTree.gsspec; auto.
  all:match goal with
      | |- context [peq ?p1 ?p2] => destruct (peq p1 p2); subst; try congruence; simpl
      end.
  - destruct (PTree.get _ _); auto.
  - destruct (PTree.get _ _); simpl; auto.
    apply gempty.
  - rewrite IHn; [|congruence].
    destruct (PTree.get _ _); simpl; auto.
    apply gempty.
Qed.

Fixpoint remove {A:Type} {n:nat} (key: list positive): (t n A) -> (t n A) :=
   match n return (t n A) -> (t n A) with
   | O => fun t => t
   | S n' =>
     fun map => match key with
             | nil => map
             | cons p k =>
                 match PTree.get p map with
                 | Some t =>
                     PTree.set p
                       (match k with
                        | nil => (None, snd t)
                        | _ => (fst t, remove k (snd t))
                        end) map
                 | None => map
                 end
             end
   end.

Lemma grs : forall A n i (m: t n A),
    get i (remove i m) = None.
Proof.
  induction n; intros; simpl; auto.
  destruct i; simpl in *; auto.
  destruct (PTree.get p m) eqn:GET; setoid_rewrite GET.
  - rewrite PTree.gss.
    destruct i; simpl; auto.
  - now setoid_rewrite GET.
Qed.

Lemma gro : forall A n i j (m: t n A),
    i <> j ->
    get i (remove j m) = get i m.
Proof.
  induction n; intros; simpl; auto.
  destruct i, j; simpl in *; try congruence.
  destruct (PTree.get p0 m) eqn:GET; setoid_rewrite GET; auto.
  rewrite PTree.gsspec; auto.
  destruct (peq p p0); subst; auto. setoid_rewrite GET.
  destruct i, j; simpl; auto; try congruence.
  rewrite IHn; auto. congruence.
Qed.

Import ListNotations.

Fixpoint map' {A B: Type} {n:nat} (f: list positive -> A -> B) xs : (t n A) -> (t n B) :=
  match n return (t n A) -> (t n B) with
  | O => fun tt => tt
  | S n' => fun t =>
             PTree.map (fun x t =>
                          let xs' := List.app xs [x] in
                          (option_map (f xs') (fst t), map' f xs' (snd t))) t
  end.
Definition map {A B: Type} {n:nat} (f: list positive -> A -> B) := @map' A B n f nil.

Lemma gmap' : forall A B n (f: _ -> A -> B) i xs (m : t n A),
    get i (map' f xs m) = option_map (f (xs ++ i)) (get i m).
Proof.
  induction n; intros; simpl; auto.
  destruct i; simpl; auto.
  rewrite PTree.gmap.
  destruct (PTree.get p m) eqn:GET; setoid_rewrite GET; simpl; auto.
  destruct i; simpl; auto.
  rewrite IHn, <-app_assoc; auto.
Qed.

Corollary gmap : forall A B n (f: _ -> A -> B) i (m : t n A),
    get i (map f m) = option_map (f i) (get i m).
Proof. intros. apply gmap'. Qed.

Fixpoint map1 {A B: Type} {n:nat} (f: A -> B) : (t n A) -> (t n B) :=
  match n return (t n A) -> (t n B) with
  | O => fun tt => tt
  | S n' => fun t =>
             PTree.map (fun _ t => (option_map f (fst t), map1 f (snd t))) t
  end.

Lemma gmap1 : forall A B n (f: A -> B) i (m : t n A),
    get i (map1 f m) = option_map f (get i m).
Proof.
  induction n; intros; simpl; auto.
  destruct i; simpl; auto.
  rewrite PTree.gmap.
  destruct (PTree.get p m) eqn:GET; setoid_rewrite GET; simpl; auto.
  destruct i; auto.
Qed.

Fixpoint combine {A B C: Type} {n:nat} (f: option A -> option B -> option C) : t n A -> t n B -> t n C :=
  match n return t n A -> t n B -> t n C with
  | O => fun _ _ => tt
  | S n' =>
      PTree.combine (fun ot1 ot2 =>
                       match ot1, ot2 with
                       | Some t1, Some t2 => Some (f (fst t1) (fst t2), combine f (snd t1) (snd t2))
                       | Some t1, None => Some (f (fst t1) None, combine f (snd t1) empty)
                       | None, Some t2 => Some (f None (fst t2), combine f empty (snd t2))
                       | None, None => None
                       end)
  end.

Lemma gcombine : forall A B C n (f: _ -> _ -> option C),
    f None None = None ->
    forall (m1: t n A) (m2: t n B) i,
      get i (combine f m1 m2) = f (get i m1) (get i m2).
Proof.
  intros * F.
  induction n; intros; simpl; auto.
  destruct i; auto.
  rewrite PTree.gcombine; auto.
  destruct (PTree.get _ m1) eqn:EQ1, (PTree.get _ m2) eqn:EQ2.
  all:fold t in *; rewrite EQ1, EQ2; auto.
  all:destruct i; simpl; auto.
  1,2:rewrite IHn, gempty; auto.
Qed.

Definition f_mostdef {A:Type} := @PTree.f_mostdef A.

Fixpoint combine_mostdef {A: Type} {n:nat} (f: A -> A -> option A) : t n A -> t n A -> option (t n A) :=
  match n return t n A -> t n A -> option (t n A) with
  | O => fun _ _ => Some tt
  | S n' => PTree.combine_mostdef
             (fun t1 t2 =>
                SOME v <- f_mostdef f (fst t1) (fst t2) IN
                SOME t <- combine_mostdef f (snd t1) (snd t2) IN
                Some (v, t))
  end.

Lemma gcombine_mostdef : forall A n (mostdef : A -> A -> option A) (m1 m2 m3 : t n A) a i,
  combine_mostdef mostdef m1 m2 = Some m3 ->
  f_mostdef mostdef (get i m1) (get i m2) = Some a ->
  get i m3 = a.
Proof.
  induction n; intros * COMB MD; simpl in *; try congruence.
  destruct i; simpl in *; try congruence.
  destruct (PTree.get p m3) as [(?&t3)|] eqn:M3; setoid_rewrite M3.
  2:{ eapply PTree.gcombine_mostdef_none_rev in COMB as (M1&M2); eauto.
      setoid_rewrite M1 in MD. setoid_rewrite M2 in MD. simpl in MD.
      congruence. }
  eapply PTree.gcombine_mostdef_ok in COMB as OK; eauto.
  destruct (PTree.get p m1) as [(?&t1)|] eqn:M1; destruct (PTree.get p m2) as [(?&t2)|] eqn:M2; destruct i.
  all:(setoid_rewrite M1 in MD; setoid_rewrite M2 in MD; simpl in * ).
  all:try destruct (f_mostdef _ o0 o1) eqn:MD'; simpl in *; try congruence.
  all:try destruct (combine_mostdef _ t1 t2) eqn:COMB'; simpl in *; try congruence.
  all:try inv OK.
  1:eapply IHn; eauto.
  all:match goal with
      | |- ?o = _ => destruct o; simpl in *; congruence
      end.
Qed.

Lemma fcombine_mostdef : forall A n (mostdef : A -> A -> option A) (m1 m2 : t n A),
    combine_mostdef mostdef m1 m2 = None ->
    (forall i (a1 a2 : A),
        0 < length i <= n -> get i m1 = Some a1 -> get i m2 = Some a2 -> mostdef a1 a2 <> None) -> False.
Proof.
  induction n; intros * COMB GETS; simpl in *; [inv COMB|].
  apply PTree.fcombine_mostdef in COMB; auto.
  intros * GET1 GET2.
  destruct (f_mostdef mostdef (fst a1) (fst a2)) eqn:MD.
  destruct (combine_mostdef mostdef (snd a1) (snd a2)) eqn:COMB'; try congruence.
  - exfalso.
    eapply IHn in COMB'; eauto.
    intros * LEN GET1' GET2'.
    eapply GETS with (i:=i::i0); eauto.
    + simpl. lia.
    + setoid_rewrite GET1. destruct i0; simpl in *; auto; lia.
    + setoid_rewrite GET2. destruct i0; simpl in *; auto; lia.
  - exfalso.
    destruct a1 as ([|]&?), a2 as ([|]&?); simpl in *; try congruence.
    specialize (GETS [i] a a0); simpl in *.
    eapply GETS.
    + lia.
    + now setoid_rewrite GET1.
    + now setoid_rewrite GET2.
    + destruct (mostdef a a0); simpl in *; congruence.
Qed.

Lemma gcombine_mostdef_ok : forall A n (mostdef : A -> A -> option A) (m1 m2 m3 : t n A) i a,
    combine_mostdef mostdef m1 m2 = Some m3 ->
    get i m3 = Some a -> f_mostdef mostdef (get i m1) (get i m2) = Some (Some a).
Proof.
  induction n; intros * COMB GET; simpl in *; [congruence|].
  destruct i; simpl in *; [congruence|].
  destruct (PTree.get p m3) as [(?&t3)|] eqn:M3; setoid_rewrite M3 in GET; [|congruence].
  eapply PTree.gcombine_mostdef_ok in COMB; eauto.
  destruct (PTree.get p m1) eqn:M1, (PTree.get p m2) eqn:M2.
  all:(setoid_rewrite M1; setoid_rewrite M2; simpl in *; try congruence).
  - destruct (f_mostdef _ (fst p0) (fst p1)) eqn:MD'; simpl in *; try congruence.
    destruct (combine_mostdef _ (snd p0) (snd p1)) eqn:COMB'; simpl in *; try congruence.
    inv COMB.
    destruct i; subst; eauto.
  - inv COMB. destruct i; simpl in *; now rewrite GET.
  - inv COMB. destruct i; simpl in *; now rewrite GET.
Qed.

Lemma gcombine_mostdef_only_l :
  forall A n (mostdef : A -> A -> option A) (m1 : t n A),
    combine_mostdef mostdef m1 empty = Some m1.
Proof.
  induction n; intros; simpl.
  - now destruct m1.
  - now rewrite PTree.gcombine_mostdef_only_l.
Qed.

Lemma gcombine_mostdef_none_rev :
  forall A n (mostdef : A -> A -> option A) (m1 m2 m3 : t n A) i,
    combine_mostdef mostdef m1 m2 = Some m3 ->
    get i m3 = None -> get i m1 = None /\ get i m2 = None.
Proof.
  induction n; intros * COMB GET; simpl in *; auto.
  destruct i; simpl in *; auto.
  destruct (PTree.get p m3) eqn:M3; setoid_rewrite M3 in GET.
  - eapply PTree.gcombine_mostdef_ok in COMB; eauto.
    destruct (PTree.get p m1) eqn:M1; destruct (PTree.get p m2) eqn:M2; simpl in *; try congruence.
    all:(setoid_rewrite M1; setoid_rewrite M2).
    + destruct (f_mostdef _ _ _) eqn:MD'; simpl in *; try congruence.
      destruct (combine_mostdef _ _ _) eqn:COMB'; simpl in *; try congruence.
      inv COMB. destruct i; simpl in *; eauto.
      destruct p1 as ([|]&?), p2 as ([|]&?); simpl in *; try congruence; auto.
      destruct (mostdef a a0); congruence.
    + inv COMB. auto.
    + inv COMB. auto.
  - eapply PTree.gcombine_mostdef_none_rev in COMB as (M1&M2); eauto.
    setoid_rewrite M1; setoid_rewrite M2; auto.
Qed.

Fixpoint elements {A: Type} {n} : t n A -> list (list positive * A) :=
  match n return t n A -> _ with
  | O => fun _ => nil
  | S _ => fun t1 =>
            List.flat_map
              (fun xv =>
                 let l := List.map (fun xsv => (fst xv::fst xsv, snd xsv)) (elements (snd (snd xv))) in
                 match fst (snd xv) with
                 | Some v => ([fst xv], v)::l
                 | None => l
                 end)
              (PTree.elements t1)
  end.

Lemma elements_correct :
  forall (A : Type) n (m : t n A) i (v : A), get i m = Some v -> In (i, v) (elements m).
Proof.
  induction n; intros * GET; simpl in *.
  - inv GET.
  - destruct i; simpl in *; [inv GET|].
    destruct (PTree.get p m) eqn:GET'; setoid_rewrite GET' in GET; [|inv GET].
    apply in_flat_map; do 2 esplit; eauto using PTree.elements_correct.
    destruct p0; simpl in *.
    destruct o; (destruct i; [inv GET|]); auto with datatypes.
    right. 1,2:eapply in_map_iff; do 2 esplit; eauto; auto.
Qed.

Lemma elements_complete :
  forall (A : Type) n (m : t n A) i (v : A), In (i, v) (elements m) -> get i m = Some v.
Proof.
  induction n; intros * GET; simpl in *.
  - inv GET.
  - apply in_flat_map in GET as ((?&(?&?))&ELEMS&GET); simpl in *.
    eapply PTree.elements_complete in ELEMS.
    destruct i; simpl in *.
    + destruct o; simpl in *. destruct GET as [|GET]; try congruence.
      1,2:apply in_map_iff in GET as (?&CONTRA&?); inv CONTRA.
    + assert (p0 = p); subst.
      { destruct o; simpl in *. destruct GET as [|GET]; try congruence.
        1,2:apply in_map_iff in GET as (?&CONTRA&?); now inv CONTRA. }
      setoid_rewrite ELEMS.
      destruct i; (destruct o; [destruct GET as [|GET]|]); simpl in *; try congruence.
      all:apply in_map_iff in GET as ((?&?)&EQ&GET); inv EQ; eauto.
      1,2:eapply IHn, get_length in GET; simpl in *; lia.
Qed.

Lemma elements_keys_norepet :
  forall (A : Type) n (m : t n A), list_norepet (List.map fst (elements m)).
Proof.
  induction n; intros; simpl.
  - constructor.
  - assert (list_norepet (List.map fst (PTree.elements m))) as ND.
    { apply PTree.elements_keys_norepet. }
    assert (Forall (fun t => list_norepet (List.map fst (elements (snd (snd t))))) (PTree.elements m)).
    { apply Forall_forall. auto. }
    induction H; simpl in *; inv ND; try constructor.
    rewrite map_app. apply list_norepet_app. repeat split; auto.
    + destruct x as (?&(?&?)); simpl in *.
      assert (list_norepet (List.map fst (List.map (fun xsv : list positive * A => (p :: fst xsv, snd xsv)) (elements t0)))) as ND.
      { erewrite map_map, map_ext, <-map_map; simpl; eauto.
        eapply list_map_norepet; eauto.
        intros * _ _ NEQ. congruence. }
      destruct o; simpl in *; auto. constructor; auto.
      intros CONTRA.
      repeat apply in_map_iff in CONTRA as ((?&?)&?EQ&CONTRA); simpl in *; subst. inv EQ0.
      eapply elements_complete, get_length in CONTRA; simpl in *; lia.
    + intros ? ? IN1 IN2 ?; subst. destruct x; simpl in *.
      apply in_map_iff in IN1 as ((?&?)&?EQ&IN1); simpl in *; subst.
      apply in_map_iff in IN2 as ((?&?)&?EQ&IN2). apply in_flat_map in IN2 as ((?&?)&?&IN2). simpl in *; subst.
      destruct p0 as ([|]&?), p2 as ([|]&?); simpl in *.
      all:repeat
            match goal with
            | H: _ \/ _ |- _ => destruct H as [?EQ|]; [inv EQ|]
            | x: _ * _ |- _ => destruct x; simpl in *; subst
            | H: In _ (List.map _ _) |- _ => apply in_map_iff in H as (?&?EQ&?); inv EQ
            | H:In ([], _) (elements _) |- _ =>
                apply elements_complete, get_length in H; simpl in *; lia
            | H:~In _ (List.map fst _) |- _ =>
                eapply H, in_map_iff; do 2 esplit; eauto; auto
            end.
Qed.

Lemma elements_remove :
  forall (A : Type) n i (v : A) (m : t n A),
  get i m = Some v ->
  exists l1 l2 : list (_ * A),
    elements m = l1 ++ (i, v) :: l2 /\ elements (remove i m) = l1 ++ l2.
Proof.
  induction n; intros * GET; simpl in *; [inv GET|].
  destruct i; simpl in *; [inv GET|].
  destruct (PTree.get p m) as [(?&?)|] eqn:GET'; setoid_rewrite GET' in GET; [|inv GET].
  destruct i; simpl in *; subst.
  1,2:eapply PTree.elements_set in GET' as EL; destruct EL as (?&?&EL1&EL2).
  2:eapply IHn in GET as EL'; destruct EL' as (?&?&EL1'&EL2').
  - do 3 esplit; [setoid_rewrite EL1|setoid_rewrite GET'; setoid_rewrite EL2].
    all:rewrite ? flat_map_app; simpl; auto.
  - destruct o.
    all:do 3 esplit; [setoid_rewrite EL1|setoid_rewrite GET'; setoid_rewrite EL2].
    all:rewrite ? flat_map_app; simpl.
    all:(setoid_rewrite EL1'||setoid_rewrite EL2').
    all:rewrite map_app, <-app_assoc; simpl.
    all:rewrite ? app_comm_cons with (a:=([p], a)), app_assoc; f_equal.
Qed.

Fixpoint fold' {A B: Type} {n:nat} (f: B -> list positive -> A -> B) xs : t n A -> B -> B :=
  match n return t n A -> B -> B with
  | O => fun _ b => b
  | S _ => PTree.fold
            (fun b x t =>
               let xs' := List.app xs [x] in
               fold' f xs' (snd t) (match fst t with Some v => f b xs' v | None => b end))
  end.

Definition fold {A B: Type} {n:nat} (f: B -> list positive -> A -> B) : t n A -> B -> B :=
  fold' f nil.

Lemma fold'_spec :
  forall A B n (f : B -> list positive -> A -> B) xs (v : B) (m : t n A),
    fold' f xs m v = fold_left (fun a p => f a (xs++fst p) (snd p)) (elements m) v.
Proof.
  induction n; intros; simpl; auto.
  rewrite PTree.fold_spec.
  remember (PTree.elements m) as ts; setoid_rewrite <-Heqts; clear Heqts.
  generalize v. induction ts; simpl; auto; intros.
  rewrite IHts, IHn, fold_left_app. f_equal.
  destruct a as (?&([]&?)); simpl.
  all:rewrite fold_left_map; apply fold_left_ext.
  all:intros; now rewrite <-app_assoc.
Qed.

Corollary fold_spec :
  forall A B n (f : B -> list positive -> A -> B) (v : B) (m : t n A),
    fold f m v = fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
Proof. intros. apply fold'_spec. Qed.

Fixpoint fold1 {A B: Type} {n} (f: B -> A -> B) : t n A -> B -> B :=
  match n return t n A -> B -> B with
  | O => fun _ b => b
  | S _ => PTree.fold1
              (fun b t => fold1 f (snd t) (match fst t with Some v => f b v | None => b end))
  end.

Lemma fold1_spec :
  forall A B n (f : B -> A -> B) (v : B) (m : t n A),
    fold1 f m v = fold_left (fun a p => f a (snd p)) (elements m) v.
Proof.
  induction n; intros; simpl; auto.
  rewrite PTree.fold1_spec.
  remember (PTree.elements m) as ts; setoid_rewrite <-Heqts; clear Heqts.
  generalize v. induction ts; simpl; auto; intros.
  rewrite IHts, IHn, fold_left_app. f_equal.
  destruct a as (?&([]&?)); simpl.
  all:rewrite fold_left_map; auto.
Qed.

Lemma flat_map_remove_nils: forall A B (f: _ -> list B) (t: PTree.t A),
    exists t', flat_map f (PTree.elements t) = flat_map f (PTree.elements t')
          /\ Forall (fun x => f x <> nil) (PTree.elements t').
Proof.
  intros.
  exists (PTree.filter (fun x v => match f (x, v) with nil => false | _ => true end) t0).
  rewrite PTree.elements_filter. split.
  - induction (PTree.elements t0) as [|(?&?)]; simpl; auto.
    destruct (f (p, a)) eqn:F; simpl; auto.
    rewrite F; simpl. repeat (f_equal; auto).
  - apply Forall_forall; intros (?&?) HIN.
    apply filter_In in HIN as (?&?); simpl in *.
    destruct (f (p, a)); congruence.
Qed.

Lemma list_forall2_flat_map : forall A1 A2 B1 B2 (f1: A1 -> list B1) (f2: A2 -> list B2) P l1 l2,
    list_forall2 (fun x1 x2 => list_forall2 P (f1 x1) (f2 x2)) l1 l2 ->
    list_forall2 P (flat_map f1 l1) (flat_map f2 l2).
Proof.
  intros * F2; induction F2; simpl.
  - constructor.
  - apply list_forall2_app; auto.
Qed.

Theorem elements_canonical_order':
  forall A B n (R: A -> B -> Prop) (t1: t n A) (t2: t n B),
  (forall i, (0 < length i <= n)%nat -> option_rel R (get i t1) (get i t2)) ->
  list_forall2
    (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
    (elements t1) (elements t2).
Proof.
  induction n; intros * REL; simpl in *; [constructor|].
  remember (fun xv => match fst (snd xv) with _ => _ end) as f1.
  remember (fun xv : positive * (option B * _) => match fst (snd xv) with _ => _ end) as f2.
  edestruct (flat_map_remove_nils f1 t1) as (t1'&EQ1&F1). setoid_rewrite EQ1.
  edestruct (flat_map_remove_nils f2 t2) as (t2'&EQ2&F2). setoid_rewrite EQ2.
  assert (forall x, @get _ (S n) x t1' = @get _ (S n) x t1) as GEQ1.
  { intros. destruct (@get _ (S n) x t1') eqn:GET1.
    - apply elements_correct in GET1; simpl in GET1.
      subst. setoid_rewrite <-EQ1 in GET1.
      symmetry. apply elements_complete; auto.
    - destruct (@get _ (S n) x t1) eqn:GET2; auto. exfalso.
      apply elements_correct in GET2; simpl in GET2.
      subst. setoid_rewrite EQ1 in GET2.
      assert (@get _ (S n) x t1' = Some a) by (apply elements_complete; auto).
      congruence. }
  assert (forall x, @get _ (S n) x t2' = @get _ (S n) x t2) as GEQ2.
  { intros. destruct (@get _ (S n) x t2') eqn:GET1.
    - apply elements_correct in GET1; simpl in GET1.
      subst. setoid_rewrite <-EQ2 in GET1.
      symmetry. apply elements_complete; auto.
    - destruct (@get _ (S n) x t2) eqn:GET2; auto. exfalso.
      apply elements_correct in GET2; simpl in GET2.
      subst. setoid_rewrite EQ2 in GET2.
      assert (@get _ (S n) x t2' = Some b) by (apply elements_complete; auto).
      congruence. }

  setoid_rewrite <-GEQ1 in REL. setoid_rewrite <-GEQ2 in REL.
  subst. eapply list_forall2_flat_map, list_forall2_imply.
  eapply PTree.elements_canonical_order'.
  2:{ fold t. intros (?&?&?) (?&?&?) IN1 IN2 (EQ&?); simpl in *; subst.
      instantiate (1:=fun p1 p2 => option_rel R (fst p1) (fst p2)) in H; simpl in *.
      apply PTree.elements_complete in IN1. apply PTree.elements_complete in IN2.
      inv H; simpl; [|constructor]; simpl; auto.
      1,2:eapply list_forall2_map, list_forall2_imply.
      1,3:(eapply IHn; intros i LEN; specialize (REL (p0::i)); simpl in *;
           setoid_rewrite IN1 in REL; setoid_rewrite IN2 in REL;
           destruct i, n; simpl in *; try constructor; eapply REL; lia).
      1,2:intros * IN1' IN2' (?&?); split; simpl; eauto; now f_equal.
  }
  all:fold t in *.
  intros p. specialize (REL [p]) as REL1; simpl in *.
  destruct (PTree.get p t1') as [(?&?)|] eqn:EQ1', (PTree.get p t2') as [(?&?)|] eqn:EQ2';
    simpl in *; try constructor; auto.
  - setoid_rewrite EQ1' in REL1. setoid_rewrite EQ2' in REL1. auto.
    apply REL1. lia.
  - exfalso.
    assert (exists i v, @get _ (S n) (p::i) t1' = Some v) as (?&?&ELEMS).
    { apply PTree.elements_correct in EQ1' as IN1. eapply Forall_forall in IN1; eauto.
      simpl in *. setoid_rewrite EQ1'.
      destruct o. exists []. eexists; simpl; eauto.
      destruct (elements t0) as [|(?&?)] eqn:ELEMS; simpl in *; try congruence.
      assert (get l t0 = Some a) as GET'.
      { eapply elements_complete. rewrite ELEMS. simpl; auto. }
      apply get_length in GET' as LENGTH'.
      destruct l; simpl in *; try lia.
      exists (p0::l). eauto. }
    apply get_length in ELEMS as LENGTH.
    specialize (REL (p::x)). setoid_rewrite ELEMS in REL.
    setoid_rewrite EQ2' in REL. specialize (REL LENGTH). inv REL.
  - exfalso.
    assert (exists i v, @get _ (S n) (p::i) t2' = Some v) as (?&?&ELEMS).
    { apply PTree.elements_correct in EQ2' as IN1. eapply Forall_forall in IN1; eauto.
      simpl in *. setoid_rewrite EQ2'.
      destruct o. exists []. eexists; simpl; eauto.
      destruct (elements t0) as [|(?&?)] eqn:ELEMS; simpl in *; try congruence.
      assert (get l t0 = Some b) as GET'.
      { eapply elements_complete. rewrite ELEMS. simpl; auto. }
      apply get_length in GET' as LENGTH'.
      destruct l; simpl in *; try lia.
      exists (p0::l). eauto. }
    apply get_length in ELEMS as LENGTH.
    specialize (REL (p::x)). setoid_rewrite ELEMS in REL.
    setoid_rewrite EQ1' in REL. specialize (REL LENGTH). inv REL.
Qed.

(* TODO move *)
Fixpoint list_beq {A: Type} (beqA: A -> A -> bool) (l1 l2: list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | hd1::tl1, hd2::tl2 => (beqA hd1 hd2) && (list_beq beqA tl1 tl2)
  | _, _ => false
  end.

Lemma list_beq_correct {A: Type} (beqA: A -> A -> bool) : forall l1 l2,
  list_beq beqA l1 l2 = true <-> list_forall2 (fun x1 x2 => beqA x1 x2 = true) l1 l2.
Proof.
  induction l1; simpl in *; intros []; (split; intros F; [try now inv F|inv F]); auto.
  constructor.
  1,2:rewrite andb_true_iff in *.
  - destruct F. constructor; auto. now apply IHl1.
  - split; auto. now apply IHl1.
Qed.

Lemma list_forall2_same {A: Type} (P: A -> A -> Prop) : forall l,
    Forall (fun x => P x x) l -> list_forall2 P l l.
Proof.
  induction l; intros * F; inv F; constructor; auto.
Qed.

Definition beq {A: Type} {n} (beqA: A -> A -> bool) (m1 m2: t n A) : bool :=
  list_beq (fun x1 x2 => list_beq Pos.eqb (fst x1) (fst x2) && beqA (snd x1) (snd x2))
    (elements m1) (elements m2).

Lemma beq_correct:
  forall {A} {n} (eqA: A -> A -> bool) (t1 t2: t n A),
  beq eqA t1 t2 = true <->
  (forall (x: list positive),
    0 < length x <= n ->
    match get x t1, get x t2 with
    | None, None => True
    | Some y1, Some y2 => eqA y1 y2 = true
    | _, _ => False
  end).
Proof.
  intros.
  assert (forall l1 l2, list_beq Pos.eqb l1 l2 = true <-> l1 = l2) as LEQ.
  { intros. rewrite list_beq_correct.
    split; intros EQ.
    - revert l2 EQ.
      induction l1; intros; inv EQ; f_equal; auto.
      now apply Pos.eqb_eq.
    - subst. apply list_forall2_same, Forall_forall; intros * _.
      apply Pos.eqb_refl. }
  setoid_rewrite list_beq_correct. split; intros H.
  - intros *.
    destruct (get x t1) eqn:GET1.
    + eapply list_forall2_in_left in H as ((?&?)&HIN&BEQ); eauto using elements_correct.
      apply Bool.andb_true_iff in BEQ as (BEQ1&BEQ2). apply LEQ in BEQ1; simpl in *; subst.
      apply elements_complete in HIN. now rewrite HIN.
    + destruct (get x t2) eqn:GET2; auto.
      eapply list_forall2_in_right in H as ((?&?)&HIN&BEQ); eauto using elements_correct.
      apply Bool.andb_true_iff in BEQ as (BEQ1&BEQ2). apply LEQ in BEQ1; simpl in *; subst.
      apply elements_complete in HIN. congruence.
  - eapply list_forall2_imply. eapply elements_canonical_order'.
    2:{ intros (?&?) (?&?) _ _ (?&?); simpl in *; subst.
        apply andb_true_intro; split; [|apply H1].
        apply list_beq_correct, list_forall2_same, Forall_forall; intros * _.
        apply Pos.eqb_refl. }
    + intros * LEN. specialize (H i).
      destruct (get i t1), (get i t2); simpl in *; try constructor; auto.
      1,2:specialize (H LEN); now inv H.
Qed.

End PTree_rec.

Module Type QUALIDENT.
  Parameter depth : nat.
  Parameter t : Type.

  Parameter eq : forall (id1 id2 : t), { id1 = id2 } + { id1 <> id2 }.
  Parameter to_list : t -> list positive.

  Parameter to_list_length : forall id,
      (0 < length (to_list id) <= depth)%nat.

  Parameter to_list_injective : forall i j,
      to_list i = to_list j ->
      i = j.

  Parameter of_list : list positive -> t.

  Parameter of_list_injective : forall i j,
      (0 < length i <= depth)%nat ->
      (0 < length j <= depth)%nat ->
      of_list i = of_list j ->
      i = j.

  Parameter to_of_list : forall l, of_list (to_list l) = l.
  Parameter of_to_list : forall l, (0 < length l <= depth)%nat -> to_list (of_list l) = l.
End QUALIDENT.

Module QITree(QI: QUALIDENT) <: TREE.
  Definition elt := QI.t.
  Definition elt_eq := QI.eq.
  Definition t := PTree_rec.t QI.depth.

  Definition empty {A: Type} : t A := @PTree_rec.empty A QI.depth.

  Definition get {A: Type} key := @PTree_rec.get A QI.depth (QI.to_list key).
  Definition set {A: Type} key := @PTree_rec.set A QI.depth (QI.to_list key).
  Definition remove {A: Type} key := @PTree_rec.remove A QI.depth (QI.to_list key).

  Lemma gempty : forall A i, get i (@empty A) = None.
  Proof. intros. apply PTree_rec.gempty. Qed.

  Lemma gss : forall A i x (m: t A), get i (set i x m) = Some x.
  Proof. intros. apply PTree_rec.gss, QI.to_list_length. Qed.

  Lemma gso : forall A i j x (m: t A), i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. apply PTree_rec.gso.
    contradict H. now apply QI.to_list_injective.
  Qed.

  Lemma gsspec : forall A i j x (m: t A),
      get i (set j x m) = if (elt_eq i j) then Some x else get i m.
  Proof.
    intros.
    destruct (elt_eq i j); subst; auto using gss, gso.
  Qed.

  Lemma grs : forall A i (m: t A), get i (remove i m) = None.
  Proof. intros. apply PTree_rec.grs. Qed.

  Lemma gro : forall A i j (m: t A), i <> j -> get i (remove j m) = get i m.
  Proof.
    intros. apply PTree_rec.gro.
    contradict H. now apply QI.to_list_injective.
  Qed.

  Lemma grspec : forall A i j (m: t A),
      get i (remove j m) = if (elt_eq i j) then None else get i m.
  Proof.
    intros.
    destruct (elt_eq i j); subst; auto using grs, gro.
  Qed.

  Definition beq {A: Type} (beqA: A -> A -> bool) (m1 m2: t A) : bool :=
    PTree_rec.beq beqA m1 m2.

  Lemma beq_correct:
    forall {A} (eqA: A -> A -> bool) (t1 t2: t A),
      beq eqA t1 t2 = true <->
        (forall x,
            match get x t1, get x t2 with
            | None, None => True
            | Some y1, Some y2 => eqA y1 y2 = true
            | _, _ => False
            end).
  Proof.
    intros. unfold beq, get.
    rewrite PTree_rec.beq_correct.
    split; intros BEQ *.
    - apply BEQ. apply QI.to_list_length.
    - intros LEN. specialize (BEQ (QI.of_list x)).
      rewrite QI.of_to_list in BEQ; auto.
  Qed.

  Definition map {A B: Type} f := @PTree_rec.map A B QI.depth (fun qi => f (QI.of_list qi)).

  Lemma gmap : forall A B (f: _ -> A -> B) i (m : t A),
      get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros.
    setoid_rewrite PTree_rec.gmap.
    now rewrite QI.to_of_list.
  Qed.

  Definition map1 {A B: Type} := @PTree_rec.map1 A B QI.depth.

  Lemma gmap1 : forall A B (f: A -> B) i (m : t A),
      get i (map1 f m) = option_map f (get i m).
  Proof. intros. apply PTree_rec.gmap1. Qed.

  Definition combine {A B C: Type} := @PTree_rec.combine A B C QI.depth.

  Lemma gcombine : forall A B C (f: _ -> _ -> option C),
      f None None = None ->
      forall (m1: t A) (m2: t B) i,
        get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof. intros. apply PTree_rec.gcombine. auto. Qed.

  Definition combine_mostdef {A} := @PTree_rec.combine_mostdef A QI.depth.
  Definition f_mostdef {A} := @PTree_rec.f_mostdef A.

  Lemma gcombine_mostdef :
    forall (A : Type) (mostdef : A -> A -> option A) (m1 m2 m3 : t A) (a : option A) (i : elt),
      combine_mostdef mostdef m1 m2 = Some m3 ->
      f_mostdef mostdef (get i m1) (get i m2) = Some a -> get i m3 = a.
  Proof. intros. eapply PTree_rec.gcombine_mostdef; eauto. Qed.

  Lemma fcombine_mostdef :
    forall (A : Type) (mostdef : A -> A -> option A) (m1 m2 : t A),
      combine_mostdef mostdef m1 m2 = None ->
      (forall i (a1 a2 : A),
          get i m1 = Some a1 -> get i m2 = Some a2 -> mostdef a1 a2 <> None) -> False.
  Proof.
    intros * ? GET.
    eapply PTree_rec.fcombine_mostdef; eauto.
    intros. eapply GET with (i:=QI.of_list i).
    all:unfold get; now rewrite QI.of_to_list.
  Qed.

  Lemma gcombine_mostdef_ok :
    forall (A : Type) (mostdef : A -> A -> option A) (m1 m2 m3 : t A) (i : elt) (a : A),
      combine_mostdef mostdef m1 m2 = Some m3 ->
      get i m3 = Some a -> f_mostdef mostdef (get i m1) (get i m2) = Some (Some a).
  Proof. intros. eapply PTree_rec.gcombine_mostdef_ok; eauto. Qed.

  Lemma gcombine_mostdef_only_l :
    forall (A : Type) (mostdef : A -> A -> option A) (m1 : t A),
      combine_mostdef mostdef m1 empty = Some m1.
  Proof. intros. eapply PTree_rec.gcombine_mostdef_only_l; eauto. Qed.

  Lemma gcombine_mostdef_none_rev :
    forall (A : Type) (mostdef : A -> A -> option A) (m1 m2 m3 : t A) (i : elt),
      combine_mostdef mostdef m1 m2 = Some m3 ->
      get i m3 = None -> get i m1 = None /\ get i m2 = None.
  Proof. intros. eapply PTree_rec.gcombine_mostdef_none_rev; eauto. Qed.

  Definition elements {A} m :=
    List.map (fun x => (QI.of_list (fst x), snd x)) (@PTree_rec.elements A QI.depth m).

  Lemma elements_correct :
    forall (A : Type) (m : t A) (i : elt) (v : A), get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros * GET. unfold elements.
    apply in_map_iff; do 2 esplit. 2:eapply PTree_rec.elements_correct; eauto.
    simpl. now rewrite QI.to_of_list.
  Qed.

  Lemma elements_complete :
    forall (A : Type) (m : t A) (i : elt) (v : A), In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros * GET. unfold elements.
    apply in_map_iff in GET as ((?&?)&EQ&GET). inv EQ.
    eapply PTree_rec.elements_complete in GET as GET'; eauto.
    unfold get. rewrite QI.of_to_list; eauto using PTree_rec.get_length.
  Qed.

  Lemma elements_keys_norepet :
    forall (A : Type) (m : t A), list_norepet (List.map fst (elements m)).
  Proof.
    intros. unfold elements.
    erewrite map_map, map_ext, <-map_map.
    eapply list_map_norepet.
    1:apply PTree_rec.elements_keys_norepet.
    2:intros (?&?); simpl; eauto.
    - intros * IN1 IN2 NEQ.
      contradict NEQ.
      apply in_map_iff in IN1 as ((?&?)&?&IN1); subst.
      apply in_map_iff in IN2 as ((?&?)&?&IN2); subst.
      apply QI.of_list_injective; eauto using PTree_rec.elements_complete, PTree_rec.get_length.
  Qed.

  Lemma elements_remove :
    forall (A : Type) (i : elt) (v : A) (m : t A),
    get i m = Some v ->
    exists l1 l2 : list (elt * A),
      elements m = l1 ++ (i, v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
    intros * GET. unfold elements.
    eapply PTree_rec.elements_remove in GET as (?&?&EL1&EL2).
    setoid_rewrite EL1. setoid_rewrite EL2.
    do 3 esplit. all:rewrite map_app; simpl; eauto.
    repeat f_equal.
    now rewrite QI.to_of_list.
  Qed.

  Definition fold {A B: Type} (f: B -> elt -> A -> B) : t A -> B -> B :=
    @PTree_rec.fold A B QI.depth (fun b xs => f b (QI.of_list xs)).

  Lemma fold_spec :
    forall (A B : Type) (f : B -> elt -> A -> B) (v : B) (m : t A),
      fold f m v = fold_left (fun (a : B) (p : elt * A) => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros.
    unfold fold, elements.
    rewrite PTree_rec.fold_spec, fold_left_map. auto.
  Qed.

  Definition fold1 {A B: Type} (f: B -> A -> B) : t A -> B -> B :=
    @PTree_rec.fold1 A B QI.depth f.

  Lemma fold1_spec :
    forall (A B : Type) (f : B -> A -> B) (v : B) (m : t A),
      fold1 f m v = fold_left (fun (a : B) (p : elt * A) => f a (snd p)) (elements m) v.
  Proof.
    intros.
    unfold fold1, elements.
    rewrite PTree_rec.fold1_spec, fold_left_map. auto.
  Qed.

  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
      (forall i, option_rel R (get i m) (get i n)) ->
      list_forall2
        (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
        (elements m) (elements n).
  Proof.
    intros * REL. unfold get in *.
    assert (forall i, (0 < length i <= QI.depth)%nat -> option_rel R (PTree_rec.get i m) (PTree_rec.get i n)) as REL'.
    { intros. specialize (REL (QI.of_list i)).
      rewrite ? QI.of_to_list in REL; auto. }
    apply PTree_rec.elements_canonical_order' in REL'.
    unfold elements. rewrite list_forall2_map1, list_forall2_map2; simpl.
    eapply list_forall2_imply; eauto.
    intros (?&?) (?&?) _ _ (?&?); simpl in *; subst; auto.
  Qed.

End QITree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition init (A : Type) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Type) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. reflexivity.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map1 f (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap1.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. simpl. decEq. apply PTree.set2.
  Qed.

  Local Open Scope positive.
  Lemma set_disjoint:
    forall (A: Type) (i j : elt) (x y: A) (m: t A),
      i <> j ->
      set j y (set i x m) = set i x (set j y m).
  Proof.
    intros. unfold set. decEq. apply PTree.set_disjoint. assumption.
  Qed.

End PMap.


(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Parameter t: Type.
  Parameter index: t -> positive.
  Axiom index_inj: forall (x y: t), index x = index y -> x = y.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PMap.t.
  Definition init (A: Type) (x: A) := PMap.init x.
  Definition get (A: Type) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Type) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Type) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi.
  Qed.

  Lemma gss:
    forall (A: Type) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso.
    red. intro. apply H. apply X.index_inj; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set.
    rewrite PMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity.
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: X.t) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map, get. apply PMap.gmap.
  Qed.

  Lemma set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. apply PMap.set2.
  Qed.

  Lemma set_disjoint:
    forall (A: Type) (i j : elt) (x y: A) (m: t A),
      i <> j ->
      set j y (set i x m) = set i x (set j y m).
  Proof.
    intros. unfold set. apply PMap.set_disjoint.
    intro INEQ.
    assert (i = j) by (apply X.index_inj; auto).
    auto.
  Qed.
End IMap.

Module ZIndexed.
  Definition t := Z.
  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Lemma index_inj: forall (x y: Z), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
    congruence.
  Qed.
  Definition eq := zeq.
End ZIndexed.

Module ZMap := IMap(ZIndexed).

Module NIndexed.
  Definition t := N.
  Definition index (n: N): positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Lemma index_inj: forall (x y: N), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
  Qed.
  Lemma eq: forall (x y: N), {x = y} + {x <> y}.
  Proof.
    decide equality. apply peq.
  Qed.
End NIndexed.

Module NMap := IMap(NIndexed).




(** * Extensional (and efficient) implementations of maps over any type able to discriminate the default value.
      Author: S. Boulmé - 2025.
*)

Class DefaultDiscr {Value:Type} := {
  default: Value;
  is_default: Value -> bool;
  is_default_true: forall x, is_default x = true <-> x = default
}.


Module Type XMAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: forall `(DefaultDiscr), Type.
  Parameter init: forall `(A: DefaultDiscr), t A.
  Parameter get: forall `(A: DefaultDiscr), elt -> t A -> Value.
  Parameter set: forall `(A: DefaultDiscr), elt -> Value -> t A -> t A.
  Parameter is_init: forall `(A: DefaultDiscr), t A -> bool.

  Axiom is_init_true: forall `(A: DefaultDiscr) (m: t A), is_init m = true <-> m = init A.

  Axiom gi:
    forall `(A: DefaultDiscr) (i: elt), get i (init A) = default.
  Axiom extensionality: 
    forall `(A: DefaultDiscr) (m1 m2: t A), (forall i, get i m1 = get i m2) -> m1 = m2.


  Axiom gss:
    forall `(A: DefaultDiscr) (i: elt) x (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall `(A: DefaultDiscr) (i j: elt) x (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall `(A: DefaultDiscr) (i j: elt) x (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall `(A: DefaultDiscr) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.

(* NOT YET SUPPORTED. Would require a [DefautDiscr] morphism 

  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
*)

   Global Instance xmap_default `(A: DefaultDiscr): @DefaultDiscr (t A) := {| 
     default := init A;
     is_default := is_init (A:=A);
     is_default_true := is_init_true (A:=A)
  |}.

End XMAP.



(** Positive Tree implementation of PXMAP

    NB: This is expected to be even more efficient than PMap (provided that [is_default] is fast) 
    since the default value is never stored in the map !
*)
Module PXMap <: XMAP.

  Require Import Eqdep_dec.

  Definition elt := positive.
  Definition elt_eq := peq.

  Section PXMapBasics.

  Context `(A: DefaultDiscr).

  Definition t := PTree.t { x: Value | is_default x = false }.

  Definition init : t := PTree.empty _.

  Definition is_init (m: t) : bool :=
   match m with
   | PTree.Empty => true
   | _ => false
   end.

   Lemma is_init_true: forall m, is_init m = true <-> m = init.
   Proof.
     unfold init; intros; split.
     - destruct m; simpl; reflexivity || congruence.
     - intros; subst; simpl; auto.
   Qed.

  Definition get (i : positive) (m : t): Value :=
    match PTree.get i m with
    | Some x => ` x
    | None => default
    end.

  Theorem gi: forall (i: positive), get i init = default.
  Proof.
    intros. reflexivity.
  Qed.

  Remark is_default_false: forall x, is_default x = false <-> x<>default.
  Proof.
    intros x; generalize (is_default_true x).
    destruct (is_default x) eqn: EQ; intuition congruence.
  Qed.

  Theorem extensionality: forall (m1 m2: t), (forall i, get i m1 = get i m2) -> m1 = m2.
  Proof.
    unfold get; intros m1 m2 GET. apply PTree.extensionality.
    intros i; generalize (GET i); clear GET.
    destruct (PTree.get i m1) as [ [] | ]; destruct (PTree.get i m2) as [ [] | ]; cbn; auto.
    - intros; subst. rewrite (UIP_dec bool_dec e e0). auto.
    - intros; subst. generalize e. rewrite is_default_false in e. congruence.
    - intros; subst. generalize e. rewrite is_default_false in e. congruence.
  Qed.

  Program Definition set_spec (i : positive) (x: Value) (m : t) :
    { m' | (forall j, get j m' = if peq j i then x else get j m) } :=
    match is_default x with
    | true => PTree.remove i m
    | _ => PTree.set i (exist _ x _) m
    end.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply is_default_true in Heq_anonymous. subst.
    unfold get.
    rewrite PTree.grspec. unfold PTree.elt_eq.
    destruct (peq _ _); auto.
  Qed.
  Next Obligation.
    destruct (is_default x); congruence.
  Qed.
  Next Obligation.
    unfold get. rewrite PTree.gsspec.
    destruct (peq _ _); auto.
  Qed.

  Definition set i x m := ` (set_spec i x m).

  Theorem gsspec:
    forall (i j: positive) x (m: t),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. unfold set. destruct (set_spec _ _ _). cbn; auto.
  Qed.

  Theorem gss:
    forall (i: positive) x (m: t), get i (set i x m) = x.
  Proof.
    intros; rewrite gsspec. rewrite pred_dec_true; auto.
  Qed.

  Theorem gso:
    forall (i j: positive) x (m: t),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros; rewrite gsspec. rewrite pred_dec_false; auto.
  Qed.

  Theorem gsident:
    forall (i j: positive) (m: t),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  (* consequences of extensionality (NB: this could be functorized !) *)
  Theorem set_get_id:
    forall (i: elt) (m: t),
    set i (get i m) m = m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite ! gsspec. destruct (peq j i); try congruence.
  Qed.

  Theorem set2:
    forall (i: elt) (m: t) v1 v2,
    set i v2 (set i v1 m) = set i v2 m.
  Proof.
    intros; apply extensionality; intros j.
    rewrite ! gsspec. destruct (peq j i); auto.
  Qed.

  Theorem set_disjoint:
    forall (i j : elt) x y (m: t),
      i <> j ->
      set j y (set i x m) = set i x (set j y m).
  Proof.
    intros. apply extensionality; intros k.
    rewrite ! gsspec.
    destruct (peq k j).
    - subst; rewrite pred_dec_false; auto.
    - destruct (peq k i); auto.
  Qed.

  Global Instance xmap_default: @DefaultDiscr t := {| 
     default := init;
     is_default := is_init;
     is_default_true := is_init_true
  |}.

  End PXMapBasics.

End PXMap.


(** Extensional version of IMap 

Use proof irrelevance axiom (Axioms.proof_irr).
We could avoid it by extending INDEXED_TYPE with a decidable test that a positive is an image of an index.
*)
Module IXMap(X: INDEXED_TYPE) <: XMAP.


  Require Import Axioms.

  Definition elt := X.t.
  Definition elt_eq := X.eq.

  Section IXMapBasics.

  Context `(A: DefaultDiscr).

  Definition t : Type := { m: PXMap.t A | forall i, is_default (PXMap.get i m) = false -> exists x, i = X.index x}.

  Program Definition init : t := PXMap.init A.
  Next Obligation.
    rewrite PXMap.gi, PXMap.is_default_false in H. congruence.
  Qed.

  Program Definition get (i: X.t) (m: t) : Value := PXMap.get (X.index i) m.

  Program Lemma inv_irr (m1 m2: t): (`m1) = (`m2) -> m1 = m2.
  Proof.
    destruct m1 as (m1 & INV1). destruct m2 as (m2 & INV2). simpl in *.
    intros; subst; f_equal. apply proof_irr.
  Qed.

  Lemma extensionality: forall (m1 m2: t), (forall i, get i m1 = get i m2) -> m1 = m2.
  Proof.
    unfold get; intros. apply inv_irr.
    destruct m1 as (m1 & INV1). destruct m2 as (m2 & INV2). simpl in *.
    apply PXMap.extensionality.
    intros i; destruct (is_default (PXMap.get i m1)) eqn: X.
    - destruct (is_default (PXMap.get i m2)) eqn: Y.
      + rewrite !is_default_true in X,Y. congruence.
      + feapply INV2. subst; auto.
    - feapply INV1. subst; auto.
  Qed.

  Program Definition set (i: X.t) (v: Value) (m: t): t := PXMap.set (X.index i) v m.
  Next Obligation.
    rewrite PXMap.gsspec in H. destruct (peq _ _).
    - eauto.
    - destruct m. simpl in *; auto. 
  Qed.

  Program Definition is_init (m: t) : bool := PXMap.is_init m.

  Lemma gi:
    forall (i: X.t), get i init = default.
  Proof.
    intros. apply PXMap.gi.
  Qed.

  Lemma gss:
    forall (i: X.t) (x: Value) (m: t), get i (set i x m) = x.
  Proof.
    intros. apply PXMap.gss.
  Qed.

  Lemma gso:
    forall (i j: X.t) (x: Value) (m: t),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. apply PXMap.gso.
    red. intro. apply H. apply X.index_inj; auto.
  Qed.

  Lemma gsspec:
    forall (i j: X.t) (x: Value) (m: t),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set. simpl.
    rewrite PXMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity.
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gsident:
    forall i j (m: t),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. simpl.
    apply PXMap.gsident.
  Qed.

  Lemma set2:
    forall (i: elt) (x y: Value) (m: t),
    set i y (set i x m) = set i y m.
  Proof.
    intros. apply inv_irr. simpl. apply PXMap.set2.
  Qed.

  Lemma set_disjoint:
    forall (i j : elt) (x y: Value) (m: t),
      i <> j ->
      set j y (set i x m) = set i x (set j y m).
  Proof.
    intros. apply inv_irr. simpl. apply PXMap.set_disjoint.
    intro INEQ.
    assert (i = j) by (apply X.index_inj; auto).
    auto.
  Qed.

  Theorem set_get_id:
    forall (i: elt) (m: t),
    set i (get i m) m = m.
  Proof.
    intros; apply inv_irr; simpl; apply PXMap.set_get_id.
  Qed.

  Lemma is_init_true: forall m, is_init m = true <-> m = init.
  Proof.
    intros; split.
    - intros; apply inv_irr; simpl; apply PXMap.is_init_true. assumption.
    - intros H; rewrite H. reflexivity.
  Qed.

  Global Instance xmap_default: @DefaultDiscr t := {| 
     default := init;
     is_default := is_init;
     is_default_true := is_init_true
  |}.


  End IXMapBasics.

End IXMap.

Module ZXMap := IXMap(ZIndexed).

(** * An implementation of maps over any type with decidable equality *)

Module Type EQUALITY_TYPE.
  Parameter t: Type.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Type) := X.t -> A.
  Definition init (A: Type) (v: A) := fun (_: X.t) => v.
  Definition get (A: Type) (x: X.t) (m: t A) := m x.
  Definition set (A: Type) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Type) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
End EMap.

(** * A partial implementation of trees over any type that injects into type [positive] *)

Module ITree(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PTree.t.

  Definition empty (A: Type): t A := PTree.empty A.
  Definition get (A: Type) (k: elt) (m: t A): option A := PTree.get (X.index k) m.
  Definition set (A: Type) (k: elt) (v: A) (m: t A): t A := PTree.set (X.index k) v m.
  Definition remove (A: Type) (k: elt) (m: t A): t A := PTree.remove (X.index k) m.

  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros. apply PTree.gempty.
  Qed.
  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros. apply PTree.gss.
  Qed.
  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. apply PTree.gso. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply gss. apply gso; auto.
  Qed.
  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros. apply PTree.grs.
  Qed.
  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros. apply PTree.gro. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply grs. apply gro; auto.
  Qed.

  Definition beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool := PTree.beq.
  Theorem beq_sound:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true ->
    forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end.
  Proof.
    unfold beq, get. intros. rewrite PTree.beq_correct in H. apply H.
  Qed.

  Definition combine: forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C := PTree.combine.
  Theorem gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros. apply PTree.gcombine. auto.
  Qed.
End ITree.

Module ZTree := ITree(ZIndexed).

(** * Additional properties over trees *)

From Stdlib Require Import Equivalence EquivDec.

Module Tree_Properties(T: TREE).

(** Two induction principles over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Type.
Variable init: A.
Variable m_final: T.t V.

Hypothesis H_base:
  forall m,
  (forall k, T.get k m = None) ->
  P m init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = Some v -> T.get k m_final = Some v ->
  P (T.remove k m) a -> P m (f a k v).

Let f' (p : T.elt * V) (a: A) := f a (fst p) (snd p).

Let P' (l: list (T.elt * V)) (a: A) : Type :=
  forall m, (forall k v, In (k, v) l <-> T.get k m = Some v) -> P m a.

Let H_base':
  P' nil init.
Proof.
  intros m EQV. apply H_base.
  intros. destruct (T.get k m) as [v|] eqn:G; auto.
  apply EQV in G. contradiction.
Defined.

Let H_rec':
  forall k v l a,
  ~In k (List.map fst l) ->
  T.get k m_final = Some v ->
  P' l a ->
  P' ((k, v) :: l) (f a k v).
Proof.
  unfold P'; intros k v l a NOTIN FINAL HR m EQV.
  set (m0 := T.remove k m).
  apply H_rec.
- apply EQV. simpl; auto.
- auto.
- apply HR. intros k' v'. rewrite T.grspec. split; intros; destruct (T.elt_eq k' k).
  + subst k'. elim NOTIN. change k with (fst (k, v')). apply List.in_map; auto.
  + apply EQV. simpl; auto.
  + congruence.
  + apply EQV in H. simpl in H. intuition congruence.
Defined.

Lemma fold_ind_aux:
  forall l,
  (forall k v, In (k, v) l -> T.get k m_final = Some v) ->
  list_norepet (List.map fst l) ->
  P' l (List.fold_right f' init l).
Proof.
  induction l as [ | [k v] l ]; simpl; intros FINAL NOREPET.
- apply H_base'.
- apply H_rec'.
  + inv NOREPET. auto.
  + apply FINAL. auto.
  + apply IHl. auto. inv NOREPET; auto.
Defined.

Theorem fold_ind:
  P m_final (T.fold f m_final init).
Proof.
  intros.
  set (l' := List.rev (T.elements m_final)).
  assert (P' l' (List.fold_right f' init l')).
  { apply fold_ind_aux.
    intros. apply T.elements_complete. apply List.in_rev. auto.
    unfold l'; rewrite List.map_rev. apply list_norepet_rev. apply T.elements_keys_norepet. }
  unfold l', f' in X; rewrite fold_left_rev_right in X.
  rewrite T.fold_spec. apply X.
  intros; simpl. rewrite <- List.in_rev.
  split. apply T.elements_complete. apply T.elements_correct.
Defined.

End TREE_FOLD_IND.

Section TREE_FOLD_REC.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Prop.
Variable init: A.
Variable m_final: T.t V.

Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base:
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v).

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  apply fold_ind. 
- intros. apply P_compat with (T.empty V); auto.
  + intros. rewrite T.gempty. auto.
- intros. apply P_compat with (T.set k v (T.remove k m)).
  + intros. rewrite T.gsspec, T.grspec. destruct (T.elt_eq x k); auto. congruence.
  + apply H_rec; auto. apply T.grs.
Qed.

End TREE_FOLD_REC.

(** A nonnegative measure over trees *)

Section MEASURE.

Variable V: Type.

Definition cardinal (x: T.t V) : nat := List.length (T.elements x).

Theorem cardinal_remove:
  forall x m y, T.get x m = Some y -> (cardinal (T.remove x m) < cardinal m)%nat.
Proof.
  unfold cardinal; intros.
  exploit T.elements_remove; eauto. intros (l1 & l2 & P & Q).
  rewrite P, Q. rewrite ! app_length. simpl. lia.
Qed.

End MEASURE.

(** Forall and exists *)

Section FORALL_EXISTS.

Variable A: Type.

Definition for_all (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b && f x a) m true.

Lemma for_all_correct:
  forall m f,
  for_all m f = true <-> (forall x a, T.get x m = Some a -> f x a = true).
Proof.
  intros m0 f.
  unfold for_all. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros. rewrite <- H in H2; auto. rewrite H in H2; auto.
- (* Base case *)
  split; intros. rewrite T.gempty in H0; congruence. auto.
- (* Inductive case *)
  split; intros.
  destruct (andb_prop _ _ H2). rewrite T.gsspec in H3. destruct (T.elt_eq x k).
  inv H3. auto.
  apply H1; auto.
  apply andb_true_intro. split.
  rewrite H1. intros. apply H2. rewrite T.gso; auto. congruence.
  apply H2. apply T.gss.
Qed.

Definition exists_ (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b || f x a) m false.

Lemma exists_correct:
  forall m f,
  exists_ m f = true <-> (exists x a, T.get x m = Some a /\ f x a = true).
Proof.
  intros m0 f.
  unfold exists_. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros (x0 & a0 & P & Q); exists x0; exists a0; split; auto; congruence.
- (* Base case *)
  split; intros. congruence. destruct H as (x & a & P & Q). rewrite T.gempty in P; congruence.
- (* Inductive case *)
  split; intros.
  destruct (orb_true_elim _ _ H2).
  rewrite H1 in e. destruct e as (x1 & a1 & P & Q).
  exists x1; exists a1; split; auto. rewrite T.gso; auto. congruence.
  exists k; exists v; split; auto. apply T.gss.
  destruct H2 as (x1 & a1 & P & Q). apply orb_true_intro.
  rewrite T.gsspec in P. destruct (T.elt_eq x1 k).
  inv P. right; auto.
  left. apply H1. exists x1; exists a1; auto.
Qed.

Remark exists_for_all:
  forall m f,
  exists_ m f = negb (for_all m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change false with (negb true). generalize (T.elements m) true.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Remark for_all_exists:
  forall m f,
  for_all m f = negb (exists_ m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change true with (negb false). generalize (T.elements m) false.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Lemma for_all_false:
  forall m f,
  for_all m f = false <-> (exists x a, T.get x m = Some a /\ f x a = false).
Proof.
  intros. rewrite for_all_exists.
  rewrite negb_false_iff. rewrite exists_correct.
  split; intros (x & a & P & Q); exists x; exists a; split; auto.
  rewrite negb_true_iff in Q. auto.
  rewrite Q; auto.
Qed.

Lemma exists_false:
  forall m f,
  exists_ m f = false <-> (forall x a, T.get x m = Some a -> f x a = false).
Proof.
  intros. rewrite exists_for_all.
  rewrite negb_false_iff. rewrite for_all_correct.
  split; intros. apply H in H0. rewrite negb_true_iff in H0. auto. rewrite H; auto.
Qed.

End FORALL_EXISTS.

(** Extensional equality between trees *)

Section EXTENSIONAL_EQUALITY.

Variable A: Type.
Variable eqA: A -> A -> Prop.
Hypothesis eqAeq: Equivalence eqA.

Definition Equal (m1 m2: T.t A) : Prop :=
  forall x, match T.get x m1, T.get x m2 with
                | None, None => True
                | Some a1, Some a2 => a1 === a2
                | _, _ => False
            end.

Lemma Equal_refl: forall m, Equal m m.
Proof.
  intros; red; intros. destruct (T.get x m); auto. reflexivity.
Qed.

Lemma Equal_sym: forall m1 m2, Equal m1 m2 -> Equal m2 m1.
Proof.
  intros; red; intros. generalize (H x). destruct (T.get x m1); destruct (T.get x m2); auto. intros; symmetry; auto.
Qed.

Lemma Equal_trans: forall m1 m2 m3, Equal m1 m2 -> Equal m2 m3 -> Equal m1 m3.
Proof.
  intros; red; intros. generalize (H x) (H0 x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto;
  destruct (T.get x m3); try tauto.
  intros. transitivity a0; auto.
Qed.

Global Instance Equal_Equivalence : Equivalence Equal := {
  Equivalence_Reflexive := Equal_refl;
  Equivalence_Symmetric := Equal_sym;
  Equivalence_Transitive := Equal_trans
}.

Hypothesis eqAdec: EqDec A eqA.

(* Global Instance Equal_EqDec : EqDec (T.t A) Equal := Equal_dec. *)

End EXTENSIONAL_EQUALITY.

(** Creating a tree from a list of (key, value) pairs. *)

Section OF_LIST.

Variable A: Type.

Let f := fun (m: T.t A) (k_v: T.elt * A) => T.set (fst k_v) (snd k_v) m.

Definition of_list (l: list (T.elt * A)) : T.t A :=
  List.fold_left f l (T.empty _).

Lemma in_of_list:
  forall l k v, T.get k (of_list l) = Some v -> In (k, v) l.
Proof.
  assert (REC: forall k v l m,
           T.get k (fold_left f l m) = Some v -> In (k, v) l \/ T.get k m = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl in H. unfold f in H. simpl in H. rewrite T.gsspec in H.
    destruct H; auto.
    destruct (T.elt_eq k k1). inv H. auto. auto.
  }
  intros. apply REC in H. rewrite T.gempty in H. intuition congruence.
Qed.

Lemma of_list_dom:
  forall l k, In k (map fst l) -> exists v, T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k l m,
            In k (map fst l) \/ (exists v, T.get k m = Some v) ->
            exists v, T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl. unfold f; rewrite T.gsspec. simpl. destruct (T.elt_eq k k1).
    right; econstructor; eauto.
    intuition congruence.
  }
  intros. apply REC. auto.
Qed.

Remark of_list_unchanged:
  forall k l m, ~In k (map fst l) -> T.get k (List.fold_left f l m) = T.get k m.
Proof.
  induction l as [ | [k1 v1] l]; simpl; intros.
- auto.
- rewrite IHl by tauto. unfold f; apply T.gso; intuition auto.
Qed.

Lemma of_list_unique:
  forall k v l1 l2,
  ~In k (map fst l2) -> T.get k (of_list (l1 ++ (k, v) :: l2)) = Some v.
Proof.
  intros. unfold of_list. rewrite fold_left_app. simpl.
  rewrite of_list_unchanged by auto. unfold f; apply T.gss.
Qed.

Lemma of_list_norepet:
  forall l k v, list_norepet (map fst l) -> In (k, v) l -> T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k v l m,
            list_norepet (map fst l) ->
            In (k, v) l ->
            T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
    contradiction.
    inv H. destruct H0.
    inv H. rewrite of_list_unchanged by auto. apply T.gss.
    apply IHl; auto.
  }
  intros; apply REC; auto.
Qed.

Lemma of_list_elements:
  forall m k, T.get k (of_list (T.elements m)) = T.get k m.
Proof.
  intros. destruct (T.get k m) as [v|] eqn:M.
- apply of_list_norepet. apply T.elements_keys_norepet. apply T.elements_correct; auto.
- destruct (T.get k (of_list (T.elements m))) as [v|] eqn:M'; auto.
  apply in_of_list in M'. apply T.elements_complete in M'. congruence.
Qed.

End OF_LIST.

Lemma of_list_related:
  forall (A B: Type) (R: A -> B -> Prop) k l1 l2,
  list_forall2 (fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)) l1 l2 ->
  option_rel R (T.get k (of_list l1)) (T.get k (of_list l2)).
Proof.
  intros until k. unfold of_list.
  set (R' := fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)).
  set (fa := fun (m : T.t A) (k_v : T.elt * A) => T.set (fst k_v) (snd k_v) m).
  set (fb := fun (m : T.t B) (k_v : T.elt * B) => T.set (fst k_v) (snd k_v) m).
  assert (REC: forall l1 l2, list_forall2 R' l1 l2 ->
               forall m1 m2, option_rel R (T.get k m1) (T.get k m2) ->
               option_rel R (T.get k (fold_left fa l1 m1)) (T.get k (fold_left fb l2 m2))).
  { induction 1; intros; simpl.
  - auto.
  - apply IHlist_forall2. unfold fa, fb. rewrite ! T.gsspec.
    destruct H as [E F]. rewrite E. destruct (T.elt_eq k (fst b1)).
    constructor; auto.
    auto. }
  intros. apply REC; auto. rewrite ! T.gempty. constructor.
Qed.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).
