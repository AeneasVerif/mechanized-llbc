Require Import lang.
Require Import base.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree.
Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import SimulationUtils.


Definition block_id := positive.
Definition offset := nat.
Definition address := (block_id * offset)%type.

Inductive PL_val :=
| PL_bot : PL_val
| PL_poison : PL_val
| PL_int : nat -> PL_val 
| PL_loc : loan_id -> PL_val -> PL_val
| PL_ptr : loan_id -> PL_val
| PL_pair : PL_val -> PL_val -> PL_val
| PL_address : address -> PL_val
.

Definition pl_val := list PL_val.

Variant PL_nodes :=
| PL_botC : PL_nodes
| PL_poisonC: PL_nodes
| PL_intC : nat -> PL_nodes
| PL_locC : loan_id -> PL_nodes
| PL_ptrC : loan_id -> PL_nodes
| PL_pairC : PL_nodes
| PL_addressC : address -> PL_nodes
.

Instance EqDec_PL_nodes : EqDecision PL_nodes.
Proof. unfold EqDecision, Decision. repeat decide equality. Qed.

Definition PL_arity c := match c with
| PL_botC => 0
| PL_poisonC => 0
| PL_intC _ => 0
| PL_locC _ => 1
| PL_ptrC _ => 0
| PL_pairC => 2
| PL_addressC _ => 0
end.

Definition PL_get_node v := match v with
| PL_bot => PL_botC
| PL_poison => PL_poisonC
| PL_int n => PL_intC n
| PL_loc l _ => PL_locC l
| PL_ptr l => PL_ptrC l
| PL_pair _ _ => PL_pairC
| PL_address addr => PL_addressC addr
end.

Definition PL_children v := match v with
| PL_bot => []
| PL_poison => []
| PL_int _ => []
| PL_loc _ v => [v]
| PL_ptr l => []
| PL_pair fst snd => [fst ; snd]
| PL_address addr => []
end.

Definition PL_fold c vs := match c, vs with
| PL_botC, _ => PL_bot
| PL_poisonC, _ => PL_poison
| PL_intC n, [] => PL_int n
| PL_locC l, [v] => PL_loc l v
| PL_ptrC l, [] => PL_ptr l
| PL_pairC, [fst; snd] => PL_pair fst snd
| PL_addressC addr, [] => PL_address addr
| _, _ => PL_bot
end.

Fixpoint PL_weight node_weight v :=
  match v with
  | PL_loc l v => node_weight (PL_locC l) + PL_weight node_weight v
  | PL_pair fst snd =>
      node_weight (PL_pairC) +
        PL_weight node_weight fst + PL_weight node_weight snd
  | v => node_weight (PL_get_node v)
end.

Program Instance ValuePL : Value PL_val PL_nodes := {
  arity := PL_arity;
  get_node := PL_get_node;
  children := PL_children;
  fold_value := PL_fold;
  vweight := PL_weight;
  bot := PL_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_node eq_children; inversion eq_node; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H;
  first [ rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->]
        | destruct (length_2_is_pair H) as [fst [snd ->] ] ];
  reflexivity.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] 
        | destruct (length_2_is_pair H) as [fst [snd ->] ] ];
  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; unfold PL_children; cbn; lia. Qed.

Record PL_state := {
  env : Pmap (block_id * type);
  heap : Pmap pl_val
}.

Fixpoint sizeof (tau : type) : nat :=
  match tau with
  | TInt | TRef _ => 1
  | TPair tau1 tau2 => sizeof tau1 + sizeof tau2
  end.

Declare Scope pl_scope.
Delimit Scope pl_scope with pl.

(* TODO: set every priority to 0? *)
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level).
Reserved Notation "'ptrC' ( l )" (at level 0).

(* Notation "'bot'" := PL_bot: pl_scope. *)
Notation "'loc' ( l , v )" := (PL_loc l v) : pl_scope.
Notation "'ptr' ( l )" := (PL_ptr l) : pl_scope.

Notation "'botC'" := PL_botC: pl_scope.
Notation "'locC' ( l )" := (PL_locC l) : pl_scope.
Notation "'ptrC' ( l )" := (PL_ptrC l) : pl_scope.

(* Bind Scope pl_scope with PL_val. *)
Open Scope pl_scope.

Inductive copy_val : PL_val -> PL_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (PL_int n) (PL_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w
| Copy_pair v1 v1' v2 v2' (H1 : copy_val v1 v1') (H2 : copy_val v2 v2') :
  copy_val (PL_pair v1 v2) (PL_pair v1' v2').

(* Functions to lookup and update PL states *)
Definition lookup_block_and_type_env (x : var) (S : PL_state)
  : option (block_id * type) :=
  lookup x (env S).

Definition lookup_env (x : var) (S : PL_state) : option block_id :=
  match lookup x (env S) with
  | None => None
  | Some (bi, _) => Some bi
  end.

Definition lookup_type_env (x : var) (S : PL_state) : option type :=
  match lookup x (env S) with
  | None => None
  | Some (_, T) => Some T
  end.
  
Definition lookup_heap (bi : block_id) (S : PL_state) : option (list PL_val) :=
  lookup bi (heap S).

Definition lookup_heap_at_addr (S : PL_state) (addr : address) : option PL_val :=
  let (bi, off) := addr in
  match lookup bi (heap S) with
  | None => None
  | Some vl =>
      List.nth_error vl off
  end.

Definition update_env (S : PL_state) (e : Pmap (block_id * type)) :=
  {|env := e ; heap := heap S |}.

Definition update_heap (S : PL_state) (h : Pmap pl_val) :=
  {|env := env S ; heap := h |}.
  
Open Scope stdpp_scope.

Inductive read_address (S : PL_state) : place -> type -> address -> Prop :=
| Read_Addr_Var x t bi
    (HS : lookup_block_and_type_env x S = Some (bi, t)) :
  read_address S (x, []) t (bi, 0)
| Read_Addr_Deref x p t bi n bi' n' vl
    (Hp : read_address S (x, p) (TRef t) (bi, n))
    (Hheap : (lookup_heap bi S = Some vl))
    (Hvl : List.nth_error vl n  = Some (PL_address (bi', n'))) :
  read_address S (x, Deref :: p) t (bi', n')
| Read_Addr_ProjPairLeft x path t0 t1 bi n
  (H : read_address S (x, path) (TPair t0 t1) (bi, n)) :
    read_address S (x, (Field First) :: path) t0 (bi, n)
| Read_Addr_ProjPairRight x path t0 t1 bi n
  (H : read_address S (x, path) (TPair t0 t1) (bi, n)) :
  read_address S (x, (Field Second) :: path) t1 (bi, n + sizeof t0).

Variant read (S : PL_state) (p : place) (t : type) (vl : pl_val) : Prop :=
  | Read bi n vl'
      (Haddr : read_address S p t (bi, n))
      (Hheap : Some vl' = lookup_heap bi S)
      (Hsub : vl = firstn (sizeof t) (skipn n vl')) :
    read S p t vl.

Variant write (S : PL_state) (p : place) (t : type) (vl : pl_val)
  : PL_state -> Prop :=
  | Write bi n vl' vl'' h
      (Haddr : read_address S p t (bi, n))
      (Hlu : Some vl' = lookup_heap bi S)
      (Hcut : vl'' = (firstn n vl') ++ vl ++ (skipn (n + sizeof t) vl'))
      (Hheap : h = alter (fun _ => vl'') bi (heap S)) :
      write S p t vl (update_heap S h).

Section TestReadWrite.
Local Open Scope stdpp_scope.

Notation x := 1%positive.
Notation y := 2%positive.
Notation b1 := 1%positive.
Notation b2 := 2%positive.
Notation b3 := 3%positive.
Definition pl_state_1 : PL_state :=
  {|
    env := {[ x := (b1, TInt) ]};
    heap := {[ b1 := [PL_poison] ]}
  |}.
Definition pl_state_2 : PL_state :=
  {|
    env := {[ x := (b1, TPair TInt TInt) ]};
    heap := {[ b1 := [PL_poison; PL_poison] ]}
  |}.
Definition pl_state_3 : PL_state :=
  {|
    env := {[ x := (b1, TPair (TRef TInt) TInt) ]};
    heap := {[ b1 := [PL_address (b1, 1); PL_int 0] ]}
  |}.
Definition pl_state_4 : PL_state :=
  {|
    env := {[ x := (b1, TRef (TRef TInt)) ]};
    heap :=
      {[
          b1 := [PL_address (b2, 1)] ;
          b2 := [PL_int 3 ; PL_address (b2, 0)]
      ]}
  |}.
Definition pl_state_5 : PL_state :=
  {|
    env := {[ x := (b1, TRef (TRef TInt)) ]};
    heap :=
      {[
          b1 := [PL_address (b2, 1)] ;
          b2 := [PL_poison ; PL_address (b2, 0)]
      ]}
  |}.

Goal exists S, write pl_state_1 (1%positive, []) TInt [PL_int 0] S.
Proof.
  repeat econstructor.
Qed.

Goal exists S, write pl_state_2 (1%positive, [Field(First)]) TInt [PL_int 0] S.
Proof.
  repeat econstructor.
Qed.

Goal exists S, write pl_state_2 (1%positive, [Field(Second)]) TInt [PL_int 0] S.
Proof.
  repeat econstructor.
Qed.

Goal read pl_state_3 (x, Deref :: [Field(First)]) TInt [PL_int 0].
Proof.
  repeat econstructor.
Qed.

Goal read pl_state_3 (x, [Field(Second)]) TInt [PL_int 0].
Proof.
  repeat econstructor.
Qed.

Goal read pl_state_4 (x, [Deref ; Deref]) TInt [PL_int 3].
Proof.
  repeat econstructor.
Qed.

Goal write pl_state_5 (x, [Deref ; Deref]) TInt [PL_int 3] pl_state_4.
Proof.
  repeat econstructor.
Qed.
End TestReadWrite.
