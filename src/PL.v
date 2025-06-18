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


Definition block_id := positive.
Definition offset := nat.
Definition address := (block_id * offset)%type.

Inductive PL_val :=
| PL_bot : PL_val
| PL_poison : PL_val
| PL_int : nat -> PL_val 
| PL_address : address -> PL_val
.

Definition pl_val := list PL_val.

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

(* Bind Scope pl_scope with PL_val. *)
Open Scope pl_scope.

Inductive copy_val : PL_val -> PL_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (PL_int n) (PL_int n).

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


(* Evaluation of Expressions in PL *)
Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).
Variant eval_operand : operand -> PL_state -> pl_val -> Prop :=
| Eval_IntConst S t n :
  S |-{op} IntConst t n => [PL_int n]
| Eval_copy S t p vl
    (Hread : read S p t vl) :
  S |-{op} Copy t p => vl
| Eval_move S t p vl
    (Hread : read S p t vl) :
  S |-{op} Move t p => vl
where "S |-{op} op => r" := (eval_operand op S r).

Local Reserved Notation "S  |-{rv}  rv =>  r" (at level 60).
Variant eval_rvalue: rvalue -> PL_state -> pl_val -> Prop :=
| Eval_just S t op vl
  (Hop : S |-{op} op => vl) :
  S |-{rv} Just t op => vl
| Eval_bin_op S t op_l n_l op_r n_r
    (Hl : S |-{op} op_l => [PL_int n_l])
    (Hr : S |-{op} op_r => [PL_int n_r]) :
  S |-{rv} BinOp t op_l op_r => [PL_int (n_l + n_r)]
| Eval_ptr S t p addr
    (Haddr : read_address S p t addr) :
  S |-{rv} &mut p : (TRef t) => [PL_address addr]
| Eval_pair S t op_l vl_l op_r vl_r
    (Hl : S |-{op} op_l => vl_l)
    (Hr : S |-{op} op_r => vl_r) :
  S |-{rv} Pair t op_l op_r =>  (vl_l ++ vl_r)
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> statement_result -> PL_state -> PL_state -> Prop :=
| Eval_nop S : S |-{stmt} Nop => rUnit, S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r
    (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
    (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :
  S0 |-{stmt} stmt_l ;; stmt_r => r, S2
| Eval_seq_panic S0 S1 stmt_l stmt_r
    (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
  S0 |-{stmt} stmt_l ;; stmt_r => rPanic, S1
| Eval_assign S vl S' p rv t
    (eval_rv : S |-{rv} rv => vl)
    (Hwrite : write S p t vl S'):
  S |-{stmt} ASSIGN p <- rv => rUnit, S'
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').


Section Tests.
  Notation x := 1%positive.
  Notation y := 2%positive.
  Notation b1 := 1%positive.
  Notation b2 := 2%positive.
  Notation b3 := 3%positive.

  Local Open Scope stdpp_scope.

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
  Definition pl_state_6 : PL_state :=
    {|
      env :=
        {[
            x := (b1, TPair TInt (TPair TInt TInt))
        ]};
      heap :=
        {[
            b1 := [PL_int 0 ; PL_int 1 ; PL_int 7]
        ]}
    |}.
  Definition pl_state_7 : PL_state :=
    {|
      env := {[ x := (b1, TInt) ]};
      heap := {[ b1 := [PL_int 3] ]}
    |}.
  Definition pl_state_8 : PL_state :=
    {|
      env := {[ x := (b1, TInt) ; y := (b2, TInt) ]};
      heap := {[ b1 := [PL_poison] ; b2 := [PL_poison] ]}
    |}.
  Definition pl_state_9 : PL_state :=
    {|
      env := {[ x := (b1, TInt) ; y := (b2, TInt) ]};
      heap := {[ b1 := [PL_int 3] ; b2 := [PL_int 7] ]}
    |}.

  Local Close Scope stdpp_scope.

  (** READ AND WRITES TESTS **)

  Goal exists S, write pl_state_1 (1%positive, []) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (1%positive, [Field(First)]) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (1%positive, [Field(Second)]) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal read pl_state_3 (x, Deref :: [Field(First)]) TInt [PL_int 0].
  Proof. repeat econstructor. Qed.

  Goal read pl_state_3 (x, [Field(Second)]) TInt [PL_int 0].
  Proof. repeat econstructor. Qed.

  Goal read pl_state_4 (x, [Deref ; Deref]) TInt [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal write pl_state_5 (x, [Deref ; Deref]) TInt [PL_int 3] pl_state_4.
  Proof. repeat econstructor. Qed.

  (** EXPRESSION EVALUATION TESTS **)

  Goal pl_state_1 |-{op} IntConst TInt 3 => [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op} Copy (TPair TInt TInt) (x, []) => [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op} Move (TPair TInt TInt) (x, []) => [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{rv} Just (TPair TInt TInt) (Copy (TPair TInt TInt) (x, [])) =>
         [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv} BinOp TInt (INT 1) (INT 4) => [PL_int (1 + 4)].
  Proof. repeat econstructor. Qed.

  Goal pl_state_6 |-{rv} BinOp TInt (Move TInt (x, [Field(Second) ; Field(Second)])) (INT 4) =>
         [PL_int (7 + 4)].
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv} &mut (x, []) : (TRef TInt) => [PL_address (b1, 0)].
  Proof. repeat econstructor.  Qed.

  Goal pl_state_1 |-{rv} Pair (TPair TInt TInt) (IntConst TInt 0) (IntConst TInt 1)
       => ([PL_int 0] ++ [PL_int 1]).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv} Pair (TPair TInt TInt) (IntConst TInt 0) (Move TInt (x, []))
       => ([PL_int 0] ++ [PL_poison]).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_7.
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_1.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  Goal pl_state_8 |-{stmt}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_9.
  Proof. repeat econstructor. Qed.

  Goal pl_state_8 |-{stmt}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_8.
  Proof. repeat econstructor. Fail reflexivity. Abort.
End Tests.
