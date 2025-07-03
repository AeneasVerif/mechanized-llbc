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
Require Import HLPL.


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
Local Reserved Notation "S  |-{op-pl}  op  =>  r" (at level 60).
Variant eval_operand : operand -> PL_state -> pl_val -> Prop :=
| Eval_IntConst S t n :
  S |-{op-pl} IntConst t n => [PL_int n]
| Eval_copy S t p vl
    (Hread : read S p t vl) :
  S |-{op-pl} Copy t p => vl
| Eval_move S t p vl
    (Hread : read S p t vl) :
  S |-{op-pl} Move t p => vl
where "S |-{op-pl} op => r" := (eval_operand op S r).

Local Reserved Notation "S  |-{rv-pl}  rv =>  r" (at level 60).
Variant eval_rvalue: rvalue -> PL_state -> pl_val -> Prop :=
| Eval_just S t op vl
  (Hop : S |-{op-pl} op => vl) :
  S |-{rv-pl} Just t op => vl
| Eval_bin_op S t op_l n_l op_r n_r
    (Hl : S |-{op-pl} op_l => [PL_int n_l])
    (Hr : S |-{op-pl} op_r => [PL_int n_r]) :
  S |-{rv-pl} BinOp t op_l op_r => [PL_int (n_l + n_r)]
| Eval_ptr S t p addr
    (Haddr : read_address S p t addr) :
  S |-{rv-pl} &mut p : (TRef t) => [PL_address addr]
| Eval_pair S t op_l vl_l op_r vl_r
    (Hl : S |-{op-pl} op_l => vl_l)
    (Hr : S |-{op-pl} op_r => vl_r) :
  S |-{rv-pl} Pair t op_l op_r =>  (vl_l ++ vl_r)
where "S |-{rv-pl} rv => r" := (eval_rvalue rv S r).

Reserved Notation "S  |-{stmt-pl}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> statement_result -> PL_state -> PL_state -> Prop :=
| Eval_nop S : S |-{stmt-pl} Nop => rUnit, S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r
    (eval_stmt_l : S0 |-{stmt-pl} stmt_l => rUnit, S1)
    (eval_stmt_r : S1 |-{stmt-pl} stmt_r => r, S2) :
  S0 |-{stmt-pl} stmt_l ;; stmt_r => r, S2
| Eval_seq_panic S0 S1 stmt_l stmt_r
    (eval_stmt_l : S0 |-{stmt-pl} stmt_l => rPanic, S1) :
  S0 |-{stmt-pl} stmt_l ;; stmt_r => rPanic, S1
| Eval_assign S vl S' p rv t
    (eval_rv : S |-{rv-pl} rv => vl)
    (Hwrite : write S p t vl S'):
  S |-{stmt-pl} ASSIGN p <- rv => rUnit, S'
where "S |-{stmt-pl} stmt => r , S'" := (eval_stmt stmt r S S').

(* Concretization of HLPL values to PL values *)

Section Concretization.
  Variable blockof : var -> option (block_id * type).
  Variable blockofinv : block_id * type -> option var.
  Variable addrof : loan_id -> option address.
  Variable imageof : list (block_id * type).

  Local Open Scope stdpp_scope.

  Inductive concr_hlpl_val : HLPL_val -> type -> pl_val -> Prop :=
  | Concr_lit n : concr_hlpl_val (HLPL_int n) TInt [PL_int n]
  | Concr_bot s t (Hs : s = ListDef.repeat PL_poison (sizeof t)) : 
    concr_hlpl_val HLPL_bot t s
  | Concr_pair v0 t0 vl0 v1 t1 vl1
      (H0 : concr_hlpl_val v0 t0 vl0)
      (H1 : concr_hlpl_val v1 t1 vl1) :
    concr_hlpl_val (HLPL_pair v0 v1) (TPair t0 t1) (vl0 ++ vl1)
  | Concr_loc l v t vl
      (Hv : concr_hlpl_val v t vl) :
    concr_hlpl_val (HLPL_loc l v) t vl
  | Concr_ptr_loc l addr t
      (Haddr : addrof l = Some addr) :
    concr_hlpl_val (HLPL_ptr l) (TRef t) [PL_address addr]
  .

  Fixpoint concr_hlpl_val_comp (v : HLPL_val) (t : type) :=
    match v, t with
    | HLPL_int n, TInt =>
        Some [ PL_int n ]
    | HLPL_bot, _ =>
        Some (ListDef.repeat PL_poison (sizeof t))
    | HLPL_pair v0 v1, TPair t0 t1 =>
        match concr_hlpl_val_comp v0 t0, concr_hlpl_val_comp v1 t1 with
        | Some vl0, Some vl1 => Some (vl0 ++ vl1)
        | _, _ => None
        end
    | HLPL_loc l v, t =>
        concr_hlpl_val_comp v t
    | HLPL_ptr l, TRef t =>
        match addrof l with
        | Some addr => Some [PL_address addr]
        | _ => None
        end
    | _, _ => None
   end. 

  Lemma concr_val_comp_implies_concr_val: forall v t vl,
       concr_hlpl_val_comp v t = Some vl -> concr_hlpl_val v t vl.
  Proof.
    intros v ; induction v; intros t vl H ; subst.
    - destruct t; simpl in * ;
        injection H ; intros ; constructor; easy.
    - destruct t; simpl in * ;
        try injection H as H; subst ; try constructor ; discriminate.
    - constructor; auto.
    - destruct t ; simpl in * ; try discriminate.
      destruct (addrof l) eqn:Haddr.
      * injection H as H ; subst ; constructor. assumption.
      * discriminate.
    - destruct t; try discriminate ; simpl in *.
      remember (concr_hlpl_val_comp v1 t1) as concr1.
      remember (concr_hlpl_val_comp v2 t2) as concr2.
      destruct concr1, concr2; try (subst ; discriminate). 
      injection H as H ; rewrite <- H. constructor ; auto.
  Qed.  

  Lemma concr_val_implies_concr_val_comp : forall v t vl,
       concr_hlpl_val v t vl -> concr_hlpl_val_comp v t = Some vl.
  Proof.
    intros v t vl H ; induction H; subst ; simpl ; try easy.
    - rewrite IHconcr_hlpl_val1, IHconcr_hlpl_val2; reflexivity.
    - rewrite Haddr ; easy.
  Qed.

  Lemma concr_val_eq_concr_val_comp : forall v t vl,
      concr_hlpl_val v t vl <-> concr_hlpl_val_comp v t = Some vl.
  Proof.
    split.
    apply concr_val_implies_concr_val_comp. apply concr_val_comp_implies_concr_val.
  Qed.

  Definition concr_hlpl_heap (S : HLPL_state) (h : Pmap pl_val) : Prop :=
    forall x v bi t, (vars S) !! (encode_var x) = Some v -> 
             blockof x = Some (bi, t) ->
             exists vl, concr_hlpl_val v t vl.

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall x bi t, blockof x = Some (bi, t) -> env !! (encode_var x) = Some (bi, t).

  Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
    concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).

  Inductive HLPL_read_offset : HLPL_val -> type -> nat -> HLPL_val -> type -> Prop :=
  | Read_zero v t : HLPL_read_offset v t 0 v t
  | Read_pair_left v0 t0 v1 t1 n v t
      (Hn : n < sizeof t0)
      (Hrec : HLPL_read_offset v0 t0 n v t) :
    HLPL_read_offset (HLPL_pair v0 v1) (TPair t0 t1) n v t
  | Read_pair_right v0 t0 v1 t1 n v t
      (Hn : n >= sizeof t0)
      (Hrec : HLPL_read_offset v1 t1 (n - sizeof t0) v t) :
    HLPL_read_offset (HLPL_pair v0 v1) (TPair t0 t1) n v t
  | Read_offset_loc v t n l v' t'
      (Hrec : HLPL_read_offset v t n v' t') :
    HLPL_read_offset (HLPL_loc l v) t n v' t'.

  Inductive HLPL_read_address : HLPL_state -> (block_id * type) -> HLPL_val -> type -> Prop :=
  | Read_address S bi t n v v' x
      (Hbinv : blockofinv (bi, t) = Some x)
      (Henv : lookup x (vars S) = Some v)
      (Hoff : HLPL_read_offset v t n v' t) :
    HLPL_read_address S (bi, t) v' t.

  Inductive spath_offset : vpath -> type -> nat -> Prop :=
  | Spath_off_int :
    spath_offset [] TInt 0
  | Spath_off_pair_left t0 t1 p n
      (H : spath_offset p t0 n) :
      spath_offset (0 :: p) (TPair t0 t1) n
  | Spath_off_pair_right t0 t1 p n
      (H : spath_offset p t1 n) :
      spath_offset (1 :: p) (TPair t0 t1) (sizeof t0 + n).

  Inductive read_val (S : HLPL_state) : type -> vpath -> address -> address -> Prop :=
  | Read_val_int addr t: read_val S t [] addr addr
  | Read_val_pair_left t0 t1 p bi off bi' off'
      (Hr : read_val S t0 p (bi, off) (bi', off')) :
    read_val S (TPair t0 t1) (0 :: p) (bi, off) (bi', off')
  | Read_val_pair_right t0 t1 p bi off bi' off'
      (Hr : read_val S t1 p (bi, off + sizeof t0) (bi', off')) :
    read_val S (TPair t0 t1) (1 :: p) (bi, off) (bi', off')
  | Read_val_loc t p bi off bi' off'
    (Hr : read_val S t p (bi, off) (bi', off')) :
    read_val S t p (bi, off) (bi', off').

  Inductive read_state (S : HLPL_state) : spath -> address -> Prop :=
  | Read_state p v bi bi' off t
      (Hv : (vars S) !! p.1 = Some v)
      (Hb : blockof p.1 = Some (bi, t))
      (H : read_val S t p.2 (bi, 0) (bi', off)) :
    read_state S p (bi', off).

  Record Compatible (S : HLPL_state) : Prop :=
    mkCompatible
      { block_dom :
        forall (x : var), exists v1 v2,
          (vars S) !! (encode_var x) = Some v1 -> blockof x = Some v2
      ; correct_addrof :
        forall (sp : spath) (addr : address) l v,
          read_state S sp addr -> S.[sp] = loc (l, v) -> addrof l = Some addr
      ; reachable_loc :
        forall l sp v,
          valid_spath  S sp -> S.[sp] = loc (l, v) ->
          exists addr, read_state S sp addr
      }.

  Inductive le_val : PL_val -> PL_val -> Prop :=
  | lev_refl v : le_val v v
  | lev_poison v : le_val PL_poison v.

  Definition le_block (b1 b2 : pl_val) :=
    Forall2 le_val b1 b2.

  Inductive le_heap: Pmap pl_val -> Pmap pl_val -> Prop :=
  | lem h1 h2 b1 b2
      (H : forall bi, h1 !! bi = Some b1 -> h2 !! bi = Some b2 /\ le_block b1 b2) :
    le_heap h1 h2.

  Inductive le_state : PL_state -> PL_state -> Prop :=
  | les S1 S2 (He : env S1 = env S2) (Hmem : le_heap (heap S1) (heap S2)) :
    le_state S1 S2.

  Infix "<={pl}" := le_state (at level 70).

  Lemma HLPL_PL_Read : forall S Spl Spl' t,
      Compatible S ->
      concr_hlpl S Spl' ->
      Spl <={pl} Spl' ->
      forall x p perm v pi, eval_place S perm (x, p) pi -> S.[pi] = v ->
      exists vl, read Spl (x, p) t vl.
  Proof.
    intros S Spl Spl' t Hcomp Hconcr Hle x p perm v pi sp Hevp.
  Admitted.
End Concretization.


Section Tests.
  Notation x := 1%positive.
  Notation y := 2%positive.
  Notation b1 := 1%positive.
  Notation b2 := 2%positive.
  Notation b3 := 3%positive.
  Notation l1 := 0%nat.
  Notation l2 := 1%nat.

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

  Goal pl_state_1 |-{op-pl} IntConst TInt 3 => [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Copy (TPair TInt TInt) (x, []) => [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Move (TPair TInt TInt) (x, []) => [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{rv-pl} Just (TPair TInt TInt) (Copy (TPair TInt TInt) (x, [])) =>
         [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} BinOp TInt (INT 1) (INT 4) => [PL_int (1 + 4)].
  Proof. repeat econstructor. Qed.

  Goal pl_state_6 |-{rv-pl} BinOp TInt (Move TInt (x, [Field(Second) ; Field(Second)])) (INT 4) =>
         [PL_int (7 + 4)].
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} &mut (x, []) : (TRef TInt) => [PL_address (b1, 0)].
  Proof. repeat econstructor.  Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (IntConst TInt 0) (IntConst TInt 1)
       => ([PL_int 0] ++ [PL_int 1]).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (IntConst TInt 0) (Move TInt (x, []))
       => ([PL_int 0] ++ [PL_poison]).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_7.
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_1.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_9.
  Proof. repeat econstructor. Qed.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_8.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  (** CONCRETIZATION TESTS **)

  Definition addroff := (fun l => if l =? l1 then Some (b1, 1) else None).

  Goal concr_hlpl_val addroff (HLPL_int 3) TInt [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff (loc (l1, (HLPL_int 3))) TInt [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff HLPL_bot (TPair TInt TInt) [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff
    HLPL_bot (TPair (TPair TInt TInt) TInt) [PL_poison ; PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff
    (HLPL_pair (HLPL_int 3) (HLPL_int 4)) (TPair TInt TInt)
    ([PL_int 3] ++ [PL_int 4]).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff
    (HLPL_pair (HLPL_int 3) (HLPL_pair (HLPL_int 7) (HLPL_int 11))) (TPair TInt (TPair TInt TInt))
    ([PL_int 3] ++ ([PL_int 7] ++ [PL_int 11])).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addroff
    (ptr (l1)) (TRef TInt) [PL_address (b1, 1)].
  Proof. repeat econstructor. Qed.
End Tests.
