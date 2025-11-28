Inductive PL_val :=
| PL_bot : PL_val
| PL_poison : PL_val
| PL_int : nat -> PL_val 
| PL_address : address -> type -> PL_val
.
Definition pl_val := list PL_val.

(* ... *)

Record PL_state := {
  env : Pmap (block_id * type); (* var -> block_id × type *)
  heap : Pmap pl_val            (* bi -> pl_val *)
}.

Notation "Spl !!h bi" := ....
Notation "Spl !!e x" := ...

Notation "Spl.heap.[ addr : τ ]" := ...
Notation "Spl.heap.[ addr <- vl : τ ]" := ...


(* ... *)

(** Evaluation of places *)

(* En HLPL *)
Notation "S  |-{p}  p =>^{ perm } sp" := ...

(* En PL *)
Notation "Spl  |-{p}  p =>^{pl} (addr, t)" := ...


(* Evaluation of operands in PL *)
Reserved Notation "S  |-{op-pl}  op  =>  r" (at level 60).
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


Variable blockof : positive -> block_id * type.
Variable addrof : loan_id -> option (address * type).

(* Concretization of HLPL values *)
Inductive concr_hlpl_val : HLPL_val -> type -> pl_val -> Prop :=
| Concr_lit n : concr_hlpl_val (HLPL_int n) TInt [PL_int n] ...


(* Lifted to heaps and envs *)
Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
  concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).


(* Comparisons of PL values *)
Inductive le_val : relation PL_val :=
| lev_refl v : le_val v v
| lev_poison v : le_val v PL_poison.

(* Lifted to blocks of PL values and PL states *)
Definition le_pl_state : relation PL_state := ...
Infix "<={pl}" := le_pl_state (at level 70).

Definition le_pl_hlpl (Spl : PL_state) (S : HLPL_state) : Prop :=
  exists Spl', Compatible blockof addrof S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.

(* Equivalence between addresses and state path *)
Notation "addr ~^{ S , t } sp" := ...

(* Main lemmas about concretization *)
Lemma state_concr_implies_val_concr : 
  forall S Spl sp v,
    concr_hlpl S Spl ->
    valid_spath S sp ->
    exists addr t vl,
      addr ~^{S, t} sp /\
        concr_hlpl_val (S.[sp]) t vl /\
        Spl.h.[addr : t] = Some vl.
Qed.

Lemma concr_state_write_at_addr :
  forall S Spl sp addr v t vl,
    concr_hlpl S Spl ->
    concr_hlpl_val v t vl ->
    addr ~^{S, t} sp ->
    concr_hlpl (S.[sp <- v] ) (Spl.h.[addr <- vl : t]).
Qed.


(* Evaluating places simulation *)
Lemma eval_place_hlpl_pl_equiv :
  forall S Spl p sp perm t,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{p} p =>^{perm} sp ->
    eval_type S sp t ->
    exists addr,
      Spl |-{p} p =>^{pl} (addr, t) /\
             addr ~^{S, t} sp.
Qed.

(* Well typedness of operands *)
Definition WellTypedOperand S blockof op :=
  match op with
  | IntConst t _ => t = TInt
  | Move t p =>
      forall perm sp,
        S |-{p} p =>^{perm} sp ->
           eval_type blockof S sp t
  | Copy t p =>
      forall perm sp,
        S |-{p} p =>^{perm} sp ->
           eval_type blockof S sp t
  end.

Definition WellTypedRValue S blockof rv :=
  match rv with
  | Just t op =>
      WellTypedOperand S blockof op /\ t = op_get_type op
  | BinOp t op_l op_r =>
      WellTypedOperand S blockof op_l /\ WellTypedOperand S blockof op_r /\
        TInt = op_get_type op_l /\ TInt = op_get_type op_r /\ t = TInt
  | BorrowMut t p =>
      t = TRef
  | Pair t op_l op_r =>
      forall t0 t1,
      WellTypedOperand S blockof op_l /\ WellTypedOperand S blockof op_r /\
        t0 = op_get_type op_l /\ t1 = op_get_type op_r /\ t = (TPair t0 t1)
  end.


(* Evaluating rvalues simulation *)
Lemma HLPL_PL_Read :
  forall blockof addrof S Spl perm p sp v t,
    le_pl_hlpl blockof addrof Spl S -> (* Spl <= S *)
    S |-{p} p =>^{perm} sp ->
    eval_type blockof S sp t ->
    exists vl vl', 
      read Spl p t vl /\
        concr_hlpl_val addrof (S.[sp]) t vl' /\
        vl <={pl-val} vl'.
Qed.


Lemma Op_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl op t vS1,
    le_pl_hlpl blockof addrof Spl S -> (* Spl <= S *)
    WellTypedOperand S blockof op ->
    op_get_type op = t ->
    S |-{op} op => vS1 ->
    exists vl vl',
      Spl |-{op-pl} op => vl /\
      le_pl_hlpl blockof addrof Spl vS1.2 /\
      concr_hlpl_val addrof vS1.1 t vl' /\
      vl <={pl-val} vl'.
Qed.

  
Lemma Rvalue_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl rv t vS1,
    le_pl_hlpl blockof addrof Spl S -> (* Spl <= S *)
    WellTypedRValue S blockof rv ->
    rv_get_type rv = t ->
    S |-{rv} rv => vS1 ->
    exists blockof1 addrof1 vl vl',
      Spl |-{rv-pl} rv => vl /\
      le_pl_hlpl blockof1 addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl' /\
      vl <={pl-val} vl'.
Qed.
