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

Definition lookup_heap_at_addr (addr : address) (t : type) (S : PL_state) : pl_val :=
  let size := sizeof t in
  let (bi, off) := addr in
  match lookup bi (heap S) with
  | None => []
  | Some vl =>
      firstn size (skipn off vl)
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
  Variable blockof : var -> block_id * type.
  Variable blockofinv : block_id * type -> var.
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
    forall x bi t v,
      S.[ (encode_var x, []) ] = v ->
      v <> bot ->
      blockof x = (bi, t) ->
      exists vl, concr_hlpl_val v t vl /\ h !! bi = Some vl .

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall x bi t v,
      vars S !! x = Some v -> 
      blockof x = (bi, t) ->
      env !! x = Some (bi, t).

  Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
    concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).

  (** Reading in HLPL state with addresses, as done in the PhD of Son *)
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
      (Hbinv : blockofinv (bi, t) = x)
      (Henv : lookup x (vars S) = Some v)
      (Hoff : HLPL_read_offset v t n v' t) :
    HLPL_read_address S (bi, t) v' t.

  (** [spath_offset vp t n] is inhabited when following a vpath [vp] in a value of type [t] is equivalent to taking the subvalue found at offset [n] *)
  Inductive spath_offset : vpath -> type -> nat -> Prop :=
  | Spath_off_int :
    spath_offset [] TInt 0
  | Spath_off_pair_left t0 t1 p n
      (H : spath_offset p t0 n) :
      spath_offset (0 :: p) (TPair t0 t1) n
  | Spath_off_pair_right t0 t1 p n
      (H : spath_offset p t1 n) :
      spath_offset (1 :: p) (TPair t0 t1) (sizeof t0 + n).

  (** TODO: delete? *)
  Variant follow_path : nat -> address * type -> address * type -> Prop :=
  | Follow_left bi off t0 t1 :
    follow_path 0 ((bi, off), TPair t0 t1) ((bi, off), t0)
  | Follow_right bi off t0 t1 :
    follow_path 0 ((bi, off), TPair t0 t1) ((bi, off + sizeof t0), t1)
  | Follow_loc bi off t :
    follow_path 0 ((bi, off), t) ((bi, off), t).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.heap(addr) *)
  Inductive addr_spath_equiv (S : HLPL_state) :
    address -> type -> spath -> Prop :=
  | Addr_spath_base bi t x
      (H : blockof x = (bi, t)) :
    addr_spath_equiv S (bi, 0) t (encode_var x, [])
  | Addr_spath_pointer bi bi' off off' t enc_x enc_y vp vp' l
      (Hloc : get_node (S.[(enc_x, vp)]) = HLPL_locC l)
      (Hptr : get_node (S.[(enc_y, vp')]) = HLPL_ptrC l)
      (Hrec : addr_spath_equiv S (bi', off') (TRef t) (enc_y, vp'))
      (Haddr : addrof l = Some (bi, off)) :
    addr_spath_equiv S (bi, off) t (enc_x, vp)
  | Addr_spath_pair_first bi off enc_x pi t0 t1
      (Hrec : addr_spath_equiv S (bi, off) (TPair t0 t1) (enc_x, pi)) :
    addr_spath_equiv S (bi, off) t0 (enc_x, pi ++ [0])
  | Addr_spath_pair_second bi off enc_x pi t0 t1
      (Hrec : addr_spath_equiv S (bi, off) (TPair t0 t1) (enc_x, pi)) :
    addr_spath_equiv S (bi, off + sizeof t0) t1 (enc_x, pi ++ [1])
  | Addr_spath_loc bi off enc_x pi t l
      (Hloc : get_node (S.[(enc_x, pi)]) = HLPL_locC l)
      (Hrec : addr_spath_equiv S (bi, off) t (enc_x, pi)) :
    addr_spath_equiv S (bi, off) t (enc_x, pi ++ [0]).

  (** [addr_proj proj (addr, t) (addr', t')] when the projection [proj] of the value at address [addr] of type [t] gives the value at address [addr'] of type [t'] *)
  Variant follow_path_addr : nat -> address * type -> address * type -> Prop :=
  | FP_Addr_first bi off t0 t1 :
    follow_path_addr 0 ((bi, off), TPair t0 t1) ((bi, off), t0)
  | FP_Addr_second bi off t0 t1 :
    follow_path_addr 1 ((bi, off), TPair t0 t1) ((bi, off + sizeof t0), t1).

  Variant follow_path_val : nat -> pl_val * type -> pl_val * type -> Prop :=
  | FP_Val_first vl t0 t1 :
    follow_path_val 0 (vl, TPair t0 t1) (firstn (sizeof t0) vl, t0)
  | FP_Val_second vl t0 t1 :
    follow_path_val 1 (vl, TPair t0 t1) (skipn (sizeof t0) vl, t1).

  Lemma concr_val_size : forall v vl t, concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v vl t Hconcr. induction Hconcr ; auto ; try reflexivity.
    - rewrite Hs, repeat_length. reflexivity.
    - rewrite List.length_app. simpl. lia.
  Qed.

  Lemma follow_path_PL_HLPL_valid : forall vl vl' t t' v i,
      get_node v <> HLPL_botC ->
      ~ (exists l, get_node v = HLPL_locC l) ->
      concr_hlpl_val v t vl ->
      follow_path_val i (vl, t) (vl', t') ->
      concr_hlpl_val (v.[[ [i] ]]) t' vl'.
  Proof.
    intros vl vl' t t' v i Hbot Hloc Hconcr Hpath.
    destruct Hconcr.
    - inversion Hpath.
    - contradiction.
    - inversion Hpath ; subst.
      * simpl. rewrite (concr_val_size _ _ _ Hconcr1), take_app_length. assumption.
      * simpl. rewrite (concr_val_size _ _ _ Hconcr1), drop_app_length. assumption.
    - exfalso. apply Hloc. exists l. reflexivity.
    - inversion Hpath.
  Qed.

  Lemma follow_path_PL_HLPL_valid_stutter : forall vl t v,
      get_node v <> HLPL_botC ->
      (exists l, get_node v = HLPL_locC l) ->
      concr_hlpl_val v t vl ->
      concr_hlpl_val (v.[[ [0] ]]) t vl.
  Proof.
    intros vl t v Hbot [l Hloc] Hconcr.
    destruct v ; simpl in Hloc ; try easy.
    injection Hloc ; intros ; inversion Hconcr ; subst. auto.
  Qed.

  Inductive eval_proj_addr : PL_state -> proj -> address * type -> address * type -> Prop :=
  | Addr_first S addr addr' t t'
    (H : follow_path_addr 0 (addr, t) (addr', t')) :
    eval_proj_addr S (Field First) (addr, t) (addr', t')
  | Addr_second S addr addr' t t'
    (H : follow_path_addr 1 (addr, t) (addr', t')) :
    eval_proj_addr S (Field Second) (addr, t) (addr', t')
  | Addr_deref S bi off bi' off' t pl 
      (Haddr : heap S !! bi = Some pl)
      (Hoff : List.nth_error pl off = Some (PL_address (bi', off'))) :
    eval_proj_addr S Deref ((bi, off), TRef t) ((bi', off'), t).

  Record Compatible (S : HLPL_state) : Prop :=
    mkCompatible
      { block_dom :
        forall (x : var) (v : HLPL_val) perm (sp : spath), 
          eval_place S perm (x, []) sp ->
          valid_spath S sp ->
          exists bi t, blockof x = (bi, t)
      ; correct_addrof :
        forall (sp : spath) (addr : address) t l,
          addr_spath_equiv S addr t sp ->
          get_node (S.[sp]) = HLPL_locC l ->
          addrof l = Some addr
      ; reachable_loc :
        forall l sp,
          valid_spath S sp ->
          get_node (S.[sp]) = HLPL_locC l ->
          exists addr t, addr_spath_equiv S addr t sp
      }.

  Inductive le_val : PL_val -> PL_val -> Prop :=
  | lev_refl v : le_val v v
  | lev_poison v : le_val v PL_poison.

  Definition le_block (b1 b2 : pl_val) :=
    Forall2 le_val b1 b2.

  Definition le_heap (h1 h2: Pmap pl_val) : Prop :=
    forall bi b1 b2, h1 !! bi = Some b2 -> h2 !! bi = Some b2 -> le_block b1 b2.

  Definition le_state (Spl1 Spl2 : PL_state) : Prop :=
    env Spl1 = env Spl2 /\ le_heap (heap Spl1) (heap Spl2).

  Infix "<={pl}" := le_state (at level 70).

  Definition le_pl_hlpl (Spl : PL_state) (S : HLPL_state) : Prop :=
    exists Spl', Compatible S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.

  (* This hypothesis is necessary to prove that the diagram commutes with dereference, it should be a consequence that the PL_state Spl is the concretization of the HLPL state S *)
  Definition addresses_are_compatible (S : HLPL_state) (Spl : PL_state) :=
    forall bi off t sp l,
      addr_spath_equiv S (bi, off) (TRef t) sp ->
      get_node (S.[ sp ]) = ptrC(l) ->
      exists bi' off',
      lookup_heap_at_addr (bi, off) (TRef t) Spl = [PL_address (bi', off')] /\
      addrof l = Some (bi', off').

  Definition ref_types_are_preserved (S : HLPL_state) (Spl : PL_state) :=
    forall sp addr l t,
      addr_spath_equiv S addr t sp ->
      get_node (S.[ sp ]) = ptrC(l) ->
      exists t', t = TRef t'.

  Definition pair_types_are_preserved (S : HLPL_state) (Spl : PL_state) :=
    forall sp addr t,
      addr_spath_equiv S addr t sp ->
      get_node (S.[ sp ]) = HLPL_pairC ->
      exists t0 t1, t = TPair t0 t1.

  Lemma addr_spath_equiv_deterministic : forall S sp t addr1 addr2,
      Compatible S ->
      addr_spath_equiv S addr1 t sp -> addr_spath_equiv S addr2 t sp -> addr1 = addr2.
  Proof.
    intros S sp t addr1 addr2 [_ Hcorr_addr _] Hequiv1. generalize dependent addr2.
    induction Hequiv1 ; intros addr2 Hequiv2.
    - inversion Hequiv2 ; subst.
      * apply encode_inj in H0 ; congruence.
      * assert (Haddrof : addrof l = Some (bi, 0)) by
          (apply Hcorr_addr with (sp := (encode_var x, [])) (t := t);
           try constructor ; auto).
        rewrite Haddr in Haddrof. congruence.
      * apply f_equal with (f := length) in H4. rewrite List.length_app in H4.
        rewrite Nat.add_comm in H4. simpl in H4. discriminate.
      * apply f_equal with (f := length) in H4. rewrite List.length_app in H4.
        rewrite Nat.add_comm in H4. simpl in H4. discriminate.
      * apply f_equal with (f := length) in H4. rewrite List.length_app in H4.
        rewrite Nat.add_comm in H4. simpl in H4. discriminate.
    - inversion Hequiv2 ; subst.
      * subst. assert (Haddrof : addrof l = Some (bi0, 0)) by 
          (apply Hcorr_addr with (sp := (encode_var x, [])) (t := t) ; auto).
        congruence.
      * rewrite Hloc in Hloc0. injection Hloc0 ; intros ; subst l0 ; clear Hloc0.
        assert (Haddrof : addrof l = Some (bi, off)) by
          (eapply Hcorr_addr ; try (eapply Addr_spath_pointer); eauto).
        congruence.
  Admitted.

  (** Concretization of states/values implies correct types for values. *)
  Lemma val_concr_implies_correct_type_size :
    forall v t vl,
      concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v t vl Hconcr. induction Hconcr ; auto.
    - subst s. rewrite repeat_length. reflexivity.
    - rewrite List.length_app. simpl. rewrite IHHconcr1, IHHconcr2. reflexivity.
  Qed.

  Theorem list_back_ind : forall (A : Type) (P : list A -> Prop) (Hnil : P []) (Hrec : (forall (a : A) (l : list A), P l -> P (l ++ [a]))), forall (l : list A), P l.
  Proof.
    intros A P Hnil Hrec l. 
    remember (length l) as len. generalize dependent l.
    induction len ; intros l Heqlen.
    - symmetry in Heqlen. apply nil_length_inv in Heqlen. subst ; auto.
    - destruct l ; simpl in Heqlen.
      * discriminate.
      * injection Heqlen as Heqlen.
        remember (rev (a :: l)) as alrev.
        destruct alrev as [ | b l'].
      + apply f_equal with (f := length) in Heqalrev.
        simpl in Heqalrev. rewrite length_app, Nat.add_comm in Heqalrev.
        simpl in Heqalrev. congruence.
        + specialize (Hrec b (rev l')).
          assert (H : len = length (rev l')).
          {
            apply f_equal with (f := length) in Heqalrev.
            simpl in Heqalrev. rewrite length_app, Nat.add_comm in Heqalrev.
            simpl in Heqalrev. injection Heqalrev ; intros ; auto.
            rewrite length_rev. rewrite length_rev in H. congruence.
          }
          specialize (IHlen (rev l') H). specialize (Hrec IHlen).
          assert (H' : rev (b :: l') = rev (rev (a :: l))) by congruence.
          rewrite rev_involutive in H'. rewrite <- H'. simpl. auto.
  Qed.

  (* TODO: Clean this proof *)
  Lemma state_concr_implies_val_concr_aux: 
    forall S Spl x path v,
      concr_hlpl S Spl ->
      (S.[ (encode_var x, path) ]) = v ->
      v <> bot ->
      exists addr t vl,
        addr_spath_equiv S addr t (encode_var x, path) /\ concr_hlpl_val v t vl.
  Proof.
    induction path using list_back_ind ; intros v [Hconcr_heap Hconcr_env] HSx Hbot.
    - remember (blockof x).1 as bi. remember (blockof x).2 as t.
      assert (Heqbit : blockof x = (bi, t)) by (subst ; rewrite <- surjective_pairing ; auto).
      specialize (Hconcr_heap x bi t v HSx Hbot Heqbit).
      destruct Hconcr_heap as [vl [Hconcr_val Hheap] ].
      exists (bi, 0), t, vl. split.
      * constructor ; auto.
      * auto.
    - replace (S.[(encode_var x, path ++ [a])]) with
        ((S.[(encode_var x, path)]).[[ [a] ]] ) in HSx.
      destruct (S.[(encode_var x, path)]) eqn:E ;
        try (simpl in HSx ; rewrite nth_error_nil in HSx ; subst v ; contradiction).
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t (encode_var x, path) ∧
                     concr_hlpl_val (loc ((l), (y))) t vl).
        { apply IHpath ; try split ; auto. }
        destruct H as [addr [t [vl [ Hequiv Hconcr_val ] ] ] ].
        destruct a ; simpl in HSx.
        * exists (addr.1, addr.2), t, vl. split.
          ** apply Addr_spath_loc with (l := l).
             *** replace (S .[ (encode_var x, path)]) with (loc ((l), (y))) ; auto.
             *** rewrite <- surjective_pairing ; auto.
          ** inversion Hconcr_val ; subst ; auto.
        * rewrite nth_error_nil in HSx ; subst v ; contradiction.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t (encode_var x, path) ∧
                     concr_hlpl_val (HLPL_pair y1 y2) t vl).
        { apply IHpath ; try split ; auto. }
        destruct H as [addr [t [vl [Hequiv Hconcr_val ] ] ] ].
        inversion Hconcr_val ; subst v0 v1 t vl.
        destruct a as [ | [ | ] ].
        * exists (addr.1, addr.2), t0, vl0. split.
          ** eapply Addr_spath_pair_first. rewrite <- surjective_pairing. eassumption.
          ** simpl in HSx. congruence.
        * exists (addr.1, addr.2 + sizeof t0), t1, vl1. split.
          ** eapply Addr_spath_pair_second. rewrite <- surjective_pairing. eassumption.
          ** simpl in HSx. congruence.
        * simpl in HSx. rewrite nth_error_nil in HSx ; subst v ; contradiction.
      + remember (encode_var x, path) as p.
        rewrite surjective_pairing with (p := p) in Heqp; injection Heqp ; intros.
        rewrite <- H, <- H0 in *.
        rewrite <- sget_app. reflexivity.
  Qed.
                                                             
  Lemma state_concr_implies_val_concr :
    forall S Spl sp addr t v,
      concr_hlpl S Spl ->
      addr_spath_equiv S addr t sp ->
      S.[ sp ] = v ->
      v <> bot ->
      exists vl, lookup_heap_at_addr addr t Spl = vl /\ concr_hlpl_val v t vl.
  Proof.
    intros S Spl sp addr t v [Hconcr_heap _] Hequiv HSsp_v Hbot.
    generalize dependent v.
    induction Hequiv ; intros v HSsp_v Hbot ; simpl in *.
    - assert (Hconcr_ex_val: ∃ vl : pl_val, concr_hlpl_val v t vl ∧
                                   (heap Spl) !! bi = Some vl)
        by (eapply Hconcr_heap ; eauto).
      destruct Hconcr_ex_val as [vl' [Hval Hheap] ].
      exists vl'. split ; auto.
      simpl. replace (heap Spl !! bi) with (Some vl').
      erewrite skipn_0, val_concr_implies_correct_type_size ; eauto.
      apply firstn_all.
    - assert (HSy : S.[(y, vp')] = ptr(l)) by
        (destruct (S.[(y, vp')]) ; try discriminate ; injection Hptr ; auto).
      assert (Hneq : ptr (l) ≠ HLPL_bot) by auto.
      destruct (IHHequiv (ptr (l)) HSy Hneq) as [vl [Hheap Hconcr] ]; clear IHHequiv. 
      inversion Hconcr ; subst l0 t0 vl ; rewrite <- H1 in Hconcr ; clear H1.
      Admitted.
           

  Lemma state_concr_implies_val_concr:
    forall S Spl sp addr_t v vl,
      concr_hlpl S Spl ->
      addr_spath_equiv S addr_t sp ->
      S.[ sp ] = v ->
      v <> bot ->
      lookup_heap_at_addr addr_t.1 addr_t.2 Spl = vl ->
      concr_hlpl_val v addr_t.2 vl.
  Proof.
    intros S Spl sp addr v vl [Hconcr_heap _] Hequiv.
    generalize dependent vl. generalize dependent v.
    induction Hequiv ; intros v vl HS_sp Hbot HSpl_addr ; simpl in *.
    - assert (Hconcr_ex_val: ∃ vl : pl_val, concr_hlpl_val v t vl ∧
                                   (heap Spl) !! bi = Some vl)
        by (eapply Hconcr_heap ; eauto).
      destruct Hconcr_ex_val as [vl' [Hval Hheap] ].
      replace (heap Spl !! bi) with (Some vl') in HSpl_addr.
      assert (Hsize_length : sizeof t = length vl') by
        (apply val_concr_implies_correct_type_size with (v := v) ; auto).
      rewrite Hsize_length, skipn_0, firstn_all in HSpl_addr. congruence.
    - specialize (IHHequiv ptr (l) ([PL_address (bi, off)])).

        

  (** Concretization of states implies concretization of values *)
  Lemma state_concr_implies_val_concr :
    forall S Spl, Compatible S -> concr_hlpl S Spl -> 
             forall addr t sp v vl,
               addr_spath_equiv S (addr, t) sp ->
               S.[ sp ] = v ->
               v <> bot ->
               lookup_heap_at_addr addr t Spl = vl ->
               concr_hlpl_val v t vl.
  Proof.
    intros S Spl [Hbo _ _] [Hconcr_heap Hconcr_env]
      addr t sp v vl Hequiv HS_sp Hbot HSpl_addr.
    remember (addr, t) as addr_t.
    induction Hequiv.
    - injection Heqaddr_t ; intros ; clear Heqaddr_t ; subst t0 addr.
      assert (Hconcr_ex_val: ∃ vl : pl_val, concr_hlpl_val v t vl ∧
                                   (heap Spl) !! bi = Some vl)
        by (eapply Hconcr_heap ; eauto).
      destruct Hconcr_ex_val as [vl' [Hval Hheap] ].
      simpl in HSpl_addr. replace (heap Spl !! bi) with (Some vl') in HSpl_addr.
      admit. (* need info on size of types *)
    - injection Heqaddr_t ; intros ; clear Heqaddr_t ; subst t0 addr.
      apply IHHequiv.

    
  (** Spl <= S implies addresses are compatible *)
  Lemma le_implies_addresses_are_compatible :
  forall S Spl, Compatible S -> concr_hlpl S Spl -> addresses_are_compatible S Spl.
  Proof.
    intros S Spl
      [Hbo Hcorr_addr Hreach_loc] [Hconcr_heap Hconcr_env]
      bi off t sp l Hequiv Hnode.
    remember (bi, off, TRef t) as addr_t.
    inversion Hequiv ; subst.
    - injection H0 ; intros ; subst ;
      destruct (S.[ (encode_var x, [])]) eqn:E ; simpl in Hnode ; try discriminate ;
      injection Hnode ; intros ; subst ; clear Hnode H0.
      assert (Hconcr_ptr : ∃ vl : pl_val, concr_hlpl_val (ptr (l)) (TRef t) vl ∧
                                   (heap Spl) !! bi = Some vl) 
        by (eapply Hconcr_heap ; eauto).
      destruct Hconcr_ptr as [vl [Hconcr_ptr Haddrof] ].
      inversion Hconcr_ptr ; subst.
      exists addr.1, addr.2. split.
      * simpl. replace (heap Spl !! bi) with (Some [PL_address addr]).
        simpl. rewrite <- surjective_pairing ; auto.
      * rewrite <- surjective_pairing ; auto.
    - injection H ; intros ; subst ; clear H. congruence. 
    - injection H ; intros ; subst ; clear H.

  Lemma le_implies_addresses_are_compatible :
  forall S Spl, le_pl_hlpl Spl S -> addresses_are_compatible S Spl.
  Proof.
    intros S Spl Spl_le_S bi off t sp l Hequiv Hnode.
    destruct Spl_le_S as
      [Spl' [[Hbo Hcorr_addr Hreach_loc]
               [[Hconcr_heap Hconcr_env] Spl_le_Spl'] ] ].
    remember (bi, off, TRef t) as addr_t.
    induction Hequiv.
    injection Heqaddr_t ; intros ; subst ;
      destruct (S.[ (encode_var x, [])]) eqn:E ; simpl in Hnode ; try discriminate ;
      injection Hnode ; intros ; subst ; clear Hnode Heqaddr_t.
    - assert (Hconcr_ptr : ∃ vl : pl_val, concr_hlpl_val (ptr (l)) (TRef t) vl ∧
                                   (heap Spl') !! bi = Some vl)
        by (eapply Hconcr_heap ; eauto).
      destruct Hconcr_ptr as [vl [Hconcr_ptr Haddrof] ].
      inversion Hconcr_ptr ; subst.
      exists addr.1, addr.2. split.
      * simpl. admit.
      * rewrite <- surjective_pairing; auto.
  Admitted.

  (** Commutation Diagram to read in states *)
  Lemma addr_spath_pair_proj (S : HLPL_state) (Spl : PL_state) :
    forall f bi off x pi y pi' t0 t1 perm,
      addr_spath_equiv S ((bi, off), TPair t0 t1) (x, pi) ->
      eval_proj S perm (Field f) (x, pi) (y, pi') ->
      exists t bi' off',
        eval_proj_addr Spl (Field f) ((bi, off), TPair t0 t1) ((bi', off'), t) /\
      addr_spath_equiv S ((bi', off'), t) (y, pi').
  Proof.
    intros f bi off x pi y pi' t0 t1 perm Hequiv Hproj.
    inversion Hproj ; subst.
    * exists t0, bi, off. split.
      ** repeat constructor.
      ** eapply Addr_spath_pair_first. eassumption.
    * exists t1, bi, (off + sizeof t0). split.
      ** repeat constructor.
      ** eapply Addr_spath_pair_second. eassumption.
  Qed.

  Lemma addr_spath_deref_proj(S : HLPL_state) (Spl : PL_state) :
    forall bi off x y pi pi' t perm,
      addresses_are_compatible S Spl ->
      addr_spath_equiv S ((bi, off), TRef t) (x, pi) ->
      eval_proj S perm Deref (x, pi) (y, pi') ->
      exists bi' off',
      eval_proj_addr Spl Deref ((bi, off), TRef t) ((bi', off'), t) /\
      addr_spath_equiv S ((bi', off'), t) (y, pi').
  Proof.
    intros bi off x y pi pi' t perm Haddrcomp Hequiv Hproj.
    inversion Hproj ; subst.
    destruct (Haddrcomp _ _ _ _ _ Hequiv get_q) as [bi' [off' [Hlookup Haddr] ] ].
    exists bi', off'.
    split.
    - simpl in Hlookup. destruct (heap Spl !! bi) eqn:E.
      + apply Addr_deref with (pl := l0).
        * simpl in Hlookup. assumption.
        * rewrite <- hd_error_skipn. 
          destruct (drop off l0) eqn:E1.
          ** simpl in Hlookup. discriminate.
          ** simpl in Hlookup. rewrite take_0 in Hlookup.
             injection Hlookup ; intros ; subst ; reflexivity.
      + discriminate.
    - econstructor ; eassumption.
  Qed.

  (* The commuting diagram to relate addresses and spath *)
  Lemma addr_spath_proj (S : HLPL_state) (Spl : PL_state) :
    forall proj bi off x y pi pi' t perm,
      ref_types_are_preserved S Spl ->
      pair_types_are_preserved S Spl ->
      addresses_are_compatible S Spl ->
      addr_spath_equiv S ((bi, off), t) (x, pi) ->
      eval_proj S perm proj (x, pi) (y, pi') ->
      exists t' bi' off',
      eval_proj_addr Spl proj ((bi, off), t) ((bi', off'), t') /\
      addr_spath_equiv S ((bi', off'), t') (y, pi').
  Proof.
    intros [ | ]
      bi off x y pi pi' t perm Hrtypes Hptypes Haddrcomp Hequiv Hproj.
    * inversion Hproj ; subst. 
      assert (Ht : exists t'', t = TRef t'') by 
      (unfold ref_types_are_preserved in Hrtypes ; eapply Hrtypes ; eassumption).
      destruct Ht as [t'' Ht''] ; subst.
      exists t''. eapply addr_spath_deref_proj ; eassumption.
    * inversion Hproj ; subst ;
      assert (Ht : exists t0 t1, t = TPair t0 t1) by 
      (unfold pair_types_are_preserved in Hptypes ; eapply Hptypes ; eassumption) ;
      destruct Ht as [t0 [t1 Ht] ] ; subst.
      ** eapply addr_spath_pair_proj ; eassumption.
      ** eapply addr_spath_pair_proj ; eassumption.
  Qed.

Lemma concr_val_TInt_implies_PL_int :
    forall v vl, concr_hlpl_val v TInt vl -> (exists n, vl = [PL_int n]) \/ vl = [PL_poison].
  Proof.
    intros v vl Hconcr. remember TInt as t. induction Hconcr ; try discriminate.
    - left. exists n. reflexivity.
    - right. subst. reflexivity.
    - auto.
  Qed.

  Lemma concr_state_implies_concr_val :
    forall S Spl v vl bi off t x pi,
      vars S !! x = Some v ->
      concr_hlpl S Spl ->
      S.[(encode_var x, pi)] = v ->
      lookup_heap_at_addr (bi, off) t Spl = vl ->
      addr_spath_equiv S (bi, off, t) (x, pi) ->
      concr_hlpl_val v t vl.
  Proof.
    intros S Spl v vl bi off t x pi Hcheat [Hconcr_heap _] HS HSpl Hequiv.
    remember (bi, off, t) as t_addr. remember (x, pi) as p.
    induction Hequiv ; injection Heqt_addr ; injection Heqp ; intros ; subst.
    - unfold sget, encode_var. simpl. rewrite sum_maps_lookup_l.
      destruct (Hconcr_heap x (S .[ (encode_var x, [])]) bi t)
        as [vl [Hval Hheap] ]; auto.
      rewrite Hcheat. replace (heap Spl !! bi) with (Some vl). unfold drop.

      inversion Hval.
      + apply Concr_lit.

      induction t ; simpl.
      + destruct (concr_val_TInt_imlies_PL_int _ _ Hval) as [ [n Hint] | Hpois ].
        * rewrite Hint in *. apply Hval.
        * rewrite Hpois in *. apply Hval.
      + admit.
      + admit.
    - admit.
    - 
  Abort.
      
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

  Definition addrof := (fun l => if l =? l1 then Some (b1, 1) else None).

  Goal concr_hlpl_val addrof (HLPL_int 3) TInt [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof (loc (l1, (HLPL_int 3))) TInt [PL_int 3].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof HLPL_bot (TPair TInt TInt) [PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    HLPL_bot (TPair (TPair TInt TInt) TInt) [PL_poison ; PL_poison ; PL_poison].
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair (HLPL_int 3) (HLPL_int 4)) (TPair TInt TInt)
    ([PL_int 3] ++ [PL_int 4]).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair (HLPL_int 3) (HLPL_pair (HLPL_int 7) (HLPL_int 11))) (TPair TInt (TPair TInt TInt))
    ([PL_int 3] ++ ([PL_int 7] ++ [PL_int 11])).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (ptr (l1)) (TRef TInt) [PL_address (b1, 1)].
  Proof. repeat econstructor. Qed.
End Tests.
