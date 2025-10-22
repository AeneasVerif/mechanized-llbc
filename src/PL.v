Require Import lang.
Require Import base.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.
Require ListBackInd.
Require Setoid.

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
| PL_address : address -> type -> PL_val
.

Definition pl_val := list PL_val.

Record PL_state := {
  env : Pmap (block_id * type);
  heap : Pmap pl_val
}.

Fixpoint sizeof (tau : type) : nat :=
  match tau with
  | TInt | TRef => 1
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

(* Notations and definition for the PL language *)
Definition add_offset (addr : address) (off : nat) : address :=
  (addr.1, addr.2 + off).

Infix "+o" := add_offset (at level 60).

Lemma addr_add_offset_fst : forall (addr : address) (off : nat),
    (addr +o off).1 = addr.1.
Proof.
  intros addr off. rewrite surjective_pairing with (p := addr). auto.
Qed.

Lemma addr_add_offset_snd : forall (addr : address) (off : nat),
    (addr +o off).2 = addr.2 + off.
Proof.
  intros addr off. rewrite surjective_pairing with (p := addr). auto.
Qed.

Lemma bi_add_offset : forall (bi : block_id) (off1 off2 : nat),
    (bi, off1 + off2) = (bi, off1) +o off2.
Proof. reflexivity. Qed.

Inductive copy_val : PL_val -> PL_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (PL_int n) (PL_int n).

(* Functions to lookup and update PL states *)
Definition update_env (S : PL_state) (e : Pmap (block_id * type)) :=
  {|env := e ; heap := heap S |}.

Definition update_heap (S : PL_state) (h : Pmap pl_val) :=
  {|env := env S ; heap := h |}.

Definition lookup_block_and_type_env (enc_x : positive) (S : PL_state)
  : option (block_id * type) :=
  lookup enc_x (env S).

Definition lookup_env (enc_x : positive) (S : PL_state) : option block_id :=
  match lookup enc_x (env S) with
  | None => None
  | Some (bi, _) => Some bi
  end.

Definition lookup_type_env (enc_x : positive) (S : PL_state) : option type :=
  match lookup x (env S) with
  | None => None
  | Some (_, T) => Some T
  end.
  
Definition lookup_heap (bi : block_id) (S : PL_state) : option (list PL_val) :=
  lookup bi (heap S).

Definition lookup_heap_at_addr (addr : address) (t : type) (S : PL_state) : pl_val :=
  let size := sizeof t in
  match lookup addr.1 (heap S) with
  | None => []
  | Some vl =>
      firstn size (skipn addr.2 vl)
  end.

Definition write_heap_at_addr (addr : address) (vl : pl_val) (S : PL_state) :=
  let (bi, off) := addr in
  let block := lookup_heap bi S in
  match block with
  | None => S
  | Some vl' =>
      let new_block := firstn off vl' ++ vl ++ skipn (off + length vl) vl' in
      update_heap S (alter (fun _ => new_block) bi (heap S))
  end. 

Lemma env_stable_by_write_at_addr :
  forall S addr vl, env (write_heap_at_addr addr vl S) = env S.
Proof.
  intros [env_S heap_S] [bi off] vl. simpl.
  destruct (lookup_heap bi {| env := env_S; heap := heap_S |}) ; reflexivity.
Qed.

Notation "S .h.[ addr : t ]" := (lookup_heap_at_addr addr t S) (left associativity, at level 50).

Notation "S .h.[ addr <- vl ]" := (write_heap_at_addr addr vl S) (left associativity, at level 50).

Inductive eval_proj_pl (Spl : PL_state) :
  proj -> (address * type) -> (address * type) -> Prop :=
| Eval_Deref_Ptr_Locs_pl :
  forall (addr addr' : address) (t: type),
    lookup_heap_at_addr addr TRef Spl = [PL_address addr' t] ->
    eval_proj_pl Spl Deref (addr, TRef) (addr', t)
| Eval_Field_First_l_pl :
  forall (addr : address) (t0 t1 : type),
    eval_proj_pl Spl (Field First) (addr, TPair t0 t1) (addr, t0)
| Eval_Field_Second_l_pl :
  forall (addr : address) (t0 t1 : type),
    eval_proj_pl Spl (Field Second) (addr, TPair t0 t1) (addr +o sizeof t0, t1).

Inductive eval_path_pl (Spl : PL_state) : path -> address * type -> address * type -> Prop :=
| Eval_nil_addr : forall addr, eval_path_pl Spl [] addr addr
| Eval_cons : forall proj P addr_t addr_t' addr_t'',
    eval_proj_pl Spl proj addr_t addr_t' ->
    eval_path_pl Spl P addr_t' addr_t'' ->
    eval_path_pl Spl (proj :: P) addr_t addr_t''.

Definition eval_place_pl (Spl : PL_state) (p : place) (addr_t : address * type) : Prop :=
  exists bi t,
    lookup_block_and_type_env (encode_var p.1) Spl = Some (bi, t) /\
      eval_path_pl Spl p.2 ((bi, 0), t) addr_t.

Lemma eval_proj_pl_deterministic :
  forall Spl proj addr_t0 addr_t1 addr_t2,
    eval_proj_pl Spl proj addr_t0 addr_t1 ->
    eval_proj_pl Spl proj addr_t0 addr_t2 ->
    addr_t1 = addr_t2.
Proof.
  intros Spl proj ? ? ? Heval_proj1 Heval_proj2.
  destruct proj ; inversion Heval_proj1 ; subst ; inversion Heval_proj2; subst ; auto.
  rewrite H in H1. injection H1 ; intros ; subst ; auto.
Qed.

Lemma eval_path_pl_deterministic :
  forall Spl P addr_t0 addr_t1 addr_t2,
    eval_path_pl Spl P addr_t0 addr_t1 ->
    eval_path_pl Spl P addr_t0 addr_t2 ->
    addr_t1 = addr_t2.
Proof.
  intros Spl P ? ? ? Heval_path01 Heval_path12.
  induction Heval_path01 ; inversion Heval_path12 ; subst ; auto.
  pose proof (eval_proj_pl_deterministic _ _ _ _ _ H H2) ; subst.
  apply IHHeval_path01 ; auto.
Qed.

Lemma eval_place_pl_deterministic :
  forall Spl p addr_t addr_t',
    eval_place_pl Spl p addr_t ->
    eval_place_pl Spl p addr_t' ->
    addr_t = addr_t'.
Proof.
  intros Spl p addr_t addr_t'
    (bi & t & Hlu & Heval_path) (bi' & t' & Hlu' & Heval_path').
  rewrite Hlu in Hlu'. injection Hlu' ; intros ; subst.
  eapply eval_path_pl_deterministic ; eauto.
Qed.

(** Read in PL state *)
Definition read_address (Spl : PL_state) (p : place) (t : type) (addr : address): Prop :=
  eval_place_pl Spl p (addr, t).

Variant read (S : PL_state) (p : place) (t : type) (vl : pl_val) : Prop :=
  | Read addr 
      (Haddr : read_address S p t addr)
      (Hlu : lookup_heap_at_addr addr t S = vl) :
    read S p t vl.

Variant write (S : PL_state) (p : place) (t : type) (vl : pl_val)
  : PL_state -> Prop :=
  | Write addr vl' vl'' h
      (Haddr : read_address S p t addr)
      (Hlu : Some vl' = lookup_heap addr.1 S)
      (Hcut : vl'' = (firstn addr.2 vl') ++ vl ++ (skipn (addr.2 + sizeof t) vl'))
      (Hheap : h = alter (fun _ => vl'') addr.1 (heap S)) :
      write S p t vl (update_heap S h).


(* Evaluation of Expressions in PL *)
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

Reserved Notation "S  |-{rv-pl}  rv =>  r" (at level 60).
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
  S |-{rv-pl} &mut p : TRef => [PL_address addr t]
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


Lemma list_app_elem_not_nil {A : Type} :
  forall (l : list A) (a : A), l ++ [ a ] <> [].
Proof. intros l a Hcontr. apply app_nil, proj2 in Hcontr. discriminate. Qed.

Lemma spath_app_elem_not_nil :
  forall (sp : spath) (n : nat) enc_x, sp +++ [ n ] <> (enc_x, []).
Proof.
  intros. unfold app_spath_vpath. intros contra.
  injection contra as _ H. destruct (list_app_elem_not_nil sp.2 n H).
Qed.
    
Ltac sp_discriminate_or_find_equalities :=
  match goal with
  | H1: ?E = HLPL_pairC, H2: ?E = locC (_) |- _ => rewrite H2 in H1 ; discriminate
  | H: [?a] = [?b] |- _ => injection H ; intros ; clear H ; try discriminate
  | H: ?l ++ [?a] = [ ] |- _ =>
      destruct (list_app_elem_not_nil l a H)
  | H: [ ] = ?l ++ [?a] |- _ =>
      symmetry in H ;
      destruct (list_app_elem_not_nil l a H)
  | H: ?l1 ++ [?a1] = ?l2 ++ [?a2] |- _ =>
      assert (Hlen_one : length [ a1 ] = length [ a2 ]) by reflexivity ;
      destruct (app_inj_2 _ _ _ _ Hlen_one H) ;
      clear H Hlen_one ; subst
  | H: ?sp +++ [?n] = (?enc_x, []) |- _ =>
      destruct (spath_app_elem_not_nil sp n enc_x H)
  end.

Ltac rewrite_pairs :=
  match goal with
  | H1 : ?sp1.1 = ?sp2.1, H2 : ?sp1.2 = ?sp2.2 |- _ =>
      assert (Htemp : sp1 = sp2) by
      (rewrite surjective_pairing with (p := sp1),
          surjective_pairing with (p := sp2) ; congruence) ;
      subst sp1 ; clear H1 H2
  end.


(* Concretization of HLPL values to PL values *)

Section Concretization.
  Variable blockof : positive -> block_id * type.
  Variable addrof : loan_id -> option (address * type).

  Local Open Scope stdpp_scope.


  (** Assigning types to spath *)
  Inductive eval_type (S : HLPL_state) : spath -> type -> Prop :=
  | Eval_base_type enc_x bi t
      (Hvp : valid_spath S (enc_x, []))
      (Hbo : blockof enc_x = (bi, t)) :
      eval_type S (enc_x, []) t
  | Eval_loc_type sp t l
    (Hnode : get_node ( S.[ sp ] ) = HLPL_locC l)
    (Hrec : eval_type S sp t) :
    eval_type S (sp +++ [0]) t
  | Eval_pair_first_type sp t0 t1
    (Hnode : get_node ( S.[ sp ] ) = HLPL_pairC)
    (Hrec : eval_type S sp (TPair t0 t1)) :
    eval_type S (sp +++ [0]) t0
  | Eval_pair_second_type sp t0 t1
    (Hnode : get_node ( S.[ sp ] ) = HLPL_pairC)
    (Hrec : eval_type S sp (TPair t0 t1)) :
    eval_type S (sp +++ [1]) t1
  .

  Lemma eval_type_deterministic :
    forall S sp t0 t1,
      eval_type S sp t0 ->
      eval_type S sp t1 ->
      t1 = t0.
  Proof.
    intros S sp t0 t1 Heval_type0. generalize dependent t1.
    induction Heval_type0 ; intros ? Heval_type1 ; inversion Heval_type1 ; subst ;
      repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs) ; auto.
    - congruence. 
    - specialize (IHHeval_type0 (TPair t2 t4) Hrec). congruence. 
    - specialize (IHHeval_type0 (TPair t3 t2) Hrec). congruence. 
  Qed.

  Fixpoint typeof (v : HLPL_val) : type :=
    match v with
    | HLPL_int _ => TInt
    | HLPL_loc _ v => typeof v
    | HLPL_pair v0 v1 => TPair (typeof v0) (typeof v1)
    | HLPL_ptr _ => TRef
    | _ => TInt
    end.

  Fixpoint offsetof (v : HLPL_val) (bi : block_id) (rvp: list nat) : nat :=
    match rvp with
    | 0 :: rvp' =>
        offsetof v bi rvp'
    | 1 :: rvp' =>
        (offsetof v bi rvp') + sizeof (typeof (v.[[rev rvp' ++ [0] ]]))
    | [] | _ :: _ => 0
    end.

  Definition addressof (S : HLPL_state) (sp : spath) : address :=
    ((blockof sp.1).1, offsetof (S.[(sp.1, [])]) (blockof sp.1).1 (rev sp.2)).

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
      (Haddr : addrof l = Some (addr, t)) :
    concr_hlpl_val (HLPL_ptr l) TRef [PL_address addr t]
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
    | HLPL_ptr l, TRef =>
        match addrof l with
        | Some (addr, t) => Some [PL_address addr t]
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
      * destruct p ; injection H as H ; subst ; constructor. assumption.
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
    forall enc_x bi t v,
      valid_spath S (enc_x, []) ->
      S.[ (enc_x, []) ] = v ->
      blockof enc_x = (bi, t) ->
      exists vl, concr_hlpl_val v t vl /\ h !! bi = Some vl .

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall x bi t,
    get_at_accessor S (encode_var x) <> None ->
      blockof (encode_var x) = (bi, t) ->
      env !! (encode_var x) = Some (bi, t).

  Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
    concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.heap(addr) *)

  Inductive addr_spath_equiv (S : HLPL_state) :
    address -> type -> spath -> Prop :=
  | Addr_spath_base sp addr bi t enc_x
      (H : blockof enc_x = (bi, t))
      (Hsp : sp = (enc_x, []))
      (Hvp : valid_spath S sp)
      (Haddr : addr = (bi, 0)) :
    addr_spath_equiv S addr t sp
  | Addr_spath_pair_first addr sp t0 t1
      (Hpair : get_node (S.[sp]) = HLPL_pairC)
      (Hrec : addr_spath_equiv S addr (TPair t0 t1) sp) :
    addr_spath_equiv S addr t0 (sp +++ [0])
  | Addr_spath_pair_second addr sp t0 t1
      (Hpair : get_node (S.[sp]) = HLPL_pairC)
      (Hrec : addr_spath_equiv S addr (TPair t0 t1) sp) :
    addr_spath_equiv S (addr +o sizeof t0) t1 (sp +++ [1])
  | Addr_spath_loc addr sp t l
      (Hloc : get_node (S.[sp]) = HLPL_locC l)
      (Hrec : addr_spath_equiv S addr t sp) :
    addr_spath_equiv S addr t (sp +++ [0]).

  Definition addr_spath_equiv_fin S addr sp :=
    exists t, addr_spath_equiv S addr t sp.

  Lemma addr_spath_equiv_eval_type :
    forall S sp t, (exists addr, addr_spath_equiv S addr t sp) <-> eval_type S sp t.
    intros S sp t ; split ; [intros (addr & Hequiv) | intros Heval_type].
    { induction Hequiv ; subst ; try (econstructor ; eassumption). }
    {
      induction Heval_type.
      - exists (bi, 0). econstructor ; eauto.
      - destruct IHHeval_type as (addr & Hequiv).
        exists addr. eapply Addr_spath_loc ; eassumption.
      - destruct IHHeval_type as (addr & Hequiv).
        exists addr. eapply Addr_spath_pair_first ; eassumption.
      - destruct IHHeval_type as (addr & Hequiv).
        exists (addr +o sizeof t0). eapply Addr_spath_pair_second ; eassumption.
    }
  Qed.

  Lemma addr_spath_equiv_sset : 
    forall S addr t sp0 sp1 v,
      ~ prefix sp1 sp0 ->
      addr_spath_equiv S addr t sp0 <->
      addr_spath_equiv (S .[ sp1 <- v]) addr t sp0.
  Proof.
    intros S addr t sp0 sp1 v Hpref. split ; intros Hequiv.
    {
      induction Hequiv ; subst.
      - eapply Addr_spath_base ; eauto.
        apply sset_not_prefix_valid ; auto. apply not_strict_prefix_nil.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_pair_first ; eauto.
        rewrite get_node_sset_sget_not_prefix ; auto.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_pair_second ; eauto.
        rewrite get_node_sset_sget_not_prefix ; auto.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_loc ; eauto.
        rewrite get_node_sset_sget_not_prefix ; eauto.
    }
    {
      induction Hequiv ; subst.
      - eapply Addr_spath_base ; eauto.
        apply sset_not_prefix_valid in Hvp; auto. apply not_strict_prefix_nil.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_pair_first ; eauto.
        erewrite <- get_node_sset_sget_not_prefix ; eauto.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_pair_second ; eauto.
        erewrite <- get_node_sset_sget_not_prefix ; eauto.
      - apply not_prefix_app in Hpref. apply IHHequiv in Hpref as Hequiv'.
        eapply Addr_spath_loc ; eauto.
        erewrite <- get_node_sset_sget_not_prefix ; eauto.
    }
  Qed.

  Lemma concr_val_size : forall v vl t, concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v vl t Hconcr. induction Hconcr ; auto ; try reflexivity.
    - rewrite Hs, repeat_length. reflexivity.
    - rewrite List.length_app. simpl. lia.
  Qed.

  Record Compatible (S : HLPL_state) : Prop :=
    mkCompatible
      {
        block_dom :
        forall (enc_x : positive), 
          valid_spath S (enc_x, []) ->
          exists bi t, blockof enc_x = (bi, t) 
      ; correct_addrof :
        forall (sp : spath) (addr : address) t l,
          addr_spath_equiv S addr t sp ->
          get_node (S.[sp]) = HLPL_locC l ->
          addrof l = Some (addr, t)
      ; reachable_loc :
        forall l sp,
          get_node (S.[sp]) = HLPL_locC l ->
          exists addr t, addr_spath_equiv S addr t sp
      }.

  Inductive le_val : relation PL_val :=
  | lev_refl v : le_val v v
  | lev_poison v : le_val v PL_poison.

  Program Instance IsPreoderVal: PreOrder le_val.
  Next Obligation.
    constructor. Qed.
  Next Obligation.
  intros x y z Hxy Hyz ; inversion Hxy ; inversion Hyz ; subst ; try constructor. Qed.
  
  Definition le_block : relation pl_val := Forall2 le_val.
  Instance IsPreoderBlock: PreOrder le_block.
  apply PreOrder_instance_1, IsPreoderVal. Qed.

  Definition le_heap : relation (Pmap pl_val) :=
    fun h1 h2 =>
      dom h1 = dom h2 /\
      forall bi b1,
        h1 !! bi = Some b1 ->
        exists b2, h2 !! bi = Some b2 /\ le_block b1 b2.
  Program Instance IsPreoderHeap: PreOrder le_heap.
  Next Obligation.
    split ; auto.
    intros bi b1 Hbi ; exists b1 ; repeat split ; auto. apply IsPreoderBlock. Qed.
  Next Obligation.
    intros h1 h2 h3 [Hdom12 H12] [Hdom23 H23].
    split. 
    - etransitivity ; eauto.
    - intros bi b1 Hh1.
      destruct (H12 bi b1 Hh1) as (b2 & Hh2 & Hle12).
      destruct (H23 bi b2 Hh2) as (b3 & Hh3 & Hle23).
      exists b3 ; split ; auto. etransitivity ; eauto. Qed.
  
  Definition le_pl_state : relation PL_state :=
    fun Spl1 Spl2 => env Spl1 = env Spl2 /\ le_heap (heap Spl1) (heap Spl2).
  Program Instance IsPreoderState : PreOrder le_pl_state.
  Next Obligation.
    intros Spl. split ; reflexivity. Qed.
  Next Obligation.
    intros Spl1 Spl2 Spl3 [env12 heap12] [env23 heap23]. split ; try congruence.
    etransitivity ; eauto.
  Qed.

  Infix "<={pl}" := le_pl_state (at level 70).

  Definition le_pl_hlpl (Spl : PL_state) (S : HLPL_state) : Prop :=
    exists Spl', Compatible S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.

  (* Addr_spath_equiv is a function: given state S and spath sp, addr and t are unique *)
  Ltac injection_list_app :=
    match goal with
    | H: ?x = ?x |- _ => clear H 
    | H: [?a] :: _ = [?b] :: _ |- _ => injection H ; intros [=]; try discriminate
    | H: ?l1 ++ [?a1] = ?l2 ++ [?a2] |- _ =>
        assert (Hlen_one : length [ a1 ] = length [ a2 ]) by reflexivity ;
        destruct (app_inj_2 _ _ _ _ Hlen_one H) ;
        clear H Hlen_one ; subst
    | H: [ ] = ?l ++ [?a] |- _ =>
        symmetry in H ;
        destruct (list_app_elem_not_nil l a H)
    | H: ?l ++ [?a] = [] |- _ =>
        destruct (list_app_elem_not_nil l a H)
    end.

  Ltac congruence' :=
    match goal with
    | H : sget ?S ?p = _ |- get_node (sget ?S ?p) = _ => rewrite H ; simpl ; reflexivity 
    | _ => congruence
    end.

  Ltac discriminate_val_from_valid_spath S sp :=
    match goal with
    | Hvp : valid_spath S (sp +++ [?n]), Heq : (S.[sp]) = _ |- _ =>
        try (
            assert (Htemp: arity (get_node (S.[sp])) <= n)
            by (rewrite Heq ; simpl;  lia) ; 
            apply not_valid_spath_app_last_get_node_arity in Htemp ;
            destruct (Htemp Hvp)) end.
  
  Ltac nodes_to_val :=
    match goal with
    | H : get_node ?v = ?r |- _ =>
        destruct v eqn:? ; simpl in H ; try congruence ;
        try (injection H ; intros ; subst) ; clear H ;
        nodes_to_val ;
        assert (get_node v = r) by (
            match goal with
            | H0 : v = _ |- _ =>
            rewrite H0 ; reflexivity end)
    | _ => idtac
    end.

  Lemma addr_spath_equiv_deterministic_type :
    forall S sp addr1 addr2 t1 t2,
      addr_spath_equiv S addr1 t1 sp ->
      addr_spath_equiv S addr2 t2 sp ->
      t1 = t2.
  Proof.
    intros S sp. induction sp using ListBackInd.state_path_back_ind ;
      intros addr1 addr2 t1 t2 Hequiv1 Hequiv2.
    - inversion Hequiv1 ; inversion Hequiv2 ; subst ;
        try sp_discriminate_or_find_equalities.
      congruence.
    - inversion Hequiv1 ; inversion Hequiv2 ; subst ;
        repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs).
      * assert (Hpt : TPair t1 t3 = TPair t2 t5) by (eapply IHsp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * assert (Hpt : TPair t0 t1 = TPair t4 t2) by (eapply IHsp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * eapply IHsp ; eauto.
  Qed.
 
  Lemma addr_spath_equiv_deterministic_addr :
    forall S sp addr1 addr2 t1 t2,
      addr_spath_equiv S addr1 t1 sp ->
      addr_spath_equiv S addr2 t2 sp ->
      addr1 = addr2.
  Proof.
    intros S sp. induction sp using ListBackInd.state_path_back_ind ;
      intros addr1 addr2 t1 t2 Hequiv1 Hequiv2.
    - inversion Hequiv1 ; inversion Hequiv2 ; subst ;
        repeat sp_discriminate_or_find_equalities. congruence.
    - inversion Hequiv1 ; inversion Hequiv2 ; subst ;
        repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs).
      * eapply IHsp ; eauto.
      * assert (addr = addr0) by (eapply IHsp ; eauto). subst.
        assert (TPair t0 t1 = TPair t4 t2)
          by (eapply addr_spath_equiv_deterministic_type ; eauto).
        congruence.
      * eapply IHsp ; eauto.
  Qed.

  Lemma addr_spath_equiv_deterministic:
    forall S sp addr1 addr2 t1 t2,
      addr_spath_equiv S addr1 t1 sp ->
      addr_spath_equiv S addr2 t2 sp ->
      addr1 = addr2 /\ t1 = t2.
  Proof.
    intros ; split ;
      [ eapply addr_spath_equiv_deterministic_addr ; eauto |
        eapply addr_spath_equiv_deterministic_type ; eauto ]. Qed.

  Lemma addr_spath_equiv_implies_valid_spath :
    forall S sp addr t, 
      addr_spath_equiv S addr t sp ->
      valid_spath S sp.
  Proof.
    intros S sp addr t Hequiv. induction Hequiv ; subst ; auto ;
      try (apply valid_spath_app ; split ; auto ; nodes_to_val ; repeat econstructor).
  Qed.

  (** Concretization of states/values implies correct types for values. *)
  Lemma val_concr_implies_correct_type_size :
    forall v t vl,
      concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v t vl Hconcr. induction Hconcr ; auto.
    - subst s. rewrite repeat_length. reflexivity.
    - rewrite List.length_app. simpl. rewrite IHHconcr1, IHHconcr2. reflexivity.
  Qed.

  (* Concretization of states implies concretization of values *)
  Lemma lookup_heap_pair_app :
    forall Spl addr t0 t1,
      lookup_heap_at_addr addr (TPair t0 t1) Spl =
        lookup_heap_at_addr addr t0 Spl ++
          lookup_heap_at_addr (addr +o sizeof t0) t1 Spl.
  Proof.
    intros Spl addr t0 t1.
    unfold lookup_heap_at_addr. rewrite addr_add_offset_fst.
    destruct (heap Spl !! addr.1) eqn:E ; auto.
    simpl. rewrite <- take_take_drop, drop_drop. reflexivity.
  Qed.

  Lemma lookup_heap_length_le_size :
    forall Spl addr t,
      length (lookup_heap_at_addr addr t Spl) <= sizeof t.
  Proof.
    intros Spl addr t. 
    unfold lookup_heap_at_addr. destruct (heap Spl !! addr.1).
    - simpl. apply firstn_le_length.
    - simpl ; lia.
  Qed.

  Lemma state_concr_implies_val_concr : 
    forall S Spl sp v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      exists addr t vl,
        addr_spath_equiv S addr t sp /\ concr_hlpl_val v t vl /\ lookup_heap_at_addr addr t Spl = vl.
  Proof.
    induction sp using ListBackInd.state_path_back_ind ;
      intros v [Hconcr_heap Hconcr_env] Hvspn HSx.
    remember (blockof enc_x).1 as bi. remember (blockof enc_x).2 as t.
    assert (Heqbit : blockof enc_x = (bi, t))
      by (subst ; rewrite <- surjective_pairing ; reflexivity).
    - specialize (Hconcr_heap enc_x bi t v Hvspn HSx Heqbit).
      destruct Hconcr_heap as [vl [Hconcr_val Hheap] ].
      exists (bi, 0), t, vl. repeat split ; auto.
      * eapply Addr_spath_base ; eauto.
      * unfold lookup_heap_at_addr ; simpl.
        replace (heap Spl !! bi) with (Some vl) by auto.
        rewrite drop_0, (val_concr_implies_correct_type_size v t vl), firstn_all ;
          auto.
    - rewrite sget_app in HSx. 
      apply valid_spath_app in Hvspn as Htemp ; destruct Htemp as (Hvsp & Hvvp).
      destruct (S.[sp]) eqn:E ; discriminate_val_from_valid_spath S sp.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t sp ∧
                     concr_hlpl_val (loc ((l), (y))) t vl /\
                     lookup_heap_at_addr addr t Spl = vl) by
        (apply IHsp ; try split ; auto).
        destruct H as [addr [t [vl [ Hequiv [Hconcr_val Hval_heap] ] ] ] ].
        destruct n ; simpl in HSx.
        * exists addr, t, vl. repeat split ; auto.
          ** apply Addr_spath_loc with (l := l) ; try rewrite E ; auto.
          ** inversion Hconcr_val ; subst ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2. congruence.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t sp ∧
                     concr_hlpl_val (HLPL_pair y1 y2) t vl /\
                     lookup_heap_at_addr addr t Spl = vl) by
        (apply IHsp ; try split ; auto).
        destruct H as [addr [t [vl [Hequiv [Hconcr_val Hval_heap] ] ] ] ].
        inversion Hconcr_val ; subst v0 v1 t vl.
        rewrite lookup_heap_pair_app in H3.
        apply concr_val_size in H4 as Hsize_t0, H5 as Hsize_t1.
        assert (Hlen_fst : length (lookup_heap_at_addr addr t0 Spl) <= sizeof t0) by (apply lookup_heap_length_le_size).
        assert (Hlen_snd : length (lookup_heap_at_addr (addr +o sizeof t0) t1 Spl) <= sizeof t1)
          by (apply lookup_heap_length_le_size).
        assert (Hlen_pair : length (lookup_heap_at_addr addr t0 Spl ++ lookup_heap_at_addr (addr +o sizeof t0) t1 Spl) = sizeof t0 + sizeof t1)
          by (rewrite <- H3, length_app; lia).
        rewrite length_app in Hlen_pair.
        apply app_inj_1 in H3 ; try lia. destruct H3 as [Hvl0 Hvl1].
        destruct n as [ | [ | ] ] ; simpl in *.
        * exists addr, t0, vl0. repeat split ; try congruence.
          eapply Addr_spath_pair_first ; eauto. rewrite E ; auto.
        * exists (addr +o sizeof t0), t1, vl1 ; repeat split ; try congruence.
          eapply Addr_spath_pair_second ; eauto. rewrite E ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2. congruence.
  Qed.

  Lemma state_concr_implies_val_concr_at_addr : 
    forall S Spl sp addr t v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      addr_spath_equiv S addr t sp ->
      exists vl,
         concr_hlpl_val v t vl /\ lookup_heap_at_addr addr t Spl = vl.
  Proof.
    intros S Spl sp addr t v Hconcr Hvsp HS_sp Hequiv.
    destruct (state_concr_implies_val_concr _ _ _ _ Hconcr Hvsp HS_sp)
      as [addr' [t' [vl [Hequiv' [Hconcr_val Hlu ] ] ] ] ].
    pose proof (addr_spath_equiv_deterministic_addr _ _ _ _ _ _ Hequiv' Hequiv) as Heq.
    pose proof (addr_spath_equiv_deterministic_type _ _ _ _ _ _ Hequiv' Hequiv) as Heqt.
    subst addr' t'; clear Hequiv'.
    exists vl ; split ; auto.
  Qed.
  
Lemma concr_val_TInt_implies_PL_int :
    forall v vl, concr_hlpl_val v TInt vl -> (exists n, vl = [PL_int n]) \/ vl = [PL_poison].
  Proof.
    intros v vl Hconcr. remember TInt as t. induction Hconcr ; try discriminate.
    - left. exists n. reflexivity.
    - right. subst. reflexivity.
    - auto.
  Qed.

  Lemma le_heap_implies_le_block :
    forall S1 S2 addr t,
      le_heap (heap S1) (heap S2) ->
      le_block (lookup_heap_at_addr addr t S1) (lookup_heap_at_addr addr t S2).
  Proof.
    intros S1 S2 addr t [Hdom Hle_heap].
    unfold lookup_heap_at_addr. 
    destruct (heap S1 !! addr.1) eqn:E1.
    - destruct (Hle_heap addr.1 l E1) as (l' & E2 & Hle_block).
      replace (heap S2 !! addr.1) with (Some l') by auto.
      apply Forall2_take, Forall2_drop ; auto.
    - apply not_elem_of_dom in E1.
      replace (dom (heap S1)) with (dom (heap S2)) in E1.
      apply not_elem_of_dom in E1. 
      replace (heap S2 !! addr.1) with (None : option pl_val) by auto.
      constructor.
  Qed.

  (** Simulation proof between spath and address *)
  Lemma spath_address_proj_simul :
    forall S Spl sp sp' addr t perm proj,
      le_pl_hlpl Spl S ->
      addr_spath_equiv S addr t sp ->
      eval_proj S perm proj sp sp' ->
      exists addr' t',
        eval_proj_pl Spl proj (addr, t) (addr', t') /\
          addr_spath_equiv S addr' t' sp'.
  Proof.
    intros S Spl sp sp' addr t perm proj
      (Spl' & HComp & Hconcr & _ & Hheap) Hequiv Hproj.
    pose proof HComp as Hcomp.
    destruct HComp as [_ Hcorr_addrof Hloc].
    inversion Hproj ; subst.
    - nodes_to_val.
      assert (Hvsp : valid_spath S sp) by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_ptr l) t vl ∧
                      lookup_heap_at_addr addr t Spl' = vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & Hlu_addr). inversion Hconcr_val ; subst.
      assert (Hvsp' : valid_spath S sp') by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp : ∃ (addr : address) (t : type) (vl : pl_val),
                 addr_spath_equiv S addr t sp' ∧
                   concr_hlpl_val (HLPL_loc l h) t vl ∧
                   lookup_heap_at_addr addr t Spl' = vl).
      { apply state_concr_implies_val_concr ; auto. }.
      destruct Htemp as (addr' & t' & vl & Hequiv' & Hconcr_val' & Hlu_addr').
      exists addr', t' ; split ; auto.
      constructor.
      pose proof (Hcorr_addrof _ _ _ _ Hequiv' H0).
      rewrite Haddr in H1 ; injection H1 ; intros ; subst ; clear H1.
      assert (Hle_block : le_block (lookup_heap_at_addr addr TRef Spl)
                            (lookup_heap_at_addr addr TRef Spl'))
        by (apply le_heap_implies_le_block ; auto).
      rewrite <- H3 in Hle_block.
      inversion Hle_block ; inversion H5 ;  inversion H6 ; subst. reflexivity.
    - nodes_to_val.
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_pair h1 h2) t vl ∧
                      lookup_heap_at_addr addr t Spl' = vl).
      assert (Hvsp : valid_spath S sp) by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & _). inversion Hconcr_val ; subst.
      exists addr, t0 ; split ; try constructor.
      eapply Addr_spath_pair_first ; eauto.
    - nodes_to_val.
      assert (Hvsp : valid_spath S sp) by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_pair h1 h2) t vl ∧
                      lookup_heap_at_addr addr t Spl' = vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & _). inversion Hconcr_val ; subst.
      exists (addr +o sizeof t0), t1 ; split.
      * constructor.
      * eapply Addr_spath_pair_second ; eauto. 
  Qed.

  Lemma spath_address_loc_simul :
    forall S Spl sp sp' addr t perm,
      le_pl_hlpl Spl S ->
      addr_spath_equiv S addr t sp ->
      eval_loc S perm sp sp' ->
      addr_spath_equiv S addr t sp'.
  Proof.
    intros S Spl sp sp' addr t perm Hle Hequiv Heval_loc.
    inversion Heval_loc ; subst.
    eapply Addr_spath_loc ; auto. rewrite get_q. reflexivity.
  Qed.
    

  Lemma spath_address_path_simul :
    forall S Spl P sp sp' addr t perm,
      le_pl_hlpl Spl S ->
      eval_path S perm P sp sp' ->
      addr_spath_equiv S addr t sp ->
      exists addr' t',
        eval_path_pl Spl P (addr, t) (addr', t') /\
          addr_spath_equiv S addr' t' sp'.
  Proof.
    intros S Spl P sp sp' addr t perm Hle Hpath Hequiv.
    pose proof Hle as Htemp.
    destruct Htemp as (Spl' & HComp & (Hconcr_heap & Hconcr_env) & Henv & Hheap).
    generalize dependent t.  generalize dependent addr.
    induction Hpath ; intros addr t Hequiv.
    - exists addr, t. repeat constructor ; auto.
    - destruct (spath_address_proj_simul _ _ _ _ _ _ _ _ Hle Hequiv Heval_proj)
                 as (addr' & t' & Heval_proj_pl & Hequiv').
      destruct (IHHpath addr' t' Hequiv') as (addr'' & t'' & Heval_pl' & Hequiv'').
      exists addr'', t'' ; split ; try assumption.
      econstructor ; eauto. 
    - inversion Heval_loc ; subst.
      assert (Hequiv' : addr_spath_equiv S addr t (p +++ [0]))
        by (eapply spath_address_loc_simul ; eauto). 
      destruct (IHHpath addr t Hequiv') as (addr' & t' & Heval_pl & Hequiv'').
      exists addr', t' ; split ; try assumption.
  Qed.

  Lemma eval_place_hlpl_pl_equiv :
    forall S Spl p sp perm t,
      le_pl_hlpl Spl S ->
      eval_place S perm p sp ->
      eval_type S sp t ->
      exists addr,
      eval_place_pl Spl p (addr, t) /\
      addr_spath_equiv S addr t sp.
  Proof.
    intros S Spl p sp perm t Hle Hplace Heval_type.
    pose proof Hle as Htemp.
    destruct Htemp as (Spl' & HComp & (Hconcr_heap & Hconcr_env) & Henv & Hheap).
    destruct Hplace as [(v & HS_x & Hvvp) Hpath]. simpl in *.
    destruct (blockof (encode_var p.1)) as [bi t0] eqn:Hbo.
    assert (Hsimul_path_pl : exists addr t,
               eval_path_pl Spl p.2 ((bi, 0), t0) (addr, t) /\
                 addr_spath_equiv S addr t sp).
    { eapply spath_address_path_simul ; eauto. eapply Addr_spath_base ; eauto.
      repeat econstructor. eauto. } 
    destruct Hsimul_path_pl as (addr & t' & Hplace_pl & Hequiv').
    apply addr_spath_equiv_eval_type in Heval_type as (addr' & Hequiv).
    apply (addr_spath_equiv_deterministic _ _ _ _ _ _ Hequiv) in Hequiv'
        as (Heq_addr & Heq_type); subst.
    exists addr ; split ; auto.
    exists bi, t0 ; split ; auto.
    unfold lookup_block_and_type_env.
    rewrite Henv. eapply Hconcr_env ; eauto. simpl ; intros H ; congruence.
    Qed.

  Lemma read_addr_spath_equiv_equiv :
    forall S Spl perm p sp t addr,
      le_pl_hlpl Spl S ->
      eval_place S perm p sp ->
      eval_type S sp t ->
      addr_spath_equiv S addr t sp <-> read_address Spl p t addr .
  Proof.
    intros S Spl perm p sp t addr Hle Heval_place Heval_type ; split.
    {
      intros Hequiv.
      destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ _ Hle Heval_place Heval_type)
        as (addr' & Heval_place' & Hequiv').
      rewrite (addr_spath_equiv_deterministic_addr _ _ _ _ _ _ Hequiv Hequiv') in *.
      assumption.
    }
    {
      intros (bi & t' & Hlu & Heval_path_pl). 
      destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ _ Hle Heval_place Heval_type)
        as (addr' & (bi' & t'' & Hlu' & Heval_path_pl') & Hequiv').
      rewrite Hlu in Hlu' ; injection Hlu' ; intros ; subst.
      by pose proof (eval_path_pl_deterministic _ _ _ _ _ Heval_path_pl Heval_path_pl')
        as [=] ; subst.
    }
  Qed.

  Lemma concr_val_equiv_concr_copy_val :
    forall v v_copy t vl, 
      HLPL.copy_val v v_copy ->
      concr_hlpl_val v t vl <-> concr_hlpl_val v_copy t vl.
  Proof.
    intros v v_copy t vl Hcopy. split ; intros Hconcr_val.
    {
      generalize dependent v_copy. induction Hconcr_val ; intros v_copy Hcopy.
      - inversion Hcopy ; constructor.
      - inversion Hcopy.
      - inversion Hcopy ; subst.
        specialize (IHHconcr_val1 v1' H3). specialize (IHHconcr_val2 v2' H4).
        constructor ; auto.
      - inversion Hcopy ; subst. by specialize (IHHconcr_val v_copy H2).
      - inversion Hcopy ; subst. by constructor.
    }
    {
      generalize dependent vl. generalize dependent t. generalize dependent v_copy.
      induction v ; intros v_copy Hcopy t vl Hconcr_val.
      - inversion Hcopy.
      - by inversion Hcopy ; subst.
      - inversion Hcopy ; subst. specialize (IHv v_copy H2 t vl Hconcr_val).
        by constructor.
      - inversion Hcopy ; subst. inversion Hconcr_val ; subst. by constructor.
      - inversion Hcopy ; subst. inversion Hconcr_val ; subst.
        specialize (IHv1 v1' H3 t0 vl0 H6). specialize (IHv2 v2' H4 t1 vl1 H7).
        by constructor.
    }
  Qed.

End Concretization.

(* TODO: how to remove type t from exists? *)
Lemma HLPL_PL_Read :
  forall blockof addrof S Spl perm p sp v t,
    le_pl_hlpl blockof addrof Spl S ->
    eval_place S perm p sp ->
    eval_type blockof S sp t ->
    S.[sp] = v ->
    exists vl vl', 
      read Spl p t vl /\
        concr_hlpl_val addrof v t vl' /\
        le_block vl vl'.
Proof.
  intros bo ao S Spl perm p sp v t Hle Hplace Heval_type HS_sp.
  destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ _ _ _ Hle Hplace Heval_type)
    as (addr & Hplace_pl & Hequiv).
  pose proof (eval_place_valid _ _ _ _ Hplace) as Hvsp.
  destruct Hle as (Spl' & HComp & Hconcr & Henv & Hheap).
  destruct
    (state_concr_implies_val_concr_at_addr bo ao _ _ _ _ _ _ Hconcr Hvsp HS_sp Hequiv)
    as [vl [ Hconcr_val Hlu] ].
  exists (lookup_heap_at_addr addr t Spl), vl ;
    repeat split ; auto.
  * eapply Read ; eauto.
  * rewrite <- Hlu. by apply le_heap_implies_le_block.
Qed.

Lemma sset_preserves_compatibility :
  forall S bo ao sp v,
    Compatible bo ao S ->
    not_contains_bot (S.[sp]) ->
    not_contains_loc (S.[sp]) ->
    not_contains_loc v ->
    Compatible bo ao (S.[sp <- v]).
Proof.
  intros S bo ao sp v Hcomp Hnot_bot_sp Hnot_loc_sp Hnot_loc_v.
  assert (Hvsp: valid_spath S sp).
  {
    apply get_not_bot_valid_spath. intros H ; rewrite H in *.
    specialize (Hnot_bot_sp [] (valid_nil _)). simpl in Hnot_bot_sp. congruence.
  }
  pose proof Hcomp as [Hblock Hcorr_ao Hread].
  split.
  - intros enc_x Hvsp'. pose proof not_strict_prefix_nil.
    eapply sset_not_prefix_valid in Hvsp' ; auto.
  - intros sp0 addr t l Hequiv Hnode.
    pose proof (not_value_contains_not_prefix is_loc (S.[sp <- v]) sp sp0).
    apply addr_spath_equiv_implies_valid_spath in Hequiv as Hvsp'.
    rewrite sset_sget_equal, Hnode in H by auto. 
    specialize (H Hnot_loc_v (IsLoc_Loc _) Hvsp').
    eapply Hcorr_ao ; eauto.
    * apply addr_spath_equiv_sset in Hequiv ; eauto.
    * rewrite get_node_sset_sget_not_prefix in Hnode; auto.
  - intros l sp0 Hnode.
    pose proof (not_value_contains_not_prefix is_loc (S.[sp <- v]) sp sp0).
    rewrite sset_sget_equal, Hnode in H by auto. 
    assert (Hvsp' : valid_spath (S .[ sp <- v]) sp0) by
     (apply get_not_bot_valid_spath ; intros G ; rewrite G in *; discriminate).
    specialize (H Hnot_loc_v (IsLoc_Loc _) Hvsp').
    rewrite get_node_sset_sget_not_prefix in Hnode ; auto.
    destruct (Hread l sp0 Hnode) as (addr & t & Hequiv).
    exists addr, t. apply addr_spath_equiv_sset ; auto.
Qed.


Lemma Op_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl op vS1,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{op} op => vS1 ->
    exists blockof1 addrof1 vl vl' t,
      Spl |-{op-pl} op => vl /\
      le_pl_hlpl blockof1 addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl' /\
      le_block vl vl'.
Proof.
  intros bo ao S Spl op vS1 Hle Heval.
  pose proof Hle as Htemp ; destruct Htemp as (Spl' & HComp & Hconcr & Hle_state).
  pose proof proj1 Hconcr as Hconcr_heap.
  pose proof proj2 Hconcr as Hconcr_env.
  induction Heval eqn:E.
  - exists bo, ao, [PL_int n], [PL_int n], TInt. repeat split ; try constructor ; auto.
    econstructor.
  - assert (Hevt : eval_type bo S pi t) by admit.
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ _ Hle Heval_place Hevt eq_refl)
    as (vl & vl' & Hread & Hconcr_val & Hle_val).
    exists bo, ao, vl, vl', t ; repeat split ; simpl ; auto.
    * constructor ; auto.
    * by apply (concr_val_equiv_concr_copy_val ao _ _ _ _ Hcopy_val).
  - assert (Hevt : eval_type bo S pi t) by admit.
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ _ Hle e Hevt eq_refl)
    as (vl & vl' & Hread & Hconcr_val & Hle_block).
    exists bo, ao, vl, vl', t ; repeat split ; auto.
    * constructor ; auto.
    * inversion Hread.
      exists (write_heap_at_addr addr (repeat PL_poison (sizeof t)) Spl').
         rewrite snd_pair. split ; [ idtac | split ] ; auto.
      + apply sset_preserves_compatibility ; auto. 
        unfold not_contains_loc. not_contains.
      + split.
        ** admit.
        ** intros x bi t0 Haccess Hbo_enc_x.
           rewrite env_stable_by_write_at_addr.
           eapply Hconcr_env ; eauto. intros Heq.
           eapply lookup_alter_at_accessor_None in Heq.
           apply Haccess in Heq ; congruence.
      + admit.
Admitted.

Lemma Rvalue_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl rv vS1,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{rv} rv => vS1 ->
    exists blockof1 addrof1 vl t,
      Spl |-{rv-pl} rv => vl /\
      le_pl_hlpl blockof1 addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl.
Proof.
  intros bo ao S Spl rv vS1 (Spl' & Hcomp & Hconcr & Hle) Heval.
  induction Heval.
  - apply Op_Preserves_PL_HLPL_Rel
      with (blockof := bo) (addrof := ao) (Spl := Spl) in Heval_op ;
      [ idtac | exists Spl' ; auto].
  Admitted.

Section Tests.
  Definition x := 1 % positive.
  Definition enc_x := encode_var x.
  Definition y := 2 % positive.
  Definition enc_y := encode_var y.
  Definition b1 := (1 % positive).
  Definition b2 := (2 % positive).
  Definition b3 := (3 % positive).
  Notation l1 := 0%nat.
  Notation l2 := 1%nat.

  Local Open Scope stdpp_scope.

  Definition pl_state_1 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ]};
      heap := {[ b1 := [PL_poison] ]}
    |}.
  Definition pl_state_2 : PL_state :=
    {|
      env := {[ enc_x := (b1, TPair TInt TInt) ]};
      heap := {[ b1 := [PL_poison; PL_poison] ]}
    |}.
  Definition pl_state_3 : PL_state :=
    {|
      env := {[ enc_x := (b1, TPair TRef TInt) ]};
      heap := {[ b1 := [PL_address (b1, 1) TInt ; PL_int 0] ]}
    |}.
  Definition pl_state_4 : PL_state :=
    {|
      env := {[ enc_x := (b1, TRef) ]};
      heap :=
        {[
            b1 := [PL_address (b2, 1) TRef] ;
            b2 := [PL_int 3 ; PL_address (b2, 0) TInt]
        ]}
    |}.
  Definition pl_state_5 : PL_state :=
    {|
      env := {[ enc_x := (b1, TRef) ]};
      heap :=
        {[
            b1 := [PL_address (b2, 1) TRef] ;
            b2 := [PL_poison ; PL_address (b2, 0) TInt]
        ]}
    |}.
  Definition pl_state_6 : PL_state :=
    {|
      env :=
        {[
            enc_x := (b1, TPair TInt (TPair TInt TInt))
        ]};
      heap :=
        {[
            b1 := [PL_int 0 ; PL_int 1 ; PL_int 7]
        ]}
    |}.
  Definition pl_state_7 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ]};
      heap := {[ b1 := [PL_int 3] ]}
    |}.
  Definition pl_state_8 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ; enc_y := (b2, TInt) ]};
      heap := {[ b1 := [PL_poison] ; b2 := [PL_poison] ]}
    |}.
  Definition pl_state_9 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ; enc_y := (b2, TInt) ]};
      heap := {[ b1 := [PL_int 3] ; b2 := [PL_int 7] ]}
    |}.

  Local Close Scope stdpp_scope.

  (** READ AND WRITES TESTS **)

  Goal exists S, write pl_state_1 (x, []) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (x, [Field(First)]) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (x, [Field(Second)]) TInt [PL_int 0] S.
  Proof. repeat econstructor. Qed.

  Goal read pl_state_3 (x, [Field(First) ; Deref ]) TInt [PL_int 0].
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

  Goal pl_state_1 |-{rv-pl} &mut (x, []) : TRef=> [PL_address (b1, 0) TInt].
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

  Definition addrof := (fun l => if l =? l1 then Some ((b1, 1), TInt) else None).

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
    (ptr (l1)) TRef [PL_address (b1, 1) TInt ].
  Proof. repeat econstructor. Qed.
End Tests.
