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

Inductive copy_val : PL_val -> PL_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (PL_int n) (PL_int n).

(* Functions to lookup and update PL states *)
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

Definition update_env (S : PL_state) (e : Pmap (block_id * type)) :=
  {|env := e ; heap := heap S |}.

Definition update_heap (S : PL_state) (h : Pmap pl_val) :=
  {|env := env S ; heap := h |}.

Inductive eval_proj_pl (Spl : PL_state) :
  proj -> (address * type) -> (address * type) -> Prop :=
| Eval_Deref_Ptr_Locs_pl :
  forall (addr addr' : address) (t : type),
    lookup_heap_at_addr addr (TRef t) Spl =  [PL_address addr'] ->
    eval_proj_pl Spl Deref (addr, TRef t) (addr', t)
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
  Variable blockof : positive -> block_id * type.
  Variable addrof : loan_id -> option address.

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
    forall enc_x bi t v,
      valid_spath S (enc_x, []) ->
      S.[ (enc_x, []) ] = v ->
      blockof enc_x = (bi, t) ->
      exists vl, concr_hlpl_val v t vl /\ h !! bi = Some vl .

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall enc_x bi t v,
      get_at_accessor S enc_x = Some v ->
      blockof enc_x = (bi, t) ->
      env !! enc_x = Some (bi, t).

  Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
    concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.heap(addr) *)

  Inductive addr_spath_equiv (S : HLPL_state) :
    address -> type -> spath -> Prop :=
  | Addr_spath_base sp addr bi t enc_x
      (H : blockof enc_x = (bi, t))
      (Hsp : sp = (enc_x, []))
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

  Lemma concr_val_size : forall v vl t, concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v vl t Hconcr. induction Hconcr ; auto ; try reflexivity.
    - rewrite Hs, repeat_length. reflexivity.
    - rewrite List.length_app. simpl. lia.
  Qed.

  Fixpoint typeof (v : HLPL_val) : type :=
    match v with
    | HLPL_int _ => TInt
    | HLPL_loc _ v => typeof v
    | HLPL_pair v0 v1 => TPair (typeof v0) (typeof v1)
    | _ => TInt
    end.

  Fixpoint addressof (v : HLPL_val) (bi : block_id) (rvp: list nat) : address :=
    match rvp with
    | 0 :: rvp' =>
        addressof v bi rvp'
    | 1 :: rvp' =>
        (addressof v bi rvp') +o sizeof (typeof (v.[[rev rvp' ++ [0] ]]))
    | [] | _ :: _ => (bi, 0)
    end.

  Record Compatible (S : HLPL_state) : Prop :=
    mkCompatible
      {
        block_dom :
        forall (enc_x : positive), 
          valid_spath S (enc_x, []) ->
          exists bi t, blockof enc_x = (bi, t) 
      ; well_typed :
        forall (enc_x : positive) bi t, 
          valid_spath S (enc_x, []) ->
          blockof enc_x = (bi, t) ->
          typeof (S.[(enc_x, [])]) = t
      ; pointers_well_typed :
        forall sp sp' addr addr' t t' l,
          get_node (S.[sp]) = HLPL_ptrC l ->
          addr_spath_equiv S addr (TRef t) sp ->
          get_node (S.[sp']) = HLPL_locC l ->
          addr_spath_equiv S addr' t' sp' ->
          t' = t
      ; correct_addrof :
        forall (sp : spath) (addr : address) t l,
          addr_spath_equiv S addr t sp ->
          get_node (S.[sp]) = HLPL_locC l ->
          addrof l = Some addr
      ; reachable_loc :
        forall l sp,
          get_node (S.[sp]) = HLPL_locC l ->
          exists addr t, addr_spath_equiv S addr t sp
      }.

  Inductive le_val : PL_val -> PL_val -> Prop :=
  | lev_refl v : le_val v v
  | lev_poison v : le_val v PL_poison.

  Definition le_block (b1 b2 : pl_val) :=
    Forall2 le_val b1 b2.

  Definition le_heap (h1 h2: Pmap pl_val) : Prop :=
    forall bi b1 b2,
      (h1 !! bi = Some b1 \/ h2 !! bi = Some b2) ->
        h1 !! bi = Some b1 /\ h2 !! bi = Some b2 /\ le_block b1 b2.

  Definition le_pl_state (Spl1 Spl2 : PL_state) : Prop :=
    env Spl1 = env Spl2 /\ le_heap (heap Spl1) (heap Spl2).

  Infix "<={pl}" := le_pl_state (at level 70).

  Definition le_pl_hlpl (Spl : PL_state) (S : HLPL_state) : Prop :=
    exists Spl', Compatible S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.


  (* Addr_spath_equiv is a function: given state S and spath sp, addr and t are unique *)
  Lemma list_app_elem_not_nil {A : Type} :
    forall (l : list A) (a : A), l ++ [ a ] <> [].
  Proof. intros l a Hcontr. apply app_nil, proj2 in Hcontr. discriminate. Qed.

  Lemma spath_app_elem_not_nil :
    forall (sp : spath) (n : nat) enc_x, sp +++ [ n ] <> (enc_x, []).
  Proof.
    intros. unfold app_spath_vpath. intros contra.
    injection contra as _ H. destruct (list_app_elem_not_nil sp.2 n H).
  Qed.
    
  Ltac rewrite_pairs :=
    match goal with
    | H1 : ?sp1.1 = ?sp2.1, H2 : ?sp1.2 = ?sp2.2 |- _ =>
        assert (Htemp : sp1 = sp2) by
        (rewrite surjective_pairing with (p := sp1),
            surjective_pairing with (p := sp2) ; congruence) ;
        subst sp1 ; clear H1 H2
    end.

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

  Lemma addr_spath_equiv_exists_type :
    forall S sp,
      Compatible S ->
      valid_spath S sp ->
      exists addr t,
        addr_spath_equiv S addr t sp.
  Proof.
    intros S sp [Hblock_dom Well_Typed _ _ _] Hvsp.
    exists (addressof (S.[(sp.1, [])]) ((blockof sp.1).1) (rev sp.2)), (typeof (S.[sp])).
    induction sp using ListBackInd.state_path_back_ind ; simpl.
    - destruct (Hblock_dom enc_x Hvsp) as (bi & t & Hbo).
      eapply Addr_spath_base ; eauto.
      rewrite Hbo. simpl. specialize (Well_Typed enc_x bi t Hvsp Hbo).
      congruence.
    - apply valid_spath_app in Hvsp as Htemp. destruct Htemp as [Hvsp' _].
      specialize (IHsp Hvsp'). rewrite rev_app_distr.
      destruct n as [ | [ | ?] ] ; destruct (S.[sp]) eqn:HeqS_sp ;
        discriminate_val_from_valid_spath S sp.
      * rewrite sget_app, HeqS_sp. eapply Addr_spath_loc ; try congruence' ; auto.
      * simpl. eapply Addr_spath_pair_first ; try congruence'.
        rewrite sget_app, HeqS_sp. simpl. eassumption.
      * simpl. apply Addr_spath_pair_second ; try congruence'. 
        rewrite rev_involutive, sget_app, <- sget_app, app_spath_vpath_assoc, sget_app.
        replace (S .[ (sp.1, []) +++ sp.2]) with (S.[sp ]) by reflexivity.
        rewrite HeqS_sp. assumption.
Qed.

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
    intros S1 S2 addr t Hle_heap.
    unfold lookup_heap_at_addr. 
    destruct (heap S1 !! addr.1) eqn:E1; destruct (heap S2 !! addr.1) eqn:E2.
    - destruct (Hle_heap addr.1 l l0 (or_introl E1)) as [_ [_ Hblock] ].
      apply Forall2_take, Forall2_drop, Hblock.
    - destruct (Hle_heap addr.1 l l (or_introl E1)) as [_ [HS2 _] ].
      unfold "!!" in * ; congruence.
    - destruct (Hle_heap addr.1 l l (or_intror E2)) as [HS1 [_ _] ].
      unfold "!!" in * ; congruence.
    - unfold le_block. constructor.
  Qed.

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
    destruct HComp as [_ _ Hwell_typed Hcorr_addrof Hloc].
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
      exists addr', t0 ; pose proof (Hwell_typed _ _ _ _ _ _ _ H Hequiv H0 Hequiv') ;
        subst ; split ; auto.
      constructor.
      pose proof (Hcorr_addrof _ _ _ _ Hequiv' H0).
      rewrite Haddr in H1 ; injection H1 ; intros ; subst ; clear H1.
      assert (Hle_block : le_block (lookup_heap_at_addr addr (TRef t0) Spl)
                            (lookup_heap_at_addr addr (TRef t0) Spl'))
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
    forall S Spl p sp perm,
      le_pl_hlpl Spl S ->
      eval_place S perm p sp ->
      exists addr t,
      eval_place_pl Spl p (addr, t) /\
      addr_spath_equiv S addr t sp.
  Proof.
    intros S Spl p sp perm Hle Hplace.
    pose proof Hle as Htemp.
    destruct Htemp as (Spl' & HComp & (Hconcr_heap & Hconcr_env) & Henv & Hheap).
    destruct Hplace as [(v & HS_x & Hvvp) Hpath]. simpl in *.
    destruct (blockof (encode_var p.1)) as [bi t0] eqn:Hbo.
    assert (Hsimul_path_pl : exists addr t,
               eval_path_pl Spl p.2 ((bi, 0), t0) (addr, t) /\
                 addr_spath_equiv S addr t sp).
    { eapply spath_address_path_simul ; eauto. eapply Addr_spath_base ; eauto. }
    destruct Hsimul_path_pl as (addr & t & Hplace_pl & Hequiv').
    exists addr, t ; split ; auto.
    exists bi, t0 ; split ; auto.
    unfold lookup_block_and_type_env.
    rewrite Henv. eapply Hconcr_env ; eauto.
    Qed.
End Concretization.

(* TODO: how to remove type t from exists? *)
Lemma HLPL_PL_Read :
  forall blockof addrof S Spl perm p sp v,
    le_pl_hlpl blockof addrof Spl S ->
    eval_place S perm p sp ->
    valid_spath S sp ->
    S.[sp] = v ->
    exists t vl, 
      read Spl p t vl /\
        forall vl', concr_hlpl_val addrof v t vl' -> le_block vl vl'.
  Proof.
  intros bo ao S Spl perm p sp v Hle Hplace Hvsp HS_sp.
  destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ _ _ Hle Hplace)
    as (addr & t & Hplace_pl & Hequiv).
  destruct Hle as (Spl' & HComp & Hconcr & Henv & Hheap).
  destruct
    (state_concr_implies_val_concr_at_addr bo ao _ _ _ _ _ _ Hconcr Hvsp HS_sp Hequiv)
    as [vl [ Hconcr_val Hlu] ].
  exists t, (lookup_heap_at_addr addr t Spl) ; repeat split ; auto.
  * eapply Read ; eauto.
  * intros vl' Hconcr_val'.
    apply concr_val_implies_concr_val_comp in Hconcr_val, Hconcr_val'.
    rewrite Hconcr_val in Hconcr_val' ; injection Hconcr_val' ; intros ; subst.
    apply le_heap_implies_le_block ; auto.
  Qed.

Lemma Op_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl op vS1,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{op} op => vS1 ->
    exists blockof1 addrof1 vl t,
      Spl |-{op-pl} op => vl /\
      le_pl_hlpl blockof1 addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl.
Proof.
  intros bo ao S Spl op vS1 Hle Heval.
  pose proof Hle as Htemp ; destruct Htemp as (Spl' & HComp & Hconcr & Hle_state).
  induction Heval.
  - exists bo, ao, [PL_int n], TInt. repeat split ; try constructor.
    exists Spl' ; auto.
  - assert (Hvsp : valid_spath S pi) by admit.
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
      env := {[ enc_x := (b1, TPair (TRef TInt) TInt) ]};
      heap := {[ b1 := [PL_address (b1, 1); PL_int 0] ]}
    |}.
  Definition pl_state_4 : PL_state :=
    {|
      env := {[ enc_x := (b1, TRef (TRef TInt)) ]};
      heap :=
        {[
            b1 := [PL_address (b2, 1)] ;
            b2 := [PL_int 3 ; PL_address (b2, 0)]
        ]}
    |}.
  Definition pl_state_5 : PL_state :=
    {|
      env := {[ enc_x := (b1, TRef (TRef TInt)) ]};
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
