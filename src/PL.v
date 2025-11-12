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

Lemma sizeof_ge_1 : forall tau, sizeof tau >= 1.
Proof.
  induction tau ; simpl ; lia. Qed.

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

Infix "+o" := add_offset (at level 30).

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

Notation "Spl !!h bi" := (lookup bi (heap Spl)) (at level 40).
Notation "Spl !!e bi" := (lookup bi (env Spl)) (at level 40).
  
Definition valid_access (S : PL_state) (addr : address) (t : type) :=
  exists vl, S !!h addr.1 = Some vl /\ addr.2 + sizeof t <= length vl.

Lemma valid_access_dec :
  forall S addr t,
    { valid_access S addr t } + { ~ valid_access S addr t }.
Proof.
  intros S addr t.
  destruct (S !!h addr.1) as [ vl | ] eqn:Elu ; unfold valid_access in *.
  - destruct (le_gt_dec (addr.2 + sizeof t) (length vl)).
    * left ; exists vl ; auto.
    * right. intros (vl' & Hlu & Hsize).
      unfold "!!h" in *. assert (vl = vl') by congruence.
      subst. lia.
  - right. intros (vl & Hlu & _).
    unfold "!!h" in *. congruence.
Defined.

Ltac is_valid_access S addr t :=
  match goal with
  | H : valid_access S addr t |- _ =>
      destruct (valid_access_dec S addr t) as [_H | ] ;
      [ clear _H | contradiction ]
  end.

Definition lookup_at_addr (addr : address) (t : type) (S : PL_state) : option pl_val :=
  let size := sizeof t in
  if valid_access_dec S addr t then
    option_map (fun vl => firstn size (skipn addr.2 vl)) (lookup addr.1 (heap S))
  else None.

Definition write_at_addr (addr : address) (t : type) (vl : pl_val) (S : PL_state) :=
  let (bi, off) := addr in
  let h := 
    alter (fun block => (firstn off block) ++ vl ++ (skipn (off + length vl) block))
      bi (heap S) in
  update_heap S h.

Notation "S .h.[ addr : t ]" := (lookup_at_addr addr t S)
                                  (at level 50, addr at next level).

Notation "S .h.[ addr <- vl : t ]" := (write_at_addr addr t vl S)
                                       (vl at next level).

Lemma env_stable_by_write_at_addr :
  forall S addr t vl, env (S.h.[addr <- vl : t]) = env S.
Proof.
  intros [env_S heap_S] [bi off] vl ?. reflexivity.
Qed.

Lemma dom_stable_by_write_at_addr :
  forall S1 S2 addr t1 t2 vl1 vl2,
    dom (heap S1) = dom (heap S2) ->
    dom (heap (S1.h.[addr <- vl1 : t1])) = dom (heap (S2.h.[addr <- vl2 : t2 ])).
Proof.
  intros [e1 h1] [e2 h2] [bi off] t1 t2 vl1 vl2 Heq. 
  unfold write_at_addr. simpl in *. by repeat rewrite dom_alter_L.
Qed.

(** Evaluating projections as addresses *)

Inductive eval_proj_pl (Spl : PL_state) :
  proj -> (address * type) -> (address * type) -> Prop :=
| Eval_Deref_Ptr_Locs_pl :
  forall (addr addr' : address) (t: type),
    lookup_at_addr addr TRef Spl = Some [PL_address addr' t] ->
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
      (Hlu : lookup_at_addr addr t S = Some vl) :
    read S p t vl.

Variant write (S : PL_state) (p : place) (t : type) (vl : pl_val)
  : PL_state -> Prop :=
  | Write addr vl' vl'' h
      (Haddr : read_address S p t addr)
      (Hlu : Some vl' = S !!h addr.1)
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
      assert (_Htemp : sp1 = sp2) by
      (rewrite surjective_pairing with (p := sp1),
          surjective_pairing with (p := sp2) ; congruence) ;
      subst sp1 ; clear H1 H2
  end.


(* Concretization of HLPL values to PL values *)

Section Concretization.
  Variable blockof : positive -> block_id * type.
  Variable addrof : loan_id -> option (address * type).
  Axiom blockof_inj :
    forall p1 p2 bi1 bi2 t1 t2,
      blockof p1 = (bi1, t1) ->
      blockof p2 = (bi2, t2) ->
      (p1 = p2 <-> bi1 = bi2).

  Lemma blockof_inj_inv :
    forall p1 p2 bi1 bi2 t1 t2,
      blockof p1 = (bi1, t1) ->
      blockof p2 = (bi2, t2) ->
      (p1 <> p2 <-> bi1 <> bi2).
  Proof.
    intros. split ; intros G contra.
    - rewrite <- blockof_inj in contra ; eauto. 
    - rewrite blockof_inj in contra ; eauto. 
  Qed.

  Local Open Scope stdpp_scope.

  (** Assigning types to vpath and spath *)
  Inductive eval_type_val (v : HLPL_val) (ti : type) : vpath -> type -> Prop :=
  | Eval_base_type :
    eval_type_val v ti nil ti
  | Eval_loc_type_val vp t l
    (Hnode : get_node ( v.[[ vp ]] ) = HLPL_locC l)
    (Hrec : eval_type_val v ti vp t) :
    eval_type_val v ti (vp ++ [0]) t
  | Eval_pair_first_type_val vp t0 t1
    (Hnode : get_node ( v.[[ vp ]] ) = HLPL_pairC)
    (Hrec : eval_type_val v ti vp (TPair t0 t1)) :
    eval_type_val v ti (vp ++ [0]) t0
  | Eval_pair_second_type vp t0 t1
    (Hnode : get_node ( v.[[ vp ]] ) = HLPL_pairC)
    (Hrec : eval_type_val v ti vp (TPair t0 t1)) :
    eval_type_val v ti (vp ++ [1]) t1
  .

  Inductive eval_type (S : HLPL_state) : spath -> type -> Prop :=
  | Eval_type sp t t' bi
      (Hvp : valid_spath S (sp.1, []))
      (Hbo : blockof sp.1 = (bi, t))
      (Heval_type : eval_type_val (S.[(sp.1, [])]) t sp.2 t') :
    eval_type S sp t'.


  Lemma eval_type_val_deterministic :
    forall v vp tinit t0 t1,
      eval_type_val v tinit vp t0 ->
      eval_type_val v tinit vp t1 ->
      t0 = t1.
  Proof.
    intros v vp tinit t0 t1 Het0. generalize dependent t1.
    pose proof (@list_app_elem_not_nil nat).
    induction Het0 ; intros ? Het' ; inversion Het' ; subst ; auto ;
      try (sp_discriminate_or_find_equalities ; congruence) ;
    sp_discriminate_or_find_equalities.
    - by apply IHHet0.
    - specialize (IHHet0 (TPair t2 t4) Hrec). congruence.
    - specialize (IHHet0 (TPair t3 t2) Hrec). congruence.
  Qed.

  Lemma eval_type_deterministic :
    forall S sp t0 t1,
      eval_type S sp t0 ->
      eval_type S sp t1 ->
      t1 = t0.
  Proof.
    intros S sp t0 t1 Het0 Het1.
    inversion Het0 ; inversion Het1 ; subst.
    assert (t = t2) by congruence ; subst. eapply eval_type_val_deterministic ; eauto.
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

  Lemma concr_val_deterministic :
    forall v t vl0 vl1,
      concr_hlpl_val v t vl0 ->
      concr_hlpl_val v t vl1 ->
      vl0 = vl1.
  Proof. intros. apply concr_val_implies_concr_val_comp in H, H0. congruence. Qed.

  Definition concr_hlpl_heap (S : HLPL_state) (h : Pmap pl_val) : Prop :=
    forall enc_x bi t v,
      valid_spath S (enc_x, []) ->
      S.[ (enc_x, []) ] = v ->
      blockof enc_x = (bi, t) ->
      exists vl, concr_hlpl_val v t vl /\ h !! bi = Some vl .

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall enc_x bi t,
      valid_spath S (enc_x, []) ->
      blockof enc_x = (bi, t) ->
      env !! enc_x = Some (bi, t).

  Definition concr_hlpl (S : HLPL_state) (Spl : PL_state) : Prop :=
    concr_hlpl_heap S (heap Spl) /\ concr_hlpl_env S (env Spl).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.heap(addr) *)

  Inductive off_vpath_equiv (v : HLPL_val) (t : type) :
    offset -> type -> vpath -> Prop :=
  | Offset_vpath_base :
    off_vpath_equiv v t 0 t nil
  | Offset_vpath_pair_first off vp t0 t1
      (Hpair : get_node (v.[[ vp ]]) = HLPL_pairC)
      (Hrec : off_vpath_equiv v t off (TPair t0 t1) vp) :
    off_vpath_equiv v t off t0 (vp ++ [0])
  | Offset_vpath_pair_second off vp t0 t1
      (Hpair : get_node (v.[[ vp ]]) = HLPL_pairC)
      (Hrec : off_vpath_equiv v t off (TPair t0 t1) vp) :
    off_vpath_equiv v t (off + sizeof t0) t1 (vp ++ [1])
  | Offset_vpath_loc off vp t' l
      (Hloc : get_node (v.[[ vp ]]) = HLPL_locC l)
      (Hrec : off_vpath_equiv v t off t' vp) :
    off_vpath_equiv v t off t' (vp ++ [0]).

  Inductive addr_spath_equiv (S : HLPL_state) : address -> type -> spath -> Prop :=
  | Addr_spath_base sp v addr tinit t
      (H : blockof sp.1 = (addr.1, tinit))
      (Hsp1 : S.[(sp.1, [])] = v)
      (Hvp : valid_spath S (sp.1, []))
      (Hvequiv: off_vpath_equiv v tinit addr.2 t sp.2) :
    addr_spath_equiv S addr t sp.

  Lemma Addr_spath_pair_first :
    forall S sp addr t0 t1,
      get_node (S.[ sp ]) = HLPL_pairC ->
      addr_spath_equiv S addr (TPair t0 t1) sp ->
      addr_spath_equiv S addr t0 (sp +++ [0]).
  Proof.
    intros S sp addr t0 t1 Hnode Hequiv.
    inversion Hequiv ; subst. econstructor ; eauto. simpl.
    eapply Offset_vpath_pair_first ; eauto.
    rewrite <- sget_app. unfold app_spath_vpath. simpl.
    by rewrite <- surjective_pairing.
  Qed.

  Lemma Addr_spath_pair_second:
    forall S sp addr t0 t1,
      get_node (S.[ sp ]) = HLPL_pairC ->
      addr_spath_equiv S addr (TPair t0 t1) sp ->
      addr_spath_equiv S (addr +o sizeof t0) t1 (sp +++ [1]).
  Proof.
    intros S sp addr t0 t1 Hnode Hequiv.
    inversion Hequiv ; subst. econstructor ; eauto. simpl.
    eapply Offset_vpath_pair_second ; eauto.
    rewrite <- sget_app. unfold app_spath_vpath. simpl.
    by rewrite <- surjective_pairing.
  Qed.

  Lemma Addr_spath_loc :
    forall S sp addr t l,
      get_node (S.[ sp ]) = HLPL_locC l ->
      addr_spath_equiv S addr t sp ->
      addr_spath_equiv S addr t (sp +++ [0]).
  Proof.
    intros S sp addr t0 t1 Hnode Hequiv.
    inversion Hequiv ; subst. econstructor ; eauto. simpl.
    eapply Offset_vpath_loc; eauto.
    rewrite <- sget_app. unfold app_spath_vpath. simpl.
    by rewrite <- surjective_pairing.
  Qed.

  Definition addr_spath_equiv_fin S addr sp :=
    exists t, addr_spath_equiv S addr t sp.

  Lemma off_vpath_equiv_sizeof :
    forall vi ti t off vp,
      off_vpath_equiv vi ti off t vp ->
      off + sizeof t <= sizeof ti.
  Proof. intros. induction H ; simpl in * ; try lia. Qed.

  Lemma off_vpath_equiv_eval_type :
    forall v vp tinit t,
      (exists off, off_vpath_equiv v tinit off t vp) <-> eval_type_val v tinit vp t.
  Proof.
    intros v vp tinit t ; split ; [intros (off & Hvequiv) | intros Het ].
    { induction Hvequiv ; subst ; try (econstructor ; eassumption). }
    {
      induction Het.
      - exists 0. econstructor ; eauto.
      - destruct IHHet as (off & Hvequiv).
        exists off. eapply Offset_vpath_loc ; eauto.
      - destruct IHHet as (off & Hvequiv).
        exists off. eapply Offset_vpath_pair_first ; eauto.
      - destruct IHHet as (off & Hvequiv).
        exists (off + sizeof t0). eapply Offset_vpath_pair_second ; eauto.
    }
  Qed.

  Lemma addr_spath_equiv_eval_type :
    forall S sp t, (exists addr, addr_spath_equiv S addr t sp) <-> eval_type S sp t.
    intros S sp t ; split ; [intros (addr & Hequiv) | intros Heval_type].
    - inversion Hequiv ; subst.
      econstructor ; eauto.
      apply off_vpath_equiv_eval_type. eexists ; eauto.
    - inversion Heval_type ; subst.
      apply off_vpath_equiv_eval_type in Heval_type0.
      destruct Heval_type0 as (off & Hvequiv).
      exists (bi, off). econstructor ; eauto.
  Qed.

  Lemma off_vpath_equiv_vset : 
    forall v tinit t off vp0 vp1 v',
      ~ vprefix vp1 vp0 ->
      off_vpath_equiv v tinit off t vp0 <->
        off_vpath_equiv (v.[[ vp1 <- v' ]]) tinit off t vp0.
  Proof.
    intros v tinit t off vp0 vp1 v' Hpref. split ; intros Hvequiv.
    {
      induction Hvequiv ; subst.
      - eapply Offset_vpath_base ; eauto.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_pair_first ; eauto.
        rewrite get_node_vset_vget_not_prefix ; auto.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_pair_second ; eauto.
        rewrite get_node_vset_vget_not_prefix ; auto.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_loc ; eauto.
        rewrite get_node_vset_vget_not_prefix ; eauto.
    }
    {
      induction Hvequiv ; subst.
      - eapply Offset_vpath_base.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_pair_first ; eauto.
        rewrite get_node_vset_vget_not_prefix in Hpair ; eauto.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_pair_second ; eauto.
        rewrite get_node_vset_vget_not_prefix in Hpair ; eauto.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_loc ; eauto.
        rewrite get_node_vset_vget_not_prefix in Hloc ; eauto.
    }
  Qed.

  Lemma addr_spath_equiv_sset : 
    forall S addr t sp0 sp1 v,
      ~ prefix sp1 sp0 ->
      addr_spath_equiv S addr t sp0 <->
      addr_spath_equiv (S .[ sp1 <- v]) addr t sp0.
  Proof.
    intros S addr t sp0 sp1 v Hpref.
    assert (Hsp0 : sp0 = (sp0.1, []) +++ sp0.2) by
      (unfold "+++" ; simpl ; by rewrite <- surjective_pairing).
    assert (Hsp1 : sp1 = (sp1.1, []) +++ sp1.2) by
      (unfold "+++" ; simpl ; by rewrite <- surjective_pairing).
    rewrite Hsp0, Hsp1.
    split ; intros Hequiv ; inversion Hequiv ; subst.
    - econstructor ; eauto.
      + rewrite <- sset_not_prefix_valid ; eauto. apply not_strict_prefix_nil.
      + simpl fst in *. simpl snd in *.
        destruct (not_prefix_var_equal_or_not_vprefix sp1 sp0 Hpref).
        * rewrite sset_sget_disj ; auto. left. auto.
        * destruct H0 as [Heq Hvpref].
          rewrite Heq in *. rewrite sset_sget_prefix ; auto.
          apply off_vpath_equiv_vset ; auto.
    - rewrite <- sset_not_prefix_valid in Hvp ; eauto ; [ | apply not_strict_prefix_nil].
      econstructor ; eauto.
      simpl fst in * ; simpl snd in *.
      destruct (not_prefix_var_equal_or_not_vprefix sp1 sp0 Hpref).
        * rewrite sset_sget_disj in Hvequiv ; auto. by left.
        * destruct H0 ; subst. rewrite <- H0 in *.
          rewrite sset_sget_prefix, <- off_vpath_equiv_vset in Hvequiv ; eauto.
  Qed.
  
  Lemma addr_spath_equiv_var_bi :
    forall S addr t sp,
      addr_spath_equiv S addr t sp -> exists t0, blockof sp.1 = (addr.1, t0).
  Proof.
    intros S addr t sp Hequiv. inversion Hequiv ; subst ; simpl ; eauto. 
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
        forall x enc_x : positive,
          enc_x = encode_var x ->
          S.[(enc_x, [])] <> bot ->
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

  Global Program Instance IsPreorderVal: PreOrder le_val.
  Next Obligation.
    constructor. Qed.
  Next Obligation.
  intros x y z Hxy Hyz ; inversion Hxy ; inversion Hyz ; subst ; try constructor. Qed.
  
  Definition le_block : relation pl_val := Forall2 le_val.
  Global Instance IsPreorderBlock: PreOrder le_block.
  apply PreOrder_instance_1, IsPreorderVal. Qed.

  Definition le_heap : relation (Pmap pl_val) :=
    fun h1 h2 =>
      dom h1 = dom h2 /\
      forall bi b1,
        h1 !! bi = Some b1 ->
        exists b2, h2 !! bi = Some b2 /\ le_block b1 b2.
  Global Program Instance IsPreorderHeap: PreOrder le_heap.
  Next Obligation.
    split ; auto.
    intros bi b1 Hbi ; exists b1 ; repeat split ; auto. apply IsPreorderBlock. Qed.
  Next Obligation.
    intros h1 h2 h3 [Hdom12 H12] [Hdom23 H23].
    split. 
    - etransitivity ; eauto.
    - intros bi b1 Hh1.
      destruct (H12 bi b1 Hh1) as (b2 & Hh2 & Hle12).
      destruct (H23 bi b2 Hh2) as (b3 & Hh3 & Hle23).
      exists b3 ; split ; auto. etransitivity ; eauto.
  Qed.
  
  Definition le_pl_state : relation PL_state :=
    fun Spl1 Spl2 => env Spl1 = env Spl2 /\ le_heap (heap Spl1) (heap Spl2).
  Global Program Instance IsPreorderState : PreOrder le_pl_state.
  Next Obligation.
    intros Spl. split ; reflexivity. Qed.
  Next Obligation.
    intros Spl1 Spl2 Spl3 [env12 heap12] [env23 heap23]. split ; try congruence.
    etransitivity ; eauto.
  Qed.

  Infix "<={pl}" := le_pl_state (at level 70).

  Definition le_pl_hlpl (Spl : PL_state) (S : HLPL_state) : Prop :=
    exists Spl', Compatible S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.

  Lemma le_block_poison :
    forall vl n,
      length vl = n ->
      le_block vl (repeat PL_poison n).
  Proof.
    intros vl.
    induction vl ; intros n Hlen ; simpl in Hlen.
    - subst. constructor.
    - rewrite <- Hlen. constructor.
      * destruct a ; constructor.
      * by apply (IHvl (length vl)).
  Qed.

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

  Lemma off_vpath_equiv_deterministic_type :
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      t1 = t2.
  Proof.
    intros vinit tinit vp. induction vp using ListBackInd.list_back_ind ; intros.
    - inversion H ; inversion H0 ; subst ; by try sp_discriminate_or_find_equalities.
    - inversion H ; inversion H0 ; subst ;
        repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs).
      * assert (Hpt : TPair t1 t3 = TPair t2 t5) by (eapply IHvp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * assert (Hpt : TPair t0 t1 = TPair t4 t2) by (eapply IHvp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * eapply IHvp ; eauto.
  Qed.

  Lemma off_vpath_equiv_deterministic_off :
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      off1 = off2.
  Proof.
    intros vinit tinit vp. induction vp using ListBackInd.list_back_ind ; intros.
    - inversion H ; inversion H0 ; subst ; by try sp_discriminate_or_find_equalities.
    - inversion H ; inversion H0 ; subst ;
        repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs).
      * eapply IHvp ; eauto.
      * assert (off = off0) by (eapply IHvp ; eauto). subst.
        assert (TPair t0 t1 = TPair t4 t2)
          by (eapply off_vpath_equiv_deterministic_type ; eauto).
        congruence.
      * eapply IHvp ; eauto.
  Qed.

  Lemma off_vpath_equiv_deterministic:
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      off1 = off2 /\ t1 = t2.
  Proof.
    intros. split ;
      [ eapply off_vpath_equiv_deterministic_off ; eauto |
        eapply off_vpath_equiv_deterministic_type ; eauto
      ].
  Qed.

  Lemma addr_spath_equiv_deterministic_type :
    forall S sp addr1 addr2 t1 t2,
      addr_spath_equiv S addr1 t1 sp ->
      addr_spath_equiv S addr2 t2 sp ->
      t1 = t2.
  Proof.
    intros. inversion H ; inversion H0 ; subst.
    assert (tinit = tinit0) by congruence ; subst.
    eapply off_vpath_equiv_deterministic_type ; eauto.
  Qed.
 
  Lemma addr_spath_equiv_deterministic_addr :
    forall S sp addr1 addr2 t1 t2,
      addr_spath_equiv S addr1 t1 sp ->
      addr_spath_equiv S addr2 t2 sp ->
      addr1 = addr2.
  Proof.
    intros. inversion H ; inversion H0 ; subst.
    destruct addr1, addr2.
    assert (tinit = tinit0) by congruence ; subst. simpl in *.
    assert (b = b0) by congruence ; subst. 
    eapply f_equal, off_vpath_equiv_deterministic_off ; eauto.
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

  Lemma off_vpath_equiv_implies_valid_vpath :
    forall vinit vp off t tinit, 
      off_vpath_equiv vinit tinit off t vp ->
      valid_vpath vinit vp.
  Proof.
    intros vinit vp off t tinit Hvequiv. induction Hvequiv ; subst ; auto ; 
      try (apply valid_vpath_app ; split ; auto ; nodes_to_val ; repeat econstructor).
    repeat econstructor.
  Qed.

  Lemma addr_spath_equiv_implies_valid_spath :
    forall S sp addr t, 
      addr_spath_equiv S addr t sp ->
      valid_spath S sp.
  Proof.
    intros S sp addr t Hequiv. inversion Hequiv ; inversion Hvp ; subst.
    apply off_vpath_equiv_implies_valid_vpath in Hvequiv.
    unfold sget in Hvequiv. destruct H3. simpl in *. 
    rewrite H0 in Hvequiv.
    econstructor ; split ; eauto. 
  Qed.

  Lemma addr_spath_equiv_implies_valid_access:
    forall S Spl sp addr t, 
      concr_hlpl S Spl ->
      addr_spath_equiv S addr t sp ->
      valid_access Spl addr t.
  Proof.
    intros S Spl (enc_x, vp) (bi, off) t [Hconcr_heap Hconcr_env] Hequiv.
    inversion Hequiv ; subst. simpl in *.
    induction Hvequiv ; subst.
    - destruct (Hconcr_heap enc_x bi tinit (S.[(enc_x, [])]) Hvp eq_refl H)
        as (vl & Hconcr_val & Hbi).
      apply concr_val_size in Hconcr_val.
      exists vl ; split ; auto ; rewrite <- Hconcr_val ; simpl ; lia.
    - destruct IHHvequiv.
      * econstructor ; eauto.
      * destruct H0. econstructor ; split ; eauto. simpl in *. lia.
    - destruct IHHvequiv.
      * econstructor ; eauto.
      * destruct H0. econstructor ; split ; eauto. simpl in *. lia.
    - destruct IHHvequiv.
      * econstructor ; eauto.
      * destruct H0. econstructor ; split ; eauto.
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

  (* Lookup heap lemmas*)
  Lemma lookup_heap_Some :
    forall Spl addr t vl,
      Spl.h.[ addr : t ] = Some vl -> valid_access Spl addr t.
  Proof.
    intros Spl addr t vl H. unfold lookup_at_addr in H.
    destruct (valid_access_dec Spl addr t) as [(b & Hb & Hsize) | ].
    - replace (Spl !!h addr.1) with (Some b) in H. injection H as <-.
      exists b ; auto.
    - congruence.
  Qed.
  
  Lemma lookup_heap_size :
    forall Spl addr t vl,
      Spl.h.[ addr : t ] = Some vl -> length vl = sizeof t.
  Proof.
    intros Spl addr t vl Hlu.
    apply lookup_heap_Some in Hlu as Hva. 
    unfold lookup_at_addr in Hlu.
    destruct (valid_access_dec Spl addr t) as [(b & Hb & Hsize) | ] ; try contradiction.
    replace (Spl !!h addr.1) with (Some b) in Hlu. injection Hlu as <-.
    rewrite length_take, length_drop. lia.
  Qed.
    
  Lemma lookup_heap_pair :
    forall Spl addr t0 t1 vl0 vl1,
      length vl0 = sizeof t0 ->
      length vl1 = sizeof t1 ->
      Spl.h.[ addr : TPair t0 t1 ] = Some (vl0 ++ vl1) <->
        Spl.h.[ addr : t0 ] = Some vl0 /\ Spl.h.[ addr +o sizeof t0 : t1 ] = Some vl1.
  Proof.
    intros Spl addr t0 t1 vl0 vl1 Hlen0 Hlen1. split ; intros H.
    - apply lookup_heap_Some in H as Hva.
      destruct Hva as (b & Hb & Hsize). simpl in Hsize.
      apply lookup_heap_Some in H as Hva01.
      assert (Hva0 : valid_access Spl addr t0).
      { exists b ; split ; auto ; lia. }
      assert (Hva1 : valid_access Spl (addr +o sizeof t0) t1).
      { exists b ; split ; auto ; rewrite addr_add_offset_snd ; lia. }
      unfold lookup_at_addr in *.
      is_valid_access Spl addr t0 ; is_valid_access Spl (addr +o sizeof t0) t1 ;
        is_valid_access Spl addr (TPair t0 t1).
      replace (Spl !!h addr.1) with (Some b) in H ;
        repeat replace (Spl !!h addr.1) with (Some b) ; simpl in *.
      injection H as H . split ; f_equal.
      * apply f_equal with (f := take (sizeof t0)) in H.
        rewrite <- Hlen0, <- Hlen1, take_take, take_app_length in H.
        rewrite <- H, <- Hlen0.
        by replace (length vl0 `min` (length vl0+length vl1)) with (length vl0) by lia.
      * apply f_equal with (f := drop (sizeof t0)) in H.
        rewrite <- Hlen0, <- Hlen1 in *.
        rewrite skipn_firstn_comm, drop_app_length, drop_drop in H.
        replace (length vl0 + length vl1 - length vl0) with (length vl1) in H by lia.
        auto.
    - destruct H as [H0 H1]. apply lookup_heap_Some in H0 as Hva0, H1 as Hva1.
      unfold lookup_at_addr in *.
      is_valid_access Spl addr t0 ; is_valid_access Spl (addr +o sizeof t0) t1.
      destruct Hva0 as (b & Hb & Hsize0). destruct Hva1 as (b' & Hb' & Hsize1).
      simpl in *. rewrite Hb' in Hb. injection Hb as ->. rewrite Hb' in *.
      simpl in *.
      assert (Hva01 : valid_access Spl addr (TPair t0 t1)) by
      ( exists b ; split ; auto ; simpl ; lia).
      is_valid_access Spl addr (TPair t0 t1) ; f_equal.
      injection H0 as H0 ; injection H1 as H1.
      by rewrite <- H0, <- H1, <- drop_drop, take_take_drop.
  Qed.
                                   
  (* Concretization of states implies concretization of values *)

  Lemma lookup_heap_length_le_size :
    forall Spl addr t vl,
      lookup_at_addr addr t Spl = Some vl ->
      length vl = sizeof t.
  Proof.
    intros Spl addr t vl. 
    unfold lookup_at_addr.
    destruct (valid_access_dec Spl addr t) as [ (vl' & Hlu & Hsize) |  ].
    - destruct (Spl !!h addr.1) eqn:E ; simpl.
      * injection Hlu ; intros -> [=<-].
        rewrite length_take, length_drop. lia.
      * intros [=].
    - intros [=].
  Qed.

  Lemma state_concr_implies_val_concr : 
    forall S Spl sp v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      exists addr t vl,
        addr_spath_equiv S addr t sp /\ concr_hlpl_val v t vl /\ Spl.h.[addr : t] = Some vl.
  Proof.
    induction sp using ListBackInd.state_path_back_ind ;
      intros v Hconcr Hvspn HSx ;
    pose proof Hconcr as [Hconcr_heap Hconcr_env].
    remember (blockof enc_x).1 as bi. remember (blockof enc_x).2 as t.
    assert (Heqbit : blockof enc_x = (bi, t))
      by (subst ; rewrite <- surjective_pairing ; reflexivity).
    - specialize (Hconcr_heap enc_x bi t v Hvspn HSx Heqbit).
      destruct Hconcr_heap as [vl [Hconcr_val Hheap] ].
      assert (Hequiv : addr_spath_equiv S (bi, 0) t (enc_x, []))
      by (eapply Addr_spath_base ; eauto ; eapply Offset_vpath_base). 
      exists (bi, 0), t, vl. repeat split ; auto.
      unfold lookup_at_addr ; simpl.
      assert (Hva: valid_access Spl (bi, 0) t) by
      (eapply addr_spath_equiv_implies_valid_access ; eauto).
      destruct (valid_access_dec Spl (bi, 0) t) ; try contradiction.
      replace (heap Spl !! bi) with (Some vl) ; simpl. f_equal.
      by rewrite drop_0, (val_concr_implies_correct_type_size v t vl), firstn_all.
    - rewrite sget_app in HSx. 
      apply valid_spath_app in Hvspn as Htemp ; destruct Htemp as (Hvsp & Hvvp).
      destruct (S.[sp]) eqn:E ; discriminate_val_from_valid_spath S sp.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t sp ∧
                     concr_hlpl_val (loc ((l), (y))) t vl /\
                     lookup_at_addr addr t Spl = Some vl) by auto.
        destruct H as [addr [t [vl [ Hequiv [Hconcr_val Hval_heap] ] ] ] ].
        destruct n ; simpl in HSx.
        * exists addr, t, vl. repeat split ; auto.

          ** inversion Hequiv ; subst.
             eapply Addr_spath_loc ; eauto. rewrite E ; auto.
          ** inversion Hconcr_val ; subst ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2. congruence.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr_spath_equiv S addr t sp ∧
                     concr_hlpl_val (HLPL_pair y1 y2) t vl /\
                     lookup_at_addr addr t Spl = Some vl) by auto.
        destruct H as [addr [t [vl [Hequiv [Hconcr_val Hval_heap] ] ] ] ].
        inversion Hconcr_val ; subst v0 v1 t vl.
        apply concr_val_size in H4 as Hsize_t0, H5 as Hsize_t1.
        apply lookup_heap_pair in Hval_heap as [Hval_t0 Hval_t1] ; auto.
        destruct n as [ | [ | ] ] ; simpl in *.

        * exists addr, t0, vl0. repeat split ; try congruence ; auto.
          eapply Addr_spath_pair_first ; eauto. rewrite E ; auto.
        * exists (addr +o sizeof t0), t1, vl1 ; repeat split ; try congruence ; auto.
          eapply Addr_spath_pair_second; eauto. rewrite E ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2. congruence.
  Qed.

  Lemma state_concr_implies_val_concr_at_addr : 
    forall S Spl sp addr t v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      addr_spath_equiv S addr t sp ->
      exists vl,
         concr_hlpl_val v t vl /\ lookup_at_addr addr t Spl = Some vl.
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

  Lemma le_heap_preserves_valid_access :
    forall S1 S2 addr t,
      le_heap (heap S1) (heap S2) ->
      valid_access S1 addr t <-> valid_access S2 addr t.
  Proof.
    intros S1 S2 addr t [Hdom Hle_heap]. split ; intros (b & Haddr & Hsize).
    - destruct (Hle_heap addr.1 b Haddr) as (b2 & Haddr2 & Hle2).
      apply Forall2_length in Hle2. exists b2 ; split ; auto ; lia.
    - assert (Hb1 : exists b1, S1 !!h addr.1 = Some b1).
      {apply elem_of_dom. rewrite Hdom. apply elem_of_dom. exists b ; auto.}
      destruct Hb1 as [b1 Haddr1].
      destruct (Hle_heap addr.1 b1 Haddr1) as (b' & Haddr' & Hsize'%Forall2_length).
      exists b1 ; split ; auto. replace (S2 !!h addr.1) with (Some b') in Haddr.
      congruence.
  Qed.

  Lemma le_heap_implies_lookup_equiv :
    forall S1 S2 addr t,
      le_heap (heap S1) (heap S2) ->
      (exists vl1, S1.h.[ addr : t ] = Some vl1) <->
      (exists vl2, S2.h.[ addr : t ] = Some vl2).
  Proof.
    intros S1 S2 addr t [Hdom Hle_heap] ; split ;
      intros (vl & Hlu).
    - unfold lookup_at_addr in *.
      destruct (valid_access_dec S1 addr t) as [(b1 & Hb1 & Hsize1) | ].
      + destruct (Hle_heap addr.1 b1 Hb1) as (b2 & Hb2 & Hle2).
        destruct (valid_access_dec S2 addr t).
        * exists (take (sizeof t) (drop addr.2 b2)).
          by replace (S2 !!h addr.1) with (Some b2).
        * apply Forall2_length in Hle2. rewrite Hle2 in Hsize1.
          assert (contra : valid_access S2 addr t) by (exists b2 ; auto). contradiction.
      + congruence.
    - unfold lookup_at_addr in *.
      destruct (valid_access_dec S1 addr t) as [(b1 & Hb1 & Hsize1) | ].
      + destruct (Hle_heap addr.1 b1 Hb1) as (b2 & Hb2 & Hle2).
        destruct (valid_access_dec S2 addr t).
        * exists (take (sizeof t) (drop addr.2 b1)).
          by replace (S1 !!h addr.1) with (Some b1).
        * apply Forall2_length in Hle2. rewrite Hle2 in Hsize1.
          assert (contra : valid_access S2 addr t) by (exists b2 ; auto). contradiction.
       + destruct (valid_access_dec S2 addr t).
         * eapply le_heap_preserves_valid_access with (S1 := S1) in v ; easy.
         * congruence.
  Qed.

  Lemma le_heap_lookup_implies_lookup_l :
    forall S1 S2 addr t vl1,
      le_heap (heap S1) (heap S2) ->
      S1.h.[ addr : t ] = Some vl1 ->
      exists vl2, S2.h.[ addr : t ] = Some vl2.
  Proof.
    intros S1 S2 addr t vl1 Hle_heap Hread.
    apply ex_intro with (x := vl1) in Hread.
    apply le_heap_implies_lookup_equiv with (S2 := S2) in Hread ; auto.
  Qed.

  Lemma le_heap_lookup_implies_lookup_r :
    forall S1 S2 addr t vl2,
      le_heap (heap S1) (heap S2) ->
      S2.h.[ addr : t ] = Some vl2 ->
      exists vl1, S1.h.[ addr : t ] = Some vl1.
  Proof.
    intros S1 S2 addr t vl1 Hle_heap Hread.
    apply ex_intro with (x := vl1) in Hread.
    apply le_heap_implies_lookup_equiv with (S1 := S1) in Hread ; auto.
  Qed.

      
  Lemma le_heap_implies_le_block_at_addr :
    forall S1 S2 addr t vl1 vl2,
      le_heap (heap S1) (heap S2) ->
      S1.h.[ addr : t ] = Some vl1 ->
      S2.h.[ addr : t ] = Some vl2 ->
      le_block vl1 vl2.
  Proof.
    intros S1 S2 addr t vl1 vl2 [Hdom Hle_heap] H1 H2.
    unfold lookup_at_addr in *. 
    destruct (valid_access_dec S1 addr t) as [(vl1' & Hheap1 & Hsize1) | ].
    - rewrite Hheap1 in * ; simpl in *.
      destruct (valid_access_dec S2 addr t) as [(vl2' & Hheap2 & Hsize2) | ].
      * rewrite Hheap2 in * ; simpl in *.
        injection H1 as H1 ; injection H2 as H2 ; subst. 
        apply Forall2_take, Forall2_drop.
        destruct (Hle_heap _ _ Hheap1) as (vl2 & Hheap2' & Hle_block).
        by replace (S2 !!h addr.1) with (Some vl2) in Hheap2 ; injection Hheap2 as ->.
      * congruence.
    - congruence.
  Qed.

  Lemma le_heap_implies_le_block :
    forall S1 S2 bi b1 b2,
      le_heap (heap S1) (heap S2) ->
      S1 !!h bi = Some b1 ->
      S2 !!h bi = Some b2 ->
      le_block b1 b2.
  Proof.
    intros S1 S2 bi b1 b2 [_ Hbi] Hb1 Hb2.
    destruct (Hbi bi b1 Hb1) as [b2' [Heq Hle ] ].
    rewrite Hb2 in Heq. congruence.
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
                      lookup_at_addr addr t Spl' = Some vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & Hlu_addr). inversion Hconcr_val ; subst.
      assert (Hvsp' : valid_spath S sp') by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp : ∃ (addr : address) (t : type) (vl : pl_val),
                 addr_spath_equiv S addr t sp' ∧
                   concr_hlpl_val (HLPL_loc l h) t vl ∧
                   lookup_at_addr addr t Spl' = Some vl).
      { apply state_concr_implies_val_concr ; auto. }.
      destruct Htemp as (addr' & t' & vl & Hequiv' & Hconcr_val' & Hlu_addr').
      exists addr', t' ; split ; auto.
      constructor.
      pose proof (Hcorr_addrof _ _ _ _ Hequiv' H0).
      rewrite Haddr in H1 ; injection H1 ; intros ; subst ; clear H1.
      apply ex_intro with (x := [PL_address addr' t']) in Hlu_addr as Hex.
      eapply le_heap_implies_lookup_equiv in Hex ; eauto. destruct Hex as (vl1 & Hlu).
      pose proof (le_heap_implies_le_block_at_addr _ _ _ _ _ _ Hheap Hlu Hlu_addr).
      by inversion H1 ; inversion H6 ; inversion H5 ; subst.
    - nodes_to_val.
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_pair h1 h2) t vl ∧
                      lookup_at_addr addr t Spl' = Some vl).
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
                      lookup_at_addr addr t Spl' = Some vl).
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
    destruct Hplace as [Hvsp Hpath]. simpl in *.
    destruct (blockof (encode_var p.1)) as [bi t0] eqn:Hbo.
    assert (Hsimul_path_pl : exists addr t,
               eval_path_pl Spl p.2 ((bi, 0), t0) (addr, t) /\
                 addr_spath_equiv S addr t sp).
    { eapply spath_address_path_simul ; eauto.
      eapply Addr_spath_base ; eauto. econstructor. } 
    destruct Hsimul_path_pl as (addr & t' & Hplace_pl & Hequiv').
    apply addr_spath_equiv_eval_type in Heval_type as (addr' & Hequiv).
    apply (addr_spath_equiv_deterministic _ _ _ _ _ _ Hequiv) in Hequiv'
        as (Heq_addr & Heq_type); subst.
    exists addr ; split ; auto.
    exists bi, t0 ; split ; auto.
    unfold lookup_block_and_type_env.
    rewrite Henv. eapply Hconcr_env ; eauto.
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

  Lemma read_write_at_addr:
    forall Spl addr t vl,
      Spl.h.[ addr : t ] = Some vl ->
      (Spl.h.[ addr <- vl : t ]).h.[ addr : t ] = Some vl.
  Proof.
    intros Spl (bi, off) t vl Haddr.
    unfold lookup_at_addr, write_at_addr in *. simpl in *.
    destruct (valid_access_dec Spl (bi, off) t) as [ (b & Hb & Hsize) | ] ;
      try congruence. simpl in *. rewrite Hb in Haddr ; injection Haddr as <-.
    assert (H: length (take (sizeof t) (drop off b)) = sizeof t) by 
      (rewrite length_take, length_drop ; lia).
    assert (H' : take off b ++ take (sizeof t) (drop off b) ++
                   drop (off + sizeof t) b = b)
      by (rewrite app_assoc, take_take_drop, take_drop ; auto).
    assert (Hva : valid_access (update_heap Spl
         (alter
            (λ block : list PL_val,
               take off block ++
               take (sizeof t) (drop off b) ++
               drop (off + length (take (sizeof t) (drop off b))) block)
            bi (heap Spl))) (bi, off) t).
    {
      eexists ; split ; eauto ; simpl. rewrite lookup_alter.
      replace (Spl !!h bi) with (Some b) ; simpl. f_equal. by rewrite H, H'.
    }
    is_valid_access (update_heap Spl
         (alter
            (λ block : list PL_val,
               take off block ++
               take (sizeof t) (drop off b) ++
               drop (off + length (take (sizeof t) (drop off b))) block)
            bi (heap Spl))) (bi, off) t.
    rewrite lookup_alter. replace (Spl !!h bi) with (Some b). simpl. f_equal.
    by rewrite H, H'.
  Qed.

  Lemma write_read_at_addr:
    forall Spl addr t vl,
      Spl.h.[ addr : t ] = Some vl ->
      (Spl.h.[ addr <- vl : t ]) = Spl.
  Proof.
    intros Spl [bi off] t vl Hread.
    unfold write_at_addr. unfold lookup_at_addr in *. simpl in *.
    destruct (valid_access_dec Spl (bi, off) t) as [ (b & Hb & Hsize) | ] ;
      try easy ; simpl in * ; rewrite Hb in Hread ; injection Hread as .
    assert (Hvl : take off b ++ vl ++ drop (off + length vl) b = b).
    {
      assert (Hlen : length (take (sizeof t) (drop off b)) = sizeof t) by
        (rewrite length_take, length_drop ; lia).
      by rewrite <- H, app_assoc, take_take_drop, Hlen, take_drop.
    }
    rewrite <- insert_id with (i := bi) (x := b) (m := (heap Spl)),
        alter_insert, Hvl, insert_id ; auto. destruct Spl ; reflexivity.
  Qed.
  
  Lemma get_block_write_at_addr_ne:
    forall Spl addr bi t vl,
      addr.1 <> bi ->
      (Spl.h.[ addr <- vl : t ]) !!h bi = Spl !!h bi.
  Proof.
    intros [e h] (bi, off) bi' t vl Heq.
    unfold write_at_addr. simpl in *. rewrite lookup_alter_ne ; auto.
  Qed.

  Lemma le_pl_write_at_addr :
    forall Spl1 Spl2 addr t vl vl',
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state (Spl1.h.[ addr <- vl : t ]) (Spl2.h.[ addr <- vl' : t ]).
  Proof.
    intros Spl1 Spl2 addr t vl vl' [Hle_env Hle_heap ] Hle_block.
    assert (Hdom :
             dom (heap (Spl1.h.[ addr <- vl : t ])) =
               dom (heap (Spl2.h.[ addr <- vl' : t ])))
      by (apply dom_stable_by_write_at_addr, (proj1 Hle_heap)).
    split.
    - by repeat rewrite env_stable_by_write_at_addr.
    - split ; auto.
      intros bi b1 Hbi.
      apply elem_of_dom_2 in Hbi as Hbi2.
      rewrite Hdom in Hbi2. apply elem_of_dom in Hbi2. destruct Hbi2 as [b2 Hbi2].
      destruct (Positive_as_DT.eqb_spec bi addr.1).
      + exists b2 ; split ; auto.
        destruct addr as [bi' off].
        unfold write_at_addr, update_heap in Hbi, Hbi2. simpl in Hbi, Hbi2.
        simpl in e ; subst bi'. rewrite lookup_alter in Hbi, Hbi2.
        rewrite <- (Forall2_length _ _ _ Hle_block) in *.
        destruct (Spl1 !!h bi) as [ b1' | ] eqn:Hbi'.
        * apply elem_of_dom_2 in Hbi' as Hbi2' ; rewrite (proj1 Hle_heap) in Hbi2'.
          apply elem_of_dom in Hbi2'. destruct Hbi2' as [b2' Hbi2'].
          rewrite Hbi2' in Hbi2. simpl in Hbi, Hbi2.
          injection Hbi as Hbi ; injection Hbi2 as Hbi2 ; subst.
          assert (Hle_block' : le_block b1' b2')
            by (eapply le_heap_implies_le_block ; eauto).
          apply Forall2_length in Hle_block as Hlen, Hle_block' as Hlen'.
          repeat (try (apply Forall2_app) ; try (apply Forall2_take)
                  ; try (apply Forall2_drop)) ;
            try reflexivity ; auto.
        * simpl in Hbi ; congruence.
      + rewrite get_block_write_at_addr_ne in Hbi ; auto.
        destruct ((proj2 Hle_heap) bi b1 Hbi) as [b2' [Hbi2' Hle] ].
        exists b2 ; split; auto.
        rewrite get_block_write_at_addr_ne in Hbi2 ; auto. 
        replace (Spl2 !!h bi) with (Some b2) in Hbi2'. congruence.
  Qed.

  Lemma le_pl_write_at_addr_r :
    forall Spl1 Spl2 addr t vl vl',
      Spl1.h.[ addr : t ] = Some vl ->
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state Spl1 (Spl2.h.[ addr <- vl' : t ]).
  Proof.
    intros Spl1 Spl2 addr t vl vl' Hread Hle_pl Hle_block.
    erewrite <- write_read_at_addr with (Spl := Spl1) ; eauto.
    by apply le_pl_write_at_addr ; auto.
  Qed.

  Lemma le_pl_write_at_addr_l :
    forall Spl1 Spl2 addr t vl vl',
      Spl2.h.[ addr : t ] = Some vl' ->
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state (Spl1.h.[ addr <- vl : t ]) Spl2.
  Proof.
    intros Spl1 Spl2 addr t vl Hsize Hle_pl Hle_block.
    erewrite <- write_read_at_addr with (Spl := Spl2) ; eauto.
    apply le_pl_write_at_addr ; auto.
  Qed.

  Lemma concr_val_off_vpath_equiv_equiv :
    forall vi ti vli,
      length vli = sizeof ti ->
      (concr_hlpl_val vi ti vli <->
         forall off vp t,
           off_vpath_equiv vi ti off t vp ->
           concr_hlpl_val (vi.[[ vp ]]) t (take (sizeof t) (drop off vli))).
  Proof.
    intros. split ; intros.
    {
      apply concr_val_size in H0 as Hleni. induction H1 ; nodes_to_val.
      - simpl ; by rewrite drop_0, Hleni, firstn_all.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. simpl.
        apply concr_val_size in H6 as Hlen0.
        apply f_equal with (f := (take (sizeof t0))) in H8.
        rewrite Hlen0, take_app_length, take_take in H8.
        replace (length vl0 `min` _ ) with (length vl0) in H8 by lia.
        congruence.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. simpl.
        apply concr_val_size in H6 as Hlen0. apply concr_val_size in H9 as Hlen1.
        apply f_equal with (f := (drop (sizeof t0))) in H8.
        rewrite Hlen0, drop_app_length, <- Hlen0, <- take_drop_commute, drop_drop in H8.
        congruence.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. by simpl.
    }
    {
      assert (off_vpath_equiv vi ti 0 ti []) by constructor.
      specialize (H0 0 [] ti H1). simpl in H0.
      by rewrite drop_0, <- H, firstn_all in H0.
    }
  Qed.

  Lemma concr_val_implies_exists_concr_val_vp :
    forall vi ti t off vp vli,
      off_vpath_equiv vi ti off t vp ->
      concr_hlpl_val vi ti vli ->
      exists vl, concr_hlpl_val (vi.[[ vp ]]) t vl.
  Proof.
    intros. apply concr_val_size in H0 as Hlen. symmetry in Hlen.
    pose proof (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hlen) H0 _ _ _ H).
    eexists ; eauto.
  Qed.

  Lemma concr_val_write :
    forall vp vi v ti t vli vl off,
      off_vpath_equiv vi ti off t vp ->
      concr_hlpl_val vi ti vli ->
      concr_hlpl_val v t vl ->
      concr_hlpl_val
        (vi.[[ vp <- v ]]) ti (take off vli ++ vl ++ drop (off + sizeof t) vli).
  Proof.
    intros. apply concr_val_size in H0 as Hleni. symmetry in Hleni.
    generalize dependent v. generalize dependent vl. induction H ; intros vl v Hconcr.
    - simpl. by rewrite <- Hleni, drop_all, app_nil_r.
    - nodes_to_val.
      assert (off_vpath_equiv vi ti (off + sizeof t0) t1 (vp ++ [1]))
        by (eapply Offset_vpath_pair_second ; eauto).
      eapply (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hleni)) in H0 as G; eauto.
      rewrite vget_app, Heqh in G. simpl in G.
      remember (take (sizeof t1) (drop (off + sizeof t0) vli)) as vl1.
      assert (concr_hlpl_val (HLPL_pair v h2) (TPair t0 t1) (vl ++ vl1))
        by (eapply Concr_pair ; eauto).
      rewrite vset_app_split, Heqh. simpl.
      specialize (IHoff_vpath_equiv _ _ H3). rewrite Heqvl1 in IHoff_vpath_equiv.
      rewrite <- !app_assoc in IHoff_vpath_equiv. simpl in *.
      by rewrite <- (take_drop (sizeof t1) (drop _ _)), drop_drop, <- Nat.add_assoc.
    - nodes_to_val. simpl in *.
      assert (off_vpath_equiv vi ti off t0 (vp ++ [0]))
        by (eapply Offset_vpath_pair_first ; eauto).
      eapply (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hleni)) in H0 as G; eauto.
      rewrite vget_app, Heqh in G. simpl in G.
      remember (take (sizeof t0) (drop off vli)) as vl0.
      assert (concr_hlpl_val (HLPL_pair h1 v) (TPair t0 t1) (vl0 ++ vl)).
        by (eapply Concr_pair ; eauto).
      rewrite vset_app_split, Heqh. simpl.
      specialize (IHoff_vpath_equiv _ _ H3). rewrite Heqvl0 in IHoff_vpath_equiv.
      by rewrite !app_assoc, take_take_drop, <- !app_assoc, Nat.add_assoc
        in IHoff_vpath_equiv.
    - nodes_to_val. simpl in *. rewrite vset_app_split, Heqh. simpl.
      assert (concr_hlpl_val (loc (l, v)) t' vl) by (apply Concr_loc ; auto).
      by specialize (IHoff_vpath_equiv _ _ H2).
  Qed.

  Lemma concr_state_write_at_addr :
    forall S Spl sp addr v t vl,
      concr_hlpl S Spl ->
      concr_hlpl_val v t vl ->
      addr_spath_equiv S  addr t sp ->
      concr_hlpl (S.[sp <- v] ) (Spl.h.[addr <- vl : t]).
  Proof.
    intros S Spl sp (bi, off) v t vl [Hconcr_heap Hconcr_env] Hconcr_val Hequiv.
    split.
    - intros enc_x bi' t' v' Hvsp HSx Hbo'.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      destruct (addr_spath_equiv_var_bi _ _ _ _ Hequiv) as (t0 & Hbo). cbn in Hbo.
      destruct (Pos.eqb_spec bi bi').
      * pose proof e as e'. rewrite <- blockof_inj in e ; eauto. subst.
        pose proof Hequiv as Htemp.
        apply addr_spath_equiv_implies_valid_access with (Spl := Spl) in Htemp
            as [vl' [ Hbi' Hsize' ] ]; try easy ; simpl in Hbi', Hsize'.
         apply concr_val_size in Hconcr_val as Hval_size.
        exists (firstn off vl' ++ vl ++ skipn (off + sizeof t) vl') ; repeat split ; auto.
      + destruct (Hconcr_heap sp.1 bi' t' (S .[ (sp.1, [])]) Hvsp eq_refl Hbo')
                   as (vl'' & Hconcr_val' & Hbi'').
        replace (Spl !!h bi') with (Some vl') in Hbi'' ; injection Hbi'' as ->.
        replace sp with ((sp.1, []) +++ sp.2) by
          (unfold "+++" ; rewrite surjective_pairing with (p := sp) ; by simpl).
        rewrite sset_sget_prefix ; auto.
        apply concr_val_write; auto. inversion Hequiv ; subst ; simpl in *.
        by replace t' with tinit by congruence.
      + unfold write_at_addr. simpl. rewrite lookup_alter.
        replace (Spl !!h bi') with (Some vl'). simpl. congruence.
      * unfold write_at_addr ; simpl ; rewrite lookup_alter_ne ; auto.
        rewrite <- blockof_inj_inv in n ; eauto.
        rewrite sset_sget_disj in HSx ; auto ; try (left ; auto).
        eapply Hconcr_heap ; eauto.
    - intros enc_x bi' t0 Hvsp Hbo. rewrite env_stable_by_write_at_addr.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      by specialize (Hconcr_env enc_x bi' t0 Hvsp Hbo).
  Qed.

End Concretization.

Definition WellTypedOperand S bo op :=
  match op with
  | IntConst t _ => t = TInt
  | Move t p =>
      forall perm sp,
      eval_place S perm p sp ->
      eval_type bo S sp t
  | Copy t p =>
      forall perm sp,
      eval_place S perm p sp ->
      eval_type bo S sp t
  end.

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
  apply ex_intro with (x := vl) in Hlu as Hlu'.
  apply le_heap_implies_lookup_equiv with (S1 := Spl) in Hlu' as [vl' Hlu'] ; auto.
  exists vl', vl ;
    repeat split ; try assumption.
  * eapply Read ; eauto.
  * eapply le_heap_implies_le_block_at_addr ; eauto.
Qed.

(** TODO : change place *)
Lemma prefix_bot_is_bot' :
  forall S p r,
    S.[p] = bot -> S.[p +++ r] = bot.
Proof.
  intros S p r Hbot. induction r using ListBackInd.list_back_ind.
  - by rewrite app_spath_vpath_nil_r.
  - rewrite app_spath_vpath_assoc, sget_app, IHr. simpl. by rewrite nth_error_nil.
Qed.

Lemma prefix_bot_is_bot :
  forall S p q,
    prefix p q -> S.[p] = bot -> S.[q] = bot.
Proof.
  intros S p q [r Heq] Hbot. rewrite <- Heq. by apply prefix_bot_is_bot'.
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
  - intros x enc_x Hvar Hbot. destruct (Positive_as_DT.eqb_spec sp.1 enc_x).
    * eapply Hblock ; eauto. intros contra.
      eapply prefix_bot_is_bot in contra.
      ** erewrite contra in Hnot_bot_sp.
      specialize (Hnot_bot_sp [] (valid_nil bot)). simpl in Hnot_bot_sp. auto.
      ** exists sp.2. unfold "+++". rewrite <- e, surjective_pairing with (p := sp). auto.
    * eapply Hblock ; eauto.
      rewrite sset_sget_disj in Hbot ; try constructor ; auto.
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
    WellTypedOperand S blockof op ->
    S |-{op} op => vS1 ->
    exists blockof1 addrof1 vl vl' t,
      Spl |-{op-pl} op => vl /\
      le_pl_hlpl blockof1 addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl' /\
      le_block vl vl'.
Proof.
  intros bo ao S Spl op vS1 Hle HWTO Heval.
  pose proof Hle as Htemp ;
    destruct Htemp as (Spl' & HComp & Hconcr & (Hle_env & Hle_heap)).
  pose proof proj1 Hconcr as Hconcr_heap.
  pose proof proj2 Hconcr as Hconcr_env.
  induction Heval eqn:E.
  - exists bo, ao, [PL_int n], [PL_int n], TInt. repeat split ; try constructor ; auto.
    econstructor.
  - specialize (HWTO _ _ Heval_place).
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ _ Hle Heval_place HWTO eq_refl)
    as (vl & vl' & Hread & Hconcr_val & Hle_val).
    exists bo, ao, vl, vl', t ; repeat split ; simpl ; auto.
    * constructor ; auto.
    * by apply (concr_val_equiv_concr_copy_val ao _ _ _ _ Hcopy_val).
  - specialize (HWTO _ _ e).
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ _ Hle e HWTO eq_refl)
    as (vl & vl' & Hread & Hconcr_val & Hle_block).
    exists bo, ao, vl, vl', t ; repeat split ; auto.
    * constructor ; auto.
    * inversion Hread.
      exists (write_at_addr addr t (repeat PL_poison (sizeof t)) Spl').
         rewrite snd_pair. split ; [ idtac | split ] ; auto.
      + apply sset_preserves_compatibility ; auto. 
        ++ unfold not_contains_loc. not_contains.
      + apply concr_state_write_at_addr ; auto ; [ by apply Concr_bot | idtac ].
        eapply read_addr_spath_equiv_equiv ; eauto.
      + etransitivity ; eauto.
        eapply le_pl_write_at_addr_r ; eauto ; try reflexivity.
        eapply le_pl_write_at_addr ; try constructor ; eauto .
        apply le_block_poison. apply Forall2_length in Hle_block.
        apply lookup_heap_size in Hlu. congruence.
Qed.
        

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
