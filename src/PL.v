Require Import lang.
Require Import base.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Relations.
From Stdlib Require Import Program.
Require Import Stdlib.Logic.ProofIrrelevance.
Require ListBackInd.
Require Setoid.
From stdpp Require list_basics.
Module LB := list_basics.
Module LR := list_relations.

From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree.
Require Import HLPL_No_Anon.

Opaque sset.

Definition block_id := positive.
Definition offset := nat.
Definition address := (block_id * offset)%type.

Inductive PL_val :=
| PL_poison : PL_val
| PL_int_frag : nat -> nat -> PL_val 
| PL_address_frag : address -> nat -> PL_val
.

Definition make_int64 (n : nat) :=
  map (fun i => PL_int_frag n i) (seq 0 8).

Definition make_ptr64 (addr : address) :=
  map (fun i => PL_address_frag addr i) (seq 0 8).

Lemma make_int64_not_contain_poison :
  forall n, ~ In PL_poison (make_int64 n).
Proof. intros n H. simpl in H. repeat (destruct H ; try discriminate). Qed.

Lemma make_ptr64_not_contain_poison :
  forall addr, ~ In PL_poison (make_ptr64 addr).
Proof. intros addr H. simpl in H. repeat (destruct H ; try discriminate). Qed.

Definition pl_val := list PL_val.

Record PL_state : Type := Build_PL_state {
  env : Pmap (block_id * type);
  mem : Pmap pl_val;
  nextblock : block_id;
  nextblock_no_access :
    forall bi, Pos.le nextblock bi -> lookup bi mem = None
}.

Lemma PL_state_extensionality:
  forall e1 e2 m1 m2 nb1 nb2 p1 p2,
    e1 = e2 -> m1 = m2 -> nb1 = nb2 ->
    Build_PL_state e1 m1 nb1 p1 = Build_PL_state e2 m2 nb2 p2.
Proof.
  intros ; subst ; f_equal ; apply proof_irrelevance.
Qed.

Fixpoint sizeof (tau : type) : nat :=
  match tau with
  | TInt | TRef _ => 8
  | TPair tau1 tau2 => sizeof tau1 + sizeof tau2
  end.

Lemma sizeof_ge_1 : forall tau, sizeof tau >= 1.
Proof. induction tau ; simpl ; lia. Qed.

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
| Copy_val_int (n i : nat) : copy_val (PL_int_frag n i) (PL_int_frag n i).

(* Functions to lookup and update PL states *)
Definition update_env (S : PL_state) (e : Pmap (block_id * type)) :=
  {| env := e ; mem := mem S ;
     nextblock := nextblock S ; nextblock_no_access := nextblock_no_access S |}.

Definition update_mem (S : PL_state) (m : Pmap pl_val)
  (P : forall bi, Pos.le (nextblock S) bi -> lookup bi m = None) :=
  {| env := env S ; mem := m ;
     nextblock := nextblock S ; nextblock_no_access := P |}.

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

Notation "Spl !!h bi" := (lookup bi (mem Spl)) (at level 40).
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

Ltac is_valid_access S addr t := match goal with
  | H : valid_access S addr t |- _ =>
      destruct (valid_access_dec S addr t) as [_H | ] ;
      [ clear _H | contradiction ]
  end.

Lemma alter_mem_preserves_nextblock1 :
  forall (m : Pmap pl_val) f i nextblock,
    (forall bi, Pos.le nextblock bi -> lookup bi m = None) ->
    forall bi, Pos.le nextblock bi -> lookup bi (alter f i m) = None.
Proof.
  intros * nextblock_no_access bi le.
  apply not_elem_of_dom. rewrite dom_alter. apply not_elem_of_dom. auto.
Qed.

Lemma loadbytes_elim :
  forall m b ofs n bytes,
    Mem.loadbytes m b ofs n = Some bytes ->
    Mem.range_perm m b ofs (ofs + n) Cur Readable /\
      bytes = Mem.getN (Z.to_nat n) ofs (Mem.mem_contents m) # b.
Proof.
  intros * load.
  Transparent Mem.loadbytes. unfold Mem.loadbytes in load. Opaque Mem.loadbytes.
  destruct (Mem.range_perm_dec m b ofs (ofs + n) Cur Readable) ; try discriminate.
  split ; auto. congruence.
Qed.

Notation "S .m.[ addr : t ]" := (Mem.loadbytes (mem S) addr.1 addr.2 (sizeof t))
                                  (at level 50, addr at next level).

Notation "S .m.[ addr <- vl : t ]" := (write_at_addr addr t vl S)
                                       (vl at next level).

Lemma read_write_at_addr:
  forall Spl addr t vl,
    Spl.m.[ addr : t ] = Some vl ->
    (Spl.m.[ addr <- vl : t ]).m.[ addr : t ] = Some vl.
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
  assert (Hva : valid_access
                  (update_mem Spl
                     (alter
                        (λ block : list PL_val,
                            take off block ++
                              take (sizeof t) (drop off b) ++
                              drop (off + length (take (sizeof t) (drop off b))) block)
                        bi (mem Spl))
                     (alter_mem_preserves_nextblock1 _ _ _ _ (nextblock_no_access Spl))
                  ) (bi, off) t).
  {
    eexists ; split ; eauto ; simpl. rewrite lookup_alter.
    replace (Spl !!h bi) with (Some b) ; simpl. f_equal. by rewrite H, H'.
  }
  is_valid_access
    (update_mem Spl
       (alter
          (λ block : list PL_val,
              take off block ++
                take (sizeof t) (drop off b) ++
                drop (off + length (take (sizeof t) (drop off b))) block)
          bi (mem Spl))
       (alter_mem_preserves_nextblock1 _ _ _ _ (nextblock_no_access Spl))
    ) (bi, off) t.
  rewrite lookup_alter. replace (Spl !!h bi) with (Some b). simpl. f_equal.
  by rewrite H, H'.
Qed.

Lemma env_stable_by_write_at_addr :
  forall S addr t vl, env (S.m.[addr <- vl : t]) = env S.
Proof.
  intros [env_S mem_S] [bi off] vl ?. reflexivity.
Qed.

Lemma dom_stable_by_write_at_addr :
  forall S1 S2 addr t1 t2 vl1 vl2,
    dom (mem S1) = dom (mem S2) ->
    dom (mem (S1.m.[addr <- vl1 : t1])) = dom (mem (S2.m.[addr <- vl2 : t2 ])).
Proof.
  intros [e1 h1] [e2 h2] [bi off] t1 t2 vl1 vl2 Heq. 
  unfold write_at_addr. simpl in *. by repeat rewrite dom_alter_L.
Qed.

Lemma mem_access_stable_by_write_at_addr :
  forall S addr t bytes,
    Mem.mem_access (mem S) = Mem.mem_access (mem (S.m.[addr <- bytes: t])).
Proof.
  intros *. unfold Mem.mem_access. simpl. unfold storebytes.
  destruct ((sizeof t =? Datatypes.length bytes)%nat) ;
    destruct (Mem.storebytes (mem S) addr.1 addr.2 bytes) eqn:E ; auto.
  eapply Mem.storebytes_access in E ; eauto.
Qed.

Lemma nextblock_stable_by_write_at_addr :
  forall S addr t bytes,
    Mem.nextblock (mem S) = Mem.nextblock (mem (S.m.[addr <- bytes: t])).
Proof.
  intros *. unfold Mem.nextblock. simpl. unfold storebytes.
  destruct ((sizeof t =? Datatypes.length bytes)%nat) ;
    destruct (Mem.storebytes (mem S) addr.1 addr.2 bytes) eqn:E ; auto.
  eapply Mem.nextblock_storebytes in E ; eauto.
Qed.

(** Evaluating projections as addresses *)

Inductive eval_proj (Spl : PL_state) :
  proj -> (address * type) -> (address * type) -> Prop :=
| Eval_Deref_Ptr_Locs :
  forall (addr addr' : address) (t: type),
    Spl.m.[addr : TRef t] = Some (make_ptr64 addr') ->
    eval_proj Spl Deref (addr, TRef t) (addr', t)
| Eval_Field_First :
  forall (addr : address) (t0 t1 : type),
    eval_proj Spl (Field First) (addr, TPair t0 t1) (addr, t0)
| Eval_Field_Second :
  forall (addr : address) (t0 t1 : type),
    eval_proj Spl (Field Second) (addr, TPair t0 t1) (addr +o sizeof t0, t1).

Inductive eval_path (Spl : PL_state) : path -> address * type -> address * type -> Prop :=
| Eval_nil_addr : forall addr, eval_path Spl [] addr addr
| Eval_cons : forall proj P addr_t addr_t' addr_t'',
    eval_proj Spl proj addr_t addr_t' ->
    eval_path Spl P addr_t' addr_t'' ->
    eval_path Spl (proj :: P) addr_t addr_t''.

Definition eval_place (Spl : PL_state) (p : place) (addr_t : address * type) : Prop :=
  exists bi t,
    lookup_block_and_type_env (encode_var p.1) Spl = Some (bi, t) /\
      eval_path Spl p.2 ((bi, 0), t) addr_t.

Notation "Spl  |-{p}  p =>^{pl} addr_t" := (eval_place Spl p addr_t) (at level 50).

Lemma eval_proj_deterministic :
  forall Spl proj addr_t0 addr_t1 addr_t2,
    eval_proj Spl proj addr_t0 addr_t1 ->
    eval_proj Spl proj addr_t0 addr_t2 ->
    addr_t1 = addr_t2.
Proof.
  intros Spl proj ? ? ? Heval_proj1 Heval_proj2.
  destruct proj ; inversion Heval_proj1 ; subst ; inversion Heval_proj2; subst ; auto.
  rewrite H in H2. injection H2 ; intros ; subst ; auto.
Qed.

Lemma eval_path_deterministic :
  forall Spl P addr_t0 addr_t1 addr_t2,
    eval_path Spl P addr_t0 addr_t1 ->
    eval_path Spl P addr_t0 addr_t2 ->
    addr_t1 = addr_t2.
Proof.
  intros Spl P ? ? ? Heval_path01 Heval_path12.
  induction Heval_path01 ; inversion Heval_path12 ; subst ; auto.
  pose proof (eval_proj_deterministic _ _ _ _ _ H H2) ; subst.
  apply IHHeval_path01 ; auto.
Qed.

Lemma eval_place_deterministic :
  forall Spl p addr_t addr_t',
    Spl |-{p} p =>^{pl} addr_t ->
    Spl |-{p} p =>^{pl} addr_t' ->
    addr_t = addr_t'.
Proof.
  intros Spl p addr_t addr_t'
    (bi & t & Hlu & Heval_path) (bi' & t' & Hlu' & Heval_path').
  rewrite Hlu in Hlu'. injection Hlu' ; intros ; subst.
  eapply eval_path_deterministic ; eauto.
Qed.

(** Read in PL state *)
Definition read_address (Spl : PL_state) (p : place) (t : type) (addr : address): Prop :=
    Spl |-{p} p =>^{pl} (addr, t).

Variant read (S : PL_state) (p : place) (t : type) (vl : pl_val) : Prop :=
  | Read addr 
      (Haddr : read_address S p t addr)
      (Hlu : S.m.[ addr : t] = Some vl) :
    read S p t vl.

Variant write (S : PL_state) (p : place) (t : type) (vl : pl_val)
  : PL_state -> Prop :=
  | Write addr S'
      (Haddr : read_address S p t addr)
      (Heq : S' = (S.m.[ addr <- vl : t])) :
      write S p t vl S'.

(* Evaluation of Expressions in PL *)
Reserved Notation "S  |-{op-pl}  op  =>  r" (at level 60).
Variant eval_operand : operand -> PL_state -> pl_val -> Prop :=
| Eval_IntConst S t n :
  S |-{op-pl} IntConst t n => (make_int64 n)
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
    (Hl : S |-{op-pl} op_l => (make_int64 n_l))
    (Hr : S |-{op-pl} op_r => (make_int64 n_r)) :
    S |-{rv-pl} BinOp t op_l op_r => (make_int64 (n_l + n_r))
| Eval_ptr S t p addr
    (Haddr : read_address S p t addr) :
  S |-{rv-pl} &mut p : TRef t => (make_ptr64 addr)
| Eval_pair S t op_l vl_l op_r vl_r
    (Hl : S |-{op-pl} op_l => vl_l)
    (Hr : S |-{op-pl} op_r => vl_r) :
  S |-{rv-pl} Pair t op_l op_r => (vl_l ++ vl_r)
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
      destruct (LB.app_inj_2 _ _ _ _ Hlen_one H) ;
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
  | Eval_pair_second_type_val vp t0 t1
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

  Inductive concr_hlpl_val : HLPL_val -> type -> pl_val -> Prop :=
  | Concr_lit n :
    concr_hlpl_val (HLPL_int n) TInt (make_int64 n)
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
    concr_hlpl_val (HLPL_ptr l) (TRef t) (make_ptr64 addr)
  .

  Fixpoint concr_hlpl_val_comp (v : HLPL_val) (t : type) :=
    match v, t with
    | HLPL_int n, TInt =>
        Some (make_int64 n)
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
        | Some (addr, t') =>
            if (decide (t = t')) then
              Some (make_ptr64 addr)
            else
              None
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
      destruct (addrof l) eqn:Haddr ; try discriminate.
      destruct p ; destruct (decide (t = t0)).
      * injection H as H ; subst. by constructor.
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
    - rewrite Haddr. destruct (decide (t = t)) ; auto. contradiction.
  Qed.

  Lemma concr_val_eq_concr_val_comp : forall v t vl,
      concr_hlpl_val v t vl <-> concr_hlpl_val_comp v t = Some vl.
  Proof.
    split.
    apply concr_val_implies_concr_val_comp. apply concr_val_comp_implies_concr_val.
  Qed.

  Lemma concr_val_size : forall v vl t, concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v vl t Hconcr. induction Hconcr ; auto ; try reflexivity.
    - rewrite Hs, repeat_length. reflexivity.
    - rewrite List.length_app. simpl. lia.
  Qed.

  Lemma concr_val_add_loc :
    forall v vp l t vl,
      concr_hlpl_val v t vl ->
      concr_hlpl_val (v.[[vp <- loc (l, v.[[vp]]) ]]) t vl.
  Proof.
    intros until vp. generalize dependent v. induction vp ; intros.
    - simpl. by constructor.
    - destruct v ; inversion H ; subst ; auto.
      + destruct a ; auto. simpl. constructor. auto.
      + destruct a as [ | [  | ] ] ; auto ; simpl.
        * specialize (IHvp _ l _ _ H2). constructor ; auto.
        * specialize (IHvp _ l _ _ H5). constructor ; auto.
  Qed.

  Lemma concr_val_remove_loc :
    forall v vloc vp l t vl,
      v.[[ vp ]] = loc(l, vloc) ->
      concr_hlpl_val v t vl ->
      concr_hlpl_val (v.[[vp <- v.[[ vp ++ [0] ]] ]]) t vl.
  Proof.
    intros until vp. generalize dependent v. induction vp ; intros.
    - simpl app. simpl in H. rewrite H. simpl.
      inversion H0 ; try congruence.
    - destruct v ; inversion H ; subst ; auto.
      + destruct a ; auto. simpl in *. constructor. 
        inversion H0 ; subst. eauto.
      + destruct a as [ | [  | ] ] ; auto ; simpl in * ; inversion H0 ; subst.
        * specialize (IHvp _ l t0 vl0 H2 H4). constructor ; auto.
        * specialize (IHvp _ l t1 vl1 H2 H7). constructor ; auto.
  Qed.

  Lemma concr_val_deterministic :
    forall v t vl0 vl1,
      concr_hlpl_val v t vl0 ->
      concr_hlpl_val v t vl1 ->
      vl0 = vl1.
  Proof. intros. apply concr_val_implies_concr_val_comp in H, H0. congruence. Qed.

  Definition concr_hlpl_mem (S : HLPL_state) (h : Pmap pl_val) : Prop :=
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
    concr_hlpl_mem S (mem Spl) /\ concr_hlpl_env S (env Spl).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.mem(addr) *)

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

Notation "addr ~^{ S , t } sp" := (addr_spath_equiv S addr t sp) (at level 40).

  Lemma Addr_spath_pair_first :
    forall S sp addr t0 t1,
      get_node (S.[ sp ]) = HLPL_pairC ->
      addr ~^{S, (TPair t0 t1)} sp ->
      addr ~^{S, t0} (sp +++ [0]).
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
      addr ~^{S, (TPair t0 t1)} sp ->
      (addr +o sizeof t0) ~^{S, t1} (sp +++ [1]).
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
      addr ~^{S, t} sp <->
      addr ~^{S, t} (sp +++ [0]).
  Proof.
    intros S sp addr t l Hnode. split ; intro Hequiv.
    - inversion Hequiv ; subst. econstructor ; eauto. simpl.
      eapply Offset_vpath_loc; eauto.
      rewrite <- sget_app. unfold app_spath_vpath. simpl.
      by rewrite <- surjective_pairing.
    - inversion Hequiv ; subst. simpl fst in *. simpl snd in *.
      rewrite (spath_var_app_vpath sp), sget_app in Hnode.
      inversion Hvequiv ; subst ; sp_discriminate_or_find_equalities ; try congruence.
      econstructor ; eauto.
  Qed.
      

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
    forall S sp t, (exists addr, addr ~^{S, t} sp) <-> eval_type S sp t.
  Proof.
    intros S sp t ; split ; [intros (addr & Hequiv) | intros Heval_type].
    - inversion Hequiv ; subst.
      econstructor ; eauto.
      apply off_vpath_equiv_eval_type. eexists ; eauto.
    - inversion Heval_type ; subst.
      apply off_vpath_equiv_eval_type in Heval_type0.
      destruct Heval_type0 as (off & Hvequiv).
      exists (bi, off). econstructor ; eauto.
  Qed.

  Lemma off_vpath_equiv_vset_eq :
    forall v tinit t off vp v',
      off_vpath_equiv v tinit off t vp <->
        off_vpath_equiv (v.[[ vp <- v' ]]) tinit off t vp.
  Proof.
    intros. split ; intros.
    {
      generalize dependent v'.
      induction H ; intros ; subst ; simpl.
      - constructor.
      - nodes_to_val. specialize (IHoff_vpath_equiv (HLPL_pair v' h2)).
        rewrite vset_app_split, Heqh. simpl. eapply Offset_vpath_pair_first ; eauto.
        rewrite vset_vget_equal ; auto.
        apply valid_get_node_vget_not_bot. simpl in *. intros ?. congruence.
      - nodes_to_val. specialize (IHoff_vpath_equiv (HLPL_pair h1 v')).
        rewrite vset_app_split, Heqh. simpl. eapply Offset_vpath_pair_second; eauto.
        rewrite vset_vget_equal ; auto.
        apply valid_get_node_vget_not_bot. simpl in *. intros ?. congruence.
      - nodes_to_val. specialize (IHoff_vpath_equiv (loc (l, v'))). simpl in H0.
        rewrite vset_app_split, Heqh. simpl. eapply Offset_vpath_loc ; auto.
        rewrite vset_vget_equal ; eauto.
        apply valid_get_node_vget_not_bot. simpl in *. intros ?. congruence.
    }
    {
      remember (v .[[ vp <- v']]) as vi. generalize dependent v'.
      induction H ; intros ; subst ; simpl.
      - constructor.
      - nodes_to_val.
        rewrite get_node_vset_vget_strict_prefix in H0 by (repeat econstructor).
        nodes_to_val.
        assert (v .[[ vp ++ [0] <- v']] = v .[[ vp <- HLPL_pair v' h4]]) by
          (by rewrite vset_app_split, Heqh0).
        specialize (IHoff_vpath_equiv _ H1).
        eapply Offset_vpath_pair_first ; eauto.
      - nodes_to_val.
        rewrite get_node_vset_vget_strict_prefix in H0 by (repeat econstructor).
        nodes_to_val.
        assert (v .[[ vp ++ [1] <- v']] = v .[[ vp <- HLPL_pair h3 v']]) by
          (by rewrite vset_app_split, Heqh0).
        specialize (IHoff_vpath_equiv _ H1).
        eapply Offset_vpath_pair_second ; eauto.
      - nodes_to_val.
        rewrite get_node_vset_vget_strict_prefix in H0 by (repeat econstructor).
        nodes_to_val.
        assert (v .[[ vp ++ [0] <- v']] = v .[[ vp <- loc (l, v')]]) by
          (by rewrite vset_app_split, Heqh0).
        specialize (IHoff_vpath_equiv _ H1).
        eapply Offset_vpath_loc ; eauto.
    }
  Qed.
      
  Lemma off_vpath_equiv_vset_not_pref :
    forall v tinit t off vp0 vp1 v',
      ~ vprefix vp1 vp0 ->
      off_vpath_equiv v tinit off t vp0 <->
        off_vpath_equiv (v.[[ vp1 <- v' ]]) tinit off t vp0.
  Proof.
    intros v tinit t off vp0 vp1 v' Hpref. split ; intros Hvequiv.
    {
      induction Hvequiv ; subst.
      - apply Offset_vpath_base ; auto.
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
      - apply Offset_vpath_base.
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

  Lemma off_vpath_equiv_vset :
    forall v tinit t off vp0 vp1 v',
      ~ vstrict_prefix vp1 vp0 ->
      off_vpath_equiv v tinit off t vp0 <->
        off_vpath_equiv (v.[[ vp1 <- v' ]]) tinit off t vp0.
  Proof.
    intros. destruct (comparable_vpaths vp0 vp1).
    - subst. apply off_vpath_equiv_vset_eq.
    - apply off_vpath_equiv_vset_not_pref. intros ([ | ?] & ?).
      + rewrite app_nil_r in H1 ; subst. auto.
      + assert (vstrict_prefix vp1 vp0) by (repeat econstructor ; eauto). auto.
    - contradiction.
    - apply not_vprefix_vdisj in H0. apply off_vpath_equiv_vset_not_pref.
      intros ( [ | ? ] & ?).
      + rewrite app_nil_r in H1. subst.
        assert (vprefix vp0 vp0) by (exists [] ; by rewrite app_nil_r). auto.
      + assert (vstrict_prefix vp1 vp0) by (repeat econstructor ; eauto). auto.
  Qed.

  Lemma addr_spath_equiv_sset_equal : 
    forall S addr t sp v,
      addr ~^{S, t} sp <->
      addr ~^{(S .[ sp <- v]), t} sp /\ valid_spath S (sp.1, []).
  Proof.
    intros.
    assert (Hsp : sp = (sp.1, []) +++ sp.2) by
      (unfold "+++" ; simpl ; by rewrite <- surjective_pairing).
    split ; intros.
    - inversion H ; subst. split ; auto. econstructor ; eauto.
      + apply sset_prefix_right_valid ; auto. rewrite Hsp ; simpl. exists sp.2. auto.
      + rewrite Hsp, sset_sget_prefix ; auto. apply off_vpath_equiv_vset_eq. by simpl.
    - destruct H. inversion H ; subst. econstructor ; eauto.
      rewrite Hsp, sset_sget_prefix in Hvequiv; auto.
      by apply off_vpath_equiv_vset_eq in Hvequiv.
  Qed.

  Lemma addr_spath_equiv_sset : 
    forall S addr t sp0 sp1 v,
      ~ prefix sp1 sp0 ->
      addr ~^{S, t} sp0 <->
      addr ~^{(S .[ sp1 <- v]), t} sp0.
  Proof.
    intros S addr t sp0 sp1 v Hpref.
    assert (Hsp0 : sp0 = (sp0.1, []) +++ sp0.2) by (apply spath_var_app_vpath).
    assert (Hsp1 : sp1 = (sp1.1, []) +++ sp1.2) by (apply spath_var_app_vpath).
    rewrite Hsp0, Hsp1.
    split ; intros Hequiv ; inversion Hequiv ; subst.
    - econstructor ; eauto.
      + rewrite <- sset_not_prefix_valid ; eauto. apply not_strict_prefix_nil.
      + simpl fst in *. simpl snd in *.
        destruct (not_prefix_var_equal_or_not_vprefix sp1 sp0 Hpref).
        * rewrite sset_sget_disj ; auto. left. auto.
        * destruct H0 as [Heq Hvpref].
          rewrite Heq in *. rewrite sset_sget_prefix ; auto.
          apply off_vpath_equiv_vset_not_pref ; auto.
    - rewrite <- sset_not_prefix_valid in Hvp ; eauto ; [ | apply not_strict_prefix_nil].
      econstructor ; eauto.
      simpl fst in * ; simpl snd in *.
      destruct (not_prefix_var_equal_or_not_vprefix sp1 sp0 Hpref).
        * rewrite sset_sget_disj in Hvequiv ; auto. by left.
        * destruct H0 ; subst. rewrite <- H0 in *.
          rewrite sset_sget_prefix, <- off_vpath_equiv_vset_not_pref in Hvequiv ; eauto.
  Qed.
  
  Lemma addr_spath_equiv_var_bi :
    forall S addr t sp,
      addr ~^{S, t} sp -> exists t0, blockof sp.1 = (addr.1, t0).
  Proof.
    intros S addr t sp Hequiv. inversion Hequiv ; subst ; simpl ; eauto. 
  Qed.

  Lemma off_vpath_equiv_deterministic_type :
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      t1 = t2.
  Proof.
    intros vinit tinit vp. induction vp using rev_ind ; intros.
    - inversion H ; inversion H0 ; subst ; by try sp_discriminate_or_find_equalities.
    - inversion H ; inversion H0 ; subst ;
        repeat (try sp_discriminate_or_find_equalities ; try rewrite_pairs).
      * assert (Hpt : TPair t1 t3 = TPair t2 t5) by (eapply IHvp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * assert (Hpt : TPair t0 t1 = TPair t4 t2) by (eapply IHvp ; eauto).
        injection Hpt ; intros ; subst ; auto.
      * eapply IHvp ; eauto.
  Qed.

  (* Addr_spath_equiv is a function: given state S and spath sp, addr and t are unique *)
  Lemma off_vpath_equiv_deterministic_off :
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      off1 = off2.
  Proof.
    intros vinit tinit vp. induction vp using rev_ind ; intros.
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
      addr1 ~^{S, t1} sp ->
      addr2 ~^{S, t2} sp ->
      t1 = t2.
  Proof.
    intros. inversion H ; inversion H0 ; subst.
    assert (tinit = tinit0) by congruence ; subst.
    eapply off_vpath_equiv_deterministic_type ; eauto.
  Qed.
 
  Lemma addr_spath_equiv_deterministic_addr :
    forall S sp addr1 addr2 t1 t2,
      addr1 ~^{S, t1} sp ->
      addr2 ~^{S, t2} sp ->
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
      addr1 ~^{S, t1} sp ->
      addr2 ~^{S, t2} sp ->
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
      addr ~^{S, t} sp -> valid_spath S sp.
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
      addr ~^{S, t} sp ->
      valid_access Spl addr t.
  Proof.
    intros S Spl (enc_x, vp) (bi, off) t [Hconcr_mem Hconcr_env] Hequiv.
    inversion Hequiv ; subst. simpl in *.
    induction Hvequiv ; subst.
    - destruct (Hconcr_mem enc_x bi tinit (S.[(enc_x, [])]) Hvp eq_refl H)
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

  Lemma off_vpath_equiv_compose' :
    forall vp1 vp2 v t0 t2 off2,
      off_vpath_equiv v t0 off2 t2 (vp1 ++ vp2) <->
        exists t1 off1,
          off2 >= off1 /\
            off_vpath_equiv v t0 off1 t1 vp1 /\
            off_vpath_equiv (v.[[ vp1]]) t1 (off2-off1) t2 vp2.
  Proof.
    intros. split ; intros.
    - generalize dependent v. generalize dependent off2. generalize dependent t2.
      induction vp2 using rev_ind ; intros.
      + exists t2, off2. rewrite app_nil_r in H. repeat split ; auto.
        rewrite Nat.sub_diag. constructor.
      + inversion H ; subst.
        * apply f_equal with (f := LB.last) in H3. simpl in H3.
          rewrite app_assoc, LB.last_snoc in H3. discriminate.
        * rewrite app_assoc in H3. apply app_inj_tail in H3 as [? ?] ; subst.
          destruct (IHvp2 (TPair t2 t3) _ _ Hrec) as (t1 & off1 & ? & ? & ?).
          exists t1, off1 ; repeat split ; auto.
          apply Offset_vpath_pair_first with (t1 := t3) ; auto. by rewrite <- vget_app.
        * rewrite app_assoc in H3. apply app_inj_tail in H3 as [? ?] ; subst.
          destruct (IHvp2 _ _ _ Hrec) as (tint & offint & ? & ? & ?).
          exists tint, offint ; repeat split ; auto ; try lia.
          replace (off + sizeof t1 - offint) with (off - offint + sizeof t1) by lia.
          eapply Offset_vpath_pair_second ; auto. by rewrite <- vget_app.
        * rewrite app_assoc in H3. apply app_inj_tail in H3 as [? ?] ; subst.
          destruct (IHvp2 _ _ _ Hrec) as (tint & offint & ? & ? & ?).
          exists tint, offint ; repeat split ; auto.
          apply Offset_vpath_loc with (l := l); auto. by rewrite <- vget_app.
    - destruct H as (t1 & off1 & ? & ? & ?).
      remember (off2 - off1) as offdiff. generalize dependent off2.
      induction H1 ; intros.
      + rewrite app_nil_r. by replace off2 with off1 by lia.
      + specialize (IHoff_vpath_equiv off2 H Heqoffdiff).
        rewrite app_assoc. eapply Offset_vpath_pair_first ; eauto.
        by rewrite vget_app.
      + assert (off2 - sizeof t2 >= off1) by lia.
        assert (off = off2 - sizeof t2 - off1) by lia.
        specialize (IHoff_vpath_equiv (off2 - sizeof t2) H2 H3).
        rewrite app_assoc. replace off2 with (off2 - sizeof t2 + sizeof t2) by lia.
        eapply Offset_vpath_pair_second; eauto.
        by rewrite vget_app.
      + rewrite app_assoc. apply Offset_vpath_loc with (l := l).
        * by rewrite vget_app.
        * apply IHoff_vpath_equiv ; auto.
  Qed.
  
  Lemma off_vpath_equiv_compose :
    forall vp1 vp2 v t0 t2 off,
      off_vpath_equiv v t0 off t2 (vp1 ++ vp2) <->
        exists t1 off1 off2,
          off = off1 + off2 /\
            off_vpath_equiv v t0 off1 t1 vp1 /\
            off_vpath_equiv (v.[[ vp1]]) t1 off2 t2 vp2.
  Proof.
    intros. split ; intros.
    - destruct (proj1 (off_vpath_equiv_compose' _ _ _ _ _ _) H)
        as (t1 & off1 & ? & ? & ?).
      exists t1, off1, (off - off1). repeat split ; auto. lia.
    - destruct H as (t1 & off1 & off2 & ? & ? & ?).
      apply off_vpath_equiv_compose'. exists t1, off1 ; repeat split ; auto ; try lia.
      by replace (off - off1) with off2 by lia.
  Qed.

  Lemma addr_spath_equiv_compose :
    forall sp vp S t addr,
      addr ~^{S, t} (sp +++ vp) <->
        exists t' addr' off,
          addr = addr' +o off /\
            addr' ~^{S, t'} sp /\
            off_vpath_equiv (S.[ sp ]) t' off t vp.
  Proof.
    intros *. split ; intro equiv.
    - inversion equiv ; subst. simpl fst in *. simpl snd in Hvequiv.
      apply off_vpath_equiv_compose in Hvequiv.
      destruct Hvequiv as (t' & off1 & off2 & eq & equiv1 & equiv2).
      exists t', (addr.1, off1), off2 ; repeat split.
      + unfold "+o". simpl. by rewrite surjective_pairing with (p := addr), <- eq.
      + econstructor ; eauto.
      + by rewrite (spath_var_app_vpath sp), sget_app.
    - destruct equiv as (t' & addr' & off & eq & equiv & vequiv).
      inversion equiv ; subst.
      apply Addr_spath_base with (v := (S.[(sp.1, [])])) (tinit := tinit) ; auto.
      simpl. apply off_vpath_equiv_compose.
      exists t', addr'.2, off ; repeat split ; auto.
      by rewrite <- sget_app, <- (spath_var_app_vpath sp).
  Qed.
      
  Lemma add_loc_off_vpath_equiv_suffix :
    forall off vi vi' ti t vpl suff l,
      off_vpath_equiv vi ti off t (vpl ++ suff) ->
      vi' = (vi.[[vpl <- loc (l, vi.[[vpl]])]]) ->
      off_vpath_equiv vi' ti off t (vpl ++ [0] ++ suff).
  Proof.
    intros. apply off_vpath_equiv_compose in H as (t1 & off1 & off2 & ? & ? & ?).
    rewrite app_assoc. apply off_vpath_equiv_compose.
    exists t1, off1, off2 ; repeat split ; auto.
    - apply Offset_vpath_loc with (l := l).
      + rewrite H0, vset_vget_equal ; try reflexivity.
        eapply off_vpath_equiv_implies_valid_vpath ; eauto.
      + by rewrite H0, <- off_vpath_equiv_vset_eq.
    - rewrite H0, vget_app, vset_vget_equal ; auto.
      eapply off_vpath_equiv_implies_valid_vpath ; eauto.
  Qed.

  Lemma add_loc_off_vpath_equiv_suffix' :
    forall off vi ti t vpl suff l,
      off_vpath_equiv vi ti off t (vpl ++ suff)  <->
        off_vpath_equiv (vi.[[vpl <- loc (l, vi.[[vpl]])]]) ti off t (vpl ++ [0] ++ suff).
  Proof.
    intros. split ; intros.
    { 
      apply off_vpath_equiv_compose in H as (t1 & off1 & off2 & ? & ? & ?).
      rewrite app_assoc. apply off_vpath_equiv_compose.
      exists t1, off1, off2 ; repeat split ; auto.
      - apply Offset_vpath_loc with (l := l).
        + rewrite vset_vget_equal ; try reflexivity.
          eapply off_vpath_equiv_implies_valid_vpath ; eauto.
        + by rewrite <- off_vpath_equiv_vset_eq.
      - rewrite vget_app, vset_vget_equal ; auto.
        eapply off_vpath_equiv_implies_valid_vpath ; eauto.
    }
    {
      rewrite app_assoc in H.
      apply off_vpath_equiv_compose in H as (t1 & off1 & off2 & ? & ? & ?).
      apply off_vpath_equiv_implies_valid_vpath in H0 as Hvp0.
      apply valid_vpath_app in Hvp0 as [Hvp0 _]. apply vset_same_valid_rev in Hvp0.
      rewrite vget_app, vset_vget_equal in H1 ; auto.
      inversion H0 ; sp_discriminate_or_find_equalities. 
      - rewrite vset_vget_equal in Hpair ; auto. simpl in Hpair. congruence.
      - rewrite vset_vget_equal in Hpair ; auto. simpl in Hpair. congruence.
      - simpl in H1. apply off_vpath_equiv_vset_eq in Hrec.
        apply off_vpath_equiv_compose. repeat econstructor ; eauto.
    } 
  Qed.

  Lemma add_loc_addr_spath_equiv_suffix :
    forall S addr t sp suff l,
      addr ~^{S, t} (sp +++ suff) <->
        addr ~^{(S.[ sp <- (loc (l, S.[sp])) ]), t} (sp +++ [0] ++ suff) /\
          valid_spath S sp.
  Proof.
    intros. split ; intros.
    {
      inversion H ; subst. split.
      - econstructor ; eauto.
        + simpl fst. apply sset_prefix_right_valid ; eauto. exists sp.2.
          unfold "+++". simpl. symmetry. apply surjective_pairing.
        + simpl fst. simpl snd. replace (0 :: suff) with ([0] ++ suff) by reflexivity.
          rewrite spath_var_app_vpath with (p := sp). simpl fst. simpl snd.
          rewrite sset_app_split, sset_sget_equal, sget_app. simpl in Hvp.
          eapply add_loc_off_vpath_equiv_suffix ; eauto. by simpl fst in Hvp.
      - by apply addr_spath_equiv_implies_valid_spath, valid_spath_app in H as [? ?].
    }
    {
      destruct H as [Hequiv Hvsp].
      assert (Hvsp' : valid_spath S (sp.1, [])) by
        (rewrite spath_var_app_vpath in Hvsp; eapply valid_spath_app ; eauto).
      inversion Hequiv ; subst. econstructor ; eauto ; simpl.
      simpl fst in *. simpl snd in *.
      replace (0 :: suff) with ([0] ++ suff) in Hvequiv by reflexivity.
      apply add_loc_off_vpath_equiv_suffix' with (l := l); auto.
      rewrite <- sset_sget_prefix, <- spath_var_app_vpath, <- sget_app ; auto.
    }
  Qed.

  Lemma remove_loc_addr_spath_equiv_suffix :
    forall S addr t p suff l,
      get_node (S.[p]) = locC (l) ->
      addr ~^{S.[p <- S.[p +++ [0] ] ], t} (p +++ suff) <->
        addr ~^{S, t} (p +++ [0] ++ suff) /\
          valid_spath S p.
  Proof.
    intros * node. split ; intros.
    {
      nodes_to_val.
      assert (vsp : valid_spath S p)
        by (apply get_not_bot_valid_spath ; rewrite Heqh ; discriminate).
      split ; auto.
      rewrite sget_app, Heqh in H. simpl in H.
      apply addr_spath_equiv_compose in H.
      destruct H as (t' & addr' & off & eq & equiv & vequiv).
      assert (vsp' : valid_spath S (p.1, [])) 
        by (rewrite spath_var_app_vpath in vsp ;
            apply valid_spath_app in vsp as (? & ?) ; auto).
      pose proof (conj equiv vsp') as equiv'.
      apply addr_spath_equiv_sset_equal in equiv'.
      rewrite app_spath_vpath_assoc.
      apply addr_spath_equiv_compose.
      exists t', addr', off ; repeat split ; auto.
      + rewrite <- Addr_spath_loc with (l := l) ; auto.
      + rewrite sget_app, Heqh. simpl. rewrite sset_sget_equal in vequiv ; auto.
    }
    {
      nodes_to_val. rewrite sget_app, Heqh. simpl.
      destruct H as (equiv & vsp).
      rewrite app_spath_vpath_assoc in equiv.
      apply addr_spath_equiv_compose in equiv.
      destruct equiv  as (t' & addr' & off & eq & equiv & vequiv).
      apply addr_spath_equiv_compose.
      exists t', addr', off ; repeat split ; auto.
      + apply addr_spath_equiv_sset_equal. 
        apply Addr_spath_loc with (l := l) ; auto.
      + rewrite sget_app, Heqh in vequiv. simpl in vequiv.
        rewrite sset_sget_equal ; auto.
    }
  Qed.

  Record Compatible (S : HLPL_state) : Prop :=
    mkCompatible
      {
        block_dom :
        forall x enc_x : positive,
          enc_x = encode_var x ->
          valid_spath S (enc_x, []) ->
          exists bi t, blockof enc_x = (bi, t) 
      ; correct_addrof :
        forall (sp : spath) (addr : address) t l,
          addr ~^{S, t} sp ->
          get_node (S.[sp]) = HLPL_locC l ->
          addrof l = Some (addr, t)
      ; reachable_loc :
        forall l sp,
          get_node (S.[sp]) = HLPL_locC l ->
          exists addr t, addr ~^{S, t} sp
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

  Lemma le_block_not_contains_poison :
    forall vl vl', le_block vl vl' -> ~ (In PL_poison vl') -> vl = vl'.
  Proof.
    intros. generalize dependent vl. induction vl' ; intros vl Hle.
    - by inversion Hle.
    - inversion Hle ; subst.
      simpl in H0. apply Decidable.not_or in H0 as [? ?].
      specialize (IHvl' H0 l H4). subst.
      inversion H3 ; subst ; congruence.
  Qed.

  Definition le_mem : relation (Pmap pl_val) :=
    fun h1 h2 =>
      dom h1 = dom h2 /\
      forall bi b1,
        h1 !! bi = Some b1 ->
        exists b2, h2 !! bi = Some b2 /\ le_block b1 b2.
  Global Program Instance IsPreorderMem: PreOrder le_mem.
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
    fun Spl1 Spl2 => env Spl1 = env Spl2 /\ le_mem (mem Spl1) (mem Spl2).
  Global Program Instance IsPreorderState : PreOrder le_pl_state.
  Next Obligation.
    intros Spl. split ; reflexivity. Qed.
  Next Obligation.
    intros Spl1 Spl2 Spl3 [env12 mem12] [env23 mem23]. split ; try congruence.
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


  (** Concretization of states/values implies correct types for values. *)
  Lemma val_concr_implies_correct_type_size :
    forall v t vl,
      concr_hlpl_val v t vl -> sizeof t = length vl.
  Proof.
    intros v t vl Hconcr. induction Hconcr ; auto.
    - subst s. rewrite repeat_length. reflexivity.
    - rewrite List.length_app. simpl. rewrite IHHconcr1, IHHconcr2. reflexivity.
  Qed.

  (* Lookup mem lemmas*)
  Lemma lookup_mem_Some :
    forall Spl addr t vl,
      Spl.m.[ addr : t ] = Some vl -> valid_access Spl addr t.
  Proof.
    intros Spl addr t0 t1 bytes0 bytes1 Hlen0 Hlen1. split ; intros H.
    - simpl in H. rewrite Nat2Z.inj_add in H.
      apply Mem.loadbytes_split in H as (bytes0' & bytes1' & load0 & load1 & eq) ;
        try lia ; simpl.
      apply Mem.loadbytes_length in load0 as len0. rewrite Nat2Z.id in len0.
      apply LB.app_inj_1 in eq as (eq0 & eq1) ;
        repeat constructor ; congruence.
    - simpl in *. destruct H as (load0 & load1). rewrite Nat2Z.inj_add. 
      apply Mem.loadbytes_concat ; auto ; lia.
  Qed.
                                   
  (* Concretization of states implies concretization of values *)

  Lemma lookup_mem_length_le_size :
    forall Spl addr t vl,
      Spl.m.[addr : t] = Some vl ->
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
        addr ~^{S, t} sp /\ concr_hlpl_val v t vl /\ Spl.m.[addr : t] = Some vl.
  Proof.
    induction sp using ListBackInd.state_path_back_ind ;
      intros v Hconcr Hvspn HSx ;
    pose proof Hconcr as [Hconcr_mem Hconcr_env].
    remember (blockof enc_x).1 as bi. remember (blockof enc_x).2 as t.
    assert (Heqbit : blockof enc_x = (bi, t))
      by (subst ; rewrite <- surjective_pairing ; reflexivity).
    - specialize (Hconcr_mem _ _ _ _ Hvspn HSx Heqbit) as (vl & Hconcr_val & Hmem).
      assert (Hequiv : (bi, 0) ~^{S, t} (enc_x, []))
      by (eapply Addr_spath_base ; eauto ; eapply Offset_vpath_base). 
      exists (bi, 0), t, vl. repeat split ; auto.
      unfold lookup_at_addr ; simpl.
      assert (Hva: valid_access Spl (bi, 0) t) by
      (eapply addr_spath_equiv_implies_valid_access ; eauto).
      destruct (valid_access_dec Spl (bi, 0) t) ; try contradiction.
      replace (mem Spl !! bi) with (Some vl) ; simpl. f_equal.
      by rewrite drop_0, (val_concr_implies_correct_type_size v t vl), firstn_all.
    - rewrite sget_app in HSx. 
      apply valid_spath_app in Hvspn as Htemp ; destruct Htemp as (Hvsp & Hvvp).
      destruct (S.[sp]) eqn:E ;
        try (apply not_valid_spath_app_last_get_node_arity in Hvspn as [] ;
        rewrite E ; simpl ; lia).
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr ~^{S, t} sp ∧
                     concr_hlpl_val (loc ((l), (y))) t vl /\
                     Spl.m.[addr : t] = Some vl) by auto.
        destruct H as [addr [t [vl [ Hequiv [Hconcr_val Hval_mem] ] ] ] ].
        destruct n ; simpl in HSx.
        * exists addr, t, vl. repeat split ; auto.
          ** inversion Hequiv ; subst.
             rewrite <- Addr_spath_loc with (l := l); auto. rewrite E ; auto.
          ** inversion Hconcr_val ; subst ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2. congruence.
      + assert (H : ∃ (addr : address) (t : type) (vl : pl_val),
                   addr ~^{S, t} sp ∧
                     concr_hlpl_val (HLPL_pair y1 y2) t vl /\
                     Spl.m.[addr : t] = Some vl) by auto.
        destruct H as [addr [t [vl [Hequiv [Hconcr_val Hval_mem] ] ] ] ].
        inversion Hconcr_val ; subst v0 v1 t vl.
        apply concr_val_size in H4 as Hsize_t0, H5 as Hsize_t1.
        apply lookup_mem_pair in Hval_mem as [Hval_t0 Hval_t1] ; auto.
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
      addr ~^{S, t} sp ->
      exists vl,
         concr_hlpl_val v t vl /\ Spl.m.[addr : t] = Some vl.
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
    forall v vl, concr_hlpl_val v TInt vl ->
            (exists n, vl = (make_int64 n)) \/ vl = repeat PL_poison (sizeof TInt).
  Proof.
    intros v vl Hconcr. remember TInt as t. induction Hconcr ; try discriminate.
    - left. exists n. reflexivity.
    - right. subst. reflexivity.
    - auto.
  Qed.

  Lemma le_mem_preserves_valid_access :
    forall S1 S2 addr t,
      le_mem (mem S1) (mem S2) ->
      valid_access S1 addr t <-> valid_access S2 addr t.
  Proof.
    intros S1 S2 addr t [Hdom Hle_mem]. split ; intros (b & Haddr & Hsize).
    - destruct (Hle_mem addr.1 b Haddr) as (b2 & Haddr2 & Hle2).
      apply Forall2_length in Hle2. exists b2 ; split ; auto ; lia.
    - assert (Hb1 : exists b1, S1 !!h addr.1 = Some b1).
      {apply elem_of_dom. rewrite Hdom. apply elem_of_dom. exists b ; auto.}
      destruct Hb1 as [b1 Haddr1].
      destruct (Hle_mem addr.1 b1 Haddr1) as (b' & Haddr' & Hsize'%Forall2_length).
      exists b1 ; split ; auto. replace (S2 !!h addr.1) with (Some b') in Haddr.
      congruence.
  Qed.

  Lemma le_mem_implies_lookup_equiv :
    forall S1 S2 addr t,
      le_mem (mem S1) (mem S2) ->
      (exists vl1, S1.m.[ addr : t ] = Some vl1) <->
      (exists vl2, S2.m.[ addr : t ] = Some vl2).
  Proof.
    intros S1 S2 addr t [Hdom Hle_mem] ; split ;
      intros (vl & Hlu).
    - unfold lookup_at_addr in *.
      destruct (valid_access_dec S1 addr t) as [(b1 & Hb1 & Hsize1) | ].
      + destruct (Hle_mem addr.1 b1 Hb1) as (b2 & Hb2 & Hle2).
        destruct (valid_access_dec S2 addr t).
        * exists (take (sizeof t) (drop addr.2 b2)).
          by replace (S2 !!h addr.1) with (Some b2).
        * apply Forall2_length in Hle2. rewrite Hle2 in Hsize1.
          assert (contra : valid_access S2 addr t) by (exists b2 ; auto). contradiction.
      + congruence.
    - unfold lookup_at_addr in *.
      destruct (valid_access_dec S1 addr t) as [(b1 & Hb1 & Hsize1) | ].
      + destruct (Hle_mem addr.1 b1 Hb1) as (b2 & Hb2 & Hle2).
        destruct (valid_access_dec S2 addr t).
        * exists (take (sizeof t) (drop addr.2 b1)).
          by replace (S1 !!h addr.1) with (Some b1).
        * apply Forall2_length in Hle2. rewrite Hle2 in Hsize1.
          assert (contra : valid_access S2 addr t) by (exists b2 ; auto). contradiction.
       + destruct (valid_access_dec S2 addr t).
         * eapply le_mem_preserves_valid_access with (S1 := S1) in v ; easy.
         * congruence.
  Qed.

  Lemma le_mem_lookup_implies_lookup_l :
    forall S1 S2 addr t vl1,
      le_mem (mem S1) (mem S2) ->
      S1.m.[ addr : t ] = Some vl1 ->
      exists vl2, S2.m.[ addr : t ] = Some vl2.
  Proof.
    intros S1 S2 addr t vl1 Hle_mem Hread.
    apply ex_intro with (x := vl1) in Hread.
    apply le_mem_implies_lookup_equiv with (S2 := S2) in Hread ; auto.
  Qed.

  Lemma le_mem_implies_lookup_equiv :
    forall S1 S2 addr t,
      le_mem (mem S1) (mem S2) ->
      (exists vl1, S1.m.[ addr : t ] = Some vl1) <->
      (exists vl2, S2.m.[ addr : t ] = Some vl2).
  Proof.
    intros * le. split ; intros (vl & load). 
    - eapply le_mem_preserves_access_l ; eauto.
    - eapply le_mem_preserves_access_r ; eauto.
  Qed.

  Opaque Mem.loadbytes. 

  (** Simulation proof between spath and address *)
  Lemma spath_address_proj_simul :
    forall S Spl sp sp' addr t proj,
      le_pl_hlpl Spl S ->
      addr ~^{S, t} sp ->
      HLPL_No_Anon.eval_proj S proj sp sp' ->
      exists addr' t',
        eval_proj Spl proj (addr, t) (addr', t') /\
          addr' ~^{S, t'} sp'.
  Proof.
    intros S Spl sp sp' addr t proj
      (Spl' & HComp & Hconcr & _ & Hmem) Hequiv Hproj.
    pose proof HComp as Hcomp.
    destruct HComp as [_ Hcorr_addrof Hloc].
    inversion Hproj ; subst.
    - nodes_to_val.
      assert (Hvsp : valid_spath S sp) by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_ptr l) t vl ∧
                      Spl'.m.[addr : t] = Some vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & Hlu_addr). inversion Hconcr_val ; subst.
      assert (Hvsp' : valid_spath S sp') by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp : ∃ (addr : address) (t : type) (vl : pl_val),
                 addr ~^{S, t} sp' ∧
                   concr_hlpl_val (HLPL_loc l h) t vl ∧
                   Spl'.m.[addr : t] = Some vl).
      { apply state_concr_implies_val_concr ; auto. }.
      destruct Htemp as (addr' & t' & vl & Hequiv' & Hconcr_val' & Hlu_addr').
      exists addr', t' ; split ; auto.
      apply Hcorr_addrof with (l := l) in Hequiv' as Haddr'; auto.
      assert (t' = t0) by congruence ; subst.
      constructor.
      pose proof (Hcorr_addrof _ _ _ _ Hequiv' H0).
      rewrite Haddr in H1 ; injection H1 ; intros ; subst ; clear H1.
      apply ex_intro with (x := (make_ptr64 addr')) in Hlu_addr as Hex.
      eapply le_mem_implies_lookup_equiv in Hex ; eauto. destruct Hex as (vl1 & Hlu).
      pose proof (le_mem_implies_le_block_at_addr _ _ _ _ _ _ Hmem Hlu Hlu_addr).
      assert (vl1 = (make_ptr64 addr')) by
       (apply le_block_not_contains_poison ; auto ;
        apply make_ptr64_not_contain_poison).
      by subst.
    - nodes_to_val.
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_pair h1 h2) t vl ∧
                      Spl'.m.[addr : t] = Some vl).
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
                             Spl'.m.[addr : t] = Some vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & _). inversion Hconcr_val ; subst.
      exists (addr +o sizeof t0), t1 ; split.
      * constructor.
      * eapply Addr_spath_pair_second ; eauto. 
  Qed.

  Lemma spath_address_loc_simul :
    forall S Spl sp sp' addr t,
      le_pl_hlpl Spl S ->
      addr ~^{S, t} sp ->
      eval_loc S sp sp' ->
      addr ~^{S, t} sp'.
  Proof.
    intros S Spl sp sp' addr t Hle Hequiv Heval_loc.
    inversion Heval_loc ; subst.
    rewrite <- Addr_spath_loc with (l := l) ; auto.
  Qed.

  Lemma spath_address_path_simul :
    forall S Spl P sp sp' addr t,
      le_pl_hlpl Spl S ->
      HLPL_No_Anon.eval_path S P sp sp' ->
      addr ~^{S, t} sp ->
      exists addr' t',
        eval_path Spl P (addr, t) (addr', t') /\
          addr' ~^{S, t'} sp'.
  Proof.
    intros S Spl P sp sp' addr t Hle Hpath Hequiv.
    pose proof Hle as Htemp.
    destruct Htemp as (Spl' & HComp & (Hconcr_mem & Hconcr_env) & Henv & Hmem).
    generalize dependent t.  generalize dependent addr.
    induction Hpath ; intros addr t Hequiv.
    - exists addr, t. repeat constructor ; auto.
    - destruct (spath_address_proj_simul _ _ _ _ _ _ _ Hle Hequiv Heval_proj)
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

  Lemma spath_address_place_simul :
    forall S Spl p sp,
      le_pl_hlpl Spl S ->
      S |-{p} p => sp ->
      exists addr t, 
        Spl |-{p} p =>^{pl} (addr, t) /\ addr ~^{S, t} sp.
  Proof.
    intros. destruct (blockof (encode_var p.1)) as (bi, t0) eqn:E.
    inversion H0 ; subst.
    assert (addr_spath_equiv S (bi, 0) t0 (encode_var p.1, [])) by
    (econstructor ; eauto ; simpl ; constructor).
    destruct (spath_address_path_simul _ _ _ _ _ _ _ H H2 H3) as (addr & t & ? & ?).
    exists addr, t ; split ; auto.
    econstructor. exists t0 ; split ; eauto.
    destruct H as (Spl' & ? & ? & ?). destruct H7. destruct H6.
    unfold lookup_block_and_type_env. rewrite H7. eapply H9 ; eauto.
  Qed.
    
  Lemma eval_place_hlpl_pl_equiv :
    forall S Spl p sp t,
      le_pl_hlpl Spl S ->
      S |-{p} p => sp ->
      eval_type S sp t ->
      exists addr,
        Spl |-{p} p =>^{pl} (addr, t) /\ addr ~^{S, t} sp.
  Proof.
    intros S Spl p sp t Hle Hplace Heval_type.
    pose proof Hle as Htemp.
    destruct Htemp as (Spl' & HComp & (Hconcr_mem & Hconcr_env) & Henv & Hmem).
    destruct Hplace as [Hvsp Hpath]. simpl in *.
    destruct (blockof (encode_var p.1)) as [bi t0] eqn:Hbo.
    assert (Hsimul_path_pl : exists addr t,
               eval_path Spl p.2 ((bi, 0), t0) (addr, t) /\ addr ~^{S, t} sp).
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
    forall S Spl p sp t addr,
      le_pl_hlpl Spl S ->
      S |-{p} p => sp ->
      eval_type S sp t ->
      addr_spath_equiv S addr t sp <-> read_address Spl p t addr .
  Proof.
    intros S Spl p sp t addr Hle Heval_place Heval_type ; split.
    {
      intros Hequiv.
      destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ Hle Heval_place Heval_type)
        as (addr' & Heval_place' & Hequiv').
      rewrite (addr_spath_equiv_deterministic_addr _ _ _ _ _ _ Hequiv Hequiv') in *.
      assumption.
    }
    {
      intros (bi & t' & Hlu & Heval_path). 
      destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ Hle Heval_place Heval_type)
        as (addr' & (bi' & t'' & Hlu' & Heval_path') & Hequiv').
      rewrite Hlu in Hlu' ; injection Hlu' ; intros ; subst.
      by pose proof (eval_path_deterministic _ _ _ _ _ Heval_path Heval_path')
        as [=] ; subst.
    }
  Qed.

  Lemma concr_val_equiv_concr_copy_val :
    forall v v_copy t vl, 
      HLPL_No_Anon.copy_val v v_copy ->
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

  Lemma le_mem_range_perm_eq :
    forall mem1 mem2 b lo hi k p,
      le_mem mem1 mem2 -> 
      Mem.range_perm mem1 b lo hi k p <->
        Mem.range_perm mem2 b lo hi k p.
  Proof.
    intros * (perms & _) ; split ; intro H ;
      intros ofs le ; specialize (H ofs le) ;
      unfold Mem.perm in * ; congruence.
  Qed.

  Lemma le_mem_storebytes_None_equiv :
    forall mem1 mem2 b ofs bytes1 bytes2,
      le_mem mem1 mem2 ->
      Datatypes.length bytes1 = Datatypes.length bytes2 ->
      Mem.storebytes mem1 b ofs bytes1 = None <->
        Mem.storebytes mem2 b ofs bytes2 = None.
  Proof.
    Transparent Mem.storebytes. unfold Mem.storebytes in *. Opaque Mem.storebytes.
    intros * Hle_mem len_eq. split.
    - intros H.
      destruct (Mem.range_perm_dec mem1 b ofs _ Cur Writable) ; try congruence.
      rewrite (le_mem_range_perm_eq _ mem2) in n ; auto.
      destruct (Mem.range_perm_dec mem2 b ofs _ Cur Writable) ; try congruence.
    - intros H.
      destruct (Mem.range_perm_dec mem2 b ofs _ Cur Writable) ; try congruence.
      rewrite <- (le_mem_range_perm_eq mem1 mem2) in n ; auto.
      destruct (Mem.range_perm_dec mem1 b ofs _ Cur Writable) ; try congruence.
  Qed.

  Lemma le_mem_loadbytes_None_equiv :
    forall mem1 mem2 b ofs n,
      le_mem mem1 mem2 ->
      Mem.loadbytes mem1 b ofs n= None <-> Mem.loadbytes mem2 b ofs n = None.
  Proof.
    Transparent Mem.loadbytes. unfold Mem.loadbytes in *. Opaque Mem.loadbytes.
    intros * le ; split ; intros H.
    - destruct (Mem.range_perm_dec mem1 b ofs (ofs + n) Cur Readable) ;
        try discriminate.
      destruct (Mem.range_perm_dec mem2 b ofs (ofs + n) Cur Readable) ; auto.
      eapply le_mem_range_perm_eq in r ; eauto. contradiction.
    - destruct (Mem.range_perm_dec mem1 b ofs (ofs + n) Cur Readable) ; auto.
      destruct (Mem.range_perm_dec mem2 b ofs (ofs + n) Cur Readable) ;
        try discriminate.
      rewrite <- (le_mem_range_perm_eq _ _ _ _ _ _ _ le) in n0. contradiction.
  Qed.

  Lemma set2 : forall (A : Type) (c : ZMap.t A) (p q : Z) v1 v2,
      p <> q ->
      ZMap.set p v1 (ZMap.set q v2 c) = ZMap.set q v2 (ZMap.set p v1 c).
  Proof.
    intros A (?, ?) * neq. unfold ZMap.set, PMap.set ; simpl. f_equal ; auto.
    apply PTree.extensionality ; intros. rewrite !PTree.gsspec.
    destruct (peq i (ZIndexed.index p)) ; destruct (peq i (ZIndexed.index q)) ; auto.
    subst. apply ZIndexed.index_inj in e0 ; congruence. 
  Qed.

  Lemma setN_inv : forall vl v c p q,
      p < q ->
      Mem.setN vl q (ZMap.set p v c) = ZMap.set p v (Mem.setN vl q c).
  Proof.
    induction vl ; intros * le.
    - reflexivity.
    - simpl. rewrite set2, !IHvl ; auto ; lia.
  Qed.

  Lemma setN_inv' : forall vl v c p,
      ZMap.get p (Mem.setN vl (p + 1) (ZMap.set p v c)) = v.
  Proof.
    intros *. rewrite Mem.setN_other ; [ rewrite ZMap.gss ; reflexivity | lia].
  Qed.

  Lemma setN_get_gt :
    forall vl v c p q,
      p + 1 <= q < p + 1 + Datatypes.length vl ->
      ZMap.get q (Mem.setN vl (p + 1) (ZMap.set p v c)) =
        ZMap.get q (Mem.setN vl (p + 1) c).
  Proof.
    induction vl ; intros * len.
    - simpl in len. lia.
    - simpl in *. rewrite set2, setN_inv ; try lia.
      rewrite ZMap.gso ; auto ; lia.
  Qed.
        
  Lemma setN_inside :
    forall vl c p q,
      p <= q /\ q < p + Datatypes.length vl ->
      ZMap.get q (Mem.setN vl p c) = List.nth (Z.to_nat (q - p)) vl Undef.
  Proof. 
    induction vl ; intros * (lb & hb).
    - simpl in hb. lia.
    - simpl. destruct (Z.to_nat (q - p)) eqn:E.
      * assert (p = q) by lia ; subst. rewrite Mem.setN_other ; [ | lia].
        rewrite ZMap.gss ; reflexivity.
      * simpl in hb. assert (p + 1 <= q < p + 1 + Datatypes.length vl) by lia.
        specialize (IHvl c (p + 1) q H).
        replace (Z.to_nat (q - (p + 1))) with n in IHvl by lia.
        rewrite <- IHvl. rewrite setN_get_gt ; auto.
  Qed.

  Lemma write_read_at_addr :
    forall S addr t v,
      S.m.[ addr : t] = Some v ->
      S.m.[ addr <-  v : t] = S.
  Proof.
    intros * get. unfold update_mem, storebytes.
    destruct ((sizeof t =? Datatypes.length v)%nat).
    - destruct (Mem.storebytes (mem S) addr.1 addr.2 v) eqn:E.
      * Transparent Mem.loadbytes. unfold Mem.loadbytes in get. Opaque Mem.loadbytes.
        Transparent Mem.storebytes. unfold Mem.storebytes in E. Opaque Mem.storebytes.
        destruct (Mem.range_perm_dec (mem S) _ _ _ _ _) ; try discriminate.
        destruct (Mem.range_perm_dec (mem S) _ _ _ _ _) ; try discriminate.
        injection get as <- ; injection E as <-. destruct S ; f_equal.
        admit.
      * destruct S ; reflexivity.
    - destruct S ; reflexivity.
  Admitted.

  Lemma le_block_nth :
    forall b1 b2 d n,
      le_val d d ->
      le_block b1 b2 ->
      le_val (List.nth n b1 d) (List.nth n b2 d).
  Proof.
    intros * le_def le_blo. generalize dependent n.
    induction le_blo.
    - destruct n ; simpl ; auto.
    - destruct n ; simpl ; auto.
  Qed.

  Lemma le_pl_write_at_addr :
    forall Spl1 Spl2 addr t vl vl',
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state (Spl1.m.[ addr <- vl : t ]) (Spl2.m.[ addr <- vl' : t ]).
  Proof.
    intros Spl1 Spl2 addr t vl vl' [Hle_env Hle_mem ] Hle_block.
    assert (Hdom :
             dom (mem (Spl1.m.[ addr <- vl : t ])) =
               dom (mem (Spl2.m.[ addr <- vl' : t ])))
      by (apply dom_stable_by_write_at_addr, (proj1 Hle_mem)).
    split.
    - by repeat rewrite env_stable_by_write_at_addr.
    - split ; auto.
      intros bi b1 Hbi.
      apply elem_of_dom_2 in Hbi as Hbi2.
      rewrite Hdom in Hbi2. apply elem_of_dom in Hbi2. destruct Hbi2 as [b2 Hbi2].
      destruct (Positive_as_DT.eqb_spec bi addr.1).
      + exists b2 ; split ; auto.
        destruct addr as [bi' off].
        unfold write_at_addr, update_mem in Hbi, Hbi2. simpl in Hbi, Hbi2.
        simpl in e ; subst bi'. rewrite lookup_alter in Hbi, Hbi2.
        rewrite <- (Forall2_length _ _ _ Hle_block) in *.
        destruct (Spl1 !!h bi) as [ b1' | ] eqn:Hbi'.
        * apply elem_of_dom_2 in Hbi' as Hbi2' ; rewrite (proj1 Hle_mem) in Hbi2'.
          apply elem_of_dom in Hbi2'. destruct Hbi2' as [b2' Hbi2'].
          rewrite Hbi2' in Hbi2. simpl in Hbi, Hbi2.
          injection Hbi as Hbi ; injection Hbi2 as Hbi2 ; subst.
          assert (Hle_block' : le_block b1' b2')
            by (eapply le_mem_implies_le_block ; eauto).
          apply Forall2_length in Hle_block as Hlen, Hle_block' as Hlen'.
          repeat (try (apply Forall2_app) ; try (apply Forall2_take)
                  ; try (apply Forall2_drop)) ;
            try reflexivity ; auto.
        * simpl in Hbi ; congruence.
      + rewrite get_block_write_at_addr_ne in Hbi ; auto.
        destruct ((proj2 Hle_mem) bi b1 Hbi) as [b2' [Hbi2' Hle] ].
        exists b2 ; split; auto.
        rewrite get_block_write_at_addr_ne in Hbi2 ; auto. 
        replace (Spl2 !!h bi) with (Some b2) in Hbi2'. congruence.
  Qed.

  Lemma le_pl_r :
    forall Spl1 Spl2 addr t vl,
      Spl2.m.[ addr : t ] = Some vl ->
      le_pl_state Spl1 Spl2 ->
      exists vl',
        Spl1.m.[ addr : t ] = Some vl' /\ le_block vl' vl.
  Proof.
    intros * lu (_ & le_mem).
    destruct (Mem.loadbytes (mem Spl1) addr.1 addr.2 (sizeof t)) eqn:E.
    - exists l ; split ; auto.
      apply loadbytes_elim in lu as (perm1 & getN1).
      apply loadbytes_elim in E as (perm2 & getN2).
      eapply le_mem_implies_le_block ; eauto.
    - rewrite le_mem_loadbytes_None_equiv in E ; eauto. congruence.
  Qed.

  Lemma le_pl_l :
    forall Spl1 Spl2 addr t vl,
      Spl1.m.[ addr : t ] = Some vl ->
      le_pl_state Spl1 Spl2 ->
      exists vl',
        Spl2.m.[ addr : t ] = Some vl' /\ le_block vl vl'.
  Proof.
    intros * lu (_ & le_mem).
    destruct (Mem.loadbytes (mem Spl2) addr.1 addr.2 (sizeof t)) eqn:E.
    - exists l ; split ; auto.
      apply loadbytes_elim in lu as (perm1 & getN1).
      apply loadbytes_elim in E as (perm2 & getN2).
      eapply le_mem_implies_le_block ; eauto.
    - rewrite <- le_mem_loadbytes_None_equiv in E ; eauto. congruence.
  Qed.

  Lemma le_pl_write_at_addr_r :
    forall Spl1 Spl2 addr t vl vl',
      Spl1.m.[ addr : t ] = Some vl ->
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state Spl1 (Spl2.m.[ addr <- vl' : t ]).
  Proof.
    intros * read le le_block.
    pose proof le as (env_eq & access_eq & nextblock_eq & le_val).
    constructor ; [ rewrite env_stable_by_write_at_addr ; auto | ].
    eapply le_pl_write_at_addr with (addr := addr) (t := t) in le
        as (le_env & le_m) ; eauto.
    rewrite <- write_read_at_addr with (S := Spl1) (addr := addr) (t := t) (v := bytes)
    ; auto.
  Qed.

  Lemma le_pl_write_at_addr_l :
    forall Spl1 Spl2 addr t vl vl',
      Spl2.m.[ addr : t ] = Some vl' ->
      le_pl_state Spl1 Spl2 ->
      le_block vl vl' ->
      le_pl_state (Spl1.m.[ addr <- vl : t ]) Spl2.
  Proof.
    intros * read le le_block.
    pose proof le as (env_eq & access_eq & nextblock_eq & le_val).
    constructor ; [ rewrite env_stable_by_write_at_addr ; auto | ].
    eapply le_pl_write_at_addr with (addr := addr) (t := t) in le
        as (le_env & le_m) ; eauto.
    rewrite <- write_read_at_addr with (S := Spl2) (addr := addr) (t := t) (v := bytes')
    ; auto.
  Qed.

  Lemma concr_val_off_vpath_equiv_equiv :
    forall vi ti vli,
      length vli = sizeof ti ->
      (concr_hlpl_val vi ti vli <->
         forall off vp t,
           off_vpath_equiv vi ti off t vp ->
           concr_hlpl_val (vi.[[ vp ]]) t (firstn (sizeof t)
                                             (skipn (Z.to_nat off) bytesi))).
  Proof.
    intros. split ; intros.
    {
      apply concr_val_size in H0 as Hleni. induction H1 ; nodes_to_val.
      - simpl. rewrite Nat2Z.id, skipn_0, Hleni, firstn_all ; auto.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. simpl.
        apply concr_val_size in H6 as Hlen0.
        apply f_equal with (f := (firstn (sizeof t0))) in H8.
        rewrite Hlen0, LB.take_app_length, LB.take_take in H8.
        replace (Init.Nat.min (length bytes0) _ ) with (length bytes0) in H8
            by lia.
        congruence.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. simpl.
        apply concr_val_size in H6 as Hlen0. apply concr_val_size in H9 as Hlen1.
        apply f_equal with (f := (skipn (sizeof t0))) in H8.
        rewrite Hlen0, LB.drop_app_length, <- Hlen0,
          <- LB.take_drop_commute, LB.drop_drop in H8.
        rewrite Z2Nat.inj_add, Nat2Z.id ; [ congruence | | lia ].
        Search (_ <= _) (_ >= _).
        eapply Z.ge_le, offset_is_positive ; eauto.
      - inversion IHoff_vpath_equiv ; subst.
        rewrite vget_app, Heqh. simpl. assumption.
    }
    {
      assert (off_vpath_equiv vi ti 0 ti []) by constructor.
      specialize (H0 0 [] ti H1). simpl in H0.
      rewrite LB.drop_0, <- H, firstn_all in H0. assumption.
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
        (vi.[[ vp <- v ]]) ti
        (firstn (Z.to_nat off) bytesi ++ bytes ++
           skipn ((Z.to_nat off) + sizeof t) bytesi).
  Proof.
    intros. apply concr_val_size in H0 as Hleni. symmetry in Hleni.
    generalize dependent v. generalize dependent bytes.
    induction H ; intros bytes v Hconcr.
    - simpl. rewrite <- Hleni, LB.drop_all, app_nil_r. assumption.
    - nodes_to_val.
      assert (off_vpath_equiv vi ti (off + sizeof t0) t1 (vp ++ [Z.to_nat 1]))
        by (eapply Offset_vpath_pair_second ; eauto).
      eapply (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hleni)) in H0 as G; eauto.
      rewrite vget_app, Heqh in G. simpl in G.
      remember (firstn (sizeof t1) (skipn (Z.to_nat off + sizeof t0) bytesi))
        as bytes1.
      apply offset_is_positive in H as off_pos.
      rewrite Z2Nat.inj_add, Nat2Z.id in G ; try lia.
      assert (concr_hlpl_val (HLPL_pair v h2) (TPair t0 t1) (bytes ++ bytes1))
               by (subst ; eapply Concr_pair ; eauto).
      rewrite vset_app_split, Heqh. simpl.
      specialize (IHoff_vpath_equiv _ _ H3). rewrite Heqvl1 in IHoff_vpath_equiv.
      rewrite <- !app_assoc in IHoff_vpath_equiv. simpl in *.
      rewrite <- (LB.take_drop (sizeof t1) (skipn _ _)), LB.drop_drop, <- Nat.add_assoc.
      assumption.
    - nodes_to_val. simpl in *.
      assert (off_vpath_equiv vi ti off t0 (vp ++ [Z.to_nat 0]))
        by (eapply Offset_vpath_pair_first ; eauto).
      eapply (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hleni)) in H0 as G; eauto.
      rewrite vget_app, Heqh in G. simpl in G.
      remember (firstn (sizeof t0) (skipn (Z.to_nat off) bytesi)) as bytes0.
      assert (concr_hlpl_val (HLPL_pair h1 v) (TPair t0 t1) (bytes0 ++ bytes)) by
        (eapply Concr_pair ; eauto).
      rewrite vset_app_split, Heqh. simpl.
      specialize (IHoff_vpath_equiv _ _ H3). rewrite Heqbytes0 in IHoff_vpath_equiv.
      apply offset_is_positive in H as off_pos.
      rewrite !app_assoc, LB.take_take_drop, <- !app_assoc, Nat.add_assoc
        in IHoff_vpath_equiv. rewrite Z2Nat.inj_add, Nat2Z.id in *; try lia.
      assumption.
    - nodes_to_val. simpl in *. rewrite vset_app_split, Heqh. simpl.
      assert (concr_hlpl_val (loc (l, v)) t' bytes) by (apply Concr_loc ; auto).
      specialize (IHoff_vpath_equiv _ _ H2). assumption.
  Qed.

  Lemma concr_state_write_at_addr :
    forall S Spl sp addr v t vl,
      concr_hlpl S Spl ->
      concr_hlpl_val v t vl ->
      addr ~^{S, t} sp ->
      concr_hlpl (S.[sp <- v] ) (Spl.m.[addr <- vl : t]).
  Proof.
    intros * [Hconcr_mem Hconcr_env] Hconcr_val Hequiv. split.
    - intros enc_x bi' t' v' Hvsp HSx Hbo'.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      destruct (addr_spath_equiv_var_bi _ _ _ _ Hequiv) as (t0 & Hbo). cbn in Hbo.
      destruct (Pos.eqb_spec bi bi').
      * subst bi'. 
        simpl.
        admit.
      * admit.
    - intros enc_x bi' t0 Hvsp Hbo. rewrite env_stable_by_write_at_addr.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      specialize (Hconcr_env enc_x bi' t0 Hvsp Hbo). assumption.
  Admitted.
End Concretization.
Notation "addr ~^{ bo , S , t } sp" := (addr_spath_equiv bo S addr t sp) (at level 40).
  
Lemma concr_val_not_val_contains :
  forall ao v t vl l addr_t,
    concr_hlpl_val ao v t vl ->
    not_value_contains (fun n => get_loc_id n = Some l) v ->
    concr_hlpl_val (fun l0 : nat => if (l =? l0)%nat then Some addr_t else ao l0) v t bytes.
Proof.
  intros. induction H ; try (constructor ; auto).
  - apply not_value_contains_struct in H0 as (? & ? & ?). auto.
  - apply not_value_contains_struct in H0 as (? & ? & ?). auto.
  - apply not_value_contains_struct_loc in H0 as (? & ?). auto.
  - specialize (H0 [] (valid_nil _)). simpl in H0.
    assert (l <> l0) by (intros ->; easy).
    rewrite (proj2 (Nat.eqb_neq _ _) H). assumption.
Qed.

Definition op_get_type op :=
  match op with
  | IntConst t _ => t
  | Move t _ => t
  | Copy t _ => t
  end.

Definition rv_get_type rv :=
  match rv with
  | Just t _ => t
  | BinOp t _ _ => t
  | BorrowMut t _ => t
  | Pair t _ _ => t
  end.

Fixpoint check_type_of_val v t :=
  match v, t with
  | HLPL_bot, _ => true
  | HLPL_int _, TInt => true
  | HLPL_loc _ v, t => check_type_of_val v t
  | HLPL_ptr _, TRef _ => true
  | HLPL_pair v0 v1, TPair t0 t1 => check_type_of_val v0 t0 && check_type_of_val v1 t1
  | _, _ => false
  end.

Definition WellTypedState S bo :=
  forall sp, valid_spath S sp -> exists t, eval_type bo S sp t.

Definition WellTypedState' (S : HLPL_state) (bo : positive -> block * type) :=
  forall enc_x, valid_spath S (enc_x, []) ->
           check_type_of_val (S.[(enc_x, [])]) ((bo enc_x).2) = true.

Lemma WellTypedState_equiv :
  forall bo S, WellTypedState S bo <-> WellTypedState' S bo.
Proof.
  intros bo S ; split ; intro WTS.
Admitted. 

Definition WellTypedOperand S bo op :=
  match op with
  | IntConst t _ => t = TInt
  | Move t p =>
      forall sp,
        S |-{p} p => sp ->
           eval_type bo S sp t
  | Copy t p =>
      forall sp,
        S |-{p} p => sp ->
           eval_type bo S sp t
  end.

Definition WellTypedRValue S bo rv :=
  match rv with
  | Just t op =>
      WellTypedOperand S bo op /\ t = op_get_type op
  | BinOp t op_l op_r =>
      WellTypedOperand S bo op_l /\ WellTypedOperand S bo op_r /\
        TInt = op_get_type op_l /\ TInt = op_get_type op_r /\ t = TInt
  | BorrowMut t p =>
      exists t', t = TRef t' /\ forall sp, S |-{p} p => sp -> eval_type bo S sp t'
  | Pair t op_l op_r =>
      forall t0 t1,
      WellTypedOperand S bo op_l /\ WellTypedOperand S bo op_r /\
        t0 = op_get_type op_l /\ t1 = op_get_type op_r /\ t = (TPair t0 t1)
  end.

Fixpoint WellTypedStmt S bo stmt :=
  match stmt with
  | Assign p rv =>
      forall t sp,
        S |-{p} p => sp -> 
           WellTypedRValue S bo rv /\ t = rv_get_type rv /\ eval_type bo S sp t
  | Seq s1 s2 =>
      WellTypedStmt S bo s1 /\ WellTypedStmt S bo s2
  | _ => True
  end.

Lemma get_node_write_bot :
  forall S sp sp',
    get_node (S.[sp' <- bot].[sp]) <> botC ->
    get_node (S.[sp]) = get_node (S.[sp' <- bot].[sp]).
Proof.
  intros. replace botC with (get_node bot) in * by reflexivity.
  apply valid_get_node_sget_not_bot in H as Hvp.
  destruct (comparable_spaths sp sp').
  - subst. apply sset_not_prefix_valid in Hvp ; try apply strict_prefix_irrefl.
    rewrite sset_sget_equal in H ; congruence.
  - rewrite get_node_sset_sget_strict_prefix ; auto.
  - destruct H0 as (n & r & ?) ; subst. apply valid_spath_app in Hvp as (? & ?).
    apply valid_spath_write_bot in H0.
    rewrite sset_sget_equal in H1 ; auto. inversion H1 ; subst.
    rewrite nth_error_nil in H5 ; congruence.
  - symmetry in H0. rewrite sset_sget_disj ; auto.
Qed.

Lemma get_node_add_loc_post :
  forall S l sp sp',
    ~ prefix sp' sp ->
    get_node (S.[sp' <- loc (l, S.[sp'])].[sp]) = get_node (S.[sp]).
Proof. intros * pref. rewrite get_node_sset_sget_not_prefix ; auto. Qed.

Lemma get_node_add_loc_eq :
  forall S l sp,
    valid_spath S sp ->
    get_node (S.[sp <- loc (l, S.[sp])].[sp]) = (HLPL_locC l).
Proof. intros * valid_sp. rewrite sset_sget_equal ; auto. Qed.

Lemma get_node_add_loc_pre :
  forall S l sp vp,
    get_node (S.[sp <- loc (l,S.[sp])].[sp +++ [0%nat] ++ vp]) = get_node (S.[sp +++ vp]).
Proof.
  intros.
  destruct (decidable_valid_spath S sp).
  - rewrite sget_app, sset_sget_equal, vget_app ; auto. cbn.
    rewrite <- sget_app ; auto.
  - rewrite !sget_app, sset_invalid, !sget_invalid ; auto.
Qed.

Lemma valid_spath_is_loc :
  forall S l sp n vp,
    valid_spath (S.[sp <- loc (l, S.[sp])]) (sp +++ n :: vp) ->
    n = 0%nat.
Proof.
  intros * valid_sp. apply valid_spath_app in valid_sp as (valid_sp & valid_vp).
  rewrite <- sset_not_prefix_valid in valid_sp by (apply strict_prefix_irrefl).
  rewrite sset_sget_equal in valid_vp ; auto.
  destruct n ; inversion valid_vp ; subst ; auto.
  simpl in H2. rewrite nth_error_nil in H2 ; congruence.
Qed.

Definition add_loc_spath p q :=
  match (decidable_prefix' p q) with
  | inleft (existT r _) =>
      p +++ [0%nat] ++ r
  | _ => q
  end.

Definition remove_loc_spath p q :=
  match (decidable_prefix' p q) with
  | inleft (existT r _) =>
      p +++ (tl r)
  | _ => q
  end.

Lemma remove_add_loc_spath (p q : spath) :
  remove_loc_spath p (add_loc_spath p q) = q. 
Proof.
  unfold add_loc_spath, remove_loc_spath.
  destruct (decidable_prefix' p q) eqn:E.
  - destruct s as (r & ?). destruct (decidable_prefix' p (p +++ [0%nat] ++ r)) eqn:E'.
    * destruct s as (r' & ?). injection e0 ; intros. apply app_inv_head in H.
      rewrite <- e, H ; auto.
    * assert (prefix p ((p +++ [0%nat] ++ r))) by (exists ([0%nat] ++ r) ; auto). congruence.
  - rewrite E ; auto.
Qed.

Lemma not_prefix_add_loc_spath :
  forall ploc p,
    ~ prefix ploc p ->
    add_loc_spath ploc p = p.
Proof.
  intros * not_pref. unfold add_loc_spath. destruct (decidable_prefix' ploc p) ; auto.
  destruct s as (r & ?). assert (pref : prefix ploc p) by (exists r ; auto). contradiction.
Qed.

Lemma not_prefix_remove_loc_spath :
  forall ploc p,
    ~ prefix ploc p ->
    remove_loc_spath ploc p = p.
Proof.
  intros * not_pref. unfold remove_loc_spath.
  destruct (decidable_prefix' ploc p) ; auto.
  destruct s as (r & ?). assert (pref : prefix ploc p) by (exists r ; auto). contradiction.
Qed.

Lemma get_node_write_loc :
  forall S l sp sp',
    get_node (S.[sp <- loc (l, S.[sp])].[add_loc_spath sp sp']) = get_node (S.[sp']).
Proof.
  intros. unfold add_loc_spath. destruct (decidable_prefix' sp sp').
  - destruct s as (r & E). rewrite <- E. eapply get_node_add_loc_pre.
  - apply get_node_add_loc_post ; auto. 
Qed.

Lemma get_node_write_loc' :
  forall S l sp sp',
    sp <> sp' ->
    valid_spath (S.[sp <- loc (l, S.[sp])]) sp' ->
    get_node (S.[sp <- loc (l, S.[sp])].[sp']) = get_node (S.[remove_loc_spath sp sp']).
Proof.
  intros * eq valid_sp. unfold remove_loc_spath. destruct (decidable_prefix' sp sp').
  - destruct s as (r & E). rewrite <- E. destruct r ; simpl.
    * rewrite app_spath_vpath_nil_r in E. contradiction.
    * subst. pose proof (valid_spath_is_loc _ _ _ _ _ valid_sp) ; subst.
      apply valid_spath_app in valid_sp as (? & ?).
      rewrite <- sset_not_prefix_valid in H by (apply strict_prefix_irrefl).
      rewrite !sget_app, sset_sget_equal ; auto.
  - apply get_node_add_loc_post ; auto. 
Qed.

Lemma get_node_remove_loc :
  forall S l r p,
    get_node (S.[ r ]) = locC (l) ->
    get_node (S.[r <- S.[r +++ [0%nat] ] ].[ p ]) = get_node (S.[ (add_loc_spath r p) ]).
Proof.
  intros * loc. unfold add_loc_spath.
  destruct (decidable_prefix' r p) as [ (suff & ?) | ] ; subst.
  - rewrite sget_app, sset_sget_equal, <- sget_app, app_spath_vpath_assoc ; auto.
    apply valid_get_node_sget_not_bot. rewrite loc. simpl. auto.
  - rewrite get_node_sset_sget_not_prefix ; auto.
Qed.

Lemma get_node_remove_loc' :
  forall S l r p,
    p <> r ->
    valid_spath S p ->
    get_node (S.[ r ]) = locC (l) ->
    get_node (S.[r <- S.[r +++ [0%nat] ] ].[ remove_loc_spath r p ]) = get_node (S.[ p ]).
Proof.
  intros * neq vsp node. unfold remove_loc_spath.
  destruct (decidable_prefix' r p) as [ (suff & ?) | ] ; subst.
  - nodes_to_val.
    assert (valid_spath S r)
      by (apply get_not_bot_valid_spath; rewrite Heqh; discriminate).
    rewrite !sget_app, Heqh, sset_sget_equal ; auto. simpl.
    destruct suff.
    + rewrite app_spath_vpath_nil_r in neq. contradiction.
    + apply valid_spath_app in vsp as (_ & vsp). rewrite Heqh in vsp.
      inversion vsp ; subst. destruct n ; auto.
      simpl in H4. rewrite nth_error_nil in H4. discriminate.
  - rewrite get_node_sset_sget_not_prefix ; auto.
Qed.

Lemma eval_place_write_bot :
  forall S p sp sp',
    (S .[ sp' <- bot]) |-{p} p => sp -> S |-{p} p => sp.
Proof.
  intros * eval_p. inversion eval_p.
  apply sset_not_prefix_valid in H ; [ | apply not_strict_prefix_nil].
  constructor ; auto. induction H0.
  - constructor.
  - apply HLPL_No_Anon.Eval_cons with (q := q).
    + inversion Heval_proj ; subst ;
        econstructor ; auto ; erewrite get_node_write_bot ; eauto ; congruence.
    + eapply IHeval_path, valid_spath_write_bot, eval_proj_valid ; eauto.
  - apply HLPL_No_Anon.Eval_path_loc with (q := q).
    + inversion Heval_loc ; subst ;
      econstructor ; auto ; erewrite get_node_write_bot ; eauto ; congruence.
    + eapply IHeval_path, valid_spath_write_bot, eval_loc_valid ; eauto.
Qed.

Lemma eval_proj_write_loc :
  forall S l proj p q r,
    p <> r ->
    HLPL_No_Anon.eval_proj (S.[ r <- loc (l, S .[ r])]) proj
      (add_loc_spath r p) (add_loc_spath r q) ->
    HLPL_No_Anon.eval_proj S proj p q.
Proof.
  intros * p_not_r eval_proj. inversion eval_proj ; subst.
  - rewrite get_node_write_loc in * ; econstructor ; eauto.
  - rewrite get_node_write_loc in *. unfold add_loc_spath in H2.
    destruct (decidable_prefix' r p).
    * destruct s as ([ | n r'] & ?).
      ** rewrite app_spath_vpath_nil_r in e. congruence.
      ** inversion eval_proj ; subst.
         destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
         *** rewrite <- !app_spath_vpath_assoc, <- !app_assoc in H2.
             apply app_spath_vpath_inv_head, app_inv_head in H2.
             rewrite <- eq0, <- H2, app_spath_vpath_assoc. constructor. auto.
         *** rewrite <- app_spath_vpath_assoc in H2.
             assert (prefix r q) by (eexists ; eauto). congruence.
    * inversion eval_proj ; subst.
      rewrite not_prefix_add_loc_spath in eval_proj ; auto.
      inversion eval_proj ; subst.
      unfold add_loc_spath in H0. destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
      ** assert (strict_prefix r (p +++ [0%nat]))
         by (rewrite H0 ; exists 0%nat, r0 ;  reflexivity).
         apply strict_prefix_app_last in H1. contradiction.
      ** rewrite <- H0. constructor ; auto.
  - rewrite get_node_write_loc in *. unfold add_loc_spath in H2.
    destruct (decidable_prefix' r p).
    * destruct s as ([ | n r'] & ?).
      ** rewrite app_spath_vpath_nil_r in e. congruence.
      ** inversion eval_proj ; subst.
         destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
         *** rewrite <- !app_spath_vpath_assoc, <- !app_assoc in H2.
             apply app_spath_vpath_inv_head, app_inv_head in H2.
             rewrite <- eq0, <- H2, app_spath_vpath_assoc. constructor ; auto.
         *** rewrite <- app_spath_vpath_assoc in H2.
             assert (prefix r q) by (eexists ; eauto). congruence.
    * inversion eval_proj ; subst.
      rewrite not_prefix_add_loc_spath in eval_proj ; auto.
      inversion eval_proj ; subst.
      unfold add_loc_spath in H0. destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
      ** assert (strict_prefix r (p +++ [1%nat]))
           by (rewrite H0; exists 0%nat, r0 ; reflexivity).
         apply strict_prefix_app_last in H1. contradiction.
      ** rewrite <- H0. constructor ; auto.
Qed.

Lemma remove_loc_spath_app :
  forall p r n,
    p <> r -> remove_loc_spath r (p +++ [n]) = remove_loc_spath r p +++ [n].
Proof.
  intros * neq. unfold remove_loc_spath.
  destruct (decidable_prefix' r p) as [(s & ?) | ].
  - destruct (decidable_prefix' r (p +++ [n])) as [(s' & ?) | ].
    + rewrite <- e, <- app_spath_vpath_assoc, app_spath_vpath_inv_head in e0.
      rewrite e0. destruct s. 
      * rewrite app_spath_vpath_nil_r in e. congruence.
      * rewrite <- app_spath_vpath_assoc ; auto.
    + rewrite <- e in n0. assert (prefix r ((r +++ s) +++ [n]))
        by (rewrite <- app_spath_vpath_assoc; eexists ; eauto). congruence.
  - destruct (decidable_prefix' r (p +++ [n])) as [(s' & ?) | ] ; auto.
    rewrite <- e. apply app_spath_vpath_inv_head.
    destruct s' ; auto. assert (strict_prefix r (p +++ [n])) by (eexists ; eauto).
    apply strict_prefix_app_last in H. contradiction.
Qed.

Lemma add_loc_spath_app :
  forall r p n,
    p +++ [ n ] <> r -> add_loc_spath r (p +++ [ n ]) = add_loc_spath r p +++ [ n ].
Proof.
  intros * neq. unfold add_loc_spath.
  destruct (decidable_prefix' r p) as [(s & ?) | ?].
  - destruct (decidable_prefix' r (p +++ [ n ])) as [(s' & ?) | ?] ; subst.
    + rewrite <- app_spath_vpath_assoc, app_spath_vpath_inv_head in e0 ; subst.
      rewrite !app_spath_vpath_assoc ; auto.
    + assert (prefix r (_ +++ [ n ]))
        by (exists (s ++ [n]) ; rewrite app_spath_vpath_assoc ; auto). contradiction.
  - destruct (decidable_prefix' r (p +++ [ n ])) as [(s' & ?) | ?] ; subst.
    + induction s' using rev_ind.
      * rewrite app_nil_r, app_spath_vpath_nil_r in *. symmetry in e ; contradiction.
      * clear IHs'. pose proof e as e'.
        apply f_equal with (f := removelast) in e'. 
        rewrite app_spath_vpath_assoc, !removelast_app in e' ; auto. simpl in e'.
        rewrite !app_spath_vpath_nil_r in e'.
        assert (prefix  r p) by (exists s' ; auto). contradiction.
    + reflexivity.
Qed.

Lemma remove_loc_spath_remove_loc:
  forall r p n,
    remove_loc_spath r (r +++ n :: p) = r +++ p.
Proof.
  intros. unfold remove_loc_spath.
  destruct (decidable_prefix' r (r +++ n :: p)) as [(r' & eq) | npref ].
  - apply app_spath_vpath_inv_head in eq. subst ; auto.
  - assert (prefix r (r +++ n :: p)) by (exists (n :: p) ; auto). contradiction.
Qed.

Lemma add_loc_spath_eq:
  forall r, add_loc_spath r r = r +++ [0%nat].
Proof.
  intros. unfold add_loc_spath.
  destruct (decidable_prefix' r r) as [ (r' & eq) | npref].
  - rewrite <- app_spath_vpath_nil_r in eq.
    apply app_spath_vpath_inv_head in eq. rewrite eq, app_nil_r ; auto.
  - assert (pref : prefix r r) by reflexivity. contradiction.
Qed.

Lemma remove_loc_spath_eq:
  forall r, remove_loc_spath r r = r.
Proof.
  intros *. unfold remove_loc_spath.
  destruct (decidable_prefix' r r) as [(r' & eq) | npref ] ; auto.
  rewrite <- (app_spath_vpath_nil_r r) in eq at 2.
  apply app_spath_vpath_inv_head in eq ; subst. simpl.
  apply app_spath_vpath_nil_r.
Qed.

Lemma add_loc_spath_pref :
  forall r p, add_loc_spath r (r +++ p) = r +++ [0%nat] ++ p.
Proof.
  intros. unfold add_loc_spath.
  destruct (decidable_prefix' r (r +++ p)) as [ (r' & eq) | npref].
  - apply app_spath_vpath_inv_head in eq. congruence.
  - assert (pref : prefix r (r +++ p)) by (exists p ; auto). contradiction.
Qed.

Lemma add_loc_spath_not_pref :
  forall r p, p <> [] -> add_loc_spath (r +++ p) r = r.
Proof.
  intros *. unfold add_loc_spath.
  destruct (decidable_prefix' (r +++ p) r) as [(r' & eq) | npref ]; auto.
  rewrite <- app_spath_vpath_assoc, <- app_spath_vpath_nil_r in eq.
  apply app_spath_vpath_inv_head, list_basics.app_nil in eq as ( ? & ?) .
  contradiction.
Qed.

Lemma add_loc_spath_not_pref' :
  forall r p, ~ prefix r p -> add_loc_spath r p = p.
Proof.
  intros. unfold add_loc_spath. destruct (decidable_prefix' r p) as [(? & ?) | ?].
  - assert (prefix r p) by (exists x ; auto). contradiction.
  - reflexivity.
Qed.

Lemma eval_proj_write_loc' :
  forall S l proj p q r,
    p <> r -> is_fresh l S ->
    HLPL_No_Anon.eval_proj (S.[ r <- loc (l, S .[ r])]) proj p q ->
    HLPL_No_Anon.eval_proj S proj (remove_loc_spath r p) (remove_loc_spath r q).
Proof.
  intros * neq fresh eval_proj.
  inversion eval_proj ; subst.
  - assert (valid_spath (S .[ r <- HLPL_loc l (S .[ r])]) p).
    { apply valid_get_node_sget_not_bot. rewrite get_q. easy. }
    assert (valid_spath (S .[ r <- HLPL_loc l (S .[ r])]) q).
    { apply valid_get_node_sget_not_bot. rewrite get_q'. easy. }
    rewrite get_node_write_loc' in get_q ; auto.
    assert (loc : l0 <> l)
      by (eapply is_fresh_loc_id_neq ; eauto ; rewrite get_q ; auto).
    destruct (decidable_spath_eq q r).
    * subst. apply sset_not_prefix_valid in H0 ; try (apply strict_prefix_irrefl).
      rewrite sset_sget_equal in get_q' ; auto. injection get_q' as ->. easy.
    * rewrite get_node_write_loc' in get_q' ; auto.
      econstructor ; eauto.
  - assert (valid_spath (S .[ r <- HLPL_loc l (S .[ r])]) p).
    { apply valid_get_node_sget_not_bot. rewrite get_q. easy. }
    rewrite get_node_write_loc' in get_q ; auto.
    rewrite remove_loc_spath_app ; auto. constructor ; auto.
  - assert (valid_spath (S .[ r <- HLPL_loc l (S .[ r])]) p).
    { apply valid_get_node_sget_not_bot. rewrite get_q. easy. }
    rewrite get_node_write_loc' in get_q ; auto.
    rewrite remove_loc_spath_app ; auto. constructor ; auto.
Qed.

Lemma app_decidable_prefix :
  forall p q, remove_loc_spath p (p +++ q) = p +++ tail q.
Proof.
  intros. unfold remove_loc_spath. destruct (decidable_prefix' p (p +++ q)).
  - destruct s as (r & ?). apply app_spath_vpath_inv_head in e ; congruence.
  - assert (prefix p (p +++ q)) by (exists q ; auto). congruence.
Qed.

Lemma eval_path_write_loc' :
  forall S l P p q r,
    is_fresh l S ->
    HLPL_No_Anon.eval_path (S.[ r <- loc (l, (S .[ r]))]) P p q ->
    HLPL_No_Anon.eval_path S P (remove_loc_spath r p) (remove_loc_spath r q).
Proof.
  intros * fresh eval_path. induction eval_path ; intros.
  - constructor.
  - destruct (decidable_spath_eq p r).
    + subst. inversion Heval_proj ; subst.
      * rewrite sset_sget_equal in get_q. simpl in get_q. congruence.
        rewrite (sset_not_prefix_valid S _ r) by (apply strict_prefix_irrefl).
        apply valid_get_node_sget_not_bot.
        rewrite get_q. easy. 
      * rewrite sset_sget_equal in get_q. simpl in get_q ; congruence.
        rewrite (sset_not_prefix_valid S _ r) by (apply strict_prefix_irrefl).
        apply valid_get_node_sget_not_bot. rewrite get_q. easy.
      * rewrite sset_sget_equal in get_q. simpl in get_q ; congruence.
        rewrite (sset_not_prefix_valid S _ r) by (apply strict_prefix_irrefl).
        apply valid_get_node_sget_not_bot. rewrite get_q. easy.
    + econstructor ; [ eapply eval_proj_write_loc' | ] ; eauto.
  - inversion Heval_loc ; subst.
    destruct (decidable_spath_eq p r).
    + subst. rewrite app_decidable_prefix, app_spath_vpath_nil_r in IHeval_path.
      replace (remove_loc_spath r r) with (remove_loc_spath r (r +++ []))
        by (rewrite app_spath_vpath_nil_r ; auto).
      rewrite app_decidable_prefix, app_spath_vpath_nil_r ; auto.
    + eapply HLPL_No_Anon.Eval_path_loc
        with (q := (remove_loc_spath r (p +++ [0%nat]))) ; auto.
      rewrite get_node_write_loc' in get_q ; auto.
      rewrite remove_loc_spath_app ; auto. econstructor ; auto. rewrite get_q. easy.
      apply valid_get_node_sget_not_bot. rewrite get_q. easy.
Qed.

Lemma eval_place_write_loc :
  forall S l p r sp,
    is_fresh l S ->
    S.[ r <- loc (l, (S .[ r]))] |-{p} p => sp ->
    S |-{p} p => (remove_loc_spath r sp).
Proof.
  intros * fresh eval_pl. inversion eval_pl.
  rewrite <- sset_not_prefix_valid in H by apply not_strict_prefix_nil.
  constructor ; auto.
  replace (encode_var p.1, []) with (remove_loc_spath r (encode_var p.1, [])).
  apply eval_path_write_loc' with (l := l) ; auto.
  unfold remove_loc_spath.
  destruct (decidable_prefix' r (encode_var p.1, [])) as [(r' & ?) | ] ; auto.
  apply f_equal with (f := snd) in e as e'. apply list_basics.app_nil in e' as [? ->].
  easy.
Qed.

Lemma eval_path_end_loc :
  forall S l P p q r,
    get_node (S.[r]) = locC (l) ->
    not_state_contains (eq ptrC (l)) S ->
    HLPL_No_Anon.eval_path (S.[r <- S.[r +++ [0%nat] ] ]) P p q ->
    HLPL_No_Anon.eval_path S P (add_loc_spath r p) (add_loc_spath r q).
Proof.
  intros * get_node not_contains eval_path. induction eval_path.
  - constructor.
  - inversion Heval_proj ; subst.
    + econstructor ; eauto.
      rewrite get_node_remove_loc with (l := l) in get_q, get_q' ; auto.
      econstructor ; eauto.
    + erewrite get_node_remove_loc in get_q ; eauto. econstructor.
      * econstructor ; eauto.
      * destruct (decidable_spath_eq (p +++ [0%nat]) r) ; subst.
        ** eapply HLPL_No_Anon.Eval_path_loc ; eauto.
           rewrite add_loc_spath_not_pref, add_loc_spath_eq ; auto.
           apply Eval_Loc with (l := l) ; auto.
        ** rewrite add_loc_spath_app in IHeval_path ; auto.
    + erewrite get_node_remove_loc in get_q ; eauto. econstructor.
      * econstructor ; eauto.
      * destruct (decidable_spath_eq (p +++ [1%nat]) r) ; subst.
        ** eapply HLPL_No_Anon.Eval_path_loc ; eauto.
           rewrite add_loc_spath_not_pref, add_loc_spath_eq ; auto.
           apply Eval_Loc with (l := l) ; auto.
        ** rewrite add_loc_spath_app in IHeval_path ; auto.
  - inversion Heval_loc ; subst.
    rewrite get_node_remove_loc with (l := l) in get_q ; auto.
    destruct (decidable_spath_eq (p +++ [0%nat]) r) ; subst.
    + apply Eval_path_loc with (q := (add_loc_spath (p +++ [0%nat]) p) +++ [0%nat]).
      * apply Eval_Loc with (l := l0) ; auto.
      * apply Eval_path_loc with (q := (add_loc_spath (p +++ [0%nat]) (p +++ [0%nat]))) ;
          auto.
        replace (add_loc_spath (p +++ [0%nat]) (p +++ [0%nat])) with
          (add_loc_spath (p +++ [0%nat]) ((p +++ [0%nat]) +++ []))
          by (rewrite app_spath_vpath_nil_r ; auto).
        rewrite add_loc_spath_pref, app_nil_r, add_loc_spath_not_pref ; auto.
        apply Eval_Loc with (l := l) ; auto.
    + eapply Eval_path_loc ; eauto. rewrite add_loc_spath_app ; auto.
      apply Eval_Loc with (l := l0) ; auto.
Qed.

Lemma eval_place_end_loc :
  forall S l p r sp,
    get_node (S.[r]) = locC (l) ->
    not_state_contains (eq ptrC (l)) S ->
    (S.[r <- S.[r +++ [0%nat] ] ]) |-{p} p => sp ->
    S |-{p} p => (add_loc_spath r sp).
Proof.
  intros * node not_contains eval_p. inversion eval_p.
  apply sset_not_prefix_valid in H ; try (apply not_strict_prefix_nil).
  constructor ; auto. remember (encode_var p.1, []) as q.
    destruct (decidable_spath_eq q r).
    + subst q. rewrite !H1 in *. apply Eval_path_loc with (q := (r +++ [0%nat])).
      * apply Eval_Loc with (l := l) ; auto.
      * rewrite <- add_loc_spath_eq. apply eval_path_end_loc with (l := l) ; auto.
    + rewrite <- (not_prefix_add_loc_spath r q) ; subst.
      * apply eval_path_end_loc with (l := l) ; auto.
      * apply prove_not_prefix ; auto. apply not_strict_prefix_nil.
Qed.

Lemma eval_place_reorg :
  forall S1 S2 p sp,
    reorg S1 S2 ->
    S2 |-{p} p => sp ->
    exists sp', S1 |-{p} p => sp'.
Proof.
  intros * reorg eval_place. induction reorg.
  - exists sp. apply eval_place_write_bot with (sp' := p0) ; auto.
  - exists (add_loc_spath p0 sp). inversion eval_place ; subst.
    apply eval_place_end_loc with (l := l) ; auto.
Qed.

Lemma eval_place_reorg_star :
  forall S1 S2 p sp,
    clos_refl_trans reorg S1 S2 ->
    S2 |-{p} p => sp ->
    exists sp', S1 |-{p} p => sp'.
Proof.
  intros * reorgs. generalize dependent sp.
  induction reorgs ; intros * eval_p.
  - eapply eval_place_reorg ; eauto.
  - exists sp ; assumption.
  - destruct (IHreorgs2 _ eval_p) as (sp' & eval_p').
    apply (IHreorgs1 sp' eval_p').
Qed.

Lemma eval_type_val_vset :
  forall vi vp0 vp1 ti t,
    ~ vstrict_prefix vp1 vp0 ->
    eval_type_val vi ti vp0 t <-> eval_type_val (vi.[[vp1 <- bot]]) ti vp0 t.
Proof.
  intros ; split ; intros.
  - apply off_vpath_equiv_eval_type in H0 as (off & ?).
    apply off_vpath_equiv_eval_type. exists off. apply off_vpath_equiv_vset ; auto.
  - apply off_vpath_equiv_eval_type in H0 as (off & ?).
    apply off_vpath_equiv_eval_type. exists off. eapply off_vpath_equiv_vset ; eauto.
Qed.

Lemma eval_type_val_write_bot :
  forall vi vp vp' ti t,
    valid_vpath (vi.[[vp' <- bot]]) vp ->
    eval_type_val vi ti vp t ->
    eval_type_val (vi.[[vp' <- bot]]) ti vp t.
Proof.
  intros. destruct (comparable_vpaths vp vp').
  - subst. apply eval_type_val_vset ; auto. apply vstrict_prefix_irrefl.
  - eapply off_vpath_equiv_eval_type in H0 as (off & ?).
    apply off_vpath_equiv_eval_type. exists off.
    apply off_vpath_equiv_vset ; auto. intros ?.
    apply not_vprefix_left_vstrict_prefix_right in H2.
    apply vstrict_prefix_is_vprefix in H1 ; auto.
  - destruct H1 as (n & r & <-). apply valid_vpath_app in H as [? ?].
    apply vset_not_prefix_valid_rev in H ; try (apply vstrict_prefix_irrefl).
    rewrite vset_vget_equal in H1 ; auto.
    inversion H1 ; subst. rewrite nth_error_nil in H5. congruence.
  - eapply off_vpath_equiv_eval_type in H0 as (off & ?).
    apply off_vpath_equiv_eval_type. exists off.
    apply off_vpath_equiv_vset ; auto.
    symmetry in H1. apply not_vstrict_prefix_vdisj in H1 ; auto.
Qed.

Lemma eval_type_write_bot :
  forall bo S sp sp' t,
    valid_spath (S .[ sp' <- bot]) sp ->
    eval_type bo S sp t ->
    eval_type bo (S .[ sp' <- bot]) sp t.
Proof.
  intros. destruct (bo sp.1) eqn:E.
  destruct (Pos.eqb_spec sp.1 sp'.1).
  - inversion H0 ; subst. econstructor ; eauto.
    * apply sset_not_prefix_valid ; auto. apply not_strict_prefix_nil.
    * rewrite spath_var_app_vpath with (p := sp'), <- e, sset_sget_prefix ; auto.
      apply eval_type_val_write_bot ; auto.
      rewrite spath_var_app_vpath with (p := sp) in H.
      apply valid_spath_app in H as (? & ?).
      rewrite <- sset_sget_prefix, e, <- spath_var_app_vpath, <- e ; auto.
  - apply addr_spath_equiv_eval_type in H0 as (addr & ?).
    apply addr_spath_equiv_eval_type. exists addr.
    apply addr_spath_equiv_sset ; auto.
    intros (? & ?). rewrite <- H1 in n. simpl fst in n ; auto.
Qed.
  
Lemma eval_type_remove_loc :
  forall bo S sp sp' l t,
    get_node (S.[ sp' ]) = locC (l) ->
    valid_spath (S .[ sp' <- S.[sp' +++ [0%nat] ] ]) sp ->
    eval_type bo S (add_loc_spath sp' sp) t ->
    eval_type bo (S .[  sp' <- S.[sp' +++ [0%nat] ] ]) sp t.
Proof.
  intros * node vsp type.
  apply addr_spath_equiv_eval_type.
  apply addr_spath_equiv_eval_type in type as (addr & equiv).
  destruct (decidable_prefix sp' sp) as [ (r & eq) | npref ] ; exists addr.
  - subst. rewrite add_loc_spath_pref in equiv.
    eapply remove_loc_addr_spath_equiv_suffix ; eauto. split ; auto.
    apply get_not_bot_valid_spath. nodes_to_val. easy.
  - apply addr_spath_equiv_sset ; auto.
    rewrite add_loc_spath_not_pref' in equiv ; auto.
Qed.

Lemma eval_operand_preserves_eval_place : 
  forall S S' p sp op v,
    S' |-{p} p => sp ->
    S |-{op} op => (v, S') ->
    S |-{p} p => sp.
Proof.
  intros * eval_p eval_op. inversion eval_op ; subst ; auto.
  apply eval_place_write_bot with (sp' := pi) ; auto.
Qed.

Lemma eval_rvalue_preserves_eval_place : 
  forall S S' p sp rv v,
    S' |-{p} p => sp ->
    S |-{rv} rv => (v, S') ->
    exists sp', S |-{p} p => sp'.
Proof.
  pose proof eval_operand_preserves_eval_place.
  intros * eval_p eval_rv. inversion eval_rv ; subst ; eauto.
  eexists ; eapply eval_place_write_loc ; eauto.
Qed.

Lemma eval_stmt_preserves_eval_place : 
  forall S S' p sp s v,
    S' |-{p} p => sp ->
    S |-{stmt} s => v, S' ->
    exists sp', S |-{p} p => sp'.
Proof.
  intros * eval_place eval_stmt. generalize dependent sp.
  induction eval_stmt ; intros * eval_place ; eauto.
  - apply IHeval_stmt2 in eval_place as (sp' & eval_place').
    apply IHeval_stmt1 in eval_place' as (sp'' & eval_place''). eauto.
  - inversion Hstore ; subst.
    eapply eval_rvalue_preserves_eval_place in eval_rv as (sp' & eval_p') ; eauto.
    admit.
  - destruct (IHeval_stmt _ eval_place) as (sp' & eval_place').
    apply (eval_place_reorg_star _ _ _ _ Hreorg eval_place').
Abort.

Lemma addr_spath_equiv_add_loc :
  forall bo S l addr t sp sp_loc,
    valid_spath (S.[sp_loc <- loc (l, S.[sp_loc])]) sp ->
    addr ~^{bo, S.[sp_loc <- loc (l, S.[sp_loc])], t} sp <->
    addr ~^{bo, S, t} (remove_loc_spath sp_loc sp).
Proof.
  intros * valid_sp. unfold remove_loc_spath.
  destruct (decidable_prefix' sp_loc sp) as [ (r & ?) | ].
  - destruct r.
    + rewrite app_spath_vpath_nil_r in *. subst. split ; intros equiv.
      * rewrite addr_spath_equiv_sset_equal ; split ; eauto.
        apply sset_not_prefix_valid in valid_sp ; try apply (strict_prefix_irrefl).
        rewrite spath_var_app_vpath in valid_sp.
        apply valid_spath_app in valid_sp as (? & _) ; auto.
      * eapply proj1, addr_spath_equiv_sset_equal ; auto.
    + simpl. subst. rewrite (valid_spath_is_loc _ _ _ _ _ valid_sp) in *.
      split ; intros equiv.
      * apply add_loc_addr_spath_equiv_suffix with (l := l) ; split ; auto.
        apply valid_spath_app in valid_sp as (? & _).
        apply sset_not_prefix_valid in H ; auto. apply strict_prefix_irrefl.
      * eapply proj1, add_loc_addr_spath_equiv_suffix ; auto.
  - rewrite <- addr_spath_equiv_sset ; auto.
Qed.

Lemma add_loc_welltyped_operand :
  forall bo S op sp l,
    is_fresh l S ->
    WellTypedOperand S bo op ->
    WellTypedOperand (S.[sp <- loc (l, S.[sp])]) bo op.
Proof.
  intros * fresh WTO. destruct op ; auto ; simpl in * ; intros * eval_pl.
  - apply eval_place_valid in eval_pl as valid_sp.
    apply eval_place_write_loc in eval_pl ; auto. specialize (WTO _ eval_pl).
    apply addr_spath_equiv_eval_type in WTO as (addr & equiv).
    eapply addr_spath_equiv_eval_type, ex_intro, addr_spath_equiv_add_loc ; eauto.
  - apply eval_place_valid in eval_pl as valid_sp.
    apply eval_place_write_loc in eval_pl ; auto. specialize (WTO _ eval_pl).
    apply addr_spath_equiv_eval_type in WTO as (addr & equiv).
    eapply addr_spath_equiv_eval_type, ex_intro, addr_spath_equiv_add_loc ; eauto.
Qed.

Lemma eval_operand_preserves_valid_spath :
  forall S S' sp v op,
    S |-{op} op => (v, S') ->
    valid_spath S' sp ->
    valid_spath S sp.
Proof.                    
  intros * eval_op vsp.
  inversion eval_op ; subst ; auto. eapply valid_spath_write_bot ; eauto.
  Qed.

Lemma eval_operand_preserves_eval_type :
  forall bo S S' sp v t op,
    S |-{op} op => (v, S') ->
    eval_type bo S sp t ->
    valid_spath S' sp ->
    eval_type bo S' sp t.
Proof.                    
  intros * eval_op eval_type vsp.
  inversion eval_op ; subst ; auto.
  apply eval_type_write_bot ; auto.
Qed.

Lemma eval_operand_preserves_welltyped_op :
  forall bo S S' v op op',
    S |-{op} op' => (v, S') ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.                    
  intros * eval_op WTO. inversion eval_op ; subst ; auto.
  destruct op ; simpl in WTO ; auto ; intros ? ?.
  - apply eval_place_valid in H as Hvp.
    eapply eval_type_write_bot, WTO, eval_place_write_bot ; eauto.
  - apply eval_place_valid in H as Hvp.
    eapply eval_type_write_bot, WTO, eval_place_write_bot ; eauto.
Qed.

Lemma eval_rvalue_preserves_eval_type :
  forall bo S S' sp v t rv,
    S |-{rv} rv => (v, S') ->
    eval_type bo S sp t ->
    exists sp', valid_spath S' sp' -> eval_type bo S' sp' t.
Proof.
  intros * eval_rv eval_type.
  inversion eval_rv ; subst ; auto.
  - exists sp ; intro vsp. eapply eval_operand_preserves_eval_type ; eauto.
  - exists sp ; intro vsp. repeat (eapply eval_operand_preserves_eval_type ; eauto).
    eapply eval_operand_preserves_valid_spath ; eauto.
  - exists sp ; intro vsp. apply addr_spath_equiv_eval_type.
    apply addr_spath_equiv_eval_type in eval_type as (addr & ?). exists addr ; auto.
  - exists (add_loc_spath pi sp) ; intro vsp. eapply addr_spath_equiv_eval_type.
    eapply addr_spath_equiv_eval_type in eval_type as (addr & ?). exists addr.
    rewrite <- (remove_add_loc_spath pi sp) in *.
    apply addr_spath_equiv_add_loc ; auto.
    rewrite !(remove_add_loc_spath pi sp) in * ; auto.
  - exists sp ; intro vsp.
    repeat (eapply eval_operand_preserves_eval_type ; eauto).
    eapply eval_operand_preserves_valid_spath ; eauto.
Abort.

(*
Variant eval_rv_spath : rvalue -> spath -> spath -> Prop :=
  | Eval_rv_spath_just :
    forall sp t op, eval_rv_spath (Just t op) sp sp
  | Eval_rv_spath_binop:
    forall sp t op_l op_r, eval_rv_spath (BinOp t op_l op_r) sp sp
  | Eval_rv_spath_pair:
    forall sp t op_l op_r, eval_rv_spath (Pair t op_l op_r) sp sp
  | Eval_rv_spath_borrowmut_noloc :
    forall p sp', S |-{p} p => sp' -> .
  end.

Lemma eval_rvalue_preserves_eval_type :
  forall bo S S' p sp sp' v t rv,
    S |-{rv} rv => (v, S') ->
    valid_spath S' sp' ->
    eval_type bo S sp t ->
    eval_type bo S' sp' t.
Proof.
  intros * eval_rv eval_p eval_p' eval_type.
  apply eval_place_valid in eval_p as vsp.
  apply eval_place_valid in eval_p' as vsp'.
  inversion eval_rv ; subst.
  - eapply eval_operand_preserves_eval_type ; eauto.
    eapply eval_operand_preserves_eval_place in eval_p' ; eauto.
    assert (sp = sp') by (apply eval_place_deterministic).
*)


Lemma eval_rvalue_preserves_welltyped_op :
  forall bo S S' v op rv,
    S |-{rv} rv => (v, S') ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.                    
  intros * eval_rv WTO. inversion eval_rv ; subst ; auto.
  - repeat (eapply eval_operand_preserves_welltyped_op ; eauto).
  - repeat (eapply eval_operand_preserves_welltyped_op ; eauto).
  - apply add_loc_welltyped_operand ; auto.
  - repeat (eapply eval_operand_preserves_welltyped_op ; eauto).
Qed.

Lemma eval_operand_preserves_welltyped_rv :
  forall bo S S' v rv op,
    S |-{op} op => (v, S') ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * eval_op WTRV. destruct rv ; simpl in * ; auto.
  - destruct WTRV as (WTO & E). split ; auto.
    eapply eval_operand_preserves_welltyped_op ; eauto.
  - destruct WTRV as (WTO_l & WTO_r & E & E' & E''). repeat split ; auto ;
      eapply eval_operand_preserves_welltyped_op ; eauto.
  - destruct WTRV as (t' & Htype & Hplace_rec). exists t' ; split ; auto.
    intros sp Hplace.
    eapply eval_operand_preserves_eval_place in Hplace as Hplace' ; eauto.
    inversion eval_op ; subst ; auto. apply eval_type_write_bot ; auto.
    apply eval_place_valid with (p := p) ; auto.
  - intros. destruct (WTRV t0 t1) as (WTO_l & WTO_r & E & E' & E'').
    repeat split ; auto ;
      eapply eval_operand_preserves_welltyped_op ; eauto.
Qed.

Lemma eval_rvalue_preserves_welltyped_rv :
  forall bo S S' v rv rv',
    S |-{rv} rv' => (v, S') ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * eval_rv WTRV. destruct rv ; simpl in * ; auto.
  - destruct WTRV as (WTO & E).
    split ; auto. eapply eval_rvalue_preserves_welltyped_op ; eauto.
  - destruct WTRV as (WTO_l & WTO_r & E & E' & E'').
    repeat split ; auto ; eapply eval_rvalue_preserves_welltyped_op ; eauto.
  - destruct WTRV as (t' & type & Hplace_rec).
    exists t' ; split ; auto. intros * eval_p.
    inversion eval_rv ; subst ; auto.
    + apply eval_place_valid in eval_p as vsp.
      eapply eval_operand_preserves_eval_type ; eauto.
      apply Hplace_rec. eapply eval_operand_preserves_eval_place ; eauto.
    + apply eval_place_valid in eval_p as vsp.
      eapply eval_operand_preserves_eval_type ; eauto.
      eapply eval_operand_preserves_eval_type ; eauto.
      * apply Hplace_rec.
        eapply eval_operand_preserves_eval_place with (S' := S'0); eauto.
        eapply eval_operand_preserves_eval_place with (S' := S'); eauto.
      * eapply eval_operand_preserves_valid_spath ; eauto.
    + apply eval_place_valid in eval_p as vsp.
      apply eval_place_write_loc in eval_p ; auto.
      specialize (Hplace_rec _ eval_p).
      apply addr_spath_equiv_eval_type in Hplace_rec as (addr & equiv).
      apply addr_spath_equiv_eval_type.
      exists addr. apply addr_spath_equiv_add_loc ; auto.
    + eapply eval_operand_preserves_eval_place in eval_p as eval_p' ; eauto.
      eapply eval_operand_preserves_eval_place in eval_p' as eval_p'' ; eauto.
      apply eval_place_valid in eval_p as vsp.
      apply eval_place_valid in eval_p' as vsp'.
      apply eval_place_valid in eval_p'' as vsp''.
      eapply eval_operand_preserves_eval_type with (S := S'0) ; eauto.
      eapply eval_operand_preserves_eval_type with (S := S) ; eauto.
  - intros. destruct (WTRV t0 t1) as (WTO_l & WTO_r & E & E' & E'').
    repeat split ; auto ; eapply eval_rvalue_preserves_welltyped_op ; eauto.
Qed.

Lemma reorg_preserves_welltyped_op :
  forall bo S S' op,
    reorg S S' ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.
  intros * reorg WTO. pose proof reorg as reorg'.
  destruct reorg ; destruct op ; simpl in * ; auto ; intros.
  - apply eval_type_write_bot.
    + eapply eval_place_valid ; eauto.
    + apply eval_place_write_bot in H0. eauto.
  - apply eval_type_write_bot.
    + eapply eval_place_valid ; eauto.
    + apply eval_place_write_bot in H0. eauto.
  - apply eval_type_remove_loc with (l := l) ; auto.
    + eapply eval_place_valid ; eauto.
    + eapply eval_place_reorg in reorg' as (sp' & eval_p') ; eauto. eapply WTO ; eauto.
      apply eval_place_end_loc with (l := l) ; auto.
  - apply eval_type_remove_loc with (l := l) ; auto.
    + eapply eval_place_valid ; eauto.
    + eapply eval_place_reorg in reorg' as (sp' & eval_p') ; eauto. eapply WTO ; eauto.
      apply eval_place_end_loc with (l := l) ; auto.
Qed.

Lemma reorg_preserves_welltyped_rv :
  forall bo S S' rv ,
    reorg S S' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * reorg WTRV. pose proof reorg as reorg'.
  destruct reorg ; destruct rv ; simpl in * ; auto ; intros.
  - destruct WTRV as (WTO & type). split ; auto.
    apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (WTO_l & WTO_r & type_l & type_r & type). repeat split ; auto ;
      apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (t' & type & ?). exists t' ; split ; auto.
    intros sp eval_p. apply eval_place_write_bot in eval_p as eval_p'.
    apply eval_place_valid in eval_p as vsp.
    apply eval_place_valid in eval_p' as vsp'.
    apply eval_type_write_bot ; auto.
  - destruct (WTRV t0 t1) as (WTO_l & WTO_r & type_l & type_r & type).
    repeat split ; auto ; apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (WTO & type). split ; auto.
    apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (WTO_l & WTO_r & type_l & type_r & type). repeat split ; auto ;
      apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (t' & type & ?). exists t' ; split ; auto.
    intros sp eval_p. apply eval_place_valid in eval_p as vsp.
    apply eval_type_remove_loc with (l := l) ; auto.
    apply H1. apply eval_place_end_loc with (l := l) ; auto.
  - destruct (WTRV t0 t1) as (WTO_l & WTO_r & type_l & type_r & type).
    repeat split ; auto ; apply reorg_preserves_welltyped_op with (S := S) ; auto.
Qed.

Lemma reorg_preserves_welltyped_stmt :
  forall bo S S' stmt,
    reorg S S' ->
    WellTypedStmt S bo stmt ->
    WellTypedStmt S' bo stmt.
Proof.
  intros * reorg WTS. pose proof reorg as reorg'.
  induction stmt ; simpl in * ; auto ; intros.
  - destruct reorg.
    + apply eval_place_valid in H as vsp.
      apply eval_place_write_bot in H.
      destruct (WTS t _ H) as (? & ? & ?) ; auto.
      repeat split ; auto.
      * apply reorg_preserves_welltyped_rv with (S := S) ; auto.
      * apply eval_type_write_bot ; auto.
    + apply eval_place_valid in H as vsp.
      apply eval_place_end_loc with (l := l) in H ; auto.
      destruct (WTS t _ H) as (? & ? & ?) ; auto. repeat split ; auto.
      * apply reorg_preserves_welltyped_rv with (S := S) ; auto.
      * apply eval_type_remove_loc with (l := l) ; auto.
  - destruct WTS as (WTS1 & WTS2).
    split ; auto.
Qed.

Lemma reorg_star_preserves_welltyped_op :
  forall bo S S' op,
    clos_refl_trans reorg S S' ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.
  intros * reorg WTO. induction reorg ; auto.
  apply reorg_preserves_welltyped_op with (S := x) ; auto.
Qed.

Lemma reorg_star_preserves_welltyped_rv :
  forall bo S S' rv ,
    clos_refl_trans reorg S S' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * reorg WTRV. induction reorg ; auto.
  apply reorg_preserves_welltyped_rv with (S := x) ; auto.
Qed.

Lemma reorg_star_preserves_welltyped_stmt :
  forall bo S S' stmt,
    clos_refl_trans reorg S S' ->
    WellTypedStmt S bo stmt ->
    WellTypedStmt S' bo stmt.
Proof.
  intros * reorg WTRV. induction reorg ; auto.
  apply reorg_preserves_welltyped_stmt with (S := x) ; auto.
Qed .

Lemma store_preserves_welltyped_stmt :
  forall bo S S' p sp t s v,
    WellTypedStmt S bo s ->
    S |-{p} p => sp ->
    eval_type bo S sp t ->
    store p (v, S) S' ->
    WellTypedStmt S' bo s.
Proof.
Abort.

Lemma eval_stmt_preserves_welltyped_op :
  forall bo S S' v op s,
    S |-{stmt} s => v, S' ->
    WellTypedState S bo ->
    WellTypedStmt S bo s ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.
  intros * eval_stmt WTS WTSt WTO. induction eval_stmt ; subst ; auto.
Abort.

Lemma eval_stmt_preserves_welltyped_rv :
  forall bo S S' v rv s,
    S |-{stmt} s => v, S' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * eval_stmt WTRV. induction eval_stmt ; auto. destruct vS'.
  - apply (eval_rvalue_preserves_welltyped_rv _ _ _ _ _ _ eval_rv) in WTRV.
    admit.
  - apply IHeval_stmt.
Abort.

Lemma eval_stmt_preserves_welltyped_stmt :
  forall bo S S' v s s',
    S |-{stmt} s' => v, S' ->
    WellTypedStmt S bo s ->
    WellTypedStmt S' bo s.
Proof.
  intros * eval_stmt WTO. induction s ; auto ; simpl in *.
  - intros * eval_p. admit.
  - destruct WTO as (WTO1%IHs1 & WTO2%IHs2). split ; auto.
Abort.

Lemma HLPL_PL_Read :
  forall blockof addrof S Spl p sp v t,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{p} p => sp ->
    eval_type blockof S sp t ->
    S.[sp] = v ->
    exists vl vl', 
      read Spl p t vl /\
        concr_hlpl_val addrof v t vl' /\
        le_block vl vl'.
Proof.
  intros bo ao S Spl p sp v t Hle Hplace Heval_type HS_sp.
  destruct (eval_place_hlpl_pl_equiv _ _ _ _ _ _ _ Hle Hplace Heval_type)
    as (addr & Hplace_pl & Hequiv).
  pose proof (eval_place_valid _ _ _ Hplace) as Hvsp.
  destruct Hle as (Spl' & HComp & Hconcr & Henv & Hmem).
  destruct
    (state_concr_implies_val_concr_at_addr bo ao _ _ _ _ _ _ Hconcr Hvsp HS_sp Hequiv)
    as [bytes [ Hconcr_val Hlu] ].
  apply ex_intro with (x := bytes) in Hlu as Hlu'.
  Search le_mem.
  apply le_mem_implies_lookup_equiv with (S1 := Spl) in Hlu' as [bytes' Hlu'] ; auto.
  exists bytes', bytes ; repeat split ; try assumption.
  * eapply Read ; eauto.
  * eapply le_mem_implies_le_block_at_addr ; eauto.
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
  - intros x enc_x Hvar Hbot. eapply Hblock ; eauto.
    destruct (peq sp.1 enc_x).
    * rewrite <- e. apply valid_spath_implies_valid_spath_var ; auto.
    * rewrite <-  sset_not_prefix_valid in Hbot ; auto. apply not_strict_prefix_nil.
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
  forall blockof addrof S Spl op t vS1,
    le_pl_hlpl blockof addrof Spl S ->
    WellTypedOperand S blockof op ->
    op_get_type op = t ->
    S |-{op} op => vS1 ->
    exists vl vl',
      Spl |-{op-pl} op => vl /\
      le_pl_hlpl blockof addrof Spl vS1.2 /\
      concr_hlpl_val addrof vS1.1 t vl' /\
      le_block vl vl'.
Proof.
  intros bo ao S Spl op t vS1 Hle HWTO Htype Heval.
  pose proof Hle as Htemp ;
    destruct Htemp as (Spl' & HComp & Hconcr & (Hle_env & Hle_mem)).
  pose proof proj1 Hconcr as Hconcr_mem.
  pose proof proj2 Hconcr as Hconcr_env.
  induction Heval eqn:E.
  - exists (make_int64 n), (make_int64 n). simpl in * ; subst.
    repeat split ; try constructor ; auto ; repeat constructor.
  - specialize (HWTO _ Heval_place). simpl in * ; subst.
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ Hle Heval_place HWTO eq_refl)
    as (bytes & bytes' & Hread & Hconcr_val & Hle_val).
    exists bytes, bytes' ; repeat split ; simpl ; auto.
    + constructor ; auto.
    + apply (concr_val_equiv_concr_copy_val ao _ _ _ _ Hcopy_val) ; auto.
  - simpl in Htype ; subst.
    specialize (HWTO _ e).
    destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ Hle e HWTO eq_refl)
    as (bytes & bytes' & Hread & Hconcr_val & Hle_block).
    exists bytes, bytes' ; repeat split ; auto.
    + constructor ; auto.
    + inversion Hread. simpl.
      exists (Spl'.m.[ addr <- repeat Undef (sizeof t) : t]).
      split ; [ idtac | split ] ; auto.
      * apply sset_preserves_compatibility ; auto.
        unfold not_contains_loc. not_contains.
      * apply concr_state_write_at_addr ; auto ; [ apply Concr_bot ; auto | ].
        eapply read_addr_spath_equiv_equiv ; eauto.
      * etransitivity ; eauto.
        eapply le_pl_write_at_addr_r ; eauto ; try reflexivity.
        eapply le_pl_write_at_addr ; try constructor ; eauto .
        apply le_block_poison. apply Forall2_length in Hle_block.
        apply concr_val_size in Hconcr_val. congruence.
Qed.

Lemma le_pl_hlpl_write_loc :
  forall S Spl bo ao l addr t pi,
    le_pl_hlpl bo ao Spl S ->
    addr ~^{bo, S, t} pi ->
    is_fresh l S ->
    valid_spath S (pi.1, []) ->
    le_pl_hlpl bo (fun l0 : nat => if (l =? l0)%nat then Some (addr, t) else ao l0) Spl
      (S .[ pi <- HLPL_loc l (S .[ pi])]).
Proof.
  intros S Spl bo ao l addr t pi (Spl' & Hcomp & Hconcr & Hle) Hequiv Hfresh. 
  exists Spl'. split ; [ | split ].
  - destruct Hcomp. split.
    + intros. apply block_dom0 with (x := x) ; auto.
      destruct (comparable_spaths pi (enc_x, [])).
      * apply f_equal with (f := fst) in H2. simpl in H2. congruence.
      * apply not_strict_prefix_nil in H2 ; easy.
      * destruct H2 as (n & r & ?). apply f_equal with (f := fst) in H2.
        simpl in H2. rewrite H2 ; auto.
      * rewrite <- sset_not_prefix_valid in H1 ; auto. apply not_strict_prefix_nil.
    + intros. destruct (comparable_spaths sp pi).
      * subst. apply addr_spath_equiv_implies_valid_spath in Hequiv as Hvp.
        rewrite sset_sget_equal in H1 ; auto. injection H1 as <-.
        rewrite Nat.eqb_refl.
        assert (addr0 ~^{bo, S, t0} pi)
          by (eapply addr_spath_equiv_sset_equal ; split ; eauto).
        destruct (addr_spath_equiv_deterministic _ _ _ _ _ _ _ H1 Hequiv) as [-> ->].
        auto.
      * rewrite get_node_sset_sget_strict_prefix in H1 ; auto.
        assert (l0 <> l) by (eapply is_fresh_loc_id_neq ; eauto ; rewrite H1; auto).
        apply Nat.eqb_neq in H3. rewrite Nat.eqb_sym, H3.
        eapply correct_addrof0 ; eauto. apply addr_spath_equiv_sset in H0 ; auto.
        apply not_prefix_left_strict_prefix_right ; auto.
      * apply addr_spath_equiv_implies_valid_spath in Hequiv as Hvsp.
        destruct H2 as (n & r & <-). rewrite sget_app, sset_sget_equal in H1 ; auto.
        rewrite vget_cons in H1.
        destruct n ; simpl in H1.
        ** rewrite <- sget_app in H1.
           assert (l0 <> l)
             by (eapply is_fresh_loc_id_neq ; eauto ; simpl ; rewrite H1; auto).
           apply Nat.eqb_neq in H2. rewrite Nat.eqb_sym, H2.
           eapply correct_addrof0 ; eauto.
           eapply add_loc_addr_spath_equiv_suffix ; eauto.
        ** (* TODO ask Alban *) replace (HLPL_bot) with bot in H1 by reflexivity.
           rewrite nth_error_nil, vget_bot in H1. simpl in H1. congruence.
      * symmetry in H2. rewrite sset_sget_disj in H1 ; auto.
        assert (l0 <> l) by (eapply is_fresh_loc_id_neq ; eauto ; rewrite H1 ; auto).
        apply Nat.eqb_neq in H3. rewrite Nat.eqb_sym, H3.
        eapply correct_addrof0 ; eauto. apply addr_spath_equiv_sset in H0 ; auto.
        apply not_prefix_disj ; auto.
    + intros. destruct (comparable_spaths pi sp).
      * subst. exists addr, t. apply addr_spath_equiv_sset_equal ; auto.
      * destruct H1 as (n & r & ?) ; subst.
        apply addr_spath_equiv_implies_valid_spath in Hequiv as Hvp.
        rewrite sget_app, sset_sget_equal, vget_cons in H0 ; auto.
        destruct n ; simpl in H0.
        ** rewrite <- sget_app in H0.
           destruct (reachable_loc0 _ _ H0) as (addr0 & t0 & ?).
           exists addr0, t0. replace (_ :: _) with ([0%nat] ++ r) by reflexivity.
           apply add_loc_addr_spath_equiv_suffix ; auto.
        ** replace HLPL_bot with bot in H0 by reflexivity.
           rewrite nth_error_nil, vget_bot in H0. simpl in H0. congruence.
      * rewrite get_node_sset_sget_strict_prefix in H0 ; auto.
        destruct (reachable_loc0 l0 sp H0) as (addr0 & t0 & ?).
        exists addr0, t0. apply addr_spath_equiv_sset ; auto.
        apply not_prefix_left_strict_prefix_right ; auto.
      * rewrite sset_sget_disj in H0 ; auto.
        destruct (reachable_loc0 l0 sp H0) as (addr0 & t0 & ?).
        exists addr0, t0. apply addr_spath_equiv_sset ; auto.
        apply not_prefix_disj ; auto.
  - destruct Hconcr as (? & ?). constructor.
    + unfold concr_hlpl_mem. intros.
      destruct (peq  (pi.1) enc_x).
      * subst. rewrite <- sset_not_prefix_valid in H2 by (apply not_strict_prefix_nil).
        destruct (H0 _ _ _ _ H2 (eq_refl (S.[(pi.1, [])])) H4)
          as ((bytes & ? & ?) & ? ).
        split ; [ | assumption] . exists bytes ; split ; [ | assumption ].
        rewrite spath_var_app_vpath with (p := pi),
            sset_app_split, sset_sget_equal, sget_app ; simpl ; auto.
        apply concr_val_add_loc, concr_val_not_val_contains,
          not_state_contains_implies_not_value_contains_sget ; auto.
      * apply sset_not_prefix_valid in H2 ; try (apply not_strict_prefix_nil).
        rewrite sset_sget_disj in H3 by (constructor ; auto).
        destruct (H0 _ _ _ _ H2 H3 H4)
          as ((bytes & ? & ?) & ? ).
        split ; [ | assumption ]. exists bytes ; split ; [ | assumption ].
        apply concr_val_not_val_contains ; auto. rewrite <- H3.
        apply not_state_contains_implies_not_value_contains_sget ; auto.
    + repeat intro. rewrite <- sset_not_prefix_valid in H2 ;
        [ apply H1 ; auto | apply not_strict_prefix_nil ].
  - auto.
Qed.

Lemma Rvalue_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl rv t vS1,
    le_pl_hlpl blockof addrof Spl S ->
    WellTypedRValue S blockof rv ->
    rv_get_type rv = t ->
    S |-{rv} rv => vS1 ->
    exists addrof1 vl vl',
      Spl |-{rv-pl} rv => vl /\
      le_pl_hlpl blockof addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t vl' /\
      le_block vl vl'.
Proof.
  intros bo ao S Spl rv t vS1 Hle_hlpl HWT Htype Heval.
  pose proof Hle_hlpl as Htemp.
  destruct Htemp as (Spl' & Hcomp & Hconcr & Hle).
  induction Heval ; simpl in Htype ; subst.
  - destruct HWT as [HWTop Heq].
    apply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) (t := t) in Heval_op as G ;
      [ | exists Spl' | | ] ; auto.
    destruct G as (vl & vl' & t0 & ? & ? & ?).
    exists ao, vl, vl' ; repeat constructor ; auto.
  - destruct HWT as (HWTopl & HWTopr & top_l & top_r & Heq_t).
    apply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) (t := TInt) in H as G1 ;
      [ | exists Spl' | | ] ; auto. simpl in *.
    destruct G1 as (vl & vl' & ? & (Spl'' & ? & ? & ?) & ? & ?).
    apply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) (t := TInt) in H0 as G2 ;
      [ | exists Spl'' | | ] ; auto.
    destruct G2 as (? & ? & ? & (Spl''' & ? & ? & ?) & ? & ?).
    simpl in *. inversion H5  ; inversion H11 ; subst.
    apply le_block_not_contains_poison in H6, H12 ; subst. 
    exists ao, (make_int64 (m + n)), (make_int64 (m + n)) ; repeat constructor ; auto.
    * exists Spl''' ; auto.
    * intros ?. apply make_int64_not_contain_Undef in H6 ; assumption.
    * intros ?. apply make_int64_not_contain_Undef in H13 ; assumption.
    * eapply eval_operand_preserves_welltyped_op ; eauto.
  - destruct HWT as (t' & type & eval_type).
    destruct (reachable_loc bo ao S Hcomp l pi Hloc) as (addr & t0 & Hequiv).
    pose proof ((correct_addrof bo ao S Hcomp) _ _ _ _ Hequiv Hloc).
    assert (Hevt : PL.eval_type bo S pi t0) by
      (apply addr_spath_equiv_eval_type ; exists addr ; auto).
    assert (read_address Spl p t0 addr) by
      (eapply read_addr_spath_equiv_equiv ; eauto ; econstructor ; eauto).
    specialize (eval_type pi Heval_place).
    assert (t' = t0) by (eapply eval_type_deterministic ; eauto) ; subst.
    exists ao, (make_ptr64 addr), (make_ptr64 addr) ; repeat split.
    * constructor ; auto.
    * exists Spl' ; auto.
    * apply Concr_ptr_loc ; auto.
    * reflexivity.
  - destruct HWT as (t' & type & eval_type). specialize (eval_type pi Heval_place).
    destruct (spath_address_place_simul _ _ _ _ _ _ Hle_hlpl Heval_place) as
      (addr & t0 & ? & ?).
    assert (t' = t0) by (apply addr_spath_equiv_eval_type in eval_type as (? & ?) ;
                         eapply addr_spath_equiv_deterministic_type ; eauto).
    subst.
    exists (fun l0 => if (l =? l0)%nat then Some (addr, t0) else ao l0),
      (make_ptr64 addr), (make_ptr64 addr) ; repeat split.
    * constructor. eapply read_addr_spath_equiv_equiv ; eauto.
    * rewrite snd_pair. apply le_pl_hlpl_write_loc ; auto.
      apply addr_spath_equiv_implies_valid_spath in H1 as Hvp.
      rewrite spath_var_app_vpath in Hvp.
      apply valid_spath_app in Hvp as [? ?] ; auto.
    * apply Concr_ptr_loc. rewrite Nat.eqb_refl ; auto.
    * reflexivity.
  - specialize (HWT t1 t2) as (HWT1 & HWT2 & Hop_t1 & Hop_t2 & _).
    apply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) (t := t1) in Heval_first as G1 ;
      [ | exists Spl' | | ] ; auto. simpl in *.
    destruct G1 as (vl1 & vl1' & ? & (Spl'' & ? & ? & ?) & ? & ?).
    apply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) (t := t2) in Heval_first0 as G2 ;
      [ | exists Spl'' | | ] ; auto.
    destruct G2 as (vl2 & vl2' & ? & (Spl''' & ? & ? & ?) & ? & ?).
    simpl in *.
    exists ao, (vl1 ++ vl2), (vl1' ++ vl2') ; repeat constructor ; auto.
    * exists Spl''' ; auto.
    * apply Forall2_app ; auto.
    * eapply eval_operand_preserves_welltyped_op ; eauto.
Qed.

Lemma val_le_val_write_bot :
  forall ao vp v vl vl' t,
    concr_hlpl_val ao v t vl' ->
    le_block vl vl' ->
    valid_vpath v vp ->
    exists vl'', concr_hlpl_val ao (v.[[vp <- bot]]) t vl'' /\ le_block vl vl''.
Proof.
  intros * concr_val. generalize dependent vp. generalize dependent vl.
  induction concr_val ; intros * le valid_vp.
  - inversion valid_vp ; subst ; try (rewrite nth_error_nil in H ; congruence).
    exists (repeat Undef 8). split.
    + constructor ; auto.
    + apply le_block_poison. rewrite (Forall2_length le). reflexivity.
  - inversion valid_vp ; subst ; try (rewrite nth_error_nil in H ; congruence).
    exists (repeat Undef (sizeof t)). split.
    + constructor ; auto.
    + apply le_block_poison. rewrite (Forall2_length le), repeat_length. reflexivity.
  - inversion valid_vp ; subst.
    + exists (repeat Undef (sizeof (TPair t0 t1))). split.
      * constructor. reflexivity.
      * apply le_block_poison. apply concr_val_size in concr_val1, concr_val2.
        rewrite (Forall2_length le), List.length_app. simpl. lia.
    + destruct i as [ | [ | ?] ] ; simpl in H ;
        try (rewrite nth_error_nil in H ; congruence) ; injection H as <-.
      * apply Forall2_length in le as size. rewrite List.length_app in size.
        rewrite <- (LB.take_drop (length bytes0) bytes) in le.
        rewrite <- (LB.take_drop (length bytes0) bytes).
        apply LR.Forall2_app_inv in le as (? & ?) ; [ | rewrite LB.length_take ; lia].
        destruct (IHconcr_val1 _ _ H H0) as (bytes''0 & concr_val0 & le0).
        exists (bytes''0 ++ bytes1) ; split.
        ** simpl. constructor ; auto.
        ** eapply Forall2_app ; auto.
      * apply Forall2_length in le as size. rewrite List.length_app in size.
        rewrite <- (LB.take_drop (length bytes0) bytes) in le.
        rewrite <- (LB.take_drop (length bytes0) bytes).
        apply LR.Forall2_app_inv in le as (? & ?) ; [ | rewrite LB.length_take ; lia].
        destruct (IHconcr_val2 _ _ H1 H0) as (bytes''1 & concr_val1' & le1).
        exists (bytes0 ++ bytes''1) ; split.
        ** simpl. constructor ; auto.
        ** eapply Forall2_app ; auto.
  - inversion valid_vp ; subst.
    + specialize (IHconcr_val vl0 []). apply IHconcr_val ; auto. constructor.
    + destruct i ; simpl in H ;
        try (rewrite nth_error_nil in H ; congruence) ; injection H as <-.
      destruct (IHconcr_val _ _ le H0) as (bytes'' & concr_val' & le').
      exists bytes'' ; split ; auto. constructor ; auto.
  - inversion valid_vp ; subst.
    + exists (repeat Undef (sizeof (TRef t))). split.
      * constructor ; auto.
      * apply le_block_poison. rewrite (LR.Forall2_length _ _ _ le) ; auto.
    + rewrite nth_error_nil in H ; congruence.
Qed.

Lemma Reorg_Preserves_PL_HLPL_Rel :
  forall bo ao S S' Spl,
    le_pl_hlpl bo ao Spl S ->
    reorg S S' ->
    le_pl_hlpl bo ao Spl S'.
Proof.
  intros * (Spl' & Comp & concr_st & le_st) reorg. induction reorg.
  - nodes_to_val. pose proof concr_st as temp.
    apply state_concr_implies_val_concr with (sp := p) (v := ptr (l)) in temp
        as (addr & t & bytes & equiv & concr & lu) ; auto.
    + exists (Spl'.m.[ addr <- repeat Undef (sizeof t) : t ]). split ; [ | split ].
      * apply sset_preserves_compatibility ; auto ; rewrite ?Heqh ;
          unfold not_contains_bot, not_contains_loc ; not_contains.
      * apply concr_state_write_at_addr ; auto. apply Concr_bot ; auto.
      * destruct (le_pl_r _ _ _ _ _ lu le_st) as (bytes' & lu' & le_b).
        eapply le_pl_write_at_addr_r ; eauto.
        apply concr_val_size in concr. apply Forall2_length in le_b.
        apply le_block_poison ; congruence.
    + apply get_not_bot_valid_spath. intros ?. rewrite H0 in Heqh. discriminate.
  - exists Spl' ; split ; [ | split].
    + split.
      * intros * enc vsp. destruct (bo enc_x) ; repeat econstructor ; eauto.
      * intros * equiv node. destruct (decidable_prefix p sp) as [ (r & ?) | ?].
        ** subst.
           eapply remove_loc_addr_spath_equiv_suffix in equiv as (equiv & vsp) ; eauto.
           apply (correct_addrof _ _ _ Comp _ _ _ _ equiv).
           erewrite get_node_remove_loc in node ; eauto.
           unfold add_loc_spath in node.
           destruct (decidable_prefix_is_prefix p r) as (equ & ?).
           rewrite H1 in node ; auto.
        ** apply addr_spath_equiv_sset in equiv ; auto.
           apply (correct_addrof _ _ _ Comp _ _ _ _ equiv).
           erewrite get_node_remove_loc in node ; eauto.
           unfold add_loc_spath in node.
           destruct (decidable_prefix_is_not_prefix p sp) as (equ & ?) ; auto.
           rewrite H2 in node ; auto.
      * intros * node. rewrite get_node_remove_loc with (l := l) in node ; auto.
        edestruct (reachable_loc _ _ _ Comp l0) as (addr & t & equiv) ; eauto.
        exists addr, t.
        unfold add_loc_spath in * ;
        destruct (decidable_prefix' p sp) as [ (r & eq) | npref] ; nodes_to_val.
        ** eapply remove_loc_addr_spath_equiv_suffix ; eauto ; split ; auto.
           apply get_not_bot_valid_spath. rewrite Heqh0. discriminate.
        ** apply addr_spath_equiv_sset ; auto.
    + destruct concr_st as (concr_mem & concr_env). split.
      * unfold concr_hlpl_mem. intros * vsp S_encx bo_encx.
        destruct (peq (p.1) enc_x) ; subst.
        ** rewrite <- sset_not_prefix_valid in vsp
               by (apply not_strict_prefix_nil).
           destruct (concr_mem _ _ _ _ vsp (eq_refl (S.[(p.1, [])])) bo_encx)
             as ((bytes & ? & ?) & ? ). split ; [ | assumption ].
           exists bytes ; split ; auto.
           rewrite spath_var_app_vpath with (p := p), sset_app_split,
               sset_sget_equal, <- app_spath_vpath_assoc, sget_app ; auto.
           nodes_to_val. rewrite spath_var_app_vpath with (p := p), sget_app in Heqh.
           eapply concr_val_remove_loc; eauto.
        ** apply sset_not_prefix_valid in vsp ; try (apply not_strict_prefix_nil).
           destruct (concr_mem _ _ _ _ vsp (eq_refl (S.[(enc_x, [])])) bo_encx)
             as ((bytes & ? & ?) & ? ). split ; [ | assumption ].
           exists bytes ; split ; auto. 
           rewrite sset_sget_disj ; auto. left ; auto.
      * unfold concr_hlpl_env. intros * vsp bo_encx. apply concr_env ; auto.
        eapply sset_not_prefix_valid ; eauto. apply not_strict_prefix_nil.
    + assumption.
Qed.

Lemma Reorg_Star_Preserves_PL_HLPL_Rel :
  forall bo ao S S' Spl,
    le_pl_hlpl bo ao Spl S ->
    clos_refl_trans reorg S S' ->
    le_pl_hlpl bo ao Spl S'.
Proof.
  intros * le reorg. induction reorg ; auto.
  apply Reorg_Preserves_PL_HLPL_Rel with (S := x) ; auto.
Qed.

Lemma Assign_Preserves_PL_HLPL_Rel :
  forall bo ao S S' Spl p rv t,
    le_pl_hlpl bo ao Spl S ->
    WellTypedStmt S bo (ASSIGN p <- rv) ->
    t = rv_get_type rv ->
    S |-{stmt} ASSIGN p <- rv => rUnit, S' ->
    exists Spl', Spl |-{stmt-pl} ASSIGN p <- rv => rUnit, Spl'.
Proof.
  intros * Hle WTS Htype Hstmt.
  remember (ASSIGN p <- rv) as asgn.
  induction Hstmt ; subst ; try discriminate.
  - inversion Hstore ; subst. simpl in WTS.
    eapply eval_rvalue_preserves_eval_place in eval_p as [sp' eval_p] ; eauto .
    destruct (WTS (rv_get_type rv) sp' eval_p) as (WTRV & _ & type).
    eapply Rvalue_Preserves_PL_HLPL_Rel in eval_rv
        as (ao1 & vl & vl' & eval_rv_pl & Hle' & Hconcr & Hle_block) ; eauto.
    simpl fst in *; simpl snd in *.
    eapply HLPL_PL_Read with (t := rv_get_type rv)
      in eval_p as (vl0 & vl0' & Hread & Hconcr' & Hleb) ; eauto.
    inversion Hread. exists (Spl.m.[addr <- vl : (rv_get_type rv)]).
    eapply Eval_assign with (t := rv_get_type rv) ; eauto.
    eapply Write ; eauto.
  - apply Reorg_Star_Preserves_PL_HLPL_Rel with (S' := S1) in Hle ; auto.
    assert (WellTypedStmt S1 bo (ASSIGN p <- rv)) by admit.
    auto.
Abort.

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

  Program Definition pl_state_1 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ]};
      mem := {[ b1 := repeat PL_poison 8 ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <-. auto.
  Qed.

  Program Definition pl_state_2 : PL_state :=
    {|
      env := {[ enc_x := (b1, TPair TInt TInt) ]};
      mem := {[ b1 := repeat PL_poison 8 ++ repeat PL_poison 8 ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <-. auto.
  Qed.

  Program Definition pl_state_3 : PL_state :=
    {|
      env := {[ enc_x := (b1, TPair (TRef TInt) TInt) ]};
      mem := {[ b1 := make_ptr64 (b1, 8) ++ make_int64 0 ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <-. auto.
  Qed.

  Program Definition pl_state_4 : PL_state :=
    {|
      env := {[ enc_x := (b1, (TRef (TRef TInt))) ]};
      mem :=
        {[
            b1 := make_ptr64 (b2, 8) ;
            b2 := make_int64 3 ++ make_ptr64 (b2, 0)
        ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_5 : PL_state :=
    {|
      env := {[ enc_x := (b1, (TRef (TRef TInt))) ]};
      mem :=
        {[
            b1 := make_ptr64 (b2, 8) ;
            b2 := repeat PL_poison 8 ++ make_ptr64 (b2, 0)
        ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_6 : PL_state :=
    {|
      env :=
        {[
            enc_x := (b1, TPair TInt (TPair TInt TInt))
        ]};
      mem :=
        {[
            b1 := make_int64 0 ++ make_int64 1 ++ make_int64 7
        ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_7 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ]};
      mem := {[ b1 := make_int64 3 ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_8 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ; enc_y := (b2, TInt) ]};
      mem := {[ b1 := repeat PL_poison 8 ; b2 := repeat PL_poison 8 ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_9 : PL_state :=
    {|
      env := {[ enc_x :=  (b1, TInt) ; enc_y := (b2, TInt) ]};
      mem := {[ b1 := make_int64 3 ; b2 := make_int64 7 ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Local Close Scope stdpp_scope.

  (** READ AND WRITES TESTS **)

  Goal exists S, write pl_state_1 (x, []) TInt (make_int64 0) S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (x, [Field(First)]) TInt (make_int64 0) S.
  Proof. repeat econstructor. Qed.

  Goal exists S, write pl_state_2 (x, [Field(Second)]) TInt (make_int64 0) S.
  Proof. repeat econstructor. Qed.

  Goal read pl_state_3 (x, [Field(First) ; Deref ]) TInt (make_int64 0).
  Proof. repeat econstructor. Qed.

  Goal read pl_state_3 (x, [Field(Second)]) TInt (make_int64 0).
  Proof. repeat econstructor. Qed.

  Goal read pl_state_4 (x, [Deref ; Deref]) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal write pl_state_5 (x, [Deref ; Deref]) TInt (make_int64 3) pl_state_4.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  (** EXPRESSION EVALUATION TESTS **)

  Goal pl_state_1 |-{op-pl} IntConst TInt 3 => (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Copy (TPair TInt TInt) (x, []) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Move (TPair TInt TInt) (x, []) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{rv-pl} Just (TPair TInt TInt) (Copy (TPair TInt TInt) (x, [])) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} BinOp TInt (INT 1) (INT 4) => make_int64 (1 + 4).
  Proof. repeat econstructor. Qed.

  Goal pl_state_6 |-{rv-pl} BinOp TInt (Move TInt (x, [Field(Second) ; Field(Second)])) (INT 4) => make_int64 (7 + 4).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} &mut (x, []) : (TRef TInt) => make_ptr64 (b1, 0).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (INT 0) (INT 1)
       => (make_int64 0 ++ make_int64 1).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (IntConst TInt 0) (Move TInt (x, []))
       => (make_int64 0 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_7.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_1.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_9.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_8.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  (** CONCRETIZATION TESTS **)

  Definition addrof := (fun l => if l =? l1 then Some ((b1, 1), TInt) else None).

  Goal concr_hlpl_val addrof (HLPL_int 3) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof (loc (l1, (HLPL_int 3))) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof HLPL_bot (TPair TInt TInt) (repeat PL_poison 16).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    HLPL_bot (TPair (TPair TInt TInt) TInt) (repeat PL_poison 24).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair (HLPL_int 3) (HLPL_int 4)) (TPair TInt TInt)
    (make_int64 3 ++ make_int64 4).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair
       (HLPL_int 3)
       (HLPL_pair (HLPL_int 7) (HLPL_int 11)))
    (TPair TInt (TPair TInt TInt))
    (make_int64 3 ++ (make_int64 7 ++ make_int64 11)).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair
       (HLPL_int 3)
       (HLPL_pair (HLPL_int 7) (HLPL_int 11)))
    (TPair TInt (TPair TInt TInt))
    (make_int64 3 ++ (make_int64 7 ++ make_int64 12)).
  Proof. repeat econstructor. Abort.

  Goal concr_hlpl_val addrof
    (ptr (l1)) (TRef TInt) (make_ptr64 (b1, 1)).
  Proof. repeat econstructor. Qed.
End Tests.
