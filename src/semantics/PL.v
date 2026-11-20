Require stdpp.base.
Require stdpp.countable.
Import -(notations) stdpp.base.
From chamois Require Import Maps.
From chamois Require Import Memdata Memtype Memory.
Require Import base.
Require Import lang.
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
Module LB := list_basics.list.
Module LR := list_relations.list.

Require Import Axioms Coqlib Integers Floats AST Values.
From Stdlib Require Import Zwf.
Require Import PathToSubtree.
Require Import Stdlib.Classes.RelationClasses.

Opaque sset.

Open Scope Z_scope.
Coercion Ptrofs.repr : Z >-> ptrofs.

Notation "p .1" := (fst p).
Notation "p .2" := (snd p).
Local Notation "a # b" := (PXMap.get b a) (at level 1).

Definition offset := Z.
Definition address := (block * Z)%type.

Definition make_ptr64 (addr : address) :=
  map (fun i => Fragment (Vptr addr.1 addr.2) Q64 i) (seq 0 8).

Definition make_int64 (n : nat) :=
  encode_val Mint64 (Vlong (Int64.repr n)).

Definition make_bool (b : bool) :=
  if b then
    encode_val Mbool (Vint Int.one)
  else
    encode_val Mbool (Vint Int.zero).

Lemma make_ptr64_not_contain_Undef : 
  forall addr, ~ In Undef (make_ptr64 addr).
Proof.
  intros * ?. simpl in H.
  destruct H as [|[|[|[|[|[|[|[|] ] ] ] ] ] ] ] ; try discriminate ; auto.
Qed.

Lemma make_int64_not_contain_Undef : 
  forall addr, ~ In Undef (make_int64 addr).
Proof.
  intros * ?. simpl in H.
  destruct H as [|[|[|[|[|[|[|[|] ] ] ] ] ] ] ] ; try discriminate ; auto.
Qed.

Record PL_state : Type := Build_PL_state {
  env : PTree.t (block * type);
  mem : Mem.mem;
                            }.

Definition encode_var (x : var) := countable.encode (A := var + anon) (inl x).

Fixpoint sizeof (tau : type) : nat :=
  match tau with
  | TInt | TRef _ => 8 (* TODO: size of boolean? *)
  | TBool => 1
  | TTuple tl => sizeof_tuple tl
  end with
sizeof_tuple (taul : type_list) : nat :=
  match taul with
  | TNil => 0
  | TCons t tl => sizeof t + sizeof_tuple tl
  end. 

Fixpoint partial_sizeof_tuple (taul : type_list) (n : nat) : nat :=
  match taul, n with
  | TCons t tl, S n => sizeof t + partial_sizeof_tuple tl n
  | _, _ => 0
  end. 

Notation pst := partial_sizeof_tuple.

Lemma n_leq_m_implies_leq_length_pst n m tl :
  (n <= m)%nat -> pst tl n <= pst tl m.
Proof.
 generalize dependent m. generalize dependent n. induction tl ; intros.
 - reflexivity.
 - destruct n ; destruct m ; cbn ; try lia. specialize (IHtl _ _ (le_S_n _ _ H)). lia.
Qed.
   

Lemma sizeof_tuple_sum (taul : type_list) :
  sizeof_tuple taul = sum (map sizeof (TypeList.to_list taul)).
Proof. induction taul ; simpl ; congruence. Qed.

Lemma partial_sizeof_tuple_firstn_sum (taul : type_list) (n : nat) :
    partial_sizeof_tuple taul n = sum (map sizeof (firstn n (TypeList.to_list taul))).
Proof.
  generalize dependent n. induction taul ; intro.
  - cbn. rewrite LB.take_nil. reflexivity.
  - destruct n.
    * reflexivity.
    * cbn. rewrite IHtaul. reflexivity.
Qed.

Lemma partial_sizeof_tuple_leq_sizeof_tuple (taul : type_list) (n : nat) : 
  partial_sizeof_tuple taul n <= sizeof_tuple taul.
Proof.
  generalize dependent n.
  induction taul ; destruct n ; cbn ; try lia. specialize (IHtaul n). lia.
Qed.

Lemma partial_sizeof_tuple_last (taul : type_list) :
  forall n t,
    TypeList.nth_error taul n = Some t ->
    (partial_sizeof_tuple taul (S n) = partial_sizeof_tuple taul n + sizeof t)%nat.
Proof.
  induction taul ; intros.
  - discriminate.
  - destruct n.
    * injection H as <-. destruct taul ; cbn ; lia.
    * apply IHtaul in H. cbn. lia.
Qed.

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
Definition add_offset (addr : address) (off : Z) : address :=
  (addr.1, addr.2 + off).

Infix "+o" := add_offset (at level 30).

Lemma addr_add_offset_fst : forall (addr : address) (off : nat),
    (addr +o off).1 = addr.1.
Proof.
  intros addr off. rewrite surjective_pairing with (p := addr). auto.
Qed.

Lemma addr_add_offset_snd : forall (addr : address) (off : Z),
    (addr +o off).2 = addr.2 + off.
Proof.
  intros addr off. rewrite surjective_pairing with (p := addr). auto.
Qed.

Lemma addr_add_offset_0 : forall (addr : address),
    addr +o 0 = addr.
Proof.
  intro. unfold "+o". rewrite Z.add_0_r. rewrite <- surjective_pairing. reflexivity.
Qed.

Lemma addr_add_offset_assoc : forall (addr : address) (off1 off2 : Z),
    addr +o (off1 + off2) = addr +o off1 +o off2.
Proof. intros. unfold "+o". cbn. rewrite Z.add_assoc. reflexivity. Qed.

Lemma bi_add_offset : forall (bi : block) (off1 off2 : Z),
    (bi, off1 + off2) = (bi, off1) +o off2.
Proof. reflexivity. Qed.

(* Functions to lookup and update PL states *)
Definition update_env (S : PL_state) (e : PTree.t (block * type)) :=
  {| env := e ; mem := mem S  |}.

Definition update_mem (S : PL_state) (m : Mem.mem) :=
  {| env := env S ; mem := m |}.

Definition lookup_block_and_type_env (enc_x : positive) (S : PL_state)
  : option (block * type) := PTree.get enc_x (env S).

Definition lookup_env (enc_x : positive) (S : PL_state) : option block :=
  match PTree.get enc_x (env S) with
  | None => None
  | Some (bi, _) => Some bi
  end.

Definition lookup_type_env (enc_x : positive) (S : PL_state) : option type :=
  match PTree.get enc_x (env S) with
  | None => None
  | Some (_, T) => Some T
  end.

Notation "Spl !!h bi" := (PXMap.get bi (Mem.mem_contents (mem Spl))) (at level 40).
Notation "Spl !!e bi" := (PTree.get bi (env Spl)) (at level 40).

Fixpoint valid_access (S : PL_state) (b : block) (off : Z)  (t : type) :=
  match t with
  | TInt => Mem.valid_access (mem S) Mint64 b off Freeable
  | TBool => Mem.valid_access (mem S) Mint64 b off Freeable (* TODO: size of boolean? *)
  | TRef _ => Mem.valid_access (mem S) Many64 b off Freeable
  | TTuple tl => valid_access_tuple S b off tl
  end with
valid_access_tuple (S : PL_state) (b : block) (off : Z)  (tl : type_list) :=
  match tl with
  | TNil => True
  | TCons t tl' =>
      valid_access S b off t /\ valid_access_tuple S b (off + sizeof t) tl'
  end.

Lemma valid_access_dec :
  forall S b off t,
    { valid_access S b off t } + { ~ valid_access S b off t }
with valid_access_tuple_dec :
  forall S b off tl,
    { valid_access_tuple S b off tl } + { ~ valid_access_tuple S b off tl }.
Proof.
  {
    intros *. generalize dependent off.
    induction t ; intros * ; try apply Mem.valid_access_dec ;
      apply valid_access_tuple_dec.
  }
  {
    intros *. generalize dependent off. induction tl ; intros.
    - left. constructor.
    - simpl. destruct (valid_access_dec S b off t) ;
        destruct (IHtl (off + sizeof t)) ;
        [ left ; auto | | | ] ; right ; firstorder.
  }
Defined.

Ltac nodes_to_val :=
  match goal with
  | H : get_node ?v = ?r |- _ =>
      destruct v eqn:? ; simpl in H ; try congruence ;
      try (injection H ; intros ; subst) ; clear H ;
      nodes_to_val ;
      try (
          assert (get_node v = r) by (
            match goal with
            | H0 : v = _ |- _ =>
                rewrite H0 ; reflexivity end))
  | _ => idtac
  end.

Definition storebytes m b off bytes t :=
  if Nat.eqb (sizeof t) (length bytes) then
    match Mem.storebytes m b off bytes with
    | None => m
    | Some m' => m'
    end
  else m.

Lemma mem_storebytes_elim : 
  forall m b ofs bytes,
    ((exists m', Mem.storebytes m b ofs bytes = Some m') /\
             Mem.range_perm m b ofs (ofs + Datatypes.length bytes) Cur Writable) \/
      (Mem.storebytes m b ofs bytes = None /\
         ~ Mem.range_perm m b ofs (ofs + Datatypes.length bytes) Cur Writable).
Proof.
  Transparent Mem.storebytes.
  intros *. destruct (Mem.storebytes m b ofs bytes) eqn:E.
  - left. split ; [ exists m0 ; reflexivity | ].
    unfold Mem.storebytes in E.
    destruct (Mem.range_perm_dec _ _ _ _ _ _) ; [injection E as <- | easy ] ; assumption.
  - right ; split ; [ reflexivity | ].
    unfold Mem.storebytes in E.
    destruct (Mem.range_perm_dec _ _ _ _ _ _) ; [ easy | assumption ].
  Opaque Mem.storebytes.
Qed.

Lemma storebytes_elim :
  forall m b off bytes t,
    (sizeof t = length bytes /\ exists m', Mem.storebytes m b off bytes = Some m' /\
     storebytes m b off bytes t = m') \/
    ((sizeof t <> length bytes \/ Mem.storebytes m b off bytes = None) /\
     storebytes m b off bytes t = m).
Proof.
  intros.
  destruct (Nat.eq_dec (sizeof t) (length bytes)) ;
  destruct (Mem.storebytes m b off bytes) eqn:E.
  - left. repeat econstructor ; eauto. unfold storebytes.
    rewrite E, e, Nat.eqb_refl ; reflexivity.
  - right ; split ; auto. unfold storebytes. rewrite e, Nat.eqb_refl, E. reflexivity.
  - right ; split.
    * left ; auto.
    * unfold storebytes. rewrite (proj2 (Nat.eqb_neq _ _)) ; auto.
  - right ; split ; auto. unfold storebytes. rewrite (proj2 (Nat.eqb_neq _ _)) ; auto.
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

Lemma getN_firstn :
  forall mem n m ofs,
    firstn n (Mem.getN m ofs mem) = Mem.getN (Nat.min n m) ofs mem.
Proof.
  induction n ; intros.
  - simpl. rewrite firstn_0. reflexivity.
  - destruct m ; simpl ; [ reflexivity | ].
    rewrite IHn. reflexivity.
Qed.

Lemma getN_skipn :
  forall mem n m ofs,
    skipn n (Mem.getN m ofs mem) = Mem.getN (m - n) (ofs + n) mem.
Proof.
  induction n ; intros.
  - rewrite skipn_0, Nat.sub_0_r, Z.add_0_r. reflexivity.
  - destruct m ; [ reflexivity | ].
    simpl. rewrite IHn. replace (ofs + S n) with (ofs + 1 + n) by lia. reflexivity.
Qed.

Notation "S .m.[ addr : t ]" := (Mem.loadbytes (mem S) addr.1 addr.2 (sizeof t))
                                  (at level 50, addr at next level).
Notation "S .m.[ addr <- bytes : t ]" :=
  (update_mem S (storebytes (mem S) addr.1 addr.2 bytes t)) (bytes at next level).

Lemma env_stable_by_write_at_addr :
  forall S addr t bytes, env (S.m.[addr <- bytes: t]) = env S.
Proof.
  intros [env_S mem_S] [bi off] bytes ?. reflexivity.
Qed.

Lemma heap_sset_sget_disj :
  forall Spl addr bi v t,
    addr.1 <> bi -> Spl.m.[addr <- v : t] !!h bi = Spl !!h bi.
Proof.
  intros [env mem] * neq. unfold storebytes. simpl.
  destruct ((sizeof t =? Datatypes.length v)%nat) eqn:len; [ | reflexivity ] ;
    destruct (Mem.storebytes mem addr.1 addr.2 v) eqn:E ; [ | reflexivity ].
  apply Mem.storebytes_mem_contents in E. rewrite E, PXMap.gso ; congruence.
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

Lemma mem_perm_range_stable_by_write_at_addr :
  forall Spl addr bi ofs bytes size t k perm,
  Mem.range_perm (mem Spl) bi ofs size k perm ->
  Mem.range_perm (mem (Spl .m.[ addr <- bytes : t])) bi ofs size k perm.
Proof.
  intros * range_perm. unfold Mem.range_perm, Mem.perm in * ; intros * eq.
  rewrite <- mem_access_stable_by_write_at_addr. auto.
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

Inductive eval_proj (Spl : PL_state) : proj -> (address * type) -> (address * type) -> Prop :=
| Eval_Deref_Ptr_Locs :
  forall (addr addr' : address) (t : type),
    0 <= addr'.2 < Ptrofs.modulus ->
    Spl.m.[addr : TRef t] = Some (make_ptr64 addr') ->
    eval_proj Spl Deref (addr, TRef t) (addr', t)
| Eval_Field :
  forall (addr addr' : address) (t : type) (tl : type_list) (n : nat),
    eval_proj_tuple Spl n (addr, tl) (addr', t) ->
    eval_proj Spl (Field n) (addr, TTuple tl) (addr', t)
with eval_proj_tuple
       (Spl : PL_state) : nat -> (address * type_list) -> (address * type) -> Prop :=
| ET_Field_Nil :
  forall (addr : address) (t : type) (tl : type_list),
    eval_proj_tuple Spl 0 (addr, TCons t tl) (addr, t)
| ET_Field_Cons :
  forall (addr addr' : address) (t t' : type) (tl : type_list) (n : nat),
    eval_proj_tuple Spl n (addr +o sizeof t, tl) (addr', t') ->
    eval_proj_tuple Spl (S n) (addr, TCons t tl) (addr', t').

Inductive eval_path (Spl : PL_state) : path -> address * type -> address * type -> Prop :=
| Eval_nil_addr : forall addr, eval_path Spl [] addr addr
| Eval_cons : forall proj P addr_t addr_t' addr_t'',
    eval_proj Spl proj addr_t addr_t' ->
    eval_path Spl P addr_t' addr_t'' ->
    eval_path Spl (proj :: P) addr_t addr_t''.

Definition eval_place (Spl : PL_state) (p : place) (addr_t : address * type) : Prop :=
  exists bi t,
    lookup_block_and_type_env (encode_var (p.1).1) Spl = Some (bi, t) /\
      eval_path Spl (p.1).2 ((bi, 0), t) addr_t.

Notation "Spl  |-{p}  p =>^{pl} addr_t" := (eval_place Spl p addr_t) (at level 50).

Lemma eval_proj_deterministic :
  forall Spl proj addr_t0 addr_t1 addr_t2,
    eval_proj Spl proj addr_t0 addr_t1 ->
    eval_proj Spl proj addr_t0 addr_t2 ->
    addr_t1 = addr_t2
with eval_proj_tuple_deterministic :
  forall Spl n addr_tl addr_t1 addr_t2,
    eval_proj_tuple Spl n addr_tl addr_t1 ->
    eval_proj_tuple Spl n addr_tl addr_t2 ->
    addr_t1 = addr_t2.
Proof.
  intros Spl proj ? ? ? Heval_proj1 Heval_proj2.
  {
    induction Heval_proj1 ; subst ; inversion Heval_proj2; subst ; auto.
    rewrite H0 in H4. injection H4 as Hfst Hsnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ ;
      intros ; subst ; auto. f_equal ; auto.
    Transparent Ptrofs.repr. unfold Ptrofs.repr in Hsnd. Opaque Ptrofs.repr.
    rewrite !Ptrofs.Z_mod_modulus_eq, !Z.mod_small in Hsnd ; try lia.
    rewrite surjective_pairing with (p := addr'),
        surjective_pairing with (p := addr'0) ; congruence.
    eauto.
  }
  intros. induction H ; inversion H0 ; subst ; auto.
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

Lemma eval_proj_tuple_pst Spl addr tl t :
  forall k, TypeList.nth_error tl k = Some t ->
       eval_proj_tuple Spl k (addr, tl) (addr +o pst tl k, t).
Proof.
  generalize dependent addr. induction tl ; intros.
  - cbn in H. congruence.
  - destruct k ; cbn in H.
    * injection H as ->. cbn. rewrite addr_add_offset_0. constructor.
    * constructor. cbn. rewrite Nat2Z.inj_add, addr_add_offset_assoc. auto.
Qed.

(** Read in PL state *)
Definition read_address (Spl : PL_state) (p : place) (t : type) (addr : address): Prop :=
    Spl |-{p} p =>^{pl} (addr, t).

Variant read (S : PL_state) (p : place) (t : type) (bytes : list memval) : Prop :=
  | Read addr 
      (Haddr : read_address S p t addr)
      (Hlu : S.m.[ addr : t] = Some bytes) :
    read S p t bytes.

Variant write (S : PL_state) (p : place) (t : type) (bytes : list memval)
  : PL_state -> Prop :=
  | Write addr S'
      (Haddr : read_address S p t addr)
      (Heq : S' = (S.m.[ addr <- bytes : t])) :
      write S p t bytes S'.

(* Evaluation of Expressions in PL *)
Reserved Notation "S  |-{op-pl}  op  =>  r" (at level 60).
Inductive eval_operand : operand -> PL_state -> list memval -> Prop :=
| Eval_IntConst S n :
  S |-{op-pl} Const (IntConst n) => (make_int64 n)
| Eval_BoolConst S b:
  S |-{op-pl} Const (BoolConst b) => (make_bool b)
| Eval_copy S t p bytes
    (Hread : read S p t bytes) :
  S |-{op-pl} Copy p => bytes
| Eval_move S t p bytes
    (Hread : read S p t bytes) :
  S |-{op-pl} Move p => bytes
| Eval_tuple S opl bytes :
  eval_tuple opl S bytes ->
  eval_operand (Tuple opl) S bytes
where "S |-{op-pl} op => r" := (eval_operand op S r)
with eval_tuple : list operand -> PL_state -> list memval -> Prop :=
| Eval_TNil S : eval_tuple [] S []
| Eval_TCons S op opl bytes0 bytes1 :
  eval_operand op S bytes0 ->
  eval_tuple opl S bytes1 ->
  eval_tuple (op :: opl) S (bytes0 ++ bytes1).

Reserved Notation "S  |-{rv-pl}  rv =>  r" (at level 60).
Variant eval_rvalue: rvalue -> PL_state -> list memval -> Prop :=
| Eval_use S op bytes
  (Hop : S |-{op-pl} op => bytes) :
  S |-{rv-pl} Use op => bytes
| Eval_bin_op S op_l n_l op_r n_r
    (Hl : S |-{op-pl} op_l => (make_int64 n_l))
    (Hr : S |-{op-pl} op_r => (make_int64 n_r)) :
    S |-{rv-pl} BinaryOp BAdd op_l op_r => (make_int64 (n_l + n_r))
| Eval_ptr S t p addr
    (Haddr : read_address S p t addr) :
  S |-{rv-pl} &mut p => (make_ptr64 addr)
where "S |-{rv-pl} rv => r" := (eval_rvalue rv S r).

Reserved Notation "S  |-{stmt-pl}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> flow_token -> PL_state -> PL_state -> Prop :=
| Eval_nop S : S |-{stmt-pl} Nop => rUnit, S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r
    (eval_stmt_l : S0 |-{stmt-pl} stmt_l => rUnit, S1)
    (eval_stmt_r : S1 |-{stmt-pl} stmt_r => r, S2) :
  S0 |-{stmt-pl} stmt_l ;; stmt_r => r, S2
| Eval_seq_panic S0 S1 stmt_l stmt_r
    (eval_stmt_l : S0 |-{stmt-pl} stmt_l => rPanic, S1) :
  S0 |-{stmt-pl} stmt_l ;; stmt_r => rPanic, S1
| Eval_assign S bytes S' p rv t
    (eval_rv : S |-{rv-pl} rv => bytes)
    (Hwrite : write S p t bytes S'):
  S |-{stmt-pl} ASSIGN p <- rv => rUnit, S'
where "S |-{stmt-pl} stmt => r , S'" := (eval_stmt stmt r S S').
