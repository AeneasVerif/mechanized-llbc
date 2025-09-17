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

Section EvalPlaces.
  Local Open Scope stdpp_scope.

  (* Definition of spath for PL state *)
  Variant lproj :=
    | LFirst
    | LSecond
    | LLoc.

  Definition lvpath : Type := list lproj.
  Definition lspath : Type := positive * lvpath.

  (* The concatenation of a lspath and a lpath. *)
  Definition app_lspath_lvpath (p : lspath) (q : lvpath) := (fst p, snd p ++ q).
  (* TODO: place the notation in a scope? *)
  Notation "p +++l q" := (app_lspath_lvpath p q) (right associativity, at level 60).

  Fixpoint vget_l (lvp : lvpath) (v : HLPL_val) :=
    match (lvp, v) with
    | ([], _) => v
    | (LFirst :: lvp', HLPL_pair v0 _) =>
        vget_l lvp' v0
    | (LSecond :: lvp', HLPL_pair _ v1) =>
        vget_l lvp' v1
    | (LLoc :: lvp', HLPL_loc _ v') =>
        vget_l lvp' v'
    | _ => HLPL_bot
    end.
Notation "v .[[ p ]]l" := (vget_l p v) (left associativity, at level 50).

  Definition sget_l (lsp : lspath) (S : HLPL_state) :=
    match get_at_accessor S lsp.1 with
  | Some v => vget_l lsp.2 v
  | None => bot
  end.
Notation "S .[ p ]l" := (sget_l p S) (left associativity, at level 50).

Inductive eval_proj_l (S : HLPL_state) : proj -> lspath -> lspath -> Prop :=
| Eval_Deref_Ptr_Locs :
    forall (q q' : lspath) (l : loan_id) perm,
      perm <> Mov ->
      get_node (S.[q]l) = ptrC (l) →
      get_node (S.[q']l) = locC (l) ->
      eval_proj_l S Deref q q'
  | Eval_Field_First_l :
    forall q : lspath,
      get_node (S.[q]l) = HLPL_pairC →
      eval_proj_l S (Field First) q (q +++l [LFirst])
  | Eval_Field_Second_l :
    forall (q : lspath),
      get_node (S.[q]l) = HLPL_pairC →
      eval_proj_l S (Field Second) q (q +++l [LSecond]).

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

  Inductive vpath_lvpath_equiv : HLPL_val -> vpath -> lvpath -> Prop :=
  | Vpath_lvpath_nil v : vpath_lvpath_equiv v [] []
  | Vpath_lvpath_First
      v0 v1 vp lvp (Hrec : vpath_lvpath_equiv v0 vp lvp) :
    vpath_lvpath_equiv (HLPL_pair v0 v1) (0 :: vp) (LFirst :: lvp)
  | Vpath_lvpath_Second
      v0 v1 vp lvp (Hrec : vpath_lvpath_equiv v1 vp lvp) :
    vpath_lvpath_equiv (HLPL_pair v0 v1) (1 :: vp) (LSecond :: lvp)
  | Vpath_lvpath_Loc
      l v vp lvp (Hrec : vpath_lvpath_equiv v vp lvp) :
    vpath_lvpath_equiv (HLPL_loc l v) (0 :: vp) (LLoc :: lvp).

  Definition spath_lspath_equiv (S : HLPL_state) (sp : spath) (lsp : lspath) :=
    sp.1 = lsp.1 /\
      exists v, get_at_accessor S sp.1 = Some v /\
      vpath_lvpath_equiv v sp.2 lsp.2.

  Lemma vget_l_bot : forall vp, HLPL_bot.[[ vp]]l = HLPL_bot.
  Proof.
    induction vp ; auto.
    destruct a ; reflexivity.
  Qed.

  Lemma vget_vget_l_equiv :
    forall v vp lvp,
      vpath_lvpath_equiv v vp lvp -> vget vp v = vget_l lvp v.
  Proof.
    intros v vp lvp Hequiv. induction Hequiv ;
      simpl ; try rewrite IHHequiv ; reflexivity.
  Qed.

  Lemma sget_sget_l_equiv :
    forall S sp lsp,
      spath_lspath_equiv S sp lsp -> S.[sp] = S.[lsp]l.
  Proof.
    intros S sp lsp [Heq [v [Haccess Hequiv] ] ].
    remember sp.2 as vp. remember lsp.2 as lvp.
    apply vget_vget_l_equiv in Hequiv.
    unfold sget, sget_l. rewrite <- Heq, Haccess, <- Heqvp, <- Heqlvp. auto.
  Qed.

  Lemma sget_l_app_nil_r : 
    forall p, p +++l [] = p.
  Proof.
    intros p. rewrite surjective_pairing with (p := p).
    unfold app_lspath_lvpath. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma vget_l_app :
    forall p q v,
      v.[[p ++ q]]l = v.[[p]]l.[[q]]l.
  Proof.
    induction p ; intros q v.
    - reflexivity.
    - destruct a ; destruct v ; simpl ; try (rewrite vget_l_bot) ; auto.
  Qed.

  Lemma sget_l_app :
    forall p q S,
       S.[p +++l q]l = S.[p]l.[[q]]l.
  Proof.
    intros p q S.
    unfold sget_l, app_lspath_lvpath. cbn.
    destruct (sum_maps (vars S) (anons S) !! p.1). 
    - apply vget_l_app.
    - rewrite vget_l_bot. reflexivity.
  Qed.

  Lemma sget_implies_sget_l :
    forall S sp v,
      S.[sp] = v -> v <> bot -> exists lsp, S.[lsp]l = v.
  Proof.
    intros S sp.
    induction sp using ListBackInd.state_path_back_ind ; intros v HS_sp Hbot.
    - exists (enc_x, []). assumption.
    - rewrite sget_app in HS_sp.
      destruct (IHsp (S.[sp]) (eq_refl _)) as [lsp Hsget_l].
      * destruct (S.[sp]) ; destruct n ; auto.
      * destruct (S.[sp]) ; simpl in * ;
          try (rewrite nth_error_nil in HS_sp ; congruence).
        ** destruct n ; simpl in *.
           *** exists (lsp +++l [LLoc]).
               rewrite sget_l_app, Hsget_l, HS_sp. reflexivity.
           *** rewrite nth_error_nil in HS_sp ; congruence.
        ** destruct n ; simpl in *.
           *** exists (lsp +++l [LFirst]).
               rewrite sget_l_app, Hsget_l. auto.
           *** destruct n ; simpl in *.
               **** exists (lsp +++l [LSecond]).
                    rewrite sget_l_app, Hsget_l. auto.
               **** rewrite nth_error_nil in HS_sp. congruence.
  Qed.

  Lemma v_equiv_l_read :
    forall v vp lvp,
      vpath_lvpath_equiv v vp lvp -> v.[[ vp ]] = v.[[ lvp ]]l.
  Proof. intros v vp lvp Hequiv. induction Hequiv ; auto. Qed.

  Lemma s_equiv_l_read :
    forall S sp lsp,
      spath_lspath_equiv S sp lsp -> S.[sp] = S.[lsp]l.
  Proof. 
    intros S sp lsp [Heq [v [Haccess Hequiv] ] ].
    unfold sget, sget_l. rewrite <- Heq, Haccess. apply v_equiv_l_read ; auto.
  Qed.

  Lemma vget_implies_exists_lvp :
    forall vp v,
      v.[[vp]] <> bot -> exists lvp, vpath_lvpath_equiv v vp lvp.
  Proof.
    induction vp ; intros v Hbot_vp.
    - exists []. constructor.
    - replace (a :: vp) with ([a] ++ vp) in Hbot_vp by auto. rewrite vget_app in Hbot_vp.
      assert (Hbot : v.[[ [a] ]] <> bot).
      { destruct (v.[[ [a] ]]) eqn:E ; auto. 
        replace HLPL_bot with bot in Hbot_vp by auto. rewrite vget_bot in Hbot_vp.
        contradiction. }
      destruct (IHvp (v.[[ [a] ]]) Hbot_vp) as [lvp Hequiv].
      destruct v ; destruct a as [ | a'] ; try destruct a' ;
        try contradiction ; simpl in *.
      * exists (LLoc :: lvp) ; constructor ; assumption.
      * exists (LFirst :: lvp) ; constructor ; assumption.
      * exists (LSecond :: lvp) ; constructor ; assumption.
      * rewrite nth_error_nil in Hbot. contradiction.
  Qed.

  Lemma sget_implies_exists_l :
    forall S sp,
      S.[sp] <> bot -> exists lsp, spath_lspath_equiv S sp lsp.
  Proof.
    intros S [x vp] Hbot.
    remember ((x, []) : spath) as p.
    replace (x, vp) with (p +++ vp) in Hbot by (unfold "+++" ; subst ; reflexivity).
    rewrite sget_app in Hbot ; subst.
    destruct (vget_implies_exists_lvp vp (S.[(x, [])]) Hbot) as [lvp Hequiv].
    exists (x, lvp) ; split.
    - reflexivity.
    - exists (S.[(x, [])]) ; split ; auto.
      unfold sget. simpl.
      destruct (sum_maps (vars S) (anons S) !! x) eqn:E ; try reflexivity.
      unfold sget in Hbot. simpl in Hbot. rewrite E in Hbot.
      replace HLPL_bot with bot in Hbot by auto. rewrite vget_bot in Hbot.
      contradiction.
  Qed.

  Lemma v_backward_proj_l_First :
    forall v v0 v1 vp lvp,
      v.[[ vp ]] = HLPL_pair v0 v1 ->
      vpath_lvpath_equiv v vp lvp ->
      vpath_lvpath_equiv v (vp ++ [0]) (lvp ++ [LFirst]).
  Proof.
    intros v v0 v1 vp lvp Hpair Hequiv.
    induction Hequiv ; simpl in * ; subst ; repeat constructor ; auto.
    Qed.

  Lemma v_backward_proj_l_Second :
    forall v v0 v1 vp lvp,
      v.[[ vp ]] = HLPL_pair v0 v1 ->
      vpath_lvpath_equiv v vp lvp ->
      vpath_lvpath_equiv v (vp ++ [1]) (lvp ++ [LSecond]).
  Proof.
    intros v v0 v1 vp lvp Hpair Hequiv.
    induction Hequiv ; simpl in * ; subst ; repeat constructor ; auto.
    Qed.

  Lemma proj_spath_lspath_commute :
    forall S perm sp sp' lsp proj,
      spath_lspath_equiv S sp lsp ->
      eval_proj S perm proj sp sp' ->
      exists lsp',
        eval_proj_l S proj lsp lsp' /\ spath_lspath_equiv S sp' lsp'.
  Proof.
    intros S perm sp sp' lsp proj Hequiv Hproj.
    remember sp.2 as vp. remember lsp.2 as lvp.
    inversion Hproj ; subst.
    - assert (H : exists lsp', spath_lspath_equiv S sp' lsp').
      { eapply sget_implies_exists_l. destruct (S.[sp']) eqn:E ; auto. } 
      destruct H as [lsp' Hequiv'].
      apply s_equiv_l_read in Hequiv as HS_sp, Hequiv' as HS_sp'.
      exists lsp' ; split ; auto.
      apply Eval_Deref_Ptr_Locs with (l := l) (perm := perm) ; congruence.
    - assert (get_q_lsp : get_node (S .[ lsp]l) = HLPL_pairC) by
        (rewrite <- s_equiv_l_read with (sp := sp); auto).
      destruct Hequiv as [Heq [v [Haccess Hequiv] ] ].
      exists (lsp +++l [LFirst]) ; split ; constructor ; auto.
      exists v ; split ; auto.
      unfold sget in get_q ; rewrite Haccess in get_q ;
        destruct (v.[[ sp.2 ]]) eqn:E' ; simpl in get_q ; try congruence.
      eapply v_backward_proj_l_First ; eauto.
    - assert (get_q_lsp : get_node (S .[ lsp]l) = HLPL_pairC) by
        (rewrite <- s_equiv_l_read with (sp := sp); auto).
      destruct Hequiv as [Heq [v [Haccess Hequiv] ] ].
      exists (lsp +++l [LSecond]) ; split ; constructor ; auto.
      exists v ; split ; auto.
      unfold sget in get_q ; rewrite Haccess in get_q ; 
        destruct (v.[[ sp.2 ]]) eqn:E' ; simpl in get_q ; try congruence.
      eapply v_backward_proj_l_Second ; eauto.
  Qed.


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
  Definition read_address (Spl : PL_state) (p : place) (t : type) (addr : address) : Prop :=
    eval_place_pl Spl p (addr, t).
End EvalPlaces.
Notation "S .[ p ]l" := (sget_l p S) (left associativity, at level 50).
Notation "p +++l q" := (app_lspath_lvpath p q) (right associativity, at level 60).
Notation "v .[[ p ]]l" := (vget_l p v) (left associativity, at level 50).

Variant read (S : PL_state) (p : place) (t : type) (vl : pl_val) : Prop :=
  | Read addr vl'
      (Haddr : read_address S p t addr)
      (Hheap : Some vl' = lookup_heap addr.1 S)
      (Hsub : vl = firstn (sizeof t) (skipn addr.2 vl')) :
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
  Variable blockofinv : block_id * type -> positive.
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
    forall enc_x bi t v,
      S.[ (enc_x, []) ] = v ->
      v <> bot ->
      blockof enc_x = (bi, t) ->
      exists vl, concr_hlpl_val v t vl /\ h !! bi = Some vl .

  Definition concr_hlpl_env (S : HLPL_state) (env : Pmap (block_id * type)) : Prop :=
    forall enc_x bi t v,
      get_at_accessor S enc_x = Some v ->
      blockof enc_x = (bi, t) ->
      env !! enc_x = Some (bi, t).

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
  | Read_address S bi t n v v' enc_x
      (Hbinv : blockofinv (bi, t) = enc_x)
      (Henv : lookup enc_x (vars S) = Some v)
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
  | Follow_left addr t0 t1 :
    follow_path 0 (addr, TPair t0 t1) (addr, t0)
  | Follow_right addr t0 t1 :
    follow_path 0 (addr, TPair t0 t1) (addr +o sizeof t0, t1)
  | Follow_loc addr t :
    follow_path 0 (addr, t) (addr, t).

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

  Inductive addr_lspath_equiv (S : HLPL_state) :
    address -> type -> lspath -> Prop :=
  | Addr_lspath_base lsp addr bi t enc_x
      (H : blockof enc_x = (bi, t))
      (Hsp : lsp = (enc_x, []))
      (Haddr : addr = (bi, 0)) :
    addr_lspath_equiv S addr t lsp
  | Addr_lspath_pair_first addr lsp t0 t1
      (Hpair : get_node ( S.[ lsp ]l ) = HLPL_pairC)
      (Hrec : addr_lspath_equiv S addr (TPair t0 t1) lsp) :
    addr_lspath_equiv S addr t0 (lsp +++l [LFirst])
  | Addr_lspath_pair_second addr lsp t0 t1
      (Hpair : get_node (S.[lsp]l) = HLPL_pairC)
      (Hrec : addr_lspath_equiv S addr (TPair t0 t1) lsp) :
    addr_lspath_equiv S (addr +o sizeof t0) t1 (lsp +++l [LSecond])
  | Addr_lspath_loc addr lsp t l
      (Hloc : get_node (S.[lsp]l) = HLPL_locC l)
      (Hrec : addr_lspath_equiv S addr t lsp) :
    addr_lspath_equiv S addr t (lsp +++l [LLoc]).

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
        forall (enc_x : positive) (v : HLPL_val) perm (sp : spath), 
          eval_place S perm (enc_x, []) sp ->
          valid_spath S sp ->
          exists bi t, blockof enc_x = (bi, t) 
      ; indirections_well_typed :
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

  (* This hypothesis is necessary to prove that the diagram commutes with dereference, it should be a consequence that the PL_state Spl is the concretization of the HLPL state S *)
  Definition addresses_are_compatible (S : HLPL_state) (Spl : PL_state) :=
    forall addr t sp l,
      addr_spath_equiv S addr (TRef t) sp ->
      get_node (S.[ sp ]) = ptrC(l) ->
      exists addr',
      lookup_heap_at_addr addr (TRef t) Spl = [PL_address addr'] /\
      addrof l = Some addr'.

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
      (S.[ sp ]) = v ->
      v <> bot ->
      exists addr t vl,
        addr_spath_equiv S addr t sp /\ concr_hlpl_val v t vl /\ lookup_heap_at_addr addr t Spl = vl.
  Proof.
    induction sp using ListBackInd.state_path_back_ind ;
      intros v [Hconcr_heap Hconcr_env] HSx Hbot.
    remember (blockof enc_x).1 as bi. remember (blockof enc_x).2 as t.
    assert (Heqbit : blockof enc_x = (bi, t))
      by (subst ; rewrite <- surjective_pairing ; reflexivity).
    - specialize (Hconcr_heap enc_x bi t v HSx Hbot Heqbit).
      destruct Hconcr_heap as [vl [Hconcr_val Hheap] ].
      exists (bi, 0), t, vl. repeat split ; auto.
      * eapply Addr_spath_base ; eauto.
      * unfold lookup_heap_at_addr ; simpl.
        replace (heap Spl !! bi) with (Some vl) by auto.
        rewrite drop_0, (val_concr_implies_correct_type_size v t vl), firstn_all ;
          auto.
    - rewrite sget_app in HSx.
      destruct (S.[sp]) eqn:E ;
        try (simpl in HSx ; rewrite nth_error_nil in HSx ; subst v ; contradiction).
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
        * rewrite nth_error_nil in HSx ; subst v ; contradiction.
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
        * rewrite nth_error_nil in HSx ; subst v ; contradiction.
  Qed.

  Lemma state_concr_implies_val_concr_at_addr : 
    forall S Spl sp addr t v,
      concr_hlpl S Spl ->
      (S.[ sp ]) = v ->
      v <> bot ->
      addr_spath_equiv S addr t sp ->
      exists vl,
         concr_hlpl_val v t vl /\ lookup_heap_at_addr addr t Spl = vl.
  Proof.
    intros S Spl sp addr t v Hconcr HS_sp Hbot Hequiv.
    destruct (state_concr_implies_val_concr _ _ _ _ Hconcr HS_sp Hbot)
      as [addr' [t' [vl [Hequiv' [Hconcr_val Hlu ] ] ] ] ].
    pose proof (addr_spath_equiv_deterministic_addr _ _ _ _ _ _ Hequiv' Hequiv) as Heq.
    pose proof (addr_spath_equiv_deterministic_type _ _ _ _ _ _ Hequiv' Hequiv) as Heqt.
    subst addr' t'; clear Hequiv'.
    exists vl ; split ; auto.
  Qed.
  
  (** Concretization of states implies addresses are compatible *)
  Lemma concr_implies_addresses_are_compatible :
    forall S Spl, Compatible S -> concr_hlpl S Spl -> addresses_are_compatible S Spl.
  Proof.
    intros S Spl [_ Hcorr_addr _] Hconcr_state addr t sp l Hequiv Hnode.
    assert (HSpl_sp : ∃ (addr : address) (t : type) (vl : pl_val),
          addr_spath_equiv S addr t sp
          ∧ concr_hlpl_val (ptr (l)) t vl ∧ lookup_heap_at_addr addr t Spl = vl).
    {
      apply state_concr_implies_val_concr ; auto.
      destruct (S .[ sp ]) ; try discriminate.
      simpl in Hnode. injection Hnode ; auto.
    }
    destruct HSpl_sp as [addr' [t' [vl [Hequiv' [Hconcr_val Hlu_heap] ] ] ] ].
    assert (Ht': t' = (TRef t))
      by (eapply addr_spath_equiv_deterministic_type ; eauto) ; subst.
    assert (Haddr: addr = addr')
      by (eapply addr_spath_equiv_deterministic_addr; eauto) ; subst. clear Hequiv'.
    inversion Hconcr_val ; subst. exists addr. intuition.
Qed.

  Lemma le_implies_addresses_are_compatible :
    forall S Spl, le_pl_hlpl Spl S -> addresses_are_compatible S Spl.
  Proof.
  Admitted.

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
    destruct HComp as [_ Hwell_typed Hcorr_addrof Hloc].
    inversion Hproj ; subst.
    - nodes_to_val.
      assert (Htemp: ∃ vl, concr_hlpl_val (HLPL_ptr l) t vl ∧
                      lookup_heap_at_addr addr t Spl' = vl).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & Hlu_addr). inversion Hconcr_val ; subst.
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
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (vl & Hconcr_val & _). inversion Hconcr_val ; subst.
      exists addr, t0 ; split ; try constructor.
      eapply Addr_spath_pair_first ; eauto.
    - nodes_to_val.
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

  (* TODO: drop induction, use spath_addres_path_simul *)
  Lemma eval_place_hlpl_pl_equiv :
    forall S Spl p sp addr t perm,
      le_pl_hlpl Spl S ->
      eval_place S perm p sp ->
      eval_place_pl Spl p (addr, t) ->
      addr_spath_equiv S addr t sp.
  Proof.
    intros S Spl p sp addr t perm
      (Spl' & HComp & (Hconcr_heap & Hconcr_env) & Henv & Hheap) Hplace Hplace_pl.
    inversion Hplace as [(v & HS_x & Hvvp) Hpath].
    inversion Hplace_pl as [bi [t0 [Hlu Hpath_pl] ] ].
    rewrite surjective_pairing with (p := p) in *.
    simpl in *. remember p.1 as x. remember p.2 as path.
    remember (encode_var x, []) as sp0. clear Heqx Heqpath.
    induction Hpath ; inversion Hpath_pl; subst.
    - unfold lookup_block_and_type_env in Hlu.
      eapply Addr_spath_base ; try eauto.
      destruct (blockof (encode_var x)) as [bi' t'] eqn:Hbo ; eauto.
      assert (Heq: env Spl' !! encode_var x = Some (bi', t')) by eauto.
      rewrite <- Henv, Hlu in Heq ; injection Heq as Heq ; subst. reflexivity.
  Admitted.

End Concretization.



Lemma HLPL_PL_Read :
  forall blockof addrof S Spl perm p sp addr v t,
    eval_place S perm p sp ->
    le_pl_hlpl blockof addrof Spl S ->
    addr_spath_equiv blockof S addr t sp ->
    S.[sp] = v ->
    v <> bot ->
    exists vl, 
      lookup_heap_at_addr addr t Spl = vl /\
        forall vl',
          concr_hlpl_val addrof v t vl' -> le_block vl vl'.
Proof.
  intros bo ao S Spl perm p sp addr v t
    [Hvalid Hpath] [Spl' [HComp [Hconcr [Hle_env Hle_heap] ] ] ] Hequiv HS_sp Hbot.
  destruct
    (state_concr_implies_val_concr_at_addr bo ao _ _ _ _ _ _ Hconcr HS_sp Hbot Hequiv)
    as [vl [ Hconcr_val Hlu] ].
  exists (lookup_heap_at_addr addr t Spl) ; split ; auto.
  intros vl' Hvl'.
  apply le_heap_implies_le_block with (addr := addr) (t := t) in Hle_heap.
  apply concr_val_implies_concr_val_comp in Hconcr_val, Hvl'.
  rewrite Hconcr_val in Hvl' ; injection Hvl' ; intros ; subst ; auto.
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
  intros bo ao S Spl op vS1 (Spl' & Hcomp & Hconcr & Hle) Heval.
  induction Heval.
  - exists bo, ao, [PL_int n], TInt. repeat split ; try constructor.
    exists Spl' ; auto.
  - exists bo, ao.
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
