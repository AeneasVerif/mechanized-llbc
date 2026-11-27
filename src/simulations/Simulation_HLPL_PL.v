Require stdpp.base.
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
Import list_monad.list.
From stdpp Require list.

Require Import semantics.HLPL.
From rustc Require Import PL.
Require Import Axioms Coqlib Integers Floats AST Values.
From Stdlib Require Import Zwf.
Require Import PathToSubtree.
Require Import Stdlib.Classes.RelationClasses.

Opaque sset.

Open Scope Z_scope.

Notation "p .1" := (fst p).
Notation "p .2" := (snd p).
Local Notation "a # b" := (PXMap.get b a) (at level 1).
Local Notation "a ## b" := (PTree.get b a) (at level 1).

Lemma nth_error_to_lookup {A} (l : list A) (i : nat) :
  nth_error l i = lookup i l.
Proof. generalize dependent i. induction l ; intros [ | i ] ; simpl; auto. Qed.

Lemma list_app_elem_not_nil {A : Type} :
  forall (l : list A) (a : A), l ++ [ a ] <> [].
Proof. intros l a Hcontr. apply app_eq_nil, proj2 in Hcontr. discriminate. Qed.

Lemma spath_app_elem_not_nil :
  forall (sp : spath) (n : nat) enc_x, sp +++ [ n ] <> (enc_x, []).
Proof.
  intros. unfold app_spath_vpath. intros contra.
  injection contra as _ H. destruct (list_app_elem_not_nil sp.2 n H).
Qed.
    
Ltac sp_discriminate_or_find_equalities :=
  match goal with
  | H1: ?E = NTuple _, H2: ?E = NLoc (_) |- _ => rewrite H2 in H1 ; discriminate
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

(* Concretization of HLPL values to PL values *)
Section Concretization.
  Variable blockof : positive -> block * type.
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
  Inductive eval_type_val (v : value) (ti : type) : vpath -> type -> Prop :=
  | Eval_base_type :
    eval_type_val v ti nil ti
  | Eval_loc_type_val vp t l
    (Hnode : get_node ( v.[[ vp ]] ) = NLoc l)
    (Hrec : eval_type_val v ti vp t) :
    eval_type_val v ti (vp ++ [0%nat]) t
  | Eval_tuple_val vp n len t tl
    (Hnode : get_node ( v.[[ vp ]] ) = NTuple len)
    (Htypelist_size : List.length tl = len)
    (Htype : List.nth_error tl n = Some t)
    (Hrec : eval_type_val v ti vp (TTuple tl)) :
    eval_type_val v ti (vp ++ [ n ]) t
  .

  Inductive eval_type (S : state) : spath -> type -> Prop :=
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
    pose proof (@list_app_elem_not_nil nat ) as H.
    intros v vp tinit t0 t1 Het0. generalize dependent t1.
    induction Het0 ; intros ? Het'.
    - inversion Het' ; subst ; auto.
      * apply H in H1. contradiction.
      * apply H in H1. contradiction.
    - inversion Het' ; subst ; auto.
      * symmetry in H1. apply H in H1. contradiction.
      * apply app_inj_tail in H1 as (? & ?) ; subst.
        rewrite Hnode in Hnode0. injection Hnode0 as <-. auto.
      * apply app_inj_tail in H1 as (? & ?) ; subst ; congruence.
    - inversion Het' ; subst.
      * symmetry in H1. apply H in H1. contradiction.
      * apply app_inj_tail in H1 as (? & ?) ; subst ; congruence.
      * apply app_inj_tail in H1 as (? & ?) ; subst.
        apply IHHet0 in Hrec. injection Hrec as <-.
        rewrite Htype in Htype0. injection Htype0 as <-. auto.
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

  Inductive concr_hlpl_val : value -> type -> list memval -> Prop :=
  | Concr_lit n :
    concr_hlpl_val (VInt n) TInt (make_int64 n)
  | Concr_bool b :
    concr_hlpl_val (VBool b) TBool (make_bool b)
  | Concr_bot s t (Hs : s = ListDef.repeat Undef (sizeof t)) : 
    concr_hlpl_val bot t s
  | Concr_loc l v t bytes
      (Hv : concr_hlpl_val v t bytes) :
    concr_hlpl_val (VLoc l v) t bytes
  | Concr_ptr_loc l addr t
      (Haddr : addrof l = Some (addr, t)) :
    concr_hlpl_val (VPtr l) (TRef t) (make_ptr64 addr)
  | Concr_tuple vl tl bytes :
    concr_hlpl_val_tuple vl tl bytes ->
    concr_hlpl_val (VTuple vl) (TTuple tl) bytes
  with concr_hlpl_val_tuple : list value -> list type -> list memval -> Prop :=
  | Concr_tuple_Nil : concr_hlpl_val_tuple [] [] []
  | Concr_tuple_Cons v vl t tl bytes0 bytes1 :
    concr_hlpl_val v t bytes0 ->
    concr_hlpl_val_tuple vl tl bytes1 ->
    concr_hlpl_val_tuple (v :: vl) (t :: tl) (bytes0 ++ bytes1)
  .

  Fixpoint concr_hlpl_val_comp (v : value) (t : type) :=
    match v, t with
    | VInt n, TInt =>
        Some (make_int64 n)
    | VBool b', TBool =>
        Some (make_bool b')
    | VBottom, _ =>
        Some (ListDef.repeat Undef (sizeof t))
    | VLoc l v, t =>
        concr_hlpl_val_comp v t
    | VPtr l, TRef t =>
        match addrof l with
        | Some (addr, t') =>
            if (base.decide (t = t')) then
              Some (make_ptr64 addr)
            else
              None
        | _ => None
        end
    | VTuple vl, TTuple tl =>
        (fix go vl tl :=
           match vl, tl with
           | [], [] => Some []
           | v :: vl, t :: tl =>
               let byteso0 := concr_hlpl_val_comp v t in
               let byteso1 := go vl tl in
               match byteso0, byteso1 with
               | Some bytes0, Some bytes1 => Some (bytes0 ++ bytes1)
               | _, _ => None
               end
           | _, _ => None
           end
        ) vl tl
    | _, _ => None
    end.

  Lemma concr_val_tuple_implies_valuelist_typelist_same_size vl tl bytes :
    concr_hlpl_val_tuple vl tl bytes -> List.length vl = List.length tl.
  Proof. intro H ; induction H ; cbn ; congruence. Qed.

  Lemma concr_val_comp_implies_concr_val: forall v t bytes,
      concr_hlpl_val_comp v t = Some bytes -> concr_hlpl_val v t bytes.
  Proof.
    intros v ; induction v ; intros.
    - destruct t; simpl in * ;
        injection H ; intros ; constructor ; easy. 
    - destruct t; simpl in * ;
        try injection H as H; subst ; try constructor ; discriminate.
    - destruct t; simpl in * ;
        try injection H as H; subst ; try constructor ; discriminate.
    - inversion H. constructor. apply IHv, H1.
    - destruct t ; simpl in * ; try discriminate.
      destruct (addrof l) eqn:Haddr ; try discriminate.
      destruct p ; destruct (base.decide (t = t0)).
      * injection H as H ; subst. apply Concr_ptr_loc, Haddr.
      * discriminate.
    - destruct t ; try discriminate. generalize dependent bytes. generalize tl.
      induction H ; intros.
      * destruct tl0 ; inversion H0 ; subst ; repeat constructor.
      * destruct tl0 ; cbn in H0 ; [ discriminate | ].
        destruct (concr_hlpl_val_comp a t) eqn:Hcompa ; [ | discriminate ].
        destruct (concr_hlpl_val_comp (VTuple l) (TTuple tl0)) eqn:Hcompvl ;
        cbn in Hcompvl ; rewrite Hcompvl in H0 ; [ | discriminate ].
        apply p in Hcompa. apply IHlist_all in Hcompvl. inversion Hcompvl ; subst.
        injection H0 as <-. repeat constructor ; auto.
  Qed.  

  Lemma concr_val_implies_concr_val_comp : forall v t bytes,
      concr_hlpl_val v t bytes -> concr_hlpl_val_comp v t = Some bytes.
  Proof.
    intros v ; induction v ; intros t bytes concr_val ; inversion concr_val ;
      subst ; simpl ; try reflexivity.
    - apply IHv. exact Hv.
    - rewrite Haddr. destruct (decide (t0 = t0)) ; easy.
    - clear concr_val. generalize dependent bytes. generalize dependent tl.
      induction H ; intros * concr_tuple ; inversion concr_tuple ; subst.
      * reflexivity.
      * apply p in H2. apply IHlist_all in H5. rewrite H5, H2. reflexivity.
  Qed.

  Lemma concr_val_eq_concr_val_comp : forall v t bytes,
      concr_hlpl_val v t bytes <-> concr_hlpl_val_comp v t = Some bytes.
  Proof.
    split.
    apply concr_val_implies_concr_val_comp. apply concr_val_comp_implies_concr_val.
  Qed.

  Lemma concr_val_size : forall v bytes t,
      concr_hlpl_val v t bytes -> sizeof t = length bytes.
  Proof.
    induction v ; intros bytes t Hconcr ; inversion Hconcr ; subst ; auto.
    - rewrite repeat_length. reflexivity.
    - destruct b ; cbn ; reflexivity.
    - simpl. clear Hconcr. generalize dependent bytes. generalize dependent tl.
      induction H ; intros * concr_tuple ; inversion concr_tuple ; subst.
      * reflexivity.
      * simpl. rewrite length_app. apply IHlist_all in H5. apply p in H2. lia.
  Qed.

  Lemma concr_val_tuple_implies_concr_val vl tl bytes :
    concr_hlpl_val_tuple vl tl bytes ->
    forall n v, List.nth_error vl n = Some v ->
             exists bytes0 bytesa bytesn t,
             concr_hlpl_val v t bytesa /\ bytes = bytes0 ++ bytesa ++ bytesn /\
               List.nth_error tl n = Some t.
  Proof.
    intro H. induction H ; intros.
    - rewrite nth_error_nil in H. congruence.
    - destruct n.
      * injection H1 as <-. cbn.
        exists [], bytes0, bytes1, t. repeat split ; auto.
      * destruct (IHconcr_hlpl_val_tuple _ _ H1)
          as (bytes0' & bytesa & bytesn' & t' & concr_val & bytes_eq & Htype). subst.
        exists (bytes0 ++ bytes0'), bytesa, bytesn', t'. repeat split; auto.
        rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma concr_val_tuple_implies_concr_val' :
    forall vl tl bytes,
      concr_hlpl_val_tuple vl tl bytes <->
      exists bytes_list,
        concat bytes_list = bytes /\
          length vl = length bytes_list /\
          length tl = length bytes_list /\
          Forall (fun n => forall v t,
                      nth_error vl n = Some v ->
                      nth_error tl n = Some t ->
                      exists bytesn,
                        List.nth_error bytes_list n = Some bytesn /\
                          concr_hlpl_val v t bytesn)
            (seq 0 (List.length bytes_list)).
  Proof.
    intros ; split ; intros.
    {
      induction H ; intros.
      - cbn. exists []. repeat split ; try reflexivity.
        apply Forall_forall. intros. rewrite nth_error_nil in H0. discriminate.
      - destruct (IHconcr_hlpl_val_tuple)
          as (bytes_list & bytes_eq & vl_len & tl_len & Hforall).
        exists (bytes0 :: bytes_list). split ; [ cbn ; rewrite bytes_eq ; reflexivity | ].
        cbn. repeat split ; try congruence ; constructor.
        * intros ? ? [=<-] [=<-]. cbn. exists bytes0 ; split ; [ reflexivity | assumption ].
        * rewrite <- seq_shift, Forall_map with (f := S) ; assumption.
    }
    {
      generalize dependent bytes. generalize dependent tl. generalize dependent vl.
      induction vl ; intros ;
      destruct H as (bytes_list & bytes_eq & vlen & tlen & Hforall).
      - cbn in vlen, tlen. rewrite <- vlen in tlen.
        destruct bytes_list ; destruct tl ; try discriminate. cbn in bytes_eq.
        subst ; constructor.
      - cbn in vlen. destruct bytes_list ; destruct tl ; try discriminate.
        subst. cbn. inversion Hforall ; subst.
        destruct (H1 _ _ eq_refl eq_refl) as (bytes0 & [=->] & concr0).
        constructor ; [ assumption | ].
        rewrite <- seq_shift, Forall_map in H2. cbn in H2.
        apply IHvl. eexists ; repeat split ; eauto.
    }
  Qed.

  Lemma slice_bytes_list (bytes : list memval) tl :
    List.length bytes = sizeof (TTuple tl) ->
    bytes =
      concat (imap
                (fun i t => firstn (sizeof t) (skipn (pst tl i) bytes)) tl).
  Proof.
    generalize dependent bytes. induction tl ; intros bytes Hsize.
    - cbn in *. apply LB.nil_length_inv in Hsize. assumption.
    - cbn. cbn in Hsize.
      assert (Hsize': Datatypes.length (skipn (sizeof a) bytes) = sizeof (TTuple tl)).
      { rewrite length_skipn ; cbn ; unfold sum ; lia. }
      specialize (IHtl (skipn (sizeof a) bytes) Hsize').
      rewrite <- (LB.take_drop (sizeof a) bytes) at 1 ; rewrite IHtl ; f_equal ; f_equal.
      apply imap_ext ; intros. cbn.
      rewrite skipn_skipn, Nat.add_comm. reflexivity.
  Qed.

  Lemma concr_val_tuple_implies_concr_val'' :
    forall vl tl bytes,
      concr_hlpl_val_tuple vl tl bytes <->
        length vl = length tl /\
          sizeof (TTuple tl) = length bytes /\
          forall n v t,
            nth_error vl n = Some v ->
            nth_error tl n = Some t ->
            concr_hlpl_val v t (firstn (sizeof t) (skipn (pst tl n) bytes)).
  Proof.
    intros. split.
    {
      intro H. induction H.
      - repeat split. intros. cbn in H. rewrite nth_error_nil in H. discriminate.
      - destruct IHconcr_hlpl_val_tuple as (Heq1 & Heq2 & IH).
        apply concr_val_size in H as Hlen.
        repeat split ; simpl sizeof in * ;
          [cbn ; congruence | rewrite length_app ; lia | ].
        intros * nth_val nth_ty.
        destruct n ; cbn in *.
        * injection nth_val as <-. injection nth_ty as <-.
          rewrite Hlen, skipn_0, LB.take_app_length. assumption.
        * rewrite !Hlen, LB.drop_app_add. auto.
    }
    {
      intros (Heq1 & Heq2 & IH). rewrite concr_val_tuple_implies_concr_val'.
      symmetry in Heq2. apply slice_bytes_list in Heq2.
      exists (imap (fun i t => firstn (sizeof t) (skipn (pst tl i) bytes)) tl).
      repeat split ; auto.
      - rewrite length_imap. assumption.
      - rewrite length_imap. reflexivity.
      - apply LR.Forall_true ; intros. 
        exists (firstn (sizeof t) (skipn (pst tl x) bytes)).
        rewrite nth_error_to_lookup, list_lookup_imap, <- nth_error_to_lookup, H0 ;
          cbn ; firstorder.
    }
  Qed.

  Lemma concr_val_add_loc :
    forall v vp l t bytes,
      concr_hlpl_val v t bytes ->
      concr_hlpl_val (v.[[vp <- loc (l, v.[[vp]]) ]]) t bytes.
  Proof.
    intros until vp. generalize dependent v. induction vp ; intros.
    - simpl. constructor ; auto.
    - destruct v ; inversion H ; subst ; auto.
      + destruct a ; auto. simpl. constructor. auto.
      + generalize dependent a. induction H1 ; intro a.
        * simpl ; repeat constructor.
        * induction a.
          ** cbn. repeat constructor ; auto.
          ** cbn. assert (concr_hlpl_val (VTuple vl) (TTuple tl) bytes1)
               by (constructor ; assumption). repeat constructor. assumption.
             inversion IHa ; subst.
             apply IHconcr_hlpl_val_tuple with (a := a) in H2. inversion H2 ; subst.
             assumption.
  Qed.

  Lemma concr_val_remove_loc :
    forall v vloc vp l t bytes,
      v.[[ vp ]] = loc(l, vloc) ->
      concr_hlpl_val v t bytes ->
      concr_hlpl_val (v.[[vp <- v.[[ vp ++ [0%nat] ]] ]]) t bytes.
  Proof.
    assert (Hbot : VBottom = bot) by reflexivity.
    intros until vp. generalize dependent v. induction vp ; intros.
    - simpl app. simpl in H. rewrite H. simpl.
      inversion H0 ; subst ; congruence.
    - destruct v ; inversion H ; subst ; inversion H0 ; subst ; auto.
      + destruct a ; cbn in H ; [ | rewrite nth_error_nil, Hbot, vget_bot in H ; auto ].
        cbn. constructor. eauto.
      + generalize dependent a. induction H3.
        * repeat constructor.
        * intros. destruct a.
          ** cbn. repeat constructor ; eauto.
          ** specialize (IHconcr_hlpl_val_tuple (Concr_tuple _ _ _ H3) a H1).
             cbn in H2. rewrite H2 in IHconcr_hlpl_val_tuple.
             specialize (IHconcr_hlpl_val_tuple eq_refl).
             cbn. rewrite vget_app, H2. repeat constructor ; [ assumption | ].
             inversion IHconcr_hlpl_val_tuple ; subst.
             rewrite vget_app, H2 in H6. auto.
  Qed.

  Lemma concr_val_deterministic :
    forall v t bytes0 bytes1,
      concr_hlpl_val v t bytes0 ->
      concr_hlpl_val v t bytes1 ->
      bytes0 = bytes1.
  Proof. intros. apply concr_val_implies_concr_val_comp in H, H0. congruence. Qed.

  Definition concr_hlpl_mem (S : state) (m : Mem.mem) : Prop :=
    forall enc_x bi t v,
      valid_spath S (enc_x, []) ->
      S.[ (enc_x, []) ] = v ->
      blockof enc_x = (bi, t) ->
      (exists bytes,
        concr_hlpl_val v t bytes /\
          Mem.getN (sizeof t) 0 ((Mem.mem_contents m) # bi) = bytes) /\ 
        (Mem.range_perm m bi 0 (sizeof t) Cur Freeable).

  Definition concr_hlpl_env (S : state) (env : PTree.t (block * type)) : Prop :=
    forall enc_x bi t,
      valid_spath S (enc_x, []) ->
      blockof enc_x = (bi, t) ->
      env ## enc_x = Some (bi, t).

  Definition concr_hlpl (S : state) (Spl : PL_state) : Prop :=
    concr_hlpl_mem S (mem Spl) /\ concr_hlpl_env S (env Spl).

  (** [add_spath_equiv S Spl addr sp] is inhabited when reading in S.[p] corresponds dto reading in Spl.mem(addr) *)

  Inductive off_vpath_equiv (v : value) (t : type) : offset -> type -> vpath -> Prop :=
  | Offset_vpath_base :
    off_vpath_equiv v t (0%nat) t nil
  | Offset_vpath_loc off vp t' l
      (Hloc : get_node (v.[[ vp ]]) = NLoc l)
      (Hrec : off_vpath_equiv v t off t' vp) :
    off_vpath_equiv v t off t' (vp ++ [0%nat])
  | Offset_vpath_tuple n len off vp t' tl
      (Htuple : get_node (v.[[ vp ]]) = NTuple len)
      (Htypelist_size : length tl = len)
      (Htype : nth_error tl n = Some t')
      (Hrec : off_vpath_equiv v t off (TTuple tl) vp) :
          off_vpath_equiv v t (off + partial_sizeof_tuple tl n) t' (vp ++ [n]).

  Lemma offset_is_positive :
    forall v ti off t vp,
      off_vpath_equiv v ti off t vp -> 0 <= off.
  Proof. intros * vpath_equiv. induction vpath_equiv ; lia. Qed.

  Lemma offset_less_modulus :
    forall v ti off t vp,
      off_vpath_equiv v ti off t vp -> off < Ptrofs.modulus.
  Proof.
  Admitted.

  Lemma offset_range :
    forall v ti off t vp,
      off_vpath_equiv v ti off t vp -> 0 <= off < Ptrofs.modulus.
  Proof.
    intros * ; split. 
    - eapply offset_is_positive ; eauto.
    - eapply offset_less_modulus ; eauto.
  Qed.

  Inductive addr_spath_equiv (S : state) : address -> type -> spath -> Prop :=
  | Addr_spath_base sp v addr tinit t
      (H : blockof sp.1 = (addr.1, tinit))
      (Hsp1 : S.[(sp.1, [])] = v)
      (Hvp : valid_spath S (sp.1, []))
      (Hvequiv: off_vpath_equiv v tinit addr.2 t sp.2) :
    addr_spath_equiv S addr t sp.

  Notation "addr ~^{ S , t } sp" := (addr_spath_equiv S addr t sp) (at level 40).

  Lemma addr_spath_equiv_offset_range :
    forall S sp addr t,
      addr ~^{S, t} sp -> 0 <= addr.2 < Ptrofs.modulus.
  Proof.
    intros * equiv. inversion equiv ; subst.
    eapply offset_range ;eauto.
  Qed.

  Lemma Addr_spath_tuple_n:
    forall S sp addr t tl len n,
      get_node (S.[ sp ]) = NTuple len ->
      length tl = len ->
      nth_error tl n = Some t ->
      addr ~^{S, (TTuple tl)} sp ->
      addr +o (partial_sizeof_tuple tl n) ~^{S, t} (sp +++ [n%nat]).
  Proof.
    intros * Hnode Hlen Htl Hequiv.
    inversion Hequiv ; subst. econstructor ; eauto. simpl.
    eapply Offset_vpath_tuple ; eauto.
    rewrite <- sget_app. unfold app_spath_vpath. simpl.
    rewrite <- surjective_pairing ; eassumption.
  Qed.

  Lemma Addr_spath_loc :
    forall S sp addr t l,
      get_node (S.[ sp ]) = NLoc l ->
      addr ~^{S, t} sp <->
      addr ~^{S, t} (sp +++ [0%nat]).
  Proof.
    intros S sp addr t l Hnode. split ; intro Hequiv.
    - inversion Hequiv ; subst. econstructor ; eauto. simpl.
      apply Offset_vpath_loc with (l := l); auto.
      rewrite <- sget_app. unfold app_spath_vpath. simpl.
      rewrite <- surjective_pairing ; assumption.
    - inversion Hequiv ; subst. simpl fst in *. simpl snd in *.
      rewrite (spath_var_app_vpath sp), sget_app in Hnode.
      pose proof app_cons_not_nil.
      inversion Hvequiv ; subst ; sp_discriminate_or_find_equalities ; try congruence.
      econstructor ; eauto.
  Qed.

  Lemma off_vpath_equiv_sizeof :
    forall vi ti t off vp,
      off_vpath_equiv vi ti off t vp ->
      off + sizeof t <= sizeof ti.
  Proof.
    intros. induction H ; simpl in * ; try lia.
    rewrite <- Z.add_assoc.
    apply partial_sizeof_tuple_last in Htype as ?.
    replace (pst tl n + sizeof t') with (Z.of_nat (pst tl (S n))) by lia.
    pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl (S n)). cbn in H1. lia.
  Qed.

  Lemma off_vpath_equiv_eval_type :
    forall v vp tinit t,
      (exists off, off_vpath_equiv v tinit off t vp) <-> eval_type_val v tinit vp t.
  Proof.
    intros v vp tinit t ; split ; [intros (off & Hvequiv) | intros Het ].
    { induction Hvequiv ; subst ; econstructor ; eauto. }
    {
      induction Het.
      - exists 0. econstructor ; eauto.
      - destruct IHHet as (off & Hvequiv).
        exists off. eapply Offset_vpath_loc ; eauto.
      - destruct IHHet as (off & Hvequiv).
        exists (off + partial_sizeof_tuple tl n). eapply Offset_vpath_tuple ; eauto.
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
      - nodes_to_val. specialize (IHoff_vpath_equiv (loc (l, v'))).
        rewrite vset_app_split, Heqv0. simpl. eapply Offset_vpath_loc ; auto.
        rewrite vset_vget_equal ; eauto.
        apply valid_get_node_vget_not_bot. simpl in *. intros ?. congruence.
      - nodes_to_val. apply f_equal with (f := get_node) in Heqv0 as H'.
        specialize (IHoff_vpath_equiv (v.[[ vp ]].[[ [n] <- v']])).
        rewrite <- vset_app_split in IHoff_vpath_equiv.
        econstructor ; eauto.
        rewrite get_node_vset_vget_strict_prefix. simpl in H'. rewrite <- H0. apply H'.
        repeat econstructor.
    }
    {
      remember (v .[[ vp <- v']]) as vi. generalize dependent v'.
      induction H ; intros ; subst ; simpl.
      - constructor.
      - nodes_to_val.
        rewrite get_node_vset_vget_strict_prefix in H0 by (repeat econstructor).
        nodes_to_val.
        assert (v .[[ vp ++ [0%nat] <- v']] = v .[[ vp <- loc (l, v')]]) by
          (rewrite vset_app_split, Heqv1 ; auto).
        specialize (IHoff_vpath_equiv _ H1).
        eapply Offset_vpath_loc ; eauto.
      - nodes_to_val.
        specialize (IHoff_vpath_equiv (v.[[ vp ]].[[ [n] <- v']])).
        rewrite <- vset_app_split in IHoff_vpath_equiv.
        econstructor ; eauto.
        apply f_equal with (f := get_node) in Heqv0.
        rewrite get_node_vset_vget_strict_prefix in Heqv0 by (repeat econstructor).
        rewrite <- H0. apply Heqv0.
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
        eapply Offset_vpath_loc ; eauto.
        rewrite get_node_vset_vget_not_prefix ; eauto.
      - apply not_vprefix_app in Hpref.
        econstructor ; eauto. rewrite get_node_vset_vget_not_prefix ; eauto.
    }
    {
      induction Hvequiv ; subst.
      - apply Offset_vpath_base.
      - apply not_vprefix_app in Hpref. apply IHHvequiv in Hpref as Hvequiv'.
        eapply Offset_vpath_loc ; eauto.
        rewrite get_node_vset_vget_not_prefix in Hloc ; eauto.
      - apply not_vprefix_app in Hpref. econstructor ; eauto.
        rewrite get_node_vset_vget_not_prefix in Htuple ; eauto.
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
        assert (vprefix vp0 vp0) by (exists [] ; rewrite app_nil_r ; auto). auto.
      + assert (vstrict_prefix vp1 vp0) by (repeat econstructor ; eauto). auto.
  Qed.

  Lemma addr_spath_equiv_sset_equal : 
    forall S addr t sp v,
      addr ~^{S, t} sp <->
      addr ~^{(S .[ sp <- v]), t} sp /\ valid_spath S (sp.1, []).
  Proof.
    intros.
    assert (Hsp : sp = (sp.1, []) +++ sp.2) by
      (unfold "+++" ; simpl ; rewrite <- surjective_pairing ; auto).
    split ; intros.
    - inversion H ; subst. split ; auto. econstructor ; eauto.
      + apply sset_prefix_right_valid ; auto. rewrite Hsp ; simpl. exists sp.2. auto.
      + rewrite Hsp, sset_sget_prefix ; auto. apply off_vpath_equiv_vset_eq.
        simpl ; auto.
    - destruct H. inversion H ; subst. econstructor ; eauto.
      rewrite Hsp, sset_sget_prefix in Hvequiv; auto.
      apply off_vpath_equiv_vset_eq in Hvequiv ; assumption.
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
        * rewrite sset_sget_disj in Hvequiv ; auto. left ; auto.
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
    - inversion H ; inversion H0 ; subst ;
        try sp_discriminate_or_find_equalities; auto.
    - inversion H ; inversion H0 ; subst ;
        repeat (try sp_discriminate_or_find_equalities) ; subst ; eauto.
      assert (TTuple tl = TTuple tl0) by eauto. congruence.
  Qed.

  (* Addr_spath_equiv is a function: given state S and spath sp, addr and t are unique *)
  Lemma off_vpath_equiv_deterministic_off :
    forall vinit tinit vp off1 off2 t1 t2,
      off_vpath_equiv vinit tinit off1 t1 vp ->
      off_vpath_equiv vinit tinit off2 t2 vp ->
      off1 = off2.
  Proof.
    intros vinit tinit vp. induction vp using rev_ind ; intros.
    - inversion H ; inversion H0 ; subst ;
        try sp_discriminate_or_find_equalities; auto.
    - inversion H ; inversion H0 ; subst ;
        repeat (try sp_discriminate_or_find_equalities).
      * eapply IHvp ; eauto.
      * assert (off = off0) by (eapply IHvp ; eauto). subst.
        assert (TTuple tl = TTuple tl0)
          by (eapply off_vpath_equiv_deterministic_type ; eauto).
        congruence.
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
    intros vinit vp off t tinit Hvequiv. induction Hvequiv ; subst ; auto. 
    - constructor.
    - apply valid_vpath_app ; split ; auto ; nodes_to_val ; repeat econstructor.
    - apply valid_vpath_app ; split ; auto ; nodes_to_val ; repeat constructor.
      assert (exists v, nth_error vl n = Some v).
      { apply nth_error_Some'. apply nth_error_length in Htype. lia. }
      destruct H0 as (v & nth_vl). econstructor ; eauto. constructor.
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
      + exists t2, off2. rewrite app_nil_r in H. repeat split ; auto ; try lia.
        rewrite Z.sub_diag. constructor.
      + inversion H ; subst.
        * apply f_equal with (f := LB.last) in H3. simpl in H3.
          rewrite app_assoc, LB.last_snoc in H3. discriminate.
        * rewrite app_assoc in H3. apply app_inj_tail in H3 as [? ?] ; subst.
          destruct (IHvp2 _ _ _ Hrec) as (tint & offint & ? & ? & ?).
          exists tint, offint ; repeat split ; auto.
          apply Offset_vpath_loc with (l := l); auto. rewrite <- vget_app ; auto.
        * rewrite app_assoc in H3. apply app_inj_tail in H3 as [? ?] ; subst.
          apply IHvp2 in Hrec as (t1 & off1 & ? & ? & ?).
          exists t1, off1 ; repeat split ; auto. lia.
          rewrite Z.add_sub_swap. econstructor ; eauto.
          rewrite <- vget_app. assumption.
    - destruct H as (t1 & off1 & ? & ? & ?).
      remember (off2 - off1) as offdiff. generalize dependent off2.
      induction H1 ; intros.
      + rewrite app_nil_r. replace off2 with off1 by lia ; auto.
      + rewrite app_assoc. apply Offset_vpath_loc with (l := l).
        * rewrite vget_app ; auto.
        * apply IHoff_vpath_equiv ; auto.
      + rewrite <- vget_app in Htuple.
        replace off2 with (off + off1 + partial_sizeof_tuple tl n) by lia. 
        rewrite app_assoc. econstructor ; eauto.
        pose proof (offset_is_positive _ _ _ _ _ H1).
        apply IHoff_vpath_equiv ; lia.
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
      apply off_vpath_equiv_compose'.
      assert (0 <= off2) by (eapply offset_is_positive ; eauto).
      exists t1, off1 ; repeat split ; auto ; try lia.
      replace (off - off1) with off2 by lia ; auto.
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
      + unfold "+o". simpl.
        rewrite surjective_pairing with (p := addr), <- eq ; reflexivity.
      + econstructor ; eauto.
      + rewrite (spath_var_app_vpath sp), sget_app ; assumption.
    - destruct equiv as (t' & addr' & off & eq & equiv & vequiv).
      inversion equiv ; subst.
      apply Addr_spath_base with (v := (S.[(sp.1, [])])) (tinit := tinit) ; auto.
      simpl. apply off_vpath_equiv_compose.
      exists t', addr'.2, off ; repeat split ; auto.
      rewrite <- sget_app, <- (spath_var_app_vpath sp) ; assumption.
  Qed.
      
  Lemma add_loc_off_vpath_equiv_suffix :
    forall off vi vi' ti t vpl suff l,
      off_vpath_equiv vi ti off t (vpl ++ suff) ->
      vi' = (vi.[[vpl <- loc (l, vi.[[vpl]])]]) ->
      off_vpath_equiv vi' ti off t (vpl ++ [0%nat] ++ suff).
  Proof.
    intros. apply off_vpath_equiv_compose in H as (t1 & off1 & off2 & ? & ? & ?).
    rewrite app_assoc. apply off_vpath_equiv_compose.
    exists t1, off1, off2 ; repeat split ; auto.
    - apply Offset_vpath_loc with (l := l).
      + rewrite H0, vset_vget_equal ; try reflexivity.
        eapply off_vpath_equiv_implies_valid_vpath ; eauto.
      + rewrite H0, <- off_vpath_equiv_vset_eq ; assumption.
    - rewrite H0, vget_app, vset_vget_equal ; auto.
      eapply off_vpath_equiv_implies_valid_vpath ; eauto.
  Qed.

  Lemma add_loc_off_vpath_equiv_suffix' :
    forall off vi ti t vpl suff l,
      off_vpath_equiv vi ti off t (vpl ++ suff)  <->
        off_vpath_equiv (vi.[[vpl <- loc (l, vi.[[vpl]])]]) ti off t
          (vpl ++ [0%nat] ++ suff).
  Proof.
    intros. split ; intros.
    { 
      apply off_vpath_equiv_compose in H as (t1 & off1 & off2 & ? & ? & ?).
      rewrite app_assoc. apply off_vpath_equiv_compose.
      exists t1, off1, off2 ; repeat split ; auto.
      - apply Offset_vpath_loc with (l := l).
        + rewrite vset_vget_equal ; try reflexivity.
          eapply off_vpath_equiv_implies_valid_vpath ; eauto.
        + rewrite <- off_vpath_equiv_vset_eq ; assumption.
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
      - simpl in H1. apply off_vpath_equiv_vset_eq in Hrec.
        apply off_vpath_equiv_compose. repeat econstructor ; eauto.
      - rewrite vset_vget_equal in Htuple; auto. simpl in Htuple. congruence.
    } 
  Qed.

  Lemma add_loc_addr_spath_equiv_suffix :
    forall S addr t sp suff l,
      addr ~^{S, t} (sp +++ suff) <->
        addr ~^{(S.[ sp <- (loc (l, S.[sp])) ]), t} (sp +++ [0%nat] ++ suff) /\
          valid_spath S sp.
  Proof.
    intros. split ; intros.
    {
      inversion H ; subst. split.
      - econstructor ; eauto.
        + simpl fst. apply sset_prefix_right_valid ; eauto. exists sp.2.
          unfold "+++". simpl. symmetry. apply surjective_pairing.
        + simpl fst. simpl snd.
          replace (0%nat :: suff) with ([0%nat] ++ suff) by reflexivity.
          rewrite spath_var_app_vpath with (p := sp). simpl fst. simpl snd.
          rewrite sset_app_split, sset_sget_equal, sget_app. simpl in Hvp.
          eapply add_loc_off_vpath_equiv_suffix ; eauto. simpl fst in Hvp ; assumption.
      - apply addr_spath_equiv_implies_valid_spath, valid_spath_app in H as [? ?] ;
          auto.
    }
    {
      destruct H as [Hequiv Hvsp].
      assert (Hvsp' : valid_spath S (sp.1, [])) by
        (rewrite spath_var_app_vpath in Hvsp; eapply valid_spath_app ; eauto).
      inversion Hequiv ; subst. econstructor ; eauto ; simpl.
      simpl fst in *. simpl snd in *.
      replace (0%nat :: suff) with ([0%nat] ++ suff) in Hvequiv by reflexivity.
      apply add_loc_off_vpath_equiv_suffix' with (l := l); auto.
      rewrite <- sset_sget_prefix, <- spath_var_app_vpath, <- sget_app ; auto.
    }
  Qed.

  Lemma remove_loc_addr_spath_equiv_suffix :
    forall S addr t p suff l,
      get_node (S.[p]) = NLoc l ->
      addr ~^{S.[p <- S.[p +++ [0%nat] ] ], t} (p +++ suff) <->
        addr ~^{S, t} (p +++ [0%nat] ++ suff) /\
          valid_spath S p.
  Proof.
    intros * node. split ; intros.
    {
      nodes_to_val.
      assert (vsp : valid_spath S p)
        by (apply get_not_bot_valid_spath ; rewrite Heqv ; discriminate).
      split ; auto.
      rewrite sget_app, Heqv in H. simpl in H.
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
      + rewrite sget_app, Heqv. simpl. rewrite sset_sget_equal in vequiv ; auto.
    }
    {
      nodes_to_val. rewrite sget_app, Heqv. simpl.
      destruct H as (equiv & vsp).
      rewrite app_spath_vpath_assoc in equiv.
      apply addr_spath_equiv_compose in equiv.
      destruct equiv  as (t' & addr' & off & eq & equiv & vequiv).
      apply addr_spath_equiv_compose.
      exists t', addr', off ; repeat split ; auto.
      + apply addr_spath_equiv_sset_equal. 
        apply Addr_spath_loc with (l := l) ; auto.
      + rewrite sget_app, Heqv in vequiv. simpl in vequiv.
        rewrite sset_sget_equal ; auto.
    }
  Qed.

  Record Compatible (S : state) : Prop :=
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
          get_node (S.[sp]) = NLoc l ->
          addrof l = Some (addr, t)
      ; reachable_loc :
        forall l sp,
          get_node (S.[sp]) = NLoc l ->
          exists addr t, addr ~^{S, t} sp
      }.

  Inductive le_val : relation memval :=
  | lev_refl v : le_val v v
  | lev_poison v : le_val v Undef.


  Global Program Instance IsPreorderVal: PreOrder le_val.
  Next Obligation.
    constructor. Qed.
  Next Obligation.
  intros x y z Hxy Hyz ; inversion Hxy ; inversion Hyz ; subst ; try constructor. Qed.
  
  Definition le_block : relation (list memval) := Forall2 le_val.
  Global Instance IsPreorderBlock: PreOrder le_block.
  apply LR.PreOrder_instance_1, IsPreorderVal. Qed.

  Lemma le_block_not_contains_poison :
    forall bytes bytes', le_block bytes bytes' -> ~ (In Undef bytes') -> bytes = bytes'.
  Proof.
    intros. generalize dependent bytes. induction bytes' ; intros bytes Hle.
    - inversion Hle ; auto.
    - inversion Hle ; subst.
      simpl in H0. apply Decidable.not_or in H0 as [? ?].
      specialize (IHbytes' H0 l H4). subst.
      inversion H3 ; subst ; congruence.
  Qed.

  Definition le_mem : relation Memory.mem :=
    fun m1 m2 =>
      Mem.mem_access m1 = Mem.mem_access m2 /\
      Mem.nextblock m1 = Mem.nextblock m2 /\
      forall bi ofs v1 v2,
        ZXMap.get ofs ((Mem.mem_contents m1) # bi) = v1 ->
        ZXMap.get ofs ((Mem.mem_contents m2) # bi) = v2 ->
        le_val v1 v2.
  Global Program Instance IsPreorderMem: PreOrder le_mem.
  Next Obligation.
    repeat split ; auto.
    intros * access1 access2. subst ; constructor. Qed.
  Next Obligation.
    intros x y z (access_xy & nextblock_xy & le_xy)
      (access_yz & nextblock_yz & le_yz) ; repeat split ; try congruence.
    intros * access1 access2.
    etransitivity ; eauto.
  Qed.
  
  Definition le_pl_state : relation PL_state :=
    fun Spl1 Spl2 => env Spl1 = env Spl2 /\ le_mem (mem Spl1) (mem Spl2).
  Global Program Instance IsPreorderState : PreOrder le_pl_state.
  Next Obligation.
    intros x. split ; reflexivity. Qed.
  Next Obligation.
    intros x y z (? & ?) (? & ?) ; split ; etransitivity ; eauto. Qed.

  Infix "<={pl}" := le_pl_state (at level 70).

  Definition le_pl_hlpl (Spl : PL_state) (S : state) : Prop :=
    exists Spl', Compatible S /\ concr_hlpl S Spl' /\ Spl <={pl} Spl'.

  Lemma le_block_poison :
    forall bytes n,
      length bytes = n ->
      le_block bytes (repeat Undef n).
  Proof.
    intros bytes. induction bytes ; intros n Hlen ; simpl in Hlen.
    - subst. constructor.
    - rewrite <- Hlen. simpl. constructor.
      * constructor.
      * apply f_equal with (f := pred) in Hlen. simpl in Hlen.
        eapply IHbytes ; eauto.
  Qed.


  (** Concretization of states/values implies correct types for values. *)
  Lemma val_concr_implies_correct_type_size :
    forall v t bytes,
      concr_hlpl_val v t bytes -> sizeof t = length bytes
  with tuple_val_concr_implies_correct_type_list_size :
    forall vl tl bytes,
      concr_hlpl_val_tuple vl tl bytes -> sizeof (TTuple tl) = length bytes.
  Proof.
    {
      intros v t bytes Hconcr. induction Hconcr ; auto.
      - destruct b ; reflexivity.
      - subst s. rewrite repeat_length. reflexivity.
      - eapply tuple_val_concr_implies_correct_type_list_size ; eauto.
    }
    {
      intros vl tl bytes Hconcr. induction Hconcr. 
      - reflexivity.
      - cbn. rewrite length_app. apply val_concr_implies_correct_type_size in H.
        apply f_equal2 ; assumption.
    }
  Qed.

  (* Lookup mem lemmas*)
  Lemma Forall2_map_r {A B B'} (g : B -> B') (R : A -> B' -> Prop) l1 l2 :
    Forall2 R l1 (map g l2) <-> Forall2 (fun x y => R x (g y)) l1 l2.
  Proof.
    revert l1. induction l2 ; split ; intro H.
    - inversion H. constructor. 
    - inversion H. cbn. constructor.
    - cbn in H. inversion H ; subst. apply IHl2 in H4. constructor ; auto.
    - cbn. inversion H ; subst. apply IHl2 in H4. constructor ; auto.
  Qed.

  Lemma lookup_mem_tuple:
    forall Spl addr tl bytes_list,
      Forall2 (fun bytes t => length bytes = sizeof t) bytes_list tl ->
      Spl.m.[ addr : TTuple tl ] = Some (concat bytes_list) <->
        length bytes_list = length tl /\
          forall i bytes t, List.nth_error bytes_list i = Some bytes ->
                       nth_error tl i = Some t ->
                         Spl.m.[ addr +o partial_sizeof_tuple tl i : t ] = Some bytes.
  Proof.
    intros ? (bi, off) * Hforall. split.
    {
      intros H. generalize dependent bytes_list.
      generalize dependent off. generalize dependent bi.
      induction tl ; intros.
      - inversion Hforall ; subst. cbn. repeat constructor. intros ? ? ? ?.
        rewrite nth_error_nil in H0. discriminate.
      - inversion Hforall ; subst. cbn in H. rewrite Nat2Z.inj_add in H.
        apply Mem.loadbytes_split in H as (bytes1 & bytes2 & Hload1 & Hload2 & Heq) ;
          try lia.
        apply Mem.loadbytes_length in Hload1 as Hlen1, Hload2 as Hlen2.
        rewrite Nat2Z.id in Hlen1, Hlen2.
        apply LB.app_inj_1 in Heq as (Heqx & Heql) ; [ | congruence].
        apply (IHtl bi (off + sizeof a)) in H4 as (Hlen & Hforall') ;
          [ | cbn ; unfold sum ; congruence]. split ; [ cbn ; congruence | ].
        intros. cbn. destruct i eqn:Ei ; subst.
        * rewrite Z.add_0_r. injection H as <-. injection H0 as <-. assumption.
        * cbn in Hforall'. cbn in H0, H. rewrite Nat2Z.inj_add, Z.add_assoc.
          apply Hforall' ; auto.
    }
    {
      intros (Hlen & H). generalize dependent tl.
      generalize dependent off. generalize dependent bi.
      induction bytes_list; cbn in * ; intros.
      - inversion Hforall ; subst. apply Mem.loadbytes_empty ; cbn ; lia.
      - inversion Hforall ; subst.
        cbn. rewrite Nat2Z.inj_add.
        eapply Mem.loadbytes_concat ; try lia.
        * specialize (H 0%nat a y eq_refl eq_refl). rewrite Z.add_0_r in H. assumption.
        * apply IHbytes_list ; auto. intros [] **.
          ** destruct l' ; [rewrite nth_error_nil in H1 ; discriminate | ].
             cbn. rewrite Z.add_0_r. injection H1 as ->.
             auto. specialize (H (S 0) bytes t). cbn in H.
             rewrite Nat.add_0_r in H. apply H ; [ | reflexivity ].
             rewrite <- H0. reflexivity.
          ** specialize (H (S (S n)) bytes t). cbn in *.
             rewrite !Nat2Z.inj_add, !Z.add_assoc in *. apply H ; auto.
    }
  Qed.

  Lemma lookup_mem_tuple':
    forall Spl addr tl bytes,
      Spl.m.[ addr : TTuple tl ] = Some (bytes) ->
      forall i, (0 <= i < length tl)%nat ->
           exists t, nth_error tl i = Some t /\
                Spl.m.[ addr +o pst tl i : t ] =
                  Some (firstn (sizeof t) (skipn (pst tl i) bytes)).
  Proof.
    intros ? (bi, off) tl.
    generalize dependent off. generalize dependent bi. cbn.
    induction tl ; cbn ; intros bi off bytes Hread i boundsi.
    - lia.
    - destruct i.
      * exists a ; split ; [ reflexivity | rewrite Z.add_0_r, skipn_0 ].
        rewrite Nat2Z.inj_add in Hread. apply Mem.loadbytes_split in Hread ; try lia.
        destruct Hread as (bytes1 & bytes2 & Hread1 & _ & Heq). subst.
        apply Mem.loadbytes_length in Hread1 as Hlen1. rewrite Nat2Z.id in Hlen1.
        rewrite <- Hlen1, LB.take_app_length. congruence.
      * rewrite Nat2Z.inj_add in Hread. apply Mem.loadbytes_split in Hread ; try lia.
        destruct Hread as (bytes1 & bytes2 & Hread1 & Hread2 & Heq).
        apply IHtl with (i := i) in Hread2 ; [ | lia].
        apply Mem.loadbytes_length in Hread1 as Hlen1. rewrite Nat2Z.id in Hlen1.
        rewrite Nat2Z.inj_add, Z.add_assoc, Heq, LB.drop_app_add' ; auto.
  Qed.

  Lemma concr_val_tuple_implies_concr_nth_val :
    forall vl v tl t bytes n,
      concr_hlpl_val_tuple vl tl bytes ->
      nth_error vl n = Some v ->
      nth_error tl n = Some t ->
      concr_hlpl_val v t (firstn (sizeof t) (skipn (pst tl n) bytes)) .
  Proof.
    intros * H. generalize dependent v. generalize dependent t. generalize dependent n.
    induction H ; intros.
    - rewrite nth_error_nil in H. discriminate.
    - apply concr_val_size in H as Hlen0. destruct n.
      * injection H1 as <- ; injection H2 as <-.
        rewrite skipn_0, Hlen0, LB.take_app_length' ; auto.
      * specialize (IHconcr_hlpl_val_tuple _ _ _ H1 H2). cbn.
        rewrite Hlen0, LB.drop_app_add. assumption.
  Qed.

  (* Concretization of states implies concretization of values *)
  Lemma state_concr_implies_val_concr : 
    forall S Spl sp v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      exists addr t bytes,
        addr ~^{S, t} sp /\ concr_hlpl_val v t bytes /\ Spl.m.[addr : t] = Some bytes.
  Proof.
    induction sp using ListBackInd.state_path_back_ind ;
      intros v Hconcr Hvspn HSx ;
      pose proof Hconcr as [Hconcr_mem Hconcr_env].
    remember (blockof enc_x).1 as bi. remember (blockof enc_x).2 as t.
    assert (Heqbit : blockof enc_x = (bi, t))
      by (subst ; rewrite <- surjective_pairing ; reflexivity).
    - destruct (Hconcr_mem _ _ _ _ Hvspn HSx Heqbit) as
        ((bytes & Hconcr_val & Hmem) & access).
      assert (Hequiv : (bi, 0) ~^{S, t} (enc_x, []))
        by (eapply Addr_spath_base ; eauto ; eapply Offset_vpath_base). 
      exists (bi, 0), t, bytes. repeat split ; auto. simpl.
      Transparent Mem.loadbytes. unfold Mem.loadbytes. Opaque Mem.loadbytes.
      rewrite Z.add_0_l.
      apply Mem.range_perm_implies with (p2 := Readable) in access ; try constructor.
      rewrite pred_dec_true ; auto. rewrite Nat2Z.id. congruence.
    - rewrite sget_app in HSx. 
      apply valid_spath_app in Hvspn as Htemp ; destruct Htemp as (Hvsp & Hvvp).
      destruct (S.[sp]) eqn:E ;
        try (apply not_valid_spath_app_last_get_node_arity in Hvspn as [] ;
             rewrite E ; simpl ; lia).
      + assert (H : exists (addr : address) (t : type) (bytes : list memval),
                   addr ~^{S, t} sp /\
                     concr_hlpl_val (loc ((l), (y))) t bytes /\
                     Spl.m.[addr : t] = Some bytes) by (apply IHsp ; auto).
        destruct H as (addr & t & bytes & Hequiv & Hconcr_val & Hval_mem).
        destruct n ; simpl in HSx.
        * exists addr, t, bytes. repeat split ; auto.
          ** inversion Hequiv ; subst.
             rewrite <- Addr_spath_loc with (l := l); auto. rewrite E ; auto.
          ** inversion Hconcr_val ; subst ; auto.
        * inversion Hvvp ; subst. simpl in H2. rewrite nth_error_nil in H2.
          congruence.
      + assert (H : exists (addr : address) (t0 : type) (bytes : list memval),
                   addr ~^{S, t0} sp /\
                     concr_hlpl_val (VTuple vl) t0 bytes /\
                     Spl.m.[addr : t0] = Some bytes).
        eapply IHsp ; auto.
        destruct H as (addr & t0 & bytes & Hequiv & Hconcr_val & Hval_mem).
        inversion Hequiv ; subst. inversion Hconcr_val ; subst.
        apply concr_val_tuple_implies_valuelist_typelist_same_size in H1 as ?.
        apply lookup_mem_tuple' with (i := n) in Hval_mem as (t' & Ht' & Hload).
        exists (addr +o partial_sizeof_tuple tl n), t',
          (firstn (sizeof t') (skipn (pst tl n) bytes)) ; repeat split ; auto.
        * eapply Addr_spath_tuple_n ; eauto. rewrite E. cbn. f_equal.
          eapply concr_val_tuple_implies_valuelist_typelist_same_size ; eauto.
        * eapply concr_val_tuple_implies_concr_nth_val ; eauto.
          cbn. apply nth_error_length in Ht'. rewrite <- H0 in Ht'.
          apply nth_error_Some' in Ht' as (v & ?). rewrite H2. reflexivity.
        * rewrite <- H0. inversion Hvvp ; subst. apply nth_error_length in H5.
          cbn in H5. lia.
  Qed.

  Lemma state_concr_implies_val_concr_at_addr : 
    forall S Spl sp addr t v,
      concr_hlpl S Spl ->
      valid_spath S sp ->
      (S.[ sp ]) = v ->
      addr ~^{S, t} sp ->
      exists bytes,
         concr_hlpl_val v t bytes /\ Spl.m.[addr : t] = Some bytes.
  Proof.
    intros S Spl sp addr t v Hconcr Hvsp HS_sp Hequiv.
    destruct (state_concr_implies_val_concr _ _ _ _ Hconcr Hvsp HS_sp)
      as [addr' [t' [bytes [Hequiv' [Hconcr_val Hlu ] ] ] ] ].
    pose proof (addr_spath_equiv_deterministic_addr _ _ _ _ _ _ Hequiv' Hequiv) as Heq.
    pose proof (addr_spath_equiv_deterministic_type _ _ _ _ _ _ Hequiv' Hequiv) as Heqt.
    subst addr' t'; clear Hequiv'.
    exists bytes ; split ; auto.
  Qed.
  
  Lemma concr_val_TInt_implies_PL_int :
    forall v bytes, concr_hlpl_val v TInt bytes ->
            (exists n, bytes = (make_int64 n)) \/ bytes = repeat Undef (sizeof TInt).
  Proof.
    intros v bytes Hconcr. remember TInt as t. induction Hconcr ; try discriminate.
    - left. exists n. reflexivity.
    - right. subst. reflexivity.
    - auto.
  Qed.

  Lemma le_mem_implies_le_block :
    forall m1 m2 bi n ofs bytes1 bytes2,
      le_mem m1 m2 ->
      Mem.getN n ofs ((Mem.mem_contents m1) # bi) = bytes1 ->
      Mem.getN n ofs ((Mem.mem_contents m2) # bi) = bytes2 ->
      le_block bytes1 bytes2.
  Proof.
    induction n ; intros * le_mem getN1 getN2 ;
    pose proof le_mem as temp ; destruct temp as (_ & _ & H).
    - subst ; constructor.
    - simpl in *. destruct bytes1 ; destruct bytes2 ; try discriminate.
      injection getN1 ; injection getN2 ; intros ; subst.
      constructor ; [eauto | apply IHn with (ofs := ofs + 1) ; auto ].
  Qed.


  Lemma le_mem_implies_le_block_at_addr :
    forall S1 S2 addr t bytes1 bytes2,
      le_mem (mem S1) (mem S2) ->
      S1.m.[ addr : t ] = Some bytes1 ->
      S2.m.[ addr : t ] = Some bytes2 ->
      le_block bytes1 bytes2.
  Proof.
    intros * le_mem H1 H2.
    pose proof le_mem as temp ; destruct temp as (Hdom & Hnextblock & Hle_mem).
    Transparent Mem.loadbytes. unfold Mem.loadbytes in *. Opaque Mem.loadbytes.
    destruct (Mem.range_perm_dec (mem S1) _ _ _ _ _) as [Hbytes1 | ? ]; 
      destruct (Mem.range_perm_dec (mem S2) _ _ _ _ _) as [Hbytes2 | ? ] ;
      try congruence ; injection H1 as <- ; injection H2 as <-. rewrite Nat2Z.id.
     remember (sizeof t) as n. clear Heqn.
     induction n eqn:E.
    - constructor.
    - eapply le_mem_implies_le_block ; eauto.
  Qed.

  Transparent Mem.loadbytes. 

  Lemma le_mem_preserves_access_l :
    forall m1 m2 b ofs n v1,
      le_mem m1 m2 ->
      Mem.loadbytes m1 b ofs n = Some v1 ->
      exists v2, Mem.loadbytes m2 b ofs n = Some v2.
  Proof.
    intros * le_mem access.
    pose proof le_mem as temp. destruct temp as (Hperm & _ & _).
    unfold Mem.loadbytes in access.
    destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable) ; try discriminate.
    injection access ; intros <- ; clear access.
    unfold Mem.range_perm, Mem.perm in r.
    rewrite Hperm in r. destruct (Mem.loadbytes m2 b ofs n) eqn:E.
    - exists l ; auto.
    - unfold Mem.loadbytes in E.  
      rewrite pred_dec_true in E ; easy.
  Qed.

  Lemma le_mem_preserves_access_r :
    forall m1 m2 b ofs n v2,
      le_mem m1 m2 ->
      Mem.loadbytes m2 b ofs n = Some v2 ->
      exists v1, Mem.loadbytes m1 b ofs n = Some v1.
  Proof.
    intros * le_mem access.
    pose proof le_mem as temp. destruct temp as (Hperm & _ & _).
    unfold Mem.loadbytes in access.
    destruct (Mem.range_perm_dec m2 b ofs (ofs + n) Cur Readable) ; try discriminate.
    injection access ; intros <- ; clear access.
    unfold Mem.range_perm, Mem.perm in r.
    rewrite <- Hperm in r. destruct (Mem.loadbytes m1 b ofs n) eqn:E.
    - exists l ; auto.
    - unfold Mem.loadbytes in E. rewrite pred_dec_true in E ; easy.
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
      HLPL.eval_proj S proj sp sp' ->
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
      assert (Htemp: exists bytes, concr_hlpl_val (VPtr l) t bytes /\
                      Spl'.m.[addr : t] = Some bytes).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (bytes & Hconcr_val & Hlu_addr). inversion Hconcr_val ; subst.
      assert (Hvsp' : valid_spath S sp') by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp : exists (addr : address) (t : type) (bytes : list memval),
                 addr ~^{S, t} sp' /\
                   concr_hlpl_val (VLoc l v) t bytes /\
                   Spl'.m.[addr : t] = Some bytes).
      { apply state_concr_implies_val_concr ; auto. }
      destruct Htemp as (addr' & t' & bytes & Hequiv' & Hconcr_val' & Hlu_addr').
      exists addr', t' ; split ; auto.
      apply Hcorr_addrof with (l := l) in Hequiv' as Haddr'; auto.
      assert (t' = t0) by congruence ; subst.
      constructor ; [ eapply addr_spath_equiv_offset_range ; eauto | idtac].
      pose proof (Hcorr_addrof _ _ _ _ Hequiv' H0).
      rewrite Haddr in H1 ; injection H1 ; intros ; subst ; clear H1.
      pose proof Hlu_addr as temp.
      eapply le_mem_preserves_access_r in temp as (v1 & Hlu); eauto.
      assert (le_block v1 (make_ptr64 addr')).
      {eapply le_mem_implies_le_block_at_addr ; eauto. }
      apply le_block_not_contains_poison in H1 ; subst ; auto.
      apply make_ptr64_not_contain_Undef.
    - nodes_to_val.
      assert (Hvsp : valid_spath S sp) by
        (apply get_not_bot_valid_spath ; unfold bot ; simpl ; congruence).
      assert (Htemp: exists bytes, concr_hlpl_val (VTuple vl) t bytes /\
                      Spl'.m.[addr : t] = Some bytes).
      { apply state_concr_implies_val_concr_at_addr with (S := S) (sp := sp) ; auto. }
      destruct Htemp as (bytes & Hconcr_val & _). inversion Hconcr_val ; subst.
      apply concr_val_tuple_implies_valuelist_typelist_same_size in H0.
      rewrite H0 in index. apply nth_error_Some' in index as (t & ?).
      exists (addr +o pst tl k), t ; split.
      * constructor. apply eval_proj_tuple_pst ; assumption.
      * eapply Addr_spath_tuple_n ; eauto. rewrite Heqv. cbn. congruence.
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
      HLPL.eval_path S P sp sp' ->
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
      assert (Hequiv' : addr_spath_equiv S addr t (p +++ [0%nat]))
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
    intros. destruct (blockof (encode_var (p.1).1)) as (bi, t0) eqn:E.
    inversion H0 ; subst.
    assert (addr_spath_equiv S (bi, 0) t0 (encode_var p.1.1, [])) by
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
    destruct (blockof (encode_var p.1.1)) as [bi t0] eqn:Hbo.
    assert (Hsimul_path_pl : exists addr t,
               eval_path Spl p.1.2 ((bi, 0), t0) (addr, t) /\ addr ~^{S, t} sp).
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
      pose proof (eval_path_deterministic _ _ _ _ _ Heval_path Heval_path')
        as [=] ; subst ; assumption.
    }
  Qed.

  Lemma concr_val_equiv_concr_copy_val :
    forall v v_copy t bytes, 
      HLPL.copy_val v v_copy ->
      concr_hlpl_val v t bytes <-> concr_hlpl_val v_copy t bytes
  with concr_val_tuple_equiv_concr_copy_val_tuple :
    forall vl vl_copy tl bytes, 
      HLPL.copy_tuple_val vl vl_copy ->
      concr_hlpl_val_tuple vl tl bytes <-> concr_hlpl_val_tuple vl_copy tl bytes.
  Proof.
    {
      intros v v_copy t bytes Hcopy. split ; intros Hconcr_val.
      - induction Hcopy ; auto.
        * inversion Hconcr_val ; subst. auto.
        * inversion Hconcr_val ; subst. constructor.
          rewrite <- concr_val_tuple_equiv_concr_copy_val_tuple ; eauto.
      - induction Hcopy ; auto.
        * constructor. auto.
        * inversion Hconcr_val ; subst. constructor.
          rewrite concr_val_tuple_equiv_concr_copy_val_tuple ; eauto.
    }
    {
      intros vl vl_copy tl bytes Hcopy. split ; intro Hconcr_val.
      - generalize dependent bytes. generalize dependent tl.
        induction Hcopy ; intros.
        * inversion Hconcr_val ; subst ; constructor.
        * inversion Hconcr_val ; subst ; constructor ; auto.
          rewrite <- concr_val_equiv_concr_copy_val ; eauto.
      - generalize dependent bytes. generalize dependent tl.
        induction Hcopy ; intros.
        * inversion Hconcr_val ; subst ; constructor.
        * inversion Hconcr_val ; subst ; constructor ; auto.
          rewrite concr_val_equiv_concr_copy_val ; eauto.
    }
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

  Lemma setN_inv : forall vl v c p q,
      p < q ->
      Mem.setN vl q (ZXMap.set p v c) = ZXMap.set p v (Mem.setN vl q c).
  Proof.
    induction vl ; intros * le.
    - reflexivity.
    - simpl. rewrite ZXMap.set_disjoint, !IHvl ; auto ; lia.
  Qed.

  Lemma setN_inv' : forall vl v c p,
      ZXMap.get p (Mem.setN vl (p + 1) (ZXMap.set p v c)) = v.
  Proof.
    intros *. rewrite Mem.setN_other ; [ rewrite ZXMap.gss ; reflexivity | lia].
  Qed.

  Lemma setN_get_gt :
    forall vl v c p q,
      p + 1 <= q < p + 1 + Datatypes.length vl ->
      ZXMap.get q (Mem.setN vl (p + 1) (ZXMap.set p v c)) =
        ZXMap.get q (Mem.setN vl (p + 1) c).
  Proof.
    induction vl ; intros * len.
    - simpl in len. lia.
    - simpl in *. rewrite ZXMap.set_disjoint, setN_inv ; try lia.
      rewrite ZXMap.gso ; auto ; lia.
  Qed.

  Lemma setN_getN_same :
    forall n ofs c,
      Mem.setN (Mem.getN n ofs c) ofs c = c.
  Proof.
    induction n ; intros.
    - reflexivity.
    - simpl. rewrite setN_inv, IHn ; [ | lia ]. apply ZXMap.extensionality ; intros i.
      destruct (zeq i ofs).
      * subst. rewrite ZXMap.gss ; reflexivity.
      * rewrite ZXMap.gso ; auto.
  Qed.

        
  Lemma setN_inside :
    forall vl c p q,
      p <= q /\ q < p + Datatypes.length vl ->
      ZXMap.get q (Mem.setN vl p c) = List.nth (Z.to_nat (q - p)) vl Undef.
  Proof. 
    induction vl ; intros * (lb & hb).
    - simpl in hb. lia.
    - simpl. destruct (Z.to_nat (q - p)) eqn:E.
      * assert (p = q) by lia ; subst. rewrite Mem.setN_other ; [ | lia].
        rewrite ZXMap.gss ; reflexivity.
      * simpl in hb. assert (p + 1 <= q < p + 1 + Datatypes.length vl) by lia.
        specialize (IHvl c (p + 1) q H).
        replace (Z.to_nat (q - (p + 1))) with n in IHvl by lia.
        rewrite <- IHvl. rewrite setN_get_gt ; auto.
  Qed.

  Lemma write_read_at_addr :
    forall S addr t bytes,
      S.m.[ addr : t] = Some bytes ->
      S.m.[ addr <-  bytes : t] = S.
  Proof.
    intros * get. unfold update_mem, storebytes.
    destruct ((sizeof t =? Datatypes.length bytes)%nat) eqn:len.
    - destruct (Mem.storebytes (mem S) addr.1 addr.2 bytes) eqn:E.
      + Transparent Mem.loadbytes. unfold Mem.loadbytes in get. Opaque Mem.loadbytes.
        Transparent Mem.storebytes. unfold Mem.storebytes in E. Opaque Mem.storebytes.
        destruct (Mem.range_perm_dec (mem S) _ _ _ _ _) ; try discriminate.
        destruct (Mem.range_perm_dec (mem S) _ _ _ _ _) ; try discriminate.
        apply Nat.eqb_eq in len.
        injection E as <-. injection get as Hv. destruct S ; f_equal. simpl.
        destruct mem eqn:Hmem. simpl. apply Mem.mkmem_ext ; auto.
        apply PXMap.extensionality.
        intros i. destruct (peq addr.1 i).
        * subst. rewrite PXMap.gss, Nat2Z.id. apply ZXMap.extensionality.
          intros i. simpl. rewrite setN_getN_same. reflexivity.
        * rewrite PXMap.gso ; congruence.
      + destruct S ; reflexivity.
    - destruct S ; reflexivity.
  Qed.

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
    forall Spl1 Spl2 addr t bytes bytes',
      le_pl_state Spl1 Spl2 ->
      le_block bytes bytes' ->
      le_pl_state (Spl1.m.[ addr <- bytes : t ]) (Spl2.m.[ addr <- bytes' : t ]).
  Proof.
    intros Spl1 Spl2 addr t bytes bytes' [Hle_env le_mem] Hle_block.
    pose proof le_mem as (perm & next & lookup).
    constructor.
    - rewrite !env_stable_by_write_at_addr ; assumption.
    - repeat split.
      + simpl. unfold storebytes.
        destruct (sizeof t =? Datatypes.length bytes)%nat eqn:E ;
        destruct (sizeof t =? Datatypes.length bytes')%nat eqn:E' ;
        destruct (Mem.storebytes (mem Spl1) addr.1 addr.2 bytes) eqn:E'' ;
        destruct (Mem.storebytes (mem Spl2) addr.1 addr.2 bytes') eqn:E''' ; auto ;
        try (apply Mem.storebytes_access in E'') ;
        try (apply Mem.storebytes_access in E''') ;
          congruence.
      + simpl. unfold storebytes.
        destruct (sizeof t =? Datatypes.length bytes)%nat eqn:E ;
        destruct (sizeof t =? Datatypes.length bytes')%nat eqn:E' ;
        destruct (Mem.storebytes (mem Spl1) addr.1 addr.2 bytes) eqn:E'' ;
        destruct (Mem.storebytes (mem Spl2) addr.1 addr.2 bytes') eqn:E''' ; auto ;
        try (apply Mem.nextblock_storebytes in E'') ;
        try (apply Mem.nextblock_storebytes in E''') ;
          congruence.
      + simpl. intros * access1 access2.
        destruct (storebytes_elim (mem Spl1) addr.1 addr.2 bytes t)
          as [(len1 & m1' & mem_acc1 & acc1) | (? & acc1) ] ;
        destruct (storebytes_elim (mem Spl2) addr.1 addr.2 bytes' t)
          as [(len2 & m2' & mem_acc2 & acc2) | (? & acc2) ].
        * apply Mem.storebytes_mem_contents in mem_acc1, mem_acc2.
          rewrite acc1, mem_acc1 in access1. rewrite acc2, mem_acc2 in access2.
          destruct (peq bi addr.1).
          ** subst bi.
             rewrite (PXMap.gss _ _) in access1. rewrite (PXMap.gss _ _) in access2.
             destruct (Z.lt_ge_cases ofs addr.2).
             *** rewrite Mem.setN_outside in access1 ; [ idtac | left ; auto].
                 rewrite Mem.setN_outside in access2 ; [ idtac | left ; auto].
                 eauto.
             *** destruct (Z.lt_ge_cases ofs (addr.2 + Datatypes.length bytes)).
                 **** rewrite setN_inside in access1 ; [ | auto].
                      rewrite setN_inside in access2 ; [ | lia].
                      rewrite <- access1, <- access2.
                      apply le_block_nth ; auto ; constructor.
                 **** rewrite Mem.setN_outside in access1 ; [ idtac | right ; lia ].
                      rewrite Mem.setN_outside in access2 ; [ idtac | right ; lia ].
                      eauto.
          ** rewrite (PXMap.gso _ _ n) in access1. rewrite (PXMap.gso _ _ n) in access2.
             eapply lookup ; eauto.
        * apply Forall2_length in Hle_block. destruct H ; try congruence.
          apply (le_mem_storebytes_None_equiv _ _ _ _ bytes _ le_mem) in H ; auto.
          congruence.
        * apply Forall2_length in Hle_block. destruct H ; try congruence.
          apply (le_mem_storebytes_None_equiv _ _ _ _ _ bytes' le_mem) in H ; auto.
          congruence.
        * rewrite acc1 in access1. rewrite acc2 in access2. eauto.
  Qed.

  Lemma le_pl_r :
    forall Spl1 Spl2 addr t bytes,
      Spl2.m.[ addr : t ] = Some bytes ->
      le_pl_state Spl1 Spl2 ->
      exists bytes',
        Spl1.m.[ addr : t ] = Some bytes' /\ le_block bytes' bytes.
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
    forall Spl1 Spl2 addr t bytes,
      Spl1.m.[ addr : t ] = Some bytes ->
      le_pl_state Spl1 Spl2 ->
      exists bytes',
        Spl2.m.[ addr : t ] = Some bytes' /\ le_block bytes bytes'.
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
    forall Spl1 Spl2 addr t bytes bytes',
      Spl1.m.[ addr : t ] = Some bytes ->
      le_pl_state Spl1 Spl2 ->
      le_block bytes bytes' ->
      le_pl_state Spl1 (Spl2.m.[ addr <- bytes' : t ]).
  Proof.
    intros * read le le_block.
    pose proof le as (env_eq & access_eq & nextblock_eq & le_val).
    constructor ; [ rewrite env_stable_by_write_at_addr ; auto | ].
    eapply le_pl_write_at_addr with (addr := addr) (t := t) in le
        as (le_env & le_m) ; eauto.
    rewrite <- write_read_at_addr
      with (S := Spl1) (addr := addr) (t := t) (bytes := bytes) ; auto.
  Qed.

  Lemma le_pl_write_at_addr_l :
    forall Spl1 Spl2 addr t bytes bytes',
      Spl2.m.[ addr : t ] = Some bytes' ->
      le_pl_state Spl1 Spl2 ->
      le_block bytes bytes' ->
      le_pl_state (Spl1.m.[ addr <- bytes : t ]) Spl2.
  Proof.
    intros * read le le_block.
    pose proof le as (env_eq & access_eq & nextblock_eq & le_val).
    constructor ; [ rewrite env_stable_by_write_at_addr ; auto | ].
    eapply le_pl_write_at_addr with (addr := addr) (t := t) in le
        as (le_env & le_m) ; eauto.
    rewrite <- write_read_at_addr
      with (S := Spl2) (addr := addr) (t := t) (bytes := bytes') ; auto.
  Qed.

  Lemma concr_val_off_vpath_equiv_equiv :
    forall vi ti bytesi,
      length bytesi = sizeof ti ->
      (concr_hlpl_val vi ti bytesi <->
         forall off vp t,
           off_vpath_equiv vi ti off t vp ->
           concr_hlpl_val (vi.[[ vp ]]) t (firstn (sizeof t)
                                             (skipn (Z.to_nat off) bytesi))).
  Proof.
    pose proof offset_is_positive as off_pos.
    intros. split ; intros.
    {
      generalize dependent bytesi. induction H1 ; intros ; nodes_to_val.
      - simpl. rewrite Nat2Z.id, skipn_0, <- H, firstn_all ; auto.
      - rewrite vget_app, Heqv. simpl.
        specialize (IHoff_vpath_equiv _ H H0). inversion IHoff_vpath_equiv ; subst.
        assumption.
      - specialize (IHoff_vpath_equiv _ H H0).
        rewrite vget_app, Heqv, Z.add_comm, Z2Nat.inj_add, <- skipn_skipn, Nat2Z.id ;
          [ | lia | eauto].
        inversion IHoff_vpath_equiv ; subst.
        apply nth_error_length in Htype as Hsize. rewrite <- H2 in Hsize.
        pose proof Hsize as Htemp. apply nth_error_Some' in Htemp as (v & ?).
        eapply concr_val_tuple_implies_concr_nth_val in H5 ; eauto.
        rewrite nth_vget_n in H3 ; [ | lia].
        rewrite skipn_firstn_comm, firstn_firstn, min_l in H5 ; [ congruence | ].
        pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl (S n)).
        rewrite partial_sizeof_tuple_last with (t := t') in H4 ; auto.
        rewrite Nat2Z.inj_le, Nat2Z.inj_sub ; cbn in * ; lia.
    }
    {
      assert (off_vpath_equiv vi ti 0 ti []) by constructor.
      specialize (H0 0 [] ti H1). simpl in H0.
      rewrite skipn_0, <- H, firstn_all in H0. assumption.
    }
  Qed.

  Lemma concr_val_implies_exists_concr_val_vp :
    forall vi ti t off vp bytesi,
      off_vpath_equiv vi ti off t vp ->
      concr_hlpl_val vi ti bytesi ->
      exists bytes, concr_hlpl_val (vi.[[ vp ]]) t bytes.
  Proof.
    intros. apply concr_val_size in H0 as Hlen. symmetry in Hlen.
    pose proof (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hlen) H0 _ _ _ H).
    eexists ; eauto.
  Qed.

  Lemma concr_val_write :
    forall vp vi v ti t bytesi bytes off,
      off_vpath_equiv vi ti off t vp ->
      concr_hlpl_val vi ti bytesi ->
      concr_hlpl_val v t bytes ->
      concr_hlpl_val
        (vi.[[ vp <- v ]]) ti
        (firstn (Z.to_nat off) bytesi ++ bytes ++
           skipn ((Z.to_nat off) + sizeof t) bytesi).
  Proof.
    intros. apply concr_val_size in H0 as Hleni. symmetry in Hleni.
    generalize dependent v. generalize dependent bytes.
    induction H ; intros bytes v Hconcr.
    - simpl. rewrite <- Hleni, skipn_all, app_nil_r. assumption.
    - nodes_to_val. simpl in *. rewrite vset_app_split, Heqv0. simpl.
      assert (concr_hlpl_val (loc (l, v)) t' bytes) by (apply Concr_loc ; auto).
      specialize (IHoff_vpath_equiv _ _ H2). assumption.
    - nodes_to_val.
      pose proof (proj1 (concr_val_off_vpath_equiv_equiv _ _ _ Hleni) H0 _ _ _ H).
      rewrite vset_app_split.
      remember (firstn (sizeof (TTuple tl)) (skipn (Z.to_nat off) bytesi))
        as bytes_tup.
      pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl n) as Hpst_n.
      pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl (S n)) as Hpst_Sn.
      apply offset_is_positive in H as Hoff.
      assert (concr_hlpl_val (vi .[[ vp]] .[[ [n] <- v]]) (TTuple tl)
                (firstn (pst tl n) bytes_tup ++ bytes ++
                   skipn (pst tl (S n)) bytes_tup)).
      {
        inversion H2 ; subst ; try congruence. assert (vl = vl0) by congruence ; subst.
        rewrite tuple_vset_n. constructor.
        apply off_vpath_equiv_sizeof in H as Hlen. cbn in Hlen.
        apply concr_val_size in Hconcr as Hsize.
        apply concr_val_tuple_implies_concr_val'' ; repeat split.
        - rewrite alter_list_length. assumption.
        - cbn. rewrite !length_app, !length_firstn, !length_skipn,
            length_firstn, length_skipn, Hleni.
          rewrite !(Nat.min_l (sizeof (TTuple tl))), Nat.min_l by (cbn in * ; lia).
          rewrite partial_sizeof_tuple_last with (t := t') ; auto.
          rewrite <- (concr_val_size _ _ _ Hconcr).
          rewrite partial_sizeof_tuple_last with (t := t') in Hpst_Sn by auto.
          cbn in * ; lia.
        - intros.
          pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl (S n0)) as Hn0.
          rewrite (partial_sizeof_tuple_last tl n0 t) in * by assumption.
          destruct (decide (n = n0)).
          * subst n0. pose proof H6 as Ht.
            apply nth_error_length in H6. rewrite <- H1 in H6.
            apply nth_error_Some' in H6 as (v' & ?).
            rewrite nth_error_alter_list_eq, H6 in H4. injection H4 as <-. cbn in *.
            rewrite LB.drop_app_le by (rewrite !length_firstn, length_skipn; lia).
            rewrite !LB.take_drop_commute, !LB.drop_drop, !LB.take_take,
              Nat.min_l by lia.
            rewrite LB.drop_ge by (rewrite length_firstn ; lia). cbn.
            rewrite (partial_sizeof_tuple_last _ _ _ Ht).
            rewrite LB.take_app_length' ; congruence.
          * rewrite nth_error_alter_list_neq in H4 by assumption.
            destruct (le_gt_dec n n0).
            ** assert (Hpst: (S n <= n0)%nat) by lia.
               apply n_leq_m_implies_leq_length_pst with (tl := tl) in Hpst.
               rewrite (partial_sizeof_tuple_last tl n t') in * by assumption.
               cbn in *.
               rewrite !skipn_app, !skipn_firstn_comm, !length_firstn, !length_skipn.
               replace (pst tl n - pst tl n0)%nat with 0%nat by lia.
               rewrite firstn_0, app_nil_l, !Nat.min_l, LB.drop_ge ; try lia.
               pose proof (partial_sizeof_tuple_leq_sizeof_tuple tl n0). cbn.
               replace (sizeof (TTuple tl) - (pst tl n + sizeof t') -
                          (pst tl n0 - pst tl n - List.length bytes))%nat with
                 (sizeof (TTuple tl) - pst tl n0)%nat by lia.
               rewrite !firstn_skipn_comm, !skipn_skipn, !firstn_firstn.
               replace (pst tl n0 - pst tl n - Datatypes.length bytes +
                          (pst tl n + sizeof t') + Z.to_nat off)%nat
                 with (pst tl n0 + Z.to_nat off)%nat by lia.
               rewrite Nat.min_l, skipn_firstn_comm by lia.
               replace ((Z.to_nat off +
                           (pst tl n + sizeof t' +
                              (pst tl n0 - pst tl n - Datatypes.length bytes +
                                 sizeof t)) - (pst tl n0 + Z.to_nat off)))%nat
                 with (sizeof t)%nat by lia.
               replace (firstn (sizeof t) (skipn (pst tl n0 + Z.to_nat off) bytesi))
                 with (firstn (sizeof t)
                         (skipn (pst tl n0)
                            (firstn (sizeof (TTuple tl))
                               (skipn (Z.to_nat off) bytesi)))).
               eapply concr_val_tuple_implies_concr_nth_val ; eauto.
               rewrite !skipn_firstn_comm, firstn_firstn, skipn_skipn.
               repeat f_equal. cbn. lia.
            ** cbn in H5. 
               replace (firstn (sizeof t)
                          (skipn (pst tl n0)
                             (firstn (pst tl n) (firstn (sizeof (TTuple tl))
                                                   (skipn (Z.to_nat off) bytesi)) ++
                                bytes ++
                                skipn (pst tl (S n))
                                (firstn (sizeof (TTuple tl))
                                   (skipn (Z.to_nat off) bytesi)))))
                 with (firstn (sizeof t)
                         (skipn (pst tl n0)
                            (firstn (sizeof (TTuple tl))
                               (skipn (Z.to_nat off) bytesi)))).
               eapply concr_val_tuple_implies_concr_nth_val ; eauto.
               assert (S n0 <= n)%nat by lia.
               apply n_leq_m_implies_leq_length_pst with (tl := tl) in H7 as Hpst.
               rewrite partial_sizeof_tuple_last with (t := t) in Hpst by assumption.
               cbn in *. rewrite !LB.drop_app_le
                 by (cbn in * ; rewrite !length_firstn, length_skipn ; lia).
               rewrite firstn_firstn, Nat.min_l by lia.
               rewrite LB.take_app_le by
                 (rewrite length_skipn, length_firstn, length_skipn ; lia).
               rewrite !skipn_firstn_comm, !firstn_firstn, !skipn_skipn, !Nat.min_l
               by lia. reflexivity.
      }
      eapply IHoff_vpath_equiv in H3. subst. simpl sizeof in H3.
      rewrite firstn_firstn, Nat.min_l, !app_assoc, LB.take_take_drop,
        <- !app_assoc, (Nat.add_comm _ (sizeof (TTuple tl))), <- skipn_skipn,
        LB.drop_take_drop, skipn_skipn,
        (partial_sizeof_tuple_last _ _ _ Htype) in H3 by (cbn in * ; lia). 
      replace (Z.to_nat (off + pst tl n))%nat with (Z.to_nat off + pst tl n)%nat by lia.
      replace (Z.to_nat off + pst tl n + sizeof t')%nat with
        (pst tl n + sizeof t' + Z.to_nat off)%nat by lia.
      assumption.
  Qed.

  Lemma concr_state_write_at_addr :
    forall S Spl sp addr v t bytes,
      concr_hlpl S Spl ->
      concr_hlpl_val v t bytes ->
      addr ~^{S, t} sp ->
      concr_hlpl (S.[sp <- v] ) (Spl.m.[addr <- bytes : t]).
  Proof.
    intros * [Hconcr_mem Hconcr_env] Hconcr_val Hequiv. split.
    - intros enc_x bi t' v' Hvsp HSx Hbo'.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      destruct (addr_spath_equiv_var_bi _ _ _ _ Hequiv) as (t0 & Hbo). cbn in Hbo.
      pose proof (Hconcr_mem _ _ _ _ Hvsp (eq_refl _) Hbo')
        as ((bytes' & concr_val' & get) & perms).
      destruct (peq addr.1 bi).
      + subst bi. simpl.
        split ; [ | apply mem_perm_range_stable_by_write_at_addr ; assumption ].
        exists (firstn (Z.to_nat addr.2) bytes' ++ bytes ++
                     skipn (Z.to_nat addr.2 + sizeof t) bytes'). 
        inversion Hequiv ; subst. split.
        * pose proof (proj2 (blockof_inj _ _ _ _ _ _ Hbo Hbo') eq_refl) ;
            assert (t' = tinit) by congruence ; subst.
          rewrite (spath_var_app_vpath sp), sset_sget_prefix ;
            [ apply concr_val_write ; auto | assumption ].
        * unfold storebytes.
          apply off_vpath_equiv_sizeof in Hvequiv as leq1.
          apply offset_is_positive in Hvequiv as leq2.
          destruct ((sizeof t =? Datatypes.length bytes)%nat) eqn:len ;
            [ destruct (Mem.storebytes (mem Spl) addr.1 addr.2 bytes) eqn:E | ].
          ** apply Nat.eqb_eq in len.
             rewrite getN_firstn, getN_skipn, Z.add_0_l.
             pose proof (proj2 (blockof_inj _ _ _ _ _ _ Hbo Hbo') eq_refl) ;
               assert (t' = tinit) by congruence ; subst tinit.
             apply offset_is_positive in Hvequiv as pos.
             unfold offset in *.
             replace (Mem.getN (sizeof t')) with
               (Mem.getN (Z.to_nat addr.2 + sizeof t +
                            (sizeof t' - (Z.to_nat addr.2 + sizeof t)))) by
               (f_equal ; lia).
             apply Mem.storebytes_mem_contents in E.
             rewrite !Mem.getN_concat, <- app_assoc, Z.add_0_l, !Z2Nat.id, Nat.min_l
               by lia.
             f_equal ; [ | f_equal ] ; auto.
             *** rewrite E, PXMap.gss, Mem.getN_setN_outside ; [reflexivity | lia ].
             *** rewrite E, PXMap.gss, len, Mem.getN_setN_same. reflexivity.
             *** rewrite E, PXMap.gss, Mem.getN_setN_outside ;
                   [reflexivity | right ; lia].
          ** destruct (mem_storebytes_elim (mem Spl) addr.1 addr.2 bytes) as
             [ ((m' & ?) & _) | (_ & nperms) ] ; [ congruence| ].
             apply Mem.range_perm_implies with (p2 := Writable) in perms ;
               [ | constructor ].
             pose proof (proj2 (blockof_inj _ _ _ _ _ _ Hbo Hbo') eq_refl) ;
               assert (t' = tinit) by congruence ; subst tinit.
             apply Nat.eqb_eq in len. rewrite <- len in *.
             assert (Mem.range_perm (mem Spl) addr.1 addr.2
                       (addr.2 + Datatypes.length bytes) Cur Writable) by
               (intros ? ? ; apply perms ; destruct addr ; simpl in * ; lia).
             congruence.
          ** rewrite (concr_val_size _ _ _ Hconcr_val), Nat.eqb_refl in len.
             discriminate.
      + split.
        * exists bytes'. split.
          ** rewrite <- HSx, sset_sget_disj ; [ assumption | ].
             left. simpl. intros ? ; congruence.
          ** rewrite heap_sset_sget_disj ; auto.
        * apply mem_perm_range_stable_by_write_at_addr ; assumption.
    - intros enc_x bi' t0 Hvsp Hbo. rewrite env_stable_by_write_at_addr.
      apply sset_not_prefix_valid in Hvsp ; try apply not_strict_prefix_nil.
      specialize (Hconcr_env enc_x bi' t0 Hvsp Hbo). assumption.
  Qed. 

End Concretization.
Notation "addr ~^{ bo , S , t } sp" := (addr_spath_equiv bo S addr t sp) (at level 40).
  
Lemma concr_val_not_val_contains :
  forall ao v t bytes l addr_t,
    concr_hlpl_val ao v t bytes ->
    not_value_contains (fun n => get_loc_id n = Some l) v ->
    concr_hlpl_val (fun l0 => if (l =? l0)%positive then
                             Some addr_t
                           else ao l0) v t bytes
with concr_val_not_val_list_contains :
  forall ao vl tl bytes l addr_t,
    concr_hlpl_val_tuple ao vl tl bytes ->
    Forall (not_value_contains (fun n => get_loc_id n = Some l)) vl ->
    concr_hlpl_val_tuple (fun l0 => if (l =? l0)%positive then
                             Some addr_t
                           else ao l0) vl tl bytes.
Proof.
  {
    intros. induction H ; try (constructor ; auto).
    - apply not_value_contains_struct_loc in H0 as (? & ?). auto.
    - specialize (H0 [] (valid_nil _)). simpl in H0.
      assert (l <> l0) by (intros ->; easy).
      rewrite (proj2 (Pos.eqb_neq _ _) H). assumption.
    - apply not_value_list_contains_forall in H0 as (? & ?). auto.
  }
  {
    intros. induction H.
    - constructor.
    - inversion H0 ; subst. constructor ; auto.
  }
Qed.

Fixpoint op_get_type (op : operand) :=
  match op with
  | Const (IntConst _) => TInt
  | Const (BoolConst _) => TBool
  | Move p => p.2
  | Copy p => p.2
  | Tuple opl =>
      TTuple
        ((fix go opl :=
            match opl with
            | [] => [] 
            | op :: opl' =>
                (op_get_type op) :: (go opl')
            end) opl)
  end.

Definition rv_get_type rv :=
  match rv with
  | Use op => op_get_type op
  | BinaryOp BAdd _ _ => TInt
  | BinaryOp BLe _ _ => TBool
  | BorrowMut p => p.2
  end.

Fixpoint check_type_of_val v t :=
  match v, t with
  | VBottom, _ => true
  | VInt _, TInt => true
  | VBool _, TBool => true
  | VLoc _ v, t => check_type_of_val v t
  | VPtr _, TRef _ => true
  | VTuple vl, TTuple tl =>
      (fix go vl tl :=
         match vl, tl with
         | [], [] => true
         | v :: vl', t :: tl' =>
             check_type_of_val v t && go vl' tl'
         | _, _ => false
         end
      ) vl tl
  | _, _ => false
  end.

Fixpoint WellTypedOperand S bo op  :=
  match op with
  | Const _ => True
  | Move p =>
      forall sp,
        S |-{p} p => sp ->
           eval_type bo S sp p.2
  | Copy p =>
      forall sp,
        S |-{p} p => sp ->
           eval_type bo S sp p.2
  | Tuple opl => 
      (fix go (opl : list operand) : Prop :=
         match opl with
         | [] => True
         | op :: opl' => WellTypedOperand S bo op /\ go opl'
         end
      ) opl
  end.

Definition WellTypedRValue S bo rv :=
  match rv with
  | Use op =>
      WellTypedOperand S bo op
  | BinaryOp BAdd op_l op_r =>
      WellTypedOperand S bo op_l /\ WellTypedOperand S bo op_r /\
        TInt = op_get_type op_l /\ TInt = op_get_type op_r
  | BinaryOp BLe op_l op_r =>
      WellTypedOperand S bo op_l /\ WellTypedOperand S bo op_r /\
        TBool = op_get_type op_l /\ TBool = op_get_type op_r
  | BorrowMut p =>
      exists t', p.2 = TRef t' /\ forall sp, S |-{p} p => sp -> eval_type bo S sp t'
  end.

Fixpoint WellTypedStmt S bo stmt :=
  match stmt with
  | Assign p rv =>
      forall t sp,
        S |-{p} p => sp -> t = rv_get_type rv ->
           WellTypedRValue S bo rv /\ eval_type bo S sp t
  | Seq s1 s2 =>
      WellTypedStmt S bo s1 /\ WellTypedStmt S bo s2
  | _ => True
  end.

Lemma get_node_write_bot :
  forall S sp sp',
    get_node (S.[sp' <- bot].[sp]) <> NBottom ->
    get_node (S.[sp]) = get_node (S.[sp' <- bot].[sp]).
Proof.
  intros. replace NBottom with (get_node bot) in * by reflexivity.
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
    get_node (S.[sp <- loc (l, S.[sp])].[sp]) = (NLoc l).
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
    get_node (S.[ r ]) = NLoc (l) ->
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
    get_node (S.[ r ]) = NLoc l ->
    get_node (S.[r <- S.[r +++ [0%nat] ] ].[ remove_loc_spath r p ]) = get_node (S.[ p ]).
Proof.
  intros * neq vsp node. unfold remove_loc_spath.
  destruct (decidable_prefix' r p) as [ (suff & ?) | ] ; subst.
  - nodes_to_val.
    assert (valid_spath S r)
      by (apply get_not_bot_valid_spath; rewrite Heqv; discriminate).
    rewrite !sget_app, Heqv, sset_sget_equal ; auto. simpl.
    destruct suff.
    + rewrite app_spath_vpath_nil_r in neq. contradiction.
    + apply valid_spath_app in vsp as (_ & vsp). rewrite Heqv in vsp.
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
  - apply HLPL.Eval_cons with (q := q).
    + inversion Heval_proj ; subst ;
        try (econstructor ; auto ; erewrite get_node_write_bot ; eauto ; congruence).
      assert (Hnbot : get_node (S .[ sp' <- bot] .[ p0]) <> nbot) by congruence.
      eapply get_node_write_bot in Hnbot.
      econstructor ; eauto. congruence.
    + eapply IHeval_path, valid_spath_write_bot, eval_proj_valid ; eauto.
  - apply HLPL.Eval_path_loc with (q := q).
    + inversion Heval_loc ; subst ;
      econstructor ; auto ; erewrite get_node_write_bot ; eauto ; congruence.
    + eapply IHeval_path, valid_spath_write_bot, eval_loc_valid ; eauto.
Qed.

Lemma eval_proj_write_loc :
  forall S l proj p q r,
    p <> r ->
    HLPL.eval_proj (S.[ r <- loc (l, S .[ r])]) proj
      (add_loc_spath r p) (add_loc_spath r q) ->
    HLPL.eval_proj S proj p q.
Proof.
  intros * p_not_r eval_proj. inversion eval_proj ; subst.
  - rewrite get_node_write_loc in * ; econstructor ; eauto.
  - rewrite get_node_write_loc in *. unfold add_loc_spath in H2.
    destruct (decidable_prefix' r p).
    * destruct s as ([ | n' r'] & ?).
      ** rewrite app_spath_vpath_nil_r in e. congruence.
      ** inversion eval_proj ; subst.
         destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
         *** rewrite <- !app_spath_vpath_assoc, <- !app_assoc in H2.
             apply app_spath_vpath_inv_head, app_inv_head in H2.
             rewrite <- eq0, <- H2, app_spath_vpath_assoc. econstructor ; eauto.
         *** rewrite <- app_spath_vpath_assoc in H2.
             assert (prefix r q) by (eexists ; eauto). congruence.
    * inversion eval_proj ; subst.
      rewrite not_prefix_add_loc_spath in eval_proj ; auto.
      inversion eval_proj ; subst.
      unfold add_loc_spath in H4. destruct (decidable_prefix' r q) as [(r0 & eq0) | ?].
      ** assert (strict_prefix r (p +++ [k%nat]))
         by (rewrite H4 ; exists 0%nat, r0 ;  reflexivity).
         apply strict_prefix_app_last in H0. contradiction.
      ** rewrite <- H4. econstructor ; eauto.
Qed.

Lemma remove_loc_spath_app :
  forall p r n,
    p <> r -> remove_loc_spath r (p +++ [n]) = remove_loc_spath r p +++ [n].
Proof.
  intros * neq. unfold remove_loc_spath.
  destruct (decidable_prefix' r p) as [(s & ?) | ].
  - destruct (decidable_prefix' r (p +++ [n])) as [(s' & ?) | ].
    + rewrite <- e, <- app_spath_vpath_assoc in e0. apply app_spath_vpath_inv_head in e0.
      rewrite e0. destruct s. 
      * rewrite app_spath_vpath_nil_r in e. congruence.
      * rewrite <- app_spath_vpath_assoc ; auto.
    + rewrite <- e in n0. assert (prefix r ((r +++ s) +++ [n]))
        by (rewrite <- app_spath_vpath_assoc; eexists ; eauto). congruence.
  - destruct (decidable_prefix' r (p +++ [n])) as [(s' & ?) | ] ; auto.
    destruct s' ; cbn in *.
    + rewrite app_spath_vpath_nil_r in *. assumption.
    + apply f_equal with (f := removelast) in e. rewrite !removelast_app in e ; auto.
      rewrite app_spath_vpath_nil_r in e.
      assert (prefix r p) by (eexists ; eauto). contradiction.
Qed.

Lemma add_loc_spath_app :
  forall r p n,
    p +++ [ n ] <> r -> add_loc_spath r (p +++ [ n ]) = add_loc_spath r p +++ [ n ].
Proof.
  intros * neq. unfold add_loc_spath.
  destruct (decidable_prefix' r p) as [(s & ?) | ?].
  - destruct (decidable_prefix' r (p +++ [ n ])) as [(s' & ?) | ?] ; subst.
    + rewrite <- app_spath_vpath_assoc in e0.
      apply app_spath_vpath_inv_head in e0 ; subst.
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
  intros.  unfold add_loc_spath.
  destruct (decidable_prefix' (r +++ p) r) as [(r' & eq) | npref ]; auto.
  rewrite <- app_spath_vpath_assoc, <- app_spath_vpath_nil_r in eq.
  apply app_spath_vpath_inv_head, LB.app_nil in eq as ( ? & ?).
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
    HLPL.eval_proj (S.[ r <- loc (l, S .[ r])]) proj p q ->
    HLPL.eval_proj S proj (remove_loc_spath r p) (remove_loc_spath r q).
Proof.
  intros * neq fresh eval_proj.
  inversion eval_proj ; subst.
  - assert (valid_spath (S .[ r <- VLoc l (S .[ r])]) p).
    { apply valid_get_node_sget_not_bot. rewrite get_q. easy. }
    assert (valid_spath (S .[ r <- VLoc l (S .[ r])]) q).
    { apply valid_get_node_sget_not_bot. rewrite get_q'. easy. }
    rewrite get_node_write_loc' in get_q ; auto.
    assert (loc : l0 <> l)
      by (eapply is_fresh_loc_id_neq ; eauto ; rewrite get_q ; auto).
    destruct (decidable_spath_eq q r).
    * subst. apply sset_not_prefix_valid in H0 ; try (apply strict_prefix_irrefl).
      rewrite sset_sget_equal in get_q' ; auto. injection get_q' as ->. easy.
    * rewrite get_node_write_loc' in get_q' ; auto.
      econstructor ; eauto.
  - assert (valid_spath (S .[ r <- VLoc l (S .[ r])]) p).
    { apply valid_get_node_sget_not_bot. rewrite get_q. easy. }
    rewrite get_node_write_loc' in get_q ; auto.
    rewrite remove_loc_spath_app ; auto. econstructor ; eauto.
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
    HLPL.eval_path (S.[ r <- loc (l, (S .[ r]))]) P p q ->
    HLPL.eval_path S P (remove_loc_spath r p) (remove_loc_spath r q).
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
    + econstructor ; [ eapply eval_proj_write_loc' | ] ; eauto.
  - inversion Heval_loc ; subst.
    destruct (decidable_spath_eq p r).
    + subst. rewrite app_decidable_prefix, app_spath_vpath_nil_r in IHeval_path.
      replace (remove_loc_spath r r) with (remove_loc_spath r (r +++ []))
        by (rewrite app_spath_vpath_nil_r ; auto).
      rewrite app_decidable_prefix, app_spath_vpath_nil_r ; auto.
    + eapply HLPL.Eval_path_loc
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
  replace (HLPL.encode_var p.1.1, []) with (remove_loc_spath r (encode_var p.1.1, [])).
  apply eval_path_write_loc' with (l := l) ; auto.
  unfold remove_loc_spath.
  destruct (decidable_prefix' r (encode_var p.1.1, [])) as [(r' & ?) | ] ; auto.
  apply f_equal with (f := snd) in e as e'. apply LB.app_nil in e' as [? ->].
  easy.
Qed.

Lemma eval_path_end_loc :
  forall S l P p q r,
    get_node (S.[r]) = NLoc l ->
    not_state_contains (eq (NPtr l)) S ->
    HLPL.eval_path (S.[r <- S.[r +++ [0%nat] ] ]) P p q ->
    HLPL.eval_path S P (add_loc_spath r p) (add_loc_spath r q).
Proof.
  intros * get_node not_contains eval_path. induction eval_path.
  - constructor.
  - inversion Heval_proj ; subst.
    + econstructor ; eauto.
      rewrite get_node_remove_loc with (l := l) in get_q, get_q' ; auto.
      econstructor ; eauto.
    + erewrite get_node_remove_loc in get_q ; eauto. econstructor.
      * econstructor ; eauto.
      * destruct (decidable_spath_eq (p +++ [k%nat]) r) ; subst.
        ** eapply HLPL.Eval_path_loc ; eauto.
           rewrite add_loc_spath_not_pref, add_loc_spath_eq ; auto.
           apply E_Loc with (l := l) ; auto.
        ** rewrite add_loc_spath_app in IHeval_path ; auto.
  - inversion Heval_loc ; subst.
    rewrite get_node_remove_loc with (l := l) in get_q ; auto.
    destruct (decidable_spath_eq (p +++ [0%nat]) r) ; subst.
    + apply Eval_path_loc with (q := (add_loc_spath (p +++ [0%nat]) p) +++ [0%nat]).
      * apply E_Loc with (l := l0) ; auto.
      * apply Eval_path_loc with (q := (add_loc_spath (p +++ [0%nat]) (p +++ [0%nat]))) ;
          auto.
        replace (add_loc_spath (p +++ [0%nat]) (p +++ [0%nat])) with
          (add_loc_spath (p +++ [0%nat]) ((p +++ [0%nat]) +++ []))
          by (rewrite app_spath_vpath_nil_r ; auto).
        rewrite add_loc_spath_pref, app_nil_r, add_loc_spath_not_pref ; auto.
        apply E_Loc with (l := l) ; auto.
    + eapply Eval_path_loc ; eauto. rewrite add_loc_spath_app ; auto.
      apply E_Loc with (l := l0) ; auto.
Qed.

Lemma eval_place_end_loc :
  forall S l p r sp,
    get_node (S.[r]) = NLoc l ->
    not_state_contains (eq (NPtr l)) S ->
    (S.[r <- S.[r +++ [0%nat] ] ]) |-{p} p => sp ->
    S |-{p} p => (add_loc_spath r sp).
Proof.
  intros * node not_contains eval_p. inversion eval_p.
  apply sset_not_prefix_valid in H ; try (apply not_strict_prefix_nil).
  constructor ; auto. remember (HLPL.encode_var p.1.1, []) as q.
    destruct (decidable_spath_eq q r).
    + subst q. rewrite !H1 in *. apply Eval_path_loc with (q := (r +++ [0%nat])).
      * apply E_Loc with (l := l) ; auto.
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
    get_node (S.[ sp' ]) = NLoc l ->
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
  forall S vS' p sp op,
    vS'.2 |-{p} p => sp -> S |-{op} op => vS' -> S |-{p} p => sp with
eval_tuple_preserves_eval_place :
  forall S vlS' p sp opl,
    vlS'.2 |-{p} p => sp -> HLPL.eval_tuple opl S vlS' -> S |-{p} p => sp.
Proof.
  {
    intros * eval_p eval_op. inversion eval_op ; subst ; auto.
    - apply eval_place_write_bot with (sp' := pi) ; auto.
    - apply (eval_tuple_preserves_eval_place _ _ _ _ _ eval_p H).
  }
  {
    intros * eval_p eval_op. induction eval_op.
    - cbn in eval_p. exact eval_p.
    - apply (eval_operand_preserves_eval_place _ _ _ _ _ (IHeval_op eval_p) Hop).
  }
Qed.

Lemma eval_rvalue_preserves_eval_place : 
  forall S vS' p sp rv,
    vS'.2 |-{p} p => sp ->
    S |-{rv} rv => vS' ->
    exists sp', S |-{p} p => sp'.
Proof.
  pose proof eval_operand_preserves_eval_place.
  intros * eval_p eval_rv. inversion eval_rv ; subst ; eauto.
  - eapply eval_operand_preserves_eval_place in eval_op_0 ; eauto.
    eapply eval_operand_preserves_eval_place in eval_op_1 ; eauto.
  - eexists ; eapply eval_place_write_loc ; eauto.
Qed.

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
  intros * fresh WTO. induction op using operand_ind' ; auto ; simpl in *.
  - intros * eval_p.
    apply eval_place_valid in eval_p as valid_sp.
    apply eval_place_write_loc in eval_p ; auto. specialize (WTO _ eval_p).
    apply addr_spath_equiv_eval_type in WTO as (addr & equiv).
    eapply addr_spath_equiv_eval_type, ex_intro, addr_spath_equiv_add_loc ; eauto.
  - intros * eval_p.
    apply eval_place_valid in eval_p as valid_sp.
    apply eval_place_write_loc in eval_p ; auto. specialize (WTO _ eval_p).
    apply addr_spath_equiv_eval_type in WTO as (addr & equiv).
    eapply addr_spath_equiv_eval_type, ex_intro, addr_spath_equiv_add_loc ; eauto.
  - induction opl.
    * apply I.
    * destruct WTO as (WTO & WTOl). inversion H ; subst. split.
      ** auto.
      ** apply IHopl ; auto.
Qed.

Lemma remove_loc_welltyped_operand :
  forall bo S op sp l,
    not_state_contains (eq nptr (l)) S ->
    get_node (S.[ sp ]) = NLoc l ->
    WellTypedOperand S bo op ->
    WellTypedOperand (S.[sp <- S.[ sp +++ [ 0%nat ] ] ]) bo op.
Proof.
  intros * not_contains node WTO.
  induction op using operand_ind' ; auto ; cbn in * ; intros.
  - apply eval_place_valid in H as vsp.
    apply eval_type_remove_loc with (l := l) ; cbn ; auto.
    apply WTO, eval_place_end_loc with (l := l) ; auto.
  - apply eval_place_valid in H as vsp.
    apply eval_type_remove_loc with (l := l) ; cbn ; auto.
    apply WTO, eval_place_end_loc with (l := l) ; auto.
  - induction opl ; auto.
    destruct WTO as (WTO & WTOl). inversion H ; subst.
    apply H2 in WTO. apply (IHopl H3) in WTOl. split ; auto.
Qed.

Lemma eval_operand_preserves_valid_spath :
  forall S vS' sp op,
    S |-{op} op => vS' ->
    valid_spath vS'.2 sp ->
    valid_spath S sp with
eval_tuple_preserves_valid_spath :
  forall S vlS' sp opl,
    HLPL.eval_tuple opl S vlS' ->
    valid_spath (vlS'.2) sp ->
    valid_spath S sp.
Proof.                    
  {
    intros * eval_op vsp.
    induction eval_op ; auto.
    - eapply valid_spath_write_bot ; eauto.
    - cbn in vsp. 
      eapply eval_tuple_preserves_valid_spath ; eauto.
  }
  {
    intros * eval_tuple. induction eval_tuple ; intros vsp.
    - exact vsp.
    - cbn in *. eapply (eval_operand_preserves_valid_spath) in Hop ; eauto.
  }
  Qed.

Lemma eval_operand_preserves_eval_type :
  forall bo S vS' sp t op,
    S |-{op} op => vS' ->
    eval_type bo S sp t ->
    valid_spath vS'.2 sp ->
    eval_type bo vS'.2 sp t with
eval_tuple_preserves_eval_type :
  forall bo S vlS' sp t opl,
    HLPL.eval_tuple opl S vlS' ->
    eval_type bo S sp t ->
    valid_spath vlS'.2 sp ->
    eval_type bo vlS'.2 sp t.
Proof.                    
  {
    intros * eval_op. induction eval_op ; intros eval_type vsp ; auto.
    - apply eval_type_write_bot ; auto.
    - cbn in *. eapply eval_tuple_preserves_eval_type ; eauto.
  }
  {
    intros * eval_op eval_type vsp. induction eval_op ; cbn in *.
    - auto.
    - apply IHeval_op ; auto. eapply eval_operand_preserves_eval_type ; eauto.
      eapply eval_tuple_preserves_valid_spath ; eauto.
  }
Qed.

Axiom falso : False.

Lemma welltyped_op_write_bot :
  forall bo S op sp,
    WellTypedOperand S bo op ->
    WellTypedOperand (S.[ sp <- bot ]) bo op.
Proof.
  pose proof eval_place_valid as eval_place_valid.
  pose proof eval_place_write_bot as eval_place_write_bot.
  intros. induction op using operand_ind' ; cbn in * ; auto ; intros.
  - apply eval_type_write_bot ; eauto.
  - apply eval_type_write_bot ; eauto.
  - induction opl ; auto. destruct H as (WTO & WTOl).
    inversion H0 ; subst. apply H2 in WTO. apply IHopl in WTOl ; auto.
Qed.

Lemma eval_operand_preserves_welltyped_op :
  forall bo S vS' op op',
    S |-{op} op' => vS' ->
    WellTypedOperand S bo op ->
    WellTypedOperand vS'.2 bo op with
eval_tuple_preserves_welltyped_op :
  forall bo S vlS' op opl,
    HLPL.eval_tuple opl S vlS' ->
    WellTypedOperand S bo op ->
    WellTypedOperand vlS'.2 bo op.
Proof.                    
  {
    pose proof eval_place_valid as eval_place_valid.
    pose proof eval_place_write_bot as eval_place_write_bot.
    intros * eval_op. induction eval_op ; intros WTO ; auto.
    - eapply welltyped_op_write_bot. exact WTO.
    - eapply eval_tuple_preserves_welltyped_op. exact H. exact WTO.
  }
  {
    intros. induction H ; auto. cbn. apply IHeval_tuple.
    eapply eval_operand_preserves_welltyped_op. exact Hop. exact H0.
  }
Qed.

Lemma eval_rvalue_preserves_welltyped_op :
  forall bo S vS' op rv,
    S |-{rv} rv => vS' ->
    WellTypedOperand S bo op ->
    WellTypedOperand vS'.2 bo op.
Proof.                    
  intros * eval_rv WTO. inversion eval_rv ; subst ; auto.
  - repeat (eapply eval_operand_preserves_welltyped_op ; eauto).
  - replace (w, S'').2 with (v1, S'').2 by reflexivity.
    eapply eval_operand_preserves_welltyped_op ; eauto.
    replace S' with (v0, S').2 by reflexivity.
    eapply eval_operand_preserves_welltyped_op ; eauto.
  - apply add_loc_welltyped_operand ; auto.
Qed.

Lemma eval_operand_preserves_welltyped_rv :
  forall bo S vS' rv op,
    S |-{op} op => vS' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue vS'.2 bo rv with
eval_operand_tuple_preserves_welltyped_rv :
  forall bo S vlS' rv opl,
    HLPL.eval_tuple opl S vlS' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue vlS'.2 bo rv.
Proof.
  {
    intros * eval_op WTRV. destruct rv ; simpl in * ; auto.
    - eapply eval_operand_preserves_welltyped_op ; eauto.
    - destruct b ; destruct WTRV as (WTO_l & WTO_r & E & E') ; repeat split ; auto ;
        eapply eval_operand_preserves_welltyped_op ; eauto.
    - induction eval_op ; auto.
      * destruct WTRV as (t' & Htype & Hplace_rec). exists t' ; split ; auto.
        intros sp Hplace.
        eapply eval_place_write_bot in Hplace as Hplace' ; eauto.
        apply eval_type_write_bot ; auto. apply eval_place_valid with (p := p) ; auto.
      * apply eval_operand_tuple_preserves_welltyped_rv
          with (bo := bo) (rv := (BorrowMut p)) in H ; auto.
  }
  {
    intros * eval_tuple WTRV. induction eval_tuple ; auto ; cbn.
    eapply IHeval_tuple, eval_operand_preserves_welltyped_rv ; eauto.
  }
Qed.

Lemma eval_rvalue_preserves_welltyped_rv :
  forall bo S vS' rv rv',
    S |-{rv} rv' => vS' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue vS'.2 bo rv.
Proof.
  intros * eval_rv WTRV. destruct rv ; simpl in * ; auto.
  - eapply eval_rvalue_preserves_welltyped_op ; eauto.
  - destruct b ; destruct WTRV as (WTO_l & WTO_r & E & E') ;
    repeat split ; auto ; eapply eval_rvalue_preserves_welltyped_op ; eauto.
  - destruct WTRV as (t' & type & Hplace_rec).
    exists t' ; split ; auto. intros * eval_p.
    inversion eval_rv ; subst ; auto.
    + apply eval_place_valid in eval_p as vsp.
      eapply eval_operand_preserves_eval_type ; eauto.
      apply Hplace_rec. eapply eval_operand_preserves_eval_place ; eauto.
    + cbn in *. apply eval_place_valid in eval_p as vsp.
      replace S'' with (v1, S'').2 by reflexivity.
      eapply eval_operand_preserves_eval_type ; eauto.
      replace S' with (v0, S').2 by reflexivity.
      eapply eval_operand_preserves_eval_type ; cbn ; eauto.
      * apply Hplace_rec.
        eapply eval_operand_preserves_eval_place ; eauto.
        eapply eval_operand_preserves_eval_place ; eauto. cbn. assumption.
      * eapply eval_operand_preserves_valid_spath ; eauto.
    + apply eval_place_valid in eval_p as vsp.
      apply eval_place_write_loc in eval_p ; auto.
      specialize (Hplace_rec _ eval_p).
      apply addr_spath_equiv_eval_type in Hplace_rec as (addr & equiv).
      apply addr_spath_equiv_eval_type.
      exists addr. apply addr_spath_equiv_add_loc ; auto.
Qed.

Lemma reorg_preserves_welltyped_op :
  forall bo S S' op,
    reorg S S' ->
    WellTypedOperand S bo op ->
    WellTypedOperand S' bo op.
Proof.
  intros * reorg WTO. pose proof reorg as reorg'.
  destruct reorg ; destruct op ; auto.
  - simpl in * ; intros. apply eval_type_write_bot.
    + eapply eval_place_valid ; eauto.
    + apply eval_place_write_bot in H0. eauto.
  - simpl in * ; intros. apply eval_type_write_bot.
    + eapply eval_place_valid ; eauto.
    + apply eval_place_write_bot in H0. eauto.
  - simpl in * ; intros. induction opl ; auto. destruct WTO as (WTO & WTOl).
    apply IHopl in WTOl. apply welltyped_op_write_bot with (sp := p) in WTO.
    split ; assumption.
  - simpl in * ; intros. apply eval_type_remove_loc with (l := l) ; auto.
    + eapply eval_place_valid ; eauto.
    + eapply eval_place_reorg in reorg' as (sp' & eval_p') ; eauto. eapply WTO ; eauto.
      apply eval_place_end_loc with (l := l) ; auto.
  - simpl in * ; intros. apply eval_type_remove_loc with (l := l) ; auto.
    + eapply eval_place_valid ; eauto.
    + eapply eval_place_reorg in reorg' as (sp' & eval_p') ; eauto. eapply WTO ; eauto.
      apply eval_place_end_loc with (l := l) ; auto.
  - apply remove_loc_welltyped_operand with (l := l) ; auto.
Qed.

Lemma reorg_preserves_welltyped_rv :
  forall bo S S' rv ,
    reorg S S' ->
    WellTypedRValue S bo rv ->
    WellTypedRValue S' bo rv.
Proof.
  intros * reorg WTRV. pose proof reorg as reorg'.
  destruct reorg ; destruct rv ; simpl in * ; auto ; intros.
  - apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct b ; destruct WTRV as (WTO_l & WTO_r & type_l & type_r) ;
      repeat split ; auto ; apply reorg_preserves_welltyped_op with (S := S) ; auto.
  - destruct WTRV as (t' & type & ?). exists t' ; split ; auto.
    intros sp eval_p. apply eval_place_write_bot in eval_p as eval_p'.
    apply eval_place_valid in eval_p as vsp.
    apply eval_place_valid in eval_p' as vsp'.
    apply eval_type_write_bot ; auto.
  - apply remove_loc_welltyped_operand with (l := l) ; auto.
  - destruct b ; destruct WTRV as (WTO_l & WTO_r & type_l & type_r) ;
    repeat split ; auto ; apply remove_loc_welltyped_operand with (l := l) ; auto.
  - destruct WTRV as (t' & type & ?). exists t' ; split ; auto.
    intros sp eval_p. apply eval_place_valid in eval_p as vsp.
    apply eval_type_remove_loc with (l := l) ; auto.
    apply H1. apply eval_place_end_loc with (l := l) ; auto.
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
      destruct (WTS t _ H) as (? & ?) ; auto.
      repeat split ; auto.
      * apply reorg_preserves_welltyped_rv with (S := S) ; auto.
      * apply eval_type_write_bot ; auto.
    + apply eval_place_valid in H as vsp.
      apply eval_place_end_loc with (l := l) in H ; auto.
      destruct (WTS t _ H) as (? & ?) ; auto. repeat split ; auto.
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

Lemma HLPL_PL_Read :
  forall blockof addrof S Spl p sp v t,
    le_pl_hlpl blockof addrof Spl S ->
    S |-{p} p => sp ->
    eval_type blockof S sp t ->
    S.[sp] = v ->
    exists bytes bytes', 
      read Spl p t bytes /\
        concr_hlpl_val addrof v t bytes' /\
        le_block bytes bytes'.
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
    exists bytes bytes',
      Spl |-{op-pl} op => bytes /\
      le_pl_hlpl blockof addrof Spl vS1.2 /\
      concr_hlpl_val addrof vS1.1 t bytes' /\
      le_block bytes bytes' with 
Opl_Preserves_PL_HLPL_Rel :
  forall blockof addrof S Spl opl tl vlS1,
    le_pl_hlpl blockof addrof Spl S ->
    WellTypedOperand S blockof (Tuple opl) ->
    op_get_type (Tuple opl) = TTuple tl ->
    HLPL.eval_tuple opl S vlS1 ->
    exists bytes bytes',
      eval_tuple opl Spl bytes /\
      le_pl_hlpl blockof addrof Spl vlS1.2 /\
      concr_hlpl_val_tuple addrof vlS1.1 tl bytes' /\
      le_block bytes bytes'.
Proof.
  {
    intros bo ao S Spl op t vS1 Hle HWTO Htype Heval.
    pose proof Hle as Htemp ;
      destruct Htemp as (Spl' & HComp & Hconcr & (Hle_env & Hle_mem)).
    pose proof proj1 Hconcr as Hconcr_mem.
    pose proof proj2 Hconcr as Hconcr_env.
    induction Heval.
    - exists (make_int64 n), (make_int64 n). simpl in * ; subst.
      repeat split ; try constructor ; auto ; repeat constructor.
    - exists (make_bool b), (make_bool b). simpl in * ; subst.
      repeat split ; try constructor ; auto ; repeat constructor. reflexivity.
    - specialize (HWTO _ Heval_place). simpl in * ; subst.
      destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ Hle Heval_place HWTO eq_refl)
        as (bytes & bytes' & Hread & Hconcr_val & Hle_val).
      exists bytes, bytes' ; repeat split ; simpl ; auto.
      + econstructor ; eauto.
      + apply (concr_val_equiv_concr_copy_val ao _ _ _ _ Hcopy_val) ; auto.
    - simpl in Htype ; subst. cbn in HWTO.
      specialize (HWTO _ H).
      destruct (HLPL_PL_Read _ _ _ _ _ _ _ _ Hle H HWTO eq_refl)
        as (bytes & bytes' & Hread & Hconcr_val & Hle_block).
      exists bytes, bytes' ; repeat split ; auto.
      + econstructor ; eauto.
      + inversion Hread. simpl.
        exists (Spl'.m.[ addr <- repeat Undef (sizeof p.2) : p.2]).
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
    - cbn. eapply Opl_Preserves_PL_HLPL_Rel in H
        as (bytes & bytes' & eval_tuple & le & concr_tuple & le_b) ; eauto.
      exists bytes, bytes' ; repeat split ; auto.
      * constructor ; auto.
      * cbn in Htype. rewrite <- Htype. constructor. auto.
  }
  {
    intros * Hle HWTO Htype Heval. generalize dependent tl.
    induction Heval ; intros.
    - destruct tl ; cbn in Htype ; try discriminate.
      exists [], [] ; repeat split ; try constructor ; auto.
    - destruct HWTO as (WTO & WTOl). cbn in Htype.
      replace ((fix go (opl : list operand) : Prop := _) opl)
        with (WellTypedOperand S blockof (Tuple opl)) in WTOl by reflexivity.
      apply (eval_operand_preserves_welltyped_op _ _ _ _ _ Hop) in WTOl.
      destruct tl ; cbn in Htype ; try discriminate.
      injection Htype ; intros Htypel Htypeop.
      destruct (Op_Preserves_PL_HLPL_Rel _ _ _ _ _ _ _ Hle WTO Htypeop Hop)
                 as (bytes & bytes' & evalop_pl & le_state & concr_val & le_block).
      specialize (IHHeval le_state WTOl tl). cbn in IHHeval. rewrite Htypel in IHHeval.
      destruct (IHHeval eq_refl) as
        (bytes0 & bytes0' & eval_tup & le_state' & concr_tuple & le_block0).
      cbn. exists (bytes ++ bytes0), (bytes' ++ bytes0'). repeat split ; eauto.
      * constructor ; auto.
      * constructor ; auto.
      * apply Forall2_app ; assumption.
  }
Qed.

Lemma le_pl_hlpl_write_loc :
  forall S Spl bo ao l addr t pi,
    le_pl_hlpl bo ao Spl S ->
    addr ~^{bo, S, t} pi ->
    is_fresh l S ->
    valid_spath S (pi.1, []) ->
    le_pl_hlpl bo (fun l0 : loan_id =>
                     if (l =? l0)%positive then Some (addr, t) else ao l0) Spl
      (S .[ pi <- VLoc l (S .[ pi])]).
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
        rewrite Pos.eqb_refl.
        assert (addr0 ~^{bo, S, t0} pi)
          by (eapply addr_spath_equiv_sset_equal ; split ; eauto).
        destruct (addr_spath_equiv_deterministic _ _ _ _ _ _ _ H1 Hequiv) as [-> ->].
        auto.
      * rewrite get_node_sset_sget_strict_prefix in H1 ; auto.
        assert (l0 <> l) by (eapply is_fresh_loc_id_neq ; eauto ; rewrite H1; auto).
        apply Pos.eqb_neq in H3. rewrite Pos.eqb_sym, H3.
        eapply correct_addrof0 ; eauto. apply addr_spath_equiv_sset in H0 ; auto.
        apply not_prefix_left_strict_prefix_right ; auto.
      * apply addr_spath_equiv_implies_valid_spath in Hequiv as Hvsp.
        destruct H2 as (n & r & <-). rewrite sget_app, sset_sget_equal in H1 ; auto.
        rewrite vget_cons in H1.
        destruct n ; simpl in H1.
        ** rewrite <- sget_app in H1.
           assert (l0 <> l)
             by (eapply is_fresh_loc_id_neq ; eauto ; simpl ; rewrite H1; auto).
           apply Pos.eqb_neq in H2. rewrite Pos.eqb_sym, H2.
           eapply correct_addrof0 ; eauto.
           eapply add_loc_addr_spath_equiv_suffix ; eauto.
        ** (* TODO ask Alban *) replace VBottom with bot in H1 by reflexivity.
           rewrite nth_error_nil, vget_bot in H1. simpl in H1. congruence.
      * symmetry in H2. rewrite sset_sget_disj in H1 ; auto.
        assert (l0 <> l) by (eapply is_fresh_loc_id_neq ; eauto ; rewrite H1 ; auto).
        apply Pos.eqb_neq in H3. rewrite Pos.eqb_sym, H3.
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
        ** replace VBottom with bot in H0 by reflexivity.
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
    exists addrof1 bytes bytes',
      Spl |-{rv-pl} rv => bytes /\
      le_pl_hlpl blockof addrof1 Spl vS1.2 /\
      concr_hlpl_val addrof1 vS1.1 t bytes' /\
      le_block bytes bytes'.
Proof.
  intros bo ao S Spl rv t vS1 Hle_hlpl HWT Htype Heval.
  pose proof Hle_hlpl as Htemp.
  destruct Htemp as (Spl' & Hcomp & Hconcr & Hle).
  induction Heval ; simpl in Htype ; subst.
  - eapply Op_Preserves_PL_HLPL_Rel with
      (blockof := bo) (addrof := ao) (Spl := Spl) in Heval_op as G ;
      [ | exists Spl' | | ] ; auto.
    destruct G as (bytes & bytes' & t0 & ? & ? & ?).
    exists ao, bytes, bytes' ; repeat constructor ; auto.
  - destruct binop.
    {
      destruct HWT as (HWTopl & HWTopr & top_l & top_r).
      apply Op_Preserves_PL_HLPL_Rel with
        (blockof := bo) (addrof := ao) (Spl := Spl) (t := TInt) in eval_op_0 as G1 ;
        [ | exists Spl' | | ] ; auto. simpl in *.
      destruct G1 as (bytes_l & bytes_l' & ? & (Spl'' & ? & ? & ?) & ? & ?).
      apply eval_operand_preserves_welltyped_op with (bo := bo) (op := op_1)
        in eval_op_0 as HWTopr' ; auto. cbn in HWTopr'.
      apply Op_Preserves_PL_HLPL_Rel with
        (blockof := bo) (addrof := ao) (Spl := Spl) (t := TInt) in eval_op_1 as G2 ;
        [ | exists Spl'' | | ] ; auto.
      destruct G2 as (bytes_r & bytes_r' & ? & (Spl''' & ? & ? & ?) & ? & ?).
      simpl in *. inversion Hbinop ; subst. inversion H3 ; inversion H9 ; subst.
      pose proof make_int64_not_contain_Undef.
      apply le_block_not_contains_poison in H4, H10 ; auto ; subst. 
      exists ao, (make_int64 (m + n)), (make_int64 (m + n)). repeat split.
      * constructor ; auto.
      * econstructor ; eauto.
      * constructor.
      * reflexivity.
    }
    {
      destruct HWT as (HWTopl & HWTopr & top_l & top_r).
      apply Op_Preserves_PL_HLPL_Rel with
        (blockof := bo) (addrof := ao) (Spl := Spl) (t := TBool) in eval_op_0 as G1 ;
        [ | exists Spl' | | ] ; auto. simpl in *.
      destruct G1 as (bytes_l & bytes_l' & ? & (Spl'' & ? & ? & ?) & ? & ?).
      apply eval_operand_preserves_welltyped_op with (bo := bo) (op := op_1)
        in eval_op_0 as HWTopr' ; auto. cbn in HWTopr'.
      apply Op_Preserves_PL_HLPL_Rel with
        (blockof := bo) (addrof := ao) (Spl := Spl) (t := TBool) in eval_op_1 as G2 ;
        [ | exists Spl'' | | ] ; auto.
      destruct G2 as (bytes_r & bytes_r' & ? & (Spl''' & ? & ? & ?) & ? & ?).
      simpl in *. inversion Hbinop ; subst. inversion H3 ; inversion H9 ; subst.
    }
  - destruct HWT as (t' & type & Heval_type).
    destruct (reachable_loc bo ao S Hcomp l pi Hloc) as (addr & t0 & Hequiv).
    pose proof ((correct_addrof bo ao S Hcomp) _ _ _ _ Hequiv Hloc).
    assert (Hevt : eval_type bo S pi t0) by
      (apply addr_spath_equiv_eval_type ; exists addr ; auto).
    assert (read_address Spl p t0 addr) by
      (eapply read_addr_spath_equiv_equiv ; eauto ; econstructor ; eauto).
    specialize (Heval_type pi Heval_place).
    assert (t' = t0) by (eapply eval_type_deterministic ; eauto) ; subst.
    exists ao, (make_ptr64 addr), (make_ptr64 addr) ; repeat split.
    * econstructor ; eauto.
    * exists Spl' ; auto.
    * rewrite type. apply Concr_ptr_loc ; auto.
    * reflexivity.
  - destruct HWT as (t' & type & eval_type). specialize (eval_type pi Heval_place).
    destruct (spath_address_place_simul _ _ _ _ _ _ Hle_hlpl Heval_place) as
      (addr & t0 & ? & ?).
    assert (t' = t0) by (apply addr_spath_equiv_eval_type in eval_type as (? & ?) ;
                         eapply addr_spath_equiv_deterministic_type ; eauto).
    subst.
    exists (fun l0 => if (l =? l0)%positive then Some (addr, t0) else ao l0),
      (make_ptr64 addr), (make_ptr64 addr) ; repeat split.
    * econstructor. eapply read_addr_spath_equiv_equiv ; eauto.
    * rewrite snd_pair. apply le_pl_hlpl_write_loc ; auto.
      apply addr_spath_equiv_implies_valid_spath in H1 as Hvp.
      rewrite spath_var_app_vpath in Hvp.
      apply valid_spath_app in Hvp as [? ?] ; auto.
    * rewrite type. apply Concr_ptr_loc. rewrite Pos.eqb_refl ; auto.
    * reflexivity.
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
      * apply sset_preserves_compatibility ; auto ; rewrite ?Heqv ;
          unfold not_contains_bot, not_contains_loc ; not_contains.
      * apply concr_state_write_at_addr ; auto. apply Concr_bot ; auto.
      * destruct (le_pl_r _ _ _ _ _ lu le_st) as (bytes' & lu' & le_b).
        eapply le_pl_write_at_addr_r ; eauto.
        apply concr_val_size in concr. apply Forall2_length in le_b.
        apply le_block_poison ; congruence.
    + apply get_not_bot_valid_spath. intros ?. rewrite H0 in Heqv. discriminate.
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
           apply get_not_bot_valid_spath. rewrite Heqv0. discriminate.
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
           nodes_to_val. rewrite spath_var_app_vpath with (p := p), sget_app in Heqv.
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
  - inversion Hstore ; subst. simpl in WTS. remember (v, S0) as vS0.
    replace S0 with vS0.2 in * by (subst ; reflexivity).
    eapply eval_rvalue_preserves_eval_place in eval_p as [sp' eval_p] ; eauto .
    injection Heqasgn as -> ->.
    destruct (WTS (rv_get_type rv) sp' eval_p eq_refl) as (WTRV & type).
    eapply Rvalue_Preserves_PL_HLPL_Rel in eval_rv
        as (ao1 & bytes & bytes' & eval_rv_pl & Hle' & Hconcr & Hle_block) ; eauto.
    simpl fst in *; simpl snd in *.
    eapply HLPL_PL_Read with (t := rv_get_type rv)
      in eval_p as (bytes0 & bytes0' & Hread & Hconcr' & Hleb) ; eauto.
    inversion Hread. exists (Spl.m.[addr <- bytes : (rv_get_type rv)]).
    eapply Eval_assign with (t := rv_get_type rv) ; eauto.
    eapply Write ; eauto.
  - apply Reorg_Star_Preserves_PL_HLPL_Rel with (S' := S1) in Hle ; auto.
    apply reorg_star_preserves_welltyped_stmt with (S' := S1) in WTS ; auto.
Qed.
