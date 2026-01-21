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
Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import SimulationUtils.

Inductive HLPL_val :=
| HLPL_bot : HLPL_val
| HLPL_int : nat -> HLPL_val 
| HLPL_loc : loan_id -> HLPL_val -> HLPL_val
| HLPL_ptr : loan_id -> HLPL_val
| HLPL_pair : HLPL_val -> HLPL_val -> HLPL_val
.

Variant HLPL_nodes :=
| HLPL_botC : HLPL_nodes
| HLPL_intC : nat -> HLPL_nodes
| HLPL_locC : loan_id -> HLPL_nodes
| HLPL_ptrC : loan_id -> HLPL_nodes
| HLPL_pairC : HLPL_nodes
.

Instance EqDec_HLPL_nodes : EqDecision HLPL_nodes.
Proof. unfold EqDecision, Decision. repeat decide equality. Qed.

Definition HLPL_arity c := match c with
| HLPL_botC => 0
| HLPL_intC _ => 0
| HLPL_locC _ => 1
| HLPL_ptrC _ => 0
| HLPL_pairC => 2
end.

Definition HLPL_get_node v := match v with
| HLPL_bot => HLPL_botC
| HLPL_int n => HLPL_intC n
| HLPL_loc l _ => HLPL_locC l
| HLPL_ptr l => HLPL_ptrC l
| HLPL_pair _ _ => HLPL_pairC
end.

Definition HLPL_children v := match v with
| HLPL_bot => []
| HLPL_int _ => []
| HLPL_loc _ v => [v]
| HLPL_ptr l => []
| HLPL_pair fst snd => [fst ; snd]
end.

Definition HLPL_fold c vs := match c, vs with
| HLPL_intC n, [] => HLPL_int n
| HLPL_locC l, [v] => HLPL_loc l v
| HLPL_ptrC l, [] => HLPL_ptr l
| HLPL_pairC, [fst; snd] => HLPL_pair fst snd
| _, _ => HLPL_bot
end.

Fixpoint HLPL_weight node_weight v :=
  match v with
  | HLPL_loc l v => node_weight (HLPL_locC l) + HLPL_weight node_weight v
  | HLPL_pair fst snd =>
      node_weight (HLPL_pairC) +
        HLPL_weight node_weight fst + HLPL_weight node_weight snd
  | v => node_weight (HLPL_get_node v)
end.

Program Instance ValueHLPL : Value HLPL_val HLPL_nodes := {
  arity := HLPL_arity;
  get_node := HLPL_get_node;
  children := HLPL_children;
  fold_value := HLPL_fold;
  vweight := HLPL_weight;
  bot := HLPL_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_node eq_children; inversion eq_node; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H;
  first [ rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->]
        | destruct (length_2_is_pair H) as [fst [snd ->] ] ];
  reflexivity.
Qed.
Next Obligation.
 intros [] ? H;
  first [rewrite length_zero_iff_nil in H; rewrite H
        | destruct (length_1_is_singleton H) as [? ->] 
        | destruct (length_2_is_pair H) as [fst [snd ->] ] ];
  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; unfold HLPL_children; cbn; lia. Qed.

Record HLPL_state := {
  vars : Pmap HLPL_val;
  anons : Pmap HLPL_val;
}.

Definition encode_var (x : var) := encode (A := var + anon) (inl x).
Definition encode_anon (a : positive) := encode (A := var + anon) (inr a).

Program Instance IsState : State HLPL_state HLPL_val (H := ValueHLPL) := {
  extra := unit;
  get_map S := sum_maps (vars S) (anons S);
  get_extra _ := ();
  alter_at_accessor f a S :=
    match decode' (A := var + anon) a with
    | Some (inl x) => {| vars := alter f x (vars S); anons := anons S|}
    | Some (inr a) => {| vars := vars S; anons := alter f a (anons S)|}
    | None => S
    end;
  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := var + anon) x with
    | Some (inr a) => Some a
    | _ => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S)|};
}.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros ? ? i. cbn. destruct (decode' i) eqn:H.
  - rewrite decode'_is_Some in H.
    destruct s; cbn; rewrite <-H; symmetry;
      first [apply sum_maps_alter_inl | apply sum_maps_alter_inr].
  - symmetry. apply map_alter_not_in_domain, sum_maps_lookup_None. assumption.
Qed.
Next Obligation. intros [? ?] [? ?]. cbn. intros (-> & ->)%sum_maps_eq _. reflexivity. Qed.
(* What are the two following obligations? *)
Next Obligation. discriminate. Qed.
Next Obligation. discriminate. Qed.
Next Obligation. intros. cbn. symmetry. apply sum_maps_insert_inr. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. unfold encode_anon. rewrite decode_encode. reflexivity. Qed.

Lemma get_at_var S x : get_at_accessor S (encode_var x) = lookup x (vars S).
Proof. unfold get_map, encode_var. cbn. apply sum_maps_lookup_l. Qed.

Declare Scope hlpl_scope.
Delimit Scope hlpl_scope with hlpl.

(* TODO: set every priority to 0? *)
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level).
Reserved Notation "'ptrC' ( l )" (at level 0).

(* Notation "'bot'" := HLPL_bot: hlpl_scope. *)
Notation "'loc' ( l , v )" := (HLPL_loc l v) : hlpl_scope.
Notation "'ptr' ( l )" := (HLPL_ptr l) : hlpl_scope.

Notation "'botC'" := HLPL_botC: hlpl_scope.
Notation "'locC' ( l )" := (HLPL_locC l) : hlpl_scope.
Notation "'ptrC' ( l )" := (HLPL_ptrC l) : hlpl_scope.

(* Bind Scope hlpl_scope with HLPL_val. *)
Open Scope hlpl_scope.

Lemma sget_loc l v p : (loc(l, v)).[[ [0] ++  p]] = v.[[p]].
Proof. reflexivity. Qed.
Hint Rewrite sget_loc : spath.
Lemma sget_loc' l v : (loc(l, v)).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite sget_loc' : spath.

(* structural definition of not_value_contains *)
Lemma valid_vpath_pair (vp : vpath) (v1 v2 : HLPL_val) : 
  valid_vpath (HLPL_pair v1 v2) vp ->
  (vp = []) \/ (exists vp', vp = 0 :: vp' ) \/ (exists vp', vp = 1 :: vp').
Proof.
  intros Hvp. destruct vp as [ _ | [ | [ | n ] ] vp' ].
  - left; reflexivity.
  - right ; left. exists vp'; reflexivity.
  - right ; right. exists vp'; reflexivity.
  - inversion Hvp ; subst. simpl in *. rewrite nth_error_nil in H2. easy.
Qed.

Lemma valid_vpath_loc (vp : vpath) (v : HLPL_val) : 
  forall l,
  valid_vpath (HLPL_loc l v) vp ->
  (vp = []) \/ (exists vp', vp = 0 :: vp' ).
Proof.
  intros ? Hvp. destruct vp as [ _ | [ | n' ] vp' ].
  - left; reflexivity.
  - right. exists vp'; reflexivity.
  - inversion Hvp ; subst. simpl in H2. rewrite nth_error_nil in H2. easy.
Qed.

Lemma not_value_contains_struct (v1 v2 : HLPL_val) (f : HLPL_nodes -> Prop) :
  not_value_contains f (HLPL_pair v1 v2)
  <-> not_value_contains f v1 /\ not_value_contains f v2 /\ ~ f HLPL_pairC.
Proof.
  split.
  {
    intros H. split ; [ idtac | split].
    - intros p Hvp. apply (H (0 :: p)). eapply valid_cons ; auto.
    - intros p Hvp. apply (H (1 :: p)). eapply valid_cons ; auto.
    - apply (H []). apply valid_nil.
  }
  {
    intros [H1 [ H2 Hp] ] p Hvp.
    destruct (valid_vpath_pair p v1 v2 Hvp) as [ Hempty | [[vp' H] | [vp' H ] ] ] ;
      subst ; simpl.
    - assumption.
    - apply H1. inversion Hvp; subst. injection H4 as Eq. congruence.
    - apply H2. inversion Hvp; subst. injection H4 as Eq. congruence.
  }
Qed.

Lemma not_value_contains_struct_loc (v : HLPL_val) (f : HLPL_nodes -> Prop) :
  forall l,
  not_value_contains f (HLPL_loc l v)
  <-> not_value_contains f v /\ ~ f (HLPL_locC l).
Proof.
  split.
  {
    intros H. split.
    - intros p Hvp. apply (H (0 :: p)). eapply valid_cons ; auto.
    - apply (H []). apply valid_nil.
  }
  {
    intros [H1 Hp ] p Hvp.
    simpl. 
    destruct (valid_vpath_loc p v l) as [ Hempty | [vp' ?] ] ; subst ; simpl ; auto.
    apply H1. inversion Hvp ; subst. simpl in H3. congruence.
  }
Qed.

(* This property represents the application of a projection p (such as a pointer dereference or a
 * field access) on spath pi0, on a state S.
 * If this projection is successful, then we have eval_proj S p pi0 pi1.
 *)
Variant eval_proj (S : HLPL_state) : proj -> spath -> spath -> Prop :=
  (* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
  | Eval_Deref_Ptr_Locs q q' l
      (get_q : get_node (S.[q]) = ptrC(l)) (get_q' : get_node (S.[q']) = locC(l)) :
    eval_proj S Deref q q'
  (* TODO: add fields *)
  | Eval_Field_First q
      (get_q : get_node (S.[q]) = HLPL_pairC) :
    eval_proj S (Field First) q (q +++ [0])
  | Eval_Field_Second q
      (get_q : get_node (S.[q]) = HLPL_pairC) :
    eval_proj S (Field Second) q (q +++ [1])
.

Variant eval_loc (S : HLPL_state) : spath -> spath -> Prop :=
  (* Coresponds to R-Loc and W-Loc in the article. *)
  | Eval_Loc q l
      (get_q : get_node (S.[q]) = locC(l)) :
    eval_loc S q (q +++ [0])
.

(* Let pi0 be a spath. If by successfully applying the projections in P we
   obtain a spath pi1, then we have the proprety eval_path S P pi0 pi1. *)
Inductive eval_path (S : HLPL_state) : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S proj p q) (Heval_path : eval_path S P q r) :
    eval_path S (proj :: P) p r
| Eval_path_loc P p q r
    (Heval_loc : eval_loc S p q) (Heval_path_rec : eval_path S P q r) :
    eval_path S P p r
.

Definition eval_place S (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S (snd p) (encode_var (fst p), []) pi.

Notation "S  |-{p}  p => pi" := (eval_place S p pi) (at level 50).

Lemma eval_proj_valid S proj q r (H : eval_proj S proj q r) : valid_spath S r.
Proof.
  destruct H; validity.
Qed.

Lemma eval_loc_valid S q r (H : eval_loc S q r) : valid_spath S r.
Proof.
  destruct H; validity.
Qed.

Lemma eval_path_valid (s : HLPL_state) P q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
  - apply IHeval_q_r. destruct Heval_loc. validity.
Qed.

Lemma eval_place_valid s p pi (H : eval_place s p pi) : valid_spath s pi.
Proof. destruct H as (? & ?). eapply eval_path_valid; eassumption. Qed.
Hint Resolve eval_place_valid : spath.

Variant is_loc : HLPL_nodes -> Prop :=
| IsLoc_Loc l : is_loc (locC(l)).
Definition not_contains_loc := not_value_contains is_loc.
Hint Unfold not_contains_loc : spath.
Hint Extern 0 (~is_loc _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Definition get_loc_id c :=
  match c with
  | locC(l) => Some l
  | ptrC(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loc_id c = Some l) S).

Lemma is_fresh_loc_id_neq (S : HLPL_state) l0 l1 (p : spath) :
  get_loc_id (get_node (S.[p])) = Some l0 -> is_fresh l1 S -> l0 <> l1.
Proof.
  intros get_p Hfresh <-. eapply Hfresh; [ | exact get_p].
  apply get_not_bot_valid_spath. intro H. rewrite H in get_p. inversion get_p.
Qed.


Hint Extern 0 (get_loc_id _ <> Some ?l) =>
  lazymatch goal with
  | Hfresh : is_fresh ?l ?S, get_p : get_node (?S.[?p]) = ?v |- _ =>
      injection;
      refine (is_fresh_loc_id_neq S _ l p _ Hfresh);
      rewrite get_p;
      reflexivity
   end : spath.

Inductive copy_val : HLPL_val -> HLPL_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_int n) (HLPL_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w
| Copy_pair v1 v1' v2 v2' (H1 : copy_val v1 v1') (H2 : copy_val v2 v2') :
  copy_val (HLPL_pair v1 v2) (HLPL_pair v1' v2').

Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> HLPL_state -> (HLPL_val * HLPL_state) -> Prop :=
  | Eval_IntConst S n :
    S |-{op} INT n => (HLPL_int n, S)
  | Eval_copy S t (p : place) pi v
      (Heval_place : eval_place S p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy t p => (v, S)
  | Eval_move S t (p : place) pi :
    eval_place S p pi ->
    not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move t p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> HLPL_state -> (HLPL_val * HLPL_state) -> Prop :=
  | Eval_just t op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just t op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' t op_l op_r m n :
      (S |-{op} op_l => (HLPL_int m, S')) ->
      (S' |-{op} op_r => (HLPL_int n, S'')) ->
      S |-{rv} (BinOp t op_l op_r) => ((HLPL_int (m + n)), S'')
  | Eval_pointer_loc S t p pi l
      (Heval_place : S |-{p} p => pi)
      (Hloc : get_node (S.[pi]) = locC(l)) : S |-{rv} &mut p : t => (ptr(l), S)
  | Eval_pointer_no_loc S t p pi l
      (* TODO *)
      (Heval_place : S |-{p} p => pi):
      is_fresh l S ->
      S |-{rv} (&mut p : t) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
  | Eval_pair
      S S' S'' v1 v2
      fst_op t1 (Heval_first: eval_operand fst_op S (v1, S'))
      snd_op t2 (Heval_first: eval_operand snd_op S' (v2, S'')) :
    eval_rvalue (Pair (TPair t1 t2) fst_op snd_op) S ((HLPL_pair v1 v2), S'')
where "S |-{rv} rv => r" := (eval_rvalue rv S r).
(* TODO: add rule for pairs *)

Lemma HLPL_Operand_NoLoc (S: HLPL_state) (op : operand) (vS : HLPL_val * HLPL_state) :
  S |-{op} op => vS -> not_contains_loc vS.1 .
Proof.
  intros [ | | ]; simpl ; try (unfold not_contains_loc ; not_contains).
  induction Hcopy_val ; not_contains.
  apply not_value_contains_struct ; repeat split ; auto.
  intros H ; inversion H.
Qed.

Lemma HLPL_Rvalue_NoLoc (S: HLPL_state) (rv : rvalue) (vS : HLPL_val * HLPL_state) :
  S |-{rv} rv => vS -> not_contains_loc vS.1.
Proof.
  intros Hrv ; induction Hrv ; try (unfold not_contains_loc ; not_contains).
  - eapply HLPL_Operand_NoLoc, Heval_op.
  - apply not_value_contains_struct.
    apply HLPL_Operand_NoLoc in Heval_first, Heval_first0; simpl in *.
    repeat split ; auto.
    intros H ; inversion H.
Qed.

Inductive reorg : HLPL_state -> HLPL_state -> Prop :=
| Reorg_end_ptr S (p : spath) l :
    get_node (S.[p]) = ptrC(l) -> reorg S (S.[p <- bot])
| Reorg_end_loc S (p : spath) l :
    get_node (S.[p]) = locC(l) -> not_state_contains (eq ptrC(l)) S ->
    reorg S (S.[p <- S.[p +++ [0] ] ])
.

(* Automatically resolving the goals of the form `ptrC(l) <> _`, used to prove the condition
   `not_state_contains (eq ptrC(l)) S` of the rule Reorg_end_loc. *)
Hint Extern 0 (ptrC( _ ) <> _) => discriminate : spath.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : HLPL_val * HLPL_state -> HLPL_state -> Prop :=
  | Store v S (sp : spath) (eval_p : S |-{p} p => sp):
    store p (v, S) (S.[sp <- v])
.

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_state -> statement -> nat -> Option (statement_result * HLPL_state) -> Prop
*)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).

Inductive eval_stmt : statement -> statement_result -> HLPL_state -> HLPL_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => rUnit, S
  | Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | Eval_assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | Eval_reorg S0 S1 S2 stmt r (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(* Test the semantics *)

Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

Fixpoint decide_not_value_contains (P : HLPL_nodes -> bool) v :=
  negb (P (get_node v)) &&
    match v with
      loc(l, w) => decide_not_value_contains P w
    | HLPL_pair v1 v2 =>
        decide_not_value_contains P v1 &&
          decide_not_value_contains P v2
    | _ => true end.

Lemma decide_not_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  decide_not_value_contains P v = true -> not_value_contains H v.
Proof.
  intro decide_is_true. induction v.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *.
      intros G%H_implies_P. rewrite G in decide_is_true. inversion decide_is_true.
    + destruct i.
      * cbn in *; subst. apply IHv. eapply andb_prop, decide_is_true.
        inversion H0. auto.
      * simpl in H0. rewrite nth_error_nil in H0; discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *. intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + cbn in *. rewrite nth_error_nil in * |-. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *. intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + cbn in *;
      destruct (andb_prop _ _ decide_is_true);
      destruct (andb_prop _ _ H3).
      destruct i.
      * cbn in *. apply IHv1. auto. congruence. 
      * destruct i.
        ** cbn in *. apply IHv2. auto. congruence.
        ** cbn in *. rewrite nth_error_nil in H0. discriminate.
Qed.

Definition decide_is_bot v := match v with botC => true | _ => false end.

Corollary decide_not_contains_bot v (H : decide_not_value_contains decide_is_bot v = true) :
  not_contains_bot v.
Proof. eapply decide_not_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Definition decide_not_state_contains (P : HLPL_nodes -> bool) (S : HLPL_state) :=
  map_fold (fun k v b => decide_not_value_contains P v && b) true (get_map S).

Lemma decide_state_contains_correct H P S (H_implies_P : forall v, H v -> P v = true) :
  decide_not_state_contains P S = true -> not_state_contains H S.
Proof.
  intros G p. unfold sget. intros (v & getval_S & ?). rewrite getval_S.
  intros H_in_v.
  unfold decide_not_state_contains in G.
  erewrite map_fold_delete_L in G; [ | intros; ring | eassumption].
  destruct (decide_not_value_contains P v) eqn:EQN.
  - eapply decide_not_value_contains_correct in EQN; [ | eassumption].
    eapply EQN; eassumption.
  - rewrite andb_false_l in G. discriminate.
Qed.

Definition decide_is_loc v := match v with locC(l) => true | _ => false end.
Definition decide_is_loc_id l v :=
  match v with
  | locC(l') | ptrC(l') => l =? l'
  | _ => false
  end.


Lemma decide_is_fresh S l (H : decide_not_state_contains (decide_is_loc_id l) S = true) :
  is_fresh l S.
  Proof.
    eapply decide_state_contains_correct; try eassumption.
    intros c G. destruct c; inversion G; apply Nat.eqb_refl.
  Qed.


Notation x := 1%positive.
Notation y := 2%positive.
Notation z := 3%positive.
Notation a := 1%positive.
Notation b := 2%positive.
Notation c := 3%positive.
Notation d := 4%positive.
Notation a1 := 1%positive.
Notation a2 := 2%positive.
Notation a3 := 3%positive.
Notation a4 := 4%positive.
Notation a5 := 5%positive.
Notation a6 := 6%positive.
Notation l1 := 0%nat.
Notation l2 := 1%nat.

Definition prog :=
  ASSIGN (x, nil) <- Just TInt (INT 3) ;;
  ASSIGN (y, nil) <- &mut (1%positive, nil) : TRef.

Definition main : statement :=
  ASSIGN (a, []) <- Just TInt (INT 1983) ;;
  ASSIGN (b, []) <- Just TInt (INT 1986) ;;
  ASSIGN (c, []) <- &mut (a, []) : TRef ;;
  ASSIGN (d, []) <- &mut (c, [Deref]) : TRef ;;
  ASSIGN (c, []) <- &mut (b, []) : TRef ;;
  ASSIGN (d, [Deref]) <- Just TInt (INT 58) ;;
  Nop
.

Definition main_pair : statement :=
  ASSIGN (a, []) <- Pair (TPair TInt TInt) (INT 667) (INT 1986) ;;
  ASSIGN (b, []) <- Just TInt (Move TInt (a, [ Field (First)] )) ;;
  ASSIGN (c, []) <- &mut (a, [Field (Second)]) : TRef ;;
  Nop
.

Section SemTest.

  Local Open Scope positive.
  Local Open Scope stdpp.

  Hint Rewrite (@alter_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singleton];
    autorewrite with core.

  Definition empty_state : HLPL_state :=
    {| vars := {[ x := HLPL_int 0; y := HLPL_int 0 ]} ; anons := PEmpty |}.
  Definition empty_state' : HLPL_state :=
    {|
      vars := {[ a := HLPL_bot; b := HLPL_bot; c := HLPL_bot; d := HLPL_bot ]} ;
      anons := PEmpty
    |}.


(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
  Ltac eval_var :=
    split; [eexists; split; [reflexivity | constructor] | ].


  Goal exists final_state, empty_state |-{stmt} prog => rUnit, final_state. 
    eexists.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      + repeat constructor.
      + apply Store ; eval_var; constructor.
    }
    {
      eapply Eval_assign.
      + apply Eval_pointer_no_loc with (l := l1) (pi := (encode_var x, [])).
        * eval_var; constructor.
        * not_contains.
          { apply decide_is_fresh. easy. }
      + apply Store ; eval_var; constructor. 
    }
  Qed.

  Goal exists final_state, empty_state' |-{stmt} main => rUnit, final_state.
    eexists.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - repeat constructor.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - repeat constructor.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - apply Eval_pointer_no_loc with (l := l1); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - apply Eval_pointer_loc with (pi := (encode_var 1, [])).
        * repeat econstructor; try easy.
        * reflexivity.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - apply Eval_pointer_no_loc with (l := l2); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - repeat constructor.
      - apply Store.
        * repeat constructor.
          ** eexists; split; constructor.
          ** simpl. apply Eval_cons with (q := (encode_var 1, []));
             repeat econstructor; easy.
    }
    apply Eval_nop.
    Qed.

  Goal exists final_state, empty_state' |-{stmt} main_pair => rUnit, final_state.
    eexists.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - repeat econstructor.
      - apply Store ; repeat constructor.
        simpl. eexists; split; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - repeat econstructor. 
        * apply decide_not_value_contains_correct with (P := decide_is_loc).
          ** intros. inversion H; subst; reflexivity.
          ** reflexivity.
        * apply decide_not_contains_bot; reflexivity.
      - apply Store ; repeat constructor. simpl. eexists; split; constructor.
    }
    simpl_state.
    eapply Eval_seq_unit.
    {
      eapply Eval_assign.
      - apply Eval_pointer_no_loc with (l := l1).
        * repeat econstructor.
        * apply decide_is_fresh; reflexivity.
      - apply Store ; repeat constructor. simpl. eexists; split; constructor.
    }
    apply Eval_nop.
    Qed.
End SemTest.


Record HLPL_well_formed (S : HLPL_state) : Prop := {
  at_most_one_loc l : at_most_one_node (locC(l)) S;
}.

Notation scount c S := (sweight (indicator c) S).

Record HLPL_well_formed_alt (S : HLPL_state) l : Prop := {
  at_most_one_loc_alt : scount (locC(l)) S <= 1;
}.

Lemma well_formedness_equiv S : HLPL_well_formed S <-> forall l, HLPL_well_formed_alt S l.
Proof.
  split.
  - intros WF l. destruct WF. split.
    rewrite<- decide_at_most_one_node; easy.
  - intros WF. split; intros l; destruct (WF l).
    apply decide_at_most_one_node; [discriminate | ]. assumption.
Qed.

Lemma vweight_loc weight l v :
  vweight weight (loc(l, v)) = weight (locC(l)) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_loc : weight.

Lemma vweight_ptr weight l : vweight weight (ptr(l)) = weight (ptrC(l)).
Proof. reflexivity. Qed.
Hint Rewrite vweight_ptr : weight.

Lemma vweight_int weight n :
  vweight weight (HLPL_int n) = weight (HLPL_intC n).
Proof. reflexivity. Qed.
Hint Rewrite vweight_int : weight.

Lemma vweight_bot weight : vweight weight bot = weight (botC).
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.
