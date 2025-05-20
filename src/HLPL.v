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
| HLPL_bot
| HLPL_int (n : nat) (* TODO: use Aeneas integer types? *)
| HLPL_loc (l : loan_id) (v : HLPL_val)
| HLPL_ptr (l : loan_id)
| HLPL_pair (fst : HLPL_val) (snd : HLPL_val)
.

Variant HLPL_nodes :=
| HLPL_botC
| HLPL_intC (n : nat)
| HLPL_locC (l : loan_id)
| HLPL_ptrC (l : loan_id)
| HLPL_pairC
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


(* This property represents the application of a projection p (such as a pointer dereference or a
 * field access) on spath pi0, on a state S and given a permission perm.
 * If this projection is successful, then we have eval_proj S perm p pi0 pi1.
 *)
Inductive eval_proj (S : HLPL_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| Eval_Deref_Ptr_Locs q q' l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = ptrC(l)) (get_q' : get_node (S.[q']) = locC(l)) :
    eval_proj S perm Deref q (q' +++ [0])
(* Coresponds to R-Loc and W-Loc in the article. *)
| Eval_Loc proj q q' l
    (Hperm : perm = Imm)
    (get_q : get_node (S.[q]) = locC(l))
    (eval_proj_rec : eval_proj S perm proj (q +++ [0]) q') : eval_proj S perm proj q q'
(* TODO: add fields *)
| Eval_Field_First q
  (get_q : get_node (S.[q]) = HLPL_pairC) :
  eval_proj S perm (Field First) q (q +++ [0])
| Eval_Field_Second q
  (get_q : get_node (S.[q]) = HLPL_pairC) :
  eval_proj S perm (Field Second) q (q +++ [1])
.

(* Let pi0 be a spath. If by successfully applying the projections in P (with permission perm) we
   obtain a spath pi1, then we have the proprety eval_path S perm P pi0 pi1. *)
Inductive eval_path (S : HLPL_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd p) (encode_var (fst p), []) pi.

Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Print sget.
Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. destruct (S.[q']) eqn:EQN; try discriminate. split.
    + apply get_not_bot_valid_spath. rewrite EQN. discriminate.
    + eapply valid_cons; reflexivity || apply valid_nil.
  - apply IHeval_proj.
  - apply valid_spath_app. destruct (S.[q]) eqn:EQN; try discriminate. split.
    + apply get_not_bot_valid_spath. rewrite EQN. discriminate.
    + apply valid_cons with (w := y1); auto. apply valid_nil.
  - apply valid_spath_app. destruct (S.[q]) eqn:EQN; try discriminate. split.
    + apply get_not_bot_valid_spath. rewrite EQN. discriminate.
    + apply valid_cons with (w := y2); auto. apply valid_nil.
Qed.

Lemma eval_path_valid (s : HLPL_state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
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
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> HLPL_state -> (HLPL_val * HLPL_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (HLPL_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
     not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

(* Note: these functions are used when borrowing a spath that is already under a location without
 * introducing a new location. spath_pred pi given the node about pi (and botC if this node doesn't
 * exist).
 * However, I should maybe rewrite it with a proposition instead of a function. *)
(* TODO: if I keep it, move in PathToSubtree.v *)
Definition vpath_pred (p : vpath) : option vpath :=
  match p with
  | [] => None
  | _ => Some (removelast p)
  end.

Definition spath_pred (p : spath) : option spath :=
  SOME q <- vpath_pred (snd p) IN Some (fst p, q).

Lemma vpath_pred_add_anon p i : vpath_pred (p ++ [i]) = Some p.
Proof.
  transitivity (Some (removelast (p ++ [i]))).
  - destruct (p ++ [i]) eqn:?.
    + exfalso. eapply app_cons_not_nil. eauto.
    + reflexivity.
  - f_equal. apply removelast_last.
Qed.

Lemma spath_pred_add_anon (p : spath) i : spath_pred (p +++ [i]) = Some p.
Proof.
  unfold spath_pred, app_spath_vpath. cbn. rewrite vpath_pred_add_anon.
  rewrite<- surjective_pairing. reflexivity.
Qed.

Lemma spath_pred_is_Some (p q : spath) : spath_pred p = Some q -> exists i, p = q +++ [i].
Proof.
  unfold spath_pred. intro.
  assert (snd p <> []) by now destruct (snd p).
  assert ((fst p, removelast (snd p)) = q) as <-.
  { destruct (snd p); [discriminate | injection H; easy]. }
  exists (List.last (snd p) 0). unfold app_spath_vpath. cbn.
  rewrite<- app_removelast_last by assumption.
  apply surjective_pairing.
Qed.

Definition vancestor (v : HLPL_val) p : HLPL_nodes :=
  match vpath_pred p with
  | None => botC
  | Some q => get_node (v.[[q]])
  end.

Definition ancestor (S : HLPL_state) (p : spath) : HLPL_nodes :=
  match spath_pred p with
  | None => botC
  | Some q => get_node (S.[q])
  end.

Lemma vancestor_singleton v i : vancestor v [i] = get_node v.
Proof. reflexivity. Qed.
Hint Rewrite vancestor_singleton : spath.

Lemma ancestor_sset_not_strict_prefix S p q v :
  ~strict_prefix q p -> ancestor (S.[q <- v]) p = ancestor S p.
Proof.
  unfold ancestor. intro. autodestruct.
  intros (? & ->)%spath_pred_is_Some.
  rewrite get_node_sset_sget_not_prefix by auto with spath. reflexivity.
Qed.
Hint Rewrite ancestor_sset_not_strict_prefix using auto with spath; fail : spath.

Lemma ancestor_is_not_bot S p c :
  ancestor S p = c -> c <> botC -> exists q i, p = q +++ [i] /\ get_node (S.[q]) = c.
Proof.
  unfold ancestor. autodestruct. intros (i & ->)%spath_pred_is_Some.
  intros. eexists _, _. eauto.
Qed.

Lemma vancestor_app v p q : q <> [] -> vancestor v (p ++ q) = vancestor (v.[[p]]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold vancestor. rewrite app_assoc, !vpath_pred_add_anon, vget_app.
  reflexivity.
Qed.

Lemma ancestor_app S p q : q <> [] -> ancestor S (p +++ q) = vancestor (S.[p]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold ancestor, vancestor.
  rewrite app_spath_vpath_assoc, spath_pred_add_anon, vpath_pred_add_anon, sget_app.
  reflexivity.
Qed.

Hint Rewrite vancestor_app using easy : spath.
Hint Rewrite ancestor_app using easy : spath.

Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> HLPL_state -> (HLPL_val * HLPL_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => (HLPL_int m, S')) ->
      (S' |-{op} op_r => (HLPL_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => ((HLPL_int (m + n)), S'')
  | Eval_pointer_loc S p pi l
      (Heval_place : S |-{p} p =>^{Mut} pi)
      (Hancestor_loc : ancestor S pi = locC(l)) : S |-{rv} &mut p => (ptr(l), S)
  | Eval_pointer_no_loc S p pi l
      (* TODO *)
      (Heval_place : S |-{p} p =>^{Mut} pi):
      is_fresh l S ->
      S |-{rv} (&mut p) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).
(* TODO: add rule for pairs *)

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
| Store v S (sp : spath) (a : anon)
  (eval_p : (S,, a |-> v) |-{p} p =>^{Mut} sp):
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
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


Record HLPL_well_formed (S : HLPL_state) : Prop := {
  at_most_one_loc l : at_most_one_node (locC(l)) S;
}.

Notation scount c S := (sweight (indicator c) S).

Record HLPL_well_formed_alt (S : HLPL_state) l : Prop := {
  at_most_one_loc_alt : scount (locC(l)) S <= 1;
}.

Lemma well_formedness_equiv S : HLPL_well_formed S <-> forall l, HLPL_well_formed_alt S l.
Proof.
Admitted.

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
