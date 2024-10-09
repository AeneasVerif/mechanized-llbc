Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Import ListNotations.

Inductive HLPL_plus_val :=
| HLPL_plus_bot
| HLPL_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| HLPL_plus_mut_loan (l : loan_id)
| HLPL_plus_mut_borrow (l : loan_id) (v : HLPL_plus_val)
(*
| HLPL_plus_shr_loan (l : loan_id) (v : HLPL_plus_val)
| HLPL_plus_shr_borrow (l : loan_id)
 *)
| HLPL_plus_loc (l : loan_id) (v : HLPL_plus_val)
| HLPL_plus_ptr (l : loan_id)
(* | HLPL_plus_pair (v0 : HLPL_plus_val) (v1 : HLPL_plus_val) *)
.

Variant HLPL_plus_binder :=
| Var (v : var)
(* | Box (l : nat) *)
| Anon.

Program Global Instance EqDec_binder : EqDec HLPL_plus_binder.
Next Obligation. repeat decide equality. Qed.

Variant HLPL_plus_constructor :=
| HLPL_plus_botC
| HLPL_plus_intC (n : nat)
| HLPL_plus_mut_loanC (l : loan_id)
| HLPL_plus_mut_borrowC (l : loan_id)
| HLPL_plus_locC (l : loan_id)
| HLPL_plus_ptrC (l : loan_id)
.

Definition HLPL_plus_arity c := match c with
| HLPL_plus_botC => 0
| HLPL_plus_intC _ => 0
| HLPL_plus_mut_loanC _ => 0
| HLPL_plus_mut_borrowC _ => 1
| HLPL_plus_locC _ => 1
| HLPL_plus_ptrC _ => 0
end.

Definition HLPL_plus_get_constructor v := match v with
| HLPL_plus_bot => HLPL_plus_botC
| HLPL_plus_int n => HLPL_plus_intC n
| HLPL_plus_mut_loan l => HLPL_plus_mut_loanC l
| HLPL_plus_mut_borrow l _ => HLPL_plus_mut_borrowC l
| HLPL_plus_loc l _ => HLPL_plus_locC l
| HLPL_plus_ptr l => HLPL_plus_ptrC l
end.

Definition HLPL_plus_subvalues v := match v with
| HLPL_plus_bot => []
| HLPL_plus_int _ => []
| HLPL_plus_mut_loan _ => []
| HLPL_plus_mut_borrow _ v => [v]
| HLPL_plus_loc _ v => [v]
| HLPL_plus_ptr l => []
end.

Definition HLPL_plus_fold c vs := match c, vs with
| HLPL_plus_intC n, [] => HLPL_plus_int n
| HLPL_plus_mut_loanC l, [] => HLPL_plus_mut_loan l
| HLPL_plus_mut_borrowC l, [v] => HLPL_plus_mut_borrow l v
| HLPL_plus_locC l, [v] => HLPL_plus_loc l v
| HLPL_plus_ptrC l, [] => HLPL_plus_ptr l
| _, _ => HLPL_plus_bot
end.

Program Instance ValueHLPL : Value HLPL_plus_val := {
  constructors := HLPL_plus_constructor;
  arity := HLPL_plus_arity;
  get_constructor := HLPL_plus_get_constructor;
  subvalues := HLPL_plus_subvalues;
  fold_value := HLPL_plus_fold;
  bot := HLPL_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
destruct v; destruct w; inversion eq_constructor; inversion eq_subvalues; reflexivity.
Qed.
Next Obligation.
  destruct c; (rewrite length_zero_iff_nil in H; rewrite H) ||
              destruct (length_1_is_singleton H) as [? ->];
              reflexivity.
Qed.
Next Obligation.
  destruct c; (rewrite length_zero_iff_nil in H; rewrite H) ||
              destruct (length_1_is_singleton H) as [? ->];
              reflexivity.
Qed.

Definition HLPL_plus_state := state HLPL_plus_binder HLPL_plus_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: move in lang.v *)
(* TODO: set every priority to 0? *)
Reserved Notation "'bot'" (at level 0).
Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level).
Reserved Notation "'ptrC' ( l )" (at level 0).

Notation "'bot'" := HLPL_plus_bot: hlpl_plus_scope.
Notation "'loan^m' ( l )" := (HLPL_plus_mut_loan l) : hlpl_plus_scope.
Notation "'borrow^m' ( l  , v )" := (HLPL_plus_mut_borrow l v) : hlpl_plus_scope.
Notation "'loc' ( l , v )" := (HLPL_plus_loc l v) : hlpl_plus_scope.
Notation "'ptr' ( l )" := (HLPL_plus_ptr l) : hlpl_plus_scope.

Notation "'botC'" := HLPL_plus_botC: hlpl_plus_scope.
Notation "'loanC^m' ( l )" := (HLPL_plus_mut_loanC l) : hlpl_plus_scope.
Notation "'borrowC^m' ( l )" := (HLPL_plus_mut_borrowC l) : hlpl_plus_scope.
Notation "'locC' ( l )" := (HLPL_plus_locC l) : hlpl_plus_scope.
Notation "'ptrC' ( l )" := (HLPL_plus_ptrC l) : hlpl_plus_scope.

(* Bind Scope hlpl_plus_scope with HLPL_plus_val. *)
Open Scope hlpl_plus_scope.

Inductive eval_proj (S : HLPL_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_constructor (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
(* Coresponds to R-Deref-Ptr-Loc and W-Deref-Ptr-Loc in the article. *)
| Eval_Deref_Ptr_Locs q q' l
    (Hperm : perm <> Mov)
    (get_q : get_constructor (S.[q]) = ptrC(l)) (get_q' : get_constructor (S.[q']) = locC(l)) :
    eval_proj S perm Deref q (q' +++ [0])
(* Coresponds to R-Loc and W-Loc in the article. *)
| Eval_Loc proj q q' l
    (Hperm : perm = Imm)
    (get_q : get_constructor (S.[q]) = locC(l))
    (eval_proj_rec : eval_proj S perm proj (q +++ [0]) q') : eval_proj S perm proj q q'
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : HLPL_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r: eval_proj S perm proj p q -> eval_path S perm P q r ->
    eval_path S perm (proj :: P) p r.

Notation eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
  - apply valid_spath_app. destruct (S.[q']) eqn:EQN; try discriminate. split.
    + apply get_not_bot_valid_spath. rewrite EQN. discriminate.
    + eapply valid_cons; reflexivity || apply valid_nil.
  - apply IHeval_proj.
Qed.

Lemma eval_path_valid (s : HLPL_plus_state) P perm q r
  (valid_q : valid_spath s q) (eval_q_r : eval_path s perm P q r) :
  valid_spath s r.
Proof.
  induction eval_q_r.
  - assumption.
  - apply IHeval_q_r. eapply eval_proj_valid. eassumption.
Qed.

Lemma eval_place_valid s p perm pi (H : eval_place s perm p pi) : valid_spath s pi.
Proof.
  destruct H as (? & ? & ?). eapply eval_path_valid; try eassumption.
  eapply find_binder_valid. eassumption.
Qed.

(* Setting up the definitions for judgements like "loan \notin v" or
   "l is fresh". *)
Definition state_contains (H : HLPL_plus_val -> Prop) (S : HLPL_plus_state) :=
  exists p, valid_spath S p /\ H (S.[p]).

Definition value_contains (H : HLPL_plus_val -> Prop) (v : HLPL_plus_val) :=
  exists p, valid_vpath v p /\ H (v.[[p]]).

Definition is_loan (v : HLPL_plus_val) :=
  exists l, v = loan^m(l).
Definition contains_loan := value_contains is_loan.

Definition is_mut_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition contains_outer_loan v :=
  exists l p, v.[[p]] = loan^m(l) /\ (forall q, vprefix q p -> ~is_mut_borrow (v.[[q]])).

Definition contains_outer_loc (v : HLPL_plus_val) :=
  exists l w p, v.[[p]] = loc(l, w) /\ (forall q, vprefix q p -> ~is_mut_borrow (v.[[q]])).

Definition is_loc (v : HLPL_plus_val) := exists l w, v = loc(l, w).
Definition contains_loc := value_contains is_loc.

Variant is_loan_id (l : loan_id) : HLPL_plus_val -> Prop  :=
| Is_loan_id_loan : is_loan_id l (loan^m(l))
| Is_loan_id_borrow w : is_loan_id l (borrow^m(l, w))
| Is_loan_id_ptr : is_loan_id l (ptr(l))
| Is_loan_id_loc w : is_loan_id l (loc(l, w)).

Definition is_fresh l S := ~state_contains (is_loan_id l) S.

Definition is_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition not_in_borrow (S : HLPL_plus_state) p :=
  forall q, prefix q p /\ is_borrow (S.[q]) -> q = p.

Definition contains_bot (v : HLPL_plus_val) :=
  value_contains (fun w => w = bot) v.

Inductive copy_val : HLPL_plus_val -> HLPL_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_plus_int n) (HLPL_plus_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

Variant eval_op (S : HLPL_plus_state) : operand -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
| Eval_IntConst n : eval_op S (IntConst n) (HLPL_plus_int n) S
| Eval_copy (p : place) pi v : eval_place S Imm p pi -> copy_val (S.[pi]) v ->
    eval_op S (Copy p) v S
| Eval_move (p : place) pi : eval_place S Mov p pi -> ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
  eval_op S (Move p) (S.[pi]) (S.[pi <- bot]).

(* FIXME *)
Variant get_loc_id (S : HLPL_plus_state) : spath -> option loan_id -> Prop :=
  | GetLocId_loc pi l : get_constructor (S.[pi]) = locC(l) -> get_loc_id S (pi +++ [0]) (Some l)
  | GetLocId_not_loc pi i : ~is_loc (S.[pi]) -> get_loc_id S (pi +++ [i]) None
  | GetLocId_nil i : get_loc_id S (i, []) None.

Variant eval_rvalue (S : HLPL_plus_state) : rvalue -> HLPL_plus_val -> HLPL_plus_state -> Prop :=
| Eval_just op v S' : eval_op S op v S' -> eval_rvalue S (Just op) v S'
(* For the moment, the only operation is the natural sum. *)
| Eval_bin_op S' S'' op_l op_r m n : eval_op S op_l (HLPL_plus_int m) S' ->
   eval_op S' op_r (HLPL_plus_int n) S'' ->
   eval_rvalue S (BinOp op_l op_r) (HLPL_plus_int (m + n)) S''
| Eval_pointer_loc p pi l : eval_place S Mut p pi -> get_loc_id S pi (Some l) ->
    ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
    eval_rvalue S (&mut p) (ptr(l)) S
| Eval_pointer p pi l : eval_place S Mut p pi -> get_loc_id S pi None ->
    ~contains_loan (S.[pi]) -> ~contains_bot (S.[pi]) ->
    is_fresh l S ->
    eval_rvalue S (&mut p) (ptr(l)) (S.[pi <- loc(l, S.[pi])]).

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_refl S : reorg S S
| Reorg_trans S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    disj p q -> S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    ~contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_plus_state -> statement -> nat -> Option (statement_result * HLPL_plus_state) -> Prop
*)
Inductive eval_stmt : HLPL_plus_state -> statement -> statement_result -> HLPL_plus_state -> Prop :=
| Eval_nop S : eval_stmt S Nop rUnit S
| Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : eval_stmt S0 stmt_l rUnit S1)
    (eval_stmt_r : eval_stmt S1 stmt_r r S2) : eval_stmt S0 (stmt_l ;; stmt_r) r S2
| Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : eval_stmt S0 stmt_l rPanic S1) :
    eval_stmt S0 (stmt_l ;; stmt_r) rPanic S1
| Eval_assign S S' p rv v sp : eval_rvalue S rv v S' -> eval_place S' Mut p sp ->
    ~contains_outer_loc (S'.[sp]) -> ~contains_outer_loan (S'.[sp]) ->
    eval_stmt S (ASSIGN p <- rv) rUnit (S'.[sp <- v] ++ [(Anon, S'.[sp])])
| Eval_reorg S0 S1 S2 stmt r : reorg S0 S1 -> eval_stmt S1 stmt r S2 -> eval_stmt S0 stmt r S2.

(* TODO: introduce well-formedness judgement. *)

Inductive le_state : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Le_refl S : le_state S S
| Le_trans S0 S1 S2 : le_state S0 S1 -> le_state S1 S2 -> le_state S0 S2
| Le_MutBorrow_To_Ptr S l p q v : disj p q -> S.[p] = loan^m(l) ->
    S.[q] = borrow^m(l, v) ->
    le_state (S.[p <- loc(l, v)].[q <- ptr(l)]) S.

(*
Inductive refl_trans_closure {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| Cl_base x y : R x y -> refl_trans_closure R x y
| Cl_refl x : refl_trans_closure R x x
| Cl_trans x y z : refl_trans_closure R x y -> refl_trans_closure R y z -> refl_trans_closure R x z.

Definition le_state := refl_trans_closure le_state_base.
 *)

Create HintDb sset_sget.

Ltac solve_validity :=
  apply get_not_bot_valid_spath; autorewrite with sset_sget; discriminate.

(* Try to rewrite sset_sget_equal (S.[p <- v].[p] = v if p is valid), and try to automatically
 * solve the validity hypothesis by proving that S.[p] <> bot. *)
Hint Rewrite @sset_sget_equal
  using solve_validity : sset_sget.
(* Try to rewrite sset_sget_disj (S.[p <- v].[q] = S.[q] if p and q are disjoint), provided that a
 * disjointness hypothesis is already present in the context. *)
Hint Rewrite @sset_sget_disj using assumption || symmetry; assumption : sset_sget.

(* Automating proofs of ~prefix p q. *)
(* TODO: move *)
(* TODO: automate proofs for more comparisons. *)
Lemma prefix_if_equal_or_strict_prefix p q : prefix p q -> p = q \/ strict_prefix p q.
Proof.
  intros ([ | i r] & <-).
  - left. symmetry. apply app_spath_vpath_nil_r.
  - right. exists i, r. reflexivity.
Qed.

Corollary prove_not_prefix p q : p <> q -> ~strict_prefix p q -> ~prefix p q.
Proof. intros ? ? [ | ]%prefix_if_equal_or_strict_prefix; auto. Qed.

Ltac prove_not_atom :=
  match goal with
  | H : ~strict_prefix ?p ?q |- ~strict_prefix ?p ?q => exact H
  | H : ?p <> ?q |- ?p <> ?q => exact H
  | H : ?q <> ?p |- ?p <> ?q => symmetry; exact H
  | _ => ()
  end.

Ltac reduce_not_prefix :=
  apply prove_not_prefix; try prove_not_atom.

(* Automatically proving that p <> q using the following facts:
   - S.[p] = v
   - S.[q] is of constructor c
   - v is not of constructor c
*)
Ltac constructor_neq :=
  match goal with
  | H : ?S.[?p] = ?v, G : get_constructor (?S.[?q]) = ?c |- ?p <> ?q =>
      let EQ := fresh "EQ" in
      intro EQ; rewrite EQ in H; rewrite H in G; discriminate
  end.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l0 : loan_id).
  Context (v : HLPL_plus_val).
  Context (sp_loan sp_borrow : spath).
  Context (Hdisj : disj sp_loan sp_borrow).
  Context (HS_r_loan : S_r.[sp_loan] = loan^m(l0)).
  Context (HS_r_borrow : S_r.[sp_borrow] = borrow^m(l0, v)).
  Notation S_l := (S_r.[sp_loan <- loc(l0, v)].[sp_borrow <- ptr(l0)]).
  Context (perm : permission).

  Hint Rewrite HS_r_borrow : sset_sget.
  Hint Rewrite HS_r_loan : sset_sget.

  (* comparison reasonning: *)
  Lemma sp_loan_not_prefix q :
    get_constructor (S_r.[q]) <> botC ->
    get_constructor (S_r.[q]) <> loanC^m(l0) -> ~prefix sp_loan q.
  Proof.
    intros H G ->%(get_nil_prefix_right S_r).
    - rewrite HS_r_loan in G. easy.
    - rewrite HS_r_loan. reflexivity.
    - apply get_not_bot_valid_spath. intros ?%(f_equal get_constructor). easy.
  Qed.
  Ltac solve_sp_loan_not_prefix :=
    apply sp_loan_not_prefix;
    match goal with
      | H : ?get_constr = _ |- ?get_constr <> _ => rewrite H
    end;
    discriminate.

  (* TODO: name *)
  Inductive rel : spath -> spath -> Prop :=
  | Rel_sp_borrow_strict_prefix q : rel (sp_loan +++ 0 :: q) (sp_borrow +++ 0 :: q)
  | Rel_other q : ~strict_prefix sp_borrow q -> rel q q.

  (* TODO: name *)
  Lemma get_loc_rel q l (H : get_constructor (S_r.[q]) = locC(l)) :
    exists q', rel (q' +++ [0]) (q +++ [0]) /\ get_constructor (S_l.[q']) = locC(l).
  Proof.
    destruct (decidable_prefix sp_borrow q) as [([ | i r] & <-) | sp_borrow_not_prefix].
    - rewrite app_spath_vpath_nil_r in H. rewrite HS_r_borrow in H. discriminate.
    - rewrite vset_app in H. autorewrite with sset_sget in H.
      assert (i = 0) as ->.
      { eapply (get_arity_0 (borrow^m(l0, v)) i).
        - reflexivity.
        - intros G. rewrite G in H. discriminate.
      }
      exists (sp_loan +++ 0 :: r). split. { rewrite<- !app_spath_vpath_assoc. constructor. }
      rewrite vset_app. autorewrite with sset_sget. exact H.
    - exists q. split.
      (* comparison reasonning: *)
      + apply Rel_other. intros ?%strict_prefix_app_last. auto.
      + rewrite constructor_sset_sget_not_prefix by assumption.
        rewrite constructor_sset_sget_not_prefix by solve_sp_loan_not_prefix.
        assumption.
  Qed.

  Lemma eval_proj_mut_sp_borrow_strict_prefix proj r q
    (H : eval_proj S_r perm proj (sp_borrow +++ 0 :: r) q) :
    exists q', rel q' q /\ eval_proj S_l perm proj (sp_loan +++ 0 :: r) q'.
  Proof.
    remember (sp_borrow +++ 0 :: r) as p. revert r Heqp. induction H; intros r ->.
    - exists ((sp_loan +++ 0 :: r) +++ [0]). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + apply Eval_Deref_MutBorrow with (l := l); try assumption.
        rewrite vset_app in *. autorewrite with sset_sget in *. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try assumption.
      rewrite vset_app in *. autorewrite with sset_sget in *. assumption.
    - specialize (IHeval_proj (r ++ [0])). destruct IHeval_proj as (q'' & ? & ?).
      + rewrite<- app_spath_vpath_assoc. reflexivity.
      + exists q''. split; try assumption.
        apply Eval_Loc with (l := l).
        * assumption.
        * rewrite vset_app in *. autorewrite with sset_sget in *. assumption.
        * rewrite<- app_spath_vpath_assoc. assumption.
  Qed.

  Lemma eval_proj_mut_not_prefix_sp_borrow proj q r
    (not_prefix : ~strict_prefix sp_borrow q) (H : eval_proj S_r perm proj q r) :
    exists r', rel r' r /\ eval_proj S_l perm proj q r'.
  Proof.
    induction H.
    - destruct (decidable_spath_eq q sp_borrow) as [-> | ].
      + exists (sp_loan +++ [0]). split. { constructor. }
        apply Eval_Deref_Ptr_Locs with (l := l0); autorewrite with sset_sget; easy.
      + exists (q +++ [0]). split.
        { apply Rel_other. enough (~prefix sp_borrow q) by (intros K%strict_prefix_app_last; easy). reduce_not_prefix. }
        apply Eval_Deref_MutBorrow with (l := l); try assumption.
        rewrite constructor_sset_sget_not_prefix by reduce_not_prefix.
        rewrite constructor_sset_sget_not_prefix by solve_sp_loan_not_prefix.
        assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try auto.
      rewrite constructor_sset_sget_not_prefix by (reduce_not_prefix; constructor_neq).
      rewrite constructor_sset_sget_not_prefix by solve_sp_loan_not_prefix.
      assumption.
    - destruct IHeval_proj as (r' & ? & ?).
      { intros G%strict_prefix_app_last; revert G. reduce_not_prefix. constructor_neq. }
      exists r'. split; try assumption. apply Eval_Loc with (l := l); try easy.
      rewrite constructor_sset_sget_not_prefix by (reduce_not_prefix; constructor_neq).
      rewrite constructor_sset_sget_not_prefix by solve_sp_loan_not_prefix.
      assumption.
  Qed.

  Lemma eval_proj_mut_borrow_to_ptr proj q_l q_r q'_r :
    rel q_l q_r -> eval_proj S_r perm proj q_r q'_r ->
    exists q'_l, rel q'_l q'_r /\ eval_proj S_l perm proj q_l q'_l.
  Proof.
    intros [ r | q G] H.
    - apply eval_proj_mut_sp_borrow_strict_prefix. assumption.
    - apply eval_proj_mut_not_prefix_sp_borrow; assumption.
  Qed.

  Corollary eval_path_mut_borrow_to_ptr P q_r q'_r :
    eval_path S_r perm P q_r q'_r -> forall q_l, rel q_l q_r ->
    exists q'_l, rel q'_l q'_r /\ eval_path S_l perm P q_l q'_l.
  Proof.
    intros H. induction H.
    - eexists. split. eassumption. constructor.
    - intros q_l ?. apply eval_proj_mut_borrow_to_ptr with (q_l := q_l) in H; try assumption.
      destruct H as (q'_l & rel_q'_l & ?).
      destruct (IHeval_path q'_l rel_q'_l) as (q''_l & ? & ?).
      exists q''_l. split. { assumption. }
      apply Eval_cons with (q := q'_l); assumption.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr p pi_r :
    eval_place S_r perm p pi_r ->
    exists pi_l, rel pi_l pi_r /\ eval_place S_l perm p pi_l.
  Proof.
    intros (i & ? & H). apply eval_path_mut_borrow_to_ptr with (q_l := (i, [])) in H.
    - destruct H as (q'_l & rel & ?). exists q'_l. split. { assumption. }
      exists i. split. { (* Doing ssets don't change the indexes *) admit. }
      assumption.
    - apply Rel_other. apply not_strict_prefix_nil.
  Admitted.
End MutBorrow_to_Ptr.
