Require Import base.
Require Import PathToSubtree.
Require Import lang.
Require Import List.
Require Import PeanoNat.
Import ListNotations.
Require Import OptionMonad.
Local Open Scope option_monad_scope.
Require Import SimulationUtils.

(* TODO: move this in a separate file. *)
Create HintDb spath.

(* Automatically solving a comparison C p q using the hypotheses. *)
Hint Resolve-> disj_common_prefix : spath.

(* TODO: move in PathToSubtree.v *)
Lemma disj_common_index i p q : disj (i, p) (i, q) <-> vdisj p q.
Proof.
  split.
  - intros [H | (_ & ?)].
    + cbn in H. congruence.
    + assumption.
  - intro. right. auto.
Qed.
Hint Resolve<- disj_common_index : spath.

Hint Immediate vstrict_prefix_is_vprefix : spath.
Hint Immediate not_vprefix_left_vstrict_prefix_right : spath.
Hint Resolve strict_prefix_irrefl : spath.
Lemma not_disj_strict_prefix p q : disj p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. eapply not_prefix_disj; eassumption. Qed.
Hint Resolve not_disj_strict_prefix : spath.
Hint Immediate symmetric_disj : spath.

Lemma not_prefix_implies_not_strict_prefix p q : ~prefix p q -> ~strict_prefix p q.
Proof. intros ? ?%strict_prefix_is_prefix. auto. Qed.
Hint Resolve not_prefix_implies_not_strict_prefix : spath.

Lemma not_vprefix_implies_not_vstrict_prefix p q : ~vprefix p q -> ~vstrict_prefix p q.
Proof. intros ? ?%vstrict_prefix_is_vprefix. auto. Qed.
Hint Immediate not_vprefix_implies_not_vstrict_prefix : spath.

Lemma neq_implies_not_prefix p q : ~prefix p q -> p <> q.
Proof. intros H <-. apply H. reflexivity. Qed.
Lemma neq_implies_not_prefix' p q : ~prefix p q -> q <> p.
Proof. intro. symmetry. apply neq_implies_not_prefix. assumption. Qed.
Hint Resolve neq_implies_not_prefix : spath.
Hint Resolve neq_implies_not_prefix' : spath.

Lemma disj_if_left_disj_prefix p q r : disj p q -> disj p (q +++ r).
Proof.
  intros [ | (? & (x & p' & q' & H))].
  - left. assumption.
  - right. split; [assumption | ]. exists x, p', (q' ++ r).
    decompose [ex and] H. repeat eexists; try eassumption. cbn.
    rewrite app_comm_cons, app_assoc. apply<- app_inv_tail_iff. assumption.
Qed.
Hint Resolve disj_if_left_disj_prefix : spath.

Corollary disj_if_right_disj_prefix p q r : disj p q -> disj (p +++ r) q.
Proof. intro. symmetry. apply disj_if_left_disj_prefix. symmetry. assumption. Qed.
Hint Resolve disj_if_right_disj_prefix : spath.

Hint Resolve<- strict_prefix_app_last : spath.

Hint Resolve not_strict_prefix_nil : spath.

Lemma not_prefix_left_strict_prefix_right' p q : prefix p q -> ~strict_prefix q p.
Proof. intros ? ?. eapply not_prefix_left_strict_prefix_right; eassumption. Qed.
Hint Resolve not_prefix_left_strict_prefix_right' : spath.

Hint Extern 0 (prefix ?p (?p +++ ?q)) => exists q; reflexivity : spath.
Hint Extern 0 (prefix (?p +++ ?q) (?p +++ ?q ++ ?r)) =>
    exists r; symmetry; apply app_spath_vpath_assoc : spath.

Lemma prefix_trans p q r : prefix (p +++ q) r -> prefix p r.
Proof. intros (z & <-). rewrite<- app_spath_vpath_assoc. auto with spath. Qed.
Hint Resolve prefix_trans : spath.

Lemma prefix_and_neq_implies_strict_prefix p q : prefix p q -> p <> q -> strict_prefix p q.
Proof.
  intros ([ | ] & <-) H.
  - rewrite app_spath_vpath_nil_r in H. easy.
  - eexists _, _. reflexivity.
Qed.
Hint Resolve prefix_and_neq_implies_strict_prefix : spath.

Lemma not_strict_prefix_app_last p q i : ~strict_prefix p (q +++ [i]) <-> ~prefix p q.
Proof. split; intros H ?; eapply H, strict_prefix_app_last; eassumption. Qed.
Hint Resolve<- not_strict_prefix_app_last : spath.

(* TODO: move in PathToSubtree.v *)
(* TODO: counterpart of get_nil_prefix_right' *)
Lemma vstrict_prefix_one_subvalue {V} `{IsValue : Value V} v p q
  (H : length (subvalues (v.[[p]])) = 1) :
  vstrict_prefix p q -> valid_vpath v q -> vprefix (p ++ [0]) q.
Proof.
  intros (i & r & <-) (_ & G)%valid_vpath_app.
  assert (i = 0) as ->.
  { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
    inversion G. destruct (nth_error (subvalues (v.[[p]]))); easy. }
  exists r. rewrite<- app_assoc. reflexivity.
Qed.

Lemma strict_prefix_one_subvalue {B V} `{IsValue : Value V} (S : state B V) p q (H : length (subvalues (S.[p])) = 1) :
  strict_prefix p q -> valid_spath S q -> prefix (p +++ [0]) q.
Proof.
  intros (i & r & <-) (_ & G)%valid_spath_app.
  assert (i = 0) as ->.
  { apply PeanoNat.Nat.lt_1_r. rewrite<- H. apply nth_error_Some.
    inversion G. destruct (nth_error (subvalues (S.[p]))); easy. }
  exists r. rewrite<- app_spath_vpath_assoc. reflexivity.
Qed.

Corollary not_vprefix_one_subvalue {V} `{IsValue : Value V} v p q :
  length (subvalues (v.[[p]])) = 1 -> valid_vpath v q -> ~vprefix (p ++ [0]) q -> ~vstrict_prefix p q.
Proof. intros ? ? H ?. eapply H, vstrict_prefix_one_subvalue; eassumption. Qed.

Corollary not_prefix_one_subvalue {B V} `{IsValue : Value V} (S : state B V) p q :
  length (subvalues (S.[p])) = 1 -> valid_spath S q -> ~prefix (p +++ [0]) q -> ~strict_prefix p q.
Proof. intros ? ? H ?. eapply H, strict_prefix_one_subvalue; eassumption. Qed.

Hint Resolve strict_prefix_one_subvalue : spath.
Hint Resolve not_vprefix_one_subvalue : spath.
Hint Resolve not_prefix_one_subvalue : spath. (* TODO: delete? *)
Hint Extern 5 (length (subvalues ?v) = _) =>
  match goal with
  | H : get_constructor (?S.[?p]) = _ |- _ =>
      rewrite length_subvalues_is_arity, H; reflexivity
  end : spath.

(* Try to automatically solve a validity goal validity S pi. Here is how the procedure should
 * work:
 * - If the state S is of the form S'.[q <- v], reduce to valid S' pi provided that
     ~strict_prefix q pi.
 * - If the state S is of the form S,, b |-> v
 *   - If pi = (length S, q), meaning that pi refers to the last binding, reduce to valid v q
 *   - Otherwise, reduce to valid S pi
 * - Search the proof that pi is the evaluation of a place.
 * - Search for a proof that S.[p] <> bot in the hypotheses.
 * - Search for a proof that the constructor of S.[p] is not bot in the hypotheses.
 *)
Lemma valid_get_constructor_sget_not_bot {B V} `{IsValue : Value V} (S : state B V) p :
  get_constructor (S.[p]) <> get_constructor bot -> valid_spath S p.
Proof. intros G. apply get_not_bot_valid_spath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_get_constructor_vget_not_bot {V} `{IsValue : Value V} v p :
  get_constructor (v.[[p]]) <> get_constructor bot -> valid_vpath v p.
Proof. intros G. apply get_not_bot_valid_vpath. intro K. apply G. rewrite K. reflexivity. Qed.

Lemma valid_vpath_app_last_get_constructor_not_zeoray {V} `{IsValue : Value V} v p :
  arity (get_constructor (v.[[p]])) > 0 -> valid_vpath v (p ++ [0]).
Proof.
  intro. apply valid_vpath_app. split.
  - apply get_not_bot_valid_vpath. intro G. rewrite G in H.
    rewrite <-length_subvalues_is_arity, subvalues_bot in H. inversion H.
  - rewrite<- length_subvalues_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

Lemma valid_spath_app_last_get_constructor_not_zeoray {B V} `{IsValue : Value V} (S : state B V) p :
  arity (get_constructor (S.[p])) > 0 -> valid_spath S (p +++ [0]).
Proof.
  intro. apply valid_spath_app. split.
  - apply get_not_bot_valid_spath. intro G. rewrite G in H.
    rewrite <-length_subvalues_is_arity, subvalues_bot in H. inversion H.
  - rewrite<- length_subvalues_is_arity in H. apply nth_error_Some' in H.
    destruct H. econstructor; [eassumption | constructor].
Qed.

(* Automatically solve equality between two states that are sets of a state S, ie solves goals of
 * the form:
 * S.[p0 <- v0] ... .[pm <- vm] = S.[q0 <- w0] ... .[qn <- vn]
 *
 * Strategy: it's easy to compute values that are a get of a sequence of sets, i.e:
 * S.[p0 <- v0] ... .[pm <- vm] .[q]
 * This works when we know the relation between the state q we get and the states p0, ..., pk we
 * set.
 * Let's denote Sl := S.[p0 <- v0] ... .[pm <- vm] and Sr := S.[q0 <- w0] ... .[qn <- vn]. To prove
 * that Sl = Sr, we are going to prove that Sl.[q] = Sr.[q] for q = p0, ..., pm. For the spaths q
 * that are not prefix of p0, ..., pm, we are going to prove that Sl.[q] and Sr.[q] have the same
 * constructor.
 * Finally, we also need to prove that Sl and Sr have the binders, which is an easy consequence of
 * the fact that they are sets of the same state S.
 *)
Lemma prove_states_eq_3 {B V} `{IsValue : Value V} (S S' : state B V) p0 p1 p2 :
  (forall i, SOME c <- nth_error S i IN Some (fst c) = SOME c <- nth_error S' i IN Some (fst c)) ->
  S.[p0] = S'.[p0] -> (S.[p1] = S'.[p1]) -> (S.[p2] = S'.[p2]) ->
  (forall q, ~prefix p0 q -> ~prefix p1 q -> ~prefix p2 q ->
    get_constructor (S.[q]) = get_constructor (S'.[q])) ->
  S = S'.
Proof.
  intros. apply get_constructor_sget_ext; [assumption | ].
  intro q.
  destruct (decidable_prefix p0 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
  destruct (decidable_prefix p1 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
  destruct (decidable_prefix p2 q) as [(? & <-) | ];
   [rewrite !sget_app; congruence | ].
   auto.
Qed.

Ltac prove_states_eq :=
  let q := fresh "q" in
  (* autorewrite with spath; *)
  lazymatch goal with
  | |- ?S.[?p0 <- _].[?p1 <- _].[?p2 <- _] = ?S' =>
    simple apply (prove_states_eq_3 _ S' p0 p1 p2);
    intros;
    [rewrite !get_binder_sset; reflexivity | autorewrite with spath; try reflexivity..]
  | |- ?S.[?p0 <- _].[?p1 <- _] = _ =>
        apply get_constructor_sget_ext; [intro; rewrite !get_binder_sset; reflexivity | ];
        intro q;
        destruct (decidable_prefix p0 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        destruct (decidable_prefix p1 q) as [(? & <-) | ];
          [rewrite !sget_app; autorewrite with spath; reflexivity | ];
        autorewrite with spath; reflexivity
  end.

(* A _comparison_ `C p q` between is one of those relation:
   - `p = q` or `p <> q`
   - `prefix p q` or `~prefix p q`
   - `strict_prefix p q` or `~strict_prefix p q`
   - `disj p q` or `~disj p q`
 *)
(* We are going to define a tactic called "reduce_comp" to assist the proof of comparisons between
 * two paths p and q, using comparisons in the hypotheses as much as possible.
 *
 * The key idea is that there are four possible "atomic" comparisons: p = q, strict_prefix p q,
 * strict_prefix q p and disj p q. These comparisons are atomic in the sense that for any p and q,
 * exactly one of those is true.
 *
 * Every comparison C p q is equivalent to a disjunction of atomic comparisons. By contraposition,
 * this means that every comparison C p q is equivalent to the conjuction of the negation of
 * atomas. For example:
 * - prefix p q <-> (p = q \/ strict_prefix p q) <-> (~strict_prefix q p /\ ~disj p q)
 * - ~prefix p q <-> (strict_prefix q p \/ ~disj p q) <-> (p <> q /\ ~strict_prefix p q)
 * - disj p q <-> disj p q <-> (p <> q /\ ~strict_prefix p q /\ ~strict_prefix q p)
 *
 * Thus, to prove a comparison C p q in the goal, reduce_comp works the following way:
 * - It generates the negative atomic relations necessary to prove C p q
 * - For each negative atomic relation, it tries to prove it automatically using the hypotheses.
 * The negative atomic relations that could not be automatically proven are left as subgoals. This
 * tactic never fails (as long as the goal is a comparison).
 *
 * Note: this tactic is not complete yet, more comparisons have to be added. It's also subject to
 * change.
 *)

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
Hint Resolve prove_not_prefix : spath.

Lemma prove_disj p q : p <> q -> ~strict_prefix p q -> ~strict_prefix q p -> disj p q.
Proof. destruct (comparable_spaths p q); easy. Qed.

Lemma get_nil_prefix_right'  {V : Type} {IsValue : Value V} {B : Type} (S : state B V)
  (p q : spath) :
subvalues (S .[ p]) = [] -> valid_spath S q -> ~strict_prefix p q.
Proof.
  intros H G K. assert (q = p) as ->.
  { eapply get_nil_prefix_right; try eassumption. apply strict_prefix_is_prefix. assumption. }
  eapply strict_prefix_irrefl. eassumption.
Qed.

Ltac reduce_comp :=
  unfold not; (* Used to prove both negations of the form ~C p q and C p q -> False *)
  match goal with
  | |- prefix ?p ?q -> False => apply prove_not_prefix
  | |- disj ?p ?q => apply prove_disj
  end;
  eauto with spath.

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

Fixpoint HLPL_plus_height v := match v with
| HLPL_plus_bot => 0
| HLPL_plus_int _ => 0
| HLPL_plus_mut_loan _ => 0
| HLPL_plus_mut_borrow _ v => 1 + HLPL_plus_height v
| HLPL_plus_loc _ v =>  1 + HLPL_plus_height v
| HLPL_plus_ptr _ => 0
end.

Program Instance ValueHLPL : Value HLPL_plus_val := {
  constructors := HLPL_plus_constructor;
  arity := HLPL_plus_arity;
  get_constructor := HLPL_plus_get_constructor;
  subvalues := HLPL_plus_subvalues;
  fold_value := HLPL_plus_fold;
  height := HLPL_plus_height;
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
Next Obligation.
  apply nth_error_In in H.
  destruct v; cbn in *; try destruct H as [-> | ]; try contradiction; constructor.
Qed.

Definition HLPL_plus_state := state HLPL_plus_binder HLPL_plus_val.

Declare Scope hlpl_plus_scope.
Delimit Scope hlpl_plus_scope with hlpl_plus.

(* TODO: move in lang.v *)
(* TODO: set every priority to 0? *)
(* Reserved Notation "'bot'" (at level 0). *)
Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'ptr' ( l )" (at level 0).

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level).
Reserved Notation "'ptrC' ( l )" (at level 0).

(* Notation "'bot'" := HLPL_plus_bot: hlpl_plus_scope. *)
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
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Notation eval_place S perm p r :=
  (exists i, find_binder S (Var (fst p)) = Some i /\ eval_path S perm (snd p) (i, []) r).

(* TODO: replace the notation by a definition, with Hint Unfold. *)
Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

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


Ltac solve_validity0 :=
  lazymatch goal with
  | H : ?S |-{p} _ =>^{ _ } ?pi |- valid_spath ?S ?pi =>
      simple eapply eval_place_valid;
      exact H
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S ?p =>
      apply (valid_get_constructor_sget_not_bot S p);
      rewrite H;
      discriminate
  | H : get_constructor (?S.[?p]) = _ |- valid_spath ?S (?p +++ [0]) =>
      simple apply valid_spath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : get_constructor (?S.[?p +++ ?q]) = _ |- valid_spath ?S (?p +++ ?q ++ [0]) =>
      rewrite (app_spath_vpath_assoc p q [0]);
      simple apply valid_spath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : ?S.[?p] = ?v |- valid_spath ?S ?p =>
      simple apply get_not_bot_valid_spath;
      rewrite H;
      discriminate
  | |- valid_spath (?S.[?p <- ?v]) (?p +++ ?q) =>
      simple apply sset_prefix_valid;
      solve_validity0
  | |- valid_spath (?S.[?p <- ?v]) ?q =>
      apply sset_not_prefix_valid; [ | solve_validity0]
  | |- valid_spath (?S ++ _) (length ?S, ?q) =>
      apply valid_spath_last;
      solve_validity0
  | |- valid_spath (?S ++ ?S') ?p =>
      simple apply valid_app_spath;
      solve_validity0
  (* Solving valid_vpath: *)
  | |- valid_vpath (?S.[?p]) ?q =>
      apply (valid_spath_app S p q);
      (* In case p is of the form p0 +++ p1, we rewrite (p0 +++ p1) +++ q into
         p0 +++ (p1 ++ q) *)
      repeat rewrite<-app_spath_vpath_assoc;
      solve_validity0
  | |- valid_vpath _ ([_] ++ _) =>
      econstructor; [reflexivity | solve_validity0]
  | H : get_constructor (?v.[[?p]]) = _ |- valid_vpath ?v (?p ++ [0]) =>
      simple apply valid_vpath_app_last_get_constructor_not_zeoray;
      rewrite H;
      constructor
  | H : ?v.[[?p]] = _ |- valid_vpath ?v ?p =>
      apply (valid_get_constructor_vget_not_bot v p);
      rewrite H;
      discriminate
  | H : get_constructor (?v.[[?p]]) = _ |- valid_vpath ?v ?p =>
      apply (valid_get_constructor_vget_not_bot v p);
      rewrite H;
      discriminate
  | |- valid_spath ?S ?p => idtac
  | |- valid_vpath ?v ?p => idtac
  end.
Hint Extern 0 (valid_spath _ _) => solve_validity0 : spath.
Print HintDb spath.
Ltac solve_validity := solve_validity0; eauto with spath.

(* Testing that I can automatically prove validity: *)
Goal forall (S : HLPL_plus_state) p l, S.[p] = ptr(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) p l, get_constructor (S.[p]) = locC(l) -> valid_spath S p.
Proof. intros. solve_validity. Qed.

Goal forall (S : HLPL_plus_state) v w p q r l, disj p r -> ~strict_prefix q r -> S.[r] = loan^m(l)
  -> valid_spath (S.[p <- v].[q <- w]) r.
Proof. intros. solve_validity. Qed.

(* TODO: rework this hint. *)
Hint Extern 5 (~strict_prefix ?p ?q) =>
  match goal with
  | H : ?S.[?p] = _ |- _ =>
      simple apply (get_nil_prefix_right' S); [rewrite H | ]
  end : spath.
(* TODO: replace by eauto with spath? *)
Ltac prove_not_atom :=
  match goal with
  (* Trying to automatically prove p <> q *)
  | H : ?p <> ?q |- ?p <> ?q => exact H
  | H : ?q <> ?p |- ?p <> ?q => symmetry; exact H
  | H : ~prefix ?p ?q |- ?p <> ?q => intros ->; apply H; reflexivity
  | H : ?S.[?p] = ?v, G : get_constructor (?S.[?q]) = ?c |- ?p <> ?q =>
      let EQ := fresh "EQ" in
      intro EQ;
      rewrite EQ in H;
      rewrite H in G;
      discriminate

  (* Trying to automatically prove ~strict_prefix p q *)
  | H : ~strict_prefix ?p ?q |- ~strict_prefix ?p ?q => exact H
  | H : ~prefix ?p ?q |- ~strict_prefix ?p ?q => intro; apply H, strict_prefix_is_prefix; assumption
  (* When we have a hypotheses H : S.[p] = v with v a 0-ary value (for example, v = loan^m(l)),
     we try to prove that p cannot be a strict prefix of q by using the validity of q: *)
  | H : ?S.[?p] = ?v |- ~strict_prefix ?p ?q =>
      let G := fresh "G" in
      (* Trying to automatically prove that p has no subvalues, this branch fails if we can't. *)
      assert (G : subvalues (S.[p]) = []) by (rewrite H; reflexivity);
      apply (get_nil_prefix_right' S p q G);
      solve_validity
  | _ => idtac
  end.


Hint Extern 2 (disj ?p (length ?S, ?q)) =>
  simple apply (disj_spath_to_last S); [solve_validity | ] : spath.
Hint Extern 2 (disj (length ?S, ?q) ?p) =>
  symmetry; simple apply (disj_spath_to_last S); [solve_validity | ] : spath.

(* TODO: document automatic rewriting. *)
(* TODO: move in PathToSubtree.v *)
Lemma sset_sget_remove_prefix (S : HLPL_plus_state) p q r v :
  valid_spath S p -> S.[p +++ q <- v].[p +++ r] = S.[p].[[q <- v]].[[r]].
intro. rewrite sget_app. rewrite sset_sget_prefix by assumption. reflexivity. Qed.
Hint Rewrite sset_sget_remove_prefix using solve_validity : spath.
(* Try to rewrite sset_sget_equal (S.[p <- v].[p] = v if p is valid), and try to automatically
 * solve the validity hypothesis by proving that S.[p] <> bot. *)
Hint Rewrite @sset_sget_equal using solve_validity : spath.
Hint Rewrite @sset_sget_prefix using solve_validity : spath.
(* Try to rewrite sset_sget_disj (S.[p <- v].[q] = S.[q] if p and q are disjoint), only if it can
 * automatically prove it. *)
Hint Rewrite @sset_sget_disj using eauto with spath; fail : spath.
Hint Rewrite @sset_sget_prefix_right using solve_validity : spath.
Hint Rewrite @sset_twice_prefix_right : spath.
Hint Rewrite<- @sset_app_state using solve_validity; fail : spath.
Hint Rewrite<- @sset_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite @sget_app_state using solve_validity; fail : spath.
Hint Rewrite @sget_app_last_state
  using repeat rewrite length_sset; try assumption; reflexivity : spath.
Hint Rewrite @constructor_sset_sget_not_prefix using eauto with spath; fail : spath.
Hint Rewrite <- @sget_app : spath.
Hint Rewrite <- @vget_app : spath.
Hint Rewrite <- app_assoc : spath.
Hint Rewrite <- app_spath_vpath_assoc : spath.
Hint Rewrite vget_vset_prefix using solve_validity : spath.
Hint Rewrite vget_vset_prefix_right using solve_validity : spath.
Hint Rewrite vget_vset_equal using solve_validity : spath.

Lemma constructor_vset_not_nil (v w : HLPL_plus_val) p :
  p <> [] -> get_constructor (v.[[p <- w]]) = get_constructor v.
Proof. intro. destruct p; [easy | apply constructor_vset_cons]. Qed.
(* Using discriminate to prove that p is not []. *)
Hint Rewrite constructor_vset_not_nil using discriminate : spath.

Lemma sget_loc l v p : (loc(l, v)).[[ [0] ++  p]] = v.[[p]].
Proof. reflexivity. Qed.
Hint Rewrite sget_loc : spath.
Lemma sget_loc' l v : (loc(l, v)).[[ [0] ]] = v.
Proof. reflexivity. Qed.
Hint Rewrite sget_loc' : spath.

Hint Rewrite app_nil_r : spath.

Lemma snd_pair [A B] (a : A) (b : B) : snd (a, b) = b. Proof. reflexivity. Qed.
Hint Rewrite snd_pair : spath.
Lemma snd_app v w : snd (v +++ w) = (snd v) ++ w. Proof. reflexivity. Qed.
Hint Rewrite snd_app : spath.

(* Setting up the definitions for judgements like "loan \notin v" or
   "l is fresh". *)
Definition not_state_contains (P : HLPL_plus_constructor -> Prop) (S : HLPL_plus_state) :=
  forall p, valid_spath S p -> ~P (get_constructor (S.[p])).

(* TODO: move *)
Definition not_value_contains (P : HLPL_plus_constructor -> Prop) (v : HLPL_plus_val) :=
  forall p, valid_vpath v p -> ~P (get_constructor (v.[[p]])).

Lemma not_value_contains_not_prefix P (S : HLPL_plus_state) p q
  (Hnot_contains : not_value_contains P (S.[p])) (HP : P (get_constructor (S.[q]))) (Hvalid : valid_spath S q) :
  ~prefix p q.
Proof.
  intros (r & <-). apply valid_spath_app in Hvalid. apply Hnot_contains with (p := r); [easy | ].
  rewrite<- sget_app. assumption.
Qed.

Lemma not_value_contains_vset P v w p : not_value_contains P v -> not_value_contains P w ->
  not_value_contains P (v.[[p <- w]]).
Proof.
  intros H G q valid_q. destruct (decidable_vprefix p q) as [(? & <-) | ].
  - apply valid_vpath_app in valid_q. destruct valid_q as (?%vset_same_valid_rev & validity_w).
    rewrite vget_vset_equal in validity_w by assumption.
    rewrite vget_vset_prefix_right by assumption. apply G. assumption.
  - rewrite constructor_vset_vget_not_prefix by assumption. apply H.
    eapply vset_not_prefix_valid_rev; [ | eassumption].
    intros ?%vstrict_prefix_is_vprefix. auto.
Qed.
Hint Resolve not_value_contains_vset : spath.

Lemma not_state_contains_sset P (S : HLPL_plus_state) v p
  (not_in_S : not_state_contains P S)
  (not_in_v : not_value_contains P v) :
  not_state_contains P (S.[p <- v]).
Proof.
  intros q valid_q.
  destruct (decidable_prefix p q) as [(r & <-) | ].
  - apply valid_spath_app in valid_q.
    destruct valid_q as (?%sset_not_prefix_valid & H); [ |  apply strict_prefix_irrefl].
    rewrite sset_sget_equal in H by assumption.
    rewrite sset_sget_prefix_right by assumption. apply not_in_v. assumption.
  - rewrite constructor_sset_sget_not_prefix by assumption.
    apply not_in_S. eapply sset_not_prefix_valid; [ | exact valid_q]. auto with spath.
Qed.
Hint Resolve not_state_contains_sset : spath.

Lemma not_value_contains_sset P (S : HLPL_plus_state) v p q
  (not_in_Sp : not_value_contains P (S.[p]))
  (not_in_v : not_value_contains P v)
  (valid_p : valid_spath (S.[q <- v]) p) :
  not_value_contains P (S.[q <- v].[p]).
Proof.
  intros r valid_r. rewrite<- sget_app.
  assert (valid_pr : valid_spath (S.[q <- v]) (p +++ r)).
  { apply valid_spath_app. split; assumption. }
  destruct (decidable_prefix q (p +++ r)) as [(? & eq) | ].
  - rewrite <-eq in *. rewrite valid_spath_app in valid_pr.
    destruct valid_pr as (valid_q & valid_v_r).
    apply sset_not_prefix_valid in valid_q; [ | apply strict_prefix_irrefl].
    rewrite sset_sget_equal in valid_v_r by assumption.
    rewrite sset_sget_prefix_right by assumption. apply not_in_v. exact valid_v_r.
  - rewrite constructor_sset_sget_not_prefix by assumption. rewrite sget_app. apply not_in_Sp.
    apply sset_not_prefix_valid in valid_pr; [ | auto with spath].
    apply valid_spath_app in valid_pr as (_ & ?). assumption.
Qed.

Lemma not_value_contains_sset_disj P (S : HLPL_plus_state) v p q
  (Hdisj : disj q p)
  (not_in_Sp : not_value_contains P (S.[p])) :
  not_value_contains P (S.[q <- v].[p]).
Proof.
  intros r valid_r. rewrite<- sget_app. rewrite sset_sget_disj by auto with spath.
  rewrite sget_app. apply not_in_Sp.
  rewrite sset_sget_disj in valid_r; assumption.
Qed.

Lemma not_value_contains_zeroary P v :
  subvalues v = [] -> ~P (get_constructor v) -> not_value_contains P v.
Proof.
  intros H ? p valid_p. destruct valid_p; [assumption | ].
  rewrite H, nth_error_nil in * |-. discriminate.
Qed.

Lemma not_value_contains_unary P v w :
  subvalues v = [w] -> ~P (get_constructor v) -> not_value_contains P w -> not_value_contains P v.
Proof.
  intros H ? ? p valid_p. destruct valid_p; [assumption | ].
  rewrite H, nth_error_cons in * |-. destruct i; [ | rewrite nth_error_nil in * |-; discriminate].
  rewrite vget_cons, H. simplify_option.
Qed.

Variant is_loan : HLPL_plus_constructor -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Hint Constructors is_loan : spath.
Notation not_contains_loan := (not_value_contains is_loan).
Hint Extern 0 (~is_loan _) => intro; easy : spath.

(* TODO: delete *)
Goal is_loan (get_constructor (loan^m(0))).
Proof. cbn. auto with spath. Qed.

Variant is_loc : HLPL_plus_constructor -> Prop :=
| IsLoc_Loc l : is_loc (locC(l)).
Notation not_contains_loc := (not_value_contains is_loc).
Hint Extern 0 (~is_loc _) => intro; easy : spath.

(*
Variant is_mut_borrow : HLPL_plus_constructor -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
 *)
(* Hint Constructors is_mut_borrow : spath. *)

Definition not_contains_outer (P : HLPL_plus_constructor -> Prop) v :=
  forall p, P (get_constructor (v.[[p]]))
  -> exists q l, vstrict_prefix q p /\ get_constructor (v.[[q]]) = borrowC^m(l).
Notation not_contains_outer_loan := (not_contains_outer is_loan).
Notation not_contains_outer_loc := (not_contains_outer is_loc).

Lemma not_contains_outer_sset_no_contains P v p w :
  not_contains_outer P v -> not_value_contains P w
  -> (forall v, P v -> v <> botC)
  -> not_contains_outer P (v.[[p <- w]]).
Proof.
  intros Hv Hw ?. destruct (valid_or_invalid p v).
  - intros q Hq. destruct (decidable_vprefix p q) as [(r & <-) | not_prefix].
    + exfalso.
      autorewrite with spath in * |-. eapply Hw; [ | eassumption].
      apply get_not_bot_valid_vpath. intro wr. apply (H _ Hq). rewrite wr. reflexivity.
    + destruct (Hv q) as (r & l & ? & ?).
      * rewrite constructor_vset_vget_not_prefix in Hq; assumption.
      * exists r, l. split; [assumption | ]. rewrite constructor_vset_vget_not_prefix.
        assumption. intro. apply not_prefix. transitivity r; auto with spath.
  - rewrite vset_invalid by assumption. assumption.
Qed.

Lemma not_contains_outer_sset_in_borrow P (v : HLPL_plus_val) p w :
  not_contains_outer P v
  -> (exists q l, vstrict_prefix q p /\ get_constructor (v.[[q]]) = borrowC^m(l))
  -> not_contains_outer P (v.[[p <- w]]).
Proof.
  intros Hv (q & l & H & ?). destruct (valid_or_invalid p v).
  - intros r Hr. destruct (decidable_vprefix p r) as [(r' & <-) | not_prefix].
    + exists q, l.
      split.
      * destruct H as (i & ? & <-). eexists i, _. rewrite<- app_assoc. reflexivity.
      * rewrite constructor_vset_vget_not_prefix by auto with spath. assumption.
    + destruct (Hv r) as (q' & l' & ? & ?).
      * rewrite constructor_vset_vget_not_prefix in Hr; assumption.
      * exists q', l'. split; [assumption | ]. rewrite constructor_vset_vget_not_prefix.
        assumption. intro. apply not_prefix. transitivity q'; auto with spath.
  - rewrite vset_invalid by assumption. assumption.
Qed.

Lemma loc_is_not_bot x : is_loc x -> x <> botC. Proof. intros [ ]; discriminate. Qed.
Lemma loan_is_not_bot x : is_loan x -> x <> botC. Proof. intros [ ]; discriminate. Qed.
Ltac prove_not_contains_outer :=
  (* The values we use this tactic on are of the form
     (S,, Anon |-> v) (.[ sp <- v])* .[sp]
     where the path sp we read is a path of S. We first do some rewritings to commute
     the read with the writes and the addition of the anonymous value. *)
  autorewrite with spath;
  try assumption;
  match goal with
  | |- not_contains_outer ?P (?v.[[?p <- ?w]]) =>
      let H := fresh "H" in
      assert (H : not_value_contains P w) by auto with spath;
      apply not_contains_outer_sset_no_contains;
        [prove_not_contains_outer | exact H | exact loc_is_not_bot || exact loan_is_not_bot]
  | no_outer_loan : not_contains_outer_loan (?S.[?q]),
    loan_at_q : ?S.[?q +++ ?p] = loan^m(?l)
    |- not_contains_outer ?P (?S.[?q].[[?p <- ?w]]) =>
    apply not_contains_outer_sset_in_borrow;
     [ prove_not_contains_outer |
       apply no_outer_loan; rewrite<- (sget_app S q p), loan_at_q; constructor ]
  | |- not_contains_outer _ _ =>
      idtac
  end.


Definition get_loan_id c :=
  match c with
  | loanC^m(l) => Some l
  | borrowC^m(l) => Some l
  | locC(l) => Some l
  | ptrC(l) => Some l
  | _ => None
  end.

(* Hint Constructors is_loan_id : spath. *)
Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).

Lemma is_fresh_loan_id_neq S l0 l1 p :
  get_loan_id (get_constructor (S.[p])) = Some l0 -> is_fresh l1 S -> l0 <> l1.
Proof.
  intros get_p Hfresh <-. eapply Hfresh; [ | exact get_p].
  apply get_not_bot_valid_spath. intro H. rewrite H in get_p. inversion get_p.
Qed.

Hint Extern 0 (get_loan_id _ <> Some ?l) =>
  lazymatch goal with
  | Hfresh : is_fresh ?l ?S, get_p : get_constructor (?S.[?p]) = ?v |- _ =>
      injection;
      refine (is_fresh_loan_id_neq S _ l p _ Hfresh);
      rewrite get_p;
      reflexivity
   end.

Lemma not_value_contains_by_decomposition P v (H : ~P (get_constructor v))
  (G : match subvalues v with
       | [] => True
       | [w] => not_value_contains P w
       | _ => False
       end) :
  not_value_contains P v.
Proof.
  destruct (subvalues v) as [ | ? [ | ] ] eqn:?.
  - apply not_value_contains_zeroary; assumption.
  - eapply not_value_contains_unary; eassumption.
  - contradiction.
Qed.

Lemma not_state_contains_implies_not_value_contains_sget P S p :
  not_state_contains P S -> valid_spath S p -> not_value_contains P (S.[p]).
Proof.
  intros H valid_p q valid_q G. rewrite<- sget_app in G. eapply H; [ | exact G].
  apply valid_spath_app. split; assumption.
Qed.

Definition is_borrow (v : HLPL_plus_val) := exists l w, v = borrow^m(l, w).

Definition not_in_borrow (S : HLPL_plus_state) p :=
  forall q, prefix q p -> is_borrow (S.[q]) -> q = p.

Notation not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Extern 0 (_ <> botC) => discriminate : spath.

(* Adding a hint to reslove a relation ~prefix p q using the facts that:
 * - S.[p] does not contain a constructor c.
 * - S.[q] starts by the constructor c.
 * To solve the second goal, we need to help auto. When we are using this lemma, there should be a
 * hypothesis S.[q] = v. We are giving the instruction to rewrite S.[q] into v, and then to reduce
 * the expression (get_value v) produced, so that it can be solved automatically.
 *)
Hint Extern 3 (~prefix ?p ?q) =>
  match goal with
  | H : ?S.[?q] = _ |- _ =>
    simple eapply not_value_contains_not_prefix; [ | rewrite H; cbn | solve_validity]
  end : spath.

Ltac prove_not_contains0 :=
  try assumption;
  lazymatch goal with
  | |- True => auto
  | |- not_state_contains ?P (?S.[?p <- ?v]) =>
      simple apply not_state_contains_sset;
      prove_not_contains0
  | |- not_value_contains ?P (?S.[?q <- ?v].[?p]) =>
      let H := fresh "H" in
      tryif assert (H : disj q p) by auto with spath
      then (simple apply (not_value_contains_sset_disj P S v p q H);
        prove_not_contains0)
      else (simple apply (not_value_contains_sset P S v p q);
       [ prove_not_contains0 | prove_not_contains0 | solve_validity0])
  | H : not_state_contains ?P ?S |- not_value_contains ?P (?S.[?p]) =>
      simple apply (not_state_contains_implies_not_value_contains_sget P S p H);
      solve_validity0
  | |- not_value_contains ?P (?S.[?p]) => idtac
  | |- not_value_contains ?P ?v =>
      simple apply not_value_contains_by_decomposition;
      [ | cbn; prove_not_contains0]
  | |- _ => idtac
  end.
Ltac prove_not_contains := prove_not_contains0; auto with spath.

Inductive copy_val : HLPL_plus_val -> HLPL_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (HLPL_plus_int n) (HLPL_plus_int n)
| Copy_ptr l : copy_val (ptr(l)) (ptr(l))
| Copy_loc l v w : copy_val v w -> copy_val (loc(l, v)) w.

(* TODO: rename `eval_operand` *)
Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> HLPL_plus_state -> (HLPL_plus_val * HLPL_plus_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (HLPL_plus_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_loc (S.[pi]) -> not_contains_bot (S.[pi]) ->
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Definition vpath_pred (p : vpath) : option vpath :=
  match p with
  | [] => None
  | _ => Some (removelast p)
  end.

Definition spath_pred (p : spath) : option spath :=
  SOME q <- vpath_pred (snd p) IN Some (fst p, q).

Lemma vpath_pred_app_last p i : vpath_pred (p ++ [i]) = Some p.
Proof.
  transitivity (Some (removelast (p ++ [i]))).
  - destruct (p ++ [i]) eqn:?.
    + exfalso. eapply app_cons_not_nil. eauto.
    + reflexivity.
  - f_equal. apply removelast_last.
Qed.

Lemma spath_pred_app_last p i : spath_pred (p +++ [i]) = Some p.
Proof.
  unfold spath_pred, app_spath_vpath. cbn. rewrite vpath_pred_app_last.
  rewrite<- surjective_pairing. reflexivity.
Qed.

Lemma spath_pred_is_Some p q : spath_pred p = Some q -> exists i, p = q +++ [i].
Proof.
  unfold spath_pred. intro.
  assert (snd p <> []) by now destruct (snd p).
  assert ((fst p, removelast (snd p)) = q) as <-.
  { destruct (snd p); [discriminate | injection H; easy]. }
  exists (last (snd p) 0). unfold app_spath_vpath. cbn.
  rewrite<- app_removelast_last by assumption.
  apply surjective_pairing.
Qed.

Definition vancestor (v : HLPL_plus_val) p : HLPL_plus_constructor :=
  match vpath_pred p with
  | None => botC
  | Some q => get_constructor (v.[[q]])
  end.

Definition ancestor (S : HLPL_plus_state) p : HLPL_plus_constructor :=
  match spath_pred p with
  | None => botC
  | Some q => get_constructor (S.[q])
  end.

Lemma vancestor_singleton v i : vancestor v [i] = get_constructor v.
Proof. reflexivity. Qed.
Hint Rewrite vancestor_singleton : spath.

(* TODO: unused. delete? *)
Lemma ancestor_app_last S p i : ancestor S (p +++ [i]) = get_constructor (S.[p]).
Proof. unfold ancestor. rewrite spath_pred_app_last. reflexivity. Qed.

Lemma ancestor_sset_not_strict_prefix S p q v :
  ~strict_prefix q p -> ancestor (S.[q <- v]) p = ancestor S p.
Proof.
  unfold ancestor. intro. autodestruct.
  intros (? & ->)%spath_pred_is_Some.
  rewrite constructor_sset_sget_not_prefix by auto with spath. reflexivity.
Qed.
Hint Rewrite ancestor_sset_not_strict_prefix using auto with spath; fail : spath.

Lemma ancestor_is_not_bot S p c :
  ancestor S p = c -> c <> botC -> exists q i, p = q +++ [i] /\ get_constructor (S.[q]) = c.
Proof.
  unfold ancestor. autodestruct. intros (i & ->)%spath_pred_is_Some.
  intros. eexists _, _. eauto.
Qed.

Lemma vancestor_app v p q : q <> [] -> vancestor v (p ++ q) = vancestor (v.[[p]]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold vancestor. rewrite app_assoc, !vpath_pred_app_last, vget_app.
  reflexivity.
Qed.

Lemma ancestor_app S p q : q <> [] -> ancestor S (p +++ q) = vancestor (S.[p]) q.
Proof.
  intro H. destruct q using rev_ind; [easy | ].
  unfold ancestor, vancestor.
  rewrite app_spath_vpath_assoc, spath_pred_app_last, vpath_pred_app_last, sget_app.
  reflexivity.
Qed.

Hint Rewrite vancestor_app using easy : spath.
Hint Rewrite ancestor_app using easy : spath.

Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> HLPL_plus_state -> (HLPL_plus_val * HLPL_plus_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => (HLPL_plus_int m, S')) ->
      (S' |-{op} op_r => (HLPL_plus_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => ((HLPL_plus_int (m + n)), S'')
  | Eval_pointer_loc S p pi l
      (Heval_place : eval_place S Mut p pi)
      (Hancestor_loc : ancestor S pi = locC(l)) : S |-{rv} &mut p => (ptr(l), S)
  | Eval_pointer_no_loc S p pi l
      (Heval_place : eval_place S Mut p pi)
      (Hancestor_no_loc : ~is_loc (ancestor S pi))
      (* This hypothesis is not necessary for the proof of preservation of HLPL+, but it is
         useful in that it can help us eliminate cases. *)
      (Hno_loan : not_contains_loan (S.[pi])) :
      is_fresh l S ->
      S |-{rv} (&mut p) => (ptr(l), (S.[pi <- loc(l, S.[pi])]))
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Inductive reorg : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Reorg_refl S : reorg S S
| Reorg_trans S0 S1 S2 : reorg S0 S1 -> reorg S1 S2 -> reorg S0 S2
| Reorg_end_borrow_m S (p q : spath) l v :
    disj p q -> S.[p] = loan^m(l) -> S.[q] = borrow^m(l, v) ->
    not_contains_loan v -> not_in_borrow S q ->
    reorg S (S.[p <- v].[q <- bot]).

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : HLPL_plus_val * HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Store v S sp (eval_p : (S,, Anon |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loc : not_contains_outer_loc (S.[sp]))
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  store p (v, S) (S.[sp <- v],, Anon |-> S.[sp])
.

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   HLPL_plus_state -> statement -> nat -> Option (statement_result * HLPL_plus_state) -> Prop
*)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).
Inductive eval_stmt : statement -> statement_result -> HLPL_plus_state -> HLPL_plus_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => rUnit, S
  | Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | Eval_assign S vS' S'' p rv : (S |-{rv} rv => vS') -> store p vS' S'' ->
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | Eval_reorg S0 S1 S2 stmt r : reorg S0 S1 -> S1 |-{stmt} stmt => r, S2 -> S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(* TODO: introduce well-formedness judgement. *)

Inductive le_state_base : HLPL_plus_state -> HLPL_plus_state -> Prop :=
| Le_MutBorrow_To_Ptr S l sp_loan sp_borrow (Hdisj : disj sp_loan sp_borrow)
    (HS_loan : S.[sp_loan] = loan^m(l))
    (HS_borrow : get_constructor (S.[sp_borrow]) = borrowC^m(l)) :
    le_state_base (S.[sp_loan <- loc(l, S.[sp_borrow +++ [0] ])].[sp_borrow <- ptr(l)]) S.

Global Program Instance HLPL_plus_state_le_base : LeBase HLPL_plus_binder HLPL_plus_val :=
{ le_base := le_state_base;
  anon := Anon;
}.

(* TODO: move *)
(* Proving a comparison between p and q using information from the environment S. *)
Lemma spath_neq_by_value_constructor (S : HLPL_plus_state) p q v c :
  S.[p] = v -> get_constructor (S.[q]) = c -> get_constructor v <> c -> p <> q.
Proof. congruence. Qed.
Hint Extern 3 (~ (@eq spath _ _)) =>
  simple eapply spath_neq_by_value_constructor; [eassumption | eassumption | discriminate] : spath.

Hint Extern 0 (~ (@eq spath _ _)) => congruence : spath.

Section MutBorrow_to_Ptr.
  Context (S_r : HLPL_plus_state).
  Context (l0 : loan_id).
  Context (sp_loan sp_borrow : spath).
  Context (Hdisj : disj sp_loan sp_borrow).
  Hypothesis (HS_r_loan : S_r.[sp_loan] = loan^m(l0)).
  Hypothesis (HS_r_borrow : get_constructor (S_r.[sp_borrow]) = borrowC^m(l0)).
  Notation v := (S_r.[sp_borrow +++ [0] ]).
  Notation S_l := (S_r.[sp_loan <- loc(l0, v)].[sp_borrow <- ptr(l0)]).
  Context (perm : permission).

  (* TODO: name *)
  Inductive rel : spath -> spath -> Prop :=
    | Rel_sp_borrow_strict_prefix q : rel (sp_loan +++ [0] ++ q) (sp_borrow +++ [0] ++ q)
  | Rel_other q : ~strict_prefix sp_borrow q -> rel q q.

  (* An equivalent (and more usable I hope) version of rel. *)
  Definition rel' p q :=
    (exists r, p = sp_loan +++ [0] ++ r /\ q = sp_borrow +++ [0] ++ r) \/
    (p = q /\ ~strict_prefix sp_borrow p).
  Definition rel_implies_rel' p q : rel p q -> rel' p q.
  Proof.
    intros [r | ].
    - left. exists r. auto.
    - right. auto.
  Qed.

  (* TODO: name *)
  Lemma get_loc_rel q l (H : get_constructor (S_r.[q]) = locC(l)) :
    exists q', rel (q' +++ [0]) (q +++ [0]) /\ get_constructor (S_l.[q']) = locC(l).
  Proof.
    destruct (decidable_prefix sp_borrow q) as [ | ].
    - assert (prefix (sp_borrow +++ [0]) q) as (r & <-) by eauto with spath.
      autorewrite with spath in H.
      exists (sp_loan +++ [0] ++ r). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + autorewrite with spath. assumption.
    - exists q. split.
      (* comparison reasonning: *)
      + apply Rel_other. auto with spath.
      + autorewrite with spath. assumption.
  Qed.

  Lemma eval_proj_mut_sp_borrow_strict_prefix proj r q
    (H : eval_proj S_r perm proj (sp_borrow +++ [0] ++ r) q) :
    exists q', rel q' q /\ eval_proj S_l perm proj (sp_loan +++ [0] ++ r) q'.
  Proof.
    remember (sp_borrow +++ [0] ++ r) as p. revert r Heqp. induction H; intros r ->.
    - exists ((sp_loan +++ [0] ++ r) +++ [0]). split.
      + rewrite<- !app_spath_vpath_assoc. constructor.
      + apply Eval_Deref_MutBorrow with (l := l); try assumption.
        autorewrite with spath. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try assumption.
      rewrite sget_app in *. autorewrite with spath in *. assumption.
    - specialize (IHeval_proj (r ++ [0])). destruct IHeval_proj as (q'' & ? & ?).
      + rewrite<- app_spath_vpath_assoc. reflexivity.
      + exists q''. split; try assumption.
        apply Eval_Loc with (l := l).
        * assumption.
        * autorewrite with spath. assumption.
        * rewrite<- app_spath_vpath_assoc. assumption.
  Qed.

  Lemma eval_proj_mut_not_prefix_sp_borrow proj q r
    (not_prefix : ~strict_prefix sp_borrow q) (H : eval_proj S_r perm proj q r) :
    exists r', rel r' r /\ eval_proj S_l perm proj q r'.
  Proof.
    induction H.
    - destruct (decidable_spath_eq q sp_borrow) as [-> | ].
      + exists (sp_loan +++ [0]). split. { constructor. }
        apply Eval_Deref_Ptr_Locs with (l := l0); autorewrite with spath; easy.
      + exists (q +++ [0]). split.
        { apply Rel_other. enough (~prefix sp_borrow q) by (intros K%strict_prefix_app_last; easy). reduce_comp. }
        apply Eval_Deref_MutBorrow with (l := l); try assumption.
        autorewrite with spath. assumption.
    - apply get_loc_rel in get_q'. destruct get_q' as (q_loc & ? & ?).
      exists (q_loc +++ [0]). split; try assumption.
      apply Eval_Deref_Ptr_Locs with (l := l); try auto.
      autorewrite with spath. assumption.
    - destruct IHeval_proj as (r' & ? & ?).
      { intros G%strict_prefix_app_last; revert G. reduce_comp. }
      exists r'. split; try assumption. apply Eval_Loc with (l := l); try easy.
      autorewrite with spath. assumption.
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
    - intros q_l ?.
      apply eval_proj_mut_borrow_to_ptr with (q_l := q_l) in Heval_proj; try assumption.
      destruct Heval_proj as (q'_l & rel_q'_l & ?).
      destruct (IHeval_path q'_l rel_q'_l) as (q''_l & ? & ?).
      exists q''_l. split. { assumption. }
      apply Eval_cons with (q := q'_l); assumption.
  Qed.

  Lemma eval_path_mut_borrow_to_ptr_Mov P q q' :
    eval_path S_r Mov P q q' -> eval_path S_l Mov P q q'.
  Proof.
    intro H. induction H.
    - constructor.
    - destruct Heval_proj; easy.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr p pi_r :
    eval_place S_r perm p pi_r ->
    exists pi_l, rel pi_l pi_r /\ eval_place S_l perm p pi_l.
  Proof.
    intros (i & ? & H). apply eval_path_mut_borrow_to_ptr with (q_l := (i, [])) in H.
    - destruct H as (q'_l & rel & ?). exists q'_l. split. { assumption. }
      exists i. split. { rewrite! find_binder_sset. assumption. }
      assumption.
    - apply Rel_other. apply not_strict_prefix_nil.
  Qed.

  Corollary eval_place_mut_borrow_to_ptr_Mov p pi :
    eval_place S_r Mov p pi -> eval_place S_l Mov p pi.
  Proof.
    intros (i & ? & H). apply eval_path_mut_borrow_to_ptr_Mov with (q := (i, [])) in H.
    exists i. split; try assumption. rewrite! find_binder_sset. assumption.
  Qed.

  Lemma eval_place_mut_borrow_to_ptr_Mov_comp p pi :
    eval_place S_r Mov p pi -> ~strict_prefix sp_borrow pi.
  Proof.
    intros (i & ? & H). remember (i, []) as pi0. induction H.
    - rewrite Heqpi0. apply not_strict_prefix_nil.
    - destruct Heval_proj; easy.
  Qed.
End MutBorrow_to_Ptr.

(* Suppose that Sl <= Sr (with a base case), and that p evaluates to a spath pi in Sr
   (Sr |-{p} p =>^{perm} pi).
   This tactic chooses the right lemmas to apply in order to prove that p reduces to a spath pi' in Sl, and generates facts about pi'.
   Finally, it proves that pi is valid in Sr, and clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  lazymatch goal with
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{Mov} ?pi,
    _ : ?Sr.[?sp_loan] = loan^m (?l),
    _ : get_constructor (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let sp_borrow_not_prefix := fresh "sp_borrow_not_prefix" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as eval_p_in_Sl;
      pose proof eval_p_in_Sr as sp_borrow_not_prefix;
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_mut_borrow_to_ptr_Mov
        with (sp_loan := sp_loan) (sp_borrow := sp_borrow) (l0 := l)
        in eval_p_in_Sl;
      apply eval_place_mut_borrow_to_ptr_Mov_comp with (sp_borrow := sp_borrow)
        in sp_borrow_not_prefix;
      apply eval_place_valid in valid_p;
      clear eval_p_in_Sr
  | eval_p_in_Sr : ?Sr |-{p} ?p =>^{ _ } ?pi_r,
    Hdisj : disj ?sp_loan ?sp_borrow,
    HSr_loan : ?Sr.[?sp_loan] = loan^m (?l),
    HSr_borrow : get_constructor (?Sr.[?sp_borrow]) = borrowC^m(?l) |- _ =>
      let pi_l := fresh "pi_l" in
      let eval_p_in_Sl := fresh "eval_p_in_Sl" in
      let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
      let valid_p := fresh "valid_p" in
      pose proof eval_p_in_Sr as valid_p;
      apply eval_place_valid in valid_p;
      apply (eval_place_mut_borrow_to_ptr Sr l sp_loan sp_borrow Hdisj HSr_loan HSr_borrow)
        in eval_p_in_Sr;
      destruct eval_p_in_Sr as (pi_l & rel_pi_l_pi_r%rel_implies_rel' & eval_p_in_Sl)
  end.

Lemma operand_preserves_HLPL_plus_rel op : preservation (eval_operand op).
Proof.
  preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = const n *)
  - destruct Hle.
    + eapply complete_square_diagram.
      * eapply prove_le_state_val.
        { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
          assumption. all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * constructor.
      * reflexivity.
  (* op = copy p *)
  - admit.
  (* op = move p *)
  - destruct Hle.
    (* Le-MutBorrow-To-Ptr *)
    + eval_place_preservation.
      assert (disj pi sp_loan) by reduce_comp.
      destruct (decidable_prefix pi sp_borrow) as [(q & <-) | ].
      (* Case 1: the mutable borrow we're transforming to a pointer is in the moved value. *)
      * eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := (length S, q)).
             auto with spath. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: prove_not_contains.
        -- autorewrite with spath. f_equal. prove_states_eq.
      (* Case 2: the mutable borrow we're transforming to a pointer is disjoint to the moved value.
       *)
      * assert (disj pi sp_borrow) by reduce_comp.
        eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- constructor. eassumption. all: autorewrite with spath; assumption.
        -- autorewrite with spath. f_equal. prove_states_eq.
Admitted.

Lemma le_base_implies_le S0 S1 : le_base S0 S1 -> le S0 S1.
Proof. now constructor. Qed.

Lemma rvalue_preserves_HLPL_plus_rel rv : preservation (eval_rvalue rv).
Proof.
  preservation_by_base_case.
  intros ? ? Heval. destruct Heval.
  (* rv = just op *)
  - apply operand_preserves_HLPL_plus_rel in Heval_op.
    intros ? ?%le_base_implies_le.
    firstorder using Eval_just.
  (* rv = op + op *)
  - apply operand_preserves_HLPL_plus_rel in H, H0.
    intros S0 Hle%le_base_implies_le.
    admit.
  (* rv = &mut p *)
  (* The place p evaluates to a spath under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      (* Case 1: the place p is under the borrow. *)
      * destruct r; autorewrite with spath in Hancestor_loc.
        (* The place p cannot be just under the borrow, because its ancestor is a loc, it cannot be
         * the mutable borrow. *)
        { congruence. }
        eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- eapply Eval_pointer_loc. eassumption. autorewrite with spath. exact Hancestor_loc.
        -- reflexivity.
      (* Case 2: the place p is not under the borrow. *)
      * eapply complete_square_diagram.
        -- eapply prove_le_state_val.
           { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
             assumption. all: autorewrite with spath; eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- eapply Eval_pointer_loc. eassumption. autorewrite with spath. exact Hancestor_loc.
        -- reflexivity.
  (* rv = &mut p *)
  (* The place p evaluates to a spath that is not under a loc. *)
  - intros Sl Hle. destruct Hle.
    + eval_place_preservation.
      destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
      * destruct r.
        (* Case 1: the place p is just under sp_borrow. *)
        -- rewrite app_nil_r in *. eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              (* This requires to apply the rule Le-Merge-Locs, that we have not defined yet. *)
              admit.
           ++ apply Eval_pointer_loc with (pi := sp_loan +++ [0]).
              assumption. autorewrite with spath. reflexivity.
           ++ admit.
        (* Case 2: the place p is just under sp_borrow, but not just under. *)
        -- eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr. eassumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              all: autorewrite with spath. autorewrite with spath in Hancestor_no_loc.
              exact Hancestor_no_loc. assumption. prove_not_contains.
           ++ f_equal. prove_states_eq.
      (* Case 3: *)
      * assert (disj sp_loan pi) by reduce_comp.
        destruct (decidable_prefix pi sp_borrow) as [(r & <-) | ].
        -- eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := pi +++ [0] ++ r).
                auto with spath. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. assumption. prove_not_contains. prove_not_contains.
           ++ f_equal. autorewrite with spath. prove_states_eq.
        -- assert (disj sp_borrow pi) by reduce_comp.
           eapply complete_square_diagram.
           ++ eapply prove_le_state_val.
              { apply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
                assumption. all: autorewrite with spath; eassumption. }
              { autorewrite with spath. reflexivity. }
              reflexivity.
           ++ apply Eval_pointer_no_loc with (l := l). eassumption.
              autorewrite with spath. assumption. prove_not_contains. prove_not_contains.
           ++ f_equal. autorewrite with spath. prove_states_eq.
Admitted.

Hint Extern 0 (not_value_contains _ _) => prove_not_contains0 : spath.
Lemma eval_rvalue_no_loan_loc S rv v S' : S |-{rv} rv => (v, S') ->
  not_contains_loan v /\ not_contains_loc v.
Proof.
  remember (v, S') as vS' eqn:EQN. intro H. destruct H; [destruct Heval_op | ..].
  all: inversion EQN; subst; auto with spath.
  induction Hcopy_val; auto with spath.
Qed.

(*
Lemma eval_path_app_last S p k pi S' : S |-{p} p =>^{k} pi -> (S ++ S') |-{p} p =>^{k} pi.
Proof.
Admitted.
 *)

Lemma eval_path_app_last S v p k pi :
  not_contains_loc v -> (S,, Anon |-> v) |-{p} p =>^{k} pi -> S |-{p} p =>^{k} pi.
Proof.
  destruct p as (x & q). intros no_loc (i & H & G). exists i. cbn.
  assert (find_binder S (Var x) = Some i).
  { apply find_binder_Some in H. destruct H as (Hi & Hi_min).
    destruct (Nat.lt_ge_cases i (length S)) as [ |  ].
    + apply find_binder_Some.
      rewrite nth_error_app1 in Hi by assumption. split; [exact Hi | ].
      intros j j_lt_i. specialize (Hi_min j j_lt_i).
      rewrite nth_error_app1 in Hi_min by (etransitivity; eassumption).
      assumption.
    + rewrite nth_error_app2 in Hi by auto using Nat.lt_le_incl.
      destruct (i - length S).
      * discriminate.
      * cbn in Hi. rewrite nth_error_nil in Hi. discriminate.
  }
  split; [assumption | ].
  cbn in *. assert (valid_pi0 : valid_spath S (i, [])) by eauto using find_binder_valid.
  apply proj1 with (B := valid_spath S (i, [])). induction G.
  + split. constructor. exact valid_pi0.
  + assert (eval_proj S k proj p q).
    { clear IHG. induction Heval_proj; autorewrite with spath in get_q.
      - eapply Eval_Deref_MutBorrow; eassumption.
      - eapply Eval_Deref_Ptr_Locs; [eassumption.. | ].
        assert (valid_q' : valid_spath (S,, Anon |-> v) q') by solve_validity.
        apply valid_spath_app_last_cases in valid_q'.
        destruct valid_q'; autorewrite with spath in get_q'.
        + exact get_q'.
        + exfalso. apply no_loc with (p := snd q'); [solve_validity | ].
          rewrite get_q'. constructor.
      - eapply Eval_Loc; eauto with spath.
    }
    destruct IHG.
    { eapply eval_proj_valid. eassumption. }
    split; [ econstructor | ]; eassumption.
Qed.

Lemma state_app_last_eq (Sl Sr : HLPL_plus_state) bl br vl vr :
  (Sl,, bl |-> vl) = (Sr,, br |-> vr) -> Sl = Sr /\ vl = vr.
Proof. intros (? & ?)%app_inj_tail. split; congruence. Qed.

(* Suppose that (v0, S0) <= (vn, Sn), and that vr does not contain any loan.
   Let us take (v1, S1), ..., (v_{n-1}, S_{n-1}) the intermediate pairs such that
   (v0, S0) <= (v1, S1) <= ... <= (vn, Sn).
   Then, we are going to prove that for each (vi, Si), the value vi does not contain any loan. *)
Definition le_val_state_base' (vSl vSr : HLPL_plus_val * HLPL_plus_state) : Prop :=
  let (vl, Sl) := vSl in
  let (vr, Sr) := vSr in
  le_base (Sl,, Anon |-> vl) (Sr,, Anon |-> vr) /\ not_contains_loan vr /\ not_contains_loc vr.
Notation le_val_state' := (refl_trans_closure le_val_state_base').

Lemma le_base_does_not_insert_loan_loc vl Sl vr Sr :
  le_base (Sl,, Anon |-> vl) (Sr,, Anon |-> vr) -> not_contains_loan vr -> not_contains_loc vr
  -> not_contains_loan vl /\ not_contains_loc vl.
Proof.
  remember (Sl,, Anon |-> vl) as vSl. remember (Sr,, Anon |-> vr) as vSr.
  intros Hle Hno_loan Hno_loc. destruct Hle; subst.
  - assert (valid_spath Sr sp_loan). { admit. }
    destruct (Nat.eq_dec (fst sp_borrow) (length Sr)).
    + autorewrite with spath in HeqvSl.
      apply state_app_last_eq in HeqvSl. destruct HeqvSl as (_ & <-).
      auto with spath.
    + assert (valid_spath Sr sp_borrow). { admit. }
      autorewrite with spath in HeqvSl.
      apply state_app_last_eq in HeqvSl. destruct HeqvSl as (_ & <-). auto.
Admitted.

Lemma le_val_state_no_loan_right vSl vSr :
  le vSl vSr -> not_contains_loan (fst vSr) -> not_contains_loc (fst vSr)
  -> le_val_state' vSl vSr.
Proof.
  intros Hle Hno_loan Hno_loc.
  apply proj1 with (B := (not_contains_loan (fst vSl)) /\ (not_contains_loc (fst vSl))).
  induction Hle as [vSl vSr | | x y z].
  - split.
    + constructor. destruct vSl, vSr. cbn. auto.
    + destruct vSl. destruct vSr. eapply le_base_does_not_insert_loan_loc; eauto.
  - split; [reflexivity | auto].
  - split; [transitivity y | ]; tauto.
Qed.

Lemma store_preserves_HLPL_plus_rel p :
  forward_simulation le_val_state' le (store p) (store p).
Proof.
  apply preservation_by_base_case.
  intros vSr Sr' Hstore vSl Hle.
  destruct vSl as (vl, Sl) eqn:?. destruct vSr as (vr, Sr) eqn:?.
  destruct Hle as (Hle & no_loan & no_loc). inversion Hstore. subst. clear Hstore.
  assert (valid_spath Sr sp).
  { eapply eval_path_app_last in eval_p; auto with spath. }
  remember (Sl,, Anon |-> vl) eqn:HeqvSl. remember (Sr,, Anon |-> vr).
  destruct Hle; subst.
  - eval_place_preservation. clear valid_p.
    assert (valid_sp_loan : valid_spath (Sr,, Anon |-> vr) sp_loan) by solve_validity.
    apply valid_spath_app_last_cases in valid_sp_loan.
    destruct valid_sp_loan.
    2: { autorewrite with spath in HS_loan. exfalso.
      eapply no_loan; [ | rewrite HS_loan ]. solve_validity. constructor. }
    autorewrite with spath in HS_loan |-.
    destruct rel_pi_l_pi_r as [ (r & -> & ->) | (-> & ?)].
    (* Case 1: the place sp where we write is inside the borrow. *)
    + assert (valid_spath Sr sp_borrow) by (eapply valid_spath_app; eassumption).
      autorewrite with spath in HS_borrow, HeqvSl. apply state_app_last_eq in HeqvSl.
      destruct HeqvSl as (<- & ->). autorewrite with spath in eval_p_in_Sl.
      eapply complete_square_diagram.
      * constructor.
        eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp_borrow).
        assumption. all: autorewrite with spath; eassumption.
      * constructor. eassumption.
        all: autorewrite with spath; assumption.
      * autorewrite with spath. f_equal. prove_states_eq.
    + assert (valid_sp_borrow : valid_spath (Sr,, Anon |-> vr) sp_borrow) by solve_validity.
      apply valid_spath_app_last_cases in valid_sp_borrow.
      destruct valid_sp_borrow as [valid_sp_borrw | ]; autorewrite with spath in HS_borrow.
      * autorewrite with spath in HeqvSl. apply state_app_last_eq in HeqvSl.
        destruct HeqvSl. subst.
        autorewrite with spath in eval_p_in_Sl.
        destruct (decidable_prefix sp sp_borrow) as [(r_borrow & <-) | ].
        (* Case 2: the borrow is inside the place we write in. *)
        -- destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r_loan))
                                                 (sp_borrow := (length Sr, r_borrow)).
                  eauto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. reflexivity.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := (length Sr, r_borrow)).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
        (* Case 3: the borrow is disjoint from the place we write in. *)
        -- assert (disj sp sp_borrow) by reduce_comp.
           destruct (decidable_prefix sp sp_loan) as [(r_loan & <-) | ].
           (* Case 3a: the loan is in the place we write in. *)
           ++ eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r_loan))
                                                 (sp_borrow := sp_borrow).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
          (* Case 3b: the loan is disjoint to the place we write in. *)
           ++ assert (disj sp sp_loan) by reduce_comp.
              eapply complete_square_diagram.
              ** constructor.
                 eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan)
                                                 (sp_borrow := sp_borrow).
                 auto with spath. all: autorewrite with spath; eassumption.
              ** constructor. eassumption. all: prove_not_contains_outer.
              ** autorewrite with spath. f_equal. prove_states_eq.
      (* Case 4: the borrow is inside the evaluated value. *)
      * destruct sp_borrow as (i & q). cbn in H2. subst i.
        autorewrite with spath in HS_borrow.
        autorewrite with spath in eval_p_in_Sl.
        autorewrite with spath in HeqvSl. apply state_app_last_eq in HeqvSl.
        destruct HeqvSl. subst.
        destruct (decidable_prefix sp sp_loan) as [(r & <-) | ].
        (* Case 4a: the loan is in the place we write in. *)
        -- eapply complete_square_diagram.
           ++ constructor.
              eapply Le_MutBorrow_To_Ptr with (sp_loan := (length Sr, r))
                                              (sp_borrow := sp +++ q).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eassumption. all: prove_not_contains_outer.
           ++ autorewrite with spath. f_equal. prove_states_eq.
        (* Case 4b: the loan is disjoint to the place we write in. *)
        -- assert (disj sp sp_loan) by reduce_comp.
           eapply complete_square_diagram.
           ++ constructor.
              eapply Le_MutBorrow_To_Ptr with (sp_loan := sp_loan) (sp_borrow := sp +++ q).
              auto with spath. all: autorewrite with spath; eassumption.
           ++ constructor. eassumption. all: prove_not_contains_outer.
           ++ autorewrite with spath. f_equal. prove_states_eq.
Qed.
