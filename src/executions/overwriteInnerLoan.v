(** * Mechanized_LLBC.executions.overwriteInnerLoan : A LLBC example where an inner loan is overwritten. *)
Require Import base.
Require Import lang.
Require Import SimulationUtils.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.
From stdpp Require Import pmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.
From Stdlib Require Bool.
(** There is already a notation [is_fresh] in std++, that is why we import LLBC after. *)
Require Import LLBC.

Local Open Scope option_monad_scope.
(** The program we execute is:
<<
fn main() {
    let mut a = 1983;
    let mut b = 1986;
    let mut c = &mut a;
    let d = &mut *c;
    c = &mut b;
    *d = 58;
}
>>
 *)
Notation a := 1%positive.
Notation b := 2%positive.
Notation c := 3%positive.
Notation d := 4%positive.
Definition main : statement :=
  ASSIGN (a, [], TInt) <- Use (Const (IntConst 1983)) ;;
  ASSIGN (b, [], TInt) <- Use (Const (IntConst 1986)) ;;
  ASSIGN (c, [], TRef TInt) <- &mut (a, [], TInt) ;;
  ASSIGN (d, [], TRef TInt) <- &mut (c, [Deref], TInt) ;;
  ASSIGN (c, [], TRef TInt) <- &mut (b, [], TInt) ;;
  ASSIGN (d, [Deref], TInt) <- Use (Const (IntConst 58)) ;;
  Nop
.
(** Note: the line << c = &mut b >> overwrites a loan, but as it is an outer loan, it does
   not cause any problem. This is a check that the overwriting of outer loans is supported.

   Also, the last [Nop] statement was added so that we could perform reorganization operations
   before the end, and but back the value 58 in the variable [a]. *)

Open Scope stdpp.

Notation init_state := {|
  vars := {[a := bot; b := bot; c := bot; d := bot]};
  anons := empty;
|}.

Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(l) => false
  | _ => true
  end.

(** For the moment, the type of values is so restricted that a value contains an outer loan if and
    only if it is a mutable loan. *)
Lemma decide_not_contains_outer_loan_correct v :
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] _ H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Instance decidable_not_value_contains P `(H : forall n, Decision (P n)) v :
  Decision (not_value_contains P v).
Proof.
  induction v; try (apply decidable_not_value_contains_zeroary; [assumption | reflexivity]).
  eapply decidable_not_value_contains_unary; reflexivity || assumption.
Defined.

Instance decidable_is_loan c : Decision (is_loan c).
Proof. destruct c; first [left; constructor | right; inversion 1]. Defined.

Instance decidable_is_mut_borrow c : Decision (is_mut_borrow c).
Proof. destruct c; first [left; constructor | right; inversion 1]. Defined.

Instance decidable_is_fresh l S : Decision (is_fresh l S).
Proof. apply decidable_not_state_contains. solve_decision. Defined.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)

(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

Section Eval_LLBC_program.
  Hint Rewrite (@alter_insert_eq _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton_eq _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  (** TODO: use automation similar to file << LLBC_sharp_exec_utils.v >>. *)
  (* Perform simplifications to put maps of the state in the form `{[x0 := v0; ...; xn := vn]}`,
     that is a notation for a sequence of insertions applied to a singleton.
     We cannot use the tactic `vm_compute` because it computes under the insertions and the
     singleton. *)
  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singleton];
    autorewrite with core.

  Lemma safe_main :
    exists end_state, eval_stmt main rUnit init_state end_state /\
      exists pi, eval_place end_state Imm ((a, [], TInt) : place) pi /\ end_state.[pi] = VInt 58.
  Proof.
    eexists. split. {
      eapply E_Seq_Unit.
      { eapply E_Assign; [ | apply Store with (a := 1%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | apply Store with (a := 2%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 3%positive)].
        - apply E_MutBorrow with (l := 1%positive);
            [eval_var; constructor | compute_done..].
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 4%positive)].
        - eapply E_MutBorrow with (l := 2%positive).
          + eval_var. repeat econstructor || easy.
          + compute_done.
          + compute_done.
          + compute_done.
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 5%positive)].
        - apply E_MutBorrow with (l := 3%positive); [eval_var; constructor | compute_done..].
        - eval_var. constructor.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Seq_Unit.
      { eapply E_Assign; [ | eapply Store with (a := 6%positive)].
        - apply E_Use, E_IntConst.
        - eval_var. repeat econstructor || easy.
        - apply decide_not_contains_outer_loan_correct. reflexivity.
        - reflexivity.
      }
      simpl_state. eapply E_Reorg.
      { etransitivity; [constructor | ].
        { apply Reorg_End_MutBorrow with (p := (encode_anon 5, [0])) (q := (encode_var d, [])) (l := 2%positive).
          + left. discriminate.
          + reflexivity.
          + reflexivity.
          + compute_done.
          + intros ? ->%prefix_nil. reflexivity. }
          simpl_state.
          constructor.
          apply Reorg_End_MutBorrow with (l := 1%positive) (p := (encode_var a, [])) (q := (encode_anon 5, [])).
          + left. discriminate.
          + reflexivity.
          + reflexivity.
          + compute_done.
          + intros ? ->%prefix_nil. reflexivity.
      }
      simpl_state. apply E_Nop.
    }
    eexists. split.
    - eval_var. constructor.
    - vm_compute. reflexivity.
  Qed.
End Eval_LLBC_program.
