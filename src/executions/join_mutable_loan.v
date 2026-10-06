From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import decidable pmap.
Require Import base PathToSubtree SimulationUtils lang.


Open Scope option_monad_scope.
(** The program we execute is:
<<
fn f(mut a: i32, mut b: i32, mut c: i32) {
    let mut x = &mut a;
    let mut y = &mut c;
    if b <= 42 {
        x = &mut b;
    }
    else {
        y = &mut b;
    }
    a += 1;
    *y += 1;
}
>>
 *)
Notation a := 1%positive.
Notation b := 2%positive.
Notation c := 3%positive.
Notation x := 4%positive.
Notation y := 5%positive.
Notation cond := 6%positive.

(* TODO: solve scope issues. *)
Close Scope stdpp_scope.

(** Note that we have to introduce a temporary variable [cond] to store the result of the comparison. *)
(** TODO: Introduce boolean type *)
Definition f :=
  ASSIGN (x, [], TRef TInt) <- &mut (a, [], TInt);;
  ASSIGN (y, [], TRef TInt) <- &mut (c, [], TInt);;
  ASSIGN (cond, [], TInt) <- BinaryOp BLe (Copy (b, [], TInt)) (Const (IntConst 42));;
  IF Move (cond, [], TInt) {{
    ASSIGN (x, [], TRef TInt) <- &mut (b, [], TInt)
  }}
  ELSE {{
    ASSIGN (y, [], TRef TInt) <- &mut (b, [], TInt)
  }};;
  ASSIGN (x, [Deref], TInt) <- BinaryOp BAdd (Copy (x, [Deref], TInt)) (Const (IntConst 1));;
  ASSIGN (a, [], TInt) <- BinaryOp BAdd (Copy (a, [], TInt)) (Const (IntConst 1));;
  ASSIGN (y, [Deref], TInt) <- BinaryOp BAdd (Copy (y, [Deref], TInt)) (Const (IntConst 1))
.

(* Conflicting constructors for type [type] (file << src/lang.v >> and [LLBC_type]
   (file << src/Symbolic_states.v >>, we import [LLBC_type] later .*)
Require Import Symbolic_states Symbolic_relations LLBC_sharp LLBC_sharp_exec_utils.

Open Scope stdpp.
(** We execute the function [f] on the most general state. The arguments << x >> and << y >> are initialized as symbolic values, while the local variables are uninitialized. *)
Definition init_state := {|
  vars := {[
    a := VSymbolic TInt;
    b := VSymbolic TInt;
    c := VSymbolic TInt;
    x := bot;
    y := bot;
    cond := bot
  ]};
  anons := empty;
  abstractions := empty;
|}.

Definition la : loan_id := 1%positive.
Definition lb : loan_id := 2%positive.
Definition lc : loan_id := 3%positive.
Definition lx : loan_id := 4%positive.
Definition ly : loan_id := 5%positive.
Definition lbx : loan_id := 6%positive.
Definition lby : loan_id := 7%positive.

Definition Ab : positive := 1.
Definition Ax : positive := 2.
Definition Ay : positive := 3.
Definition A_extra : positive := 4.

(** The join state at the end of the conditional. *)
Definition join_state : state := {|
  vars := {[
    a := loan^m(TInt, la);
    b := loan^m(TInt, lb);
    c := loan^m(TInt, lc);
    x := borrow^m(lx, VSymbolic TInt);
    y := borrow^m(ly, VSymbolic TInt);
    cond := VBottom
  ]};
  anons := empty;
  abstractions := {[
    Ab := {[1%positive := borrow^m(lb, VSymbolic TInt);
            2%positive := loan^m(TInt, lbx);
            3%positive := loan^m(TInt, lby)]};
    Ax := {[1%positive := borrow^m(la, VSymbolic TInt);
            2%positive := borrow^m(lbx, VSymbolic TInt);
            3%positive := loan^m(TInt, lx)]};
    Ay := {[1%positive := borrow^m(lby, VSymbolic TInt);
            2%positive := borrow^m(lc, VSymbolic TInt);
            3%positive := loan^m(TInt, ly)]}
    ]}
|}.

(* TODO: move *)
Lemma try_assert {P : Prop} (o : option P) (p : P) : o = Some p -> P.
Proof. intros _. exact p. Qed.

Lemma safe_f : exists end_state, init_state |-# f ~> end_state.
Proof.
  eexists.
  (** Evaluation of << x = &mut a; >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_borrow_mut la _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.
  (** Evaluation of << y = &mut c; >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_borrow_mut lc _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.
  (** Evaluation of the computation << b <= 42 >>. The result is stored in the temporary variable [cond]. *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** Evaluation of the conditional. *)
  eapply eval_seq_unit.
  { eapply E_IfThenElse_Symbolic with (B := {[rUnit := join_state]});
      [ | eapply Consequence_Postcondition..].
    { refine (try_compute (compute_eval_op _ _) _ _ _). reflexivity. }

    (** Evaluation of the if branch. *)
    { eapply E_Assign.
      { refine (try_compute (compute_borrow_mut lb _ _) _ _ _). reflexivity. }
      { refine (try_compute (compute_eval_store 1%positive _ _) _ _ _). reflexivity. }
    }

    (** The state [join_state] is more abstract than the state at the end of the if branch. *)
    { apply leq_singleton.
      eapply prove_leq_symbolic; [constructor | ].
      { remove_anon 1%positive.
        eapply Leq_ToAbs with (i := A_extra); [reflexivity.. | ].
        apply ToAbs_MutBorrow with (k := 1%positive); [constructor | compute_done..]. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var y, []) _ ly Ay 2%positive 3%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var x, []) _ lbx Ab 1%positive 2%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var x, []) _ lx Ax 2%positive 3%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [constructor | ].
      { remove_abstraction Ax. remove_abstraction A_extra.
        rewrite remove_add_abstraction_ne by discriminate.
        apply Leq_MergeAbs; [reflexivity.. | | discriminate].
        eexists _, _. split; [apply Remove_nothing | ].
        apply UnionInsert with (j := 1%positive); [reflexivity.. | ].
        apply UnionEmpty. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { remove_abstraction Ab. remove_abstraction Ay.
        rewrite remove_add_abstraction_ne by discriminate.
        eapply leq_borrow_abs with (l := lby) (ty := TInt) (ja := 3%positive) (jb := 1%positive).
        all: compute_done. }
      reflexivity.
    }

    (** Evaluation of the else branch. *)
    { eapply E_Assign.
      { refine (try_compute (compute_borrow_mut lb _ _) _ _ _). reflexivity. }
      { refine (try_compute (compute_eval_store 1%positive _ _) _ _ _). reflexivity. }
    }

    (** The state [join_state] is more abstract than the state at the end of the else branch. *)
    { apply leq_singleton.
      eapply prove_leq_symbolic; [constructor | ].
      { remove_anon 1%positive.
        eapply Leq_ToAbs with (i := A_extra); [reflexivity.. | ].
        apply ToAbs_MutBorrow with (k := 2%positive); [constructor | compute_done..]. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var x, []) _ lx Ax 1%positive 3%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var y, []) _ lby Ab 1%positive 3%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { eapply (Leq_Reborrow_MutBorrow_Abs _ (encode_var y, []) _ ly Ay 1%positive 3%positive);
          [compute_done | reflexivity | | reflexivity | discriminate | constructor].
        refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
      simpl_state.
      eapply prove_leq_symbolic; [constructor | ].
      { remove_abstraction Ay. remove_abstraction A_extra.
        rewrite remove_add_abstraction_ne by discriminate.
        apply Leq_MergeAbs; [reflexivity.. | | discriminate].
        eexists _, _. split; [apply Remove_nothing | ].
        apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
        apply UnionEmpty. }
      simpl_state.
      eapply prove_leq_symbolic; [ | ].
      { remove_abstraction Ab. remove_abstraction Ax.
        rewrite remove_add_abstraction_ne by discriminate.
        eapply leq_borrow_abs with (l := lbx) (ty := TInt) (ja := 2%positive) (jb := 2%positive).
        all: compute_done. }
      reflexivity.
    }
  }

  (** Evaluation of << *x += 1; >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  eapply E_Reorg.
  { etransitivity; [constructor | ].
    (** Ending the borrow in << x >>. *)
    { remove_abstraction Ax. remove_abstraction_element 3%positive.
      eapply Reorg_End_MutBorrow_in_abstraction with (q := (encode_var x, [])).
      reflexivity. reflexivity. reflexivity. constructor. compute_done.
      refine (proj2 (try_assert (compute_not_in_borrow _ _) _ _)). reflexivity.
      refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity. }
    simpl_state.

    (** Ending the abstraction << Ax >>. *)
    etransitivity; [constructor | ].
    { remove_abstraction Ax. eapply Reorg_End_Abstraction; [reflexivity | compute_done | ].
      econstructor.
      eapply UnionInsert with (j := 1%positive); [reflexivity.. | ].
      eapply UnionInsert with (j := 2%positive); [reflexivity.. | ].
      apply UnionEmpty. }
    simpl_state.

    (** Ending the loan << a >>. *)
    constructor.
    eapply Reorg_End_MutBorrow with (p := (encode_var a, []))
                                    (q := (anon_accessor 1%positive, [])).
    reflexivity. reflexivity. constructor. compute_done.
    refine (proj2 (try_assert (compute_not_in_borrow _ _) _ _)). reflexivity.
    left. discriminate.
    refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity.
    refine (try_assert (compute_not_in_abstraction _) _ _). reflexivity.
  }
  simpl_state.

  (** Evaluation of << a += 1; >> *)
  eapply eval_seq_unit.
  { eapply assign_no_anon.
    { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
    { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
  }
  simpl_state.

  (** Evaluation of << *y += 1; >> *)
  eapply assign_no_anon.
  { refine (try_compute (compute_eval_rv _ _) _ _ _). reflexivity. }
  { refine (try_compute (compute_eval_store_no_anon _ _) _ _ _). reflexivity. }
Qed.
