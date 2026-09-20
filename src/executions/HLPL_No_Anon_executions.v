(** * Mechanized_LLBC.executions.HLPL_executions : Execution HLPL programs. *)
(** TODO: split into severel files, one for each execution. *)
From Stdlib Require Import List.
Import ListNotations.
From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.

Require Import PathToSubtree lang HLPL_No_Anon.

Fixpoint decide_not_value_contains (P : nodes -> bool) v :=
  negb (P (get_node v)) &&
    match v with
      loc(l, w) => decide_not_value_contains P w
    | VTuple vl => decide_not_value_list_contains P vl
    | _ => true end
with decide_not_value_list_contains (P : nodes -> bool) vl :=
  match vl with
  | VNil => true
  | VCons v vl' => decide_not_value_contains P v && decide_not_value_list_contains P vl'
  end.

Lemma decide_not_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  decide_not_value_contains P v = true -> not_value_contains H v
with decide_not_value_list_contains_correct H P vl
       (H_implies_P : forall vl, H vl -> P vl = true) :
  decide_not_value_list_contains P vl = true ->
  ValueList.Forall (not_value_contains H) vl.
Proof.
  intro decide_is_true. induction v.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    * cbn in *. intros G%H_implies_P.
      apply andb_prop in decide_is_true as (? & _). rewrite G in H0. discriminate.
    * rewrite nth_error_nil in H0. discriminate.
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
  - apply not_value_list_contains_forall. split.
    + apply andb_prop in decide_is_true as (?%negb_true_iff & _).
      intros ?%H_implies_P. congruence.
    + eapply decide_not_value_list_contains_correct ; eauto.
      induction t.
      * reflexivity.
      * simpl in *. by apply andb_prop in decide_is_true as (_ & (-> & ->)%andb_prop).
  - induction vl ; simpl ; [intros | intros (? & ?)%andb_prop ] ; constructor.
    + eapply decide_not_value_contains_correct ; eassumption.
    + apply IHvl ; auto.
Qed.

Definition decide_is_bot v := match v with NBottom => true | _ => false end.

Corollary decide_not_contains_bot v (H : decide_not_value_contains decide_is_bot v = true) :
  not_contains_bot v.
Proof. eapply decide_not_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Definition decide_not_state_contains (P : nodes -> bool) (S : state) :=
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

Definition decide_is_loc v := match v with nloc(l) => true | _ => false end.
Definition decide_is_loc_id l v :=
  match v with
  | nloc(l') | nptr(l') => Pos.eqb l l'
  | _ => false
  end.


Lemma decide_is_fresh S l (H : decide_not_state_contains (decide_is_loc_id l) S = true) :
  is_fresh l S.
  Proof.
    eapply decide_state_contains_correct; try eassumption.
    intros c G. destruct c; inversion G; apply Pos.eqb_refl.
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
Notation l1 := 1%positive.
Notation l2 := 2%positive.

Open Scope rtype_scope.

Definition prog :=
  ASSIGN (x, nil, TInt) <- Use (INT 3) ;;
  ASSIGN (y, nil, TInt) <- &mut (1%positive, nil, TInt).

Definition main : statement :=
  ASSIGN (a, [], TInt) <- Use (INT 1983) ;;
  ASSIGN (b, [], TInt) <- Use (INT 1986) ;;
  ASSIGN (c, [], TInt) <- &mut (a, [], TInt);;
  ASSIGN (d, [], TInt) <- &mut (c, [Deref], TInt);;
  ASSIGN (c, [], TInt) <- &mut (b, [], TInt);;
  ASSIGN (d, [Deref], TInt) <- Use (INT 58) ;;
  Nop
.
Definition main_pair : statement :=
  ASSIGN (a, [], t[ TInt ; TInt]) <- Use (Tuple [ INT 667 ; INT 1986 ]) ;;
  ASSIGN (b, [], TInt) <- Use (Move (a, [ Field (0)], TInt)) ;;
  ASSIGN (c, [], TRef TInt) <- &mut (a, [Field (1)], TInt);;
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

  Definition empty_state : state :=
    {| vars := {[ x := VInt 0; y := VInt 0 ]} ; anons := PEmpty |}.
  Definition empty_state' : state :=
    {|
      vars := {[ a := bot; b := bot; c := bot; d := bot ]} ;
      anons := PEmpty
    |}.


(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
  Ltac eval_var :=
    split; [eexists; split; [reflexivity | constructor] | ].


  Goal exists final_state, empty_state |-{stmt} prog => rUnit, final_state.
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      + repeat constructor.
      + apply Store ; eval_var; constructor.
    }
    {
      eapply E_Assign.
      + simpl. eapply E_Pointer_Fresh with (l := l1).
        * eval_var; constructor.
        * apply decide_is_fresh. easy.
      + apply Store ; eval_var; constructor.
    }
  Qed.

  Goal exists final_state, empty_state' |-{stmt} main => rUnit, final_state.
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - eapply E_Pointer_Fresh with (l := l1); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Loc with (pi := (encode_var 1, [])).
        * repeat econstructor; try easy.
        * reflexivity.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Fresh with (l := l2); repeat constructor.
        * eexists ; split; constructor; easy. (* TODO: why validity does not solve this goal? *)
        * apply decide_is_fresh. easy.
      - apply Store ; eval_var; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat constructor.
      - apply Store.
        * repeat constructor.
          ** eexists; split; constructor.
          ** simpl. apply Eval_cons with (q := (encode_var 1, []));
             repeat econstructor; easy.
    }
    apply E_Nop.
    Qed.

  Goal exists final_state, empty_state' |-{stmt} main_pair => rUnit, final_state.
    eexists.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat econstructor.
      - apply Store ; repeat constructor.
        simpl. eexists; split; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - repeat econstructor.
        * apply decide_not_value_contains_correct with (P := decide_is_loc).
          ** intros. inversion H; subst; reflexivity.
          ** reflexivity.
        * apply decide_not_contains_bot; reflexivity.
      - apply Store ; repeat constructor. simpl. eexists; split; constructor.
    }
    simpl_state.
    eapply E_Seq_Unit.
    {
      eapply E_Assign.
      - apply E_Pointer_Fresh with (l := l1).
        * repeat econstructor.
        * apply decide_is_fresh; reflexivity.
      - apply Store ; repeat constructor. simpl. eexists; split; constructor.
    }
    apply E_Nop.
    Qed.
End SemTest.
