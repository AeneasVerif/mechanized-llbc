Require Import base.
Require Import lang.
Require Import SimulationUtils.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PeanoNat Lia.
(* Notation conflict between stdpp's `+++` and our `+++`. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.
Require Import OptionMonad.

Inductive LLBC_plus_val :=
| LLBC_plus_bot
| LLBC_plus_int (n : nat) (* TODO: use Aeneas integer types? *)
| LLBC_plus_mut_loan (l : loan_id)
| LLBC_plus_mut_borrow (l : loan_id) (v : LLBC_plus_val)
(*
| LLBC_plus_shr_loan (l : loan_id) (v : LLBC_plus_val)
| LLBC_plus_shr_borrow (l : loan_id)
 *)
(* | LLBC_plus_pair (v0 : LLBC_plus_val) (v1 : LLBC_plus_val) *)
(* Note: symbolic values should be parameterized by a type, when we introduce other datatypes than
   integers. *)
| LLBC_plus_symbolic
.

Variant LLBC_plus_nodes :=
| LLBC_plus_botC
| LLBC_plus_intC (n : nat)
| LLBC_plus_mut_loanC (l : loan_id)
| LLBC_plus_mut_borrowC (l : loan_id)
| LLBC_plus_symbolicC
.

Instance EqDecision_LLBC_plus_nodes : EqDecision LLBC_plus_nodes.
Proof. unfold RelDecision, Decision. repeat decide equality. Qed.

Definition LLBC_plus_arity c := match c with
| LLBC_plus_botC => 0
| LLBC_plus_intC _ => 0
| LLBC_plus_mut_loanC _ => 0
| LLBC_plus_mut_borrowC _ => 1
| LLBC_plus_symbolicC => 0
end.

Definition LLBC_plus_get_node v := match v with
| LLBC_plus_bot => LLBC_plus_botC
| LLBC_plus_int n => LLBC_plus_intC n
| LLBC_plus_mut_loan l => LLBC_plus_mut_loanC l
| LLBC_plus_mut_borrow l _ => LLBC_plus_mut_borrowC l
| LLBC_plus_symbolic => LLBC_plus_symbolicC
end.

Definition LLBC_plus_children v := match v with
| LLBC_plus_bot => []
| LLBC_plus_int _ => []
| LLBC_plus_mut_loan _ => []
| LLBC_plus_mut_borrow _ v => [v]
| LLBC_plus_symbolic => []
end.

Definition LLBC_plus_fold c vs := match c, vs with
| LLBC_plus_intC n, [] => LLBC_plus_int n
| LLBC_plus_mut_loanC l, [] => LLBC_plus_mut_loan l
| LLBC_plus_mut_borrowC l, [v] => LLBC_plus_mut_borrow l v
| LLBC_plus_symbolicC, [] => LLBC_plus_symbolic
| _, _ => LLBC_plus_bot
end.

Fixpoint LLBC_plus_weight node_weight v :=
  match v with
  | LLBC_plus_mut_borrow l v => node_weight (LLBC_plus_mut_borrowC l) + LLBC_plus_weight node_weight v
  | v => node_weight (LLBC_plus_get_node v)
end.

Program Instance ValueLLBC_plus : Value LLBC_plus_val LLBC_plus_nodes := {
  arity := LLBC_plus_arity;
  get_node := LLBC_plus_get_node;
  children := LLBC_plus_children;
  fold_value := LLBC_plus_fold;
  vweight := LLBC_plus_weight;
  bot := LLBC_plus_bot;
}.
Next Obligation. destruct v; reflexivity. Qed.
Next Obligation.
  intros [] [] eq_nodes eq_children; inversion eq_nodes; inversion eq_children; reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation.
  intros [] ? H; (rewrite length_zero_iff_nil in H; rewrite H) ||
                  destruct (length_1_is_singleton H) as [? ->];
                  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros ? []; cbn; lia. Qed.

Record LLBC_plus_state := {
  vars : Pmap LLBC_plus_val;
  anons : Pmap LLBC_plus_val;
  abstractions : Pmap (Pmap LLBC_plus_val);
}.

Definition encode_var (x : var) :=
  encode (A := _ + positive * positive) (inl (encode (A := _ + anon) (inl x))).
Definition encode_anon (a : anon) :=
  encode (A := _ + positive * positive) (inl (encode (A := var + _) (inr a))).
Definition encode_abstraction (x : positive * positive) := encode (A := positive + _) (inr x).

Lemma encode_anon_inj : Inj eq eq encode_anon.
Proof.
  unfold encode_anon. intros ? ? H%encode_inj. inversion H. apply encode_inj. congruence.
Qed.

Instance encode_abstraction_inj : Inj eq eq encode_abstraction.
Proof.
  unfold encode_abstraction. intros x y H. eapply (f_equal decode') in H.
  rewrite !decode'_encode in H. congruence.
Qed.

Program Instance IsState : State LLBC_plus_state LLBC_plus_val := {
  get_map S := sum_maps (sum_maps (vars S) (anons S)) (flatten (abstractions S));

  (* The flatten function in not injective. For example, R and R<[A := empty]> have the same
   * flattening. An empty region abstraction and a non-existant region abstraction can't be
   * distinguished. Therefore, for the axiom `state_eq_ext` to be true, we need the set of region
   * abstractions identifiers as extra information. *)
  extra := Pset;
  get_extra S := dom (abstractions S);

  alter_at_accessor f a S :=
    match decode' (A := positive + positive * positive) a with
    | Some (inl a) =>
        match decode' (A := var + anon) a with
        | Some (inl x) => {| vars := alter f x (vars S); anons := anons S; abstractions := abstractions S|}
        | Some (inr a) => {| vars := vars S; anons := alter f a (anons S); abstractions := abstractions S|}
        | None => S
        end
    | Some (inr (i, j)) => {| vars := vars S; anons := anons S;
                              abstractions := alter (fun r => alter f j r) i (abstractions S)|}
    | None => S
    end;

  anon_accessor := encode_anon;
  accessor_anon x :=
    match decode (A := positive + positive * positive) x with
    | Some (inl y) =>
        match decode (A := var + anon) y with
        | Some (inr a) => Some a
        | Some (inl _) => None
        | None => None
        end
    | Some (inr _) => None
    | None => None
    end;
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S); abstractions := abstractions S|};
}.
Next Obligation.
  intros ? ? y. cbn. destruct (decode' y) as [[z | (i & j)] | ] eqn:H.
  - destruct (decode' z) as [[? | ?] | ]; reflexivity.
  - cbn. apply dom_alter_L.
  - reflexivity.
Qed.
Next Obligation.
  intros ? ? y. cbn. destruct (decode' y) as [[z | (i & j)] | ] eqn:H.
  - rewrite decode'_is_Some in H.
    destruct (decode' z) as [[x | a] | ] eqn:G.
    + cbn. rewrite decode'_is_Some in G. rewrite <-H, <-G, <- !sum_maps_alter_inl.
      reflexivity.
    + cbn. rewrite decode'_is_Some in G.
      rewrite <-H, <-G, <-sum_maps_alter_inr, <-sum_maps_alter_inl. reflexivity.
    + symmetry. apply map_alter_not_in_domain. rewrite <-H, sum_maps_lookup_l.
      now apply sum_maps_lookup_None.
  - cbn. rewrite decode'_is_Some in H. rewrite <-H,  sum_maps_alter_inr, alter_flatten. reflexivity.
  - symmetry. apply map_alter_not_in_domain, sum_maps_lookup_None. assumption.
Qed.
Next Obligation.
  intros [? ? R0] [? ? R1]. cbn. intros ((-> & ->)%sum_maps_eq & ?)%sum_maps_eq ?. f_equal.
  apply map_eq. intros i. destruct (decide (elem_of i (dom R0))) as [e | ].
  - assert (elem_of i (dom R1)) as (b & Ha)%elem_of_dom by congruence.
    apply elem_of_dom in e. destruct e as (a & Hb). rewrite Ha, Hb. f_equal.
    apply map_eq. intros j.
    apply lookup_Some_flatten with (j := j) in Ha. apply lookup_Some_flatten with (j := j) in Hb.
    congruence.
  - assert (~(elem_of i (dom R1))) by congruence. rewrite not_elem_of_dom in * |-. congruence.
Qed.
Next Obligation.
  intros. cbn. unfold encode_anon. rewrite sum_maps_insert_inl, sum_maps_insert_inr. reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. unfold encode_anon. rewrite !decode_encode. reflexivity. Qed.

Lemma get_at_var S x : get_at_accessor S (encode_var x) = lookup x (vars S).
Proof. unfold get_map, encode_var. cbn. rewrite !sum_maps_lookup_l. reflexivity. Qed.

Lemma get_at_anon S a : get_at_accessor S (anon_accessor a) = lookup a (anons S).
Proof.
  unfold get_map, anon_accessor. cbn. unfold encode_anon.
  rewrite sum_maps_lookup_l, sum_maps_lookup_r. reflexivity.
Qed.

Lemma get_at_abstraction S i j : get_at_accessor S (encode_abstraction (i, j)) =
  mbind (lookup j) (lookup i (abstractions S)).
Proof.
  unfold get_map, encode_abstraction. cbn. rewrite sum_maps_lookup_r. apply lookup_flatten.
Qed.

Lemma get_at_abstraction' S i j A (H : lookup i (abstractions S) = Some A) :
  get_at_accessor S (encode_abstraction (i, j)) = lookup j A.
Proof. rewrite get_at_abstraction, H. reflexivity. Qed.

Variant get_at_accessor_rel S : positive -> Prop :=
  | GetAtVar x v : lookup x (vars S) = Some v -> get_at_accessor_rel S (encode_var x)
  | GetAtAnon a v : lookup a (anons S) = Some v -> get_at_accessor_rel S (anon_accessor a)
  | GetAtAbstraction i j A v : lookup i (abstractions S) = Some A -> lookup j A = Some v ->
      get_at_accessor_rel S (encode_abstraction (i, j))
.

(* TODO: redo proofs with this lemma. *)
Lemma get_at_accessor_is_Some S acc :
  is_Some (get_at_accessor S acc) -> get_at_accessor_rel S acc.
Proof.
  intros [(i & -> & H) | ((i & j) & -> & (? & H))]%sum_maps_is_Some.
  - apply sum_maps_is_Some in H. destruct H as [(x & -> & (? & ?)) | (a & -> & (? & ?))].
    + eapply GetAtVar. eassumption.
    + eapply GetAtAnon. eassumption.
  - rewrite lookup_flatten, bind_Some in H. destruct H as (A & ? & ?).
    eapply GetAtAbstraction with (A := A); eauto.
Qed.

Declare Scope llbc_plus_scope.
Delimit Scope llbc_plus_scope with llbc.

(* TODO: move? *)
(* TODO: set every priority to 0? *)
Reserved Notation "'loan^m' ( l )" (at level 0).
Reserved Notation "'borrow^m' ( l , v )" (at level 0, l at next level, v at next level).
Reserved Notation "'loc' ( l , v )" (at level 0, l at next level, v at next level). (* TODO: unused in LLBC_plus.v *)
Reserved Notation "'ptr' ( l )" (at level 0). (* TODO: unused in LLBC_plus.v *)

Reserved Notation "'botC'" (at level 0).
Reserved Notation "'loanC^m'( l )" (at level 0).
Reserved Notation "'borrow^m' ( l )" (at level 0, l at next level).
Reserved Notation "'locC' ( l , )" (at level 0, l at next level). (* TODO: unused in LLBC_plus.v *)
Reserved Notation "'ptrC' ( l )" (at level 0). (* TODO: unused in LLBC_plus.v *)

(* Notation "'bot'" := LLBC_plus_bot: llbc_plus_scope. *)
Notation "'loan^m' ( l )" := (LLBC_plus_mut_loan l) : llbc_plus_scope.
Notation "'borrow^m' ( l  , v )" := (LLBC_plus_mut_borrow l v) : llbc_plus_scope.

Notation "'botC'" := LLBC_plus_botC: llbc_plus_scope.
Notation "'loanC^m' ( l )" := (LLBC_plus_mut_loanC l) : llbc_plus_scope.
Notation "'borrowC^m' ( l )" := (LLBC_plus_mut_borrowC l) : llbc_plus_scope.

(* Bind Scope llbc_plus_scope with LLBC_plus_val. *)
Open Scope llbc_plus_scope.

Inductive eval_proj (S : LLBC_plus_state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| Eval_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = borrowC^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : LLBC_plus_state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| Eval_nil pi : eval_path S perm [] pi pi
| Eval_cons proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst p), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd p) pi_0 pi.

Local Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi) (at level 50).

Lemma eval_proj_valid S perm proj q r (H : eval_proj S perm proj q r) : valid_spath S r.
Proof.
  induction H.
  - apply valid_spath_app. split.
    + apply get_not_bot_valid_spath. destruct (S.[q]); discriminate.
    + destruct (S.[q]); inversion get_q. econstructor; reflexivity || constructor.
Qed.

Lemma eval_path_valid (s : LLBC_plus_state) P perm q r
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

Variant is_loan : LLBC_plus_nodes -> Prop :=
| IsLoan_MutLoan l : is_loan (loanC^m(l)).
Hint Constructors is_loan : spath.
Definition not_contains_loan := not_value_contains is_loan.
Hint Unfold not_contains_loan : spath.
Hint Extern 0 (~is_loan _) => intro; easy : spath.

Variant is_borrow : LLBC_plus_nodes -> Prop :=
| IsLoan_MutBorrow l : is_borrow (borrowC^m(l)).
Hint Constructors is_borrow : spath.
Definition not_contains_borrow := not_value_contains is_borrow.
Hint Unfold not_contains_borrow : spath.
Hint Extern 0 (~is_borrow _) => intro; easy : spath.

Definition not_contains_bot v :=
  (not_value_contains (fun c => c = botC) v).
Hint Unfold not_contains_bot : spath.
Hint Extern 0 (_ <> botC) => discriminate : spath.

Lemma not_contains_bot_valid S sp : not_contains_bot (S.[sp]) -> valid_spath S sp.
Proof.
  intros H. specialize (H []). cbn in H. apply get_not_bot_valid_spath.
  intros G. apply H. constructor. rewrite G. reflexivity.
Qed.
Hint Resolve not_contains_bot_valid : spath.

Definition not_contains_symbolic v :=
  (not_value_contains (fun c => c = LLBC_plus_symbolicC) v).
Hint Unfold not_contains_symbolic : spath.
Hint Extern 0 (_ <> LLBC_plus_symbolicC) => discriminate : spath.

Variant is_mut_borrow : LLBC_plus_nodes -> Prop :=
| IsMutBorrow_MutBorrow l : is_mut_borrow (borrowC^m(l)).
Notation not_contains_outer_loan := (not_contains_outer is_mut_borrow is_loan).

Lemma loan_is_not_bot x : is_loan x -> x <> botC. Proof. intros [ ]; discriminate. Qed.

Inductive copy_val : LLBC_plus_val -> LLBC_plus_val -> Prop :=
| Copy_val_int (n : nat) : copy_val (LLBC_plus_int n) (LLBC_plus_int n)
(* Note: copies should only be allowed on copiable types. *)
| Copy_val_symbolic : copy_val LLBC_plus_symbolic LLBC_plus_symbolic
.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> LLBC_plus_state -> (LLBC_plus_val * LLBC_plus_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (LLBC_plus_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi (Heval : eval_place S Mov p pi)
    (move_no_loan : not_contains_loan (S.[pi])) (move_no_bot : not_contains_bot (S.[pi])) :
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S |-{op} op => r" := (eval_operand op S r).

Definition get_loan_id c :=
  match c with
  | loanC^m(l) => Some l
  | borrowC^m(l) => Some l
  | _ => None
  end.

Notation is_fresh l S := (not_state_contains (fun c => get_loan_id c = Some l) S).
Local Reserved Notation "S  |-{rv}  rv  =>  r" (at level 50).

Variant eval_rvalue : rvalue -> LLBC_plus_state -> (LLBC_plus_val * LLBC_plus_state) -> Prop :=
  | Eval_just op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Just op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | Eval_bin_op S S' S'' op_l op_r m n :
      (S |-{op} op_l => (LLBC_plus_int m, S')) ->
      (S' |-{op} op_r => (LLBC_plus_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => ((LLBC_plus_int (m + n)), S'')
  (* Additional rules to evaluate the "+" operator with a symbolic value. *)
  | Eval_bin_op_symbolic_int S S' S'' op_l op_r n :
      (S |-{op} op_l => (LLBC_plus_symbolic, S')) ->
      (S' |-{op} op_r => (LLBC_plus_int n, S'')) ->
      S |-{rv} (BinOp op_l op_r) => (LLBC_plus_symbolic, S'')
  | Eval_bin_op_int_symbolic S S' S'' op_l op_r m :
      (S |-{op} op_l => (LLBC_plus_int m, S')) ->
      (S' |-{op} op_r => (LLBC_plus_symbolic, S'')) ->
      S |-{rv} (BinOp op_l op_r) => (LLBC_plus_symbolic, S'')
  | Eval_bin_op_symbolic_symbolic S S' S'' op_l op_r :
      (S |-{op} op_l => (LLBC_plus_symbolic, S')) ->
      (S' |-{op} op_r => (LLBC_plus_symbolic, S'')) ->
      S |-{rv} (BinOp op_l op_r) => (LLBC_plus_symbolic, S'')

  | Eval_mut_borrow S p pi l : S |-{p} p =>^{Mut} pi ->
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) -> is_fresh l S ->
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Notation not_in_borrow := (no_ancestor is_mut_borrow).

(* Note: I'm not satisfied with the name choices.
 *)
Definition in_abstraction i x := exists j, x = encode_abstraction (i, j).
Definition not_in_abstraction (p : spath) := forall i, ~in_abstraction i (fst p).

Instance Decidable_in_abstraction i x : Decision (in_abstraction i x).
Proof.
  unfold in_abstraction, encode_abstraction.
  destruct (decode' (A := positive + positive * positive) x) as [[ | (i' & j)] | ] eqn:EQN.
  - right. intros (j & H). rewrite H, decode'_encode in EQN. discriminate.
  - destruct (decide (i = i')) as [<- | ].
    + left. exists j. apply decode'_is_Some in EQN. congruence.
    + right. intros (? & H). rewrite H, decode'_encode in EQN. congruence.
  - right. intros (? & H). rewrite H, decode'_encode in EQN. discriminate.
Qed.

Lemma var_not_in_abstraction p x : fst p = encode_var x -> not_in_abstraction p.
Proof.
  unfold not_in_abstraction, in_abstraction. intros H ? (? & G).
  rewrite G in H. inversion H.
Qed.

Lemma anon_not_in_abstraction p a : fst p = encode_anon a -> not_in_abstraction p.
Proof.
  unfold not_in_abstraction, in_abstraction. intros H ? (? & G).
  rewrite G in H. inversion H.
Qed.

Definition add_abstraction S i A :=
  {|vars := vars S; anons := anons S; abstractions := insert i A (abstractions S)|}.

Notation "S ,,, i |-> A" := (add_abstraction S i A) (at level 50, left associativity).

Definition fresh_abstraction S i := lookup i (abstractions S) = None.

Notation abstraction_contains_value S i j v :=
  (get_at_accessor S (encode_abstraction (i, j)) = Some v).

(* Remove the value at j in the region abstraction at i, if this value exists. *)
Definition remove_abstraction_value S i j :=
  {|vars := vars S; anons := anons S; abstractions := alter (delete j) i (abstractions S)|}.

Lemma get_at_accessor_add_abstraction S i j A :
  get_at_accessor (S,,, i |-> A) (encode_abstraction (i, j)) = lookup j A.
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_lookup_r.
  rewrite <-insert_delete_insert, flatten_insert by now simpl_map.
  rewrite lookup_union_l.
  - rewrite lookup_kmap by typeclasses eauto. reflexivity.
  - apply lookup_None_flatten. simpl_map. reflexivity.
Qed.

(* The hypothesis `fresh_abstraction S i` is not necessary, we're going to remove it. *)
Lemma _get_at_accessor_add_abstraction_notin S i A x (fresh_i : fresh_abstraction S i)
  (H : ~in_abstraction i x) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  unfold get_map. cbn. 
  rewrite flatten_insert' by assumption. rewrite sum_maps_union.
  rewrite lookup_union_l; [reflexivity | ].
  rewrite eq_None_not_Some. rewrite lookup_kmap_is_Some by typeclasses eauto.
  intros (p & ? & G). rewrite lookup_kmap_is_Some in G by typeclasses eauto.
  destruct G as (j & -> & _). eapply H. firstorder.
Qed.

Definition remove_abstraction i S :=
  {|vars := vars S; anons := anons S; abstractions := delete i (abstractions S)|}.

Lemma add_remove_abstraction i A S (H : lookup i (abstractions S) = Some A) :
  (remove_abstraction i S),,, i |-> A = S.
Proof.
  unfold add_abstraction, remove_abstraction.
  destruct S. cbn. f_equal. apply insert_delete in H. exact H.
Qed.

Lemma remove_add_abstraction i A S (H : fresh_abstraction S i) :
  remove_abstraction i (S,,, i |-> A) = S.
Proof.
  unfold add_abstraction, remove_abstraction.
  destruct S. cbn. f_equal. apply delete_insert. assumption.
Qed.

Lemma remove_add_abstraction_ne i j A S :
  i <> j -> remove_abstraction i (S,,, j |-> A) = remove_abstraction i S,,, j |-> A.
Proof.
  unfold add_abstraction, remove_abstraction.
  intros ?. destruct S. cbn. f_equal. apply delete_insert_ne. assumption.
Qed.

Lemma add_remove_add_abstraction S i A : (remove_abstraction i S),,, i |-> A = S,,, i |-> A.
Proof. unfold add_abstraction, remove_abstraction. cbn. f_equal. apply insert_delete_insert. Qed.

Lemma get_at_accessor_add_abstraction_notin S i A x (H : ~in_abstraction i x) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN at 2. rewrite <-add_remove_add_abstraction.
    rewrite !_get_at_accessor_add_abstraction_notin; auto; apply lookup_delete.
  - apply _get_at_accessor_add_abstraction_notin; assumption.
Qed.

Lemma sget_add_abstraction S i A p : ~in_abstraction i (fst p) -> (S,,, i |-> A).[p] = S.[p].
Proof. intros H. unfold sget. rewrite get_at_accessor_add_abstraction_notin; auto. Qed.

Lemma get_extra_add_abstraction S i A :
  get_extra (S,,, i |-> A) = (union (singleton i) (get_extra S)).
Proof. unfold get_extra. cbn. rewrite dom_insert_L. reflexivity. Qed.

Lemma sset_add_abstraction S i A p v :
  ~in_abstraction i (fst p) -> (S,,, i |-> A).[p <- v] = S.[p <- v],,, i |-> A.
Proof.
  intros ?. unfold sset. apply state_eq_ext.
  - apply map_eq. intros x.
    destruct (decide (fst p = x)) as [<- | ].
    + rewrite get_map_alter, lookup_alter.
      rewrite !get_at_accessor_add_abstraction_notin by assumption.
      rewrite get_map_alter, lookup_alter. reflexivity.
    + rewrite get_map_alter, lookup_alter_ne by auto.
      destruct (decide (in_abstraction i x)) as [(j & ->) | ].
      * rewrite !get_at_accessor_add_abstraction. reflexivity.
      * rewrite !get_at_accessor_add_abstraction_notin by assumption.
        rewrite get_map_alter, lookup_alter_ne by assumption. reflexivity.
  - rewrite get_extra_alter, !get_extra_add_abstraction, get_extra_alter. reflexivity.
Qed.

Lemma fresh_anon_add_abstraction S a i A : fresh_anon (S,,, i |-> A) a <-> fresh_anon S a.
Proof. unfold fresh_anon. rewrite !get_at_anon. reflexivity. Qed.

Hint Resolve<- fresh_anon_add_abstraction : spath.
(* Hint Rewrite fresh_anon_add_abstraction : spath. *)

(* TODO: Hint? *)
Lemma fresh_anon_remove_abstraction_value S a i j :
  fresh_anon (remove_abstraction_value S i j) a <-> fresh_anon S a.
Proof. unfold fresh_anon. rewrite !get_at_anon. reflexivity. Qed.

Lemma fresh_abstraction_add_abstraction S i j A :
  fresh_abstraction S i -> fresh_abstraction S j -> i <> j ->
  fresh_abstraction (S,,, i |-> A) j.
Proof. unfold fresh_abstraction, add_abstraction. cbn. intros. simpl_map. assumption. Qed.
Hint Resolve fresh_abstraction_add_abstraction : spath.

Lemma fresh_abstraction_add_abstraction_rev S i j A :
  fresh_abstraction (S,,, i |-> A) j -> fresh_abstraction S j /\ i <> j.
Proof. unfold fresh_abstraction, add_abstraction. cbn. now rewrite lookup_insert_None. Qed.

Lemma fresh_abstraction_sset S p v i :
  fresh_abstraction S i <-> fresh_abstraction (S.[p <- v]) i.
Proof.
  unfold fresh_abstraction. rewrite<-!not_elem_of_dom.
  replace (dom (abstractions S)) with (get_extra S) by reflexivity.
  replace (dom (abstractions (S.[p <- v]))) with (get_extra (S.[p <- v])) by reflexivity.
  unfold sset. rewrite get_extra_alter. reflexivity.
Qed.

Lemma fresh_abstraction_add_anon S a v i :
  fresh_abstraction S i <-> fresh_abstraction (S,, a |-> v) i.
Proof. split; intros H; exact H. Qed.

Hint Resolve-> fresh_abstraction_sset : spath.
Hint Resolve-> fresh_abstraction_add_anon : spath.

Hint Rewrite sget_add_abstraction using auto; fail : spath.
Hint Rewrite sset_add_abstraction using auto with spath; fail : spath.

Lemma abstractions_remove_abstraction_value S i j :
  flatten (abstractions (remove_abstraction_value S i j)) =
  delete (i, j) (flatten (abstractions S)).
Proof.
  unfold remove_abstraction_value. cbn.
  apply map_eq. intros (a & b). destruct (decide (i = a)) as [<- | ].
  - rewrite lookup_flatten. rewrite lookup_alter.
    rewrite option_fmap_bind.
    destruct (decide (j = b)) as [<- | ].
    + rewrite lookup_delete.
      erewrite option_bind_ext_fun by (intros ?; apply lookup_delete).
      destruct (lookup i (abstractions S)); reflexivity.
    + rewrite lookup_delete_ne by congruence. rewrite lookup_flatten.
      apply option_bind_ext_fun. intros ?. apply lookup_delete_ne. assumption.
  - rewrite lookup_delete_ne by congruence. rewrite !lookup_flatten.
    rewrite lookup_alter_ne by assumption. reflexivity.
Qed.

Lemma get_map_remove_abstraction_value S i j :
  get_map (remove_abstraction_value S i j) = delete (encode_abstraction (i, j)) (get_map S).
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_delete_inr. rewrite <-abstractions_remove_abstraction_value. reflexivity.
Qed.

Lemma get_extra_remove_abstraction_value S i j :
  get_extra (remove_abstraction_value S i j) = get_extra S.
Proof. unfold get_extra. cbn. rewrite dom_alter_L. reflexivity. Qed.

Lemma sget_remove_abstraction_value S i j p (H : fst p <> encode_abstraction (i, j)) :
  (remove_abstraction_value S i j).[p] = S.[p].
Proof. unfold sget. rewrite get_map_remove_abstraction_value. simpl_map. reflexivity. Qed.

Lemma sset_remove_abstraction_value S i j p v (H : fst p <> encode_abstraction (i, j)) :
  remove_abstraction_value (S.[p <-v]) i j = (remove_abstraction_value S i j).[p <- v].
Proof.
  apply state_eq_ext.
  - unfold sset. rewrite get_map_remove_abstraction_value. rewrite !get_map_alter.
    rewrite get_map_remove_abstraction_value. apply delete_alter_ne. congruence.
  - unfold sset. rewrite get_extra_alter, !get_extra_remove_abstraction_value, get_extra_alter.
    reflexivity.
Qed.

Hint Rewrite sget_remove_abstraction_value using assumption : spath.
Hint Rewrite sset_remove_abstraction_value using assumption : spath.

Lemma add_abstraction_add_anon S a v i A : (S,, a |-> v),,, i |-> A = (S,,, i |-> A),, a |-> v.
Proof. reflexivity. Qed.

Lemma remvoe_abstraction_value_add_anon S a v i j :
  remove_abstraction_value (S,, a |-> v) i j = (remove_abstraction_value S i j),, a |-> v.
Proof. reflexivity. Qed.

Hint Rewrite add_abstraction_add_anon : spath.
Hint Rewrite remvoe_abstraction_value_add_anon : spath.

(* Used to change a mutable borrow from borrow^m(l', v) to borrow^m(l, v). *)
Notation rename_mut_borrow S sp l := (S.[sp <- borrow^m(l, S.[sp +++ [0] ])]).

Variant is_integer : LLBC_plus_val -> Prop :=
  | Symbolic_is_integer : is_integer LLBC_plus_symbolic
  | Integer_is_integer n : is_integer (LLBC_plus_int n).

Variant add_anons : LLBC_plus_state -> Pmap LLBC_plus_val -> LLBC_plus_state -> Prop :=
  | AddAnons S A anons' : union_maps (anons S) A anons' ->
      add_anons S A {|vars := vars S; anons := anons'; abstractions := abstractions S|}.

(* Note: we use the variable names i' and j' instead of i and j that are used for leq_state_base.
 * We are also using the name A' instead of A, B or C for the region abstractions.
 *)
Variant reorg : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Ends a borrow when it's not in an abstraction: *)
| Reorg_end_borrow_m S (p q : spath) l :
    disj p q -> get_node (S.[p]) = loanC^m(l) -> get_node (S.[q]) = borrowC^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    not_in_abstraction p -> not_in_abstraction q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
(* Ends a borrow when it's in an abstraction: *)
(* The value that is transferred back, S.[q +++ [0]], has to be of integer type. *)
| Reorg_end_borrow_m_in_abstraction S q i' j' l :
    fst q <> encode_abstraction (i', j') -> abstraction_contains_value S i' j' loan^m(l) ->
    get_node (S.[q]) = borrowC^m(l) -> is_integer (S.[q +++ [0] ]) ->
    not_in_borrow S q -> not_in_abstraction q ->
    reorg S ((remove_abstraction_value S i' j').[q <- bot])
(* q refers to a path in abstraction A, at index j. *)
| Reorg_end_abstraction S i' A' S'
    (fresh_i : fresh_abstraction S i')
    (A_no_loans : map_Forall (fun _ => not_contains_loan) A')
    (Hadd_anons : add_anons S A' S') : reorg (S,,, i' |-> A') S'
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : LLBC_plus_val * LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : (S,, a |-> v) |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp])) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(* When introducing non-terminating features (loops or recursivity), the signature of the relation
   is going to be:
   LLBC_plus_state -> statement -> nat -> Option (statement_result * LLBC_plus_state) -> Prop
*)
Reserved Notation "S  |-{stmt}  stmt  =>  r , S'" (at level 50).
Inductive eval_stmt : statement -> statement_result -> LLBC_plus_state -> LLBC_plus_state -> Prop :=
  | Eval_nop S : S |-{stmt} Nop => rUnit, S
  | Eval_seq_unit S0 S1 S2 stmt_l stmt_r r (eval_stmt_l : S0 |-{stmt} stmt_l => rUnit, S1)
      (eval_stmt_r : S1 |-{stmt} stmt_r => r, S2) :  S0 |-{stmt} stmt_l;; stmt_r => r, S2
  | Eval_seq_panic S0 S1 stmt_l stmt_r (eval_stmt_l : S0 |-{stmt} stmt_l => rPanic, S1) :
      S0 |-{stmt} stmt_l;; stmt_r => rPanic, S1
  | Eval_assign S vS' S'' p rv : (S |-{rv} rv => vS') -> store p vS' S'' ->
      S |-{stmt} ASSIGN p <- rv => rUnit, S''
  | Eval_reorg S0 S1 S2 stmt r (Hreorg : reorg^* S0 S1) (Heval : S1 |-{stmt} stmt => r, S2) :
      S0 |-{stmt} stmt => r, S2
where "S |-{stmt} stmt => r , S'" := (eval_stmt stmt r S S').

(* A version of to-abs that is limited compared to the paper. Currently, we can only turn into a
 * region abstraction a value of the form:
 * - borrow^m l σ (with σ a symbolic value)
 * - borrow^m l0 (loan^m l1)
 * Consequently, a single region abstraction is created.
 *)
Variant to_abs : LLBC_plus_val -> Pmap LLBC_plus_val -> Prop :=
| ToAbs_MutReborrow l0 l1:
    to_abs (borrow^m(l0, loan^m(l1)))
           ({[1%positive := (borrow^m(l0, LLBC_plus_symbolic)); 2%positive := loan^m(l1)]})%stdpp
| ToAbs_MutBorrow l v (Hv : is_integer v):
    to_abs (borrow^m(l, v)) ({[1%positive := (borrow^m(l, LLBC_plus_symbolic))]})%stdpp
.

Inductive remove_loans A B : Pmap LLBC_plus_val -> Pmap LLBC_plus_val-> Prop :=
  | Remove_nothing : remove_loans A B A B
  | Remove_MutLoan A' B' i j l (H : remove_loans A B A' B') :
      lookup i A' = Some (loan^m(l)) -> lookup j B' = Some (borrow^m(l, LLBC_plus_symbolic)) ->
      remove_loans A B (delete i A') (delete j B')
.

Definition merge_abstractions A B C := exists A0 B0, remove_loans A B A0 B0 /\ union_maps A0 B0 C.

Lemma sweight_add_abstraction S weight i A :
  fresh_abstraction S i ->
  sweight weight (S,,, i |-> A) = sweight weight S + map_sum (vweight weight) A.
Proof.
  intros ?. unfold sweight, get_map. cbn. rewrite flatten_insert' by assumption.
  rewrite sum_maps_union. rewrite map_sum_union. rewrite !map_sum_kmap by typeclasses eauto.
  reflexivity.
  apply map_disjoint_spec. intros j ? ? lookup_l.
  intros ((? & ?) & ? & (? & (? & ?)%pair_eq & ?)%lookup_kmap_Some)%lookup_kmap_Some.
  subst. rewrite sum_maps_lookup_r, lookup_None_flatten in lookup_l by assumption.
  discriminate. all: typeclasses eauto.
Qed.
Hint Rewrite sweight_add_abstraction using auto with spath; fail : weight.

Hint Rewrite @sweight_add_anon using auto with weight : weight.

Variant leq_state_base : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Contrary to the article, symbolic values should be typed. Thus, only an integer can be converted
 * to a symbolic value for the moment. *)
| Leq_ToSymbolic S sp n :
    get_node (S.[sp]) = LLBC_plus_intC n -> leq_state_base S (S.[sp <- LLBC_plus_symbolic])
| Leq_ToAbs S a i v A
    (fresh_a : fresh_anon S a)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base (S,, a |-> v) (S,,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon S a v
    (fresh_a : fresh_anon S a)
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v) :
    leq_state_base (S,, a |-> v) S
| Leq_MoveValue S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (Hnot_in_abstraction : not_in_abstraction sp) :
    leq_state_base S (S.[sp <- bot],, a |-> S.[sp])
(* Note: for the merge, we reuse the region abstraction at i. Maybe we should use another region
 * abstraction index k? *)
| Leq_MergeAbs S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan S sp l a
    (fresh_l1 : is_fresh l S)
    (fresh_a : fresh_anon S a)
    (* We need a hypothesis that ensures that sp is valid. We could just add valid_spath S sp.
       I am going a step further: there should not be bottoms in borrowed values. *)
    (no_bot : not_contains_bot (S.[sp])) :
    leq_state_base S (S.[sp <- loan^m(l)],, a |-> borrow^m(l, S.[sp]))
| Leq_Reborrow_MutBorrow (S : LLBC_plus_state) (sp : spath) (l0 l1 : loan_id) (a : anon)
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow : get_node (S.[sp]) = borrowC^m(l0)) :
    leq_state_base S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(l1)))
(* Note: this rule makes the size of the state increase from right to left.
   We should add a decreasing quantity. *)
| Leq_Abs_ClearValue S i j v
    (get_at_i_j : abstraction_contains_value S i j v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base S (remove_abstraction_value S i j)
| Leq_AnonValue S a (is_fresh : fresh_anon S a) : leq_state_base S (S,, a |-> bot)
.

(* Derived rules *)
Lemma Leq_Reborrow_MutBorrow_Abs S sp l0 l1 i
    (fresh_l1 : is_fresh l1 S)
    (fresh_i : fresh_abstraction S i)
    (get_borrow : get_node (S.[sp]) = borrowC^m(l0)) :
    leq_state_base^* S (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],,,
                        i |-> {[1%positive := (borrow^m(l0, LLBC_plus_symbolic)); 2%positive := loan^m(l1)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. apply Leq_Reborrow_MutBorrow; eassumption. }
  constructor. eapply Leq_ToAbs with (a := a).
  - eauto with spath.
  - repeat apply fresh_abstraction_sset. eassumption.
  - autorewrite with spath. constructor.
Qed.

Lemma Leq_Fresh_MutLoan_Abs S sp l i n
    (fresh_l1 : is_fresh l S)
    (fresh_i : fresh_abstraction S i)
    (is_int : get_node (S.[sp]) = LLBC_plus_intC n) :
    leq_state_base^* S (S.[sp <- loan^m(l)],,,
                        i |-> {[1%positive := borrow^m(l, LLBC_plus_symbolic)]}%stdpp).
Proof.
  destruct (exists_fresh_anon S) as (a & fresh_a).
  etransitivity.
  { constructor. eapply Leq_ToSymbolic; eassumption. }
  etransitivity.
  { constructor. apply Leq_Fresh_MutLoan with (sp := sp).
    - not_contains.
    - apply fresh_anon_sset. eassumption.
    - autorewrite with spath. apply not_value_contains_zeroary; auto. }
  etransitivity.
  { constructor. eapply Leq_ToAbs with (a := a) (i := i).
    - eauto with spath.
    - repeat apply fresh_abstraction_sset. assumption.
    - autorewrite with spath. constructor. constructor. }
  autorewrite with spath. reflexivity.
Qed.

(* We are going to give an alternative definition of map equivalence that is computable.
 * Hence, two states S0 and S1 are equivalent if one is a permutation of the other:
 * S0 == S1 iff exists P, S0 = P(S1)
 * An interesting thing is that the permutation P can be applied to spaths, and it commutes with
 * common operations.
 * For example: P(S.[sp <- v]) = P(S).[P(sp) <- v]
 * This is going to be useful to prove the equivalence of states that are modified with common
 * operations.
 *)

(* A state permutation is a permutation of the anonymous variables and the elemnts of each regions.
 * It does not affect the variables. *)
Record state_perm := {
  anons_perm : Pmap positive;
  abstractions_perm : Pmap (Pmap positive);
}.

Definition is_state_equivalence perm S :=
  is_permutation (anons_perm perm) (anons S) /\
  map_Forall2 (fun k => is_permutation) (abstractions_perm perm) (abstractions S).

Program Definition apply_state_permutation perm S := {|
  vars := vars S;
  anons := apply_permutation (anons_perm perm) (anons S);
  abstractions :=
    map_zip_with (fun p A => apply_permutation p A) (abstractions_perm perm) (abstractions S);
|}.

Lemma get_extra_state_permutation perm S :
  is_state_equivalence perm S -> get_extra (apply_state_permutation perm S) = get_extra S.
Proof.
  intros (_ & Habstractions_equiv). unfold get_extra. cbn. rewrite dom_map_zip_with_L.
  apply map_Forall2_dom_L in Habstractions_equiv. rewrite Habstractions_equiv. set_solver.
Qed.

(* Applying a permutation to an accessor. *)
Definition permutation_accessor (perm : state_perm) acc : option positive :=
  match decode' (A := positive + positive * positive) acc with
  | Some (inl i) =>
      match decode' (A := var + anon) i with
      | Some (inl _) => Some acc
      | Some (inr a) => option_map anon_accessor (lookup a (anons_perm perm))
      | None => None
      end
  | Some (inr (i, j)) =>
      option_map (fun k => encode_abstraction (i, k)) (mbind (lookup j) (lookup i (abstractions_perm perm)))
  | None => None
  end.

(* In order to show that permutation_accessor is injective, we are going to give a caracteziration
 * of it as a relation. *)
Variant permutation_accessor_rel perm : positive -> positive -> Prop :=
  | PA_Var x : permutation_accessor_rel perm (encode_var x) (encode_var x)
  | PA_Anon a b (get_a : lookup a (anons_perm perm) = Some b) :
      permutation_accessor_rel perm (encode_anon a) (encode_anon b)
  | PA_Abstraction i j p j' (get_i : lookup i (abstractions_perm perm) = Some p)
      (get_j : lookup j p = Some j') :
      permutation_accessor_rel perm (encode_abstraction (i, j)) (encode_abstraction (i, j'))
.

Lemma permutation_accessor_is_Some perm acc acc' :
  permutation_accessor perm acc = Some acc' -> permutation_accessor_rel perm acc acc'.
Proof.
  unfold permutation_accessor. intros H.
    destruct (decode' acc) as [i | ] eqn:EQN; [ | discriminate].
    rewrite decode'_is_Some in EQN. subst.
    destruct i as [i | (i & j)].
    - destruct (decode' i) as [i' | ] eqn:EQN; [ | discriminate].
      rewrite decode'_is_Some in EQN. subst.
      destruct i'.
      + inversion H. constructor.
      + destruct (lookup a (anons_perm perm)) eqn:?; [ | discriminate].
        inversion H. constructor. assumption.
    - destruct (lookup i (abstractions_perm perm)) as [A | ] eqn:?; [ | discriminate]. cbn in H.
      destruct (lookup j A) as [j' | ] eqn:?; [ | discriminate]. cbn in H. inversion H.
      econstructor; eassumption.
Qed.

Lemma permutation_accessor_is_equivalence S perm :
  is_state_equivalence perm S -> is_equivalence (permutation_accessor perm) (get_map S).
Proof.
  intros ((inj_anons_perm & dom_anons_perm) & inj_abstractions_perm). split.
  - intros i Some_i j Hij. pose proof Some_i as Some_j. rewrite Hij in Some_j.
    destruct Some_i as (i' & Some_i). destruct Some_j as (j' & Some_j).
    rewrite Some_i, Some_j in Hij. inversion Hij; subst.
    apply permutation_accessor_is_Some in Some_i, Some_j.
    destruct Some_i.
    + inversion Some_j. f_equal. eapply encode_inj. congruence.
    + inversion Some_j. f_equal. eapply inj_anons_perm; [eassumption.. | ].
      eapply encode_inj. auto.
    + specialize (inj_abstractions_perm i).
      inversion inj_abstractions_perm as [q A (inj_p & _) | ]; [ | congruence].
      replace q with p in * by congruence.
      inversion Some_j as [| | i'' ? q' ? get_i'' ? _H eq_encode].
      f_equal. apply encode_inj in eq_encode. inversion eq_encode. subst. f_equal.
      rewrite get_i in get_i''. replace q' with p in * by congruence.
      eapply inj_p; [eassumption.. | congruence].
  - unfold get_map, permutation_accessor. cbn. intros i.
    intros [(i' & -> & Hi') | ((i' & j') & -> & Hij')]%sum_maps_is_Some.
    + rewrite decode'_encode.
      apply sum_maps_is_Some in Hi'.
      destruct Hi' as [(? & -> & _) | (? & -> & G)]; rewrite decode'_encode.
      * auto.
      * rewrite <-dom_anons_perm in G. destruct G as (? & G). setoid_rewrite G. auto.
    + rewrite decode'_encode. revert Hij'. rewrite lookup_flatten.
      specialize (inj_abstractions_perm i').
      inversion inj_abstractions_perm as [? A (_ & dom_A) | ];
          [ | intros (? & ?); discriminate].
      cbn. rewrite <-dom_A. intros (? & ->). auto.
Qed.

Lemma perm_at_var perm v : permutation_accessor perm (encode_var v) = Some (encode_var v).
Proof. unfold permutation_accessor, encode_var. rewrite !decode'_encode. reflexivity. Qed.

Lemma perm_at_anon perm a :
  permutation_accessor perm (anon_accessor a) =
  option_map anon_accessor (lookup a (anons_perm perm)).
Proof.
  unfold permutation_accessor, anon_accessor. cbn. unfold encode_anon.
  rewrite !decode'_encode. reflexivity.
Qed.

Lemma perm_at_abstraction perm i j :
  permutation_accessor perm (encode_abstraction (i, j)) =
  option_map (fun j' => encode_abstraction (i, j')) (mbind (lookup j) (lookup i (abstractions_perm perm))).
Proof. unfold permutation_accessor, encode_abstraction. rewrite decode'_encode. reflexivity. Qed.

Lemma abstraction_apply_state_permutation perm S i p A :
  lookup i (abstractions_perm perm) = Some p ->
  lookup i (abstractions S) = Some A ->
  lookup i (abstractions (apply_state_permutation perm S)) =
    Some (apply_permutation p A).
Proof.
  intros H G.  unfold apply_state_permutation. cbn.
  apply map_lookup_zip_with_Some. eexists _, _. eauto.
Qed.

(* The main property of apply_state_permutation. *)
Lemma get_map_state_permutation perm S (H : is_state_equivalence perm S) :
  get_map (apply_state_permutation perm S) = pkmap (permutation_accessor perm) (get_map S).
Proof.
  symmetry. apply pkmap_eq.
  - apply permutation_accessor_is_equivalence. assumption.
  - destruct H as ((anons_perm_inj & _) & Habs_perm).
    intros ? ? G%permutation_accessor_is_Some.
    destruct G as [ | | i ? p ? get_p_i].
    + rewrite !get_at_var. reflexivity.
    + rewrite !get_at_anon. unfold apply_state_permutation; cbn.
      erewrite lookup_pkmap by (rewrite <-?map_inj_equiv; eassumption). reflexivity.
    + rewrite !get_at_abstraction.
      specialize (Habs_perm i). rewrite get_p_i in Habs_perm.
      inversion Habs_perm as [? A (? & _) _p get_A_i | ]; subst.
      erewrite abstraction_apply_state_permutation by eauto.
      symmetry. apply lookup_pkmap; rewrite <-?map_inj_equiv; assumption.
  - destruct H as (Hanons_perm & Habs_perm).
    unfold get_map. cbn. rewrite !size_sum_maps.
    rewrite size_pkmap by now apply permutation_is_equivalence. f_equal.
    apply size_flatten.
    intros i. rewrite map_lookup_zip_with. specialize (Habs_perm i). destruct Habs_perm.
    + constructor. symmetry. apply size_pkmap, permutation_is_equivalence. assumption.
    + constructor.
Qed.

Corollary get_at_accessor_state_permutation perm S i (H : is_state_equivalence perm S) :
  is_Some (get_at_accessor S i) ->
  exists j, permutation_accessor perm i = Some j /\
  get_at_accessor (apply_state_permutation perm S) j = get_at_accessor S i.
Proof.
  intros G. rewrite get_map_state_permutation by assumption.
  apply permutation_accessor_is_equivalence in H.
  destruct H as (inj_perm & H). edestruct H; [exact G | ].
  eexists. split; [eassumption | ]. apply lookup_pkmap; assumption.
Qed.

Definition permutation_spath (perm : state_perm) (sp : spath) : spath :=
  match permutation_accessor perm (fst sp) with
  | Some j => (j, snd sp)
  | None => sp
  end.

Lemma permutation_valid_spath S sp perm (H : is_state_equivalence perm S) :
  valid_spath S sp -> valid_spath (apply_state_permutation perm S) (permutation_spath perm sp).
Proof.
  intros (v & ? & ?). exists v. unfold permutation_spath.
  edestruct get_at_accessor_state_permutation as (? & -> & ->); auto.
Qed.

Lemma permutation_sget S (perm : state_perm) (H : is_state_equivalence perm S)
  sp (valid_sp : valid_spath S sp) :
  (apply_state_permutation perm S).[permutation_spath perm sp] = S.[sp].
Proof.
  destruct valid_sp as (v & get_at_sp & _). unfold permutation_spath, sget.
  edestruct get_at_accessor_state_permutation as (? & -> & <-); [eassumption | auto | reflexivity].
Qed.

Lemma sset_abstractions_dom S sp v :
  map_Forall2 (fun _ A A' => dom A = dom A') (abstractions S) (abstractions (S.[sp <- v])).
Proof.
  intros i.
  assert (is_Some (lookup i (abstractions S)) <-> is_Some (lookup i (abstractions (S.[sp <- v])))).
  { rewrite <-!elem_of_dom.
    replace (dom (abstractions S)) with (get_extra S) by reflexivity.
    replace (dom (abstractions (S .[sp <- v]))) with (get_extra (S.[sp <- v])) by reflexivity.
    unfold sset. rewrite get_extra_alter. reflexivity. }
  destruct (lookup i (abstractions S)) eqn:?;
  destruct (lookup i (abstractions (S.[sp <- v]))) eqn:?.
  - constructor. apply set_eq. intros j. rewrite !elem_of_dom.
    erewrite <-get_at_abstraction' by eassumption.
    symmetry. erewrite <-get_at_abstraction' by eassumption.
    unfold sset. rewrite get_map_alter. apply lookup_alter_is_Some.
  - destruct H as (H & _). destruct H; easy.
  - destruct H as (_ & H). destruct H; easy.
  - constructor.
Qed.

Lemma is_state_equivalence_sset perm S sp v :
  is_state_equivalence perm S -> is_state_equivalence perm (S.[sp <- v]).
Proof.
  intros ((? & H) & G). split. split.
  - assumption.
  - intros a. rewrite H. rewrite <-!get_at_anon. rewrite <-!elem_of_dom.
    unfold sset. rewrite get_map_alter, dom_alter. reflexivity.
  - intros i. specialize (G i).
    remember (lookup i (abstractions S)) as A eqn:EQN_A.
    remember (lookup i (abstractions_perm perm)) as perm_A.
    destruct G as [? ? G | ].
    + pose proof (sset_abstractions_dom S sp v i) as dom_abs.
      rewrite <-EQN_A in dom_abs.
      remember (lookup i (abstractions (S.[sp <- v]))).
      inversion dom_abs as [? ? eq_dom | ]; subst. constructor.
      unfold is_permutation. destruct G. setoid_rewrite <-elem_of_dom.
      rewrite <-eq_dom. setoid_rewrite elem_of_dom. split; assumption.
    + assert (fresh_abstraction S i) as G by easy.
      rewrite fresh_abstraction_sset in G. rewrite G. constructor.
Qed.

Lemma permutation_sset S (perm : state_perm) v (H : is_state_equivalence perm S)
  sp (valid_sp : valid_spath S sp) :
  (apply_state_permutation perm (S.[sp <- v])) = (apply_state_permutation perm S).[permutation_spath perm sp <- v].
Proof.
  destruct valid_sp as (w & G & _). apply state_eq_ext.
  - rewrite get_map_state_permutation by now apply is_state_equivalence_sset.
    unfold sset. rewrite !get_map_alter.
    rewrite get_map_state_permutation by assumption.
    unfold permutation_spath.
    edestruct get_at_accessor_state_permutation as (? & uwu & ?); [eassumption | auto | ].
    rewrite !uwu.
    apply alter_pkmap.
    now apply permutation_accessor_is_equivalence. assumption.
  - rewrite get_extra_state_permutation by now apply is_state_equivalence_sset.
    unfold sset. rewrite get_extra_alter.
    rewrite get_extra_alter. symmetry. apply get_extra_state_permutation. assumption.
Qed.

Definition add_anon_perm perm a b := {|
  anons_perm := insert a b (anons_perm perm);
  abstractions_perm := abstractions_perm perm;
|}.

Lemma add_anon_perm_equivalence perm S a b v :
  fresh_anon S a -> fresh_anon (apply_state_permutation perm S) b ->
  is_state_equivalence perm S -> is_state_equivalence (add_anon_perm perm a b) (S,, a |-> v).
Proof.
  intros fresh_a fresh_b p_is_state_equiv.
  unfold fresh_anon in fresh_b. rewrite get_at_anon in fresh_b. cbn in fresh_b.
  destruct p_is_state_equiv as ((? & eq_dom) & Habstractions_perm). split.
  - cbn. split.
    + apply map_inj_insert; [ | assumption]. intros ? get_i.
      erewrite lookup_pkmap in fresh_b; [ | now apply map_inj_equiv | eassumption].
      rewrite eq_None_not_Some, <-eq_dom, get_i in fresh_b. auto.
    + setoid_rewrite lookup_insert_is_Some. intros i. specialize (eq_dom i). tauto.
  - exact Habstractions_perm.
Qed.

Lemma permutation_add_anon S perm a b v :
  is_state_equivalence perm S ->
  fresh_anon S a -> fresh_anon (apply_state_permutation perm S) b ->
  apply_state_permutation (add_anon_perm perm a b) (S,, a |-> v) =
      (apply_state_permutation perm S),, b |-> v.
Proof.
  intros ? fresh_a fresh_b.
  apply state_eq_ext.
  - assert (is_state_equivalence (add_anon_perm perm a b) (S,, a |-> v)) as G
      by now apply add_anon_perm_equivalence.
    rewrite get_map_state_permutation by assumption.
    rewrite !get_map_add_anon.
    rewrite get_map_state_permutation by assumption.
    apply permutation_accessor_is_equivalence in G.
    rewrite pkmap_insert; [ | apply G | exact fresh_a].
    unfold insert_permuted_key. rewrite perm_at_anon.
    (* A trick to perform a cbn only in the term `option_map _ _` *)
    remember (option_map _ _) eqn:EQN. cbn in EQN. simpl_map. cbn in EQN. subst.
    f_equal. apply pkmap_fun_eq. intros i get_rel%get_at_accessor_is_Some.
    destruct get_rel as [ | a' ? get_a' | ].
    + rewrite !perm_at_var. reflexivity.
    + rewrite !perm_at_anon. unfold add_anon_perm. cbn.
      rewrite lookup_insert_ne by (rewrite <-get_at_anon in get_a'; congruence).
      reflexivity.
    + erewrite !perm_at_abstraction. reflexivity.
  - rewrite get_extra_state_permutation by now apply add_anon_perm_equivalence.
    rewrite !get_extra_add_anon.
    symmetry. apply get_extra_state_permutation. assumption.
Qed.

Definition remove_anon_perm perm a := {|
  anons_perm := delete a (anons_perm perm);
  abstractions_perm := abstractions_perm perm;
|}.

Lemma remove_anon_perm_equivalence perm S a v :
  fresh_anon S a -> is_state_equivalence perm (S,, a |-> v) ->
  is_state_equivalence (remove_anon_perm perm a) S /\
  exists b, perm = add_anon_perm (remove_anon_perm perm a) a b /\
            fresh_anon (apply_state_permutation (remove_anon_perm perm a) S) b.
Proof.
  intros ? p_is_state_equiv.
  destruct p_is_state_equiv as ((anons_perm_inj & eq_dom) & Habstractions_perm).
  split; [split | ].
  - cbn. split.
    + intros ? ? (_ & ?)%lookup_delete_Some ? ? (_ & ?)%lookup_delete_Some ?.
      eapply anons_perm_inj; eassumption.
    + intros i. setoid_rewrite lookup_delete_is_Some.
      specialize (eq_dom i). cbn in eq_dom. rewrite lookup_insert_is_Some' in eq_dom.
      unfold fresh_anon in H.
      split.
      -- intuition.
      -- intros ?. rewrite get_at_anon, eq_None_not_Some in H.
        assert (a <> i) by now intros <-. intuition.
  - exact Habstractions_perm.
  - pose proof (eq_dom a) as (_ & (b & G)). { cbn. simpl_map. easy. }
    exists b. split.
    + unfold add_anon_perm, remove_anon_perm. destruct perm. cbn. rewrite insert_delete; easy.
    + unfold fresh_anon. rewrite get_at_anon. cbn.
      replace (anons S) with (delete a (anons (S,, a |-> v))).
      2: { cbn. rewrite delete_insert by now rewrite <-get_at_anon. reflexivity. }
      erewrite apply_permutation_delete by eassumption. simpl_map. reflexivity.
Qed.

Lemma permutation_fresh_abstraction S p i :
  fresh_abstraction S i -> fresh_abstraction (apply_state_permutation p S) i.
Proof. unfold fresh_abstraction. cbn. rewrite map_lookup_zip_with_None. auto. Qed.

Definition add_abstraction_perm perm i p := {|
  anons_perm := anons_perm perm;
  abstractions_perm := insert i p (abstractions_perm perm);
|}.

Lemma add_abstraction_perm_equivalence perm S i A p :
  is_state_equivalence perm S -> is_permutation p A ->
  is_state_equivalence (add_abstraction_perm perm i p) (S,,, i |-> A).
Proof.
  intros (? & ?) ?. split.
  - assumption.
  - apply map_Forall2_insert_2; assumption.
Qed.
Hint Resolve add_abstraction_perm_equivalence : spath.

Lemma permutation_add_abstraction S perm p i A :
  fresh_abstraction S i -> is_state_equivalence perm S -> is_permutation p A ->
  apply_state_permutation (add_abstraction_perm perm i p) (S,,, i |-> A) =
  apply_state_permutation perm S,,, i |-> apply_permutation p A.
Proof.
  intros fresh_A Hstate_perm p_is_perm.
  assert (is_state_equivalence (add_abstraction_perm perm i p) (S,,, i |-> A)) as G
      by now apply add_abstraction_perm_equivalence.
  apply state_eq_ext.
  - rewrite get_map_state_permutation by assumption.
    apply pkmap_eq.
    + apply permutation_accessor_is_equivalence. assumption.
    + intros ? ? perm_rel%permutation_accessor_is_Some.
      destruct perm_rel as [ | | i' ? ? ? perm_at_i].
      * rewrite !get_at_var. reflexivity.
      * rewrite !get_at_anon. cbn. erewrite lookup_pkmap;
          [reflexivity | apply map_inj_equiv, G | assumption].
      * erewrite !get_at_abstraction.
        destruct (decide (i = i')) as [<- | ].
        -- cbn in *. simpl_map. inversion perm_at_i; subst. symmetry.
           apply lookup_pkmap; [apply map_inj_equiv, p_is_perm | assumption].
        -- cbn in *. simpl_map. rewrite map_lookup_zip_with, perm_at_i. cbn.
           destruct Hstate_perm as (_ & Habstractions_perm).
           specialize (Habstractions_perm i'). rewrite perm_at_i in Habstractions_perm.
           inversion Habstractions_perm as [? B (? & _) | ].
           cbn. symmetry. apply lookup_pkmap; [apply map_inj_equiv | ]; assumption.
    + cbn. rewrite !size_sum_maps.
      rewrite flatten_insert by now rewrite fresh_A.
      rewrite flatten_insert by (apply map_lookup_zip_with_None; auto).
      rewrite !map_size_disj_union by
        (apply disj_kmap_flatten; rewrite ?map_lookup_zip_with_None; auto).
      rewrite !size_kmap by typeclasses eauto.
      destruct Hstate_perm as (? & Habstractions_perm).
      rewrite !size_pkmap by now apply permutation_is_equivalence.
      f_equal. f_equal. apply size_flatten.
      intros i'. rewrite map_lookup_zip_with.
      specialize (Habstractions_perm i'). destruct Habstractions_perm; constructor.
      symmetry. apply size_pkmap, permutation_is_equivalence. assumption.
  - rewrite get_extra_add_abstraction, !get_extra_state_permutation by assumption.
    rewrite get_extra_add_abstraction. reflexivity.
Qed.

Definition remove_abstraction_perm perm i := {|
  anons_perm := anons_perm perm;
  abstractions_perm := delete i (abstractions_perm perm);
|}.

Lemma remove_abstraction_perm_equivalence perm S i A :
  fresh_abstraction S i ->
  is_state_equivalence perm (S,,, i |-> A) ->
  is_state_equivalence (remove_abstraction_perm perm i) S /\
  exists p, is_permutation p A /\ perm = add_abstraction_perm (remove_abstraction_perm perm i) i p.
Proof.
  intros ? (? & H). split; [split | ].
  - assumption.
  - replace (abstractions S) with (delete i (abstractions (S,,, i |-> A))).
    2: { cbn. now rewrite delete_insert. }
    apply map_Forall2_delete. assumption.
  - specialize (H i). cbn in H. simpl_map. inversion H. eexists. split; [eassumption | ].
    unfold add_abstraction_perm, remove_abstraction_perm. cbn.
    rewrite insert_delete by congruence. destruct perm. reflexivity.
Qed.

Definition remove_abstraction_value_perm perm i j := {|
  anons_perm := anons_perm perm;
  abstractions_perm := alter (delete j) i (abstractions_perm perm);
|}.

Lemma remove_abstraction_value_perm_equivalence perm S i j :
  is_state_equivalence perm S ->
  is_state_equivalence (remove_abstraction_value_perm perm i j) (remove_abstraction_value S i j).
Proof.
  intros (? & H). split.
  - assumption.
  - cbn. intros i'. destruct (decide (i = i')) as [<- | ]; simpl_map.
    + destruct (H i) as [p ? (p_inj & ?) | ]; constructor. split.
      * intros ? ? (_ & ?)%lookup_delete_Some ? ? (_ & ?)%lookup_delete_Some.
        apply p_inj; assumption.
      * setoid_rewrite lookup_delete_is_Some. firstorder.
    + apply H.
Qed.

Lemma permutation_abstraction_element perm S i j v :
  is_state_equivalence perm S -> abstraction_contains_value S i j v -> exists j',
    permutation_accessor perm (encode_abstraction (i, j)) = Some (encode_abstraction (i, j')).
Proof.
  intros (_ & equiv_abs) H%mk_is_Some%get_at_accessor_is_Some.
  inversion H as [ | | ? ? A ? get_A get_at_j eq_encode].
  apply encode_inj in eq_encode. inversion eq_encode; subst.
  specialize (equiv_abs i). rewrite get_A in equiv_abs.
  inversion equiv_abs as [p ? (_ & eq_dom) | ]; subst.
  apply mk_is_Some in get_at_j. rewrite <-eq_dom in get_at_j. destruct get_at_j as (j' & ?).
  exists j'. rewrite perm_at_abstraction. simpl_map. cbn. simpl_map. reflexivity.
Qed.

Lemma permutation_remove_abstraction_value S perm i j j' :
  is_state_equivalence perm S ->
  permutation_accessor perm (encode_abstraction (i, j)) = Some (encode_abstraction (i, j')) ->
  apply_state_permutation (remove_abstraction_value_perm perm i j) (remove_abstraction_value S i j) =
  remove_abstraction_value (apply_state_permutation perm S) i j'.
Proof.
  intros H ?. pose proof (remove_abstraction_value_perm_equivalence _ _ i j H) as G.
  pose proof (permutation_accessor_is_equivalence _ _ H) as K.
  apply state_eq_ext.
  - rewrite get_map_remove_abstraction_value.
    rewrite !get_map_state_permutation by assumption.
    rewrite get_map_remove_abstraction_value.
    erewrite <-pkmap_delete; [ | apply K | eassumption].
    apply pkmap_fun_eq.
    intros ? (? & get_rel)%lookup_delete_is_Some.
    apply get_at_accessor_is_Some in get_rel. destruct get_rel as [ | | i' j''].
    + rewrite !perm_at_var. reflexivity.
    + rewrite !perm_at_anon. reflexivity.
    + rewrite !perm_at_abstraction. cbn.
      destruct (decide (i = i')) as [<- | ]; simpl_map; [ | reflexivity].
      assert (j <> j'') by congruence.
      destruct (lookup i (abstractions_perm perm)); [ | reflexivity].
      cbn. simpl_map. reflexivity.
  - rewrite get_extra_remove_abstraction_value.
    rewrite !get_extra_state_permutation by assumption. apply get_extra_remove_abstraction_value.
Qed.

Lemma remove_loans_equiv A B A' B' (H : remove_loans A B A' B') :
  forall pA pB, is_permutation pA A -> is_permutation pB B ->
    exists pA' pB', is_permutation pA' A' /\ is_permutation pB' B' /\
      remove_loans (apply_permutation pA A) (apply_permutation pB B)
                   (apply_permutation pA' A') (apply_permutation pB' B').
Proof.
  intros pA pB perm_A perm_B. induction H as [ | ? ? ? ? ? ? IH].
  - exists pA, pB. split; [assumption | ]. split; [assumption | ]. constructor.
  - destruct IH as (pA' & pB' & perm_A' & perm_B' & IH).
    eexists _, _.
    split. { eapply is_permutation_delete, perm_A'. }
    split. { eapply is_permutation_delete, perm_B'. }
    destruct perm_A' as (inj_pA' & dom_pA'). destruct perm_B' as (inj_pB' & dom_pB').
    assert (is_Some (lookup i pA')) as (i' & ?). { apply dom_pA'. auto. }
    assert (is_Some (lookup j pB')) as (j' & ?). { apply dom_pB'. auto. }
    erewrite !apply_permutation_delete by eassumption.
    eapply Remove_MutLoan; [ | erewrite lookup_apply_permutation..]; eassumption.
Qed.

Lemma merge_abstractions_equiv A B C pA pB :
  is_permutation pA A -> is_permutation pB B -> merge_abstractions A B C ->
  exists pC, is_permutation pC C /\
    merge_abstractions (apply_permutation pA A) (apply_permutation pB B) (apply_permutation pC C).
Proof.
  intros perm_A perm_B (A' & B' & Hremove & union_A'_B').
  edestruct remove_loans_equiv as (pA' & pB' & ? & ? & BATORA); [eassumption.. | ].
  eapply union_maps_equiv in union_A'_B'; [ | eassumption..].
  destruct union_A'_B' as (pC & ? & ?).
  exists pC. split; [assumption | ]. eexists _, _. split; eassumption.
Qed.

Global Instance LLBC_plus_state_leq_base : LeqBase LLBC_plus_state :=
{ leq_base := leq_state_base }.

(* TODO: should it be the main definition instead of a characterization? *)
Definition equiv_states S0 S1 :=
  exists perm, is_state_equivalence perm S1 /\ S0 = apply_state_permutation perm S1.

(* An alternative definition. *)
Definition equiv_states' (S0 S1 : LLBC_plus_state) :=
  vars S0 = vars S1 /\
  equiv_map (anons S0) (anons S1) /\
  map_Forall2 (fun _ => equiv_map) (abstractions S0) (abstractions S1).

Definition leq := chain leq_state_base^* equiv_states.

Lemma equiv_states_perm S0 S1 : equiv_states' S0 S1 <-> equiv_states S0 S1.
Proof.
  split.
  - intros (eq_vars & H%equiv_map_alt & abstractions_equiv).
    destruct H as (anons_perm & ? & ?).
    assert (exists M,
      map_Forall2 (fun _ => is_permutation) M (abstractions S1) /\
      abstractions S0 = map_zip_with (fun p A => apply_permutation p A) M (abstractions S1))
      as (M & G & ?).
    { remember (abstractions S0) as As0 eqn:EQN. clear EQN.
      remember (abstractions S1) as As1 eqn:EQN. clear EQN.
      revert As1 abstractions_equiv.
      induction As0 as [ | i A As0 ? ? IH] using map_first_key_ind.
      - intros ? ->%map_Forall2_empty_inv_l.
        exists empty. split; [apply map_Forall2_empty | reflexivity].
      - intros _As1 G. apply map_Forall2_insert_inv_l in G; [ | assumption].
        destruct G as (B & As1 & -> & ? & (p & ? & ->)%equiv_map_alt & G).
        specialize (IH _ G). destruct IH as (M & ? & ->).
        exists (insert i p M). split.
        + apply map_Forall2_insert_2; assumption.
        + rewrite<- map_insert_zip_with. reflexivity. }
    exists {|anons_perm := anons_perm; abstractions_perm := M|}.
    split; [split | ].
    + assumption.
    + cbn. intros i. specialize (G i). destruct G; constructor. assumption.
    + unfold apply_state_permutation. destruct S0, S1. cbn in *. congruence.
  - intros ((anons_perm0 & abs_perm0) & (? & Habs_perm) & ->). cbn in *.
    split; [ | split].
    + reflexivity.
    + cbn. eexists. split; [ | reflexivity]. apply permutation_is_equivalence. assumption.
    + cbn. intros i. specialize (Habs_perm i). rewrite map_lookup_zip_with.
      destruct Habs_perm; constructor. eexists.
      split; [ | reflexivity]. apply permutation_is_equivalence. assumption.
Qed.

Instance equiv_states_reflexive : Reflexive equiv_states.
Proof.  intros ?. apply equiv_states_perm. repeat split; repeat intro; reflexivity. Qed.

Instance equiv_states_transitive : Transitive equiv_states.
Proof.
  intros S0 S1 S2. rewrite <-!equiv_states_perm. intros (? & ? & H) (? & ? & G).
  split; [ | split].
  - congruence.
  - transitivity (anons S1); assumption.
  - intros i. specialize (G i). destruct (H i); [ | assumption].
    inversion G; subst. constructor. etransitivity; eassumption.
Qed.

(* Note: the condition H (and the argument S) could be removed. But because of how the lemma
 * get_at_accessor_is_Some is defined, it's easier to include them. *)
Lemma in_abstraction_perm S perm i x y (H : is_Some (get_at_accessor S x)) :
  permutation_accessor perm x = Some y -> in_abstraction i y ->
  in_abstraction i x.
Proof.
  intros G (? & ->). apply get_at_accessor_is_Some in H. destruct H as [ | a | i' j].
  - rewrite perm_at_var in G. discriminate.
  - rewrite perm_at_anon in G. destruct (lookup a (anons_perm perm)); discriminate.
  - rewrite perm_at_abstraction in G.
    destruct (lookup i' (abstractions_perm perm)) as [p | ]; [ | discriminate]. cbn in G.
    destruct (lookup j p); [ | discriminate]. cbn in G.
    inversion G as [K]. apply encode_inj in K. exists j. congruence.
Qed.

Corollary not_in_abstraction_perm S perm sp (valid_sp : valid_spath S sp) :
  not_in_abstraction sp -> not_in_abstraction (permutation_spath perm sp).
Proof.
  unfold not_in_abstraction, in_abstraction, permutation_spath.
  intros H i (j & ?). apply (H i).
  destruct (permutation_accessor perm (fst sp)) eqn:EQN.
  - destruct valid_sp as (? & G%mk_is_Some & _).
    eapply in_abstraction_perm; [eassumption.. | ]. eexists. eassumption.
  - eexists. eassumption.
Qed.

Lemma leq_equiv_states_commute :
  forward_simulation equiv_states equiv_states leq_state_base leq_state_base.
Proof.
  intros Sl Sr Hleq.
  intros ? (perm & valid_perm & ->). destruct Hleq.
  (* TODO: automatization *)
  - eexists. rewrite Logic.and_comm. split.
    + eapply Leq_ToSymbolic.
      rewrite permutation_sget. eassumption. assumption. validity.
    + eexists. rewrite permutation_sset by eauto with spath.
      split; [ | reflexivity]. apply is_state_equivalence_sset. assumption.
  - apply remove_anon_perm_equivalence in valid_perm; [ | assumption].
    destruct valid_perm as (valid_perm & b & G & ?). rewrite G.
    eexists. rewrite permutation_add_anon; try assumption.
    rewrite Logic.and_comm. split.
    + apply Leq_ToAbs with (i := i); eauto using permutation_fresh_abstraction.
    + eexists. erewrite permutation_add_abstraction with (p := id_permutation A);
        [ | eassumption.. | apply id_permutation_is_permutation].
      rewrite apply_id_permutation. split; [ | reflexivity].
      apply add_abstraction_perm_equivalence; [assumption | apply id_permutation_is_permutation].
  - apply remove_anon_perm_equivalence in valid_perm; [ | assumption].
    destruct valid_perm as (valid_perm & b & G & ?).
    rewrite G, permutation_add_anon by assumption.
    eexists. rewrite Logic.and_comm. split.
    + apply Leq_RemoveAnon; eassumption.
    + eexists. eauto.
  - destruct (exists_fresh_anon (apply_state_permutation perm S)) as (b & fresh_b).
    eexists. rewrite Logic.and_comm. split.
    + apply Leq_MoveValue.
      rewrite permutation_sget by eauto. assumption.
      exact fresh_b. now apply permutation_valid_spath.
      eapply not_in_abstraction_perm; eassumption.
    + eexists.
      rewrite permutation_add_anon.
      2: { apply is_state_equivalence_sset. eassumption. }
      2: { eauto with spath. }
      2: { rewrite permutation_sset by auto with spath. eauto with spath. }
      rewrite permutation_sset by auto with spath.
      rewrite permutation_sget by auto with spath.
      split; [ | reflexivity].
      apply add_anon_perm_equivalence. auto with spath.
      rewrite permutation_sset by auto with spath. auto with spath.
      apply is_state_equivalence_sset. assumption.
  - apply remove_abstraction_perm_equivalence in valid_perm; [ | auto with spath].
    destruct valid_perm as (valid_perm & p & p_perm & Hperm).
    apply remove_abstraction_perm_equivalence in valid_perm; [ | assumption].
    destruct valid_perm as (valid_perm & q & q_perm & Hperm').
    eapply merge_abstractions_equiv in Hmerge; [ | eassumption..].
    destruct Hmerge as (r & perm_r & Hmerge).
    rewrite Hperm, Hperm'.
    rewrite !permutation_add_abstraction by auto with spath.
    eexists. rewrite Logic.and_comm. split.
    + apply Leq_MergeAbs.
      * apply map_lookup_zip_with_None. cbn. simpl_map. auto.
      * apply map_lookup_zip_with_None. cbn. simpl_map. auto.
      * eassumption.
      * assumption.
    + eexists. rewrite permutation_add_abstraction by eassumption. split; [ | reflexivity].
      auto using add_abstraction_perm_equivalence.
  - admit.
  - admit.
  - pose proof get_at_i_j as _get_at_i_j.
    (* TODO: pose this for the whole proof? *)
    pose proof (permutation_accessor_is_equivalence _ _ valid_perm) as perm_equivalence.
    apply (permutation_abstraction_element perm) in _get_at_i_j; [ | assumption].
    destruct _get_at_i_j as (j' & perm_abs_val).
    eexists. rewrite Logic.and_comm. split.
    + apply Leq_Abs_ClearValue with (i := i) (j := j') (v := v).
      rewrite get_map_state_permutation by assumption.
      erewrite lookup_pkmap; [eassumption | apply perm_equivalence | eassumption].
      assumption. assumption.
    + eexists. erewrite permutation_remove_abstraction_value by eassumption.
      split; [now apply remove_abstraction_value_perm_equivalence | reflexivity].
Admitted.

Lemma vweight_bot weight : vweight weight bot = weight botC.
Proof. reflexivity. Qed.
Hint Rewrite vweight_bot : weight.

Lemma vweight_symbolic weight : vweight weight (LLBC_plus_symbolic) = weight (LLBC_plus_symbolicC).
Proof. reflexivity. Qed.
Hint Rewrite vweight_symbolic : weight.

Lemma vweight_mut_loan weight l : vweight weight loan^m(l) = weight loanC^m(l).
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_loan : weight.

Lemma vweight_mut_borrow weight l v :
  vweight weight borrow^m(l, v) = weight borrowC^m(l) + vweight weight v.
Proof. reflexivity. Qed.
Hint Rewrite vweight_mut_borrow : weight.

(* We cannot automatically rewrite map_sum_empty. Is it because of typeclasses?
 * Thus, we crate an alternative. *)
Lemma abstraction_sum_empty (weight : LLBC_plus_val -> nat) : map_sum weight (M := Pmap) empty = 0.
Proof. apply map_sum_empty. Qed.
Hint Rewrite abstraction_sum_empty : weight.

Lemma abstraction_sum_insert weight i v (A : Pmap LLBC_plus_val) :
  lookup i A = None -> map_sum weight (insert i v A) = weight v + map_sum weight A.
Proof. apply map_sum_insert. Qed.
Hint Rewrite abstraction_sum_insert using auto : weight.

Lemma abstraction_sum_singleton weight i v :
  map_sum weight (singletonM (M := Pmap LLBC_plus_val) i v) = weight v.
Proof.
  unfold singletonM, map_singleton.
  rewrite abstraction_sum_insert, abstraction_sum_empty by apply lookup_empty. lia.
Qed.
Hint Rewrite abstraction_sum_singleton : weight.

(* Simulation proofs. *)
Lemma eval_path_preservation Sl Sr perm p R :
  (forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) ->
  forward_simulation R R (eval_path Sr perm p) (eval_path Sl perm p).
Proof.
  intros preservation_proj. intros ? ? Heval_path.
  induction Heval_path.
  - intros ?. intros ?. eexists. split; [eassumption | constructor].
  - intros pi_l HR.
    edestruct preservation_proj as (pi_l' & ? & ?); [eassumption.. | ].
    edestruct IHHeval_path as (pi_l'' & ? & ?); [eassumption | ].
    exists pi_l''. split; [ | econstructor]; eassumption.
Qed.

(* This lemma is use to prove preservation of place evaluation for a relation rule Sl < Sr.
 * We prove that if p evaluates to a spath pi_r on Sr, then it also evaluates for a spath
 * pi_l on the left, with R pi_l pi_r.
 * The relation R depends on the rule, but for most rules it is simply going to be the equality. *)
Lemma eval_place_preservation Sl Sr perm p (R : spath -> spath -> Prop)
  (* Initial case: the relation R must be preserved for all spath corresponding to a variable. *)
  (R_nil : forall x, R (encode_var x, []) (encode_var x, []))
  (* All of the variables of Sr are variables of Sl.
   * Since most of the time, Sr is Sl with alterations on region abstractions, anonymous variables
   * or by sset, this is always true. *)
  (dom_eq : dom (vars Sl) = dom (vars Sr))
  (Hsim : forall proj, forward_simulation R R (eval_proj Sr perm proj) (eval_proj Sl perm proj)) :
  forall pi_r, eval_place Sr perm p pi_r -> exists pi_l, R pi_l pi_r /\ eval_place Sl perm p pi_l.
Proof.
  intros pi_r ((? & G%mk_is_Some & _) & Heval_path).
  cbn in G. unfold encode_var in G. rewrite !sum_maps_lookup_l in G.
  rewrite <-elem_of_dom, <-dom_eq, elem_of_dom, <-get_at_var in G. destruct G as (? & ?).
  eapply eval_path_preservation in Heval_path; [ | eassumption].
  edestruct Heval_path as (pi_l' & ? & ?); [apply R_nil | ].
  exists pi_l'. split; [assumption | ]. split; [ | assumption].
  eexists. split; [eassumption | constructor].
Qed.

Lemma sset_preserves_vars_dom S sp v : dom (vars (S.[sp <- v])) = dom (vars S).
Proof.
  unfold sset. unfold alter_at_accessor. cbn. repeat autodestruct.
  intros. apply dom_alter_L.
Qed.

Lemma add_anon_preserves_vars_dom S a v : dom (vars (S,, a |-> v)) = dom (vars S).
Proof. reflexivity. Qed.

Hint Resolve sget_sset_zeroary_not_prefix : spath.

Lemma eval_place_ToSymbolic S sp p pi perm n
  (His_integer : get_node (S.[sp]) = LLBC_plus_intC n)
  (H : (S.[sp <- LLBC_plus_symbolic]) |-{p} p =>^{perm} pi) :
  S |-{p} p =>^{perm} pi /\ ~strict_prefix sp pi.
Proof.
  pose proof (valid_pi := H). apply eval_place_valid in valid_pi.
  eapply eval_place_preservation with (R := eq) in H.
  - split.
    + destruct H as (? & -> & H). exact H.
    + eapply get_nil_prefix_right; [ | eassumption]. autorewrite with spath. reflexivity.
  - reflexivity.
  - symmetry. apply sset_preserves_vars_dom.
  - intros proj pi_r pi_r' Heval_proj ? ->. eexists. split; [reflexivity | ].
    inversion Heval_proj; subst.
    (* TODO: automate this. *)
    + autorewrite with spath in get_q. eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(* While we only have mutable loans and borrows, we cannot "jump into" an abstraction. When we
 * introduce shared loans/borrows, we need to redefine this relation. *)
Definition rel_ToAbs a i (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ fst p <> anon_accessor a.

(* Note: the hypothesis `no_borrow` is not necessary to prove this lemma. *)
(* The hypothesis `no_loan` is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_ToAbs S a i v A p perm
  (fresh_a : fresh_anon S a)
  (fresh_i : fresh_abstraction S i)
  (Hto_abs : to_abs v A) :
  forall pi_r, (S,,, i |-> A) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_ToAbs a i pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; [now eapply var_not_in_abstraction | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'.
    inversion Heval_proj; subst. repeat split; auto.
    autorewrite with spath in get_q. econstructor; autorewrite with spath; eassumption.
Qed.

(* Let Sl < Sr be two states in relation. Let's assume that there is a difference of one anonymous
 * variables between the two states.
 * Ex: Sr = Sl.[p <- v],, a |- w, or Sr = remove_anon a Sl
 * Any valid spath in Sl and Sr cannot be in the anonymous variable a.
 * The relation "rel_change_anon a" relates two equal paths in Sl and Sr that are not in a. *)
Definition rel_change_anon a (p q : spath) := p = q /\ fst p <> anon_accessor a.

(* Relates two equal paths pi_l and pi_r such that:
 * - Neither is in the anonymous variable a.
 * - Neither is under a given spath sp. *)
(* Used by the rules Leq_MoveValue and Leq_Fresh_MutLoan. *)
Definition rel_change_anon_not_in_spath sp a pi_l pi_r :=
  rel_change_anon a pi_l pi_r /\ ~strict_prefix sp pi_l.

(* Note: the hypothesis `no_borrow` is not necessary to prove this lemma. *)
(* The hypothesis `no_loan` is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_RemoveAnon S perm a v p
  (fresh_a : fresh_anon S a)
  (no_loan : not_contains_loan v) :
  forall pi_r, S |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ (S,, a |-> v) |-{p} p =>^{perm} pi_l.
Proof.
  eapply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + autorewrite with spath in get_q.
      repeat split; try assumption.
      eapply Eval_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

(* Take Sr = Sl.[sp <- bot],, a |-> Sl.[sp] the left state. Relation between the evaluation
 * pi_l in Sl and pi_r in Sr: *)
Definition rel_MoveValue_imm sp a pi_l pi_r :=
  (pi_l = pi_r /\ ~strict_prefix sp pi_l /\ fst pi_l <> encode_anon a) \/
  (* If there is a (non-outer) mutable loan in S.[sp], it's possible to evaluate a place p there.
   * What happens is that in Sl, pi_l is under sp whereas in Sr, pi_r is in the newly added
   * anonymous variable. *)
  (* However, this is only possible when evaluating in mode Imm. *)
  (exists r, pi_l = sp +++ r /\ pi_r = (encode_anon a, r)).

Lemma eval_place_MoveValue_imm S sp a p
  (fresh_a : fresh_anon S a)
  (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{Imm} pi_r ->
  exists pi_l, rel_MoveValue_imm sp a pi_l pi_r /\ S |-{p} p =>^{Imm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. left. repeat split; [apply not_strict_prefix_nil | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as [(-> & ? & ?) | (r & -> & ->)].
      * assert (sp <> pi_r).
        { intros ->. autorewrite with spath in get_q. discriminate. }
        exists (pi_r +++ [0]). split.
        -- left. repeat split; auto with spath.
        -- eapply Eval_Deref_MutBorrow. assumption.
           autorewrite with spath in get_q. exact get_q.
      * exists ((sp +++ r) +++ [0]). split.
        --- right. exists (r ++ [0]). split; autorewrite with spath; reflexivity.
        --- eapply Eval_Deref_MutBorrow. assumption.
            autorewrite with spath in get_q. exact get_q.
Qed.

Lemma eval_place_change_anon_not_in_spath S sp a perm p
  (Hperm : perm <> Imm) (fresh_a : fresh_anon S a) (valid_sp : valid_spath S sp)
  (not_in_abstraction : not_in_abstraction sp) :
  forall pi_r, (S.[sp <- bot],, a |-> S.[sp]) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - intros x. repeat split; [inversion 1 | apply not_strict_prefix_nil].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as ((-> & ?) & ?).
      assert (sp <> pi_r).
      { intros ->. autorewrite with spath in get_q. discriminate. }
      exists (pi_r +++ [0]). split.
      * repeat split; auto with spath.
      * eapply Eval_Deref_MutBorrow. assumption.
         autorewrite with spath in get_q. exact get_q.
Qed.

Definition rel_MergeAbs i j (p q : spath) :=
  p = q /\ ~in_abstraction i (fst p) /\ ~in_abstraction j (fst p) /\ ~in_abstraction i (fst q).

Lemma eval_place_MergeAbs S i j A B C perm p
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) (diff : i <> j) :
    forall pi_r, (S,,, i |-> C) |-{p} p =>^{perm} pi_r ->
    exists pi_l, rel_MergeAbs i j pi_l pi_r /\ (S,,, i |-> A,,, j |-> B) |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; intros (? & ?); easy.
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as (-> & ? & ? & ?). exists (pi_r +++ [0]).
      repeat split; [assumption.. | ].
      autorewrite with spath in get_q.
      eapply Eval_Deref_MutBorrow; autorewrite with spath; eassumption.
Qed.

Lemma eval_place_Fresh_MutLoan S sp l a perm p :
  forall pi_r, (S.[sp <- loan^m(l)],, a |-> borrow^m(l, S.[sp])) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon_not_in_spath sp a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; auto with spath.
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? ((-> & ?) & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + (* We must perform a single rewrite in order to have the information required to prove
       * ~prefix sp pi_r. *)
      rewrite sget_add_anon in get_q by assumption.
      assert (~prefix sp pi_r) by eauto with spath.
      autorewrite with spath in get_q.
      repeat split; eauto with spath. eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(* When changing the id of a mutable borrow at p, generally using the rule Leq_Reborrow_MutBorrow,
 * accessing any other node that the one in sp is unchanged. *)
(* Note: in its current form, this lemma cannot be used with rewrite, but only with erewrite.
 * This is because the equality does not involve l0. Replacing H with an existential could make
 * this lemma amenable to rewrite and autorewrite. *)
Lemma get_node_rename_mut_borrow S p q l0 l1
  (H : get_node (S.[p]) = borrowC^m(l0)) (diff_p_q : p <> q) :
  get_node ((rename_mut_borrow S p l1).[q]) = get_node (S.[q]).
Proof.
  destruct (decidable_prefix p q).
  - assert (strict_prefix p q) as (i & ? & <-) by auto with spath.
    autorewrite with spath. destruct i.
    + cbn. autorewrite with spath. reflexivity.
    (* If i > 0, then the path q is invalid. *)
    + cbn. rewrite sget_app.
      apply (f_equal arity) in H. rewrite<- length_children_is_arity in H.
      apply length_1_is_singleton in H. cbn - [children]. destruct H as (? & ->).
      reflexivity.
  - autorewrite with spath. reflexivity.
Qed.

(* In the state `rename_mut_borrow S p l1`, compared to S, only the node at p is changed.
 * Thus, if we read at a place q that is not a prefix of p, no node is changed. *)
Lemma sget_reborrow_mut_borrow_not_prefix S p q l0 l1
  (H : get_node (S.[p]) = borrowC^m(l0)) (G : ~prefix q p) :
  (rename_mut_borrow S p l1).[q] = S.[q].
Proof.
  apply value_get_node_ext. intros r. rewrite <-!sget_app.
  eapply get_node_rename_mut_borrow.
  - eassumption.
  - intros ->. apply G. exists r. reflexivity.
Qed.

Lemma valid_spath_rename_mut_borrow S p q l0 l1
  (H : get_node (S.[p]) = borrowC^m(l0)) :
  valid_spath (rename_mut_borrow S p l1) q <-> valid_spath S q.
Proof.
  split.
  - intros valid_q. destruct (decidable_prefix (p +++ [0]) q) as [(r & <-) | ].
    + rewrite valid_spath_app in *. destruct valid_q as (_ & valid_r). split.
      * apply valid_spath_app_last_get_node_not_zeroary. rewrite H. constructor.
      * autorewrite with spath in valid_r. exact valid_r.
    + rewrite sset_not_prefix_valid. exact valid_q.
      eapply (not_prefix_one_child (rename_mut_borrow S p l1)); [ | eassumption..].
      rewrite length_children_is_arity. autorewrite with spath. reflexivity.
  - intros valid_q. destruct (decidable_prefix (p +++ [0]) q) as [(r & <-) | ].
    + autorewrite with spath in *. rewrite valid_spath_app in *. split.
      * validity.
      * econstructor.
        -- autorewrite with spath. reflexivity.
        -- apply valid_spath_app. autorewrite with spath. rewrite valid_spath_app. auto.
    + rewrite <-sset_not_prefix_valid by eauto with spath. assumption.
Qed.

Lemma sset_reborrow_mut_borrow_not_prefix S p q l0 l1 v
  (H : get_node (S.[p]) = borrowC^m(l0)) (G : ~prefix q p) :
  (rename_mut_borrow S p l1).[q <- v] = rename_mut_borrow (S.[q <- v]) p l1.
Proof.
  destruct (decidable_valid_spath S q).
  - destruct (decidable_prefix p q) as [ | ].
    + assert (prefix (p +++ [0]) q) as (r & <-) by eauto with spath.
      autorewrite with spath. reflexivity.
    + assert (disj p q) by reduce_comp. states_eq.
  - rewrite !(sset_invalid _ q); erewrite ?valid_spath_rename_mut_borrow; eauto.
Qed.

Lemma not_contains_rename_mut_borrow S p q l0 l1 P :
  get_node (S.[p]) = borrowC^m(l0) -> ~P (borrowC^m(l0)) ->
  not_value_contains P ((rename_mut_borrow S p l1).[q]) -> not_value_contains P (S.[q]).
Proof.
  destruct (decidable_valid_spath S q) as [valid_q | ].
  - intros get_at_p ? Hnot_contains r valid_r.
    specialize (Hnot_contains r). rewrite <-!sget_app in *.
    destruct (decidable_spath_eq p (q +++ r)) as [-> | ].
    + autorewrite with spath. rewrite get_at_p. assumption.
    + erewrite get_node_rename_mut_borrow in Hnot_contains; [ | eassumption..].
      apply Hnot_contains. apply valid_spath_app.
      rewrite valid_spath_rename_mut_borrow by eassumption.
      rewrite valid_spath_app. auto.
  - intros ? ?. rewrite !sget_invalid; [auto.. | ].
    intros G. apply H. erewrite valid_spath_rename_mut_borrow in G by eassumption. exact G.
Qed.

Lemma eval_place_Reborrow_MutBorrow S sp l0 l1 a perm p
    (get_borrow : get_node (S.[sp]) = borrowC^m(l0)) pi_r :
  (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(l1))) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  revert pi_r. apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - rewrite add_anon_preserves_vars_dom, sset_preserves_vars_dom. reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption.
      destruct (decide (sp = pi_r)) as [<- | ].
      * eapply Eval_Deref_MutBorrow; eassumption.
      * autorewrite with spath in get_q.
        (* Note: this rewrite take up to 2s, with 80% of time spent on eauto with spath. *)
        erewrite get_node_rename_mut_borrow in get_q by eassumption.
        eapply Eval_Deref_MutBorrow; eassumption.
Qed.

Lemma eval_place_AnonValue S a perm p :
  forall pi_r, (S,, a |-> bot) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption. autorewrite with spath in get_q.
      eapply Eval_Deref_MutBorrow; eassumption.
Qed.

Definition rel_Abs_ClearValue i j (p q : spath) := p = q /\ fst p <> encode_abstraction (i, j).

Lemma eval_place_Abs_ClearValue S i j v perm p :
  abstraction_contains_value S i j v -> not_contains_loan v ->
  forall pi_r, (remove_abstraction_value S i j) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_Abs_ClearValue i j pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  intros ? ?. apply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros ? pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + repeat split; try assumption. rewrite sget_remove_abstraction_value in get_q by assumption.
      eapply Eval_Deref_MutBorrow; eassumption.
Qed.

(* TODO: move *)
Lemma valid_spath_add_abstraction S i A sp :
  valid_spath (S,,, i |->  A) sp -> ~in_abstraction i (fst sp) -> valid_spath S sp.
Proof.
  unfold not_in_abstraction. intros (v & H & ?) ?.
  exists v. split; [ | assumption].
  rewrite <-H, get_at_accessor_add_abstraction_notin; auto.
Qed.

(* Suppose that Sl <= Sr (with a base case), and that p evaluates to a spath pi in Sr
   (Sr |-{p} p =>^{perm} pi).
   This tactic chooses the right lemmas to apply in order to prove that p reduces to a spath pi' in Sl, and generates facts about pi'.
   It finally clears the initial hypothesis.
 *)
Ltac eval_place_preservation :=
  let eval_p_in_Sl := fresh "eval_p_in_Sl" in
  let pi_l := fresh "pi_l" in
  let rel_pi_l_pi_r := fresh "rel_pi_l_pi_r" in
  lazymatch goal with
  | get_integer : get_node (?S.[?sp]) = LLBC_plus_intC ?n,
    H : (?S.[?sp <- LLBC_plus_symbolic]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply (eval_place_ToSymbolic _ _ _ _ _ _ get_integer) in H;
        destruct H as (eval_p_in_Sl & ?)
  | fresh_a : fresh_anon ?S ?a,
    fresh_i : fresh_abstraction ?S ?i,
    Hto_abs : to_abs ?v ?A,
    Heval : (?S,,, ?i |-> ?A) |-{p} ?p =>^{?perm} ?pi |- _ =>
        let _valid_pi := fresh "_valid_pi" in
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        (* Proving that pi is a valid spath of (remove_anon a S),,, i |-> A *)
        pose proof (eval_place_valid _ _ _ _ Heval) as _valid_pi;
        apply (eval_place_ToAbs _ _ _ _ _ _ _ fresh_a fresh_i Hto_abs) in Heval;
        destruct Heval as (? & (-> & pi_not_in_abstraction & pi_not_in_a) & eval_p_in_Sl);
        (* We can then prove that pi is a valid spath of (remove_anon a S) *)
        pose proof (valid_spath_add_abstraction _ _ _ _ _valid_pi pi_not_in_abstraction) as valid_pi;
        clear _valid_pi
  | fresh_a : fresh_anon ?S ?a,
    no_loan : not_contains_loan ?v,
    Heval : ?S |-{p} ?p =>^{?perm} ?pi |- _ =>
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        pose proof (eval_place_valid _ _ _ _ Heval) as valid_pi;
        apply (eval_place_RemoveAnon _ _ _ _ _ fresh_a no_loan) in Heval;
        destruct Heval as (? & (-> & pi_not_a) & eval_p_in_Sl)
  (* Case MoveValue *)
  (* Preservation of place evaluation with permission Imm. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{Imm} ?pi |- _ =>
        apply (eval_place_MoveValue_imm _ _ _ _ fresh_a valid_sp Hnot_in_abstraction) in H;
        destruct H as (pi_l & rel_pi_l_pi_r & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Mut or Mov. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    Hnot_in_abstraction : not_in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_change_anon_not_in_spath in H;[ | discriminate | assumption..];
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  | fresh_i : fresh_abstraction ?S ?i, fresh_j : fresh_abstraction ?S ?j,
    Hmerge : merge_abstractions ?A ?B ?C, diff : ?i <> ?j,
    Heval : (?S,,, ?i |-> ?C) |-{p} ?p =>^{?perm} ?pi_r
    |- _ =>
        apply (eval_place_MergeAbs _ _ _ _ _ _ _ _ fresh_i fresh_j Hmerge diff) in Heval;
        destruct Heval as (? & (-> & ? & ? & ?) & eval_p_in_Sl)
  (* Case Fresh_MutLoan *)
  | H : (?S.[?sp <- loan^m(?l)],, ?a |-> borrow^m(?l, ?S.[?sp])) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_Fresh_MutLoan in H;
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)
  (* Case Abs_ClearValue *)
  | H : abstraction_contains_value ?S ?i ?j ?v,
    no_loan : not_contains_loan ?v,
    Heval : remove_abstraction_value ?S ?i ?j |-{p} ?p =>^{?perm} ?pi_r |- _ =>
        eapply eval_place_Abs_ClearValue in Heval; [ | eassumption..];
        destruct Heval as (? & (-> & ?) & eval_p_in_Sl)
  end.

Lemma fresh_anon_diff S a b v
  (get_a : get_at_accessor S (anon_accessor a) = Some v)
  (fresh_b : fresh_anon S b) : a <> b.
Proof. congruence. Qed.
Hint Resolve fresh_anon_diff : spath.
Hint Resolve<- fresh_anon_sset : spath.
Hint Resolve anon_accessor_diff : spath.

(* Lemmas about add_anon. *)
Lemma add_anons_insert S i A v S' :
  lookup i A = None -> add_anons S (insert i v A) S' ->
  exists a, fresh_anon S a /\ add_anons (S,, a |-> v) A S'.
Proof.
  intros ? H. inversion H as [? ? ? Hunion]; subst.
  apply union_maps_insert_r_l in Hunion; [ | assumption].
  destruct Hunion as (a & G & fresh_a).
  exists a. unfold fresh_anon. rewrite get_at_anon. split; [assumption | ].
  replace (insert _ _ _) with (anons (S,, a |-> v)) in G by reflexivity.
  apply AddAnons in G. exact G.
Qed.

Corollary add_anons_delete S i A v S' :
  lookup i A = Some v -> add_anons S A S' ->
  exists a, fresh_anon S a /\ add_anons (S,, a |-> v) (delete i A) S'.
Proof.
  intros H G. apply add_anons_insert with (i := i).
  - apply lookup_delete.
  - rewrite insert_delete; assumption.
Qed.

Lemma add_anons_empty S S' : add_anons S empty S' -> S = S'.
Proof.
  intros H. destruct S. inversion H as [? ? ? G]; subst. inversion G; subst; cbn in *.
  - reflexivity.
  - exfalso. eapply insert_non_empty. eassumption.
Qed.

Lemma add_anons_singleton S i v S' : add_anons S (singletonM i v) S' ->
  exists a, fresh_anon S a /\ S' = S,, a |-> v.
Proof.
  intros (a & fresh_a & H)%add_anons_insert; [ | now simpl_map].
  exists a. split; [assumption | ]. apply add_anons_empty in H. congruence.
Qed.

(* An alternative definition of add_anon. *)
Inductive add_anons' : LLBC_plus_state -> Pmap LLBC_plus_val -> LLBC_plus_state -> Prop :=
  | AddAnons_empty S : add_anons' S empty S
  | AddAnons_insert S A S' a i v :
      lookup i A = None -> fresh_anon S a -> add_anons' (S,, a |-> v) A S' ->
          add_anons' S (insert i v A) S'
.

Lemma add_anons_alt S A S' : add_anons S A S' <-> add_anons' S A S'.
Proof.
  split.
  - intros H. destruct H as [? ? ? H]. remember (anons S) as _anons eqn:EQN.
    revert S EQN. induction H as [ | ? A anons' i a v ? ? ? IH].
    + intros S ->. destruct S; cbn. constructor.
    + intros S ->. apply AddAnons_insert with (a := a);
      [assumption | unfold fresh_anon; now rewrite get_at_anon | ].
      specialize (IH (S,, a |-> v)). unfold add_anon in IH. cbn in IH.
      apply IH. reflexivity.
  - induction 1 as [S | ? ? ? ? ? ? ? fresh_a ? IH].
    + destruct S. constructor. constructor.
    + inversion IH; subst. unfold add_anon in *; cbn in *. constructor.
      unfold fresh_anon in fresh_a. rewrite get_at_anon in fresh_a.
      econstructor; eassumption.
Qed.

(* Commutation lemmas for add_anons. *)
Lemma add_anons_sset S S' A p v :
  add_anons S A S' -> valid_spath S p -> add_anons (S.[p <- v]) A (S'.[p <- v]).
Proof.
  rewrite !add_anons_alt. induction 1.
  - constructor.
  - intros Hvalid. eapply AddAnons_insert.
    + assumption.
    + eauto with spath.
    + autorewrite with spath in IHadd_anons'. apply IHadd_anons'. validity.
Qed.

Lemma add_anons_get_at_accessor S S' A i v :
  add_anons S A S' -> get_at_accessor S i = Some v -> get_at_accessor S' i = Some v.
Proof.
  rewrite add_anons_alt. induction 1.
  - auto.
  - intros ?. rewrite get_at_accessor_add_anon in * |- by congruence. auto.
Qed.

Lemma add_anons_sget S S' A p :
  add_anons S A S' -> valid_spath S p -> S'.[p] = S.[p].
Proof.
  intros ? (? & H & _). unfold sget. erewrite add_anons_get_at_accessor, H by eassumption.
  reflexivity.
Qed.

Lemma add_anons_add_abstraction S A B S' i :
  add_anons (S,,, i |-> B) A S' ->
      exists S'', S' = S'',,, i |-> B /\ add_anons S A S''.
Proof.
  setoid_rewrite add_anons_alt.
  remember (S,,, i |-> B) eqn:EQN. intros H. revert S EQN. induction H; intros ? ->.
  - eexists. split; [reflexivity | constructor].
  - edestruct IHadd_anons' as (S'' & ? & ?).
    { rewrite <-add_abstraction_add_anon. reflexivity. }
    rewrite fresh_anon_add_abstraction in * |-.
    eexists.  split; [eassumption | ]. econstructor; eassumption.
Qed.

(* TODO: name *)
Lemma add_anons_add_abstraction' S A B S' i :
  add_anons S A S' -> add_anons (S,,, i |-> B) A (S',,, i |-> B).
Proof.
  setoid_rewrite add_anons_alt. induction 1.
  - constructor.
  - autorewrite with spath in * |-. econstructor; [assumption | | eassumption].
    eauto with spath.
Qed.

Lemma add_anons_remove_abstraction_value S A S' i j :
  add_anons S A S' ->
  add_anons (remove_abstraction_value S i j) A (remove_abstraction_value S' i j).
Proof.
  rewrite !add_anons_alt. induction 1.
  - constructor.
  - autorewrite with spath in * |-. econstructor; [assumption | | eassumption].
    apply fresh_anon_remove_abstraction_value. assumption.
Qed.

Lemma add_anons_fresh_abstraction S A S' i :
  add_anons S A S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof.
  rewrite add_anons_alt. induction 1.
  - auto.
  - rewrite <-fresh_abstraction_add_anon in * |-. assumption.
Qed.
Hint Resolve add_anons_fresh_abstraction : spath.

(* Note: this could be made into a tactic. *)
Lemma prove_add_anons S0 A S1 :
  (exists S', add_anons S' A S1 /\ S0 = S') -> add_anons S0 A S1.
Proof. intros (? & ? & ->). assumption. Qed.

(* TODO: move *)
Lemma valid_spath_remove_abstraction_value S sp i j :
  valid_spath S sp -> fst sp <> encode_abstraction (i, j) ->
  valid_spath (remove_abstraction_value S i j) sp.
Proof.
  intros (v & ? & ?) ?. exists v. split; [ | assumption].
  rewrite get_map_remove_abstraction_value. simpl_map. reflexivity.
Qed.
Hint Resolve valid_spath_remove_abstraction_value : spath.

Lemma add_anons_assoc S0 S1 S2 S'2 A B C :
  union_maps A B C -> add_anons S0 B S1 -> add_anons S1 A S2 -> add_anons S0 C S'2 ->
  equiv_states S2 S'2.
Proof.
  intros ? H G K.
  (* The variables and abstractions of states S0, S1, S2 and S'2 are the same. *)
  (* We just need to prove that the anonymous variables are equivalent. We need a little bit of
   * boilerplate tactics to inverse everything and use the lemma union_maps_assoc. *)
  inversion G; subst. inversion H; subst. inversion K; subst. cbn in *.
  rewrite <-equiv_states_perm. split; [ | split].
  - reflexivity.
  - cbn. eapply union_maps_assoc; [ | | eassumption..]; eassumption.
  - intros ?. reflexivity.
Qed.

(*
Ltac prove_add_anons :=
  lazymatch goal with
  | |- add_anons ?S0 ?S1 =>
      let S := fresh S in
      assert (exists S, S
  end.
 *)

(* TODO: move *)
Lemma get_abstraction_sset i S p v :
  ~in_abstraction i (fst p) -> lookup i (abstractions (S.[p <- v])) = lookup i (abstractions S).
Proof.
  intros H. unfold sset, alter_at_accessor. cbn. repeat autodestruct.
  intros. cbn. apply lookup_alter_ne. intros ?. subst.
  eapply H. rewrite decode'_is_Some in * |-. eexists. symmetry. eassumption.
Qed.
Hint Rewrite get_abstraction_sset using assumption : spath.

Ltac leq_step_left :=
  let a := fresh "a" in
  lazymatch goal with
  |  |- ?leq_star (?vl, ?Sl,, ?b |-> ?w) ?vSr =>
      eapply prove_leq_val_state_anon_left;
        [eauto with spath |
         intros a ? ? ?; eexists; split |
        ]
  (* When proving a goal `leq (vl, Sl) ?vSr`, using this tactic creates three subgoals:
     1. leq_base (Sl,, a |-> v) ?vSm
     2. ?vSm = ?Sm,, a |-> ?vm
     3. leq (?vm, ?Sm) ?vSr *)
  (* Note: the hypothesis that a is fresh in ?Sm creates problems.
     Indeed, ?Sm is an existential and it can be accidently instantiated to a wrong value by
     eauto. That's why we're removing this hypothesis.
     TODO: remove it from the hypotheses of the lemma? *)
  | |- ?leq_star (?vl, ?Sl) ?vSr =>
      eapply prove_leq_val_state_left_to_right;
        [intros a _ ?; eexists; split; [
          repeat rewrite <-add_abstraction_add_anon |
          ] |
        ]
  end.

Lemma operand_preserves_LLBC_plus_rel op :
  forward_simulation leq_base^* leq_val_state_base^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  (* op = IntConst n *)
  - destruct Hle.
    + execution_step. { constructor. }
      leq_step_left.
      { eapply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_ToAbs with (a := a) (i := i) (A := A).
        all: autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply Leq_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply Leq_MoveValue with (sp := sp) (a := a).
        autorewrite with spath. assumption. eassumption. validity. assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_MergeAbs _ i j A B C); assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Fresh_MutLoan _ sp l a).
        apply not_state_contains_add_anon. assumption. not_contains.
        eassumption.
        autorewrite with spath. assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_Reborrow_MutBorrow _ sp l0 l1 a).
        apply not_state_contains_add_anon. assumption. not_contains. eassumption.
        autorewrite with spath. assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_step_left.
      { apply (Leq_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.
    + execution_step. { constructor. }
      leq_val_state_add_anon.
      { apply (Leq_AnonValue _ a); [assumption.. | ]. eassumption. }
      { reflexivity. }
      reflexivity.

  (* op = copy p *)
  - admit.

  (* op = move p *)
  - destruct Hle.
    (* Leq-ToSymbolic *)
    + eval_place_preservation.
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the value we turn into a symbolic value is in the place we move. *)
      * autorewrite with spath in * |-.
        execution_step.
        { constructor. eassumption.
          (* TODO: automatize *)
          eapply not_value_contains_vset_rev with (p := q).
          autorewrite with spath.
          eapply not_value_contains_zeroary; rewrite H. reflexivity. easy. eassumption.
          eapply not_value_contains_vset_rev with (p := q).
          autorewrite with spath.
          eapply not_value_contains_zeroary; rewrite H. reflexivity. discriminate. eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := (anon_accessor a, q)) (n := n).
          all: autorewrite with spath; assumption. }
        { autorewrite with spath. reflexivity. }
        apply reflexive_eq. states_eq.

      (* Case 2: the value we turn into a symbolic value is disjoint to the place we move. *)
      * assert (disj sp pi) by reduce_comp.
        autorewrite with spath in * |-.
        execution_step. { apply Eval_move; eassumption. }
        leq_step_left.
        { apply Leq_ToSymbolic with (sp := sp) (n := n).
          all: autorewrite with spath; assumption. }
        { autorewrite with spath. reflexivity. }
        apply reflexive_eq. states_eq.

    (* Leq-ToAbs *)
    + eval_place_preservation.
      autorewrite with spath in *.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath in *.
      leq_step_left.
      { apply Leq_ToAbs with (a := a) (i := i); [ | autorewrite with spath | ]; eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-RemoveAnon *)
    + eval_place_preservation.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; eassumption. }
      autorewrite with spath. leq_step_left.
      { apply Leq_RemoveAnon with (a := a). eauto with spath.
        all: autorewrite with spath; assumption. }
      { reflexivity. }
      reflexivity.

    (* Leq-MoveValue *)
    + eval_place_preservation.
      (* The place pi we move does not contain any bottom value is the right state, as a
       * condition of the move rule.
       * The right state is Sr = S.[sp <- bot],, a |-> S.[sp].
       * That means that that sp cannot be inside sp, thus pi and sp are disjoint. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_bot. eapply move_no_bot with (p := q).
        apply vset_same_valid. validity. autorewrite with spath. reflexivity. }
      assert (disj sp pi) by reduce_comp.
      autorewrite with spath in * |-.
      execution_step. { apply Eval_move; eassumption. }
      leq_val_state_add_anon.
       { apply Leq_MoveValue with (sp := sp) (a := a).
         autorewrite with spath. assumption. assumption. validity. assumption. }
       { autorewrite with spath. reflexivity. }
      apply reflexive_eq. states_eq.

    (* Leq-MergeAbs *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      execution_step. { apply Eval_move. eassumption. all: autorewrite with spath; assumption. }
      autorewrite with spath. leq_step_left.
      { apply Leq_MergeAbs with (A := A) (B := B) (i := i) (j := j); eauto with spath. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-Fresh-MutLoan *)
    + eval_place_preservation.
      autorewrite with spath in * |-.
      (* Because the path pi we move does not contain any loan, it cannot contain the spath sp
       * where the mutable loan is written. *)
      (* Note: this is similar to a reasonning we do for the case Leq_MoveValue. Make a lemma? *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_loan.
        eapply move_no_loan with (p := q). apply vset_same_valid. validity.
        autorewrite with spath. constructor. }
      assert (disj pi sp) by reduce_comp. autorewrite with spath in *.
      execution_step. { apply Eval_move; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_Fresh_MutLoan with (sp := sp) (l := l).
        (* TODO: the tactic not_contains should solve it. *)
        apply not_state_contains_add_anon. not_contains. not_contains.
        eassumption. autorewrite with spath. assumption. }
      { autorewrite with spath. reflexivity. }
      apply reflexive_eq. states_eq.

    (* Leq-Reborrow-MutBorrow *)
    + apply eval_place_Reborrow_MutBorrow in Heval; [ | exact get_borrow].
      destruct Heval as (? & (-> & ?) & eval_p_in_Sl).
      autorewrite with spath in * |-.
      destruct (decidable_prefix pi sp) as [(q & <-) | ].

      (* Case 1: the spath sp we reborrow is in the place pi we move. *)
      * execution_step.
        { apply Eval_move. eassumption.
          eapply not_contains_rename_mut_borrow; eauto with spath.
          eapply not_contains_rename_mut_borrow; eauto with spath. }
         leq_val_state_add_anon.
        (* Because the place we reborrow was at sp +++ q, and that we move and return S.[sp],
         * the borrow is now in the anonymous value we evaluate a0, at path q. *)
         (* TODO: rename a0 *)
        { apply Leq_Reborrow_MutBorrow with (sp := (anon_accessor a0, q)) (l1 := l1).
          not_contains. eassumption. autorewrite with spath. eassumption. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath. reflexivity.

       (* Case 2: the spath sp we reborrow is not in the place pi we move. *)
      * execution_step.
        { apply Eval_move. eassumption.
          all: erewrite sget_reborrow_mut_borrow_not_prefix in * by eassumption; assumption. }
        leq_val_state_add_anon.
        { apply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1).
          not_contains. eassumption. autorewrite with spath. eassumption. }
        { autorewrite with spath. reflexivity. }
        autorewrite with spath.
        erewrite sget_reborrow_mut_borrow_not_prefix by eassumption.
        erewrite sset_reborrow_mut_borrow_not_prefix by eauto with spath. reflexivity.

    (* Leq-Abs-ClearValue *)
    + eval_place_preservation. autorewrite with spath in *.
      execution_step. { constructor; eassumption. }
      leq_step_left.
      { eapply Leq_Abs_ClearValue with (i := i) (j := j); autorewrite with spath; eassumption. }
      { autorewrite with spath. reflexivity. }
      reflexivity.

    (* Leq-AnonValue *)
    + apply eval_place_AnonValue in Heval.
      destruct Heval as (? & (-> & ?) & eval_p_in_Sl).
      autorewrite with spath in *.
      execution_step. { econstructor; eassumption. }
      leq_val_state_add_anon.
      { apply Leq_AnonValue; eassumption. }
      { reflexivity. }
      reflexivity.
Abort.

Notation node_measure n :=
  match n with
  | LLBC_plus_symbolicC => 2
  | _ => 1
  end.
Definition measure S := sweight (fun c => node_measure c) S + size (abstractions S).
Notation abs_measure S := (map_sum (vweight (fun c => node_measure c)) S).

(* TODO: meaningful comment *)
Variant leq_state_base_n : nat -> LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Leq_ToSymbolic_n S sp x :
    get_node (S.[sp]) = LLBC_plus_intC x -> leq_state_base_n 0 S (S.[sp <- LLBC_plus_symbolic])
| Leq_ToAbs_n S a i v A
    (fresh_a : fresh_anon S a)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base_n 0 (S,, a |-> v) (S,,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon_n S a v
    (fresh_a : fresh_anon S a)
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v) :
    leq_state_base_n (1 + vweight (fun c => node_measure c) v) (S,, a |-> v) S
| Leq_MoveValue_n S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (Hnot_in_abstraction : not_in_abstraction sp) n :
    leq_state_base_n n S (S.[sp <- bot],, a |-> S.[sp])
| Leq_MergeAbs_n S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base_n (abs_measure A + abs_measure B - abs_measure C + 2) 
                                (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan_n S sp l a
    (fresh_l1 : is_fresh l S)
    (fresh_a : fresh_anon S a)
    (* We need a hypothesis that ensures that sp is valid. We could just add valid_spath S sp.
       I am going a step further: there should not be bottoms in borrowed values. *)
    (no_bot : not_contains_bot (S.[sp])) n :
    leq_state_base_n n S (S.[sp <- loan^m(l)],, a |-> borrow^m(l, S.[sp]))
| Leq_Reborrow_MutBorrow_n (S : LLBC_plus_state) (sp : spath) (l0 l1 : loan_id) (a : anon)
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow : get_node (S.[sp]) = borrowC^m(l0)) :
    leq_state_base_n 0 S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(l1)))
| Leq_Abs_ClearValue_n S i j v :
    abstraction_contains_value S i j v -> not_contains_loan v -> not_contains_borrow v ->
    leq_state_base_n 1 S (remove_abstraction_value S i j)
| Leq_AnonValue_n S a (is_fresh : fresh_anon S a) :
    leq_state_base_n 0 S (S,, a |-> bot)
.

Lemma size_abstractions_sset S p v : size (abstractions (S.[p <- v])) = size (abstractions S).
Proof.
  unfold sset, alter_at_accessor. cbn. repeat autodestruct. cbn.
  rewrite<- !size_dom, dom_alter_L. reflexivity.
Qed.

Lemma size_abstraction_add_anon S a v :
  size (abstractions (S,, a |-> v)) = size (abstractions S).
Proof. reflexivity. Qed.

Lemma size_abstraction_add_abstraction S i A (H : fresh_abstraction S i) :
  size (abstractions (S,,, i |-> A)) = 1 + size (abstractions S).
Proof. cbn. rewrite map_size_insert, H. reflexivity. Qed.

Hint Rewrite size_abstractions_sset : weight.
Hint Rewrite size_abstraction_add_anon : weight.
Hint Rewrite size_abstraction_add_abstraction using auto with spath; fail : weight.

Lemma leq_state_base_n_decreases n Sl Sr (H : leq_state_base_n n Sl Sr) :
  measure Sl < measure Sr + n.
Proof.
  unfold measure. destruct H.
  - autorewrite with weight. weight_given_node. lia.
  - autorewrite with weight. destruct Hto_abs.
    + autorewrite with weight. lia.
    + autorewrite with weight. destruct Hv; cbn; lia.
  - autorewrite with weight. cbn. lia.
  - autorewrite with weight. lia.
  - autorewrite with weight. lia.
  - autorewrite with weight. lia.
  - weight_inequality.
    (* I don't want to prove that. *)
  - admit.
  - weight_inequality.
Admitted.

Hint Resolve no_ancestor_sset_rev : spath.

Lemma is_integer_valid S p : is_integer (S.[p]) -> valid_spath S p.
Proof. intros H. apply valid_get_node_sget_not_bot. inversion H; easy. Qed.
Hint Resolve is_integer_valid : spath.

(* TODO: move *)
Lemma remove_abstraction_value_add_abstraction S i j A :
  remove_abstraction_value (S,,, i |-> A) i j = S,,, i |-> (delete j A).
Proof.
  apply state_eq_ext.
  - rewrite get_map_remove_abstraction_value.
    apply map_eq. intros x.
    destruct (decide (encode_abstraction (i, j) = x)) as [<- | H].
    + rewrite lookup_delete, get_at_accessor_add_abstraction, lookup_delete. reflexivity.
    + rewrite lookup_delete_ne by assumption.
      destruct (decide (in_abstraction i x)) as [(k & ->) | ].
      * rewrite !get_at_accessor_add_abstraction.
        symmetry. apply lookup_delete_ne. intros ->. auto.
      * rewrite !get_at_accessor_add_abstraction_notin by assumption. reflexivity.
  - rewrite get_extra_remove_abstraction_value, !get_extra_add_abstraction. reflexivity.
Qed.
Hint Rewrite remove_abstraction_value_add_abstraction : spath.

(* TODO: move *)
Lemma not_in_borrow_add_abstraction S i A sp (H : ~in_abstraction i (fst sp)) :
  not_in_borrow (S,,, i |-> A) sp <-> not_in_borrow S sp.
Proof.
  split.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    rewrite sget_add_abstraction; assumption.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    rewrite sget_add_abstraction in *; assumption.
Qed.

(* TODO: similar lemma for add_anon *)
(*
Lemma not_in_borrow_remove_anon S a sp (H : fst sp <> anon_accessor a) :
  not_in_borrow (remove_anon a S) sp <-> not_in_borrow S sp.
Proof.
  split.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    autorewrite with spath. assumption.
  - intros G ? ? K. eapply G; [ | exact K]. destruct K as (? & ? & <-).
    autorewrite with spath in *. assumption.
Qed.
 *)

Hint Resolve-> not_in_borrow_add_abstraction : spath.
(*Hint Resolve-> not_in_borrow_remove_anon : spath.*)

Lemma remove_loans_elem_right A B A' B' i :
  remove_loans A B A' B' ->
  lookup i B = lookup i B' \/ exists l, lookup i B = Some (borrow^m(l, LLBC_plus_symbolic)).
Proof.
  intros H. induction H.
  - left. reflexivity.
  - destruct (decide (i = j)) as [<- | ].
    + right. destruct IHremove_loans as [-> | ]; [ | assumption]. firstorder.
    + simpl_map. assumption.
Qed.

Lemma merge_no_loan A B C :
  merge_abstractions A B C -> map_Forall (fun _ => not_contains_loan) C ->
  map_Forall (fun _ => not_contains_loan) B.
Proof.
  intros (A' & B' & H & Hunion) G i.
  apply remove_loans_elem_right with (i := i) in H.
  destruct H as [-> | (l & ->) ].
  - intros v ?.  eapply union_contains_right in Hunion; [ | eassumption].
    destruct Hunion as (? & ?). eapply G. eassumption.
  - intros ? [=<-]. unfold not_contains_loan. not_contains.
Qed.

Definition leq_n (n : nat) := chain (measured_closure leq_state_base_n n) equiv_states.

Lemma leq_n_step m n Sl Sm Sr :
  leq_state_base_n m Sl Sm -> m <= n -> leq_n (n - m) Sm Sr -> leq_n n Sl Sr.
Proof.
  intros ? ? (Sr' & ? & ?). replace n with (m + (n - m)) by lia.
  exists Sr'. split.
  - eapply MC_trans.
    + constructor. eassumption.
    + assumption.
  - assumption.
Qed.

Lemma leq_n_by_equivalence n S S' : equiv_states S S' -> leq_n n S S'.
Proof. intros ?. exists S. split; [reflexivity | assumption]. Qed.

Lemma add_anon_equivalence S a b v :
  fresh_anon S a -> fresh_anon S b -> equiv_states (S,, a |-> v) (S,, b |-> v).
Proof.
  intros fresh_a fresh_b. apply equiv_states_perm. split; [ | split].
  - reflexivity.
  - cbn. apply equiv_map_insert; [reflexivity | | ]; rewrite <-get_at_anon; assumption.
  - intros ?. reflexivity.
Qed.

Lemma exists_add_anon S A : exists S', add_anons S A S'.
Proof.
  destruct (exists_union_maps A (anons S)) as (anons' & ?).
  eexists. constructor. eassumption.
Qed.

Inductive add_anonymous_bots : nat -> LLBC_plus_state -> LLBC_plus_state -> Prop :=
  | Add_no_bots S : add_anonymous_bots 0 S S
  | Add_anonymous_bot n S a S' :
      add_anonymous_bots n S S' -> fresh_anon S' a ->
      add_anonymous_bots (1 + n) S (S',, a |-> bot).

Lemma add_anonymous_bots_fresh_abstraction n S S' i :
  add_anonymous_bots n S S' -> fresh_abstraction S i -> fresh_abstraction S' i.
Proof. induction 1; eauto with spath. Qed.
Hint Resolve add_anonymous_bots_fresh_abstraction : spath.

Lemma abs_measure_remove_loans A B A' B' :
  remove_loans A B A' B' -> abs_measure A' <= abs_measure A /\ abs_measure B' <= abs_measure B.
Proof.
  induction 1.
  - auto.
  - repeat lazymatch goal with
    | H : lookup ?i ?A = Some ?v |- _ =>
        apply (map_sum_delete (vweight (fun c => node_measure c))) in H
    end.
    lia.
Qed.

(* The crucial lemma for the commutation between leq and reorganizations, when we end a region C that
 * is the merge of two regions A and B. By definition, C is the union of A' and B' where we removed
 * common loans and borrows.
 * After ending the region B and placing its borrows in anonymous bindings, we must end all the
 * borrows that are in B \ B', and the corresponding loans in A \ A'.
 * TODO: explain the add_anonymous_bots operation. *)
Lemma end_removed_loans S0 S0_anons i A B A' B'
  (H : remove_loans A B A' B') (fresh_i : fresh_abstraction S0 i) :
  add_anons (S0,,, i |-> A) B S0_anons ->
  exists n S1,
    add_anonymous_bots n S0 S1 /\
    2 * n <= abs_measure A + abs_measure B - abs_measure A' - abs_measure B' /\
    exists S1_anons, reorg^* S0_anons S1_anons /\
                     add_anons (S1,,, i |-> A') B' S1_anons.
Proof.
  intros Hadd_anons. induction H as [ | A' B' j ? l Hremove_loans IH HA' HB'].
  - eexists 0, _. repeat split.
    + constructor.
    + apply le_0_n.
    + exists S0_anons; easy.
  - clear Hadd_anons.
    destruct IH as (n & S1 & ? & ? & S1_anons & ? & Hadd_anons).
    eapply add_anons_delete in Hadd_anons; [ | eassumption].
    destruct Hadd_anons as (a & fresh_a%fresh_anon_add_abstraction & Hadd_anons).
    eexists (1 + n), _.
    split.
    { econstructor; eassumption. }
    split.
    { apply (map_sum_delete (vweight (fun c => node_measure c))) in HA', HB'.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      remember (vweight _ _) eqn:EQN. cbn in EQN. subst.
      apply abs_measure_remove_loans in Hremove_loans. lia. }
    eexists. split.
    { transitivity S1_anons; [assumption | ].
      constructor. apply Reorg_end_borrow_m_in_abstraction
        with (l := l) (q := (anon_accessor a, [])) (i' := i) (j' := j).
        - inversion 1.
           (* We need lemmas of commutation between add_anons and regular operations. *)
        - eapply add_anons_get_at_accessor; [eassumption | ].
          (* TODO: autorewrite *)
          autorewrite with spath. rewrite get_at_accessor_add_abstraction.
          simpl_map. reflexivity.
        - erewrite add_anons_sget by eauto with spath.
          autorewrite with spath. reflexivity.
        - erewrite add_anons_sget. 2: eassumption.
          (* TODO: automatize *)
          2: { apply valid_spath_anon. econstructor. reflexivity. constructor. }
          autorewrite with spath. constructor.
        - intros ? ?. eauto with spath.
        - intros ? (? & ?). inversion H2. }
    eapply prove_add_anons. eexists. split.
    { apply add_anons_sset. apply add_anons_remove_abstraction_value. eassumption.
      eauto with spath. }
    { autorewrite with spath. reflexivity. }
Qed.

(* TODO: move *)
Lemma add_anon_add_anons' S A a v S' :
  add_anons' (S,, a |-> v) A S' -> fresh_anon S a ->
      exists S'', S' = S'',, a |-> v /\ add_anons' S A S'' /\ fresh_anon S'' a.
Proof.
  intros H. remember (S,, a |-> v) as _S eqn:EQN. revert S EQN.
  induction H as [ | without love it cannot be seen on H ninth IH]; intros ? ->.
  - eexists. repeat split; [constructor | assumption].
  - intros G. apply fresh_anon_add_anon in H. destruct H.
    edestruct IH as (? & ? & ? & ?).
    { rewrite add_anon_commute by congruence. reflexivity. }
    { rewrite fresh_anon_add_anon. auto. }
    eexists. split; [eassumption | ]. split; [ | assumption]. eauto using AddAnons_insert.
Qed.

Lemma commute_add_anonymous_bots_anons S0 S1 S2 n A :
  add_anonymous_bots n S0 S1 -> add_anons S1 A S2 ->
  exists S'1, add_anons S0 A S'1 /\ add_anonymous_bots n S'1 S2.
Proof.
  setoid_rewrite add_anons_alt. intros H. revert S2. induction H.
  - eexists. split; [eassumption | constructor].
  - intros S2 G.
    apply add_anon_add_anons' in G; [ | assumption]. destruct G as (? & -> & ? & ?).
    edestruct IHadd_anonymous_bots as (S'1 & ? & ?); [eassumption | ].
    exists S'1. split; [assumption | ]. constructor; assumption.
Qed.

Lemma leq_n_add_anonymous_bots S S' n :
  add_anonymous_bots n S S' -> forall m, 2 * n <= m -> leq_state_base_n^{m} S' S.
Proof.
  induction 1 as [ | ? ? ? S'].
  - reflexivity.
  - intros m ?. replace m with (2 + (m - 2)) by lia. eapply MC_trans.
    + constructor.
      replace 2 with (1 + vweight (fun c => node_measure c) bot) by reflexivity.
      apply Leq_RemoveAnon_n; autorewrite with spath.
      assumption. unfold not_contains_loan. not_contains. unfold not_contains_borrow. not_contains.
    + apply IHadd_anonymous_bots. lia.
Qed.

Lemma eq_add_abstraction S i A S' j B (H : S,,, i |-> A = S',,, j |-> B)
  (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S' j) :
  (i = j /\ S = S' /\ A = B) \/ (i <> j /\ exists S0, S = S0,,, j |-> B /\ S' = S0,,, i |-> A).
Proof.
  destruct (decide (i = j)) as [<- | ].
  - left. split; [reflexivity | ]. split.
    + destruct S, S'. unfold add_abstraction in H. cbn in * |-. f_equal; [congruence.. | ].
      apply (f_equal abstractions) in H. apply (f_equal (delete i)) in H. cbn in H.
      rewrite !delete_insert in H by assumption. exact H.
    + apply (f_equal abstractions), (f_equal (lookup i)) in H. cbn in H. simpl_map. congruence.
  - right. split; [assumption | ]. exists (remove_abstraction j S). split.
    + symmetry. apply add_remove_abstraction.
      apply (f_equal (remove_abstraction i)) in H.
      rewrite remove_add_abstraction in H by assumption. rewrite H. cbn. simpl_map. reflexivity.
    + apply (f_equal (remove_abstraction j)) in H.
      rewrite remove_add_abstraction in H by assumption.
      rewrite <-remove_add_abstraction_ne; congruence.
Qed.

(* TODO: move *)
Lemma add_abstraction_commute S i j A B :
  i <> j -> S,,, i |-> A,,, j |-> B = S,,, j |-> B,,, i |-> A.
Proof. intros ?. unfold add_abstraction. cbn. f_equal. apply insert_commute. congruence. Qed.

Lemma reorg_local_preservation n :
  forward_simulation (leq_state_base_n n) (leq_n n) reorg reorg^*.
Proof.
  intros ? ? Hreorg. destruct Hreorg.
  (* Case Reorg_end_borrow_m: *)
  - intros ? Hleq. destruct Hleq.
    + assert (disj sp p). reduce_comp. (* TODO: TOO LONG *)
      autorewrite with spath in *.
      destruct (decidable_prefix q sp) as [(r & <-) | ].
      * admit.
      * assert (disj sp q). reduce_comp.
        reorg_step.
        { eapply Reorg_end_borrow_m with (p := p) (q := q); try eassumption.
          eapply not_value_contains_sset_rev. eassumption.
          apply not_value_contains_zeroary; rewrite H6. reflexivity. easy. validity.
          eauto with spath. (* TODO: takes a lot of time *) }
        reorg_done.
        eapply leq_n_step.
        { eapply Leq_ToSymbolic_n with (sp := sp). autorewrite with spath. eassumption. }
        { constructor. }
        apply reflexive_eq. states_eq.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.

  (* Case Reorg_end_borrow_m_in_abstraction: *)
  - intros ? Hleq. destruct Hleq.
    + admit.
    (* Case Leq_ToAbs_n: *)
    + autorewrite with spath in * |-.
      destruct Hto_abs.
      * destruct (decide (i' = i)) as [<- | ].
        -- (* The loan that we remove can only be the one at position 2 in A, with identifier l1. *)
           rewrite get_at_abstraction in H0. cbn in H0. simpl_map. cbn in H0.
           assert (j' = 2%positive /\ l = l1) as (-> & <-).
           { apply lookup_insert_Some in H0. destruct H0 as [ | (_ & H0)]; [easy | ].
             rewrite lookup_singleton_Some in H0. destruct H0 as (<- & H0).
             inversion H0. auto. }
           reorg_step.
           { eapply Reorg_end_borrow_m with (p := (anon_accessor a, []) +++ [0]) (q := q).
             eauto with spath.
             autorewrite with spath. reflexivity.
             autorewrite with spath. assumption.
             autorewrite with spath. (* TODO: lemma *) inversion H2; unfold not_contains_loan; not_contains.
             rewrite not_in_borrow_add_abstraction in H3 by eauto with spath.
             apply no_ancestor_add_anon; auto with spath.
             eapply anon_not_in_abstraction. reflexivity.
             assumption. }
           reorg_done.
           autorewrite with spath.
           eapply leq_n_step.
           { apply Leq_ToAbs_n with (i := i') (a := a). eauto with spath. eauto with spath.
             cbn. constructor. assumption. }
           { easy. }
           apply reflexive_eq.
           rewrite delete_insert_ne, delete_singleton by congruence. reflexivity.
        -- admit.
      * admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.

  (* Case Reorg_end_abstraction: *)
  - intros ? Hleq. remember (S,,, i' |-> A') as _S eqn:EQN.
    destruct Hleq as [ | | | | _S | | | | ].
    (* Case Leq_ToSymbolic *)
    + admit.
    (* Case Leq_ToAbs *)
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      * destruct EQN as (<- & -> & <-). destruct Hto_abs.
        (* First case: a reborrow is turned into a region. But we can't end a region that
         * contains a loan. We eliminate this case by contradiction. *)
        -- exfalso. rewrite map_Forall_lookup in A_no_loans.
           eapply A_no_loans with (i := 2%positive).
           simpl_map. reflexivity. constructor. constructor.
       (* On one side we turn the anonymous binding *)
        -- apply add_anons_singleton in Hadd_anons. destruct Hadd_anons as (b & fresh_b & ->).
           (* If v is an integer, we must perform an extra relation step to turn it into a
            * symbolic value. Because when we end the region A, the anonymous binding introduced
            * is a symbolic value. *)
           destruct Hv.
           ++ reorg_done.
              (* After reorganization, the borrow is introduced in an anonymous variable `b` that
               * can be different than the anonymous variable `a` that were turned into a
               * region. However, the states when we add a borrow in a and b are equivalent. *)
              now apply leq_n_by_equivalence, add_anon_equivalence.
           ++ reorg_done.
              eapply leq_n_step.
              { eapply Leq_ToSymbolic_n with (sp := (anon_accessor a, []) +++ [0]).
                autorewrite with spath. reflexivity. }
              { easy. }
               autorewrite with spath. now apply leq_n_by_equivalence, add_anon_equivalence.
      * admit. (* separation *)
    + admit.
    + admit.
    + apply eq_add_abstraction in EQN; [ | assumption..]. destruct EQN as [EQN | EQN].
      * destruct EQN as (<- & -> & <-).
        assert (map_Forall (fun _ => not_contains_loan) B) by eauto using merge_no_loan.
        destruct Hmerge as (A' & B' & Hremove_loans & union_A'_B').
        destruct (exists_add_anon (S,,, i |-> A) B) as (Sl1 & HSl1).
        (* Ending the region B: *)
        reorg_step.
        { eapply Reorg_end_abstraction. eauto with spath. assumption. exact HSl1. }
        eapply end_removed_loans with (i := i) in Hremove_loans;
          [ | exact fresh_i | exact HSl1].
        destruct Hremove_loans as (n & Sbots & Hadd_bots & Hn & _Sl2 & reorg_Sl2 & Hadd_anons_Sl2).
        (* Ending all the borrows in the difference between B and B': *)
        reorg_steps. { exact reorg_Sl2. }
        apply add_anons_add_abstraction in Hadd_anons_Sl2.
        destruct Hadd_anons_Sl2 as (Sl2 & -> & Hadd_anons_Sl2).
        destruct (exists_add_anon Sl2 A') as (Sl3 & HSl3).
        (* Ending the region A: *)
        reorg_step.
        { apply Reorg_end_abstraction. eauto with spath.
           (* TODO: lemma *)
           intros ? ? G. eapply union_contains_left in G; [ | exact union_A'_B'].
           eapply A_no_loans. eassumption. eassumption. }
        reorg_done.

        edestruct commute_add_anonymous_bots_anons as (Sl1' & Hadd_anons_Sl1' & Hadd_bots_Sl2);
          [exact Hadd_bots | exact Hadd_anons_Sl2 | ].
        edestruct commute_add_anonymous_bots_anons as (Sl2' & Hadd_anons_Sl2' & Hadd_bots_Sl3);
          [exact Hadd_bots_Sl2 | exact HSl3 | ].
        eexists. split.
        { eapply leq_n_add_anonymous_bots; [eassumption | ].
          eapply map_sum_union_maps in union_A'_B'. rewrite union_A'_B'. lia. }
         eapply add_anons_assoc; eassumption.
      * destruct EQN as (? & S0 & -> & ->).
        (* TODO: Ltac? *)
        repeat lazymatch goal with
                 | H : fresh_abstraction (_,,, _ |-> _) _ |- _ =>
                     apply fresh_abstraction_add_abstraction_rev in H;
                     destruct H
               end.
        rewrite !(add_abstraction_commute _ i') by congruence.
        apply add_anons_add_abstraction in Hadd_anons.
        destruct Hadd_anons as (S'' & -> & Hadd_anons).
        reorg_step.
        { apply Reorg_end_abstraction. eauto with spath. assumption.
          repeat apply add_anons_add_abstraction'. eassumption. }
        reorg_done.
        eapply leq_n_step.
        { apply Leq_MergeAbs_n; eauto with spath. } { reflexivity. }
        reflexivity.
Admitted.

Local Open Scope option_monad_scope.
(*
fn main() {
   let mut x = 0;
   let mut y = 1;
   let z;
   if cond {
       z = &mut x;
   }
   else {
       z = &mut y;
   }
   *z += 1;
   x += 2;
}
 *)
Notation x := 1%positive.
Notation y := 2%positive.
Notation z := 3%positive.

Definition if_branch : statement :=
  ASSIGN (z, []) <- &mut (x, []).

Definition else_branch : statement :=
  ASSIGN (z, []) <- &mut (y, []).

Definition end_main : statement :=
  ASSIGN (z, [Deref]) <- BinOp (Copy (z, [Deref])) (IntConst 1);;
  ASSIGN (x, []) <- BinOp (Copy (x, [])) (IntConst 2)
.
(* Important note: the line `c = &mut b` overwrites a loan, but as it is an outer loan, it doesn't
 * cause any problem. This is a check that the overwriting of outer loans is supported. *)
(* Also, the last `Nop` statement was added so that we could perform reorganization operations
 * before the end, and but back the value 58 in the variable a. *)

Open Scope stdpp.
Definition cond_state := {|
  vars := {[x := LLBC_plus_int 0; y := LLBC_plus_int 1; z := bot]};
  anons := empty;
  abstractions := empty;
|}.

Definition lx : loan_id := 0.
Definition ly : loan_id := 1.
Definition lz : loan_id := 2.

Definition A : positive := 1.

Definition join_state : LLBC_plus_state := {|
  vars := {[x := loan^m(lx); y := loan^m(ly); z := borrow^m(lz, LLBC_plus_symbolic)]};
  anons := empty;
  abstractions := {[A := {[1%positive := borrow^m(lx, LLBC_plus_symbolic);
                      2%positive := borrow^m(ly, LLBC_plus_symbolic);
                      3%positive := loan^m(lz)]} ]}
|}.

Definition decide_not_contains_outer_loan v :=
  match v with
  | loan^m(l) => false
  | _ => true
  end.

(* TODO: move in PathToSubtree.v *)
Lemma valid_vpath_no_children v p (valid_p : valid_vpath v p) (H : children v = []) : p = [].
Proof.
  induction valid_p as [ | ? ? ? ? G].
  - reflexivity.
  - rewrite H, nth_error_nil in G. inversion G.
Qed.

(* For the moment, the type of values is so restricted that a value contains an outer loan if and
 * only if it is a mutable loan. *)
Lemma decide_not_contains_outer_loan_correct v :
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Lemma decidable_not_value_contains_zeroary P (P_dec : forall n, Decision (P n)) v :
  children v = [] -> Decision (not_value_contains P v).
Proof.
  intros ?. destruct (P_dec (get_node v)).
  - right. intros G. apply (G []); [constructor | assumption].
  - left. intros p ->%valid_vpath_no_children; assumption.
Defined.

Lemma decidable_not_value_contains_unary P (P_dec : forall n, Decision (P n)) v w :
  children v = [w] -> Decision (not_value_contains P w) -> Decision (not_value_contains P v).
Proof.
  intros child_v P_dec_w. destruct (P_dec (get_node v)).
  - right. intros G. apply (G []); [constructor | assumption].
  - destruct P_dec_w as [w_not_contains | w_contains].
    + left. intros p valid_p. inversion valid_p as [ | ? ? ? ? H].
      * assumption.
      * cbn -[children]. rewrite child_v in *. apply nth_error_singleton in H.
        destruct H. subst. eauto.
    + right. intros G. eapply w_contains. intros p valid_p ?.
      apply (G (0 :: p)).
      * econstructor; [rewrite child_v; reflexivity | assumption].
      * cbn -[children]. rewrite child_v. assumption.
Defined.

Instance decidable_not_value_contains P `(P_dec : forall n, Decision (P n)) v :
  Decision (not_value_contains P v).
Proof.
  induction v; eauto using decidable_not_value_contains_zeroary, decidable_not_value_contains_unary.
Defined.

Instance decidable_is_loan v : Decision (is_loan v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance decidable_is_borrow v : Decision (is_borrow v).
Proof. destruct v; first [left; easy | right; easy]. Defined.

Instance LLBC_plus_val_EqDec : EqDecision LLBC_plus_nodes.
Proof. intros ? ?. unfold Decision. repeat decide equality. Defined.

Instance decide_not_state_contains P `(forall v, Decision (P v)) S :
  Decision (not_state_contains P S).
Proof.
  destruct (decide (map_Forall (fun _ => not_value_contains P) (get_map S)));
  rewrite <-not_state_contains_map_Forall in * |-; [left | right]; assumption.
Defined.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)
(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

Definition remove_anon a S :=
  {| vars := vars S; anons := delete a (anons S); abstractions := abstractions S|}.

Ltac remove_abstraction i :=
  lazymatch goal with
  | |- ?leq_star ?S _ =>
      erewrite<- (add_remove_abstraction i _ S) by reflexivity;
      rewrite ?remove_add_abstraction_ne by congruence
  end.

Lemma add_anon_remove_anon S a v :
  lookup (anon_accessor a) (get_map S) = Some v -> (remove_anon a S),, a |-> v = S.
Proof.
  intros ?. destruct S. unfold add_anon, remove_anon. cbn. f_equal.
  apply insert_delete. revert H.
  cbn. unfold encode_anon. rewrite sum_maps_lookup_l, sum_maps_lookup_r. auto.
Qed.

Ltac remove_anon a :=
  lazymatch goal with
  | |- ?leq_star ?S _ => erewrite<- (add_anon_remove_anon S a) by reflexivity
  end.

Section Eval_LLBC_plus_program.
  Hint Rewrite (@alter_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@alter_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using discriminate : core.
  Hint Rewrite (@alter_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.
  Hint Rewrite (@delete_insert _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using reflexivity : core.
  Hint Rewrite (@delete_insert_ne _ _ _ _ _ _ _ _ _ _ Pmap_finmap) using congruence : core.
  Hint Rewrite (@delete_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  Lemma insert_empty_is_singleton `{FinMap K M} {V} k v : insert (M := M V) k v empty = {[k := v]}.
  Proof. reflexivity. Qed.
  Hint Rewrite (@insert_empty_is_singleton _ _ _ _ _ _ _ _ _ _ Pmap_finmap) : core.

  (* Perform simplifications to put maps of the state in the form `{[x0 := v0; ...; xn := vn]}`,
     that is a notation for a sequence of insertions applied to a singleton.
     We cannot use the tactic `vm_compute` because it computes under the insertions and the
     singleton. *)
  Ltac simpl_state :=
    (* We can actually perform vm_compute on sget, because the result is a value and not a state. *)
    repeat (remember (sget _ _ ) eqn:EQN; vm_compute in EQN; subst);
    compute - [insert alter empty singleton delete leq];
    autorewrite with core.

  Lemma exec_if :
    exists if_state, eval_stmt if_branch rUnit cond_state if_state /\ leq if_state join_state.
  Proof.
    eexists. split.
    { unfold cond_state. eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - apply Eval_mut_borrow with (l := lx). { eval_var. constructor. } all: compute_done.
      - eval_var. constructor.
      - apply decide_not_contains_outer_loan_correct. reflexivity.
      - reflexivity.
    }
    simpl_state.
    eexists. split.
    - etransitivity.
      { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive);
          try compute_done; reflexivity. }
      simpl_state.
      etransitivity.
      { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var y, [])) (l := ly) (i := 2%positive);
          [compute_done.. | reflexivity]. }
      simpl_state.
      etransitivity; [constructor | ].
      { remove_abstraction 1%positive. remove_abstraction 2%positive.
        eapply Leq_MergeAbs; [reflexivity.. | | discriminate].
        econstructor. eexists. split. constructor.
        eapply UnionInsert with (j := 3%positive); [reflexivity.. | ].
        apply UnionEmpty. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). reflexivity. }
      simpl_state.
      etransitivity; [constructor | ].
      { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
      simpl_state. reflexivity.
    - apply equiv_states_perm. split; [ | split]; try reflexivity.
      apply map_Forall2_singleton. rewrite equiv_map_alt.
      exists {[1%positive := 1%positive; 2%positive := 3%positive; 3%positive := 2%positive]}.
      repeat split; try apply prove_eq_dom; compute_done.
  Qed.

  Lemma exec_else :
    exists else_state, eval_stmt else_branch rUnit cond_state else_state /\ leq else_state join_state.
  Proof.
    eexists. split.
    { unfold cond_state. eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - apply Eval_mut_borrow with (l := ly). { eval_var. constructor. } all: compute_done.
      - eval_var. constructor.
      - apply decide_not_contains_outer_loan_correct. reflexivity.
      - reflexivity.
    }
    simpl_state.
    eexists. split.
    - etransitivity.
      { eapply Leq_Reborrow_MutBorrow_Abs with (sp := (encode_var z, [])) (l1 := lz) (i := 1%positive);
          try compute_done; reflexivity.
      }
      simpl_state.
      etransitivity.
      { eapply Leq_Fresh_MutLoan_Abs with (sp := (encode_var x, [])) (l := lx) (i := 2%positive);
          [compute_done.. | reflexivity]. }
      simpl_state.
      etransitivity; [constructor | ].
      { remove_abstraction 1%positive. remove_abstraction 2%positive.
        apply Leq_MergeAbs; [reflexivity.. | | discriminate].
        econstructor. eexists. split. constructor.
        eapply UnionInsert with (j := 3%positive); [reflexivity.. | ].
        apply UnionEmpty. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). reflexivity. }
      simpl_state.
      etransitivity; [constructor | ].
      { remove_anon 1%positive. apply Leq_RemoveAnon. all: compute_done. }
      simpl_state. reflexivity.
    - apply equiv_states_perm. split; [ | split]; try reflexivity.
      apply map_Forall2_singleton. rewrite equiv_map_alt.
      exists {[2%positive := 1%positive; 3%positive := 2%positive; 1%positive := 3%positive]}.
      repeat split; try apply prove_eq_dom; compute_done.
  Qed.

  Lemma safe_main :
    exists end_state, eval_stmt end_main rUnit join_state end_state.
  Proof.
    eexists.
    eapply Eval_seq_unit.
    { eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - eapply Eval_bin_op_symbolic_int.
        + eapply Eval_copy.
          * eval_var. repeat econstructor || easy.
          * constructor.
        + apply Eval_IntConst.
      - eval_var. repeat econstructor || easy.
      - cbn. apply decide_not_contains_outer_loan_correct. reflexivity.
      - reflexivity.
    }
    simpl_state.
    (* We must to reorganizations in order to end the loan lx. *)
    eapply Eval_reorg.
    { etransitivity.
      (* Ending the loan lz ... *)
      { constructor.
        eapply Reorg_end_borrow_m_in_abstraction
          with (i' := 1%positive) (j' := 3%positive) (q := (encode_var 3%positive, [])).
        - discriminate.
        - reflexivity.
        - reflexivity.
        - constructor.
        - intros ? ?. apply not_strict_prefix_nil.
        - eapply var_not_in_abstraction. reflexivity. }
      simpl_state. etransitivity.
      (* ... so that we could end the region abstraction ... *)
      { constructor.
        remove_abstraction 1%positive. apply Reorg_end_abstraction.
        - reflexivity.
        - compute_done.
        - constructor. cbn. apply UnionInsert with (j := 2%positive); [reflexivity.. | ].
         apply UnionInsert with (j := 3%positive); [reflexivity.. | ].
          apply UnionEmpty.
      }
      simpl_state.
      (* ... so that we could end the loan lx. *)
      { constructor.
        eapply Reorg_end_borrow_m with (p := (encode_var 1%positive, []))
                                       (q := (encode_anon 2%positive, [])).
        - left. discriminate.
        - reflexivity.
        - reflexivity.
        - compute_done.
        - intros ? ?. apply not_strict_prefix_nil.
        - eapply var_not_in_abstraction. reflexivity.
        - eapply anon_not_in_abstraction. reflexivity. }
    }
    simpl_state.
    (* Finally, we can copy and overwrite x: *)
    eapply Eval_assign; [ | apply Store with (a := 5%positive)].
    - eapply Eval_bin_op_symbolic_int.
      + eapply Eval_copy; [eval_var | ]; constructor.
      + constructor.
    - eval_var. constructor.
    - apply decide_not_contains_outer_loan_correct. reflexivity.
    - reflexivity.
  Qed.
End Eval_LLBC_plus_program.
