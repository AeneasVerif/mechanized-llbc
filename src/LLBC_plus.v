Require Import base.
Require Import lang.
Require Import SimulationUtils.
Require Import List.
Import ListNotations.
Require Import PeanoNat Lia.
(* Notation conflict between stdpp's `+++` and our `+++`. That's why we're importing stpp first,
   then closing the scope. *)
From stdpp Require Import pmap gmap.
Close Scope stdpp_scope.
Require Import PathToSubtree.

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
  regions : Pmap (Pmap LLBC_plus_val);
}.

Definition encode_var (x : var) :=
  encode (A := _ + positive * positive) (inl (encode (A := _ + anon) (inl x))).
Definition encode_anon (a : anon) :=
  encode (A := _ + positive * positive) (inl (encode (A := var + _) (inr a))).
Definition encode_region (x : positive * positive) := encode (A := var + anon + _) (inr x).

(* TODO: move in base.v *)
Lemma alter_map_union {V} `{FinMap K M} (m0 m1 : M V) f k :
  alter f k (union m0 m1) = union (alter f k m0) (alter f k m1).
Proof.
  apply map_eq. intros i. destruct (decide (i = k)) as [-> | ].
  - simpl_map. rewrite !lookup_union. simpl_map.
Admitted.

Program Instance IsState : State LLBC_plus_state LLBC_plus_val := {
  get_map S := sum_maps (sum_maps (vars S) (anons S)) (flatten (regions S));

  (* The flatten function in not injective. For example, R and R<[A := empty]> have the same
   * flattening. An empty region and a non-existant region can't be distinguished.
   * Therefore, for the axiom `state_eq_ext` to be true, we need the set of regions identifiers as
   * extra information. *)
  extra := Pset;
  get_extra S := dom (regions S);

  alter_at_accessor f a S :=
    match decode' (A := positive + positive * positive) a with
    | Some (inl a) =>
        match decode' (A := var + anon) a with
        | Some (inl x) => {| vars := alter f x (vars S); anons := anons S; regions := regions S|}
        | Some (inr a) => {| vars := vars S; anons := alter f a (anons S); regions := regions S|}
        | None => S
        end
    | Some (inr (i, j)) => {| vars := vars S; anons := anons S;
                              regions := alter (fun r => alter f j r) i (regions S)|}
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
  add_anon a v S := {| vars := vars S; anons := insert a v (anons S); regions := regions S|};
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
  intros. cbn. symmetry. unfold encode_anon. rewrite sum_maps_insert_inl, sum_maps_insert_inr.
  reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros. unfold encode_anon. rewrite !decode_encode. reflexivity. Qed.

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
  valid_spath S pi_0 /\ eval_path S perm (snd p) (encode_var (fst p), []) pi.

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
| Copy_val_symbolic (n : nat) : copy_val LLBC_plus_symbolic LLBC_plus_symbolic
.

Local Reserved Notation "S  |-{op}  op  =>  r" (at level 60).

Variant eval_operand : operand -> LLBC_plus_state -> (LLBC_plus_val * LLBC_plus_state) -> Prop :=
| Eval_IntConst S n : S |-{op} IntConst n => (LLBC_plus_int n, S)
| Eval_copy S (p : place) pi v
    (Heval_place : eval_place S Imm p pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| Eval_move S (p : place) pi : eval_place S Mov p pi ->
    not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) ->
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
  | Eval_mut_borrow S p pi l : S |-{p} p =>^{Mut} pi ->
      not_contains_loan (S.[pi]) -> not_contains_bot (S.[pi]) -> is_fresh l S ->
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(l)])
where "S |-{rv} rv => r" := (eval_rvalue rv S r).

Definition not_in_borrow (S : LLBC_plus_state) p :=
  forall q, prefix q p -> is_mut_borrow (get_node (S.[q])) -> q = p.

Variant in_region : spath -> Prop :=
  | InRegion i r q :
      decode' (A := positive + positive * positive) i = Some (inr r) -> in_region (i, q).

(* The property merge_maps A B C is true if the map C contains all of the pairs (key, element) of
 * A, and all the elements of B with possibly different keys.

 * Example: let's take A = {[1 := x; 2 := y|} and B = {[1 := z]}. Then merge A B C is true for any
 * map C = {[ 1 := x; 2 := y; i := z]} for any i different from 1 or 2. *)
Inductive merge_maps {V : Type} : Pmap V -> Pmap V -> Pmap V -> Prop :=
  | MergeEmpty A : merge_maps A empty A
  | MergeInsert A B C i j x :
      ~elem_of i (dom A) -> ~elem_of j (dom B) ->
      merge_maps (insert j x A) B C -> merge_maps A (insert i x B) C.

Inductive reorg : LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Reorg_end_borrow_m S (p q : spath) l :
    disj p q -> get_node (S.[p]) = loanC^m(l) -> get_node (S.[q]) = borrowC^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q -> ~in_region q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
    (* q refers to a path in region A, at index j. *)
| Reorg_end_abstraction S i A anons' :
    lookup i (regions S) = Some A ->
    merge_maps (anons S) A anons' ->
    (* no loan in A *)
    reorg S {|vars := vars S; anons := anons'; regions := delete i (regions S)|}.

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

(* A version of to-abs that is limited compared to the paper. Currently, we can only turn into an
 * abstraction a value of the form:
 * - borrow^m l σ (with σ a symbolic value)
 * - borrow^m l0 (loan^m l1)
 * Consequently, a single region is created.
 *)
Variant to_abs : LLBC_plus_val -> Pmap LLBC_plus_val -> Prop :=
| ToAbs_MutBorrow l :
    to_abs (borrow^m(l, LLBC_plus_symbolic)) ({[1%positive := (borrow^m(l, LLBC_plus_symbolic))]})%stdpp
| ToAbs_MutReborrow l0 l1:
    to_abs (borrow^m(l0, loan^m(l1)))
           ({[1%positive := (borrow^m(l0, LLBC_plus_symbolic)); 2%positive := loan^m(l1)]})%stdpp
.

Inductive merge_abstractions :
  Pmap LLBC_plus_val -> Pmap LLBC_plus_val -> Pmap LLBC_plus_val -> Prop :=
  | MergeAbsEmpty A : merge_abstractions A empty A
  | MergeAbsInsert A B C i j x :
      lookup i A = None -> lookup j B = None ->
      merge_abstractions (insert i x A) B C -> merge_abstractions A (insert j x B) C
  | MergeAbs_Mut A B C i j l (H : merge_abstractions A B C) :
      lookup i A = None -> lookup j B = None ->
      merge_abstractions (insert i (loan^m(l)) A) (insert j (borrow^m(l, LLBC_plus_symbolic)) B) C
.

Notation "S ,,, i |-> A" :=
    {|vars := vars S; anons := anons S; regions := insert i A (regions S)|}
  (at level 50, left associativity).

Notation fresh_abstraction S i := (lookup i (regions S) = None).

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
Hint Rewrite sweight_add_abstraction using cbn; simpl_map; auto : weight.

Definition remove_anon a S :=
  {| vars := vars S; anons := delete a (anons S); regions := regions S|}.

Lemma add_anon_remove_anon S a v :
  lookup (anon_accessor a) (get_map S) = Some v -> (remove_anon a S),, a |-> v = S.
Proof.
  intros ?. destruct S. unfold add_anon, remove_anon. cbn. f_equal.
  apply insert_delete. revert H.
  cbn. unfold encode_anon. rewrite sum_maps_lookup_l, sum_maps_lookup_r. auto.
Qed.

Lemma remove_anon_fresh S a : fresh_anon (remove_anon a S) a.
Proof.
  unfold fresh_anon, remove_anon, get_map. cbn. unfold encode_anon.
  rewrite sum_maps_lookup_l, sum_maps_lookup_r. apply lookup_delete.
Qed.
Hint Rewrite @sweight_add_anon using auto using fresh_anon_sset, remove_anon_fresh : weight.

(* TODO: create a definition instead of a notation? *)
Notation remove_region i S :=
  {|vars := vars S; anons := anons S; regions := delete i (regions S)|}.

Lemma add_remove_region i A S (H : lookup i (regions S) = Some A) :
  remove_region i S,,, i |-> A = S.
Proof. destruct S. cbn. f_equal. apply insert_delete in H. exact H. Qed.

Lemma remove_add_region_ne i j A S :
  i <> j -> remove_region i (S,,, j |-> A) = remove_region i S,,, j |-> A.
Proof. intros ?. destruct S. cbn. f_equal. apply delete_insert_ne. assumption. Qed.

Variant leq_state_base : LLBC_plus_state -> LLBC_plus_state -> Prop :=
| Leq_ToSymbolic S sp
    (no_loan : not_contains_loan (S.[sp]))
    (no_borrow : not_contains_borrow (S.[sp]))
    (no_bot : not_contains_bot (S.[sp])) :
    leq_state_base S (S.[sp <- LLBC_plus_symbolic])
| Leq_ToAbs S a v i A
    (get_a : get_at_accessor S (anon_accessor a) = Some v)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base S ((remove_anon a S),,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region is created. *)
| Leq_RemoveAnon S a v
    (get_a : get_at_accessor S (anon_accessor a) = Some v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base S (remove_anon a S)
| Leq_MoveValue S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (not_in_region : ~in_region sp) :
    leq_state_base S (S.[sp <- bot],, a |-> S.[sp])
(* Note: for the merge, we reuse the region i. Maybe we should use another region k? *)
| Leq_MergeAbs S i j A B C
    (get_A : lookup i (regions S) = Some A) (get_B : lookup j (regions S) = Some B)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base S (remove_region i (remove_region j S),,, i |-> C)
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
    leq_state_base S (S.[sp <- borrow^m(l1, S.[sp +++ [0] ])],, a |-> borrow^m(l0, loan^m(l1)))
(* Note: this rule makes the size of the state increase from right to left.
   We should add a decreasing quantity. *)
| Leq_Abs_Clear_Value S i A j v :
    lookup i (regions S) = Some A -> lookup j A = Some v ->
    not_contains_loan v -> not_contains_borrow v ->
    leq_state_base S
    {|vars := vars S; anons := anons S; regions := insert i (delete j A) (regions S)|}
| Leq_AnonValue S v a
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v)
    (no_symbolic : not_contains_symbolic v)
    (is_fresh : fresh_anon S a) :
    leq_state_base S (S,, a |-> v)
.

Record LLBC_plus_well_formed (S : LLBC_plus_state) : Prop := {
  at_most_one_borrow_mut l : at_most_one_node (borrowC^m(l)) S;
  at_most_one_loan_mut l : at_most_one_node (loanC^m(l)) S;
}.

Record LLBC_plus_well_formed_alt (S : LLBC_plus_state) l : Prop := {
  at_most_one_borrow_mut_alt : sweight (indicator borrowC^m(l)) S <= 1;
  no_mut_loan_loc_alt : sweight (indicator loanC^m(l)) S <= 1;
}.

Lemma well_formedness_equiv S : LLBC_plus_well_formed S <-> forall l, LLBC_plus_well_formed_alt S l.
Proof.
  split.
  - intros WF l. destruct WF. split.
    + rewrite<- decide_at_most_one_node; easy.
    + rewrite<- decide_at_most_one_node; easy.
  - intros WF. split; intros l; destruct (WF l).
    + apply decide_at_most_one_node; [discriminate | ]. assumption.
    + apply decide_at_most_one_node; [discriminate | ]. assumption.
Qed.

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
Lemma region_sum_empty (weight : LLBC_plus_val -> nat) : map_sum weight (M := Pmap) empty = 0.
Proof. apply map_sum_empty. Qed.
Hint Rewrite region_sum_empty : weight.

Lemma region_sum_insert weight i v (A : Pmap LLBC_plus_val) :
  lookup i A = None -> map_sum weight (insert i v A) = weight v + map_sum weight A.
Proof. apply map_sum_insert. Qed.
Hint Rewrite region_sum_insert using auto : weight.

Lemma region_sum_singleton weight i v :
  map_sum weight (singletonM (M := Pmap LLBC_plus_val) i v) = weight v.
Proof.
  unfold singletonM, map_singleton.
  rewrite region_sum_insert, region_sum_empty by apply lookup_empty. lia.
Qed.
Hint Rewrite region_sum_singleton : weight.

Global Instance HLPL_plus_state_leq_base : LeqBase LLBC_plus_state :=
{ leq_base := leq_state_base }.

Global Instance LLBC_plus_WellFormed : WellFormed LLBC_plus_state :=
{ well_formed := LLBC_plus_well_formed }.

Lemma leq_base_preserves_wf_l Sl Sr : well_formed Sl -> leq_base Sl Sr -> well_formed Sr.
Proof.
  rewrite !well_formedness_equiv.
  intros H G l'. specialize (H l'). destruct G.
  - destruct H. split; weight_inequality.
  - apply add_anon_remove_anon in get_a. rewrite<- get_a in H. destruct H, Hto_abs.
    + destruct (decide (l = l')) as [<- | ]; split; weight_inequality.
    + destruct (decide (l0 = l')) as [-> | ]; [ | split; weight_inequality].
      destruct (decide (l1 = l')) as [-> | ]; split; weight_inequality.
  - apply add_anon_remove_anon in get_a. rewrite<- get_a in H.
    apply not_value_contains_weight with (weight := indicator (loanC^m(l'))) in no_loan;
      [ | intros ? <-%indicator_non_zero; constructor].
    apply not_value_contains_weight with (weight := indicator (borrowC^m(l'))) in no_borrow;
      [ | intros ? <-%indicator_non_zero; constructor].
    destruct H; split; weight_inequality.
  - destruct H. split; weight_inequality.
  - apply add_remove_region in get_A, get_B.
    rewrite<- get_B, remove_add_region_ne in get_A by assumption.
    rewrite <-get_B, <-get_A in H. clear get_A get_B. destruct H.
    induction Hmerge.
    + split; weight_inequality.
    + apply IHHmerge; weight_inequality.
    + apply IHHmerge; weight_inequality.
  - assert (sweight (indicator (borrowC^m(l))) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | eassumption].
      intros ? <-%indicator_non_zero. constructor. }
    assert (sweight (indicator (loanC^m(l))) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | eassumption].
      intros ? <-%indicator_non_zero. constructor. }
    destruct H, (decide (l = l')) as [<- | ]; split; weight_inequality.
    (* Note: the fact l0 <> l1 may be useful at other places. *)
  - assert (l0 <> l1).
    { intros <-. eapply fresh_l1; [ | rewrite get_borrow]; [validity | constructor]. }
    assert (sweight (indicator (borrowC^m(l1))) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | eassumption].
      intros ? <-%indicator_non_zero. constructor. }
    assert (sweight (indicator (loanC^m(l1))) S = 0).
    { eapply not_state_contains_implies_weight_zero; [ | eassumption].
      intros ? <-%indicator_non_zero. constructor. }
    destruct H. destruct (decide (l1 = l')) as [<- | ]; [split; weight_inequality | ].
    destruct (decide (l0 = l')) as [<- | ]; split; weight_inequality.
  (* TODO: Compute the weight when removing a value. *)
  - admit.
  - apply not_value_contains_weight with (weight := indicator (loanC^m(l'))) in no_loan;
      [ | intros ? <-%indicator_non_zero; constructor].
    apply not_value_contains_weight with (weight := indicator (borrowC^m(l'))) in no_borrow;
      [ | intros ? <-%indicator_non_zero; constructor].
    destruct H; split; weight_inequality.
Admitted.

Require Import Bool.
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
  ASSIGN (y, []) <- &mut (x, []).

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
  regions := empty;
|}.

Definition lx : loan_id := 0.
Definition ly : loan_id := 1.
Definition lz : loan_id := 2.

Definition A : positive := 1.

Definition join_state : LLBC_plus_state := {|
  vars := {[x := loan^m(lx); y := loan^m(ly); z := borrow^m(lz, LLBC_plus_symbolic)]};
  anons := empty;
  regions := {[A := {[1%positive := borrow^m(lx, LLBC_plus_symbolic);
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
Lemma decide_contains_outer_loan_correct v :
  is_true (decide_not_contains_outer_loan v) -> not_contains_outer_loan v.
Proof.
  intros no_outer_loan [ | ] H.
  - destruct v; inversion H. discriminate.
  - destruct v; rewrite vget_cons, ?nth_error_nil, ?vget_bot in H; inversion H.
    exists []. split.
    * eexists _, _. reflexivity.
    * constructor.
Qed.

Definition decide_is_bot v := match v with botC => true | _ => false end.
Definition decide_is_loan v := match v with loanC^m(l) => true | _ => false end.
Definition decide_is_borrow v := match v with borrowC^m(l) => true | _ => false end.
Definition decide_is_loan_id l v :=
  match v with
  | borrowC^m(l') | loanC^m(l') => l =? l'
  | _ => false
  end.

Fixpoint decide_not_value_contains (P : LLBC_plus_nodes -> bool) v :=
  negb (P (get_node v)) && match v with borrow^m(l, w) => decide_not_value_contains P w | _ => true end.

(* split in two lemmas. *)
Lemma decide_not_value_contains_correct H P v (H_implies_P : forall v, H v -> P v = true) :
  decide_not_value_contains P v = true -> not_value_contains H v.
Proof.
  intro decide_is_true. induction v.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
  - intros p valid_p. inversion valid_p; subst.
    + cbn in *. intros G%H_implies_P. rewrite G in decide_is_true. discriminate.
    + cbn in *. rewrite nth_error_cons in * |-. destruct i.
      * cbn in *. apply IHv. eapply andb_prop. eassumption. inversion H0. assumption.
      * rewrite nth_error_nil in * |-. discriminate.
  - intros p valid_p. apply valid_vpath_no_children in valid_p; [ | reflexivity].
    subst. cbn in *. intros G%H_implies_P. rewrite G in *. discriminate.
Qed.

Corollary decide_contains_bot v (H : decide_not_value_contains decide_is_bot v = true) :
  not_contains_bot v.
Proof. eapply decide_not_value_contains_correct; try exact H. intros ? ->. reflexivity. Qed.

Corollary decide_contains_loan v (H : decide_not_value_contains decide_is_loan v = true) :
  not_contains_loan v.
Proof.
  eapply decide_not_value_contains_correct; try exact H.
  intros ? G. destruct G. reflexivity.
Qed.

Corollary decide_contains_borrow v (H : decide_not_value_contains decide_is_borrow v = true) :
  not_contains_borrow v.
Proof.
  eapply decide_not_value_contains_correct; try exact H.
  intros ? G. destruct G. reflexivity.
Qed.

Definition decide_not_state_contains (P : LLBC_plus_nodes -> bool) (S : LLBC_plus_state) :=
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

Corollary decide_not_is_fresh S l (H : decide_not_state_contains (decide_is_loan_id l) S = true) :
  is_fresh l S.
Proof.
  eapply decide_state_contains_correct; try eassumption.
  intros c G. destruct c; inversion G; apply Nat.eqb_refl.
Qed.

(* TODO: move in PathToSubtree.v? *)
Lemma prefix_nil p i : prefix p (i, []) -> p = (i, []).
Proof.
  destruct p as (j & q). intros (r & H). unfold app_spath_vpath in H. cbn in H.
  apply pair_equal_spec in H. destruct H as (-> & H).
  apply app_eq_nil in H. destruct H as (-> & _). reflexivity.
Qed.

(* Note: an alternative to using tactics is to define functions, and prove their correction. *)

(* When meeting the goal S |-{p} P[x] =>^{k} pi, this tactics:
   - Compute the spath pi0 corresponding to the variable x
   - Leaves the evaluation of pi0 under the path P[] as a goal. *)
Ltac eval_var :=
  split; [eexists; split; [reflexivity | constructor] | ].

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
    compute - [insert alter empty singleton delete];
    autorewrite with core.

  Lemma exec_if :
    exists if_state, eval_stmt if_branch rUnit cond_state if_state /\ leq if_state join_state.
  Proof.
    eexists. split.
    { unfold cond_state. eapply Eval_assign; [ | apply Store with (a := 1%positive)].
      - apply Eval_mut_borrow with (l := lx).
        + eval_var. constructor.
        + apply decide_contains_loan. reflexivity.
        + apply decide_contains_bot. reflexivity.
        + apply decide_not_is_fresh. reflexivity.
      - eval_var. constructor.
      - apply decide_contains_outer_loan_correct. reflexivity.
      - reflexivity.
    }
    simpl_state.
    etransitivity; [constructor | ].
    { eapply Leq_Reborrow_MutBorrow with (sp := (encode_var z, [])) (l1 := lz) (a := 2%positive).
      - apply decide_not_is_fresh. reflexivity.
      - reflexivity.
      - reflexivity.
    }
    simpl_state.
    etransitivity; [constructor | ].
    { apply Leq_Fresh_MutLoan with (sp := (encode_var y, [])) (l := ly) (a := 3%positive).
      - apply decide_not_is_fresh. reflexivity.
      - reflexivity.
      - apply decide_contains_bot. reflexivity.
    }
    simpl_state.
    etransitivity; [constructor | ].
    { eapply Leq_ToAbs with (a := 2%positive) (i := 1%positive); [reflexivity.. | constructor]. }
    simpl_state.
    etransitivity; [constructor | ].
    { apply Leq_ToSymbolic with (sp := (encode_anon 3%positive, [0])).
      - apply decide_contains_loan. reflexivity.
      - apply decide_contains_borrow. reflexivity.
      - apply decide_contains_bot. reflexivity.
    }
    simpl_state.
    etransitivity; [constructor | ].
    { eapply Leq_ToAbs with (a := 3%positive) (i := 2%positive); [reflexivity.. | constructor]. }
    simpl_state.
    etransitivity; [constructor | ].
    { eapply Leq_MergeAbs with (i := 1%positive) (j := 2%positive); [reflexivity.. | | discriminate].
      eapply MergeAbsInsert with (i := 3%positive); [reflexivity.. | ].
      apply MergeAbsEmpty. }
    simpl_state.
    etransitivity; [constructor | ].
    { apply Leq_ToSymbolic with (sp := (encode_var z, [0])).
      - apply decide_contains_loan. reflexivity.
      - apply decide_contains_borrow. reflexivity.
      - apply decide_contains_bot. reflexivity. }
    simpl_state.
    etransitivity; [constructor | ].
    { eapply Leq_RemoveAnon with (a := 1%positive).
      - reflexivity.
      - apply decide_contains_loan. reflexivity.
      - apply decide_contains_borrow. reflexivity. }
    simpl_state.
