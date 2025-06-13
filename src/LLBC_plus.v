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

Variant in_abstraction : spath -> Prop :=
  | InRegion i r q :
      decode' (A := positive + positive * positive) i = Some (inr r) -> in_abstraction (i, q).

(* The property merge_maps A B C is true if the map C contains all of the pairs (key, element) of
 * A, and all the elements of B with possibly different keys.

 * Example: let's take A = {[1 := x; 2 := y|} and B = {[1 := z]}. Then merge A B C is true for any
 * map C = {[ 1 := x; 2 := y; i := z]} for any i different from 1 or 2. *)
Inductive merge_maps {V : Type} : Pmap V -> Pmap V -> Pmap V -> Prop :=
  | MergeEmpty A : merge_maps A empty A
  | MergeInsert A B C i j x :
      lookup j A = None -> merge_maps (insert j x A) B C -> merge_maps A (insert i x B) C.

Notation abstraction_contains_value S i j v :=
  (get_at_accessor S (encode_abstraction (i, j)) = Some v).

(* Remove the value at j in the region abstraction at i, if this value exists. *)
Definition remove_abstraction_value S i j :=
  {|vars := vars S; anons := anons S; abstractions := alter (delete j) i (abstractions S)|}.

Variant is_integer : LLBC_plus_val -> Prop :=
  | Symbolic_is_integer : is_integer LLBC_plus_symbolic
  | Integer_is_integer n : is_integer (LLBC_plus_int n).

Inductive reorg : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Ends a borrow when it's not in an abstraction: *)
| Reorg_end_borrow_m S (p q : spath) l :
    disj p q -> get_node (S.[p]) = loanC^m(l) -> get_node (S.[q]) = borrowC^m(l) ->
    not_contains_loan (S.[q +++ [0] ]) -> not_in_borrow S q ->
    ~in_abstraction p -> ~in_abstraction q ->
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
(* Ends a borrow when it's in an abstraction: *)
(* The value that is transferred back, S.[q +++ [0]], has to be of integer type. *)
| Reorg_end_borrow_m_in_abstraction S q i j l :
    fst q <> encode_abstraction (i, j) -> abstraction_contains_value S i j loan^m(l) ->
    get_node (S.[q]) = borrowC^m(l) -> is_integer (S.[q +++ [0] ]) ->
    not_in_borrow S q -> ~in_abstraction q ->
    reorg S ((remove_abstraction_value S i j).[q <- bot])
(* q refers to a path in abstraction A, at index j. *)
| Reorg_end_abstraction S i A anons' :
    lookup i (abstractions S) = Some A ->
    merge_maps (anons S) A anons' ->
    (* No value in A contains a loan: *)
    map_Forall (fun _ => not_contains_loan) A ->
    reorg S {|vars := vars S; anons := anons'; abstractions := delete i (abstractions S)|}.

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

Definition add_abstraction S i A :=
  {|vars := vars S; anons := anons S; abstractions := insert i A (abstractions S)|}.

Notation "S ,,, i |-> A" := (add_abstraction S i A) (at level 50, left associativity).

Notation fresh_abstraction S i := (lookup i (abstractions S) = None).

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
  {| vars := vars S; anons := delete a (anons S); abstractions := abstractions S|}.

Lemma add_anon_remove_anon S a v :
  lookup (anon_accessor a) (get_map S) = Some v -> (remove_anon a S),, a |-> v = S.
Proof.
  intros ?. destruct S. unfold add_anon, remove_anon. cbn. f_equal.
  apply insert_delete. revert H.
  cbn. unfold encode_anon. rewrite sum_maps_lookup_l, sum_maps_lookup_r. auto.
Qed.

(* Note: this is a general lemma on states, that could be moved into PathToSubtree.v *)
Lemma add_anons_states_eq S S' a v w
  (fresh_a_S : fresh_anon S a) (fresh_a_S' : fresh_anon S' a)
  (H : S,, a |-> v = S',, a |-> w) : S = S'.
Proof.
  apply state_eq_ext.
  - apply (f_equal get_map) in H. rewrite !get_map_add_anon in H.
    apply (f_equal (delete (anon_accessor a))) in H.
    rewrite !delete_insert in H by assumption. exact H.
  - apply (f_equal get_extra) in H. rewrite !get_extra_add_anon in H. exact H.
Qed.

Lemma remove_anon_is_fresh S a : fresh_anon (remove_anon a S) a.
Proof.
  unfold fresh_anon, remove_anon, get_map. cbn. unfold encode_anon.
  rewrite sum_maps_lookup_l, sum_maps_lookup_r. apply lookup_delete.
Qed.
Hint Resolve remove_anon_is_fresh : weight.
Hint Rewrite @sweight_add_anon using auto with weight : weight.

Lemma remove_anon_fresh S a : fresh_anon S a -> remove_anon a S = S.
Proof.
  unfold fresh_anon, remove_anon. intros H. rewrite delete_notin.
  - destruct S. cbn. reflexivity.
  - unfold get_map, encode_anon in H. cbn in H. unfold encode_anon in H.
    rewrite sum_maps_lookup_l, sum_maps_lookup_r in H. exact H.
Qed.

Lemma get_map_remove_anon S a : get_map (remove_anon a S) = delete (encode_anon a) (get_map S).
Proof.
  destruct (lookup (anon_accessor a) (get_map S)) eqn:EQN.
  - apply add_anon_remove_anon in EQN. rewrite<- EQN at 2.
    rewrite get_map_add_anon. symmetry. apply delete_insert, remove_anon_is_fresh.
  - rewrite delete_notin by assumption. f_equal. apply remove_anon_fresh. assumption.
Qed.

Lemma remove_anon_add_anon S a v : fresh_anon S a -> remove_anon a (S,, a |-> v) = S.
Proof.
  intros H. apply add_anons_states_eq with (a := a) (v := v) (w := v).
  - apply remove_anon_is_fresh.
  - assumption.
  - rewrite add_anon_remove_anon; [reflexivity | ].
    rewrite get_map_add_anon. simpl_map. reflexivity.
Qed.

(* TODO: change the hypotheses to fst sp <> anon_accessor a? *)
Lemma sget_remove_anon S a sp :
  valid_spath (remove_anon a S) sp -> (remove_anon a S).[sp] = S.[sp].
Proof.
  intros (? & H & _). unfold sget.
  rewrite get_map_remove_anon, lookup_delete_ne; [reflexivity | ].
  intros G. rewrite<- G, remove_anon_is_fresh in H. discriminate.
Qed.
Hint Rewrite sget_remove_anon using validity : spath.

(* TODO: change the hypotheses to fst sp <> anon_accessor a? *)
Lemma sset_remove_anon S a sp v :
  valid_spath (remove_anon a S) sp -> (remove_anon a S).[sp <- v] = remove_anon a (S.[sp <- v]).
Proof.
  intros valid_sp. destruct (valid_sp) as (w & ? & _).
  destruct (get_at_accessor S (anon_accessor a)) eqn:EQN.
  - rewrite <-(add_anon_remove_anon _ _ _ EQN) at 2.
    rewrite sset_add_anon.
    + symmetry. apply remove_anon_add_anon, fresh_anon_sset, remove_anon_is_fresh.
    + eapply valid_spath_diff_fresh_anon; [ | eassumption].
      apply remove_anon_is_fresh.
  - rewrite !remove_anon_fresh by auto with spath. reflexivity.
Qed.
Hint Rewrite sset_remove_anon using validity : spath.

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

Lemma remove_fresh_abstraction i S : fresh_abstraction S i -> remove_abstraction i S = S.
Proof.
  intros ?. unfold remove_abstraction. rewrite delete_notin by assumption. destruct S. reflexivity.
Qed.

Definition not_in_abstraction i (p : spath) := forall j, fst p <> encode_abstraction (i, j).

Lemma decidable_not_in_abstraction i x :
  (exists j, x = encode_abstraction (i, j)) \/ (forall j, x <> encode_abstraction (i, j)).
Proof.
  unfold encode_abstraction.
  destruct (decode' (A := positive + positive * positive) x) as [[ | (i' & j)] | ] eqn:EQN.
  - right. intros j H. rewrite H, decode'_encode in EQN. discriminate.
  - destruct (decide (i = i')) as [<- | ].
    + left. exists j. apply decode'_is_Some in EQN. auto.
    + right. intros ? H. rewrite H, decode'_encode in EQN. congruence.
  - right. intros ? H. rewrite H, decode'_encode in EQN. discriminate.
Qed.

Lemma not_in_abstraction_app i p q : not_in_abstraction i p -> not_in_abstraction i (p +++ q).
Proof. intros H ? ?. eapply H. eassumption. Qed.

Lemma add_remove_add_abstraction S i A : (remove_abstraction i S),,, i |-> A = S,,, i |-> A.
Proof. unfold add_abstraction, remove_abstraction. cbn. f_equal. apply insert_delete_insert. Qed.

(* The hypothesis `fresh_abstraction S i` is not necessary, we're going to remove it. *)
Lemma _get_at_accessor_add_abstraction S i j A (i_fresh : fresh_abstraction S i) :
  get_at_accessor (S,,, i |-> A) (encode_abstraction (i, j)) = lookup j A.
Proof.
  unfold get_map, encode_abstraction. cbn.
  rewrite sum_maps_lookup_r. rewrite flatten_insert by assumption.
  rewrite lookup_union_l.
  - rewrite lookup_kmap by typeclasses eauto. reflexivity.
  - apply lookup_None_flatten. assumption.
Qed.

Lemma get_at_accessor_add_abstraction S i j A :
  get_at_accessor (S,,, i |-> A) (encode_abstraction (i, j)) = lookup j A.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN. rewrite <-add_remove_add_abstraction.
    rewrite !_get_at_accessor_add_abstraction; auto; apply lookup_delete.
  - apply _get_at_accessor_add_abstraction. assumption.
Qed.

(* The hypothesis `fresh_abstraction S i` is not necessary, we're going to remove it. *)
Lemma _get_at_accessor_add_abstraction_notin S i A x (i_fresh : fresh_abstraction S i)
  (H : forall j, x <> encode_abstraction (i, j)) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  unfold get_map. cbn. rewrite flatten_insert' by assumption.
  rewrite sum_maps_union. rewrite lookup_union_l; [reflexivity | ].
  rewrite eq_None_not_Some. rewrite lookup_kmap_is_Some by typeclasses eauto.
  intros (p & ? & G). rewrite lookup_kmap_is_Some in G by typeclasses eauto.
  destruct G as (j & -> & _). eapply H. eassumption.
Qed.

Lemma get_at_accessor_add_abstraction_notin S i A x (H : forall j, x <> encode_abstraction (i, j)) :
  get_at_accessor (S,,, i |-> A) x = get_at_accessor S x.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN at 2. rewrite <-add_remove_add_abstraction.
    rewrite !_get_at_accessor_add_abstraction_notin; auto; apply lookup_delete.
  - apply _get_at_accessor_add_abstraction_notin; assumption.
Qed.

Lemma get_at_accessor_remove_abstraction S i x (H : forall j, x <> encode_abstraction (i, j)) :
  get_at_accessor (remove_abstraction i S) x = get_at_accessor S x.
Proof.
  destruct (lookup i (abstractions S)) eqn:EQN.
  - apply add_remove_abstraction in EQN. rewrite<- EQN at 2. symmetry.
    apply get_at_accessor_add_abstraction_notin. assumption.
  - repeat f_equal. unfold remove_abstraction. rewrite delete_notin by assumption.
    destruct S. reflexivity.
Qed.

Lemma sget_add_abstraction S i A p : not_in_abstraction i p -> (S,,, i |-> A).[p] = S.[p].
Proof. intros H. unfold sget. rewrite get_at_accessor_add_abstraction_notin; auto. Qed.

Lemma get_extra_add_abstraction S i A :
  get_extra (S,,, i |-> A) = (union {[i]} (get_extra S))%stdpp.
Proof. unfold get_extra. cbn. rewrite dom_insert_L. reflexivity. Qed.

Lemma sset_add_abstraction S i A p v :
  not_in_abstraction i p -> (S,,, i |-> A).[p <- v] = S.[p <- v],,, i |-> A.
Proof.
  intros ?. unfold sset. apply state_eq_ext.
  - apply map_eq. intros x.
    destruct (decide (fst p = x)) as [<- | ].
    + rewrite get_map_alter, lookup_alter.
      rewrite !get_at_accessor_add_abstraction_notin by assumption.
      rewrite get_map_alter, lookup_alter. reflexivity.
    + rewrite get_map_alter, lookup_alter_ne by auto.
      destruct (decidable_not_in_abstraction i x) as [(j & ->) | ].
      * rewrite !get_at_accessor_add_abstraction. reflexivity.
      * rewrite !get_at_accessor_add_abstraction_notin by assumption.
        rewrite get_map_alter, lookup_alter_ne by assumption. reflexivity.
  - rewrite get_extra_alter, !get_extra_add_abstraction, get_extra_alter. reflexivity.
Qed.

Lemma fresh_abstraction_sset S p v i :
  fresh_abstraction S i <-> fresh_abstraction (S.[p <- v]) i.
Proof.
  rewrite<-!not_elem_of_dom.
  replace (dom (abstractions S)) with (get_extra S) by reflexivity.
  replace (dom (abstractions (S.[p <- v]))) with (get_extra (S.[p <- v])) by reflexivity.
  unfold sset. rewrite get_extra_alter. reflexivity.
Qed.

Lemma fresh_abstraction_add_anon S a v i :
  fresh_abstraction S i <-> fresh_abstraction (S,, a |-> v) i.
Proof. split; intros H; exact H. Qed.

Hint Resolve-> fresh_abstraction_sset : spath.
Hint Resolve-> fresh_abstraction_add_anon : spath.

Lemma sset_remove_abstraction S i p v :
  not_in_abstraction i p -> remove_abstraction i (S.[p <- v]) = (remove_abstraction i S).[p <- v].
Proof.
  intros ?.
  destruct (lookup i (abstractions S)) as [A | ] eqn:?.
  - rewrite <-(add_remove_abstraction i A S) at 1 by assumption.
    rewrite sset_add_abstraction by assumption.
    apply remove_add_abstraction.
    rewrite <-fresh_abstraction_sset. cbn. apply lookup_delete.
  - rewrite !remove_fresh_abstraction; rewrite <-?fresh_abstraction_sset; easy.
Qed.

Lemma sget_remove_abstraction S i p : not_in_abstraction i p -> (remove_abstraction i S).[p] = S.[p].
Proof. intros H. unfold sget. rewrite get_at_accessor_remove_abstraction; auto. Qed.

Hint Rewrite sget_add_abstraction using assumption : spath.
Hint Rewrite sset_add_abstraction using assumption : spath.
Hint Rewrite sget_remove_abstraction using assumption : spath.
Hint Rewrite sset_remove_abstraction using assumption : spath.

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

(* TODO: autorewrite? *)
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

(* In order to prove that a state is of the form (S,, a |-> v), it's useful to have lemmas that
 * commute the addition of an anonymous variable to the end. *)
Lemma remove_anon_add_anon_ne S a a' v :
  a <> a' -> remove_anon a (S,, a' |-> v) = (remove_anon a S),, a' |-> v.
Proof.
  intros ?. unfold remove_anon, add_anon. cbn. rewrite delete_insert_ne by assumption. reflexivity.
Qed.

Lemma add_abstraction_add_anon S a v i A : (S,, a |-> v),,, i |-> A = (S,,, i |-> A),, a |-> v.
Proof. reflexivity. Qed.

Lemma remove_abstraction_add_anon S a v i :
  remove_abstraction i (S,, a |-> v) = (remove_abstraction i S),, a |-> v.
Proof. reflexivity. Qed.

Lemma remvoe_abstraction_value_add_anon S a v i j :
  remove_abstraction_value (S,, a |-> v) i j = (remove_abstraction_value S i j),, a |-> v.
Proof. reflexivity. Qed.

Hint Rewrite remove_anon_add_anon_ne using eauto with spath; fail : spath.
Hint Rewrite add_abstraction_add_anon : spath.
Hint Rewrite remove_abstraction_add_anon : spath.
Hint Rewrite remvoe_abstraction_value_add_anon : spath.

(* Used to change a mutable borrow from borrow^m(l', v) to borrow^m(l, v). *)
Notation rename_mut_borrow S sp l := (S.[sp <- borrow^m(l, S.[sp +++ [0] ])]).

Variant leq_state_base : LLBC_plus_state -> LLBC_plus_state -> Prop :=
(* Contrary to the article, symbolic values should be typed. Thus, only an integer can be converted
 * to a symbolic value for the moment. *)
| Leq_ToSymbolic S sp n :
    get_node (S.[sp]) = LLBC_plus_intC n -> leq_state_base S (S.[sp <- LLBC_plus_symbolic])
| Leq_ToAbs S a i A
    (a_valid : valid_spath S (anon_accessor a, []))
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs (S.[(anon_accessor a, [])]) A) :
    leq_state_base S ((remove_anon a S),,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon S a
    (a_valid : valid_spath S (anon_accessor a, []))
    (no_loan : not_contains_loan (S.[(anon_accessor a, [])]))
    (no_borrow : not_contains_borrow (S.[(anon_accessor a, [])])) :
    leq_state_base S (remove_anon a S)
| Leq_MoveValue S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (not_in_abstraction : ~in_abstraction sp) :
    leq_state_base S (S.[sp <- bot],, a |-> S.[sp])
(* Note: for the merge, we reuse the region abstraction at i. Maybe we should use another region
 * abstraction index k? *)
| Leq_MergeAbs S i j A B C
    (get_A : lookup i (abstractions S) = Some A) (get_B : lookup j (abstractions S) = Some B)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base S (remove_abstraction i (remove_abstraction j S),,, i |-> C)
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
| Leq_Abs_ClearValue S i j v :
    abstraction_contains_value S i j v -> not_contains_loan v -> not_contains_borrow v ->
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
  etransitivity.
  { constructor. eapply Leq_ToAbs with (a := a).
    - validity. constructor. (* TODO: add this case in the validity tactic? *)
    - repeat apply fresh_abstraction_sset. eassumption.
    - autorewrite with spath. constructor. }
  rewrite remove_anon_add_anon by auto with spath. reflexivity.
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
    - validity. constructor.
    - repeat apply fresh_abstraction_sset. assumption.
    - autorewrite with spath. constructor. constructor. }
  autorewrite with spath. rewrite remove_anon_add_anon by auto with spath. reflexivity.
Qed.

Definition equiv_states (S0 S1 : LLBC_plus_state) :=
  vars S0 = vars S1 /\
  equiv_map (anons S0) (anons S1) /\
  map_Forall2 (fun _ => equiv_map) (abstractions S0) (abstractions S1).

Global Instance LLBC_plus_state_leq_base : LeqBase LLBC_plus_state :=
{ leq_base := leq_state_base }.

Definition leq S0 S1 :=
  exists S1', leq_base^* S0 S1' /\ equiv_states S1' S1.

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

Global Instance LLBC_plus_WellFormed : WellFormed LLBC_plus_state :=
{ well_formed := LLBC_plus_well_formed }.

(*
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
    destruct H. split; weight_inequality.
  - destruct H. split; weight_inequality.
  - apply add_remove_abstraction in get_A, get_B.
    rewrite<- get_B, remove_add_abstraction_ne in get_A by assumption.
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
  - destruct H; split; weight_inequality.
Admitted.
 *)

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

(* TODO: move in PathToSubtree.v *)
(* TODO: name *)
Lemma sget_sset_zeroary_not_prefix S p q v n :
  get_node (S.[p <- v].[q]) = n ->
  arity (get_node v) = 0 -> get_node v <> n -> n <> get_node bot -> ~prefix p q.
Proof.
  intros H ? ? ? Hprefix.
  assert (valid_q : valid_spath (S.[p <- v]) q) by (apply get_not_bot_valid_spath; congruence).
  assert (valid_spath S p). {
    destruct Hprefix as (? & <-). apply valid_spath_app in valid_q.
    destruct valid_q as (valid_p & _).
    rewrite <-sset_not_prefix_valid in valid_p; auto with spath. }
  apply prefix_if_equal_or_strict_prefix in Hprefix. destruct Hprefix as [<- | Hstrict_prefix].
  - rewrite sset_sget_equal in H by assumption. auto.
  - apply get_nil_prefix_right with (S := S.[p <- v]) in Hstrict_prefix.
    + assumption.
    + rewrite sset_sget_equal; assumption.
    + apply get_not_bot_valid_spath. congruence.
Qed.
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
Definition rel_ToAbs a i p q := p = q /\ not_in_abstraction i p /\ fst p <> anon_accessor a.

(* Note: the hypothesis `no_borrow` is not necessary to prove this lemma. *)
(* The hypothesis `no_loan` is not necessary yet, but it will be when we introduce shared
 * borrows. *)
Lemma eval_place_ToAbs S a i A p perm
  (get_a : valid_spath S (anon_accessor a, []))
  (fresh_i : fresh_abstraction S i)
  (Hto_abs : to_abs (S.[(anon_accessor a, [])]) A) :
  forall pi_r, ((remove_anon a S),,, i |-> A) |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_ToAbs a i pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; inversion 1.
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ? & ?). exists pi_r'.
    inversion Heval_proj; subst.
    split; [split; auto using not_in_abstraction_app | ].
    autorewrite with spath in get_q. econstructor; eassumption.
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
Lemma eval_place_RemoveAnon S perm a p
  (a_valid : valid_spath S (anon_accessor a, []))
  (no_loan : not_contains_loan (S.[(anon_accessor a, [])])) :
  forall pi_r, remove_anon a S |-{p} p =>^{perm} pi_r ->
  exists pi_l, rel_change_anon a pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  eapply eval_place_preservation.
  - split; [reflexivity | inversion 1].
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj ? (-> & ?). exists pi_r'.
    inversion Heval_proj; subst.
    + rewrite sget_remove_anon in get_q by validity.
      repeat split; try assumption. eapply Eval_Deref_MutBorrow; eassumption.
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
  (not_in_abstraction : ~in_abstraction sp) :
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
  (not_in_abstraction : ~in_abstraction sp) :
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

Definition rel_MergeAbs i j p q :=
  p = q /\ not_in_abstraction i p /\ not_in_abstraction j p /\ not_in_abstraction i q.

Lemma eval_place_MergeAbs S i j A B C perm p
    (get_A : lookup i (abstractions S) = Some A) (get_B : lookup j (abstractions S) = Some B)
    (Hmerge : merge_abstractions A B C) (diff : i <> j) :
    forall pi_r, (remove_abstraction i (remove_abstraction j S),,, i |-> C) |-{p} p =>^{perm} pi_r ->
    exists pi_l, rel_MergeAbs i j pi_l pi_r /\ S |-{p} p =>^{perm} pi_l.
Proof.
  apply eval_place_preservation.
  - repeat split; inversion 1.
  - reflexivity.
  - intros proj pi_r pi_r' Heval_proj pi_l rel_pi_l_pi_r.
    inversion Heval_proj; subst.
    + destruct rel_pi_l_pi_r as (-> & ? & ? & ?). exists (pi_r +++ [0]).
      repeat split; [eauto using not_in_abstraction_app.. | ].
      autorewrite with spath in get_q. eapply Eval_Deref_MutBorrow; eassumption.
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
  valid_spath (S,,, i |->  A) sp -> not_in_abstraction i sp -> valid_spath S sp.
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
  | a_valid : valid_spath ?S (anon_accessor ?a, _),
    fresh_i : fresh_abstraction ?S ?i,
    Hto_abs : to_abs ?v ?A,
    Heval : ((remove_anon ?a ?S),,, ?i |-> ?A) |-{p} ?p =>^{?perm} ?pi |- _ =>
        let _valid_pi := fresh "_valid_pi" in
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        (* Proving that pi is a valid spath of (remove_anon a S),,, i |-> A *)
        pose proof (eval_place_valid _ _ _ _ Heval) as _valid_pi;
        apply (eval_place_ToAbs _ _ _ _ _ _ a_valid fresh_i Hto_abs) in Heval;
        destruct Heval as (? & (-> & pi_not_in_abstraction & pi_not_in_a) & eval_p_in_Sl);
        (* We can then prove that pi is a valid spath of (remove_anon a S) *)
        pose proof (valid_spath_add_abstraction _ _ _ _ _valid_pi pi_not_in_abstraction) as valid_pi;
        clear _valid_pi
  | a_valid : valid_spath ?S (anon_accessor ?a, _),
    no_loan : not_contains_loan (?S.[(anon_accessor ?a, _)]),
    Heval : (remove_anon ?a ?S) |-{p} ?p =>^{?perm} ?pi |- _ =>
        let valid_pi := fresh "valid_pi" in
        let pi_not_in_a := fresh "pi_not_in_a" in
        pose proof (eval_place_valid _ _ _ _ Heval) as valid_pi;
        apply (eval_place_RemoveAnon _ _ _ _ a_valid no_loan) in Heval;
        destruct Heval as (? & (-> & pi_not_a) & eval_p_in_Sl)
  (* Case MoveValue *)
  (* Preservation of place evaluation with permission Imm. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    not_in_abstraction0 : ¬ in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{Imm} ?pi |- _ =>
        apply (eval_place_MoveValue_imm _ _ _ _ fresh_a valid_sp not_in_abstraction0) in H;
        destruct H as (pi_l & rel_pi_l_pi_r & eval_p_in_Sl)
  (* Preservation of place evaluation with permission Mut or Mov. *)
  | no_outer_loan : not_contains_outer_loan (?S.[?sp]),
    fresh_a : fresh_anon ?S ?a,
    valid_sp : valid_spath ?S ?sp,
    not_in_abstraction0 : ¬ in_abstraction ?sp,
    H : (?S.[?sp <- bot],, ?a |-> ?S.[?sp]) |-{p} ?p =>^{?perm} ?pi |- _ =>
        apply eval_place_change_anon_not_in_spath in H;[ | discriminate | assumption..];
        destruct H as (pi_l & ((-> & ?) & ?) & eval_p_in_Sl)

  | get_A : lookup ?i (abstractions ?S) = Some ?A, get_B : lookup ?j (abstractions ?S) = Some ?B,
    Hmerge : merge_abstractions ?A ?B ?C, diff : ?i <> ?j,
    Heval : (remove_abstraction ?i (remove_abstraction ?j ?S),,, ?i |-> ?C) |-{p} ?p =>^{?perm} ?pi_r
    |- _ =>
        apply (eval_place_MergeAbs _ _ _ _ _ _ _ _ get_A get_B Hmerge diff) in Heval;
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

(* TODO: move *)
Lemma get_abstraction_add_anon i S a v :
  lookup i (abstractions (S,, a |-> v)) = lookup i (abstractions S).
Proof. reflexivity. Qed.
Hint Rewrite get_abstraction_add_anon : spath.

(* TODO: move *)
Lemma get_abstraction_sset i S p v :
  not_in_abstraction i p -> lookup i (abstractions (S.[p <- v])) = lookup i (abstractions S).
Proof.
  intros H. unfold sset, alter_at_accessor. cbn. repeat autodestruct.
  intros. cbn. apply lookup_alter_ne. intros ?. subst.
  eapply H. unfold encode_abstraction. symmetry. rewrite<-decode'_is_Some. eassumption.
Qed.
Hint Rewrite get_abstraction_sset using assumption : spath.

Lemma operand_preserves_LLBC_plus_rel op :
  forward_simulation leq_base^* leq_val_state_base^* (eval_operand op) (eval_operand op).
Proof.
  apply preservation_by_base_case.
  intros Sr (vr & S'r) Heval Sl Hle. destruct Heval.
  - destruct Hle.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_step.
        { eapply Leq_ToSymbolic with (sp := sp); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_step.
        { apply Leq_ToAbs with (a := a) (i := i) (A := A).
          all: autorewrite with spath; try assumption; validity. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_step.
        { apply Leq_RemoveAnon with (a := a); autorewrite with spath; try assumption; validity. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_add_anon.
        { apply Leq_MoveValue with (sp := sp) (a := a).
          autorewrite with spath. assumption. eassumption. validity. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_step.
        { apply (Leq_MergeAbs _ i j A B C); assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_add_anon.
        { apply (Leq_Fresh_MutLoan _ sp l a).
          apply not_state_contains_add_anon. assumption. not_contains.
          eassumption.
          autorewrite with spath. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_add_anon.
        { apply (Leq_Reborrow_MutBorrow _ sp l0 l1 a).
          apply not_state_contains_add_anon. assumption. not_contains. eassumption.
          autorewrite with spath. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_step.
        { apply (Leq_Abs_ClearValue _ i j v); autorewrite with spath; assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + eapply complete_square_diagram'.
      * constructor.
      * leq_val_state_add_anon.
        { apply (Leq_AnonValue _ a); [assumption.. | ]. eassumption. }
        { reflexivity. }
        reflexivity.
      * reflexivity.
  - admit.
  - destruct Hle.
    + eval_place_preservation.
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the value we turn into a symbolic value is in the place we move. *)
      * autorewrite with spath in * |-.
        eapply complete_square_diagram'.
        -- constructor. eassumption.
           (* TODO: automatize *)
           eapply not_value_contains_vset_rev with (p := q).
           autorewrite with spath.
           eapply not_value_contains_zeroary; rewrite H. reflexivity. easy. eassumption.
           eapply not_value_contains_vset_rev with (p := q).
           autorewrite with spath.
           eapply not_value_contains_zeroary; rewrite H. reflexivity. discriminate. eassumption.
        -- leq_val_state_step.
           { apply Leq_ToSymbolic with (sp := (anon_accessor a, q)) (n := n).
             all: autorewrite with spath; assumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- states_eq.
      (* Case 2: the value we turn into a symbolic value is disjoint to the place we move. *)
      * assert (disj sp pi) by reduce_comp.
        autorewrite with spath in * |-.
        eapply complete_square_diagram'.
        --- apply Eval_move; eassumption.
        --- leq_val_state_step.
            { apply Leq_ToSymbolic with (sp := sp) (n := n).
              all: autorewrite with spath; assumption. }
            { autorewrite with spath. reflexivity. }
            reflexivity.
        --- states_eq.
    + eval_place_preservation.
      autorewrite with spath in * |-.
      eapply complete_square_diagram'.
      * apply Eval_move; eassumption.
      * leq_val_state_step.
        { apply Leq_ToAbs with (a := a) (i := i); try validity.
          autorewrite with spath. assumption. autorewrite with spath. eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * autorewrite with spath. reflexivity.
    + eval_place_preservation.
      autorewrite with spath in * |-.
      eapply complete_square_diagram'.
      * apply Eval_move; eassumption.
      * leq_val_state_step.
        { apply Leq_RemoveAnon with (a := a). validity. all: autorewrite with spath; assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * autorewrite with spath. reflexivity.
    + eval_place_preservation.
      (* The place pi we move does not contain any bottom value is the right state, as a
       * condition of the move rule.
       * The right state is Sr = S.[sp <- bot],, a |-> S.[sp].
       * That means that that sp cannot be inside sp, thus pi and sp are disjoint. *)
      assert (~prefix pi sp).
      { intros (q & <-). autorewrite with spath in move_no_bot. eapply move_no_bot with (p := q).
        apply vset_same_valid. validity. autorewrite with spath. reflexivity. }
      assert (disj sp pi) by reduce_comp.
      autorewrite with spath in * |-. eapply complete_square_diagram'.
      * apply Eval_move; eassumption.
      * leq_val_state_add_anon.
         { apply Leq_MoveValue with (sp := sp) (a := a).
           autorewrite with spath. assumption. assumption. validity. assumption. }
         { autorewrite with spath. reflexivity. }
         reflexivity.
      * states_eq.
    + eval_place_preservation.
      autorewrite with spath in * |-. eapply complete_square_diagram'.
      * apply Eval_move; eassumption.
      * leq_val_state_step.
        { apply Leq_MergeAbs with (A := A) (B := B) (i := i) (j := j).
          all: autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * autorewrite with spath. reflexivity.
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
      eapply complete_square_diagram'.
      * apply Eval_move; eassumption.
      * leq_val_state_add_anon.
        { apply Leq_Fresh_MutLoan with (sp := sp) (l := l).
          (* TODO: the tactic not_contains should solve it. *)
          apply not_state_contains_add_anon. not_contains. not_contains.
          eassumption. autorewrite with spath. assumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * states_eq.
    + apply eval_place_Reborrow_MutBorrow in Heval; [ | exact get_borrow].
      destruct Heval as (? & (-> & ?) & eval_p_in_Sl).
      autorewrite with spath in * |-.
      destruct (decidable_prefix pi sp) as [(q & <-) | ].
      (* Case 1: the spath sp we reborrow is in the place pi we move. *)
      * eapply complete_square_diagram'.
        -- apply Eval_move. eassumption.
           eapply not_contains_rename_mut_borrow; eauto with spath.
           eapply not_contains_rename_mut_borrow; eauto with spath.
        -- leq_val_state_add_anon.
          (* Because the place we reborrow was at sp +++ q, and that we move and return S.[sp],
           * the borrow is now in the anonymous value we evaluate a0, at path q. *)
           (* TODO: rename a0 *)
          { apply Leq_Reborrow_MutBorrow with (sp := (anon_accessor a0, q)) (l1 := l1).
            not_contains. eassumption. autorewrite with spath. eassumption. }
          { autorewrite with spath. reflexivity. }
          reflexivity.
        -- autorewrite with spath. reflexivity.
       (* Case 2: the spath sp we reborrow ... *)
      * eapply complete_square_diagram'.
        -- apply Eval_move. eassumption.
           all: erewrite sget_reborrow_mut_borrow_not_prefix in * by eassumption; assumption.
        -- leq_val_state_add_anon.
           { apply Leq_Reborrow_MutBorrow with (sp := sp) (l1 := l1).
             not_contains. eassumption. autorewrite with spath. eassumption. }
           { autorewrite with spath. reflexivity. }
           reflexivity.
        -- autorewrite with spath.
           erewrite sget_reborrow_mut_borrow_not_prefix by eassumption.
           erewrite sset_reborrow_mut_borrow_not_prefix by eauto with spath. reflexivity.
    + eval_place_preservation. autorewrite with spath in *. eapply complete_square_diagram'.
      * constructor; eassumption.
      * leq_val_state_step.
        { eapply Leq_Abs_ClearValue with (i := i) (j := j); autorewrite with spath; eassumption. }
        { autorewrite with spath. reflexivity. }
        reflexivity.
      * reflexivity.
    + apply eval_place_AnonValue in Heval.
      destruct Heval as (? & (-> & ?) & eval_p_in_Sl).
      autorewrite with spath in *. eapply complete_square_diagram'.
      * econstructor; eassumption.
      * leq_val_state_add_anon.
        { apply Leq_AnonValue; eassumption. }
        { reflexivity. }
        reflexivity.
      * reflexivity.
Abort.

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

(* TODO: move in base.v *)
Lemma nth_error_singleton {A} (a b : A) i : nth_error [a] i = Some b -> a = b /\ i = 0.
Proof. destruct i; cbn; rewrite ?nth_error_nil; split; congruence. Qed.

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

(* TODO: move in PathToSubtree.v *)
Lemma not_state_contains_map_Forall S P :
  not_state_contains P S <-> map_Forall (fun _ => not_value_contains P) (get_map S).
Proof.
  split.
  - intros H i ? get_i p valid_p ?. eapply (H (i, p)). eexists. split; eassumption.
    unfold sget. replace (fst (i, p)) with i by reflexivity. rewrite get_i. assumption.
  - intros H p (? & G & ?) P_p. eapply H. eassumption. eassumption. unfold sget in P_p.
    rewrite G in P_p. exact P_p.
Qed.

Instance decide_not_state_contains P `(forall v, Decision (P v)) S :
  Decision (not_state_contains P S).
Proof.
  destruct (decide (map_Forall (fun _ => not_value_contains P) (get_map S)));
    rewrite <-not_state_contains_map_Forall in * |-; [left | right]; assumption.
Defined.

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
      { eapply Leq_MergeAbs with (i := 1%positive) (j := 2%positive); [reflexivity.. | | discriminate].
        eapply MergeAbsInsert with (i := 3%positive); [reflexivity.. | ].
        apply MergeAbsEmpty. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). reflexivity. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_RemoveAnon with (a := 1%positive).
        econstructor; split; [reflexivity | constructor]. all: compute_done. }
      simpl_state. reflexivity.
    - split; [ | split]; try reflexivity.
      apply map_Forall2_singleton.
      exists {[1%positive := 1%positive; 2%positive := 3%positive; 3%positive := 2%positive]}.
      repeat split; compute_done.
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
      { eapply Leq_MergeAbs with (i := 1%positive) (j := 2%positive); [reflexivity.. | | discriminate].
        eapply MergeAbsInsert with (i := 3%positive); [reflexivity.. | ].
        apply MergeAbsEmpty. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_ToSymbolic with (sp := (encode_var z, [0])). reflexivity. }
      simpl_state.
      etransitivity; [constructor | ].
      { eapply Leq_RemoveAnon with (a := 1%positive).
        econstructor. split; [reflexivity | constructor]. all: compute_done. }
      simpl_state. reflexivity.
    - split; [ | split]; try reflexivity.
      apply map_Forall2_singleton.
      exists {[1%positive := 2%positive; 2%positive := 3%positive; 3%positive := 1%positive]}.
      repeat split; compute_done.
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
          with (i := 1%positive) (j := 3%positive) (q := (encode_var 3%positive, [])).
        - discriminate.
        - reflexivity.
        - reflexivity.
        - constructor.
        - intros ? ?. apply not_strict_prefix_nil.
        - intros H. inversion H. discriminate. }
      simpl_state. etransitivity.
      (* ... so that we could end the region abstraction ... *)
      { constructor. eapply Reorg_end_abstraction with (i := 1%positive).
        - reflexivity.
        - cbn. apply MergeInsert with (j := 2%positive); [reflexivity | ].
          apply MergeInsert with (j := 3%positive); [reflexivity | ].
          apply MergeEmpty.
        - compute_done.
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
        - intros H. inversion H. discriminate.
        - intros H. inversion H. discriminate. }
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
