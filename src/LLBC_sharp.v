(** * Mechanized_LLBC.LLBC_sharp : Semantics of LLBC#. *)
From stdpp Require Import pmap fin_maps.
Require Import base PathToSubtree lang.
Require Import Symbolic_states.

(** * Symbolic relations. *)
(** A version of to-abs that is limited compared to the paper. Currently, we can only turn into a
   region abstraction a value of the form:
   - borrow^m l σ (with σ a symbolic value)
   - borrow^m l0 (loan^m l1)
   Consequently, a single region abstraction is created.
 *)
Variant to_abs : value -> Pmap value -> Prop :=
| ToAbs_MutReborrow l0 l1 kb kl ty (Hk : kb <> kl) :
    to_abs (borrow^m(l0, loan^m(ty, l1)))
           ({[kb := (borrow^m(l0, VSymbolic ty)); kl := loan^m(ty, l1)]})%stdpp
| ToAbs_MutBorrow l v k ty (Htype : is_of_type ty v)
    (v_no_loan : not_contains_loan v) (v_no_borrow : not_contains_borrow v) :
    to_abs (borrow^m(l, v)) ({[k := (borrow^m(l, VSymbolic ty))]})%stdpp
.

Definition measure S := sweight (fun _ => 1) S + size (abstractions S).
Notation abs_measure S := (map_sum (vweight (fun _ => 1)) S).

Variant leq_state_base_n : nat -> state -> state -> Prop :=
| Leq_ToSymbolic_n S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base_n (vweight (fun _ => 1) (S.[sp])) S (S.[sp <- VSymbolic ty])
| Leq_ToAbs_n S a i v A
    (fresh_a : fresh_anon S a)
    (fresh_i : fresh_abstraction S i)
    (Hto_abs : to_abs v A) :
    leq_state_base_n (vweight (fun _ => 1) v) (S,, a |-> v) (S,,, i |-> A)
(* Note: in the article, this rule is a consequence of Le_ToAbs, because when the value v doesn't
 * contain any loan or borrow, no region abstraction is created. *)
| Leq_RemoveAnon_n S a v
    (fresh_a : fresh_anon S a)
    (no_loan : not_contains_loan v)
    (no_borrow : not_contains_borrow v) :
    leq_state_base_n (1 + vweight (fun _ => 1) v) (S,, a |-> v) S
| Leq_MoveValue_n S sp a
    (no_outer_loan : not_contains_outer_loan (S.[sp]))
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_borrow : not_in_borrow S sp)
    (sp_in_abstraction : not_in_abstraction sp) :
    leq_state_base_n 0 S (S.[sp <- bot],, a |-> S.[sp])
| Leq_MergeAbs_n S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base_n (abs_measure A + abs_measure B - abs_measure C + 2)
                                (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan_n S sp l' a ty
    (fresh_l' : is_fresh l' S)
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp])) :
    leq_state_base_n 0 S (S.[sp <- loan^m(ty, l')],, a |-> borrow^m(l', S.[sp]))
| Leq_Reborrow_MutBorrow_n (S : state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp +++ [0] ])) :
    leq_state_base_n 0 S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(ty, l1)))
| Leq_Abs_ClearValue_n S i j v
    (get_at_i_j : abstraction_element S i j  = Some v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base_n (1 + vweight (fun _ => 1) v) S (remove_abstraction_value S i j)
| Leq_AnonValue_n S a (is_fresh : fresh_anon S a) :
    leq_state_base_n 0 S (S,, a |-> bot)
.

(* Note: the definition is duplicated in [leq_state_base_n].
 * Perhaps we should only define leq_state_base_n, and define [leq_state_base Sl Sr] as
 * [exists n, leq_state_base_n n Sl Sr]. *)
Variant leq_state_base : state -> state -> Prop :=
(* Contrary to the article, symbolic values should be typed. Thus, only an integer can be converted
 * to a symbolic value for the moment. *)
| Leq_ToSymbolic S sp ty (Htype : is_of_type ty (S.[sp]))
    (no_loan : not_contains_loan (S.[sp])) (no_borrow : not_contains_borrow (S.[sp])) :
    leq_state_base S (S.[sp <- VSymbolic ty])
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
    (sp_not_in_borrow : not_in_borrow S sp)
    (sp_not_in_abstraction : not_in_abstraction sp) :
    leq_state_base S (S.[sp <- bot],, a |-> S.[sp])
(* Note: for the merge, we reuse the region abstraction at i. Maybe we should use another region
 * abstraction index k? *)
| Leq_MergeAbs S i j A B C
    (fresh_i : fresh_abstraction S i) (fresh_j : fresh_abstraction S j)
    (Hmerge : merge_abstractions A B C) :
    i <> j -> leq_state_base (S,,, i |-> A,,, j |-> B) (S,,, i |-> C)
| Leq_Fresh_MutLoan S sp l' a ty
    (fresh_l' : is_fresh l' S)
    (fresh_a : fresh_anon S a)
    (valid_sp : valid_spath S sp)
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp])) :
    leq_state_base S (S.[sp <- loan^m(ty, l')],, a |-> borrow^m(l', S.[sp]))
| Leq_Reborrow_MutBorrow (S : state) (sp : spath) (l0 l1 : loan_id) (a : anon) ty
    (fresh_l1 : is_fresh l1 S)
    (fresh_a : fresh_anon S a)
    (get_borrow_l0 : get_node (S.[sp]) = nborrow^m(l0))
    (sp_not_in_abstraction : not_in_abstraction sp)
    (Htype : is_of_type ty (S.[sp +++ [0] ])) :
    leq_state_base S ((rename_mut_borrow S sp l1),, a |-> borrow^m(l0, loan^m(ty, l1)))
| Leq_Abs_ClearValue S i j v
    (get_at_i_j : abstraction_element S i j = Some v)
    (no_loan : not_contains_loan v) (no_borrow : not_contains_borrow v) :
    leq_state_base S (remove_abstraction_value S i j)
| Leq_AnonValue S a (is_fresh : fresh_anon S a) : leq_state_base S (S,, a |-> bot)
.

Definition leq_symbolic := chain equiv_states leq_state_base^*.

Inductive eval_proj (S : state) perm : proj -> spath -> spath -> Prop :=
(* Coresponds to R-Deref-MutBorrow and W-Deref-MutBorrow in the article. *)
| E_Deref_MutBorrow q l
    (Hperm : perm <> Mov)
    (get_q : get_node (S.[q]) = nborrow^m(l)) :
    eval_proj S perm Deref q (q +++ [0])
.

Section Leq_state_base_n_is_leq_state_base.
  Hint Constructors leq_state_base : core.
  Hint Constructors leq_state_base_n : core.
  Lemma leq_state_base_n_is_leq_state_base Sl Sr :
    leq_state_base Sl Sr <-> exists n, leq_state_base_n n Sl Sr.
  Proof.
    split.
    - intros [ ]; eexists; eauto.
    - intros (n & [ ]); eauto.
  Qed.
End Leq_state_base_n_is_leq_state_base.

(** A branching state [Br] is more general than a branching state [Bl] if for any token [r], if [Bl] maps a control-flow token [r] to a symbolic state [Sl] ([lookup r Bl = Some Sl]), then [Br] maps [r] to a more general state [Sr] ([lookup r Br = Some Sr] and [leq_symbolic Sl Sr]).

   Note that the domain of [Br] can be bigger than the domain of [Bl]. There can be computations that terminate on a token [r] that are abstracted by [Bl] but not [Br]. *)
Variant leq_option_symbolic : relation (option state) :=
  | LeqNone oSr : leq_option_symbolic None oSr
  | LeqSome Sl Sr : leq_symbolic Sl Sr -> leq_option_symbolic (Some Sl) (Some Sr).

Definition leq_branching (Bl Br : branching_state) :=
  forall r, leq_option_symbolic (lookup r Bl) (lookup r Br).

(** In the ICPF article, Ho et al introduce a join operation, described with non-deterministic computation rules. However, we are not interested in an algorithm for joins. The join [Bjoin] of two states [B0] and [B1] can be provided by an oracle, we do not describe the computation rules. We only require two properties.
   - The state [B_join] is an upper bound of [B0] and [B1], that means that we have [leq_branching B0 Bjoin] and [leq_branching Bs Bjoin].
   - If a control-flow token [r] is not in the domain of [Bl] (respectively [Br]), then [lookup r Bjoin = lookup r Br] (respectively [lookup r Bjoin = lookup r Bl]).

   The second condition is here to ensure that LLBC is a stable subset of LLBC#. In particular, the join of a state [B = {[r := S]}] and the empty state can only be [B].
 *)
Variant option_is_join :
  option state -> option state -> option state -> Prop :=
  | UpperBound_None_None : option_is_join None None None
  | UpperBound_Some_None S0 : option_is_join (Some S0) None (Some S0)
  | UpperBound_None_Some S1 : option_is_join None (Some S1) (Some S1)
  | UpperBound_Some_Some S0 S1 S2 : leq_symbolic S0 S2 -> leq_symbolic S1 S2 ->
      option_is_join (Some S0) (Some S1) (Some S2).

Definition is_join (B0 B1 Bjoin : branching_state) :=
  forall r, option_is_join (lookup r B0) (lookup r B1) (lookup r Bjoin).

(** * Operational semantics. *)
(* TODO: eval_path represents a computation, that evaluates and accumulate the result over [...] *)
Inductive eval_path (S : state) perm : path -> spath -> spath -> Prop :=
(* Corresponds to R-Base and W-Base in the article. *)
| E_Path_Nil pi : eval_path S perm [] pi pi
| E_Path_Proj proj P p q r
    (Heval_proj : eval_proj S perm proj p q) (Heval_path : eval_path S perm P q r) :
    eval_path S perm (proj :: P) p r.

Definition eval_place S perm (p : place) pi :=
  let pi_0 := (encode_var (fst (fst p)), []) in
  valid_spath S pi_0 /\ eval_path S perm (snd (fst p)) pi_0 pi.
(* TODO: reserved notation. *)
Global Notation "S  |-{p}  p =>^{ perm } pi" := (eval_place S perm p pi)
  (at level 50) : llbc_sharp_scope.

Definition copiable (ty : LLBC_type) := True.

Inductive copy_val : value -> value -> Prop :=
| Copy_val_int (n : nat) : copy_val (VInt n) (VInt n)
| Copy_val_bool (b : bool) : copy_val (VBool b) (VBool b)
| Copy_val_symbolic ty : copiable ty ->
    copy_val (VSymbolic ty) (VSymbolic ty)
.

Variant eval_operand : operand -> state -> (value * state) -> Prop :=
| E_IntConst S n : S |-{op} Const (IntConst n) => (VInt n, S)
| E_BoolConst S b : S |-{op} Const (BoolConst b) => (VBool b, S)
| E_Copy S (p : place) pi v
    (Heval_place : S |-{p} p =>^{Imm} pi) (Hcopy_val : copy_val (S.[pi]) v) :
    S |-{op} Copy p => (v, S)
| E_Move S (p : place) pi (Heval : S |-{p} p =>^{Mov} pi)
    (move_no_loan : not_contains_loan (S.[pi])) (move_no_bot : not_contains_bot (S.[pi])) :
    S |-{op} Move p => (S.[pi], S.[pi <- bot])
where "S  |-{op}  op  =>  r" := (eval_operand op S r) : llbc_sharp_scope.

Variant eval_binary_op : BinOp -> value -> value -> value -> Prop :=
  | E_Add_int_int m n :
      eval_binary_op BAdd (VInt m) (VInt n) (VInt (m + n))
  | E_Add_int_symbolic m :
      eval_binary_op BAdd (VInt m) (VSymbolic TInt) (VSymbolic TInt)
  | E_Add_symbolic_int n :
      eval_binary_op BAdd (VSymbolic TInt) (VInt n) (VSymbolic TInt)
  | E_Add_symbolic_symbolic :
      eval_binary_op BAdd (VSymbolic TInt) (VSymbolic TInt) (VSymbolic TInt)
  | E_Le_int_int m n :
      eval_binary_op BLe (VInt m) (VInt n) (VBool (m <=? n))
  | E_Le_int_symbolic m :
      eval_binary_op BLe (VInt m) (VSymbolic TInt) (VSymbolic TBool)
  | E_Le_symbolic_int n :
      eval_binary_op BLe (VSymbolic TInt) (VInt n) (VSymbolic TBool)
  | E_Le_symbolic_symbolic :
      eval_binary_op BLe (VSymbolic TInt) (VSymbolic TInt) (VSymbolic TBool)
.

Variant eval_rvalue : rvalue -> state -> (value * state) -> Prop :=
  | E_Use op S vS' (Heval_op : S |-{op} op => vS') : S |-{rv} (Use op) => vS'
  (* For the moment, the only operation is the natural sum. *)
  | E_BinOp S S' S'' binop op_0 op_1 v0 v1 w
      (eval_op_0 : S |-{op} op_0 => (v0, S')) (eval_op_1 : S' |-{op} op_1 => (v1, S''))
      (Hbinop : eval_binary_op binop v0 v1 w) :
      S |-{rv} (BinaryOp binop op_0 op_1) => (w, S'')
  (* Note: with a typing judgement on LLBC, and with a well-typedness invariant, the type
   * [ty] could be obtained from the type of the place p, and the well-typedness of
   * [S.[pi]] could be derived from the well-typedness of [S]. *)
  | E_MutBorrow S p pi l ty (eval_p : S |-{p} p =>^{Mut} pi)
      (borrow_no_loan : not_contains_loan (S.[pi]))
      (borrow_no_bot : not_contains_bot (S.[pi]))
      (fresh_l : is_fresh l S)
      (Htype : is_of_type ty (S.[pi])) :
      S |-{rv} (&mut p) => (borrow^m(l, S.[pi]), S.[pi <- loan^m(ty, l)])
where "S  |-{rv}  rv  =>  r" := (eval_rvalue rv S r) : llbc_sharp_scope.

(* Note: we use the variable names i' and j' instead of i and j that are used for leq_state_base.
 * We are also using the name A' instead of A, B or C for the region abstractions.
 *)
Variant reorg : state -> state -> Prop :=
(* Ends a borrow when it's not in an abstraction: *)
| Reorg_End_MutBorrow S (p q : spath) l ty
    (get_loan : get_node (S.[p]) = nloan^m(ty, l)) (get_borrow : get_node (S.[q]) = nborrow^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (Hdisj : disj p q)
    (loan_not_in_abstraction : not_in_abstraction p)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S (S.[p <- (S.[q +++ [0] ])].[q <- bot])
(* Ends a borrow when it's in an abstraction: *)
(* The value that is transferred back, S.[q +++ [0]], has to be of integer type. *)
| Reorg_End_MutBorrow_in_abstraction S q i' j' l ty
    (get_loan : abstraction_element S i' j' = Some (loan^m(ty, l)))
    (get_borrow : get_node (S.[q]) = nborrow^m(l))
    (type_borrow : is_of_type ty (S.[q +++ [0] ]))
    (Hno_loan : not_contains_loan (S.[q +++ [0] ])) (Hnot_in_borrow : not_in_borrow S q)
    (borrow_not_in_abstraction : not_in_abstraction q) :
    reorg S ((remove_abstraction_value S i' j').[q <- bot])
(* q refers to a path in abstraction A, at index j. *)
| Reorg_End_Abstraction S i' A' S'
    (fresh_i' : fresh_abstraction S i')
    (A_no_loans : map_Forall (fun _ => not_contains_loan) A')
    (Hadd_anons : add_anons S A' S') : reorg (S,,, i' |-> A') S'
.

(* This operation realizes the second half of an assignment p <- rv, once the rvalue v has been
 * evaluated to a pair (v, S). *)
Variant store (p : place) : value * state -> state -> Prop :=
| Store v S (sp : spath) (a : anon)
  (eval_p : S |-{p} p =>^{Mut} sp)
  (no_outer_loan : not_contains_outer_loan (S.[sp]))
  (Hstore_type : store_compatible_types S sp v) :
  fresh_anon S a -> store p (v, S) (S.[sp <- v],, a |-> S.[sp])
.

(** Turning the state at the end of the last iteration of the loop into the state after the loop. *)
(** We simply need to rename the tags of each branch. *)
Definition end_loop (B : branching_state) : branching_state := pkmap end_loop_tag B.

Inductive eval_stmt : statement -> state -> branching_state -> Prop :=
  | E_Nop S : S |-# Nop ~> {[rUnit := S]}
  | E_Panic S : S |-# Panic ~> {[rPanic := S]}
  | E_Break S : S |-# Break ~> {[rBreak := S]}
  | E_Continue S : S |-# Continue ~> {[rContinue := S]}
  | E_Seq_Propagate S0 B1 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-# stmt_0 ~> B1) (Hno_unit : lookup rUnit B1 = None) :
      S0 |-# (Seq stmt_0 stmt_1) ~> B1
  | E_Seq_Unit_Propagate S0 B1 S1 B2 stmt_0 stmt_1
      (eval_stmt_0 : S0 |-# stmt_0 ~> B1)
      (H_unit : lookup rUnit B1 = Some S1)
      (leq_B1_B2 : leq_branching (delete rUnit B1) B2)
      (eval_stmt_1 : S1 |-# stmt_1 ~> B2) :
      S0 |-# (Seq stmt_0 stmt_1) ~> B2
  | E_Assign S vS' S'' p rv (eval_rv : S |-{rv} rv => vS') (Hstore : store p vS' S'') :
      S |-# ASSIGN p <- rv ~> {[rUnit := S'']}
  | E_IfThenElse_T S S' B_if cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool true, S'))
      (Heval_if_branch : S' |-# stmt_if ~> B_if) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B_if
  | E_IfThenElse_F S S' B_else cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VBool false, S'))
      (Heval_else_branch : S' |-# stmt_else ~> B_else) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B_else
  (* Note: in the ICFP'24 article, the symbolic value is replaced by a concrete boolean in each
     branch. We cannot do that as symbolic values are currently not named. *)
  | E_IfThenElse_Symbolic S S' B cond stmt_if stmt_else
      (eval_cond : S |-{op} cond => (VSymbolic TBool, S'))
      (Heval_if_branch : S' |-# stmt_if ~> B)
      (Heval_else_branch : S' |-# stmt_else ~> B) :
      S |-# (IF cond {{ stmt_if }} ELSE {{ stmt_else }}) ~> B
  | E_Reorg S0 S1 B2 stmt (Hreorg : reorg^* S0 S1) (Heval : S1 |-# stmt ~> B2) :
      S0 |-# stmt ~> B2
  (* We perform a single loop iteration, and stop because it does not continue. *)
  | E_Loop_Stop S body B1
      (eval_body : S |-# body ~> B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (no_continue : lookup rContinue B1 = None) :
      S |-# (LOOP {{ body }}) ~> (end_loop B1)
  | E_Loop_Continue S0 body B1 S1 Bend
      (eval_body : S0 |-# body ~> B1)
      (* An iteration that yields `rUnit` gets stuck. *)
      (no_unit : lookup rUnit B1 = None)
      (leq_B1_Bend : leq_branching (end_loop (delete rContinue B1)) Bend)
      (Hcontinue : lookup rContinue B1 = Some S1)
      (Heval2 : S1 |-# (LOOP {{ body }}) ~> Bend) :
       S0 |-# (LOOP {{ body }}) ~> Bend
  (* These are LLBC## only rules. *)
  | E_Loop_Invariant body Sinv Binv
      (eval_body : Sinv |-# body ~> Binv)
      (inv_preservation : lookup rContinue Binv = Some Sinv)
      (no_unit : lookup rUnit Binv = None) :
      Sinv |-# (LOOP {{ body }}) ~> (end_loop (delete rContinue Binv))
  | Consequence_Precondition s Sl Sr B
      (Hweaken : leq_symbolic Sl Sr) (Heval : Sr |-# s ~> B) :
      Sl |-# s ~> B
  | Consequence_Postcondition s S Bl Br
      (Heval : S |-# s ~> Bl) (Hweaken : leq_branching Bl Br) :
      S |-# s ~> Br
where "S |-# stmt ~> B" := (eval_stmt stmt S B) : llbc_sharp_scope.
