From chamois Require Import Memdata Memtype Memory Integers.
From rustc.semantics Require Import PL.
From rustc.semantics Require Import HLPL_No_Anon.
From rustc Require Import lang.
From chamois Require Import Maps.
From Stdlib Require Import ZArith.
From Stdlib Require Import Program.
From Stdlib Require Import List.
Import ListNotations.
Require Import BinNums.

Open Scope positive_scope.
Open Scope list_scope.
Coercion BinPos.Pos.of_nat : nat >-> positive.

Local Notation "a # b" := (PXMap.get b a) (at level 1).
Local Notation "a ## b" := (PTree.get b a) (at level 1).

Definition x := 1%positive.
Definition enc_x := encode_var x.
Definition y := 2 % positive.
Definition enc_y := encode_var y.
Notation l1 := 0%nat.
Notation l2 := 1%nat.

Definition m1_b1 := Mem.alloc Mem.empty 0 64 8.
Definition m1 := fst m1_b1.
Definition b1 := snd m1_b1.
Definition m2_b2 := Mem.alloc Mem.empty 0 64 8.
Definition m2 := fst m2_b2.
Definition b2 := snd m2_b2.
Definition m3_b3 := Mem.alloc Mem.empty 0 64 8.
Definition m3 := fst m3_b3.
Definition b3 := snd m3_b3.

Open Scope rtype_scope.
Open Scope Z_scope.
Open Scope stdpp_scope.

Definition update_mem_contents (m : Mem.mem) contents :=
  {|
    Mem.mem_contents := contents ;
    Mem.mem_access := Mem.mem_access m ;
    Mem.mem_align := Mem.mem_align m ;
    Mem.nextblock := Mem.nextblock m ;
    Mem.access_max := Mem.access_max m;
    Mem.nextblock_noaccess := Mem.nextblock_noaccess m;
    Mem.only_representable_ofs := Mem.only_representable_ofs m
  |}.

Definition mem_setN bytes b ofs m :=
  update_mem_contents m
    (PXMap.set b (Mem.setN bytes ofs ((Mem.mem_contents m) # b))
       (Mem.mem_contents m)).

Definition pl_state_1 : PL_state :=
  {|
    env := PTree.set enc_x (b1, TInt) (PTree.empty _) ;
    mem := m3
  |}.

Program Definition pl_state_2 : PL_state :=
  {|
    env := PTree.set enc_x (b1, t[ TInt ; TInt] ) (PTree.empty _) ;
    mem := m3
  |}.

Program Definition pl_state_3 : PL_state :=
  {|
    env := PTree.set enc_x (b1, t[ (TRef TInt) ; TInt]) (PTree.empty _) ;
    mem := mem_setN (make_ptr64 (b1, 8) ++ make_int64 0) b1 0 m3
  |}.

(*
  Program Definition pl_state_4 : PL_state :=
    {|
      env := {[ enc_x := (b1, (TRef (TRef TInt))) ]};
      mem :=
        {[
            b1 := make_ptr64 (b2, 8) ;
            b2 := make_int64 3 ++ make_ptr64 (b2, 0)
        ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_5 : PL_state :=
    {|
      env := {[ enc_x := (b1, (TRef (TRef TInt))) ]};
      mem :=
        {[
            b1 := make_ptr64 (b2, 8) ;
            b2 := repeat PL_poison 8 ++ make_ptr64 (b2, 0)
        ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_6 : PL_state :=
    {|
      env :=
        {[
            enc_x := (b1, TPair TInt (TPair TInt TInt))
        ]};
      mem :=
        {[
            b1 := make_int64 0 ++ make_int64 1 ++ make_int64 7
        ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_7 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ]};
      mem := {[ b1 := make_int64 3 ]};
      nextblock := b2
    |}.
  Next Obligation.
    intros. rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_8 : PL_state :=
    {|
      env := {[ enc_x := (b1, TInt) ; enc_y := (b2, TInt) ]};
      mem := {[ b1 := repeat PL_poison 8 ; b2 := repeat PL_poison 8 ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.

  Program Definition pl_state_9 : PL_state :=
    {|
      env := {[ enc_x :=  (b1, TInt) ; enc_y := (b2, TInt) ]};
      mem := {[ b1 := make_int64 3 ; b2 := make_int64 7 ]};
      nextblock := b3
    |}.
  Next Obligation.
    intros. rewrite lookup_insert_ne ; [ | intros <- ; auto ]. 
    rewrite lookup_singleton_None. intros <- ; auto .
  Qed.
 *)

Local Close Scope stdpp_scope.

(** READ AND WRITES TESTS **)
Parameter off_pos : forall (ofs : offset), 0 <= ofs.
Parameter off_mod : forall (ofs : offset), ofs < Ptrofs.modulus.

Goal exists S, write pl_state_1 (x, [], TInt) TInt (make_int64 0) S.
Proof. repeat econstructor. Qed.

Goal exists S, write pl_state_2 (x, [Field(0)], TInt) TInt (make_int64 0) S.
Proof. repeat econstructor. Qed.

Goal exists S, write pl_state_2 (x, [Field(1)], TInt) TInt (make_int64 0) S.
Proof. repeat econstructor. Qed.

Goal read pl_state_3 (x, [Field(0) ; Deref ], TInt) TInt (make_int64 0).
Proof. Abort.

Goal read pl_state_3 (x, [Field(1)], TInt) TInt (make_int64 0).
Proof. repeat econstructor. simpl. rewrite Z.add_0_l. Abort.

(*
  Goal read pl_state_4 (x, [Deref ; Deref]) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal write pl_state_5 (x, [Deref ; Deref]) TInt (make_int64 3) pl_state_4.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  (** EXPRESSION EVALUATION TESTS **)

  Goal pl_state_1 |-{op-pl} IntConst TInt 3 => (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Copy (TPair TInt TInt) (x, []) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{op-pl} Move (TPair TInt TInt) (x, []) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_2 |-{rv-pl} Just (TPair TInt TInt) (Copy (TPair TInt TInt) (x, [])) =>
         (repeat PL_poison 8 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} BinOp TInt (INT 1) (INT 4) => make_int64 (1 + 4).
  Proof. repeat econstructor. Qed.

  Goal pl_state_6 |-{rv-pl} BinOp TInt (Move TInt (x, [Field(Second) ; Field(Second)])) (INT 4) => make_int64 (7 + 4).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} &mut (x, []) : (TRef TInt) => make_ptr64 (b1, 0).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (INT 0) (INT 1)
       => (make_int64 0 ++ make_int64 1).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{rv-pl} Pair (TPair TInt TInt) (IntConst TInt 0) (Move TInt (x, []))
       => (make_int64 0 ++ repeat PL_poison 8).
  Proof. repeat econstructor. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_7.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  Goal pl_state_1 |-{stmt-pl} ASSIGN (x, []) <- Just TInt (INT 3) => rUnit, pl_state_1.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_9.
  Proof. repeat econstructor. apply PL_state_extensionality ; auto. Qed.

  Goal pl_state_8 |-{stmt-pl}
                     ASSIGN (x, []) <- Just TInt (INT 3) ;;
                     ASSIGN (y, []) <- Just TInt (INT 7)
       => rUnit, pl_state_8.
  Proof. repeat econstructor. Fail reflexivity. Abort.

  (** CONCRETIZATION TESTS **)

  Definition addrof := (fun l => if l =? l1 then Some ((b1, 1), TInt) else None).

  Goal concr_hlpl_val addrof (HLPL_int 3) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof (loc (l1, (HLPL_int 3))) TInt (make_int64 3).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof HLPL_bot (TPair TInt TInt) (repeat PL_poison 16).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    HLPL_bot (TPair (TPair TInt TInt) TInt) (repeat PL_poison 24).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair (HLPL_int 3) (HLPL_int 4)) (TPair TInt TInt)
    (make_int64 3 ++ make_int64 4).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair
       (HLPL_int 3)
       (HLPL_pair (HLPL_int 7) (HLPL_int 11)))
    (TPair TInt (TPair TInt TInt))
    (make_int64 3 ++ (make_int64 7 ++ make_int64 11)).
  Proof. repeat econstructor. Qed.

  Goal concr_hlpl_val addrof
    (HLPL_pair
       (HLPL_int 3)
       (HLPL_pair (HLPL_int 7) (HLPL_int 11)))
    (TPair TInt (TPair TInt TInt))
    (make_int64 3 ++ (make_int64 7 ++ make_int64 12)).
  Proof. repeat econstructor. Abort.

  Goal concr_hlpl_val addrof
    (ptr (l1)) (TRef TInt) (make_ptr64 (b1, 1)).
  Proof. repeat econstructor. Qed.
 *)
