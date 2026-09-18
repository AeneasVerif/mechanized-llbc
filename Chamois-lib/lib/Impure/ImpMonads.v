(** Impure monad for interface with impure code
*)


Module Type MayReturnMonad.

  (** The type of impure computations *)
  Axiom t: Type -> Type.

  (** The may-return relation *)
  Axiom mayRet: forall {A:Type}, t A -> A -> Prop.

  (** Standard monad operator: lift pure computation *)
  Axiom ret: forall {A}, A -> t A.

  (** Standard monad operator: bind two impure computations *)
  Axiom bind: forall {A B}, (t A) -> (A -> t B) -> t B.

  (** Axioms of monad operators wrt to may-return monad *)
  Axiom mayRet_ret: forall A (a b:A), 
     mayRet (ret a) b -> a=b.

  Axiom mayRet_bind: forall A B k1 k2 (b:B),
     mayRet (bind k1 k2) b -> exists a:A, mayRet k1 a /\ mayRet (k2 a) b.

  (** Operator to annotate returned types with may-return relation.
      This overcomes the non-dependent [bind] application within dependent types. 
  *)
  Axiom mk_annot: forall {A} (k: t A), t { a: A | mayRet k a }.

  (** Exiting the monad for observationally deterministic computations (within partial correctness) *)
  Axiom det_coerce: forall {A} (k: t A) (v: unit -> A) (DET: forall r, mayRet k r -> r = v tt), A.

  Axiom det_coerce_correct: forall A (k: t A) v (DET: forall r, mayRet k r -> r = v tt), (det_coerce k v DET)=(v tt).

  (** Exiting the monad on termination *)
  Axiom has_returned: forall {A}, t A -> bool.

  Axiom has_returned_correct: forall A (k: t A),
     has_returned k = true -> exists r, mayRet k r.

End MayReturnMonad.



(** Model of impure computation as predicate *)
Module PowerSetMonad<: MayReturnMonad.

   Definition t (A:Type) := A -> Prop.

   Definition mayRet {A:Type} (k: t A) a: Prop := k a.

   Definition ret {A:Type} (a:A) := eq a.

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) := 
     fun b => exists a, k1 a /\ k2 a b.

   Definition mk_annot {A} (k: t A) : t { a | mayRet k a } := fun _ => True.

   Lemma mayRet_ret A (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     unfold mayRet, ret. firstorder.
   Qed.

   Lemma mayRet_bind A B k1 k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     unfold mayRet, bind. 
     firstorder.
   Qed.
  
   (* exiting the monad: "logical" models *)

   Definition det_coerce {A} (k: t A) (v: unit -> A) (DET: forall r, mayRet k r -> r = v tt) := v tt.

   Lemma det_coerce_correct: forall A (k: t A) v (DET: forall r, mayRet k r -> r = v tt), det_coerce k v DET = v tt.
   Proof.
     unfold det_coerce; auto.
   Qed.

   Definition has_returned {A} (k:t A) := false.

   Lemma has_returned_correct: forall A (k: t A),
     has_returned k = true -> exists r, mayRet k r.
   Proof.
     unfold has_returned; congruence.
   Qed.

End PowerSetMonad.



(** The identity interpretation *)
Module IdentityMonad<: MayReturnMonad.

   Definition t (A:Type) := A.

   (* may-return semantics of computations *)
   Definition mayRet {A:Type} (a b:A): Prop := a=b.

   Definition ret {A:Type} (a:A) := a.

   Definition bind {A B:Type} (k1: A) (k2: A -> B) := k2 k1.

   Definition mk_annot {A} (k: t A) : t { a: A | mayRet k a } 
    := exist _ k (eq_refl k) .

   Lemma mayRet_ret (A:Type) (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     intuition.
   Qed.

   Lemma mayRet_bind (A B:Type) (k1:t A) k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     firstorder.
   Qed.

   (* exiting the monad: "computational" models *)
   Definition det_coerce {A} (k: t A) (v: unit -> A) (DET: forall r, mayRet k r -> r = v tt) := k.

   Lemma det_coerce_correct A (k: t A) v (DET: forall r, mayRet k r -> r = v tt): det_coerce k v DET = v tt.
   Proof.
     eapply (DET k); refine (eq_refl _).
     (* Very strange: in coq 8.16.1, "apply eq_refl" instead of "refine ..." generates a too strong universe constraint
        that may later come problematic !
     *)
   Qed.

   Definition has_returned {A} (k:t A) := true.

   Lemma has_returned_correct: forall A (k: t A),
     has_returned k = true -> exists r, mayRet k r.
   Proof.
     unfold has_returned, mayRet; eauto.
   Qed.

End IdentityMonad.


Require Program.

(** Model of impure computation as state-transformers (with error-raising) *)
Module StateOptionMonad<: MayReturnMonad.
 
   Parameter St: Type. (* A global state *)

   Definition t (A:Type) := St -> (option A) * St.

   Definition mayRet {A:Type} (k: t A) a: Prop :=
     exists s, fst (k s)=Some a.

   Definition ret {A:Type} (a:A) := fun (s:St) => (Some a,s).

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) := 
     fun s0 => 
      let r := k1 s0 in 
      match fst r with
      | Some a => k2 a (snd r)
      | None => (None, snd r)
      end.

   Program Definition mk_annot {A} (k: t A) : t { a | mayRet k a } := 
     fun s0 =>
     let r := k s0 in 
     match fst r with
     | Some a => (Some (exist _ a _), snd r)
     | None => (None, snd r)
     end.
   Obligation 1.
     unfold mayRet; eauto.
   Qed.

   Lemma mayRet_ret {A:Type} (a b:A): mayRet (ret a) b -> a=b.
   Proof.
     unfold mayRet, ret; simpl. firstorder congruence.
   Qed.

   Lemma mayRet_bind {A B:Type} k1 k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     unfold mayRet, bind.
     intros (s & H); destruct (fst (k1 s)) eqn: H1; firstorder eauto.
     simpl in *; congruence.
   Qed.

   (* exiting the monad: "computational" models *)
   Parameter st: St. (* the global state is not empty! *)

   Definition det_coerce {A} (k: t A) (v: unit -> A) (DET: forall r, mayRet k r -> r = v tt): A 
    := match fst (k st) with
       | Some a => a
       | None => v tt
       end.

   Lemma det_coerce_correct: forall A (k: t A) v (DET: forall r, mayRet k r -> r = v tt), det_coerce k v DET = v tt.
   Proof.
     unfold det_coerce, mayRet; intros A k v DET.
     destruct (fst (k st)) eqn: H1; simpl; eauto.
   Qed.

   Definition has_returned {A} (k:t A) 
   := match fst (k st) with
      | Some _ => true
      | None => false
      end.

   Lemma has_returned_correct: forall A (k: t A),
     has_returned k = true -> exists r, mayRet k r.
   Proof.
     unfold has_returned, mayRet; intros A k H.
     destruct (fst (k st)) eqn: H1; simpl; eauto.
     congruence.
   Qed.

End StateOptionMonad.



(** The deferred interpretation *)
Module DeferredMonad<: MayReturnMonad.

   Definition t (A:Type) := unit -> A.

   (* may-return semantics of computations *)
   Definition mayRet {A:Type} (a: t A) (b:A): Prop := a tt=b.

   Definition ret {A:Type} (a:A) : t A := fun _ => a.

   Definition bind {A B:Type} (k1: t A) (k2: A -> t B) : t B := fun _ => k2 (k1 tt) tt.

   Definition mk_annot {A} (k: t A) : t { a: A | mayRet k a } 
    := fun _ => exist _ (k tt) (eq_refl (k tt)).

   Lemma mayRet_ret (A:Type) (a b: A): mayRet (ret a) b -> a=b.
   Proof.
     intuition.
   Qed.

   Lemma mayRet_bind (A B:Type) (k1:t A) k2 (b:B):
         mayRet (bind k1 k2) b -> exists (a:A), mayRet k1 a /\ mayRet (k2 a) b.
   Proof.
     firstorder.
   Qed.

   (* exiting the monad: "computational" models *)

   Definition det_coerce {A} (k: t A) (v: unit -> A) (DET: forall r, mayRet k r -> r = v tt) := k tt.

   Lemma det_coerce_correct: forall A (k: t A) v (DET: forall r, mayRet k r -> r = v tt), det_coerce k v DET = v tt.
   Proof.
     unfold det_coerce, mayRet; intros A k v DET; eapply DET. apply eq_refl.
   Qed.

   Definition has_returned {A} (k:t A) := true.

   Lemma has_returned_correct: forall A (k: t A),
     has_returned k = true -> exists r, mayRet k r.
   Proof.
     unfold has_returned, mayRet; eauto.
   Qed.

End DeferredMonad.