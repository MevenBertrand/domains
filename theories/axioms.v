(** * Domains.Axioms: Axioms for the development *)

Require Import basics.

(** R. Donkins' original development was all done using explicit setoids, incurring a
  high complexity overhead. We take a different approach to setoids, which is to use them
  implicitly by working with (a mock-up) observational equality, which gives us
  an internal language for setoids. This is achieved by importing a number of
  axioms below. *)

(** ** Propositional extensionality *)
From Stdlib Require Import PropExtensionalityFacts.

Axiom prop_ext : forall {P Q : Prop}, P <-> Q -> P = Q.

Smpl Add 50 (apply prop_ext) : extensionality.

(** ** Proof irrelevance *)
(** Ideally, we'd be using SProp here instead, but for the time being this shall be
  good enough. *)
From Stdlib Require Export ProofIrrelevanceFacts.

(** Propositional proof irrelevance is a consequence of propositional extensionality,
  so we do not need to postulate it explicitly. *)

Module PropExtProofIrr : ProofIrrelevance.

  Definition proof_irrelevance {P:Prop} (p q : P) : p = q.
  Proof.
    assert (P = True) as e.
    {
      apply prop_ext.
      now split.
    }
    revert p q.
    subst P.
    now intros [] [].
  Qed.

End PropExtProofIrr.

Import PropExtProofIrr.

Smpl Add (apply proof_irrelevance) : extensionality.

(** ** Function extensionality *)
(** Corresponds to the definition of function setoids. *)
From Stdlib Require Export FunctionalExtensionality.

Smpl Add 200 (apply functional_extensionality_dep) : extensionality.

Corollary pred_ext: forall {A} (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q.
Proof.
  intros.
  now ext.
Qed.


(* Print functional_extensionality_dep. *)

(** ** Quotients *)

From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses.

(** The quotient type *)
Axiom quot : forall {T : Type} (R : relation T) `{! Equivalence R}, Type.

(** The quotient element constructor *)
Axiom to_quot : forall {T : Type} {R : relation T} `{! Equivalence R}, T -> quot R.

(** The quotient path constructor *)
Axiom quot_ext : forall {T : Type} {R : relation T} `{! Equivalence R} (t t' : T),
  R t t' -> to_quot t = to_quot t'.

(** Quotient effectivity axiom*)
Axiom quot_eq : forall {T : Type} {R : relation T} `{! Equivalence R} (t t' : T),
  to_quot t = to_quot t' -> R t t'.

(** Induction for quotients *)
Axiom quot_ind : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t)),
  (forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y)) ->
  forall u : quot R, P u.

(** Propositional computation rule *)
Axiom quot_ind_eq : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t))
  (r : forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y))
  (x : T),
  quot_ind P f r (to_quot x) = f x.