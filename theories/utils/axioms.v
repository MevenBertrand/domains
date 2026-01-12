(** * Domains.Axioms: Axioms for the development *)

Require Import basics tactics ssreflect ssrfun.

(** R. Donkins' original development was all done using explicit setoids, incurring a
  high complexity overhead. We take a different approach to setoids, which is to use them
  implicitly by working with (a mock-up) observational equality, which gives us
  an internal language for setoids. This is achieved by importing a number of
  axioms below. *)

(** ** Propositional extensionality *)
From Stdlib Require Export PropExtensionalityFacts.

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

Export PropExtProofIrr.

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

From Stdlib Require Import Relations.Relation_Definitions Classes.RelationClasses Classes.Morphisms.

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
Axiom quot_rect : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t)),
  (forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y)) ->
  forall u : quot R, P u.

(** Propositional computation rule *)
Axiom quot_rect_eq : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Type)
  (f : forall (t : T), P (to_quot t))
  (r : forall (x y :T) (e : R x y), (quot_ext _ _ e) # (f x) = f y :> P (to_quot y))
  (x : T),
  quot_rect P f r (to_quot x) = f x.

(** *** Quotient derived functions *)

Program Definition quot_rec {T : Type} {R : relation T} `{! Equivalence R} {P : Type}
  (f : T -> P)
  `{p : Proper _ (R ==> eq)%signature f} :
  quot R -> P :=
  quot_rect (fun _ => P) f _.
Next Obligation.
  intros.
  now rewrite transport_const.
Qed.

Lemma quot_rec_eq {T : Type} {R : relation T} `{! Equivalence R} {P : Type}
  (f : T -> P)
  `{! Proper (R ==> eq) f}
  (t : T) : quot_rec f (to_quot t) = f t.
Proof.
  by rewrite /quot_rec quot_rect_eq.
Qed.

Lemma quot_ind : forall {T : Type} {R : relation T} `{! Equivalence R},
  forall (P : quot R -> Prop)
  (f : forall (t : T), P (to_quot t)),
  forall u : quot R, P u.
Proof.
  intros.
  unshelve eapply quot_rect.
  1: assumption.
  intros.
  ext.
Qed.

Instance to_quot_proper
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f} :
  Proper (RA ==> eq) (to_quot \o f).
Proof.
  intros x y h.
  by apply quot_ext, e.
Qed.

Definition quot_map
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f}
  : quot RA -> quot RB :=
  quot_rec (to_quot \o f).

Lemma quot_map_eq
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  (f : A -> B)
  `{e : Proper _ (RA ==> RB) f}
  (a : A)
  : quot_map f (to_quot a) = to_quot (f a).
Proof.
  by rewrite /quot_map quot_rec_eq.
Qed.

From Stdlib Require Import RelationPairs Morphisms.

Instance PER_Equivalence {A} {RA : relation A} `{! PER RA} :
  @Equivalence {a : A | Proper RA a} (RA @@ sval).
Proof.
  rewrite /RelCompFun /Proper.
  split ; red.
  - apply proj2_sig.
  - intros.
    now symmetry.
  - intros.
    now etransitivity.
Qed.

Existing Instance respectful_per.

Program Definition quot_map2
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  {C : Type} {RC : relation C} `{! Equivalence RC}
  (f : A -> B -> C)
  `{e : Proper _ (RA ==> RB ==> RC) f}
  (a : quot RA) (b : quot RB) : quot RC :=
  quot_rec (fun a' => quot_rec (fun b' => to_quot (f a' b')) (p := _) b)
    (p := _) a.
Next Obligation.
  intros.
  rewrite /Proper /respectful.
  intros.
  now apply quot_ext, e.
Qed.
Next Obligation.
  intros.
  rewrite /Proper /respectful.
  intros.
  pattern b ; apply quot_ind ; intros b'.
  rewrite !quot_rec_eq.
  now apply quot_ext, e.
Qed.

Lemma quot_map2_eq
  {A : Type} {RA : relation A} `{! Equivalence RA}
  {B : Type} {RB : relation B} `{! Equivalence RB}
  {C : Type} {RC : relation C} `{! Equivalence RC}
  (f : A -> B -> C)
  `{e : Proper _ (RA ==> RB ==> RC) f}
  : forall a b, quot_map2 f (to_quot a) (to_quot b) = to_quot (f a b).
Proof.
  intros.
  unfold quot_map2.
  now rewrite !quot_rec_eq.
Qed.

(** ** Decisions *)

(** Extensionality *)
Lemma sumbool_excluded_ext (P Q : Prop) (p p' : {P} + {Q}) : ~ (P /\ Q) -> p = p'.
Proof.
  intros ?.
  destruct p, p'.
  all: try solve [exfalso ; intuition].
  all: f_equal ; ext.
Qed.

Lemma decision_ext P (p p' : Decision P) : p = p'.
Proof.
  apply sumbool_excluded_ext.
  intuition.
Qed.

Smpl Add (apply decision_ext) : extensionality.

(** Special recursions *)
Definition quot_rect_sumbool {T : Type} {R : relation T} `{! Equivalence R} {P Q : quot R -> Prop}
  (f : forall t : T, {P (to_quot t)} + {Q (to_quot t)})
  (e : forall x, ~ (P (to_quot x) /\ Q (to_quot x))) :
  forall u : quot R, {P u} + {Q u}.
Proof.
  eapply (quot_rect _ f).
  intros.
  now apply sumbool_excluded_ext.
Qed.

Definition quot_rect_dec {T : Type} {R : relation T} `{! Equivalence R} {P : quot R -> Prop}
  (f : forall t : T, Decision (P (to_quot t))) :
  forall u : quot R, Decision (P u).
Proof.
  apply quot_rect_sumbool ; tea.
  intuition.
Qed.