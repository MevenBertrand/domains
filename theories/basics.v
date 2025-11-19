(** * Domains.Basics: basic definitions and utilities (such as tactics) *)
From Stdlib Require Import Morphisms CRelationClasses.
From smpl Require Export Smpl.
From HB Require Import structures.
Require Import notations.

(** ** Equalities *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with eq_refl => u end.

(** See above for the meaning of [simpl nomatch]. *)
Arguments transport {A}%_type_scope P%_function_scope {x y} p u : simpl nomatch.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Global Arguments ap {A B}%_type_scope f%_function_scope {x y} p : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression. *)
Notation "p # u" := (transport _ p u) (only parsing).

(** ** Tactics *)

#[global]Hint Unfold notT: core.
#[global] Hint Resolve eq_refl eq_sym : core.

(* To use in intro patterns, similar to SSReflects' /dup view *)
Definition dup {A : Type} : A -> A * A := fun x => (x,x).

Ltac tea := try eassumption.
#[global] Ltac easy ::= solve [eauto 3 with core crelations].

#[global]Obligation Tactic := idtac.
#[global] Ltac Tauto.intuition_solver ::= auto.

(*** A tactic to use extensionality of equality. *)

(** A general refolding tactic to recover lost typeclasses
  (due for instance to the cbn or constructor tactics).
  Updated on the fly using the Smpl plugin. *)
Smpl Create extensionality.

Ltac ext := repeat (intros ; smpl extensionality).

(** * Setoids and equality.

      We use the symbol ≈ to indicate the equality relation on setoids, which,
      thanks to working with observational equality, coincides with the usual
      equality type.
  *)

(** We keep the notations around for now, but they should ultimately disappear. *)
Notation "x ≈ y" := (x = y) (only parsing).
Notation "x ≉ y" := (~(x = y)) (only parsing).


(** *)

HB.mixin Record HasEqDec (T:Type) := {eqdec : forall x y:T, {x = y} + {x <> y} }. 

HB.structure Definition EqTy := {T of HasEqDec T}.