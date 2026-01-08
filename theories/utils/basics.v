(** * Domains.Basics: basic definitions *)
From Stdlib Require Import Morphisms CRelationClasses CMorphisms ssreflect.
From smpl Require Export Smpl.
From HB Require Import structures.
Require Import notations tactics.

(** ** Equalities *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with eq_refl => u end.

Arguments transport {A}%_type_scope P%_function_scope {x y} p u : simpl nomatch.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y
  := match p with eq_refl => eq_refl end.

Global Arguments ap {A B}%_type_scope f%_function_scope {x y} p : simpl nomatch.

(** Transport is very common so it is worth introducing a parsing notation for it.  However, we do not use the notation for output because it hides the fibration, and so makes it very hard to read involved transport expression. *)
Notation "p # u" := (transport _ p u) (only parsing).

Lemma transport_const {A B} {x y : A} {e : x = y} (b : B) :
  transport (fun _ => B) e b = b.
Proof.
  destruct e ; reflexivity.
Qed.

(** ** Setoids and equality.

      We use the symbol ≈ to indicate the equality relation on setoids, which,
      thanks to working with observational equality, coincides with the usual
      equality type.
  *)

(** We keep the notations around for now, but they should ultimately disappear. *)
Notation "x ≈ y" := (x = y) (only parsing).
Notation "x ≉ y" := (~(x = y)) (only parsing).

(** ** Lemmas for working with [iffT] *)
Lemma arrowTE: CMorphisms.Proper (iffT ==> iffT ==> iffT) arrow.
Proof. move=>A A' e B B' f; split; move=>p a; apply f, p, e, a. Defined.

Definition allT {A} (f: A -> Type) := forall a, f a.
Definition pointwise_crelation {A B} (R: crelation B): crelation (A -> B) := fun f g => forall a, R (f a) (g a).
Lemma allTE {A}: CMorphisms.Proper (@pointwise_crelation A _ iffT ==> iffT) allT.
Proof. move=>f g fg; split; move=>Hf x; apply fg, Hf. Defined.
Lemma allTE' {A B} (f: A -> Type) (g: B -> Type):
  iffT A B -> (forall a b, iffT (f a) (g b)) -> iffT (allT f) (allT g).
Proof. move=>ab fg; split; move=>H x; unshelve eapply fg, H; apply ab, x. Qed.

Lemma sigTE {A}: CMorphisms.Proper (pointwise_crelation iffT ==> iffT) (@sigT A).
Proof. move=>f g fg; split; move=>[x H]; exists x; apply fg, H. Defined.
Lemma sigTE' {A B} (f: A -> Type) (g: B -> Type):
  iffT A B -> (forall a b, iffT (f a) (g b)) -> iffT (sigT f) (sigT g).
Proof. move=>ab fg; split; move=>[x H]; (unshelve eexists; [apply ab, x|eapply fg, H]). Qed.

Lemma iffT_hyp {A A' B}: (iffT A A') -> (A' -> B) -> A -> B.
Proof. move=>[+ _]; auto. Qed.

(** ** Unique existence *)

(** unique existence, in Prop *)
Definition unique [A : Type] (P : A -> Prop) : A -> Prop :=
  fun (x : A) => P x /\ (forall x' : A, P x' -> x' = x).

Notation "∃! x .. y , P" :=
  (ex (unique (fun x => .. (ex (unique (fun y => P))) ..)))
  (at level 200, x binder, right associativity).

Notation "Σ! x .. y , P" := (sig (unique (fun x => .. (sig (unique (fun y => P))) ..)))
  (at level 200, x binder, y binder, right associativity).

Definition unique_elt {A} {P : A -> Prop} (s : Σ! x : A, P x) : A := proj1_sig s.
Definition unique_prop {A} {P : A -> Prop} (s : Σ! x : A, P x) : P (unique_elt s) :=
  proj1 (proj2_sig s).
Definition unique_unique {A} {P : A -> Prop} (s : Σ! x : A, P x) :
  forall x : A, P x -> x = (unique_elt s) :=
  proj2 (proj2_sig s).

Lemma unique_unique_impl {T : Type} (P Q: T -> Prop) :
  (forall x, P x -> Q x) ->
  forall (p: Σ! x, (P x)), forall (q: Σ! x, (Q x)), unique_elt p = unique_elt q.
Proof.
  move=>PQ p q. apply unique_unique, PQ, unique_prop.
Qed.

(** ** Decidable predicates *)

Class Decision (P : Prop) := decide : {P} + {~P}.
Global Hint Mode Decision ! : typeclass_instances.
Global Arguments decide _ {_} : simpl never, assert.

(** Decidable equality *)

HB.mixin Record HasEqDec (T:Type) := {eqdec : forall x y:T, Decision (x = y) }. 

HB.structure Definition EqTy := {T of HasEqDec T}.

(** Option *)

Definition onSome {A} (P : A -> Prop) (x : option A) : Prop :=
  match x with
  | None => False
  | Some x => P x
  end.

Arguments onSome {_}_ !_/.