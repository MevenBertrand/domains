(** * Domains.Basics: basic definitions and utilities (such as tactics) *)
From Stdlib Require Import Morphisms CRelationClasses CMorphisms ssreflect.
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

(** *** A tactic to use extensionality of equality. *)

(** A general refolding tactic to recover lost typeclasses
  (due for instance to the cbn or constructor tactics).
  Updated on the fly using the Smpl plugin. *)
Smpl Create extensionality.

Ltac ext := repeat (intros ; smpl extensionality ; intros).

(** * Setoids and equality.

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
  fun (x : A) => P x /\ (forall x' : A, P x' -> x = x').

Notation "∃! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity).

(** unique existence, in Type *)
Record Unique [T: Type] (P : T -> Type) := {
    unique_elt: T;
    unique_prop: P unique_elt;
    uniqueness: forall x : T, P x -> unique_elt = x;
  }.
Arguments unique_elt {_ _}.
Arguments unique_prop {_ _}.
Arguments uniqueness {_ _}.

Notation "Σ! x .. y , P" := (Unique (fun x => .. (Unique (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Lemma unique_unique {T : Type} (P Q: T -> Type) :
  (forall x, P x -> Q x) ->
  forall (p: Σ! x, (P x)), forall (q: Σ! x, (Q x)), unique_elt p = unique_elt q.
Proof.
  move=>PQ p q. symmetry. apply uniqueness, PQ, unique_prop.
Qed.

Lemma Unique_iff {T : Type} : CMorphisms.Proper (pointwise_crelation iffT ==> iffT) (@Unique T).
Proof.
  move=> P Q PQ. split; move=>[f Hf Uf]; exists f; (try by apply PQ);
  move=>g Hg; apply Uf; by apply PQ.
Qed.

(** Decidable equality *)

HB.mixin Record HasEqDec (T:Type) := {eqdec : forall x y:T, {x = y} + {x <> y} }. 

HB.structure Definition EqTy := {T of HasEqDec T}.