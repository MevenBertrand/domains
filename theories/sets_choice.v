(** * domains.sets_choice: exploring choice-like properties of our sets *)
From Stdlib Require Import Arith Arith.Cantor ssreflect ssrfun List
  Relations Classes.RelationClasses Classes.Morphisms Lia.
From HB Require Import structures.

Require Import utils.all nat_isos categories.all preord sets finsets esets.

Instance True_Equiv A : Equivalence (fun (_ _ : A) => True).
Proof.
  do 2 constructor.
Qed.

Definition Squash (A : Type) : Type := quot (fun (_ _ : A) => True).
Definition squash {A} : A -> Squash A := to_quot.

Notation "∥ A ∥" := (Squash A) (at level 10).
Notation "| a |" := (squash _ a) (at level 10).

Lemma unique_choice {A} :
  (forall x y : A, x = y) -> 
  ∥ A ∥ -> A.
Proof.
  intros e.
  unshelve eapply (quot_rec (fun x => x)).
  cbv ; eauto.
Qed.

Lemma squash_ext A (x y : ∥ A ∥) : x = y.
Proof.
  destruct x using quot_ind.
  destruct y using quot_ind.
  now ext.
Qed.

Smpl Add (apply squash_ext) : extensionality.

(**  * Countable indefinite description

    A version of the principle of indefinite description can be proved for
    enumerable sets. However, in order to enforce the quotient we have to restrict
    to merely obtaining an element of the squash. If we know this element is uniquely
    specified, we will however be able to upgrade this to a proper element.

  *)
Section CountableID.
  Context {A:Type}.

  (** Here we define inhabitedness of an enumerable set as an inductive
      predicate with a single constructor.  This enables us to define
      a constructive choice function on inhabited enumerable sets.
    *)
  Inductive inhabited_ind (P : nat -> option A) : Prop :=
    | inhS : ((P 0 = None) -> inhabited_ind (P \o S)) -> inhabited_ind P.

  Lemma inhabited_indP P : inhabited_ind P <-> (exists a, fun_member a P).
  Proof.
    split.
    - rewrite /fun_member.
      intros Hin.
      induction Hin as [? ? IHHin].
      destruct (P 0) eqn: e.
      1: now do 2 eexists.
      destruct IHHin as (?&?&?) ; [easy|].
      now do 2 eexists.
    - intros [a [n H]].
      induction n in P, H |- * ; econstructor ; solve [congruence|eauto].
  Qed.

  Instance Proper_inh : Proper (funset_ext A ==> eq) inhabited_ind.
  Proof.
    intros ?? e.
    ext.
    rewrite !inhabited_indP.
    rewrite /funset_ext in e.
    now setoid_rewrite e.
  Qed.

  Definition einhabited : eset A -> Prop :=
    quot_rec inhabited_ind.

  Lemma einhabitedP P : einhabited P <-> (exists a, a ∈ P).
  Proof.
    induction P using quot_ind.
    rewrite /einhabited quot_rec_eq inhabited_indP.
    setoid_rewrite esetP.
    reflexivity.
  Qed.

  (**  [find_inhabitant] is defined by recursion on the [einhabited] fact,
       and it finds the smallest index in the set [P] that is defined.
    *)
  Definition find_inhabitant P (H: inhabited_ind P) :
    { a:A & { n | P n = Some a /\
      forall n' a', P n' = Some a' -> (n <= n')} }.
  Proof.
    induction H as [? ? IH].
    destruct (P 0) as [a|] eqn:e.
    - exists a, 0 ; intuition lia.
    - destruct IH as (a&n&[Hsome Hle]); [easy|].
      exists a, (S n).
      split ; [easy|].
      intros ?? Hn'.
      destruct n'.
      1: congruence.
      specialize (Hle _ _ Hn').
      lia.
  Qed.

  Definition choose_fun P (H : inhabited_ind P) : A
    := projT1 (find_inhabitant P H).

  Lemma choose_funP P H : fun_member (choose_fun P H) P.
  Proof.
    intros.
    unfold choose_fun.
    destruct find_inhabitant as (?&?&[]); auto.
    cbn.
    now eexists.
  Qed.

  Definition choose (P : eset A) : einhabited P -> ∥ {x : A | x ∈ P} ∥.
  Proof.
    pattern P.
    unshelve eapply (quot_rect _ _ _ P).
    - clear P.
      intros P ; cbn.
      rewrite /einhabited quot_rec_eq.
      intros H.
      apply to_quot.
      exists (choose_fun P H).
      rewrite esetP.
      apply choose_funP.
    - cbn.
      ext.
  Qed.

  Lemma inhabited_einhabited (P : eset A) : color_prop inhabited P <-> einhabited P.
  Proof.
    cbn.
    rewrite einhabitedP.
    reflexivity.
  Qed.
End CountableID.

Theorem countable_indefinite_description {A:Type} (X:eset A) :
  (exists x:A, x ∈ X) -> ∥ { x:A | x ∈ X } ∥.
Proof.
  intros.
  apply choose, inhabited_einhabited.
  assumption.
Qed.

Theorem countable_definite_description {A:Type} (X:eset A) :
  (exists x:A, x ∈ X) ->
  (forall x y, x ∈ X -> y ∈ X -> x = y) ->
  { x:A | x ∈ X }.
Proof.
  intros ? Hunique.
  apply unique_choice.
  2: now apply countable_indefinite_description.
  intros [x] [y].
  enough (x = y) as -> by ext.
  now apply Hunique.
Qed.

(** * Weak countable choice 

     Countable indefinite description gives rise to a functional choice principle:
       "Every total enumerable relation gives rise to a (computable) function."

     There are two subtle points regarding the formal statemet: first,
     we need need to assume a decidable order on A;
     second, the choice function is _constructed_
     not just asserted to exist.

     This statement is weaker than the "standard" version of countable choice.
     In countable choice, the domain [A] is assumed to be countable,
     but the cardinality of the relation [R] is unconstrained.

     Here, we instead require [R] to be enumerable and [A] to have a decidable
     order.  Because [R] is total, this implies [A] is countable (and
     effective, as defined in "effective.v.")  Hence this statement is
     implied by countable choice (more precisely, a statement of countable choice
     that constructs a function, rather than merely asserting it to exist).
     This statement is _strictly_ weaker, as the usual version of
     countable choice is not provable in Coq.
  *)

Theorem weak_countable_choice {A : EqTy} {B : Type} (R:erel A B) :
  (forall a : A, ∃! (b : B), (a,b) ∈ R) ->
  { f:A -> B | forall a, (a, f a) ∈ R }.
Proof.
  intros.
  unshelve econstructor.
  - intros x.
    refine (projT1 (countable_definite_description (erel_image R x) _ _)).
    + setoid_rewrite erel_imageP.
      edestruct H ; unfold unique in *.
      now eexists.
    + setoid_rewrite erel_imageP.
      intros.
      eapply unique_exists_unique.
      1: apply H.
      all: cbn ; eauto.
  - intros ; cbn.
    destruct (countable_definite_description _) as [b Hb]; cbn in *.
    rewrite eimageP in Hb.
    destruct Hb as ([]&[Hb]) ; subst.
    rewrite esubset_decP in Hb.
    destruct Hb as [? ->].
    now cbn in *.
Qed.