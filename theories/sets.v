(** * domains.sets: An abstract notion of "set theory" *)
From Stdlib Require Import Relations List Program ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories.all preord.

Declare Scope set_scope.
Delimit Scope set_scope with set.
#[global]Open Scope set_scope.

(**  ** Set theory.

       Here we define a notion of "set theory" that is sufficent
       for our purposes.  Note that the set theories we define
       are significantly weaker than the set theories used for
       foundational mathematics (say, ZF).  

       First, our sets are typed: a "set theory" defines an operator
       [set] that sents preorders to preorders.  In addition to the
       membership predicate, the only operations we stipulate must
       exist are the operation to form singleton sets, the union
       operation, and the operation to take the image of a monotone
       function.

       Two particular notions of "set theory" we are interested in
       are the finite sets and the enumerable (countable) sets.
       We'll also be interested in the notion of directed sets,
       which play an important role in the deveopment of domain theory.
       Directeness is abstracted into a notion of "colored" sets, which
       unifies several closely related definitions.

       Note that the operations we require are precicely what is
       required for "set" to be a monad in the category of preorders.
       This, as it happens, is an unanticipated coincidence!  Perhaps
       there is some deeper meaning implied by this coincidence, but I
       have yet to discover it.
  *)

#[primitive] HB.mixin Record IsBaseSetTheory (set : PreOrder -> Poset) := {
  member {A : PreOrder} : A -> set A -> Prop ;
  #[canonical=no]_set_leP T (X Y : set T) : X ≤ Y <-> (forall t, member t X -> member t Y) ;
  }.

#[short(type="BaseSetTheory"),primitive]
HB.structure Definition basesettheory :=
  { set & IsBaseSetTheory set }.

Arguments member {set _} : simpl never, rename.
Notation "x ∈ X" := (member x (X)%set) : set_scope.
Notation "x ∉ X"  := (not (member x (X)%set)) : set_scope.

Lemma set_leP {set : BaseSetTheory} (A : PreOrder) (X Y : set A) :
  X ≤ Y <-> (forall t : A, t ∈ X -> t ∈ Y).
Proof.
  apply _set_leP.
Qed.

Lemma set_ext (set : BaseSetTheory)
(A : PreOrder) (X Y : set A) :
  (forall t : A, t ∈ X <-> t ∈ Y) -> X = Y.
Proof.
  intros * H.
  apply ord_antisym.
  all: apply set_leP, H.
Qed.

Smpl Add (apply: set_ext) : extensionality.


(** *** Set quantifiers *)

Definition set_ex {set : BaseSetTheory} {A : PreOrder} (P : A -> Prop) (X : set A) :=
  exists x, x ∈ X /\ P x.

Notation "∃ x ∈ M , P" := (set_ex (fun x => P) M)
  (at level 10, x binder, M at level 200, P at level 200) : type_scope.

Definition set_all {set : BaseSetTheory} {A : PreOrder} (P : A -> Prop) (X : set A) :=
  forall x, x ∈ X -> P x.

Notation "∀ x ∈ M , P" := (set_all (fun x => P) M)
  (at level 10, x binder, M at level 200, P at level 200) : type_scope.

(** *** Inclusion *)

Definition incl {set set' : BaseSetTheory} {A : PreOrder} (X : set A) (Y : set' A) :=
  ∀ a ∈ X, a ∈ Y.

Notation "X ⊆ Y" := (incl (X)%set (Y)%set) : set_scope.

Lemma le_incl {set : BaseSetTheory} {A : PreOrder} (X Y : set A) : X ≤ Y <-> X ⊆ Y.
Proof.
  by rewrite set_leP /incl.
Qed.

Instance incl_PreOrd {set : BaseSetTheory} (A : PreOrder) :
  RelationClasses.PreOrder (A := set A) incl.
Proof.
  split.
  all: red ; cbn.
  all: now rewrite /incl /set_all.
Qed.

(** We can always build a "canonical" set theory by using inclusion as the preorder *)

Definition IsExtMem
  (set : PreOrder -> Type)
  (pmember : forall {A : PreOrder}, A -> set A -> Prop) : Prop := 
  forall T (X Y : set T), (forall t, pmember t X <-> pmember t Y) -> X = Y.

Program Definition promote_set
  (set : PreOrder -> Type)
  (pmember : forall {A : PreOrder}, A -> set A -> Prop)
  : IsExtMem set (@pmember) -> (PreOrder -> Poset) :=
  fun Hset A =>
  {| poset.sort := (set A) |}.
Next Obligation.
  unshelve econstructor.
  all: unshelve econstructor.
  - exact (fun X Y => forall a, pmember _ a X -> pmember _ a Y).
  - intros ? ; red ; cbn.
    intuition.
  - intros ??? H H'.
    red in H, H' |- * ; cbn in *.
    intuition.
  - intros ?? H H'.
    red in H, H' ; cbn in *.
    apply Hset.
    intuition.
Defined.

Program Definition SetIncl
  (set : PreOrder -> Type)
  (pmember : forall {A : PreOrder}, A -> set A -> Prop)
  (H : IsExtMem set (@pmember)) :=
  IsBaseSetTheory.Build (promote_set set (@pmember) H) (@pmember) ltac:(reflexivity).

#[global]Opaque promote_set_obligation_1.

#[primitive] HB.mixin Record IsPreSetTheory set of basesettheory set := {
  (* empty (A : Type) : set A ; *)
  single {A : PreOrder} : A -> set A ;
  image {A B : PreOrder} (f : A ⤳ B) : set A -> set B ;
  union {A : PreOrder} : set (set A) -> set A ;
  }.

#[short(type="PreSetTheory"),primitive]
HB.structure Definition presettheory :=
  { set of basesettheory set & IsPreSetTheory set }.

(* Arguments empty {set _} : rename. *)
Arguments single {set _} : rename, simpl never.
Arguments image {set _ _} : rename, simpl never.
Arguments union {set _} : rename, simpl never.

(* Notation "∅" := (empty) : set_scope. *)
Notation "∪ XS" := (union (XS)%set) : set_scope.

#[primitive] HB.mixin Record IsSetTheory set of presettheory set :=
  {
    (* emptyP T (x : T) : (x ∈ empty (set := set)) <-> False ; *)
    singleP (T : PreOrder) (a b : T) : (a ∈ single (set := set) b) <-> a = b ;
    imageP (A B : PreOrder) (f : A ⤳ B) (P : (set A)) (y : B) :
      y ∈ (image f P) <-> exists x, x ∈ P /\ y = f x ;
    unionP (T : PreOrder) (xs : set (set T)) (a : T) :
      a ∈ (∪ xs) <-> exists x : (set T), x ∈ xs /\ a ∈ x
  }.

#[short(type="SetTheory"),primitive]
HB.structure Definition settheory :=
  { set of basesettheory set & IsPreSetTheory set & IsSetTheory set}.

Lemma image_compose (set : SetTheory) (A B C : PreOrder) (f:A ⤳ B) (g:B ⤳ C) (X: set A) :
  image (g ∘ f) X = image g (image f X).
Proof.
  ext.
  rewrite !imageP.
  split.
  - intros (x&[Hx ->]).
    exists (f x).
    split => //.
    rewrite imageP.
    exists x.
    now split.
  - intros (?&[(x&[? ->])%imageP ->]).
    now exists x ; split.
Qed.

Lemma image_fun {set : SetTheory} {A B : PreOrder} (f:A ⤳ B) (X: set A) :
  ∀ x ∈ X, f x ∈ image f X.
Proof.
  intros ??.
  now rewrite !imageP.
Qed.

Lemma image_all {set : SetTheory} {A B : PreOrder} {P : B -> Prop} (f:A ⤳ B) (X: set A) :
  (∀ x ∈ image f X, P x) <-> ∀ x ∈ X, P (f x).
Proof.
  rewrite /set_all.
  setoid_rewrite imageP.
  intuition eauto.
  now destruct H0 as (?&?&->).
Qed.

Lemma image_ex {set : SetTheory} {A B : PreOrder} {P : B -> Prop} (f:A ⤳ B) (X: set A) :
  (∃ x ∈ image f X, P x) <-> ∃ x ∈ X, P (f x).
Proof.
  rewrite /set_ex.
  setoid_rewrite imageP.
  split.
  - intros (?&(?&?&->)&?).
    now eexists. 
  - intros (?&?&?).
    repeat (eexists ; tea).
Qed.

Lemma single_incl {set set' : SetTheory} {A : PreOrder} (a : A) (X : set' A) :
  (single (set := set) a) ⊆ X <-> a ∈ X.
Proof.
  rewrite /incl /set_all.
  setoid_rewrite singleP.
  intuition (subst ; auto).
Qed.

Lemma incl_single {set set' : SetTheory} {A : PreOrder} (a : A) (X : set' A) :
  X ⊆ (single (set := set) a) <-> forall x, x ∈ X -> x = a.
Proof.
  rewrite /incl /set_all.
  setoid_rewrite singleP.
  intuition (subst ; auto).
Qed.

Lemma image_incl {set set' : SetTheory} {A B : PreOrder} (X : set A) (Y : set' B) (f : A ⤳ B) :
  image f X ⊆ Y <-> ∀ x ∈ X, (f x) ∈ Y.
Proof.
  rewrite /incl /set_all.
  setoid_rewrite imageP.
  split.
  - intros h ? ?.
    apply h.
    now eexists.
  - now intros ? ? (?&?&->).
Qed.

Lemma union_incl {set : SetTheory} {A} (X : set (set A)) (Y : set A) :
  union X ⊆ Y <-> ∀ x ∈ X, x ⊆ Y.
Proof.
  rewrite /incl /set_all.
  setoid_rewrite unionP.
  split.
  - intros h **.
    apply h.
    now eexists.
  - intros ? ? (?&?&?).
    eauto.
Qed.

(** ** General notions mixing order and set theory *)

Definition lower_set {set : BaseSetTheory} {A : PreOrder} (X : set A) :=
  forall (a b:A), a ≤ b -> b ∈ X -> a ∈ X.

Definition upper_set {set : BaseSetTheory} {A : PreOrder} (X : set A) :=
  forall (a b:A), a ≤ b -> a ∈ X -> b ∈ X.

Definition upper_bound {set : BaseSetTheory} {A : PreOrder}
  (ub:A) (X : set A) :=
  ∀ x ∈ X, x ≤ ub.

Definition lower_bound {set : BaseSetTheory} {A : PreOrder}
  (lb:A) (X : set A) :=
  ∀ x ∈ X, lb ≤ x.

Definition minimal_upper_bound {set : BaseSetTheory} {A : PreOrder}
  (mub:A) (X : set A) :=
  upper_bound mub X /\
  (forall b, upper_bound b X -> b ≤ mub -> mub ≤ b).
  
Definition maximal_lower_bound {set : BaseSetTheory} {A : PreOrder}
  (mlb:A) (X : set A) :=
  lower_bound mlb X /\
  (forall b, lower_bound b X -> mlb ≤ b -> b ≤ mlb).

Definition least_upper_bound {set : BaseSetTheory} {A : PreOrder}
  (lub:A) (X : set A) :=
  upper_bound lub X /\
  (forall b, upper_bound b X -> lub ≤ b).

Definition greatest_lower_bound {set : BaseSetTheory} {A : PreOrder}
  (glb:A) (X : set A) :=
  lower_bound glb X /\
  (forall b, lower_bound b X -> b ≤ glb).

Lemma lub_unique {set : BaseSetTheory} {A : Poset} (lub lub':A) (X : set A) :
  least_upper_bound lub X -> least_upper_bound lub' X -> lub = lub'.
Proof.
  intros H H'.
  apply ord_antisym.
  - apply H, H'.
  - apply H', H.
Qed.