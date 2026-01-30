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

#[primitive] HB.mixin Record IsPreBaseSetTheory (set : Type -> Type) := {
  member {A : Type} : A -> set A -> Prop ;
  }.

#[short(type="PreBaseSetTheory"),primitive]
HB.structure Definition prebasesettheory :=
  { set & IsPreBaseSetTheory set }.

Arguments member {set _} : simpl never, rename.
Notation "x ∈ X" := (member x (X)%set) : set_scope.
Notation "x ∉ X"  := (not (member x (X)%set)) : set_scope.

#[primitive] HB.mixin Record IsBaseSetTheory set of prebasesettheory set :=
  {
    set_ext T (X Y : set T) : (forall t, member t X <-> member t Y) -> X = Y ;
  }.

#[short(type="BaseSetTheory"),primitive]
HB.structure Definition basesettheory := { set of prebasesettheory set & IsBaseSetTheory set }.

Smpl Add (apply: @set_ext) : extensionality.

#[primitive] HB.mixin Record IsPreSetTheory set of prebasesettheory set := {
  (* empty (A : Type) : set A ; *)
  single {A : Type} : A -> set A ;
  image {A B : Type} (f : A -> B) : set A -> set B ;
  union {A : Type} : set (set A) -> set A ;
  }.

#[short(type="PreSetTheory"),primitive]
HB.structure Definition presettheory :=
  { set of prebasesettheory set & IsPreSetTheory set }.

(* Arguments empty {set _} : rename. *)
Arguments single {set _} : rename.
Arguments image {set _ _} : rename.
Arguments union {set _} : rename.

(* Notation "∅" := (empty) : set_scope. *)
Notation "∪ XS" := (union (XS)%set) : set_scope.

#[primitive] HB.mixin Record IsSetTheory set of presettheory set :=
  {
    (* emptyP T (x : T) : (x ∈ empty (set := set)) <-> False ; *)
    singleP T (a b : T) : (a ∈ single (set := set) b) <-> a = b ;
    imageP (A B : Type) (f : A -> B) (P : (set A)) (y : B) :
      y ∈ (image f P) <-> exists x, x ∈ P /\ y = f x ;
    unionP T (xs : (set (set T))) (a : T) :
      a ∈ (∪ xs) <-> exists x : (set T), x ∈ xs /\ a ∈ x
  }.

#[short(type="SetTheory"),primitive]
HB.structure Definition settheory :=
  { set of basesettheory set & IsPreSetTheory set & IsSetTheory set }.

Lemma image_compose (set : SetTheory) A B C (f:A -> B) (g:B -> C) (X: set A) (c:C) :
  c ∈ (image (g \o f) X) <-> c ∈ (image g (image f X)).
Proof.
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

Lemma image_fun (set : SetTheory) A B (f:A -> B) (X: set A) (x : A) :
  x ∈ X -> f x ∈ image f X.
Proof.
  now rewrite !imageP.
Qed.

Definition incl {set set' : BaseSetTheory} {A : Type} (X : set A) (Y : set' A) :=
  forall a, a ∈ X -> a ∈ Y.

Notation "X ⊆ Y" := (incl (X)%set (Y)%set) : set_scope.

HB.instance Definition _ (set : BaseSetTheory) (A : Type) :=
  IsPrePreOrder.Build (set A) (@incl set set A).
  
Program Definition _SetPreOrder (set : BaseSetTheory) (A : Type) :=
  IsPreOrder.Build (set A) _ _.
Next Obligation.
  now cbv.
Qed.
Next Obligation.
  red.
  now rewrite /ord /= /incl /=.
Qed.

HB.instance Definition _ (set : BaseSetTheory) (A : Type) := _SetPreOrder set A.

Program Definition _SetPoset (set : SetTheory) (A : Type) :=
  IsPoset.Build ((set :> BaseSetTheory) A) _.
Next Obligation.
  rewrite /ord /= /incl /=.
  apply set_ext.
  ext.
  now split.
Qed.

HB.instance Definition _ (set : SetTheory) (A : Type) := _SetPoset set A.

(** ** Decidablitiy *)

(**  A set has a [set_dec] if set membership is decidable. *)

Record set_dec (set : BaseSetTheory) (A:Type) :=
  Setdec
  { setdec :> forall (x:A) (X:set A), { x ∈ X } + { x ∉ X } }.


(** ** General notions mixing order and set theory *)

Definition lower_set {set : BaseSetTheory} {A : Poset} (X : set A) :=
  forall (a b:A), a ≤ b -> b ∈ X -> a ∈ X.

Definition upper_set {set : BaseSetTheory} {A : Poset} (X : set A) :=
  forall (a b:A), a ≤ b -> a ∈ X -> b ∈ X.

Definition upper_bound {set : BaseSetTheory} {A : Poset}
  (ub:A) (X : set A) :=
  forall x, x ∈ X -> x ≤ ub.

Definition lower_bound {set : BaseSetTheory} {A : Poset}
  (lb:A) (X : set A) :=
  forall x, x ∈ X -> lb ≤ x.

Definition minimal_upper_bound {set : BaseSetTheory} {A : Poset}
  (mub:A) (X : set A) :=
  upper_bound mub X /\
  (forall b, upper_bound b X -> b ≤ mub -> mub ≤ b).
  
Definition maximal_lower_bound {set : BaseSetTheory} {A : Poset}
  (mlb:A) (X : set A) :=
  lower_bound mlb X /\
  (forall b, lower_bound b X -> mlb ≤ b -> b ≤ mlb).

Definition least_upper_bound {set : BaseSetTheory} {A : Poset}
  (lub:A) (X : set A) :=
  upper_bound lub X /\
  (forall b, upper_bound b X -> lub ≤ b).

Definition greatest_lower_bound {set : BaseSetTheory} {A : Poset}
  (glb:A) (X : set A) :=
  lower_bound glb X /\
  (forall b, lower_bound b X -> b ≤ glb).


(**  ** Colored sets *)

(**
    Colored sets are a generalization of the idea of "directed" sets.

     A "color" is a property a set may have which is parametric over
     a set theory.  We require that the property of being "colored" is
     preserved by the operations of a set theory: every singleton set
     is colored; a colored union of colored sets is colored; and the
     image (under a monotone function) of a colored set is again colored.
  *)

Record color {set : PreSetTheory} :=
  Color
  { color_prop : forall (A : Type) (X : set A), Prop
  ; color_single : forall (A : Type) (a:A),
        color_prop A (single a)
  ; color_image : forall (A B : Type) (f:A -> B) (X : set A),
        color_prop A X -> color_prop B (image f X)
  ; color_union : forall (A : Type) (XS:set (set A)),
        color_prop (set A) XS ->
        (forall X : set A, X ∈ XS -> color_prop A X) ->
        color_prop A (∪XS)
  }.

Arguments color : clear implicits.
Arguments color_prop {_} _ {_}.

(**  The conjunction of two coloring properties is again a color. *)

Program Definition color_and {set : SetTheory} (C1 C2:color set) : color set :=
  {| color_prop := (fun A X => (color_prop C1 X) /\ (color_prop C2 X)) ; |}.
Next Obligation.
  cbn ; eauto using color_single.
Qed.
Next Obligation.
  cbn ; eauto using color_image.
Qed.
Next Obligation.
  split.
  all: apply color_union ; eauto.
  all: intros ; match goal with | H : _ |- _ => now apply H end.
Qed.
  
(**  The property of being inhabited is a simple example of a color. *)

Program Definition inhabited {set : SetTheory} : color set :=
  {| color_prop := fun A X => exists a:A, a ∈ X ; |}.
Next Obligation.
  cbn.
  eexists.
  now apply singleP.
Qed.
Next Obligation.
  eexists.
  now apply image_fun.
Qed.
Next Obligation.
  match goal with | H : _ |- _=> edestruct H end ; eauto.
  eexists.
  now apply unionP.
Qed.

(**  Given a base set theory [T], we can collect together all the sets
     of [T] that satisfy some coloring property: these colored sets
     again form a set theory.
  *)

Section ColoredSets.
  Context {set : SetTheory} (C:color set).

  Definition colored_sets : Type -> Type :=
    fun A => { X : set A | color_prop C X }.

  Definition cmember A a (X:colored_sets A) := a ∈ proj1_sig X.

  Definition csingle A a : colored_sets A := exist _ (single a) (color_single C A a).

  Definition cimage (A B:Type) (f:A -> B) (X : colored_sets A) :=
    exist _ (image f (proj1_sig X))
            (color_image C A B f (proj1_sig X) (proj2_sig X)).

  Program Definition cunion (A : Type) (XS : colored_sets (colored_sets A)) : colored_sets A :=
    exist (color_prop C) (∪ (image sval (projT1 XS))) _.
  Next Obligation.
    intros.
    cbn.
    apply color_union.
    - apply color_image, proj2_sig.
    - intros ? Hin.
      apply imageP in Hin as [? [? ->]].
      apply proj2_sig.
  Qed.

End ColoredSets.

Arguments cmember _ _ _/.
Arguments csingle _ _ /.
Arguments cimage _ _ _ _/.
Arguments cunion _ _/.

HB.instance Definition _ (set : SetTheory) (c : color set) :=
  IsPreBaseSetTheory.Build (colored_sets c) (cmember c).

HB.instance Definition _ (set : SetTheory) (c : color set) :=
  IsPreSetTheory.Build (colored_sets c) (csingle c) (cimage c) (cunion c).

Program Definition _BaseColoredSets (set : SetTheory) (c : color set) :=
  IsBaseSetTheory.Build (colored_sets c) _.
Next Obligation.
  destruct X as [X], Y as [Y].
  enough (X = Y) as -> by (f_equal ; ext).
  now apply set_ext.
Qed.

HB.instance Definition _ (set : SetTheory) (c : color set) := _BaseColoredSets set c.

Program Definition _ColoredSets (set : SetTheory) (c : color set) :=
  IsSetTheory.Build (colored_sets c) _ _ _.
Next Obligation.
  intros.
  apply singleP.
Qed.
Next Obligation.
  intros.
  apply imageP.
Qed.
Next Obligation.
  intros.
  rewrite /member /=.
  rewrite unionP.
  intuition.
  - destruct H as [X [??]].
    apply imageP in H.
    destruct H as [Y [??]].
    exists Y. split; auto.
    now subst.
  - destruct H as [X [??]].
    exists (proj1_sig X).
    split; auto.
    now apply imageP.
Qed.

HB.instance Definition _ (set : SetTheory) (c : color set) := _ColoredSets set c.