(** * domains.colsets: Colored sets *)
From Stdlib Require Import Relations List Program ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories.all preord sets.

(**
    Colored sets are a generalization of the idea of "directed" sets.

     A "color" is a property a set may have which is parametric over
     a set theory.  We require that the property of being "colored" is
     preserved by the operations of a set theory: every singleton set
     is colored; a colored union of colored sets is colored; and the
     image (under a monotone function) of a colored set is again colored.
  *)

Record color {set : SetTheory} :=
  Color
  { color_prop : forall (A : Poset) (X : set A), Prop
  ; color_single : forall (A : Poset) (a:A),
        color_prop A (single a)
  ; color_image : forall (A B : Poset) (f:A → B) (X : set A),
        color_prop A X -> color_prop B (image f X)
  ; color_union : forall (A : Poset) (XS:set (set A)),
        color_prop (set A) XS ->
        (forall X : (set A), X ∈ XS -> color_prop A X) ->
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

  Lemma colored_ext : IsExtMem (fun A => { X : set A | color_prop C X }) (fun A a X => a ∈ sval X).
  Proof.
    intros ? [X] [Y] ? ; cbn in *.
    enough (X = Y) as <- by (f_equal ; ext).
    now apply set_ext.
  Qed.

  Definition colored_sets : Poset -> Poset :=
    promote_set (fun A => { X : set A | color_prop C X }) (fun A a X => a ∈ sval X) colored_ext.

  HB.instance Definition _ : IsBaseSetTheory.axioms_ colored_sets :=
    SetIncl (fun A => { X : set A | color_prop C X }) (fun A a X => a ∈ sval X) colored_ext.

  Definition csingle A a : colored_sets A := exist _ (single a) (color_single C A a).

  Definition cimage (A B:Poset) (f:A → B) (X : colored_sets A) :=
    exist _ (image f (proj1_sig X))
            (color_image C A B f (proj1_sig X) (proj2_sig X)).

  Program Definition cunion
    (A : Poset) (XS : colored_sets (colored_sets A)) : colored_sets A :=
    exist (color_prop C) (∪ (image _ (projT1 XS))) _.
  Next Obligation.
    unshelve econstructor.
    1: exact sval.
    red.
    intros [] [] ? ; cbn in *.
    rewrite set_leP.
    assumption.
  Defined.
  Next Obligation.
    apply color_union.
    - now apply: color_image.
    - intros ? Hin.
      apply imageP in Hin as [? [? ->]].
      apply: proj2_sig.
  Qed.

End ColoredSets.

HB.instance Definition _ (set : SetTheory) (c : color set) :=
  IsPreSetTheory.Build (colored_sets c) (csingle c) (cimage c) (cunion c).

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
  rewrite /member /= unionP /=.
  split.
  - intros [X [[Y [??]]%imageP ?]] ; cbn in * ; subst.
    now eexists.
  - intros [X [??]].
    exists (sval X).
    split; auto.
    apply imageP.
    now cbn.
Qed.

HB.instance Definition _ (set : SetTheory) (c : color set) := _ColoredSets set c.