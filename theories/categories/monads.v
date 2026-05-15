(** * Domains.functors: functors and natural transformations *)
From Stdlib Require Import Program Setoid ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories functors.

#[local] Open Scope cat_scope.

#[primitive]HB.mixin Record IsPreMonad (C : Quiver) (F : PreFunctor C C) := {
  pure : forall (a : C), (a → F a) ;
  mult : forall (a : C), (F (F a) → F a)
}.

#[short(type="PreMonad"),primitive]
HB.structure Definition premonad (C : Quiver) :=
  { F & IsPreMonad C F }.