(** * Domains.groupoids: definitions and lemmas for groupoids *)
From Stdlib Require Import Morphisms CRelationClasses.
From smpl Require Export Smpl.
From HB Require Import structures.
Require Import notations categories.


(**  Groupoids are categories in which every morphism has an inverse.
     Groupoids generalize groups (hence the name) in the sense that
     a groupoid with a single object forms a group.
     
     When [f] is a morphism in a groupoid [f⁻¹] is its inverse.
  *)

#[primitive] HB.mixin Record IsPreGpd (T : Type) of quiver T := {
  #[canonical=no] inv : forall (a b : T), (a ⤳ b) -> (b ⤳ a)
}.

#[short(type="PreGpd")]
HB.structure Definition pregpd := { T of IsPreGpd T & }.

Arguments inv {_ _ _}.
Notation "f ⁻¹" := (inv f) : cat_scope.

(** groupoids: pregroupoids + laws *)
HB.mixin Record IsGpd T of cat T & pregpd T := {
  #[canonical=no] invl : forall (a b : T) (f : a ⤳ b), f ⁻¹ ∘ f = idmap ;
  #[canonical=no] invr : forall (a b : T) (f : a ⤳ b), f ∘ f ⁻¹ = idmap ;
}.

#[short(type="Gpd")]
HB.structure Definition groupoid := { C of IsGpd C & }.

Arguments invl {_ _ _}.
Arguments invr {_ _ _}.

Lemma inv_inv (X:Gpd) (A B:X) (f:A ⤳ B) : (f⁻¹)⁻¹ = f.
Proof.
  transitivity ((f⁻¹)⁻¹ ∘ f⁻¹ ∘ f).
  - by rewrite compoA invl comp1o.
  - by rewrite invl compo1.
Qed.

Lemma inv_compose (X:Gpd) (A B C:X) (g:B ⤳ C) (f:A ⤳ B) :
  (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹.
Proof.
  assert ((g ∘ f)⁻¹ ∘ (g ∘ f) ∘ f⁻¹ = (g ∘ f)⁻¹ ∘ g) as e
    by rewrite !compoA invr comp1o //.
  rewrite invl compo1 in e.
  by rewrite e compoA invr comp1o.
Qed.

Lemma inv_eq (X:Gpd) (A B:X) (f g:A ⤳ B) : 
  f = g -> f⁻¹ = g⁻¹.
Proof.
  by move => -> //.
Qed.

Lemma inv_inj (X:Gpd) (A B:X) (f g:A ⤳ B) : 
  f⁻¹ = g⁻¹ -> f = g.
Proof.
  move => /inv_eq e.
  by rewrite !inv_inv in e.
Qed.