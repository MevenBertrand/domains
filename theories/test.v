From HB Require Import structures.
From Stdlib Require Import ssreflect.

(** Adapted from Arsac et al.'s category theory library for HB
  https://gitlab.com/SamuelArsac/graph-rewriting *)

Declare Scope cat_scope.
Delimit Scope cat_scope with Cat.
Local Open Scope cat_scope.

#[primitive] HB.mixin Record IsQuiver C := {
    #[canonical=no] hom : C -> C -> Type
  }.
#[short(type="Quiver")]
HB.structure Definition quiver := { C of IsQuiver C }.

Bind Scope cat_scope with Quiver.
Bind Scope cat_scope with hom.
Arguments hom {_}.
Notation "a → b" := (hom a b) (at level 65) : cat_scope.
Notation bare f := (f: hom _ _).

(** precategories: quivers + id and comp *)
#[primitive] HB.mixin Record IsPreCat (T : Type) of quiver T := {
  #[canonical=no] idmap : forall (a : T), a → a;
  #[canonical=no] comp : forall (a b c : T), (a → b) -> (b → c) -> (a → c);
}.

#[short(type="PreCat")]
HB.structure Definition precat := { T of IsPreCat T & }.

Bind Scope cat_scope with precat.
Arguments idmap {_ _}.
Arguments comp {_ _ _ _}.
Notation "f ∘ g" := (comp g f) (at level 40, left associativity) : cat_scope.

(** categories: precategories + laws *)
HB.mixin Record IsCat (T : Type) of precat T := {
  #[canonical=no] comp1o : forall (a b : T) (f : a → b), idmap ∘ f = f;
  #[canonical=no] compo1 : forall (a b : T) (f : a → b), f ∘ idmap = f;
  #[canonical=no] compoA : forall (a b c d : T)
    (f : a → b) (g : b → c) (h : c → d), h ∘ (g ∘ f) = (h ∘ g) ∘ f
}.
#[short(type="Cat")]
HB.structure Definition cat := { C of IsCat C & }.

Bind Scope cat_scope with Cat.
Arguments compo1 {_ _ _}.
Arguments comp1o {_ _ _}.
Arguments compoA {_ _ _ _ _}.

#[primitive] HB.mixin Record IsPreGpd (T : Type) of quiver T := {
  #[canonical=no] inv : forall (a b : T), (a → b) -> (b → a)
}.

#[short(type="PreGpd")]
HB.structure Definition pregpd := { T of IsPreGpd T & }.

Arguments inv {_ _ _}.
Notation "f ⁻¹" := (inv f) (at level 1): cat_scope.

(** groupoids: pregroupoids + laws *)
HB.mixin Record IsGpd T of cat T & pregpd T := {
  #[canonical=no] invl : forall (a b : T) (f : a → b), f⁻¹ ∘ f = idmap ;
  #[canonical=no] invr : forall (a b : T) (f : a → b), f ∘ f ⁻¹ = idmap ;
}.

#[short(type="Gpd")]
HB.structure Definition groupoid := { C of IsGpd C & }.

Arguments invl {_ _ _}.
Arguments invr {_ _ _}.

Lemma inv_inv (X:Gpd) :
  forall (A B:X) (f:A → B), (f⁻¹)⁻¹ = f.
Proof.
  intros.
  transitivity ((f⁻¹)⁻¹ ∘ f⁻¹ ∘ f).
  - now rewrite -compoA invl compo1.
  - now rewrite invl comp1o.
Qed.