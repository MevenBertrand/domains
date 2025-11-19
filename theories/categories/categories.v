(** * Domains.categories: basic definitions of categories *)
From Stdlib Require Import Program ssreflect ssrfun.
From HB Require Import structures.

Require Import notations basics.

(** ** Definitions *)

(** Adapted from Arsac et al.'s category theory library for HB
  https://gitlab.com/SamuelArsac/graph-rewriting *)

Declare Scope cat_scope.
Delimit Scope cat_scope with Cat.
#[local] Open Scope cat_scope.

#[primitive] HB.mixin Record IsQuiver C := {
    #[canonical=no] hom : C -> C -> Type
  }.
#[short(type="Quiver")]
HB.structure Definition quiver := { C of IsQuiver C }.

Bind Scope cat_scope with Quiver.
Bind Scope cat_scope with hom.
Arguments hom {_}.
Notation "a → b" := (hom a b) : cat_scope.
Notation "a →[ C ] b" := (@hom C a b) (only parsing) : cat_scope.
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
Notation "f ∘ g" := (comp g f) : cat_scope.
Notation "f ∘[ C ] g" := (@comp C _ _ _ g f) (only parsing): cat_scope.
Notation "f \; g" := (comp f g) (only parsing): cat_scope.

(** categories: precategories + laws *)
HB.mixin Record IsCat (T : Type) of precat T := {
  #[canonical=no] comp1o : forall (a b : T) (f : a → b), idmap \; f = f;
  #[canonical=no] compo1 : forall (a b : T) (f : a → b), f \; idmap = f;
  #[canonical=no] compoA : forall (a b c d : T) (f : a → b) (g : b → c) (h : c → d), f \; (g \; h) = (f \; g) \; h
}.
#[short(type="Cat")]
HB.structure Definition cat := { C of IsCat C & }.

Bind Scope cat_scope with Cat.
Arguments compo1 {_ _ _}.
Arguments comp1o {_ _ _}.
Arguments compoA {_ _ _ _ _}.

(** ** Concrete categories *)

(**  A concrete category is one where every object has a [Type]
     carrier, and every hom defines a function between the carriers.

     Further, equal homs produce extensionally-equal functions, and
     compostion of homs corresponds to to the composition of functions.
  *)

(** Is this simply a category with a functor into Type?? *)

#[primitive] HB.mixin Record IsConcrete (T : Type) of precat T := {
  #[canonical=no] obmap : T -> Type ;
  #[canonical=no] hommap : forall {a b : T}, (a → b) -> obmap a -> obmap b ;
  #[canonical=no] hommap1: forall (a : T), hommap (idmap (a := a)) = idfun ;
  #[canonical=no] hommapo: forall (a b c : T) (f : a → b) (g : b → c),
    hommap (g ∘ f) = fun x => (hommap g (hommap f x))
}.

#[short(type="Concrete")]
HB.structure Definition concretecat := { T of IsConcrete T & }.

Arguments hommap {_ _ _} _ _.

Notation "f # x" := (hommap f x) 
  : cat_scope.

(** ** Examples *)

(** *** Terminal *)

(**  The category with a single object and a single morphism. *)

Definition One := unit.

HB.instance Definition _ := IsQuiver.Build One (fun _ _ => unit).
HB.instance Definition _ := IsPreCat.Build One (fun _ => tt) (fun _ _ _ _ _ => tt).

Program Definition _One_cat := IsCat.Build One _ _ _.
Next Obligation.
  move => ?? [] //=.
Qed.
Next Obligation.
  move => ?? [] //=.
Qed.
Next Obligation.
  reflexivity.
Qed.

HB.instance Definition _ := _One_cat.

(** *** Dual *)
(** The opposite category *)

Definition catop (C : Type) : Type := C.
Notation "C ^op" := (catop C) (at level 2, format "C ^op") : cat_scope.
HB.instance Definition _ (C : Quiver) :=
  IsQuiver.Build C^op (fun a b => hom b a).
HB.instance Definition _ (C : PreCat) :=
  IsPreCat.Build (C^op) (fun _ => idmap) (fun _ _ _ f g => g \; f).
HB.instance Definition _ (C : Cat) := IsCat.Build (C^op)
  (fun _ _ => compo1) (fun _ _ => comp1o) (fun _ _ _ _ _ _ _ => eq_sym (compoA _ _ _)).
Definition morphop {C: Quiver} [x y: C] (f: x → y): y →[C^op] x := f.

(** *** Product *)
(**  The product category. *)

Definition Prod C D : Type := (C * D)%type.
Definition Prod_hom {C D : Quiver} (s : Prod C D) (t : Prod C D) : Type :=
  (fst s → fst t) * (snd s → snd t).

HB.instance Definition _ (C D : Quiver) :=
  IsQuiver.Build (Prod C D) (Prod_hom (C := C) (D := D)).

Definition Prod_id (C D : PreCat) (X : Prod C D) : Prod_hom X X :=
  (idmap,idmap).
Definition Prod_comp (C D : PreCat) (X Y Z : Prod C D)
  (f : Prod_hom X Y) (g : Prod_hom Y Z) : Prod_hom X Z :=
   (fst g ∘ fst f, snd g ∘ snd f).

HB.instance Definition _ (C D : PreCat) :=
  IsPreCat.Build (Prod C D) (Prod_id C D) (Prod_comp C D).

Program Definition _Prod_cat (C D : Cat) := IsCat.Build (Prod C D) _ _ _.
Next Obligation.
  move => ?? ?? [fa fb].
  by rewrite /idmap /= /Prod_id /comp /= /Prod_comp /= !comp1o.
Qed.
Next Obligation.
  move => ?? ?? [fa fb].
  by rewrite /idmap /= /Prod_id /comp /= /Prod_comp /= !compo1.
Qed.
Next Obligation.
  move => ?? ???? [fa fb] [ga gb] [ha hb].
  by rewrite /comp /= /Prod_comp /= !compoA.
Qed.

HB.instance Definition _ (C D : Cat) := _Prod_cat C D.

(** *** Types *)

(** The category of types from a fixed universe, with all type-theoretic functions. *)

Definition Type_hom (A B : Type) := A -> B.

HB.instance Definition _ :=
  IsQuiver.Build Type Type_hom.

HB.instance Definition _ := IsPreCat.Build Type (fun _ x => x) (fun _ _ _ f g x => g (f x)).

Definition _Type_cat := IsCat.Build Type (fun _ _ _ => eq_refl).