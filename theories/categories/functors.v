(** * Domains.functors: functors and natural transformations *)
From Stdlib Require Import Program Setoid ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories.

#[local] Open Scope cat_scope.

(** ** Definitons *)

#[primitive]HB.mixin Record IsPreFunctor (C D : Quiver) (F : C -> D) := {
   #[canonical=no] Fhom : forall (a b : C), (a ⤳ b) -> (F a ⤳ F b)
  }.
#[short(type="PreFunctor"),primitive]
HB.structure Definition prefunctor (C D : Quiver) :=
  { F of IsPreFunctor C D F }.

Notation "F <$> f" := (Fhom (s := F) _ _ f) : cat_scope.

Definition pack_prefunctor [C D: Quiver] (F: C -> D)
  (Fhom : forall (a b : C), (a ⤳ b) -> (F a ⤳ F b)): PreFunctor C D :=
  HB.pack F (IsPreFunctor.Build _ _ F Fhom).


(** We follow Dockins and phrase the axioms in a "forded" fashion, if I understand
  correctly this helps with making a number of things hold up to defeq, in particular
  associativity of composition, by exploiting the fact that composition of functions
  is definitionally associative. Maybe we'll want to go back on this later… *)
  
#[primitive]HB.mixin Record PreFunctor_IsFunctor (C D : PreCat) F of @prefunctor C D F := {
   #[canonical=no] F1_ford : forall {a : C} {f : a ⤳ a}, f = idmap -> F <$> f = idmap;
   #[canonical=no] Fcomp_ford : forall {a b c : C} {f : a ⤳ b} {g : b ⤳ c} {h : a ⤳ c},
      h = g ∘ f -> F <$> h = F <$> f \; F <$> g;
}.
#[short(type="Functor"),primitive]
HB.structure Definition functor (C D : PreCat) :=
  { F of prefunctor C D F & PreFunctor_IsFunctor C D F }.

#[primitive]HB.factory Record IsFunctor (C D: PreCat) (F: C -> D) := {
  #[canonical=no] Fhom : forall (a b : C), (a ⤳ b) -> (F a ⤳ F b);
  #[canonical=no] F1 : forall (a : C), Fhom a _ idmap = idmap;
  #[canonical=no] Fcomp : forall (a b c : C) (f : a ⤳ b) (g : b ⤳ c),
    Fhom _ _ (g ∘ f) = Fhom _ _ g ∘ Fhom _ _ f;
}.

Lemma F1 {C D : PreCat} {F : Functor C D} (a : C) : F <$> (idmap (a := a)) = idmap.
Proof.
  by apply F1_ford.
Qed.

Lemma Fcomp {C D : PreCat} {F : Functor C D} {a b c : C} {f : a ⤳ b} {g : b ⤳ c} :
  F <$> (g ∘ f) = F <$> f \; F <$> g.
Proof.
  by apply Fcomp_ford.
Qed.

HB.builders Context (C D: PreCat) F of IsFunctor C D F.

HB.instance Definition _ := IsPreFunctor.Build _ _ F Fhom.

Lemma _F1_ford (a : C) (f : a ⤳ a) : f = idmap -> F <$> f = idmap.
Proof.
  move => ->.
  by apply F1.
Qed.

Lemma _Fcomp_ford (a b c : C) (f : a ⤳ b) (g : b ⤳ c) (h : a ⤳ c) :
      h = g ∘ f -> F <$> h = F <$> f \; F <$> g.
Proof.
  move => ->.
  by apply Fcomp.
Qed.

HB.instance Definition _ := PreFunctor_IsFunctor.Build _ _ F _F1_ford _Fcomp_ford.

HB.end.

(* Definition pack_functor [C D: PreCat] (F: C -> D)
  (Fhom : forall (a b : C), (a ⤳ b) -> (F a ⤳ F b))
  (F1 : forall (a : C), Fhom _ _ idmap = idmap)
  (Fcomp : forall (a b c : C) (f : a ⤳ b) (g : b ⤳ c),
    Fhom _ _ (f \; g) = Fhom _ _ f \; Fhom _ _ g): Functor C D :=
  HB.pack F (IsFunctor.Build _ _ F Fhom F1 Fcomp).
Arguments pack_functor [_ _] _ _. *)

(** ** Identity and composition *)

(** identity functor *)
HB.instance Definition IdPreFun (C : Quiver) :=
  IsPreFunctor.Build C C idfun (fun _ _ f => f).
HB.instance Definition IdFun (C : PreCat) :=
  PreFunctor_IsFunctor.Build C C idfun (fun _ _ e => e) (fun _ _ _ _ _ _ e => e).

(** composition of functors *)
Section comp_prefunctor.
Context {C D E : Quiver} {F : PreFunctor C D} {G : PreFunctor D E}.

HB.instance Definition CompPreFun := IsPreFunctor.Build C E (G \o F)%function
   (fun a b => (Fhom (s := G) (F a) (F b)) \o (Fhom (s := F) a b)).

Lemma comp_Fun (a b : C) (f : a ⤳ b) : (G \o F)%function <$> f = G <$> (F <$> f).
Proof. reflexivity. Qed.

End comp_prefunctor.

Section comp_functor.
Context {C D E : PreCat} {F : Functor C D} {G : Functor D E}.

Lemma comp_F1_ford (a : C) (f : a ⤳ a) : f = idmap -> (G \o F)%function <$> f = idmap.
Proof. exact (fun e => F1_ford _ _ (F1_ford _ _ e)). Defined.
Lemma comp_Fcomp_ford  (a b c : C) (f : a ⤳ b) (g : b ⤳ c) (h : a ⤳ c) :
  h = g ∘ f ->
  (G \o F)%function <$> h = ((G \o F)%function <$> g) ∘ ((G \o F)%function <$> f).
Proof. exact (fun e => Fcomp_ford _ _ _ _ _ _ (Fcomp_ford _ _ _ _ _ _ e)). Defined.

HB.instance Definition CompFun := PreFunctor_IsFunctor.Build C E (G \o F)%function
  comp_F1_ford comp_Fcomp_ford.

Lemma comp_F1 (a : C) : (G \o F)%function <$> (idmap (a := a)) = idmap.
Proof. by apply comp_F1_ford. Qed.
Lemma comp_Fcomp  (a b c : C) (f : a ⤳ b) (g : b ⤳ c) (h : a ⤳ c) :
  (G \o F)%function <$> (g ∘ f) = ((G \o F)%function <$> g) ∘ ((G \o F)%function <$> f).
Proof. by apply comp_Fcomp_ford. Qed.

End comp_functor.

(** Sanity checking: if we unset universe checking, we indeed have a pre-category of quivers. *)
(** Once we have universe polymorphism, we can build this pre-category and the (large) category
  of categories. *)

(* Unset Universe Checking.

Section Sanity.
  HB.instance Definition _ := IsQuiver.Build Quiver PreFunctor.

  Program Definition _PreFunPreCat := IsPreCat.Build Quiver _ _.
  Next Obligation.
    move => a.
    rewrite /hom /=.
    exact ((HB.pack idfun (IdPreFun a)) : PreFunctor a a).
  Defined.
  Next Obligation.
    move => C D E F G.
    rewrite /hom /=.
    exact (HB.pack (G \o F) (CompPreFun (F := F) (G := G)) : PreFunctor C E).
  Defined.

  HB.instance Definition _ := _PreFunPreCat.

  (** Moreover, identity and associativity are definitional *)

  Variables C D E F:Quiver.
  Variable G:E ⤳ F.
  Check (G : PreFunctor E F). (* The arrow ⤳ of Quivers is indeed PreFunctors *)
  Variable H:D ⤳ E.
  Variable I:C ⤳ D.

  Goal (G ∘ (H ∘ I) = (G ∘ H) ∘ I).
  Proof (eq_refl _).

  Goal (G ∘ idmap = G).
  Proof (eq_refl _).

  Goal (idmap ∘ G = G).
  Proof (eq_refl _).

End Sanity.

Set Universe Checking. *)

(** ** Examples *)

(** *** Constant functor *)

(** constant functor *)

Definition cst (C D : Quiver) (c : C) := fun of D => c.
Arguments cst {C} D c/.
HB.instance Definition _ {C D : PreCat} (c : C) :=
  IsPreFunctor.Build D C (cst D c) (fun _ _ => const idmap).
HB.instance Definition _ {C D : Cat} (c : C) :=
  IsFunctor.Build D C (cst D c) (fun _ _ => const (idmap (s := C)))
    (fun=> eq_refl) (fun _ _ _ _ _ => eq_sym (compo1 (idmap (s := C)))).

(** ** Natural transformations *)

(** *** Transformations *)
HB.instance Definition _  (C : Type) (D : Quiver) :=
  IsQuiver.Build (C -> D) (fun f g => forall c, f c ⤳ g c).

(** *** Naturality *)
#[primitive]HB.mixin Record IsNatural {C : Quiver} {D : PreCat} (F G : PreFunctor C D) (n : forall c, F c ⤳ G c) :=
  { #[canonical=no] natural : forall (a b : C) (f : a ⤳ b), F <$> f \; n b = n a \; G <$> f }.
#[primitive]HB.structure Definition Natural {C : Quiver} {D : PreCat} (F G : PreFunctor C D) :=
  { n of @IsNatural C D F G n }.
Arguments Natural.type {_} {_} _ _.

(** characterising the equality of natural transformation, which is the (pointwise) equality
  of the underlying transformations *)
Lemma nat_ext {C : Quiver} {D : PreCat} (F G : PreFunctor C D) (m n : Natural.type F G) :
  (forall x, m x = n x) -> m = n.
Proof.
  destruct m as [? [[]]], n as [? [[]]] ; cbn in *.
  move => e.
  apply functional_extensionality_dep in e as <-.
  now ext.
Qed.

Smpl Add (apply nat_ext) : extensionality.

Definition pack_natural {C: Quiver} {D: PreCat} [F G: PreFunctor C D]
  (n : forall c, F c ⤳ G c)
  (natural : forall (a b : C) (f : a ⤳ b), F <$> f \; n b = n a \; G <$> f): Natural.type F G :=
  HB.pack n (IsNatural.Build _ _ _ _ n natural).
Arguments pack_natural {_ _} [_ _] _ _.

(** *** Category of functors and natural transformations *)
HB.instance Definition _  (C : Quiver) (D : PreCat) :=
  IsQuiver.Build (PreFunctor C D) ( @Natural.type C D).
HB.instance Definition _  (C D : PreCat) :=
  IsQuiver.Build (Functor C D) ( @Natural.type C D).
Arguments natural {_ _ _ _} _ [_ _] _.

Definition natural_id {C D : PreCat} (F : PreFunctor C D) (a : C) := idmap (a := F a).
Definition natural_id_natural (C D : Cat) (F : PreFunctor C D) :
  IsNatural C D F F (natural_id F).
Proof. by constructor=> a b f; rewrite /natural_id/= compo1 comp1o. Qed.
HB.instance Definition _ C D F := @natural_id_natural C D F.

Definition natural_comp {C D : PreCat} (F G H : PreFunctor C D)
   (m : F ⤳ G) (n : G ⤳ H) (a : C) := m a \; n a.
Definition natural_comp_natural (C D : Cat) (F G H : PreFunctor C D) m n :
  IsNatural C D F H ( @natural_comp C D F G H m n).
Proof.
constructor=> a b f; rewrite /natural_comp/=.
by rewrite compoA natural -compoA natural compoA.
Qed.
HB.instance Definition _ C D F G H m n := @natural_comp_natural C D F G H m n.

HB.instance Definition _ {C D : Cat} :=
  IsPreCat.Build (PreFunctor C D) natural_id natural_comp.
HB.instance Definition _ {C D : Cat} :=
  IsPreCat.Build (Functor C D) natural_id natural_comp.

Lemma _prefunctor_cat (C D : Cat) : IsCat (PreFunctor C D).
Proof.
  constructor ; ext.
  - exact: comp1o.
  - exact: compo1.
  - exact: compoA.
Qed.
HB.instance Definition _ C D := _prefunctor_cat C D.

Lemma _functor_cat (C D : Cat) : IsCat (Functor C D).
Proof.
  constructor; ext.
  - exact: comp1o.
  - exact: compo1.
  - exact: compoA.
Qed.
HB.instance Definition _ C D := _functor_cat C D.

(** *** Whiskering *)
(** pre- and post-composing a natural transformation by a functor *)

Definition whiskL {C D E : PreCat} (F : PreFunctor C D) {G G' : PreFunctor D E}
  (n : G ⤳ G') (c : C) : (G \o F) c ⤳ (G' \o F) c := n (F c).
Definition whiskR {C D E : PreCat} {F F' : PreFunctor C D} (m : F ⤳ F')
  (G : PreFunctor D E) (c : C) : (G \o F) c ⤳ (G \o F') c := G <$> (m c).

Definition whiskL_natural {C D E : Cat} (F : Functor C D) (G G' : Functor D E)
  (n : G ⤳ G') : IsNatural C E (G \o F) (G' \o F) (whiskL F n).
Proof.
  constructor => ?? f.
  rewrite /whiskL /= natural //.
Qed.

Definition whiskR_natural {C D E : PreCat} {F F' : Functor C D} (m : F ⤳ F')
  (G : Functor D E) : IsNatural C E (G \o F) (G \o F') (whiskR m G).
Proof.
  constructor => ?? f.
  rewrite /whiskR /= !comp_Fun -!Fcomp natural //.
Qed.

Notation "F ▹ n " := (whiskL F n) : cat_scope.
Notation "m ◃ G" := (whiskR m G) : cat_scope.