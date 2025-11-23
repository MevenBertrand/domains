(** * Domains.morphisms: important classes of morphisms: monos, epis, isos *)
From Stdlib Require Import Program ssreflect.
From HB Require Import structures.

Require Import notations basics axioms categories.

#[local] Open Scope cat_scope.

(** ** Monomorphisms *)
(**  A monomorphism is a morphism which cancels on the left. *)

Definition isMono {C: PreCat} [x y: C] (f : x → y) :=
  forall z (g1 g2 : z → x), f ∘ g1 = f ∘ g2 -> g1 = g2.

#[primitive] HB.mixin Record IsMono {C: PreCat} (x y: C) (f : x → y) :=
  { #[canonical=no] mono_prop: isMono f}.
#[short(type="Mono")]
HB.structure Definition mono {C: PreCat} (x y: C)
  := { f of IsMono _ x y f }.
Notation "a ↣ b" := (Mono _ a b) : cat_scope.
Notation "a ↣[ C ] b" := (Mono C a b) (only parsing) : cat_scope.
Arguments Mono {_}.

Definition pack_mono {C: PreCat} [x y: C] (f : x → y)
  (mono_f: isMono f): x ↣ y :=
  HB.pack f (IsMono.Build _ _ _ f mono_f).

Lemma IsMono_id {C: Cat} (x: C): isMono (idmap (a := x)).
Proof. move=>B f g. by rewrite !compo1. Qed.
  
Lemma IsMono_comp {C: Cat} [a b c : C] (f: a ↣ b) (g: b ↣ c):
  isMono (g ∘ f).
Proof.
  intros z g1 g2 eq.
  rewrite 2!compoA in eq.
  by do 2 apply mono_prop in eq.
Qed.

Lemma IsMono_decomp {C: Cat} [a b c : C] (m: a → b) (n: b → c):
  isMono (n ∘ m) -> isMono m.
Proof.
  intros mono D f g eq. apply mono.
  by rewrite compoA eq -compoA.
Qed.

Definition joint_mono {C: Cat} [a b c: C] (f: c → a) (g: c → b) :=
  forall d (x y: d → c), f ∘ x = f ∘ y -> g ∘ x = g ∘ y -> x = y.


(** ** Epimorphisms *)
(**  An epimorphism is a morphism which cancels on the right. *)

Definition isEpi {C: PreCat} [x y: C] (f : x → y) :=
  forall z (g1 g2 : y → z), g1 ∘ f = g2 ∘ f -> g1 = g2.

#[primitive] HB.mixin Record IsEpi {C: PreCat} (x y: C) (f : x → y) :=
  { #[canonical=no] epi_prop: isEpi f}.
#[short(type="Epi")]
HB.structure Definition epi {C: PreCat} [x y: C]
  := { f of IsEpi C x y f }.
Notation "a ↠ b" := (Epi _ a b) : cat_scope.
Notation "a ↠[ C ] b" := (Epi C a b) (only parsing) : cat_scope.
Arguments Epi {_}.

(** duality with monos  *)
HB.instance Definition _morphop_mono {C: PreCat} (x y: C) (f : x ↣ y)
  := IsEpi.Build C^op y x (morphop f) ( @mono_prop _ _ _ f).
HB.instance Definition _morphop_epi {C: PreCat} (x y: C) (f : x ↠ y)
  := IsMono.Build C^op y x (morphop f) ( @epi_prop _ _ _ f).

Definition pack_epi {C: PreCat} [x y: C] (f : x → y)
  (epi_f: isEpi f): x ↠ y :=
  HB.pack f (IsEpi.Build _ _ _ f epi_f).

Lemma IsEpi_id {C: Cat} (x: C): isEpi ( @idmap _ x).
Proof. exact: (IsMono_id (C := C^op)). Qed.

Lemma IsEpi_comp {C: Cat} [a b c : C] (f: a ↠ b) (g: b ↠ c):
  isEpi (g ∘ f).
Proof. exact: (IsMono_comp (C := C^op) (morphop g) (morphop f)). Qed.

Lemma IsEpi_decomp {C: Cat} [a b c: C] (f: a → b) (e: b → c):
  isEpi (e ∘ f) -> isEpi e.
Proof. exact (IsMono_decomp (C := C^op) e f). Qed.

(** ** Isomorphisms *)
(** *** Definitions *)

(* #[primitive]HB.mixin Record AreInv {C: PreCat} [a b: C] (i: a → b) (j : b → a) :=
  { #[canonical=no] _isoK: i ∘ j = idmap;
    #[canonical=no] _isoK': j ∘ i = idmap }. *)

#[primitive] HB.mixin Record IsIso {C: PreCat} [a b: C] (i: a → b) :=
  { #[canonical=no] inverse: b → a; 
    #[canonical=no] _isoK: i ∘ inverse = idmap;
    #[canonical=no] _isoK': inverse ∘ i = idmap }.

#[short(type="Iso")]
HB.structure Definition iso {C: PreCat} (a b: C) :=
  { f of IsIso _ a b f }.
Arguments Iso {_}.
Arguments inverse {_ _ _}.
Notation "a ↔[ C ] b" := ( @iso.type C a b) (only parsing).
Notation "a ↔ b" := (Iso a b).
Notation isIso i := (IsIso _ _ _ i).

(** forward and backward components *)
Definition forward {C: Cat} [a b: C] (i: Iso a b) := bare i.
Notation "f '¹'" := (forward f).
Notation "f '⁻¹'" := (inverse f).

(** forging isomorphisms *)
Definition pack_iso {C: Cat} [a b: C] (i : a → b) (Hi: isIso i): a ↔ b :=
  HB.pack i Hi.
Definition pack_iso2 {C: Cat} [a b: C] (i : a → b) (j: b → a)
  (ij: i ∘ j = idmap) (ji: j ∘ i = idmap): a ↔ b :=
  pack_iso i (IsIso.Build _ _ _ i j ij ji).

(** restated key properties *)
Lemma isoK {C: Cat} {X Y: C} (i: X ↔ Y): i ∘ i⁻¹ = idmap.
Proof. exact: _isoK. Qed.
Lemma isoK' {C: Cat} {X Y: C} (i: X ↔ Y): i⁻¹ ∘ i = idmap.
Proof. exact: _isoK'. Qed.

(** (self) duality *)
HB.instance Definition _ {C: Cat} (X Y: C) (i: X ↔ Y) := IsIso.Build (C^op) Y X (morphop i) _ (isoK' i) (isoK i). 
Definition iso_op {C: Cat} {X Y: C} (i: X ↔ Y): Y ↔[C^op] X := morphop i.
(* the variant below is not necessary, because [iso_op] works, thanks to precat_IsIso being in precat;
   we keep it in case we need to change this choice *)
Definition iso_op' {C: Cat} {X Y: C} (i: X ↔[C^op] Y): Y ↔[C] X := iso_op i.

Lemma iso_ext {C : Cat} (t t' : C) (f g : t ↔ t') : forward f = forward g -> f = g.
Proof.
  move => e.
  destruct f as [f [[f' Hf Hf']]], g as [g [[g' Hg Hg']]] ; cbn in *.
  move : g' Hg Hg'.
  subst g.
  move => g' Hg Hg'.
  assert (e : g' = f').
  {
    transitivity (g' ∘ f ∘ f').
    - rewrite compoA Hf comp1o //.
    - rewrite Hg' compo1 //.
  }
  move: Hg Hg'.
  subst g'.
  move=> Hg Hg'.
  repeat f_equal.
  all: ext.
Qed.

Smpl Add (apply iso_ext) : extensionality.