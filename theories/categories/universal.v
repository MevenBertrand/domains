(** * Domains.universal: basic universal properties *)
From Stdlib Require Import Program Setoid ssreflect.
From HB Require Import structures.

Require Import notations basics categories.


(**  Categories with terminal objects, which we call terminated categories.

     Such categories have a distinguished object [terminus] (notation [!])
     and a family of morphisms [terminate : A → !] for each object [A].
     Furthermore, [terminate] is universial, in that every for every
     [f : A → !], [f ≈ terminate].
  *)
Module Terminated.
Section terminated.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).

  Definition eq' A B := Eq.Pack _ (eq A B).

  Canonical Structure eq'.

  Record mixin_of :=
  Mixin
  { terminus : ob
  ; terminate : forall A:ob, hom A terminus
  ; axiom : forall A (f:hom A terminus), f ≈ terminate A
  }.
End terminated.
  
Record terminated :=
  Terminated
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin
  }.

Canonical Structure eq (X:terminated) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Canonical Structure comp (X:terminated) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Canonical Structure category (X:terminated) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).

Definition terminus_op (X:terminated) := terminus _ _ _ (mixin X).
Definition terminate_op (X:terminated) := terminate _ _ _ (mixin X).
End Terminated.

Notation terminated := Terminated.terminated.
Notation Terminated := Terminated.Terminated.

Canonical Structure Terminated.eq.
Canonical Structure Terminated.comp.
Canonical Structure Terminated.category.
Coercion Terminated.category : terminated >-> category.

Notation "'!'" := (Terminated.terminus_op _) : category_ob_scope.
Notation "'∗'" := (Terminated.terminate_op _ _) : category_ops_scope.

Lemma terminate_univ (X:terminated) :
  forall (A:X) (f:A → !), f ≈ ∗.
Proof (Terminated.axiom _ _ _ (Terminated.mixin X)).

(** TODO The category of Types is terminated *)

Definition SET_terminus : ob SET := SET.Ob unit (lib_eq _).
Program Definition SET_terminate (A:ob SET) : A → SET_terminus :=
  SET.Hom A SET_terminus (fun x => tt) _.

Program Definition SET_terminated : terminated :=
  Terminated SET.ob SET.hom SET.set_hom_eq SET.set_hom_comp
     SET_obligation_1
     (Terminated.Mixin SET.ob SET.hom SET.set_hom_eq
       SET_terminus SET_terminate _).
Next Obligation.
  hnf. simpl. intro.
  destruct (f x). auto.
Qed.
Canonical Structure SET_terminated.

Definition elem (X:ob SET) (x:X) : ! → X :=
  SET.Hom !%cat_ob X (fun _ => x) (fun a b H => eq_refl _ _).

(**  Categories with initial objects, called initilized categories.

     Such categories have a distinguished object [initium] (notation [¡])
     and a family of morphisms [initiate : ¡ → A] for each object [A].
     Furthermore, [initiate] is universial, in that every for every
     [f : ¡ → A], [f ≈ initiate].
  *)
Module Initialized.
Section initialized.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).

  Definition eq' A B := Eq.Pack _ (eq A B).

  Canonical Structure eq'.

  Record mixin_of :=
  Mixin
  { initium : ob
  ; initiate : forall A:ob, hom initium A
  ; axiom : forall A (f:hom initium A), f ≈ initiate A
  }.
End initialized.
  
Record initialized :=
  Initialized
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin
  }.

Canonical Structure eq (X:initialized) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Canonical Structure comp (X:initialized) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Canonical Structure category (X:initialized) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).

Definition initium_op (X:initialized) := initium _ _ _ (mixin X).
Definition initiate_op (X:initialized) := initiate _ _ _ (mixin X).
End Initialized.

Notation initialized := Initialized.initialized.
Notation Initialized := Initialized.Initialized.

Canonical Structure Initialized.eq.
Canonical Structure Initialized.comp.
Canonical Structure Initialized.category.
Coercion Initialized.category : initialized >-> category.

Notation "'¡'" := (Initialized.initium_op _) : category_ob_scope.
Notation initiate := (Initialized.initiate_op _ _).

Lemma initiate_univ (X:initialized) :
  forall (A:X) (f:¡ → A), f ≈ initiate.
Proof (Initialized.axiom _ _ _ (Initialized.mixin X)).


(**  Cocartesian categories have all finite coproducts.  In particular
     they are initialized and have a binary coproduct for every pair
     of objects satisfying the usual universal property.

     The coproduct of [A] and [B] is written [A + B].  The injection
     functions are [ι₁] and [ι₂].  When we have [f:A → C]  and [g:B → C],
     the case function [either f g : A⊕B → C] is the mediating universal
     morphism for the colimit diagram.
  *)
Module Cocartesian.
Section cocartesian.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.

  Canonical Structure eq'.
  Canonical Structure comp'.

  Section axioms.
    Variable sum : ob -> ob -> ob.
    Variable inl : forall A B, hom A (sum A B).
    Variable inr : forall A B, hom B (sum A B).
    Variable either : forall C A B:ob,
      hom A C -> hom B C -> hom (sum A B) C.

    Record axioms :=
      Axioms
      { inl_commute : forall (C A B:ob) f g,
          either C A B f g ∘ inl A B ≈ f 
      ; inr_commute : forall (C A B:ob) f g,
          either C A B f g ∘ inr A B ≈ g
      ; either_univ : forall (C A B:ob) f g h,
          h ∘ inl A B ≈ f ->
          h ∘ inr A B ≈ g ->
          h ≈ either C A B f g
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { sum : ob -> ob -> ob
  ; inl : forall A B:ob, hom A (sum A B)
  ; inr : forall A B:ob, hom B (sum A B)
  ; either : forall C A B:ob, hom A C -> hom B C -> hom (sum A B) C
  ; cocartesian_axioms : axioms sum inl inr either
  }.
End cocartesian.
  
Record cocartesian :=
  Cocartesian
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin:forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin:Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; init_mixin : Initialized.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin
  }.

Definition sum_op (X:cocartesian) := sum _ _ _ _ (mixin X).
Definition inl_op (X:cocartesian) := inl _ _ _ _ (mixin X).
Definition inr_op (X:cocartesian) := inr _ _ _ _ (mixin X).
Definition either_op (X:cocartesian) := either _ _ _ _ (mixin X).

Definition eq (X:cocartesian) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cocartesian) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition initalized (X:cocartesian) :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (init_mixin X).
Definition category (X:cocartesian) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
End Cocartesian.

Notation cocartesian := Cocartesian.cocartesian.
Notation Cocartesian := Cocartesian.Cocartesian.

Canonical Structure Cocartesian.eq.
Canonical Structure Cocartesian.comp.
Canonical Structure Cocartesian.category.
Canonical Structure Cocartesian.initalized.

Coercion Cocartesian.initalized : cocartesian >-> initialized.
Coercion Cocartesian.category : cocartesian >-> category.

Notation "A + B" := (Cocartesian.sum_op _ A B)
  : category_ob_scope.
Notation "'ι₁'"  := (Cocartesian.inl_op _ _ _) : category_ops_scope.
Notation "'ι₂'"  := (Cocartesian.inr_op _ _ _) : category_ops_scope.
Notation either := Cocartesian.either_op.
Arguments either [X C A B] f g.

Lemma inl_commute (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C), either f g ∘ ι₁ ≈ f.

Proof (Cocartesian.inl_commute _ _ _ _ _ _ _ _ 
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Lemma inr_commute (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C), either f g ∘ ι₂ ≈ g.

Proof (Cocartesian.inr_commute _ _ _ _ _ _ _ _ 
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Lemma either_univ (X:cocartesian) :
  forall (C A B:ob X) (f:A → C) (g:B → C) (h:A+B → C),
  h ∘ ι₁ ≈ f -> h ∘ ι₂ ≈ g -> h ≈ either f g.

Proof (Cocartesian.either_univ _ _ _ _ _ _ _ _
         (Cocartesian.cocartesian_axioms _ _ _ _ (Cocartesian.mixin X))).

Program Definition sum_map (X:cocartesian) (A B C D:ob X)
  (f:A → B) (g:C → D) : A+C → B+D := either (ι₁ ∘ f) (ι₂ ∘ g).
Arguments sum_map [X A B C D] f g.

Add Parametric Morphism (X:cocartesian) (C A B:ob X) :
  (@Cocartesian.either_op X C A B)
   with signature (eq_op (Cocartesian.eq X A C)) ==>
                  (eq_op (Cocartesian.eq X B C)) ==>
                  (eq_op (Cocartesian.eq X (A+B)%cat_ob C))
    as either_morphism.
Proof.
  intros. apply either_univ.
  rewrite <- H. apply inl_commute.
  rewrite <- H0. apply inr_commute.
Qed.

(**  Cartesian categories have all finite products.  In particular
     they are terminated and have a binary product for every pair
     of objects satisfying the usual universal property.

     The product of [A] and [B] is written [A × B].  The projection
     functions are [π₁] and [π₂].  When we have [f:C → A]  and [g:C → B],
     the pairing function [〈 f, g 〉 : C → A×B] is the mediating universal
     morphism for the limit diagram.
  *)
Module Cartesian.
Section cartesian.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.

  Canonical Structure eq'.
  Canonical Structure comp'.

  Section axioms.

    Variable product : ob -> ob -> ob.
    Variable proj1 : forall A B, hom (product A B) A.
    Variable proj2 : forall A B, hom (product A B) B.
    Variable pairing : forall C A B:ob, hom C A -> hom C B -> hom C (product A B).

    Record axioms :=
      Axioms
      { proj1_commute : forall (C A B:ob) f g,
          proj1 A B ∘ pairing C A B f g ≈ f
      ; proj2_commute : forall (C A B:ob) f g,
          proj2 A B ∘ pairing C A B f g ≈ g
      ; pairing_univ : forall (C A B:ob) f g h,
          proj1 A B ∘ h ≈ f ->
          proj2 A B ∘ h ≈ g ->
          h ≈ pairing C A B f g
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { product : ob -> ob -> ob
  ; proj1 : forall A B:ob, hom (product A B) A
  ; proj2 : forall A B:ob, hom (product A B) B
  ; pairing : forall C A B:ob, hom C A -> hom C B -> hom C (product A B)
  ; cartesian_axioms : axioms product proj1 proj2 pairing
  }.
End cartesian.
  
Record cartesian :=
  Cartesian
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin:forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin:Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; term_mixin : Terminated.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin
  }.

Definition product_op (X:cartesian) := product _ _ _ _ (mixin X).
Definition proj1_op (X:cartesian) := proj1 _ _ _ _ (mixin X).
Definition proj2_op (X:cartesian) := proj2 _ _ _ _ (mixin X).
Definition pairing_op (X:cartesian) := pairing _ _ _ _ (mixin X).

Definition eq (X:cartesian) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cartesian) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition terminated (X:cartesian) :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (term_mixin X).
Definition category (X:cartesian) :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
End Cartesian.

Notation cartesian := Cartesian.cartesian.
Notation Cartesian := Cartesian.Cartesian.

Canonical Structure Cartesian.eq.
Canonical Structure Cartesian.comp.
Canonical Structure Cartesian.category.
Canonical Structure Cartesian.terminated.

Coercion Cartesian.terminated : cartesian >-> terminated.
Coercion Cartesian.category : cartesian >-> category.

Notation "A × B" := (Cartesian.product_op _ A B)
  : category_ob_scope.
Notation "'π₁'"  := (Cartesian.proj1_op _ _ _) : category_ops_scope.
Notation "'π₂'"  := (Cartesian.proj2_op _ _ _) : category_ops_scope.
Notation "〈 f , g 〉" := (Cartesian.pairing_op _ _ _ _ f g)
  : category_ops_scope.

Lemma proj1_commute (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B), π₁ ∘ 〈 f, g 〉 ≈ f.

Proof (Cartesian.proj1_commute _ _ _ _ _ _ _ _ 
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Lemma proj2_commute (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B), π₂ ∘ 〈 f, g 〉 ≈ g.

Proof (Cartesian.proj2_commute _ _ _ _ _ _ _ _ 
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Lemma pairing_univ (X:cartesian) :
  forall (C A B:ob X) (f:C → A) (g:C → B) (h:C → A × B),
  π₁ ∘ h ≈ f -> π₂ ∘ h ≈ g -> h ≈ 〈 f, g 〉.

Proof (Cartesian.pairing_univ _ _ _ _ _ _ _ _
         (Cartesian.cartesian_axioms _ _ _ _ (Cartesian.mixin X))).

Program Definition pair_map (X:cartesian) (A B C D:ob X)
  (f:A → B) (g:C → D) : A×C → B×D :=
  〈 f ∘ π₁, g ∘ π₂ 〉.
Arguments pair_map [X A B C D] f g.

Add Parametric Morphism (X:cartesian) (C A B:ob X) :
  (Cartesian.pairing_op X C A B)
   with signature (eq_op (Cartesian.eq X C A)) ==>
                  (eq_op (Cartesian.eq X C B)) ==>
                  (eq_op (Cartesian.eq X C (A×B)%cat_ob))
    as pairing_morphism.
Proof.
  intros. apply pairing_univ.
  rewrite proj1_commute. auto.
  rewrite proj2_commute. auto.
Qed.


(**  A distributive category has binary products and binary coproducts,
     and sums distribute over products. 
  *)
Module Distributive.
Section distributive.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms : Category.axioms ob hom eq comp.
  Variable terminated : Terminated.mixin_of ob hom eq.
  Variable cartesian : Cartesian.mixin_of ob hom eq comp.
  Variable initialized : Initialized.mixin_of ob hom eq.
  Variable cocartesian : Cocartesian.mixin_of ob hom eq comp.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.
  Definition cartesian' := Cartesian ob hom eq comp cat_axioms terminated cartesian.
  Definition cocartesian' := Cocartesian ob hom eq comp cat_axioms initialized cocartesian.

  Canonical Structure eq'.
  Canonical Structure comp'.
  Canonical Structure cartesian'.
  Canonical Structure cocartesian'.

  Record mixin_of :=
  { distrib_law : forall A B C:ob, A×(B+C) ↔ (A×B) + (A×C)
  }.

End distributive.

Record distributive :=
  Distributive
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; initialized_mixin : Initialized.mixin_of ob hom eq_mixin
  ; cocartesian_mixin : Cocartesian.mixin_of ob hom eq_mixin comp_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin cat_axioms terminated_mixin cartesian_mixin initialized_mixin cocartesian_mixin
  }.

Definition distrib_law_op (X:distributive) :=
   distrib_law _ _ _ _ _ _ _ _ _ (mixin X).

Definition eq (X:distributive) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:distributive) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:distributive) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:distributive) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (terminated_mixin X).
Definition cartesian (X:distributive) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
Definition initialized (X:distributive) : initialized :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (initialized_mixin X).
Definition cocartesian (X:distributive) : cocartesian :=
  Cocartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (initialized_mixin X) (cocartesian_mixin X).
End Distributive.
  
Notation distributive := Distributive.distributive.
Notation Distributive := Distributive.Distributive.

Canonical Structure Distributive.eq.
Canonical Structure Distributive.comp.
Canonical Structure Distributive.category.
Canonical Structure Distributive.terminated.
Canonical Structure Distributive.cartesian.
Canonical Structure Distributive.initialized.
Canonical Structure Distributive.cocartesian.

Coercion Distributive.category : distributive >-> category.
Coercion Distributive.terminated : distributive >-> terminated.
Coercion Distributive.cartesian : distributive >-> cartesian.
Coercion Distributive.initialized : distributive >-> initialized.
Coercion Distributive.cocartesian : distributive >-> cocartesian.

Notation distrib_law := Distributive.distrib_law_op.
Arguments distrib_law {X A B C}.

(**  Cartesian closed categories, in addition to being cartesian,
     have "internal" hom objects corresponding to each homset called
     the exponential object.  Here we give the definition of cartesian
     closure in terms of curry and apply morphisms.
     
     When [A] and [B] are objects, [A ⇒ B] is the exponential object.
     The morphism [apply : (A⇒B) × A → B] applies an internal hom
     to an argument.  For [f : C×A → B], we have a unique curried
     morphism [Λ f : C → A⇒B] that commutes with the action of [apply].
  *)
Module CartesianClosed.
Section cartesian_closed.
  Variables (ob:Type) (hom:ob -> ob -> Type).
  Variable eq:forall A B:ob, Eq.mixin_of (hom A B).
  Variable comp:Comp.mixin_of ob hom.
  Variable cat_axioms : Category.axioms ob hom eq comp.
  Variable terminated : Terminated.mixin_of ob hom eq.
  Variable cartesian : Cartesian.mixin_of ob hom eq comp.
  
  Definition eq' A B := Eq.Pack _ (eq A B).
  Definition comp' := Comp.Pack ob hom comp.
  Definition cartesian' := Cartesian ob hom eq comp cat_axioms terminated cartesian.

  Canonical Structure eq'.
  Canonical Structure comp'.
  Canonical Structure cartesian'.

  Section axioms.
    Variable exp : ob -> ob -> ob.
    Variable curry : forall C A B, (C×A → B) -> (C → exp A B).
    Variable apply : forall A B, exp A B × A → B.

    Record axioms :=
      Axioms
      { curry_commute : forall C A B (f:C×A → B),
           apply A B ∘ 〈 curry C A B f ∘ π₁, π₂ 〉 ≈ f
      ; curry_univ : forall C A B (f:C×A → B) (f':C → exp A B),
           apply A B ∘ 〈 f' ∘ π₁, π₂ 〉 ≈ f ->
           f' ≈ curry C A B f
      }.
  End axioms.

  Record mixin_of :=
  Mixin
  { exp : ob -> ob -> ob
  ; curry : forall C A B, (C×A → B) -> (C → exp A B)
  ; apply : forall A B, exp A B × A → B
  ; ccc_axioms : axioms exp curry apply
  }.
End cartesian_closed.

Record cartesian_closed :=
  CartesianClosed
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; mixin : mixin_of ob hom eq_mixin comp_mixin cat_axioms terminated_mixin cartesian_mixin
  }.

Definition curry_op (X:cartesian_closed) := curry _ _ _ _ _ _ _ (mixin X).
Definition apply_op (X:cartesian_closed) := apply _ _ _ _ _ _ _ (mixin X).
Definition exp_op (X:cartesian_closed) := exp _ _ _ _ _ _ _ (mixin X).

Definition eq (X:cartesian_closed) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:cartesian_closed) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:cartesian_closed) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:cartesian_closed) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) (terminated_mixin X).
Definition cartesian (X:cartesian_closed) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
End CartesianClosed.
  
Notation cartesian_closed := CartesianClosed.cartesian_closed.
Notation CartesianClosed := CartesianClosed.CartesianClosed.

Canonical Structure CartesianClosed.eq.
Canonical Structure CartesianClosed.comp.
Canonical Structure CartesianClosed.category.
Canonical Structure CartesianClosed.terminated.
Canonical Structure CartesianClosed.cartesian.

Coercion CartesianClosed.category : cartesian_closed >-> category.
Coercion CartesianClosed.terminated : cartesian_closed >-> terminated.
Coercion CartesianClosed.cartesian : cartesian_closed >-> cartesian.

Notation "'Λ' f" := (CartesianClosed.curry_op _ _ _ _ f) : category_ops_scope.
Notation "A ⇒ B" := (CartesianClosed.exp_op _ A B)
  : category_ob_scope.
Notation apply := (CartesianClosed.apply_op _ _ _).

Lemma curry_commute (X:cartesian_closed) : 
  forall (C A B:ob X) (f:C×A → B), apply ∘ 〈 Λ f ∘ π₁, π₂ 〉 ≈ f.

Proof (CartesianClosed.curry_commute _ _ _ _ _ _ _ _ _ _
         (CartesianClosed.ccc_axioms _ _ _ _ _ _ _ (CartesianClosed.mixin X))).

Lemma curry_univ (X:cartesian_closed) :
  forall (C A B:ob X) (f:C×A → B) (f':C → A ⇒ B),
          apply ∘ 〈 f' ∘ π₁, π₂ 〉 ≈ f -> f' ≈ Λ f.

Proof (CartesianClosed.curry_univ _ _ _ _ _ _ _ _ _ _
         (CartesianClosed.ccc_axioms _ _ _ _ _ _ _ (CartesianClosed.mixin X))).

Add Parametric Morphism (X:cartesian_closed) (C A B:ob X) :
  (CartesianClosed.curry_op X C A B)
  with signature (eq_op (CartesianClosed.eq X (C×A)%cat_ob B)) ==>
                 (eq_op (CartesianClosed.eq X C (A⇒B)%cat_ob))
   as curry_morphism.
Proof.
  intros. apply curry_univ. rewrite curry_commute. auto.
Qed.

Lemma curry_commute3 (X:cartesian_closed) : 
  forall (D C A B:X) (f:C×A → B) (g:D → C) (h:D → A),
    apply ∘ 〈 Λ f ∘ g, h 〉 ≈ f ∘ 〈 g, h 〉.
Proof.
  intros.
  transitivity (apply ∘ 〈Λ f ∘ π₁, π₂〉 ∘ 〈g, h〉).
  - rewrite <- (cat_assoc X). apply (cat_respects X); auto.
    symmetry. apply pairing_univ.
    + rewrite (cat_assoc X).
      transitivity (Λ(f) ∘ π₁ ∘ 〈g,h〉).
      * apply cat_respects; auto.
        apply (proj1_commute X).
      * rewrite <- (cat_assoc X).
        apply cat_respects; auto.
        apply proj1_commute.
    + rewrite (cat_assoc X).
      transitivity (π₂ ∘ 〈g,h〉).
      * apply cat_respects; auto.
        apply (proj2_commute X).
      * apply (proj2_commute X).
  - apply cat_respects; auto.
    apply curry_commute.
Qed.

Lemma curry_commute2 (X:cartesian_closed) : 
  forall (C A B:X) (f:C×A → B) (h:C → A),
    apply ∘ 〈 Λ f, h 〉 ≈ f ∘ 〈 id, h 〉.
Proof.
  intros. rewrite <- (curry_commute3 X C C A B f id h).
  apply cat_respects; auto.
  apply pairing_morphism; auto.
  symmetry. apply cat_ident1.
Qed.

(**  Here I define "polynomial categories" as categories with finite sums,
     finite products, and exponents where sums distribute over products.

     As far as I know, this terminology is not already taken.
  *)
Module PolynomialCategory.

Record polynomial_category :=
  PolynomialCategory
  { ob : Type
  ; hom : ob -> ob -> Type
  ; eq_mixin : forall A B:ob, Eq.mixin_of (hom A B)
  ; comp_mixin : Comp.mixin_of ob hom
  ; cat_axioms : Category.axioms ob hom eq_mixin comp_mixin
  ; terminated_mixin : Terminated.mixin_of ob hom eq_mixin
  ; cartesian_mixin : Cartesian.mixin_of ob hom eq_mixin comp_mixin
  ; initialized_mixin : Initialized.mixin_of ob hom eq_mixin
  ; cocartesian_mixin : Cocartesian.mixin_of ob hom eq_mixin comp_mixin
  ; ccc_mixin : CartesianClosed.mixin_of ob hom eq_mixin comp_mixin 
       cat_axioms terminated_mixin cartesian_mixin
  ; distributive_mixin : Distributive.mixin_of ob hom eq_mixin comp_mixin
       cat_axioms terminated_mixin cartesian_mixin
                  initialized_mixin cocartesian_mixin
  }.

Definition eq (X:polynomial_category) (A B:ob X) :=
  Eq.Pack (hom X A B) (eq_mixin X A B).
Definition comp (X:polynomial_category) :=
  Comp.Pack (ob X) (hom X) (comp_mixin X).
Definition category (X:polynomial_category) : category :=
  Category (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X).
Definition terminated (X:polynomial_category) : terminated :=
  Terminated (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
     (terminated_mixin X).
Definition cartesian (X:polynomial_category) : cartesian :=
  Cartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (terminated_mixin X) (cartesian_mixin X).
Definition initialized (X:polynomial_category) : initialized :=
  Initialized (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
     (initialized_mixin X).
Definition cocartesian (X:polynomial_category) : cocartesian :=
  Cocartesian (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
     (initialized_mixin X) (cocartesian_mixin X).
Definition cartesian_closed (X:polynomial_category) : cartesian_closed :=
  CartesianClosed (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X) 
      (cartesian_mixin X) (terminated_mixin X) (ccc_mixin X).
Definition distributive (X:polynomial_category) : distributive :=
  Distributive (ob X) (hom X) (eq_mixin X) (comp_mixin X) (cat_axioms X)
      (terminated_mixin X) (cartesian_mixin X)
      (initialized_mixin X) (cocartesian_mixin X)
      (distributive_mixin X).
End PolynomialCategory.

Notation polynomial_category := PolynomialCategory.polynomial_category.
Notation PolynomialCategory := PolynomialCategory.PolynomialCategory.

Canonical Structure PolynomialCategory.eq.
Canonical Structure PolynomialCategory.comp.
Canonical Structure PolynomialCategory.category.
Canonical Structure PolynomialCategory.terminated.
Canonical Structure PolynomialCategory.cartesian.
Canonical Structure PolynomialCategory.initialized.
Canonical Structure PolynomialCategory.cocartesian.
Canonical Structure PolynomialCategory.cartesian_closed.
Canonical Structure PolynomialCategory.distributive.

Coercion PolynomialCategory.category : polynomial_category >-> category.
Coercion PolynomialCategory.terminated : polynomial_category >-> terminated.
Coercion PolynomialCategory.cartesian : polynomial_category >-> cartesian.
Coercion PolynomialCategory.initialized : polynomial_category >-> initialized.
Coercion PolynomialCategory.cocartesian : polynomial_category >-> cocartesian.
Coercion PolynomialCategory.cartesian_closed : polynomial_category >-> cartesian_closed.
Coercion PolynomialCategory.distributive : polynomial_category >-> distributive.

(**  Here we define pullbacks in the direct style.
  *)
Module Pullback.
Section pullback.
  Variable C:category.

  Definition commuting_square (X Y Z W:ob C) 
    (f:X → Z) (g:Y → Z)
    (f':W → Y) (g': W → X) :=
      g ∘ f' ≈ f ∘ g'.

  Record square  (X Y Z W:ob C) 
    (f:X → Z) (g:Y → Z)
    (f':W → Y) (g': W → X) :=
    Square
    { commute : commuting_square X Y Z W f g f' g'
    ; map : forall Q p q,
           commuting_square X Y Z Q f g p q ->
           Q → W
    ; axiom1 : forall Q p q H,
           g' ∘ map Q p q H ≈ q
    ; axiom2 : forall Q p q H,
           f' ∘ map Q p q H ≈ p
    ; uniq : forall Q p q H k,
           f ∘ g' ∘ k ≈ f ∘ q -> k ≈ map Q p q H
    }.

  Record pullback (X Y Z:ob C) (f:X → Z) (g:Y → Z) :=
    Pullback
    { pb_ob : ob C
    ; pb_f : pb_ob → Y
    ; pb_g : pb_ob → X
    ; is_pullback : square X Y Z pb_ob f g pb_f pb_g
    }.
End pullback.

Arguments commuting_square [C] [X] [Y] [Z] [W] f g f' g'.
Arguments square [C] [X] [Y] [Z] [W] f g f' g'.
Arguments Square [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments pullback [C] [X] [Y] [Z] f g.
Arguments Pullback [C] [X] [Y] [Z] [f] [g] _ _ _ _.
Arguments commute [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _.
Arguments map [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ [Q] _ _ _.
Arguments axiom1 [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments axiom2 [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _.
Arguments uniq [C] [X] [Y] [Z] [W] [f] [g] [f'] [g'] _ _ _ _ _ _ _.
Arguments pb_ob [C] [X] [Y] [Z] [f] [g] _.
Arguments pb_f [C] [X] [Y] [Z] [f] [g] _.
Arguments pb_g [C] [X] [Y] [Z] [f] [g] _.
Arguments is_pullback [C] [X] [Y] [Z] [f] [g] _.

Section pullback_lemma.
  Variable C:category.

  (**  The pullback lemma proved here is that, given objects and
       morphisms as in the below diagram; if both of the inner
       diagrams are pullbacks then the outer diagram is a pullback.

<<
        f1 
     R ----> S
     |       |
  g1 |       | h1
     v  f2   v
     W ----> Y
     |       |
  g2 |       | h2
     V  f3   v
     X ----> Z
>>
  *)

  Variables X Y Z W R S:ob C.
  Variable f1:R → S.
  Variable f2:W → Y.
  Variable f3:X → Z.
  Variable g1:R → W.
  Variable g2:W → X.
  Variable h1:S → Y.
  Variable h2:Y → Z.

  Section pullback_lemma1.
    Variable PB1: Pullback.square f2 h1 f1 g1.
    Variable PB2: Pullback.square f3 h2 f2 g2.

    Section pb_map.
    Variable Q:ob C.
    Variable p:Q → S.
    Variable q:Q → X.
    Variable H:commuting_square f3 (h2 ∘ h1) p q.

    Lemma pb_lemma1_comm : commuting_square f3 h2 (h1 ∘ p) q.
    Proof.
      red. red in H.
      rewrite <- H.
      apply cat_assoc.
    Qed.

    Definition pullback_lemma1_map1 : Q → W :=
      Pullback.map PB2 (h1 ∘ p) q pb_lemma1_comm.

    Program Definition pullback_lemma_map2 : Q → R :=
      Pullback.map PB1 p pullback_lemma1_map1 _.
    Next Obligation.
      red. red in H.
      generalize (axiom2 PB2 _ _ _ pb_lemma1_comm).  intro.
      auto.
    Qed.      
    End pb_map.

    Program Definition pullback_lemma1 : square f3 (h2 ∘ h1) f1 (g2 ∘ g1) :=
      Square _ (fun Q p q H => pullback_lemma_map2 Q p q H) _ _ _ .
    Next Obligation.
      red.
      generalize (commute PB1). generalize (commute PB2).
      simpl; intros.
      red in H; red in H0.
      etransitivity.
      - symmetry. apply cat_assoc.
      - rewrite H0.
        etransitivity. apply cat_assoc.
        rewrite H.
        symmetry. apply cat_assoc.
    Qed.      
    Next Obligation.
      unfold pullback_lemma_map2.
      etransitivity.
      - symmetry. apply cat_assoc.
      - generalize (axiom1 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
        intros. rewrite H0.
        apply (axiom1 PB2).
    Qed.
    Next Obligation.
      apply (axiom2 PB1 _ p _ (pullback_lemma_map2_obligation_1 Q p q H)).
    Qed.
    Next Obligation.
      assert (g1 ∘ k ≈ pullback_lemma1_map1 Q p q H).
      { apply (uniq PB2).
        rewrite <- H0.
        rewrite <- (cat_assoc _ _ _ _ _ f3 g2 _).
        rewrite <- (cat_assoc _ _ _ _ _ f3 (g2 ∘ g1) _).
        apply cat_respects; auto.
        apply cat_assoc.
      }
      apply (uniq PB1).
      rewrite <- (cat_assoc _ _ _ _ _ f2 g1 _).
      rewrite H1. auto.
    Qed.      
  End pullback_lemma1.
End pullback_lemma.

End Pullback.

Notation pullback := Pullback.pullback.
Notation Pullback := Pullback.Pullback.