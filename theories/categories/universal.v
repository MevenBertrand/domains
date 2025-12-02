(** * Domains.universal: basic universal properties *)
From Stdlib Require Import ssreflect ssrfun.
From HB Require Import structures.

Require Import notations axioms basics categories morphisms functors.

Set Primitive Projections.

#[local] Open Scope cat_scope.

(** ** Categories with terminal objects

     Such categories have a distinguished object [terminus] (notation [!])
     and a family of morphisms [terminate : A → !] for each object [A].
     Furthermore, [terminate] is universial, in that for every
     [f : A → !], [f = terminate].
  *)

(* #[primitive] HB.mixin Record IsTerminal {C : Quiver} (t : C) := {
    terminal_fun : forall x, x → t ;
    term_unique : forall x (f : x → t), f = (terminal_fun x) ;
  }.
#[short(type="Terminal"),primitive]
HB.structure Definition terminal {C : Quiver} := { t of IsTerminal C t}. *)

#[primitive] HB.mixin Record IsPreTerminated C of quiver C := {
  terminus : C ;
}.

#[short(type="PreTerminated")]
HB.structure Definition preterm := { T of quiver T & IsPreTerminated T}.

Notation "'!'" := (terminus) : cat_scope.

#[primitive] HB.mixin Record IsTerminated (C : Type) of preterm C := {
  terminate : forall (x : C), x → ! ;
  termU : forall (x : C) (f : x → !), f = (terminate x)
}.

#[short(type="Terminated"),primitive]
HB.structure Definition terminated := { C of preterm C & IsTerminated C}.

Arguments terminate {_ _}.

Goal forall {C : Terminated} (x : C) (f : x → !), f = terminate.
Proof.
  intros ; apply termU.
Qed.

(* Program Definition terminalI {C : Cat} (t t' : Terminal C) :
  (Σ! h : (terminal.sort _ t) ↔ (terminal.sort _ t'), True).
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    1: exact terminate.
    do 2 (unshelve econstructor).
    1: exact terminate.
    all: etransitivity ; [|symmetry].
    all: apply term_unique.
  - split => //.
    move => g _.
    apply iso_ext => /=.
    apply term_unique.
Qed. *)

(* TODO The category of Types is terminated *)

(* Definition elem (X:ob SET) (x:X) : ! → X :=
  SET.Hom !%cat_ob X (fun _ => x) (fun a b H => eq_refl _ _). *)

(** ** Categories with initial objects

     Such categories have a distinguished object [init] (notation [¡])
     and a family of morphisms [initiate : ¡ → A] for each object [A].
     Furthermore, [initiate] is universal, in that every for every
     [f : ¡ → A], [f = initiate].
  *)

(* #[primitive] HB.mixin Record IsInitial {C : Quiver} (t : C) := {
    initial_fun : forall x, t → x ;
    initialU : forall x (f : t → x), f = (initial_fun x) ;
  }.
#[short(type="Initial"),primitive]
HB.structure Definition initial {C : Quiver} := { t of IsInitial C t}. *)

#[primitive] HB.mixin Record IsPreInitialised C of quiver C := {
  initium : C ;
}.

#[short(type="PreInitialised")]
HB.structure Definition preinit := { T of quiver T & IsPreInitialised T}.

Notation "'¡'" := (initium) : cat_scope.

#[primitive] HB.mixin Record IsInitialised (C : Type) of preinit C := {
  initiate : forall (x : C), ¡ → x ;
  initU : forall (x : C) (f : ¡ → x), f = (initiate x)
}.

#[short(type="Initialised"),primitive]
HB.structure Definition initialised := { C of preinit C & IsInitialised C}.

Arguments initiate {_ _}.

(* Program Definition initialI {C : Cat} (t t' : Initial C) :
  (Σ! h : (initial.sort _ t) ↔ (initial.sort _ t'), True).
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    1: exact initiate.
    do 2 (unshelve econstructor).
    1: exact initiate.
    all: etransitivity ; [|symmetry].
    all: apply initialU.
  - split => //.
    move => g _.
    apply iso_ext => /=.
    apply initialU.
Qed. *)

(** ** Finite coproducts

    The coproduct of [A] and [B] is written [A + B].  The injection
    functions are [ι₁] and [ι₂].  When we have [f:A → C]  and [g:B → C],
    the case function [either f g : A+B → C] is the mediating universal
    morphism for the colimit diagram.

    Cocartesian categories have all finite coproducts:
    they are initialized and have all binary coproducts.
  *)

(* #[primitive] HB.mixin Record IsSum {C : PreCat} (a b : C) (t : C) := {
    sum_inlU : a → t ;
    sum_inrU : b → t ;
    eitherU : forall x, a → x -> b → x -> t → x ;
    inlK : forall x f g, (eitherU x f g) ∘ sum_inlU = f ; 
    inrK : forall x f g, (eitherU x f g) ∘ sum_inrU = g ;
    sumU : forall x f g h, h ∘ sum_inlU = f -> h ∘ sum_inrU = g -> h = eitherU x f g
  }.
#[short(type="Sum"),primitive]
HB.structure Definition sum {C : PreCat} (a b : C) := { t of IsSum C a b t}. *)

#[primitive] HB.mixin Record ObjHasSums C := {
  cat_sum : C -> C -> C
}.

#[short(type="ObjSums"),primitive]
HB.structure Definition obj_sums := { T of ObjHasSums T}.

Notation "A + B" := (cat_sum A B) : cat_scope.

#[primitive] HB.mixin Record MorHasSums C of quiver C & obj_sums C := {
  sum_inl : forall {a b : C}, a → a + b ;
  sum_inr : forall {a b : C}, b → a + b ;
  either : forall {a b x : C}, a → x -> b → x -> a + b → x
}.

#[short(type="MorSums"),primitive]
HB.structure Definition mor_sums := { T of quiver T & obj_sums T & MorHasSums T}.

Notation "'ι₁'" := (sum_inl _ _) : cat_scope.
Notation "'ι₂'" := (sum_inr _ _) : cat_scope.
Arguments either {_ _ _ _} _ _.

#[primitive] HB.mixin Record HasSums C of precat C & mor_sums C := {
  inlK : forall {a b x : C} {f : a → x} {g : b → x}, (either f g) ∘[C] ι₁ = f ; 
  inrK : forall {a b x : C} {f : a → x} {g : b → x}, (either f g) ∘[C] ι₂ = g ;
  sumU : forall {a b x : C} {f : a → x} {g : b → x} {h : a + b → x},
    h ∘[C] ι₁ = f -> h ∘[C] ι₂ = g -> h = either f g
}.

#[short(type="CoCartesian"),primitive]
HB.structure Definition cocartesian := {
    C of cat C & terminated C & mor_sums C & HasSums C}.

Definition sum_map {X:CoCartesian} {a b c d: X}
  (f:a → b) (g:c → d) : a+c → b+d := either (ι₁ ∘ f) (ι₂ ∘ g).

(** ** Finite products

    The product of [A] and [B] is written [A × B].  The projection
    functions are [π₁] and [π₂].  When we have [f:C → A]  and [g:C → B],
    the pairing function [⟨ f, g ⟩ : C → A×B] is the mediating universal
    morphism for the limit diagram.

  Cartesian categories have all finite products:
  they are finalized and have all binary products.
*)

(* #[primitive] HB.mixin Record IsProd {C : PreCat} (a b : C) (t : C) := {
    prod_projlU : t → a ;
    prod_projrU : t → b ;
    pairingU : forall x, x → a -> x → b -> x → t ;
    projlK : forall x f g, prod_projlU ∘ (pairingU x f g) = f ; 
    projrK : forall x f g, prod_projrU ∘ (pairingU x f g) = g ; 
    prodU : forall x f g h, prod_projlU ∘ h = f -> prod_projrU ∘ h = g -> h = pairingU x f g
  }.

#[short(type="Prod"),primitive]
HB.structure Definition prod {C : PreCat} (a b : C) := { t of IsProd C a b t}. *)

#[primitive] HB.mixin Record ObjHasProds C := {
  cat_prod : C -> C -> C
}.

#[short(type="ObjProds"),primitive]
HB.structure Definition obj_prods := { T of ObjHasProds T}.

Notation "A × B" := (cat_prod A B) : cat_scope.

#[primitive] HB.mixin Record MorHasProds C of quiver C & obj_prods C := {
  prod_projl : forall {a b : C}, a × b → a ;
  prod_projr : forall {a b : C}, a × b → b ;
  pairing : forall {a b x : C}, x → a -> x → b -> x → a × b
}.

#[short(type="MorProds"),primitive]
HB.structure Definition mor_prods := { T of quiver T & obj_prods T & MorHasProds T}.

Notation "'π₁'" := (prod_projl  _ _) : cat_scope.
Notation "'π₂'" := (prod_projr _ _) : cat_scope.
Notation "⟨ f , g ⟩" := (pairing _ _ _ f g) : cat_scope.

#[primitive] HB.mixin Record HasProds C of precat C & mor_prods C := {
  projlK : forall {a b x : C} {f : x → a} {g : x → b}, π₁ ∘[C] ⟨f,g⟩ = f ; 
  projrK : forall {a b x : C} {f : x → a} {g : x → b}, π₂ ∘[C] ⟨f,g⟩ = g ; 
  prodU : forall {a b x : C} {f : x → a} {g : x → b} {h : x → a × b},
    π₁ ∘[C] h = f -> π₂ ∘[C] h = g -> h = ⟨f,g⟩
}.

#[short(type="Cartesian"),primitive]
HB.structure Definition cartesian := {
    C of cat C & initialised C & mor_prods C & HasProds C}.

Definition prod_map {X:Cartesian} {a b c d: X}
  (f:a → b) (g:c → d) : a×c → b×d := ⟨ f ∘ π₁ , g ∘ π₂ ⟩.

(**  ** Distributive category

    A distributive category has binary products and binary coproducts,
    and sums distribute over products. 
  *)

#[primitive] HB.mixin Record IsDistributive C of cat C & cocartesian C & cartesian C := {
  distr : forall (a b c : C), a × (b + c) ↔ (a × b) + (a × c)
}.

#[short(type="Distributive"),primitive]
  HB.structure Definition distributive :=
    { C of cat C & cartesian C & cocartesian C & IsDistributive C}.

(**  Cartesian closed categories

    In addition to being cartesian,
    have "internal" hom objects corresponding to each homset called
    the exponential object.  Here we give the definition of cartesian
    closure in terms of curry and apply morphisms.
     
    When [A] and [B] are objects, [A ⇒ B] is the exponential object.
    The morphism [apply : (A⇒B) × A → B] applies an internal hom
    to an argument.  For [f : C×A → B], we have a unique curried
    morphism [curry f : C → A⇒B] that commutes with the action of [apply].
  *)

(* #[primitive] HB.mixin Record IsExp {C : Cartesian} (a b : C) (t : C) := {
    evalU : t × a → b ;
    curryU : forall x, ((x × a) → b) -> x → t ;
    evalK : forall x (f : (x × a) → b), evalU ∘ (prod_map (curryU _ f) idmap) = f ;
    expU : forall x (f : (x × a) → b) (h : x → t), evalU ∘ (prod_map h idmap) = f -> h = curryU _ f
  }.

#[short(type="Exp"),primitive]
HB.structure Definition exp {C : Cartesian} (a b : C) := { t of IsExp C a b t}. *)

#[primitive] HB.mixin Record ObjHasExps C := {
  cat_exp : C -> C -> C
}.

#[short(type="ObjExps"),primitive]
HB.structure Definition obj_exps := { T of ObjHasProds T & ObjHasExps T}.

Notation "a ⇒ b" := (cat_exp a b) : cat_scope.

#[primitive] HB.mixin Record MorHasExps C of quiver C & obj_exps C := {
  eval : forall (a b : C), cat_prod (a ⇒ b) a →[C] b ;
  curry : forall (a b x : C), (x × a → b) -> x → (a ⇒ b)
}.

#[short(type="MorExps"),primitive]
HB.structure Definition mor_exps := {
    T of quiver T & obj_exps T & MorHasProds T & MorHasExps T}.

Arguments eval {_ _ _}.
Arguments curry {_ _ _ _} _.

#[primitive] HB.mixin Record HasExps C of cartesian C & mor_exps C := {
  evalK : forall (a b x : C) (f : (x × a) → b),
    eval ∘[C] (prod_map (curry f) idmap) = f ;
  expU : forall (a b x : C) (f : (x × a) → b) (h : x → (a ⇒ b)),
    eval ∘ (prod_map h idmap) = f -> h = curry f
}.

#[short(type="CartesianClosed"),primitive]
HB.structure Definition cartesian_closed := { C of cartesian C & mor_exps C & HasExps C}.

(* Disable Notation "'π₁'".
Disable Notation "'π₂'".
Disable Notation "⟨ f , g ⟩". *)

Lemma curry_commute3 (X:CartesianClosed) : 
  forall (d c a b:X) (f:c×a → b) (g:d → c) (h:d → a),
    eval ∘ ⟨ curry f ∘ g, h ⟩ = f ∘ ⟨ g, h ⟩.
Proof.
  intros.
  (* transitivity (eval ∘ ⟨curry f ∘ π₁, π₂⟩ ∘ ⟨ g, h⟩). *)
  transitivity (comp (⟨(curry f) ∘ π₁, π₂⟩ ∘ ⟨g,h⟩) eval).
  - f_equal.
    symmetry.
    apply (prodU _ (curry f ∘ g) _).
    apply prodU.
  
    rewrite <- (cat_assoc X). apply (cat_respects X); auto.
    symmetry. apply pairing_univ.
    + rewrite (cat_assoc X).
      transitivity (Λ(f) ∘ π₁ ∘ ⟨g,h⟩).
      * apply cat_respects; auto.
        apply (proj1_commute X).
      * rewrite <- (cat_assoc X).
        apply cat_respects; auto.
        apply proj1_commute.
    + rewrite (cat_assoc X).
      transitivity (π₂ ∘ ⟨g,h⟩).
      * apply cat_respects; auto.
        apply (proj2_commute X).
      * apply (proj2_commute X).
  - apply cat_respects; auto.
    apply curry_commute.
Qed.

Lemma curry_commute2 (X:cartesian_closed) : 
  forall (C A B:X) (f:C×A → B) (h:C → A),
    apply ∘ ⟨ Λ f, h ⟩ ≈ f ∘ ⟨ id, h ⟩.
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