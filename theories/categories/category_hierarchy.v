(** * Domains.category_hierarchy: hierarchy of structures on the whole categories:
  cartesian, cocartesian, closed. *)
From Stdlib Require Import ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories morphisms functors.

#[local] Open Scope cat_scope.

(** ** Categories with terminal objects

     Such categories have a distinguished object [terminus] (notation [!])
     and a family of morphisms [terminate : A → !] for each object [A].
     Furthermore, [terminate] is universial, in that for every
     [f : A → !], [f = terminate].
  *)

Definition IsTerminal {C : Quiver} (t : C) (f : forall x, x → t) := forall x (g : x → t), g = (f x).

#[primitive] HB.mixin Record IsPreTerminated (C : Type) of quiver C := {
  terminus : C ;
  terminate : forall (x : C), x → terminus ;
}.

#[short(type="PreTerminated"),primitive]
HB.structure Definition pre_terminated := { C of quiver C & IsPreTerminated C}.

Notation "'!'" := (terminus) : cat_scope.
Arguments terminate {_ _}.

#[primitive] HB.mixin Record IsTerminated (C : Type) of pre_terminated C := {
  termU : IsTerminal (C := C) ! (@terminate _)
}.

#[short(type="Terminated"),primitive]
HB.structure Definition terminated := { C of pre_terminated C & IsTerminated C}.

Arguments termU : clear implicits.

Lemma terminate_terminal {C : Terminated} : IsTerminal (C := C) ! (@terminate _).
Proof.
  red.
  intros.
  apply termU.
Succeed Qed.
Abort.

Definition terminalI {C : Cat} (t t' : C) (f : forall x, x → t) (f' : forall x, x → t') :
  IsTerminal t f ->
  IsTerminal t' f' ->
  (Σ! h : t ↔ t', (forall x, h ∘ (f x) = f' x) /\ (forall x, h⁻¹ ∘ (f' x) = f x)).
Proof.
  intros Ht Ht'.
  unshelve econstructor.
  - unshelve econstructor.
    1: apply f'.
    do 2 (unshelve econstructor).
    1: apply f.
    all: etransitivity ; [|symmetry].
    1-2: now apply Ht'.
    1-2: now apply Ht.
  - split => //.
    move => g _.
    apply iso_ext => /=.
    apply Ht'.
Qed.

(* TODO The category of Types is terminated *)

(* Definition elem (X:ob SET) (x:X) : ! → X :=
  SET.Hom !%cat_ob X (fun _ => x) (fun a b H => eq_refl _ _). *)

(** ** Categories with initial objects

     Such categories have a distinguished object [init] (notation [¡])
     and a family of morphisms [initiate : ¡ → A] for each object [A].
     Furthermore, [initiate] is universal, in that every for every
     [f : ¡ → A], [f = initiate].
  *)

Definition IsInitial {C : Quiver} (t : C) (f : forall x, t → x) := forall x (g : t → x), g = (f x).

#[primitive] HB.mixin Record IsPreInitialised (C : Type) of quiver C := {
  initium : C ;
  initiate : forall (x : C), initium → x ;
}.

#[short(type="PreInitialised"),primitive]
HB.structure Definition pre_initialised := { C of quiver C & IsPreInitialised C}.

Notation "'¡'" := (initium) : cat_scope.
Arguments initiate {_ _}.

#[primitive] HB.mixin Record IsInitialised C of pre_initialised C := {
  initU : IsInitial (C := C) ¡ (@initiate _)
}.

#[short(type="Initialised"),primitive]
HB.structure Definition initialised := { C of pre_initialised C & IsInitialised C}.

Arguments initU : clear implicits.

Definition initialI {C : Cat} (t t' : C) (f : forall x, t → x) (f' : forall x, t' → x) :
  IsInitial t f ->
  IsInitial t' f' ->
  (Σ! h : t ↔ t', (forall x, (f' x) ∘ h = f x) /\ (forall x, (f x) ∘ h⁻¹ = f' x)).
Proof.
  intros Ht Ht'.
  unshelve econstructor.
  - unshelve econstructor.
    1: apply f.
    do 2 (unshelve econstructor).
    1: apply f'.
    all: etransitivity ; [|symmetry].
    1-2: apply Ht'.
    1-2: apply Ht.
  - split => //.
    move => g _.
    apply iso_ext => /=.
    apply Ht.
Qed.

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

#[primitive] HB.mixin Record PreHasSums C of precat C := {
  cat_sum : C -> C -> C ;
  sum_inl : forall {a b : C}, a → cat_sum a b ;
  sum_inr : forall {a b : C}, b → cat_sum a b ;
  either : forall {a b x : C}, a → x -> b → x -> cat_sum a b → x ;
}.

#[short(type="PreHasSums"),primitive]
HB.structure Definition pre_has_sums := {
    C of precat C & PreHasSums C}.

Notation "A + B" := (cat_sum A B) : cat_scope.
Notation "A +[ X ] B" := (@cat_sum X A B) (only parsing) : cat_scope.
Notation "'ι₁'" := (sum_inl _ _) : cat_scope.
Notation "'ι₂'" := (sum_inr _ _) : cat_scope.
Arguments either {_ _ _ _} _ _.

#[primitive] HB.mixin Record HasSums C of precat C & pre_has_sums C := {
  inlK : forall {a b x : C} {f : a → x} {g : b → x}, (either f g) ∘[C] ι₁ = f ; 
  inrK : forall {a b x : C} {f : a → x} {g : b → x}, (either f g) ∘[C] ι₂ = g ;
  sumU : forall {a b x : C} {f : a → x} {g : b → x} {h : cat_sum a b → x},
    h ∘[C] ι₁ = f -> h ∘[C] ι₂ = g -> h = either f g
}. 

#[short(type="CoCartesian"),primitive]
HB.structure Definition cocartesian := {
    C of cat C & initialised C & pre_has_sums C & HasSums C}.

Arguments inlK {_ _ _ _} _ _.
Arguments inrK {_ _ _ _} _ _.
Arguments sumU : clear implicits.

Definition sum_map {X:CoCartesian} {a b c d: X}
  (f:a → b) (g:c → d) : a + c →[X] b + d := either (ι₁ ∘ f) (ι₂ ∘ g).

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

#[primitive] HB.mixin Record PreHasProds C of precat C := {
  cat_prod : C -> C -> C ;
  prod_projl : forall {a b : C}, cat_prod a b → a ;
  prod_projr : forall {a b : C}, cat_prod a b → b ;
  pairing : forall {a b x : C}, x → a -> x → b -> x → cat_prod a b ;
}.

#[short(type="PreHasProds"),primitive]
HB.structure Definition pre_has_prods := {
    C of precat C & PreHasProds C}.

Notation "A × B" := (cat_prod A B) : cat_scope.
Notation "A ×[ X ] B" := (@cat_prod X A B) (only parsing): cat_scope.
Notation "'π₁'" := (prod_projl  _ _) : cat_scope.
Notation "'π₂'" := (prod_projr _ _) : cat_scope.
Notation "⟨ f , g ⟩" := (pairing _ _ _ f g) : cat_scope.

#[primitive] HB.mixin Record HasProds C of precat C & pre_has_prods C := {
  projlK : forall (a b x : C) (f : x → a) (g : x → b), π₁ ∘[C] ⟨f,g⟩ = f ; 
  projrK : forall (a b x : C) (f : x → a) (g : x → b), π₂ ∘[C] ⟨f,g⟩ = g ; 
  prodU : forall (a b x : C) (f : x → a) (g : x → b) (h : x → cat_prod a b),
    π₁ ∘[C] h = f -> π₂ ∘[C] h = g -> h = ⟨f,g⟩
}.

#[short(type="Cartesian"),primitive]
HB.structure Definition cartesian := {
    C of cat C & terminated C & pre_has_prods C & HasProds C}.

Arguments projlK {_ _ _ _} _ _.
Arguments projrK {_ _ _ _} _ _.
Arguments prodU : clear implicits.

Definition prod_map {X:Cartesian} {a b c d: X}
  (f:a → b) (g:c → d) : a×c →[X] b×d :=
    ⟨ (f ∘ (π₁ : a × c →[X] a)) , (g ∘ (π₂ : a × c →[X] c)) ⟩.

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


Arguments distr : clear implicits.

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

#[primitive] HB.mixin Record PreHasExps C of cartesian C := {
  cat_exp : C -> C -> C ;
  eval : forall {a b : C}, (cat_exp a b) × a →[C] b ;
  curry : forall {a b x : C}, ((x × a) → b) -> x → cat_exp a b
}.

#[short(type="PreCartesianClosed"),primitive]
  HB.structure Definition pre_cart_closed :=
    { C of cartesian C & PreHasExps C}.

Notation "a ⇒ b" := (cat_exp a b) : cat_scope.
Arguments eval {_ _ _}.
Arguments curry {_ _ _ _} _.

#[primitive] HB.mixin Record HasExps C of pre_cart_closed C := {
  evalK : forall (a b x : C) (f : (x × a) → b),
    eval ∘[C] ⟨ curry f ∘[C] π₁, π₂⟩ = f ;
  expU : forall (a b x : C) (f : (x × a) → b) (h : x → cat_exp a b),
    eval ∘ ⟨ h ∘[C] π₁, π₂⟩ = f -> h = curry f
}.

#[short(type="CartesianClosed"),primitive]
HB.structure Definition cartesian_closed := { C of pre_cart_closed C & HasExps C}.

Arguments evalK {_ _ _ _} _.
Arguments expU : clear implicits.


Lemma curry_commute3 (X:CartesianClosed) : 
  forall (d c a b:X) (f:c×a → b) (g:d → c) (h:d → a),
    eval ∘ ⟨ curry f ∘ g, h ⟩ = f ∘ ⟨ g, h ⟩.
Proof.
  intros.
  rewrite -(evalK f).
  rewrite compoA.
  f_equal.
  symmetry.
  apply prodU.
  + rewrite -compoA projlK compoA projlK evalK //.
  + rewrite -compoA projrK projrK //.
Qed.

(**  Polynomial categories

    Categories with finite sums, finite products, and exponents where sums distribute over products.
    That is, the categorification of Heyting algebras.

  *)

#[short(type="PolynomialCat"),primitive]
HB.structure Definition poly_cat := { C of cartesian_closed C & distributive C}.

(** Note: any categoy that is cartesian closed + cocartesian is automatically distributive, because
  [A × -], being a left adjoint, preserves colimits. So we could have a simpler factory to construct
  polynomial categories, which we have not defined here. *)

HB.factory Record IsPolynomial C
  of cartesian_closed C & cocartesian C := {}.

HB.builders Context C of IsPolynomial C.

Lemma exp_distr (a b c : C) : a × (b + c) ↔ (a × b) + (a × c).
Proof.
Admitted.

HB.instance Definition _ := IsDistributive.Build C exp_distr.
HB.end.