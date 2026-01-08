(** * Domains.categories.all: definitions of preorders *)

From Stdlib Require Import Morphisms ssreflect ssrfun Arith.
From HB Require Import structures.

Require Import utils.all categories.all.

Open Scope type_scope.

Declare Scope preord_scope.
Delimit Scope preord_scope with preord.
#[global]Open Scope preord_scope.

(**  ** Ordered types and monotone functions.

     A preorder is a type equipped with a transitive,
     reflexive relation.  Unlike standard domain theory,
     we will be concentrating on preorders rather than
     partial orders as the basis of order theory.
  *)

#[primitive] HB.mixin Record IsPrePreOrder C := {
    #[canonical=no] ord : C -> C -> Prop
  }.
#[short(type="PrePreOrder")]
HB.structure Definition pre_pre_ord := { C of IsPrePreOrder C }.

Bind Scope preord_scope with PrePreOrder.
Arguments ord {_} : simpl never.
Notation "x ≤ y" := (ord x y) : preord_scope.
Notation "y ≥ x" := (ord y x) (only parsing) : preord_scope.

#[primitive] HB.mixin Record IsPreOrder (T : Type) of pre_pre_ord T := {
  ord_refl : forall (a : T), a ≤ a;
  ord_trans : forall (a b c : T), a ≤ b -> b ≤ c -> a ≤ c;
}.

#[short(type="PreOrder")]
HB.structure Definition pre_order := { T of pre_pre_ord T & IsPreOrder T}.

#[primitive] HB.mixin Record IsPoset (T : Type) of pre_order T := {
  ord_antisym : forall (a b : T), a ≤ b -> b ≤ a -> a = b;
}.

#[short(type="Poset")]
HB.structure Definition poset := { T of pre_order T & IsPoset T}.

(** *** Every poset is a category *)

Definition CatPos (C : Type) : Type := C.
HB.instance Definition _ (C : PrePreOrder) :=
  IsQuiver.Build (CatPos C) (fun a b => a ≤ b).
HB.instance Definition _ (C : PreOrder) :=
  IsPreCat.Build (CatPos C) ord_refl ord_trans.
HB.instance Definition _ (C : Poset) := IsCat.Build (CatPos C)
  (fun a b _ => proof_irrelevance (a ≤ b) _ _) (fun a b _ => proof_irrelevance (a ≤ b) _ _)
  (fun a b c d _ _ _ => proof_irrelevance (a ≤ d) _ _).


(** *** Monotone maps and the categories of preorders and posets *)

Definition IsMonotone {C D : PrePreOrder} (f : C -> D) :=
  forall x y, x ≤ y -> f x ≤ f y.

Record Monotone {C D : PrePreOrder} :=
  {
    mon_map :> C -> D ;
    mon_mon : IsMonotone mon_map
  }.

Arguments Monotone : clear implicits.

HB.instance Definition _ := IsQuiver.Build PrePreOrder Monotone.
HB.instance Definition _ := IsQuiver.Build PreOrder Monotone.
HB.instance Definition _ := IsQuiver.Build Poset Monotone.


Lemma mon_ext_ppo (C D : PrePreOrder) (f g : Monotone C D) :
  mon_map f = mon_map g -> f = g.
Proof.
  destruct f,g ; cbn in *.
  intros ->.
  ext.
Qed.

Smpl Add (apply: mon_ext_ppo ; cbn) : extensionality.
(* Smpl Add (apply: mon_ext_po ; cbn) : extensionality.
Smpl Add (apply: mon_ext_pos ; cbn) : extensionality. *)

Section Monotone.
  Context {C D E : PrePreOrder}.

  Definition mon_id : Monotone C C := {| mon_map := ssrfun.id ; mon_mon := fun _ _ h => h |}.

  Program Definition mon_comp (g : Monotone D E) (f : Monotone C D) : Monotone C E :=
    {| mon_map := ssrfun.comp g f ; mon_mon := _ |}.
  Next Obligation.
    intros [? Hg] [? Hf] x y ? ; cbn.
    now apply Hg, Hf.
  Qed.

End Monotone.

HB.instance Definition _ := IsPreCat.Build PrePreOrder
  (fun _ => mon_id) (fun _ _ _ f g => mon_comp g f).
Definition _PrePreOrd_Cat : IsCat PrePreOrder :=
  IsCat.Build PrePreOrder ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _PrePreOrd_Cat.

HB.instance Definition _ := IsPreCat.Build PreOrder
  (fun _ => mon_id) (fun _ _ _ f g => mon_comp g f).
Definition _PreOrd_Cat : IsCat PreOrder :=
  IsCat.Build PreOrder ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _PreOrd_Cat.

HB.instance Definition _ := IsPreCat.Build Poset (fun _ => mon_id) (fun _ _ _ f g => mon_comp g f).
Definition _Poset_Cat : IsCat Poset := IsCat.Build Poset ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _Poset_Cat.


(* To get transitivity to work *)
Add Parametric Relation (A:PreOrder) : A (@ord A)
  reflexivity proved by (@ord_refl A)
  transitivity proved by (@ord_trans A)
    as ord_rel.

(**  This lemma is handy for using an equality in the context to prove a goal
     by transitivity on both sides.
  *)
Lemma use_ord (A:PreOrder) (a b c d:A) :
  b ≤ c -> a ≤ b -> c ≤ d -> a ≤ d.
Proof.
  intros.
  transitivity b; auto.
  transitivity c; auto.
Qed.
Arguments use_ord [A] [a] [b] [c] [d] _ _ _.

(** *** An example : natural numbers *)

HB.instance Definition _ := IsPrePreOrder.Build nat le.
HB.instance Definition _ := IsPreOrder.Build nat Nat.le_refl Nat.le_trans.
HB.instance Definition _ := IsPoset.Build nat Nat.le_antisymm.

(** ** Poset is terminated. *)

HB.instance Definition _ := IsPrePreOrder.Build unit (fun _ _ => True).
HB.instance Definition _ := IsPreOrder.Build unit (fun _ => I) (fun _ _ _ _ _ => I).

Lemma unit_ext (x y : unit) : x = y.
Proof (match x, y with | tt, tt => eq_refl end).

Smpl Add (apply unit_ext) : extensionality.

HB.instance Definition _ := IsPoset.Build unit (fun _ _ _ _ => unit_ext _ _).

Program Definition _PreTermPoset := IsPreTerminated.Build Poset unit
  (fun P => {| mon_map := fun x => tt ; mon_mon := _ |} ).
Next Obligation.
  intros x.
  red.
  reflexivity.
Qed.

HB.instance Definition _ := _PreTermPoset.

Program Definition _TermPoset := IsTerminated.Build Poset _.
Next Obligation.
  red ; ext.
Qed.

HB.instance Definition _ := _TermPoset.

(** ** Poset is initialised. *)

HB.instance Definition _ := IsPrePreOrder.Build False (fun _ _ => False).
HB.instance Definition _ := IsPreOrder.Build False (fun x => except x) (fun x _ _ _ _ => except x).

Lemma empty_ext (x y : False) : x = y.
Proof (except x).

Smpl Add (apply empty_ext) : extensionality.

HB.instance Definition _ := IsPoset.Build False (fun _ _ _ _ => empty_ext _ _).

Program Definition _PreInitPoset := IsPreInitialised.Build Poset False
  (fun P => {| mon_map := fun x => False_rect _ x ; mon_mon := _ |} ).
Next Obligation.
  by intros ? ?.
Qed.

HB.instance Definition _ := _PreInitPoset.

Program Definition _InitPoset := IsInitialised.Build Poset _.
Next Obligation.
  red ; ext.
  by cbn in *.
Qed.

HB.instance Definition _ := _InitPoset.

(**  ** Poset is cartesian *)

Definition prod_ord (A B:PrePreOrder) (x y:A*B):=
  (fst x) ≤ (fst y) /\ (snd x) ≤ (snd y).

Arguments prod_ord _ _ _ _/.

HB.instance Definition _ (A B:PrePreOrder) := IsPrePreOrder.Build (A*B) (prod_ord A B).

Program Definition _ProdPreOrd (A B : PreOrder) := IsPreOrder.Build (A*B) _ _.
Next Obligation.
  intros ? ? [] ; cbn ; red ; cbn.
  split ; reflexivity.
Qed.
Next Obligation.
  intros ? ? [] [] [] [] [] ; cbn in * ; red ; cbn.
  split ; now etransitivity.
Qed.

HB.instance Definition _ (A B : PreOrder) := _ProdPreOrd A B.

Program Definition _ProdPoset (A B : Poset) := IsPoset.Build (A*B) _.
Next Obligation.
  intros ?? [] [] [] [] ; cbn in *.
  ext ; now apply ord_antisym.
Qed.

HB.instance Definition _ (A B : Poset) := _ProdPoset A B.

Program Definition _PreHasProdsPoset := PreHasProds.Build Poset
  (fun A B => HB.pack (A*B))
  (fun p q => {| mon_map := fst ; mon_mon := _|})
  (fun p q => {| mon_map := snd ; mon_mon := _|})
  (fun p q x f g => {| mon_map := fun x => (f x,g x) ; mon_mon := _|}).
Next Obligation.
  now intros ?? [] [] [].
Qed.
Next Obligation.
  now intros ?? [] [] [].
Qed.
Next Obligation.
  intros * ?? ?.
  split ; cbn.
  all: now apply: mon_mon.
Qed.

HB.instance Definition _ := _PreHasProdsPoset.

Program Definition _HasProdsPoset := HasProds.Build Poset _ _ _.
Next Obligation.
  now ext.
Qed.
Next Obligation.
  now ext.
Qed.
Next Obligation.
  intros ; subst.
  ext ; cbn.
  apply surjective_pairing.
Qed.

HB.instance Definition _ := _HasProdsPoset.

(**  ** Poset is cartesian closed *)

Definition exp_ord (A B:PrePreOrder) (f g : Monotone A B):=
  forall x x', x ≤ x' -> f x ≤ g x'.

Arguments exp_ord _ _ _ _/.

HB.instance Definition _ (A B:PrePreOrder) :=
  IsPrePreOrder.Build (Monotone A B) (exp_ord A B).

Program Definition _ExpPreOrd (A B : PreOrder) := IsPreOrder.Build (Monotone A B) _ _.
Next Obligation.
  intros * ; cbn ; red ; cbn ; intros.
  now apply: mon_mon.
Qed.
Next Obligation.
  move => * ; rewrite /ord /= => *.
  now etransitivity.
Qed.

HB.instance Definition _ (A B : PreOrder) := _ExpPreOrd A B.

Program Definition _ExpPoset (A B : Poset) := IsPoset.Build (Monotone A B) _.
Next Obligation.
  rewrite /ord /= => *.
  ext.
  now apply ord_antisym.
Qed.

HB.instance Definition _ (A B : Poset) := _ExpPoset A B.

Program Definition _HasExpsPoset := PreHasExps.Build Poset
  (fun A B => HB.pack (Monotone A B))
  (fun A B => {| mon_map := fun x => (fst x) (snd x) ; mon_mon := _|})
  (fun A B X => {| 
    mon_map := fun (f : Monotone (X*A) B) =>
      {|
        mon_map := fun (x : X) => {| mon_map := fun a => f (x,a) ; mon_mon := _ |} ;
        mon_mon := _
      |} ;
    mon_mon := _|} ).
Next Obligation.
  cbn.
  intros ?? ??.
  rewrite {1}/ord /=.
  intros [Hf Ha] ; cbn in *.
  now apply: Hf.
Qed.
Next Obligation.
  cbn.
  intros ** ???.
  apply mon_mon.
  now split ; cbn.
Qed.
Next Obligation.
  intros ** ?????? ; cbn.
  apply: mon_mon.
  now split ; cbn.
Qed.
Next Obligation.
  intros ** ?? P ? ** ? **; cbn in *.
  apply: P.
  now split.
Qed.

(** The preorder on sums, defined in the standard way.
  *)
Definition sum_ord (A B:PrePreOrder) (x y:A+B):=
  match x, y with
  | inl x', inl y' => x' ≤ y'
  | inr x', inr y' => x' ≤ y'
  | _, _ => False
  end.

Arguments sum_ord _ _ !_ !_/.

HB.instance Definition _ (A B:PrePreOrder) := IsPrePreOrder.Build (A+B)%type (sum_ord A B).

Program Definition _SumPreOrd (A B : PreOrder) := IsPreOrder.Build (A+B)%type _ _.
Next Obligation.
  intros ? ? [] ; red ; cbn.
  all: reflexivity.
Qed.
Next Obligation.
  intros ? ? [] [] [] H H'; cbn in * ; red in H, H' |- * ; cbn in *.
  all: try done.
  all: now etransitivity.
Qed.

HB.instance Definition _ (A B : PreOrder) := _SumPreOrd A B.

Program Definition _SumPoset (A B : Poset) := IsPoset.Build (A+B)%type _.
Next Obligation.
  intros ?? [] [] H H' ; red in H, H' ; cbn in *.
  all: try done.
  all: ext ; now apply ord_antisym.
Qed.

HB.instance Definition _ (A B : Poset) := _SumPoset A B.

Program Definition _PreHasSumsPoset := PreHasSums.Build Poset
  (fun A B => HB.pack (A+B)%type)
  (fun p q => {| mon_map := inl ; mon_mon := _|})
  (fun p q => {| mon_map := inr ; mon_mon := _|})
  (fun p q x f g => {|
      mon_map := fun x => match x with | inl x => f x | inr x => g x end ;
      mon_mon := _|}).
Next Obligation.
  now intros ?? ? ** ; cbn ; red ; cbn.
Qed.
Next Obligation.
  now intros ?? ? ** ; cbn ; red ; cbn.
Qed.
Next Obligation.
  intros * [] [] H ; red in H ; cbn in * => //.
  all: now apply mon_mon.
Qed.

HB.instance Definition _ := _PreHasSumsPoset.

Program Definition _HasSumsPoset := HasSums.Build Poset _ _ _.
Next Obligation.
  now ext.
Qed.
Next Obligation.
  now ext.
Qed.
Next Obligation.
  intros; subst.
  ext.
  now destruct x0.
Qed.

HB.instance Definition _ := _HasSumsPoset.

(**  Preorders with decidable ordering *)

#[primitive]HB.mixin Record HasOrdDec T of poset T := {
  orddec : forall x y:T, Decision (x ≤ y) }.

#[short(type="DecPoset")]
HB.structure Definition dec_poset := { T of poset T & HasOrdDec T & HasEqDec T}.

(**  Preorders with decidable ordering also have decidable equality. *)

HB.builders Context P of HasOrdDec P.

Fact ord_dec_eq_dec (x y : P) : Decision (x = y).
Proof.
  case: (orddec x y) => [hle | hnle].
  2:{
    right.
    intros ->.
    apply hnle.
    apply: ord_refl.
  }
  case: (orddec y x) => [hle' | hnle'].
  2:{
    right.
    intros ->.
    apply hnle'.
    apply: ord_refl.
  }
  left.
  now apply ord_antisym.
Qed.

HB.instance Definition _ := HasEqDec.Build P ord_dec_eq_dec.

HB.end.

HB.instance Definition _ := HasOrdDec.Build nat le_dec.

(** ** Concreteness *)

Program Definition _PrePreOrder_Concrete := 
  IsConcrete.Build PrePreOrder pre_pre_ord.sort (@mon_map) ltac:(by ext) ltac:(by ext).

HB.instance Definition _ := _PrePreOrder_Concrete.

Program Definition _PreOrder_Concrete := 
  IsConcrete.Build PreOrder pre_order.sort (@mon_map) ltac:(by ext) ltac:(by ext).

HB.instance Definition _ := _PreOrder_Concrete.

Program Definition _Poset_Concrete := 
  IsConcrete.Build Poset poset.sort (@mon_map) ltac:(by ext) ltac:(by ext).

HB.instance Definition _ := _Poset_Concrete.

(** ** Lift *)
(** The "lift" preorder, which adjoins a new bottom element.
    The lift construction gives rise to an endofunctor on PREORD.
  *)

Definition lift A := {p : Prop & p -> A}.
Definition defined {A} (x : lift A) : Prop := projT1 x.
Definition value {A} (x : lift A) : defined x -> A :=
  projT2 x.

Definition on_lift {A} (P : A -> Prop) (x : lift A) : Prop :=
  {p : defined x & P (value x p)}.

Lemma lift_ext {A} (x y : lift A) :
  forall (f : defined x <-> defined y),
  (forall p : defined x, value x p = value y (fst f p)) ->
  x = y.
Proof.
  intros f e.
  destruct x, y ; cbn in *.
  pose proof (prop_ext f) ; subst.
  ext.
  rewrite e.
  f_equal.
  ext.
Qed.

Definition lift_ord (A:PrePreOrder) (x:lift A) (y: lift A) : Prop :=
  {f : defined x -> defined y & forall p : defined x, value x p = value y (f p)}.

HB.instance Definition _ (A:PrePreOrder) :=
  IsPrePreOrder.Build (lift A) (lift_ord A).

Definition PrePreOrder_lift (A : PrePreOrder) : PrePreOrder := HB.pack (lift A).

Program Definition _LiftPreOrd (A : PreOrder) := IsPreOrder.Build (lift A) _ _.
Next Obligation.
  intros ?? ; red ; cbn.
  unshelve eexists.
  1: exact ssrfun.id.
  reflexivity.
Qed.
Next Obligation.
  intros ? ??? [f Hf] [g Hg] ; red ; cbn.
  unshelve eexists.
  1: exact (ssrfun.comp g f).
  intros.
  rewrite Hf Hg => //=.
Qed.

HB.instance Definition _ (A : PreOrder) := _LiftPreOrd A.

Definition PreOrder_lift (A : PreOrder) : PreOrder := HB.pack (lift A).

Program Definition _LiftPoset (A : Poset) := IsPoset.Build (lift A) _.
Next Obligation.
  intros ? ?? [] [].
  unshelve eapply lift_ext.
  1: split ; assumption.
  intros.
  rewrite e.
  f_equal.
  ext.
Qed.

HB.instance Definition _ (A : Poset) := _LiftPoset A.

Definition Poset_lift (A : Poset) : Poset := HB.pack (lift A).

(* HB.instance Definition _ := _LiftPreFunctor. *)

Definition liftF_map {A B : PrePreOrder} (f : A -> B) : lift A -> lift B :=
  fun x => existT _ (defined x) (fun p => f (value x p)).

Program Definition liftF (A B : PrePreOrder) (f : A -> B) : Monotone (lift A) (lift B) :=
  {|
      mon_map := liftF_map f ;
      mon_mon := _
  |}.
Next Obligation.
  intros ** ?? [fd fv].
  red ; cbn ; red ; cbn.
  exists fd.
  intros ; by rewrite fv.
Qed.
 
Program Definition _LiftFunctor_PrePreOrder := IsFunctor.Build PrePreOrder PrePreOrder PrePreOrder_lift
  liftF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  cbn ; intros ??? f g.
  by ext.
Qed.

HB.instance Definition _ := _LiftFunctor_PrePreOrder.
 
Program Definition _LiftFunctor_PreOrder := IsFunctor.Build PreOrder PreOrder PreOrder_lift
  liftF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  cbn ; intros ??? f g.
  by ext.
Qed.

HB.instance Definition _ := _LiftFunctor_PreOrder.
 
Program Definition _LiftFunctor_Poset := IsFunctor.Build Poset Poset Poset_lift
  liftF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  cbn ; intros ??? f g.
  by ext.
Qed.

HB.instance Definition _ := _LiftFunctor_Poset.