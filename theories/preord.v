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

Definition lt {A : PrePreOrder} (x y : A) := x ≤ y /\ x <> y.

Notation "x < y" := (lt x y) : preord_scope.

#[primitive] HB.mixin Record IsPreOrder T of pre_pre_ord T := {
  ord_refl : Reflexive (ord (s := T));
  ord_trans : Transitive (ord (s := T));
}.

#[short(type="PreOrder")]
HB.structure Definition pre_order := { T of pre_pre_ord T & IsPreOrder T}.

#[primitive] HB.mixin Record IsPoset (T : Type) of pre_order T := {
  ord_antisym : forall (a b : T), a ≤ b -> b ≤ a -> a = b;
}.

(* To get transitivity to work *)
Instance PreOrder_class (A : PreOrder) : RelationClasses.PreOrder (ord (s := A)).
Proof.
  split.
  - apply ord_refl.
  - apply ord_trans.
Qed.

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

  Definition id_mon : Monotone C C := {| mon_map := ssrfun.id ; mon_mon := fun _ _ h => h |}.

  Program Definition comp_mon (g : Monotone D E) (f : Monotone C D) : Monotone C E :=
    {| mon_map := ssrfun.comp g f ; mon_mon := _ |}.
  Next Obligation.
    destruct g as [? Hg], f as [? Hf] ; cbn.
    intros x y ? ; cbn.
    now apply Hg, Hf.
  Qed.

End Monotone.

HB.instance Definition _ := IsPreCat.Build PrePreOrder
  (fun _ => id_mon) (fun _ _ _ f g => comp_mon g f).
Definition _PrePreOrd_Cat : IsCat PrePreOrder :=
  IsCat.Build PrePreOrder ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _PrePreOrd_Cat.

HB.instance Definition _ := IsPreCat.Build PreOrder
  (fun _ => id_mon) (fun _ _ _ f g => comp_mon g f).
Definition _PreOrd_Cat : IsCat PreOrder :=
  IsCat.Build PreOrder ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _PreOrd_Cat.

HB.instance Definition _ := IsPreCat.Build Poset (fun _ => id_mon) (fun _ _ _ f g => comp_mon g f).
Definition _Poset_Cat : IsCat Poset := IsCat.Build Poset ltac:(by ext) ltac:(by ext) ltac:(by ext).
HB.instance Definition _ := _Poset_Cat.


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

Lemma lt_nle (A:Poset) (a b : A) : a < b -> ~(b ≤ a).
Proof.
  intros [? Hne] ?.
  now apply Hne, ord_antisym.
Qed.

Lemma lt_le (A : PrePreOrder) (x y : A) : x < y -> x ≤ y.
Proof.
  now intros [].
Qed.

Hint Resolve lt_le : core.

(** *** An example : natural numbers *)

HB.instance Definition _ := IsPrePreOrder.Build nat le.
HB.instance Definition _ := IsPreOrder.Build nat Nat.le_refl Nat.le_trans.
HB.instance Definition _ := IsPoset.Build nat Nat.le_antisymm.

(** ** Poset is terminated. *)

HB.instance Definition _ := IsPrePreOrder.Build unit (fun _ _ => True).
HB.instance Definition _ := IsPreOrder.Build unit (fun _ => I) (fun _ _ _ _ _ => I).
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

(** *** Constant monotone function *)


Program Definition const_mon {C D : Poset} (d : D) : Monotone C D := {| mon_map := fun=> d |}.
Next Obligation.
  red ; reflexivity.
Qed.

(** ** Poset is initialised. *)

HB.instance Definition _ := IsPrePreOrder.Build void (fun _ _ => False).
HB.instance Definition _ := IsPreOrder.Build void (fun x => of_void _ x) (fun x _ _ _ _ => of_void _ x).
HB.instance Definition _ := IsPoset.Build void (fun _ _ _ _ => empty_ext _ _).

Program Definition _PreInitPoset := IsPreInitialised.Build Poset void
  (fun P => {| mon_map := fun x => of_void _ x ; mon_mon := _ |} ).
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

Definition prod_ord (A B:PrePreOrder) (x y:A*B) : Prop :=
  (fst x) ≤ (fst y) /\ (snd x) ≤ (snd y).

Arguments prod_ord _ _ _ _/.

HB.instance Definition _ (A B:PrePreOrder) := IsPrePreOrder.Build (A*B) (prod_ord A B).

Program Definition _ProdPreOrd (A B : PreOrder) := IsPreOrder.Build (A*B) _ _.
Next Obligation.
  split ; reflexivity.
Qed.
Next Obligation.
  red ; intros ; red ; cbn.
  repeat match goal with | H : _ ≤ _ |- _ => destruct H end.
  split; now etransitivity.
Qed.

HB.instance Definition _ (A B : PreOrder) := _ProdPreOrd A B.

Program Definition _ProdPoset (A B : Poset) := IsPoset.Build (A*B) _.
Next Obligation.
  repeat match goal with | H : _ ≤ _ |- _ => destruct H end.
  ext ; now apply ord_antisym.
Qed.

HB.instance Definition _ (A B : Poset) := _ProdPoset A B.

Definition _PreHasProdsPoset := PreHasProds.Build Poset (fun A B => HB.pack (A*B)).

HB.instance Definition _ := _PreHasProdsPoset.

Program Definition _HasProjsPoset := HasProjs.Build Poset
  (fun p q => {| mon_map := fst ; mon_mon := _|})
  (fun p q => {| mon_map := snd ; mon_mon := _|})
  (fun p q x f g => {| mon_map := fun x => (f x,g x) ; mon_mon := _|}).
Next Obligation.
  now intros [] [] [].
Qed.
Next Obligation.
  now intros [] [] [].
Qed.
Next Obligation.
  split ; cbn.
  all: now apply: mon_mon.
Qed.

HB.instance Definition _ := _HasProjsPoset.

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
  now apply: mon_mon.
Qed.
Next Obligation.
  red ; intros.
  unfold ord in * ; cbn in *.
  intros.
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
  intros ?? ; cbn in *.
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
  intros [] ; red ; cbn ; reflexivity.
Qed.
Next Obligation.
  intros [] [] [] ** ;
  repeat (match goal with | H : _ ≤ _ |- _ => red in H end) ; red ; cbn in *.
  all: try done.
  all: now etransitivity.
Qed.

HB.instance Definition _ (A B : PreOrder) := _SumPreOrd A B.

Program Definition _SumPoset (A B : Poset) := IsPoset.Build (A+B)%type _.
Next Obligation.
  repeat (match goal with | H : _ + _ |- _ => destruct H end) ;
  repeat (match goal with | H : _ ≤ _ |- _ => red in H end) ; cbn in *.
  all: try done.
  all: ext ; now apply ord_antisym.
Qed.

HB.instance Definition _ (A B : Poset) := _SumPoset A B.

Definition _PreHasSumsPoset := PreHasSums.Build Poset (fun A B => HB.pack (A+B)%type).

HB.instance Definition _ := _PreHasSumsPoset.

Program Definition _HasInjsPoset := HasInjs.Build Poset
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

HB.instance Definition _ := _HasInjsPoset.

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

(** ** Preorders with decidable ordering *)

#[primitive]HB.mixin Record HasOrdDec T of poset T := {
  #[canonical=no]ord_dec : forall x y:T, Decision (x ≤ y)
}.

#[short(type="DecPoset")]
HB.structure Definition dec_poset := { T of poset T & HasOrdDec T & HasEqDec T}.

(**  Preorders with decidable ordering also have decidable equality. *)

HB.builders Context P of HasOrdDec P.

Fact ord_dec_eq_dec x y : Decision (x = y :> P).
Proof.
  case: (ord_dec x y) => [hle | hnle].
  1: case: (ord_dec y x) => [hle' | hnle].
  2-3: right => ? ; subst ; apply: hnle ; reflexivity.
  1: by left ; apply: ord_antisym.
Qed.

HB.instance Definition _ := HasEqDec.Build P ord_dec_eq_dec.

HB.end.

Lemma lt_le_eq {A : DecPoset} (x y : A) : (~ (x < y)) <-> (x ≤ y -> x = y).
Proof.
  ext.
  split.
  - intros Hneg ?.
    apply (dec_stable _).
    intros ?.
    apply Hneg.
    now constructor.
  - intros ? [? Hneg].
    intuition.
Qed.

(** *** Instances *)

HB.instance Definition _ := HasOrdDec.Build nat le_dec.

Hint Extern 100 (Decision (_ ≤ _)) => (apply: ord_dec) : typeclass_instances.

Lemma unit_dec (x y : unit) : Decision (x ≤ y).
Proof.
  repeat match goal with | h : unit |- _ => destruct h end.
  now left.
Qed.

Lemma void_dec (x y : void) : Decision (x ≤ y).
Proof.
  now eapply of_void.
Qed.

HB.instance Definition _ := HasOrdDec.Build unit unit_dec.
HB.instance Definition _ := HasOrdDec.Build void void_dec.

HB.instance Definition _ (A B : DecPoset) := HasOrdDec.Build (A*B) _.

Definition _PreHasProdsOrdDec := PreHasProds.Build DecPoset (fun A B => HB.pack (A*B)).
HB.instance Definition _ := _PreHasProdsOrdDec.

Program Definition _SumDec (A B : DecPoset) := HasOrdDec.Build (A+B) _.
Next Obligation.
  destruct x as [a|b], y as [a'|b'].
  2,3: right ; now cbv.
  - destruct (ord_dec a a').
    2: right ; now cbv.
    left.
    assumption.
  - destruct (ord_dec b b').
    2: right ; now cbv.
    left.
    assumption.
Qed.

HB.instance Definition _ (A B : DecPoset) := _SumDec A B.

Definition _PreHasSumsOrdDec := PreHasSums.Build DecPoset (fun A B => HB.pack (A+B)).
HB.instance Definition _ := _PreHasSumsOrdDec.

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
    The lift construction gives rise to an endofunctor on preorders.
  *)

Definition lift A := option A.

Definition lift_bot {A} : lift A := None.

Definition lift_ord (A:PrePreOrder) (x:option A) (y:option A) : Prop :=
   match x with None => True | Some x' =>
     match y with None => False | Some y' => x' ≤ y' end end.

HB.instance Definition _ (A:PrePreOrder) :=
  IsPrePreOrder.Build (lift A) (lift_ord A).

Definition PrePreOrder_lift (A : PrePreOrder) : PrePreOrder := HB.pack (lift A).

Program Definition _LiftPreOrd (A : PreOrder) := IsPreOrder.Build (lift A) _ _.
Next Obligation.
  red ; cbn.
  intros [] ; red ; cbn.
  all: reflexivity.
Qed.
Next Obligation.
  intros [] [] [] h1 h2.
  all: red in h1, h2 |- * ; cbn in * ; try easy.
  now etransitivity.
Qed.

HB.instance Definition _ (A : PreOrder) := _LiftPreOrd A.

Definition PreOrder_lift (A : PreOrder) : PreOrder := HB.pack (lift A).

Program Definition _LiftPoset (A : Poset) := IsPoset.Build (lift A) _.
Next Obligation.
  destruct a, b.
  all: repeat (match goal with | H : _ ≤ _ |- _ => red in H end) ; cbn in *.
  all: try easy.
  f_equal.
  now apply ord_antisym.
Qed.

HB.instance Definition _ (A : Poset) := _LiftPoset A.

Definition Poset_lift (A : Poset) : Poset := (lift A).

Program Definition liftup {A : PreOrder} : Monotone A (lift A) :=
  {|
      mon_map := Some ;
      mon_mon := _
  |}.
Next Obligation.
  intros ?? Hl.
  exact Hl.
Qed.

(* HB.instance Definition _ := _LiftPreFunctor. *)

Definition liftF_map {A B : PrePreOrder} (f : A -> B) : lift A -> lift B :=
  fun x => match x with | None => None | Some x' => Some (f x') end.

Program Definition liftF (A B : PrePreOrder) (f : Monotone A B) : Monotone (lift A) (lift B) :=
  {|
      mon_map := liftF_map f ;
      mon_mon := _
  |}.
Next Obligation.
  intros ** [] [] h.
  all: red in h |- * ; cbn in *.
  all: try easy.
  now apply mon_mon.
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
  ext ; cbn.
  destruct x ; reflexivity.
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
  ext.
  destruct x ; reflexivity.
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
  ext.
  destruct x ; reflexivity.
Qed.

HB.instance Definition _ := _LiftFunctor_Poset.


Lemma lift_dec {A : DecPoset} (x y : lift A) : Decision (x ≤ y).
Proof.
  destruct x as [x|], y as [y|].
  - now destruct (ord_dec x y) ; [left |right].
  - right.
    now cbv.
  - left.
    now cbv.
  - now left.
Qed.

HB.instance Definition _ (A : DecPoset) := HasOrdDec.Build (lift A) lift_dec.

(** ** Partial *)
(** The "partial" preorder, which classifies partial maps:
    a function [A -> partial B] is the same as a partial function from [A] to [B].
    The partial construction gives rise to an endofunctor on preorders.
  *)

Definition partial A := {p : Prop & p -> A}.
Definition defined {A} (x : partial A) : Prop := projT1 x.
Definition value {A} (x : partial A) : defined x -> A :=
  projT2 x.

Definition partial_bot {A} : partial A := existT _ False (False_rect _).

Definition on_partial {A} (P : A -> Prop) (x : partial A) : Prop :=
  {p : defined x & P (value x p)}.

Lemma partial_ext {A} (x y : partial A) :
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

Definition partial_ord (A:PrePreOrder) (x:partial A) (y: partial A) : Prop :=
  {f : defined x -> defined y & forall p : defined x, value x p ≤ value y (f p)}.

HB.instance Definition _ (A:PrePreOrder) :=
  IsPrePreOrder.Build (partial A) (partial_ord A).

Definition PrePreOrder_partial (A : PrePreOrder) : PrePreOrder := HB.pack (partial A).

Program Definition _PartialPreOrd (A : PreOrder) := IsPreOrder.Build (partial A) _ _.
Next Obligation.
  red ; cbn.
  unshelve eexists.
  1: exact ssrfun.id.
  reflexivity.
Qed.
Next Obligation.
  intros ? * [] [].
  red ; cbn.
  unshelve eexists.
  1: refine (ssrfun.comp _ _) ; shelve.
  intros ; cbn.
  etransitivity ; eauto.
Qed.

HB.instance Definition _ (A : PreOrder) := _PartialPreOrd A.

Definition PreOrder_partial (A : PreOrder) : PreOrder := HB.pack (partial A).

Program Definition _PartialPoset (A : Poset) := IsPoset.Build (partial A) _.
Next Obligation.
  repeat (match goal with | H : _ ≤ _ |- _ => let e := fresh e in destruct H as [? e] end).
  unshelve eapply partial_ext.
  1: split ; assumption.
  intros.
  cbn.
  apply ord_antisym.
  - etransitivity.
    1: eauto.
    apply rrefl.
    f_equal.
    ext.
  - etransitivity.
    1: eauto.
    apply rrefl.
    f_equal.
    ext.
Qed.

HB.instance Definition _ (A : Poset) := _PartialPoset A.

Definition Poset_partial (A : Poset) : Poset := HB.pack (partial A).

Program Definition partialup {A : PreOrder} : Monotone A (partial A) :=
  {|
      mon_map := fun x => existT _ True (fun _ => x) ;
      mon_mon := _
  |}.
Next Obligation.
  intros ?? Hl.
  red ; cbn ; red ; cbn.
  now exists idfun.
Qed.

(* HB.instance Definition _ := _PartialPreFunctor. *)

Definition partialF_map {A B : PrePreOrder} (f : A -> B) : partial A -> partial B :=
  fun x => existT _ (defined x) (fun p => f (value x p)).

Program Definition partialF (A B : PrePreOrder) (f : Monotone A B) : Monotone (partial A) (partial B) :=
  {|
      mon_map := partialF_map f ;
      mon_mon := _
  |}.
Next Obligation.
  intros ** ?? [fd fv].
  red ; cbn ; red ; cbn.
  exists fd.
  intros.
  now apply mon_mon.
Qed.
 
Program Definition _PartialFunctor_PrePreOrder := IsFunctor.Build PrePreOrder PrePreOrder PrePreOrder_partial
  partialF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  by ext.
Qed.

HB.instance Definition _ := _PartialFunctor_PrePreOrder.
 
Program Definition _PartialFunctor_PreOrder := IsFunctor.Build PreOrder PreOrder PreOrder_partial
  partialF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  by ext.
Qed.

HB.instance Definition _ := _PartialFunctor_PreOrder.
 
Program Definition _PartialFunctor_Poset := IsFunctor.Build Poset Poset Poset_partial
  partialF _ _.
Next Obligation.
  cbn.
  intros.
  ext.
  destruct x ; reflexivity.
Qed.
Next Obligation.
  by ext.
Qed.

HB.instance Definition _ := _PartialFunctor_Poset.