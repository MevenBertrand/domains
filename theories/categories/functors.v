(** * Domains.functors: functors and natural transformations *)
From Stdlib Require Import Program Setoid ssreflect ssrfun.
From HB Require Import structures.

Require Import notations basics categories.

#[local] Open Scope cat_scope.

(** ** Definitons *)

#[primitive]HB.mixin Record IsPreFunctor (C D : Quiver) (F : C -> D) := {
   #[canonical=no] Fhom : forall (a b : C), (a → b) -> (F a → F b)
  }.
#[short(type="PreFunctor"),primitive]
HB.structure Definition prefunctor (C D : Quiver) :=
  { F of IsPreFunctor C D F }.

Notation "F <$> f" := (@Fhom _ _ F _ _ f) : cat_scope.

Definition pack_prefunctor [C D: Quiver] (F: C -> D)
  (Fhom : forall (a b : C), (a → b) -> (F a → F b)): PreFunctor C D :=
  HB.pack F (IsPreFunctor.Build _ _ F Fhom).


(** We follow Dokins and phrase the axioms in a "forded" fashion, if I understand
  correctly this helps with making a number of things hold up to defeq, in particular
  associativity of composition, by exploiting the fact that composition of functions
  is definitionally associative. Maybe we'll want to go back on this later… *)
  
#[primitive]HB.mixin Record PreFunctor_IsFunctor (C D : PreCat) F of @prefunctor C D F := {
   #[canonical=no] F1 : forall {a : C} {f : a → a}, f = idmap -> F <$> f = idmap;
   #[canonical=no] Fcomp : forall {a b c : C} {f : a → b} {g : b → c} {h : a → c},
      h = g ∘ f -> F <$> h = F <$> f \; F <$> g;
}.
#[short(type="Functor"),primitive]
HB.structure Definition functor (C D : PreCat) :=
  { F of IsPreFunctor C D F & PreFunctor_IsFunctor C D F }.

#[primitive]HB.factory Record IsFunctor (C D: PreCat) (F: C -> D) := {
  #[canonical=no] Fhom : forall (a b : C), (a → b) -> (F a → F b);
  #[canonical=no] F1 : forall (a : C), Fhom a _ idmap = idmap;
  #[canonical=no] Fcomp : forall (a b c : C) (f : a → b) (g : b → c),
    Fhom _ _ (g ∘ f) = Fhom _ _ g ∘ Fhom _ _ f;
}.

HB.builders Context (C D: PreCat) F of IsFunctor C D F.

HB.instance Definition _ := IsPreFunctor.Build _ _ F Fhom.

Lemma F1_ford (a : C) (f : a → a) : f = idmap -> F <$> f = idmap.
Proof.
  move => ->.
  by apply F1.
Qed.

Lemma Fcomp_ford (a b c : C) (f : a → b) (g : b → c) (h : a → c) :
      h = g ∘ f -> F <$> h = F <$> f \; F <$> g.
Proof.
  move => ->.
  by apply Fcomp.
Qed.

HB.instance Definition _ := PreFunctor_IsFunctor.Build _ _ F F1_ford Fcomp_ford.

HB.end.

Definition pack_functor [C D: PreCat] (F: C -> D)
  (Fhom : forall (a b : C), (a → b) -> (F a → F b))
  (F1 : forall (a : C), Fhom _ _ idmap = idmap)
  (Fcomp : forall (a b c : C) (f : a → b) (g : b → c),
    Fhom _ _ (f \; g) = Fhom _ _ f \; Fhom _ _ g): Functor C D :=
  HB.pack F (IsFunctor.Build _ _ F Fhom F1 Fcomp).
Arguments pack_functor [_ _] _ _.

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
   (fun a b f => G <$> (F <$> f)).

Lemma comp_Fun (a b : C) (f : a → b) : (G \o F)%function <$> f = G <$> (F <$> f).
Proof. reflexivity. Qed.

End comp_prefunctor.

Section comp_functor.
Context {C D E : PreCat} {F : Functor C D} {G : Functor D E}.

Lemma comp_F1 (a : C) (f : a → a) : f = idmap -> (G \o F)%function <$> f = idmap.
Proof. exact (fun e => F1 _ _ (F1 _ _ e)). Defined.
Lemma comp_Fcomp  (a b c : C) (f : a → b) (g : b → c) (h : a → c) :
  h = g ∘ f ->
  (G \o F)%function <$> h = ((G \o F)%function <$> g) ∘ ((G \o F)%function <$> f).
Proof. exact (fun e => Fcomp _ _ _ _ _ _ (Fcomp _ _ _ _ _ _ e)). Defined.

HB.instance Definition CompFun := PreFunctor_IsFunctor.Build C E (G \o F)%function
  comp_F1 comp_Fcomp.

End comp_functor.

(** Sanity checking: if we unset universe checking, we indeed have a pre-category of quivers
    TODO: clean *)

Unset Universe Checking.

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
  Variable G:E → F.
  Check (G : PreFunctor E F). (* The arrow → of Quivers is indeed PreFunctors *)
  Variable H:D → E.
  Variable I:C → D.

  Goal (G ∘ (H ∘ I) = (G ∘ H) ∘ I).
  Proof (eq_refl _).

  Goal (G ∘ idmap = G).
  Proof (eq_refl _).

  Goal (idmap ∘ G = G).
  Proof (eq_refl _).

End Sanity.

Set Universe Checking.

(** ** Examples *)

(** *** Constant functor *)

Program Definition fconst (C D:category) (A:ob D) : functor C D :=
  Functor C D (fun _ => A) (fun _ _ _ => id(A)) _ _ _.
Next Obligation.
  intros. apply eq_symm. apply cat_ident1.
Defined.

(** *** Functors to/from a product category *)

Section projF.
  Variables C D:category.
  
  Program Definition fstF : functor (PROD C D) C :=
    Functor (PROD C D) C
      (fun X => obl X)
      (fun X Y f => homl f)
      _ _ _.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.

  Program Definition sndF : functor (PROD C D) D :=
    Functor (PROD C D) D
      (fun X => obr X)
      (fun X Y f => homr f)
      _ _ _.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
  Next Obligation.
    intros. destruct H; auto.
  Qed.
End projF.

Section pairF.
  Variables C D E:category.
  Variable F:functor C D.
  Variable G:functor C E.

  Program Definition pairF : functor C (PROD D E) :=
    Functor C (PROD D E)
      (fun X => PROD.Ob D E (F X) (G X))
      (fun X Y f => PROD.Hom _ _ _ _ (F<$>f) (G<$>f))
      _ _ _.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.ident; auto.
    apply Functor.ident; auto.
  Qed.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.compose; auto.
    apply Functor.compose; auto.
  Qed.
  Next Obligation.
    simpl; intros. split; simpl.
    apply Functor.respects; auto.
    apply Functor.respects; auto.
  Qed.
End pairF.
Arguments pairF [C D E] _ _.

(** *** Categories *)

(** We can define the category structure for the large
     category of small categories.  However! we cannot complete
     the construction due to a universe inconsistency.  If we
     had universe polymorphism we could get the definition we want.
  *)
  
Program Definition CAT_axioms :=
   Category.Axioms
      category
      functor
      (fun A B => lib_eq (functor A B))
      (Comp.Mixin category functor
        (fun X => FunctorIdent X)
        (fun X Y Z => FunctorCompose X Y Z))
      _ _ _ _.
Next Obligation.
  intros. hnf. destruct f; auto.
Qed.
Next Obligation.
  intros. hnf. destruct f; auto.
Qed.
Next Obligation.
  intros. hnf in *. subst. auto.
Qed.

(** No can do, universe inconsistency:
<<
Definition CAT : category := Category category functor _ _ CAT_axioms.
>>
*)

(**  Natural transfomations, defined in the standard way.
  *)
Module NT.
Section nt.
  Variables C D:category.
  Variable F G:functor C D.

  Structure nt := NT
    { transform :> forall A, F A → G A
    ; axiom : forall A B (f:A → B), transform B ∘ F<$>f ≈ G<$>f ∘ transform A
    }.
End nt.

Arguments nt [C] [D] F G.
Arguments NT [C] [D] F G transform axiom.
Arguments transform [C] [D] [F] [G] (n)%_cat (A)%_cat_ob.
Arguments axiom [C] [D] [F] [G] n [A] [B] (f)%_cat.

Section nt_compose.
  Variables C D E:category.

  Program Definition ident (F:functor C D) : nt F F :=
    NT F F (fun A => id(F A)) _.
  Next Obligation.
    rewrite (cat_ident2 D).
    rewrite (cat_ident1 D).
    trivial.
  Qed.

  Program Definition compose (F G H:functor C D) (s:nt G H) (t:nt F G) : nt F H :=
    NT F H (fun A => s A ∘ t A) _.
  Next Obligation.
    rewrite <- (cat_assoc D _ _ _ _ (s B) (t B) (F<$>f)).
    rewrite (axiom t).
    rewrite (cat_assoc D _ _ _ _ (s B) (G<$>f) (t A)).
    rewrite (axiom s).
    rewrite <- (cat_assoc D).
    trivial.
  Qed.

  (**  There are two possible ways to combine a natural transformation
       with the action of a functor to get another natural transformation,
       depending on which side you wish to compose the functor.
    *)
  Program Definition stacknt
    (F:functor D E) (G H:functor C D)
    (n:nt G H) : nt (F ∘ G) (F ∘ H) :=
    NT _ _ (fun A => F<$>(n A)) _.
  Next Obligation.
    rewrite <- (Functor.compose F). 2: reflexivity.
    rewrite axiom.
    rewrite (Functor.compose F). 2: reflexivity.
    trivial.
  Qed.

  Program Definition pushnt
    (G H:functor D E)
    (n:nt G H) (F:functor C D)
    : nt (G ∘ F) (H ∘ F) :=
    NT _ _ (fun A => n (F A)) (fun A B f => NT.axiom n (F<$>f)).
End nt_compose.

Section NT_mixins.
  Variables C D:category.

  Program Definition NTEQ_mixin
    (G H:functor C D) :=
      (Eq.Mixin _ (fun s t:nt G H => forall A, s A ≈ t A) _ _ _).
  Next Obligation.
    eauto.
  Qed.

  Definition NTComp_mixin :=
    (Comp.Mixin (functor C D) (@nt C D)
      (ident C D) (compose C D)).
End NT_mixins.
End NT.

Coercion NT.transform : NT.nt >-> Funclass.
Notation "F ▹ nt" := (NT.stacknt _ _ _ F _ _ nt)
  : category_hom_scope.
Notation "nt ◃ F" := (NT.pushnt _ _ _ _ _ nt F)
  : category_hom_scope.
Notation nt := NT.nt.
Notation NT := NT.NT.

Canonical Structure NTEQ (C D:category) G H :=
  Eq.Pack (nt G H) (NT.NTEQ_mixin C D G H).

Canonical Structure NTComp (C D:category) :=
  Comp.Pack (functor C D) (@NT.nt C D) (NT.NTComp_mixin C D).


(**  [FUNC C D] is the functor category from [C] to [D],
     whose objects are the functors from [C] to [D] and whose
     morphisms are natural transformations.
  *)
Program Definition FUNC
  (C D:category) : category :=
  Category (functor C D) (@NT.nt C D)
           (NT.NTEQ_mixin C D)
           (NT.NTComp_mixin C D) _.
Next Obligation.
  intros. constructor.
  intros. hnf. intro. apply cat_ident1.
  intros. hnf. intro. apply cat_ident2.
  intros. hnf. intro. apply cat_assoc.
  intros. hnf. intro. apply cat_respects.
  apply H. apply H0.
Qed.

(* Would these do anything worthwhile ?
Canonical Structure FUNC_COMP C D := CAT_COMP _ _ (FUNC C D).
Canonical Structure FUNC_EQ C D := CAT_EQ _ _ (FUNC C D).
*)


(**  Here we define adjunction using the unit/counit definition.
  *)
Module Adjunction.
Section adjunction.
  Variable C D:category.
  Variable L:functor D C.
  Variable R:functor C D.

  Record adjunction :=
    Adjunction
    { unit   : nt id(D) (R ∘ L)
    ; counit : nt (L ∘ R) id(C)
    ; adjoint_axiom1 : counit◃L ∘ L▹unit ≈ id
    ; adjoint_axiom2 : R▹counit ∘ unit◃R ≈ id
    }.
End adjunction.

Arguments adjunction [C] [D] L R.
Arguments Adjunction [C] [D] L R _ _ _ _.
Arguments unit [C] [D] [L] [R] a.
Arguments counit [C] [D] [L] [R] a.
Arguments adjoint_axiom1 [C] [D] [L] [R] a _.
Arguments adjoint_axiom2 [C] [D] [L] [R] a _.
End Adjunction.

Notation Adjunction := Adjunction.Adjunction.
Notation adjunction := Adjunction.adjunction.


(**  Here we define the category of cones, the morphisms of which
     are homs in the original category that commute with the
     spokes of the cones.
  *)
Module Cone.
Section cone.
  Variable C:category.

  Variable J:category.
  Definition diagram := functor J C.
  Variable F:diagram.

  Record cone :=
    Cone
    { point : ob C
    ; spoke : forall j, point → (F j) 
    ; axiom : forall j j' (h:j → j'), spoke j' ≈ F<$>h ∘ spoke j 
    }.
  
  Record cone_hom (M N:cone) :=
    Cone_hom
    { hom_map :> point M → point N
    ; hom_axiom : forall j,
         spoke M j ≈ spoke N j ∘ hom_map
    }.
  Global Arguments hom_map [M] [N] c.
  Global Arguments hom_axiom [M] [N] c j.

  Program Definition cone_ident (M:cone) :=
    Cone_hom M M (id) _.
  Next Obligation. 
    rewrite (cat_ident1 C _ _ (spoke M j)). reflexivity.
  Qed.

  Program Definition cone_compose (M N O:cone)
    (f:cone_hom N O) (g:cone_hom M N) : cone_hom M O :=
    Cone_hom M O (hom_map f ∘ hom_map g) _.
  Next Obligation.
    intros.
    rewrite (hom_axiom g).
    rewrite (hom_axiom f).
    symmetry; apply cat_assoc.
  Qed.    

  Program Definition CONE : category :=
    Category cone cone_hom
      (fun A B => Eq.Mixin _ (fun f g => hom_map f ≈ hom_map g) _ _ _)
      (Comp.Mixin _ _ cone_ident cone_compose)
      _.
  Next Obligation.      
    eauto.
  Qed.
  Next Obligation.
    constructor.
    intros. apply cat_ident1.
    intros. apply cat_ident2.
    intros. apply cat_assoc.
    intros. apply cat_respects; auto.
  Qed.
End cone.
End Cone.

(**  Here we define algebras of an endofunctor, and we define
     initial algebras directly.  We'll be interested in
     initial algebras when it comes time to define recursive domains.
  *)
Module Alg.
Section alg.
  Variable C:category.
  Variable F:functor C C.

  Record alg :=
  Alg
  { carrier :> ob C
  ; iota : (F carrier) → carrier
  }.

  Record alg_hom (M N:alg) :=
  Alg_hom
  { hom_map : carrier M → carrier N
  ; hom_axiom : hom_map ∘ iota M ≈ iota N ∘ F<$>hom_map
  }.

  Program Definition ident (M:alg) : alg_hom M M :=
    Alg_hom M M (id) _.
  Next Obligation.
    intros.
    rewrite (cat_ident2 _ _ _ (iota M)).
    rewrite (Functor.ident F); trivial.
    rewrite (cat_ident1 _ _ _ (iota M)).
    trivial.
  Qed.

  Program Definition compose (M N O:alg)
    (f:alg_hom N O) (g:alg_hom M N) : alg_hom M O :=
    Alg_hom M O (hom_map _ _ f ∘ hom_map _ _ g) _.
  Next Obligation.
    intros.
    rewrite <- (cat_assoc _ _ _ _ _ (hom_map N O f)).
    rewrite (hom_axiom _ _ g).
    rewrite (cat_assoc _ _ _ _ _ (hom_map N O f)).
    rewrite (hom_axiom _ _ f).
    rewrite <- (cat_assoc _ _ _ _ _ (iota O)).
    rewrite <- (Functor.compose F); reflexivity.
  Qed.

  Record initial_alg :=
  Initial_alg
  { init :> alg
  ; cata : forall M:alg, alg_hom init M
  ; cata_axiom : forall (M:alg) (h:alg_hom init M), 
       hom_map _ _ h ≈ hom_map _ _ (cata M)
  }.

  Lemma cata_axiom' I :
    forall (M:alg) (h:carrier (init I) → carrier M),
      (h ∘ iota (init I) ≈ iota  M ∘ F<$>h) ->
      h ≈ hom_map _ _ (cata I M).
  Proof.
    intros.
    apply (cata_axiom I M (Alg_hom _ _ h H)).
  Qed.

  Definition lift_alg (A:alg) :=
    Alg (F A) (F<$>iota A).

  Definition out (I:initial_alg) :=
    hom_map _ _ (cata I (lift_alg I)).

  Lemma in_out : forall (I:initial_alg),
    iota I ∘ out I ≈ id.
  Proof.
    intros.
    transitivity (hom_map _ _ (cata I I)).
    - apply cata_axiom'.
      rewrite <- (cat_assoc _ _ _ _ _ (iota I)).
      apply cat_respects; auto.
      rewrite (hom_axiom _ _ (cata I (lift_alg I))).
      simpl.
      symmetry. apply Functor.compose. auto.

    - symmetry. apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite (Functor.ident F); auto.
      rewrite (cat_ident1 _ _ _ (iota I)).
      auto.
  Qed.

  Lemma out_in : forall (I:initial_alg),
    out I ∘ iota I ≈ id.
  Proof.
    intros.
    transitivity (F<$>(hom_map _ _ (cata I I))).
    - unfold out.
      rewrite (hom_axiom).
      simpl.
      symmetry.
      apply Functor.compose.
      rewrite in_out.
      symmetry.
      apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite Functor.ident.
      rewrite (cat_ident1 _ _ _ (iota I)).
      reflexivity. reflexivity.
    - apply Functor.ident.
      symmetry.
      apply cata_axiom'.
      rewrite (cat_ident2 _ _ _ (iota I)).
      rewrite Functor.ident.
      rewrite (cat_ident1 _ _ _ (iota I)).
      reflexivity. reflexivity.
  Qed.    

  Lemma initial_inj_epic : forall (I:initial_alg) B (g h: I → B),
    g ∘ iota I ≈ h ∘ iota I ->
    g ≈ h.
  Proof.
    intros.
    cut (g ∘ id ≈ h ∘ id ).
    { rewrite (cat_ident1 _ _ _ g).
      rewrite (cat_ident1 _ _ _ h).
      auto.
    }
    rewrite <- (in_out I).
    rewrite (cat_assoc _ _ _ _ _ g).
    rewrite H.
    rewrite (cat_assoc _ _ _ _ _ h).
    trivial.
  Qed.

End alg.
Arguments carrier [C] [F] a.
Arguments iota [C] [F] a.
Arguments alg_hom [C] [F] M N.
Arguments hom_map [C] [F] [M] [N] a.
Arguments hom_axiom [C] [F] [M] [N] a.
Arguments ident [C] [F] M.
Arguments compose [C] [F] [M] [N] [O] f g.
Arguments Alg [C] [F] carrier iota.
Arguments Alg_hom [C] [F] [M] [N] hom_map hom_axiom.

Arguments init [C] [F] i.
Arguments cata [C] [F] i M.
Arguments cata_axiom [C] [F] i M h.
Arguments Initial_alg [C] [F] init cata cata_axiom.

Program Definition ALG C (F:functor C C) : category :=
    Category (alg C F) (@alg_hom C F)
      (fun A B => Eq.Mixin _ (fun f g => Alg.hom_map f ≈ Alg.hom_map g) _ _ _)
      (Comp.Mixin _ _ (@ident _ _) (@compose _ _)) 
      _.
Next Obligation.
  eauto.
Qed.
Next Obligation.
  constructor.
  - intros. apply cat_ident1.
  - intros. apply cat_ident2.
  - intros. apply cat_assoc.
  - intros. apply cat_respects; auto.
Qed.
Arguments ALG [C] F.

Section forget.
  Variable (C:category).
  Variable (F:functor C C).

  Program Definition forget : functor (ALG F) C :=
    Functor (ALG F) C (@carrier C F) (@hom_map C F) _ _ _.
End forget.
Arguments forget [C] F.

Definition free C (F:functor C C) (FREE:functor C (ALG F)) :=
  adjunction FREE (Alg.forget F).
Arguments free [C] F FREE.

End Alg.

Coercion Alg.carrier : Alg.alg >-> ob.
Coercion Alg.init : Alg.initial_alg >-> Alg.alg.
Coercion Alg.hom_map : Alg.alg_hom >-> hom.
Notation ALG := Alg.ALG.
Notation Alg := Alg.Alg.
Notation alg := Alg.alg.

Canonical Structure Alg.ALG.
