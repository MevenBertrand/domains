
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
