
(**  ** Pullbacks *)
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