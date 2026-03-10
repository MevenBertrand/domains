(** * domains.plotkin: Plotkin orders and normal sets *)

From Stdlib Require Import List ssreflect.
From HB Require Import structures.
Require Import utils.all categories.all preord sets finsets colsets effective directed.

(**  ** 
  
    A Plotkin order is a preorder where every conditionally-inhabited,
    bounded finite set has a minimal upper bound; and where every
    finite set has a finite MUB closure.

    The Plotkin orders are alternately characterized has having
    finite normal sets.  A set X is normal if, for every z,
    the set { x | x ∈ X ∧ x ≤ z } is h-directed.  A preorder is
    Plotkin iff every conditionally-inhabted finite set has an
    enclosing finite normal set.

    Demonstrating the existence of normal sets is generally easier
    than producing finite MUB closures, so that is our preferred
    method for demonstrating that an order is Plotkin.

    It might be better (following Gunter) to simply take the normal
    set definition as primary and drop the MUB closure definition
    altogether.  That might make other things more complicated,
    I'm not sure.  Anyway, it would mean major changes to difficult
    proofs, like those in joinable.v.
  *)


(**  A preorder is MUB complete if every bounded, h-inhabited finite
     set has a least upper bound below the given bound.
  *)
Definition is_mub_complete hf (A:Poset) :=
  forall (M:finset A) (x:A), inh hf M -> upper_bound x M ->
    exists mub:A, minimal_upper_bound mub M /\ mub ≤ x.

(**  A set is MUB closed if it contains every MUB of every
     h-inhabited finite subset.
  *)
Definition mub_closed hf (A:Poset) (X:finset A) :=
  forall M:finset A, inh hf M -> M ⊆ X ->
    forall x:A, minimal_upper_bound x M -> x ∈ X.

(**  A Plotkin order is MUB complete and has a finite MUB closure
     operation.  Note, we explicitly require mub_closure to be
     the smallest MUB closure operation.  It is thus uniquely
     determined.  In fact, this requirement is not strictly necessary;
     given an arbitrary MUB closure operation, we can compute the
     minimal one.
  *)

#[primitive] HB.mixin Record IsPlotkin (hf : bool) (A : Type) of poset A :=
  {
  mub_complete : is_mub_complete hf A
  ; mub_closure : finset A -> finset A
  ; mub_clos_incl : forall M:finset A, M ⊆ mub_closure M
  ; mub_clos_mub : forall (M:finset A), mub_closed hf A (mub_closure M)
  ; mub_clos_smallest : forall (M X:finset A),
        M ⊆ X ->
        mub_closed hf A X -> 
        mub_closure M ⊆ X
  }.

#[short(type="PlotkinPoset"),primitive]
HB.structure Definition plotkin_poset (hf : bool) :=
  { T of poset T & IsPlotkin hf T}.

#[short(type="EffectivePlotkin"),primitive]
HB.structure Definition effective_plotkin (hf : bool) :=
  {T of eff_poset T & IsPlotkin hf T}.

(**  MUB-closure is actually a closure operation: it is
     monotone, inclusive and idempotent.
  *)
Lemma mub_clos_mono hf (A:PlotkinPoset hf) (M N:finset A) :
    M ⊆ N -> mub_closure M ⊆ mub_closure N.
Proof.
  intros.
  apply mub_clos_smallest; auto.
  - etransitivity ; tea.
    now apply mub_clos_incl.
  - now apply mub_clos_mub.
Qed.

Lemma mub_clos_idem hf (A : PlotkinPoset hf) (M:finset A) :
    mub_closure M = mub_closure (mub_closure M).
Proof.
  ext. split.
  - apply mub_clos_incl.
  - apply mub_clos_smallest; auto.
    1: reflexivity.
    apply mub_clos_mub; auto.
Qed.

(** ** Instances *)

(**  The empty preorder is Plotkin *)

Program Definition empty_plotkin hf :=
  IsPlotkin.Build hf False _ (fun _ => fempty) _ _ _.
Solve Obligations of empty_plotkin with (repeat intro; simpl in *; intuition).

HB.instance Definition _ hf := empty_plotkin hf.

(**  The unit preorder is Plotkin.
  *)
Program Definition unit_plotkin hf :=
  IsPlotkin.Build hf unit _ (fun M => if hf then M else (single tt)) _ _ _.
Next Obligation.
  repeat intro. exists tt.
  split; hnf; auto.
Qed.
Next Obligation.
  intros [].
  destruct hf; auto.
  rewrite singleP //.
Qed.
Next Obligation.
  intros ? Hinh Hsub [].
  destruct hf.
  - destruct Hinh as [[]].
    intros _.
    now apply Hsub.
  - rewrite singleP //.
Qed.
Next Obligation.
  repeat intro.
  destruct hf; [ apply H; auto |].
  apply (H0 M); auto.
  - red; auto.
  - split; hnf; auto.
    repeat intro. hnf. auto.
Qed.
 
(**  When a preorder is effective Plotkin, it is decidable if an
     element is an upper bound or a minimal upper bound of a finite set.
  *)

Instance upper_bound_dec (hf : bool) {A : DecPoset} (M:finset A) (x:A) :
  Decision (upper_bound x M).
Proof.
  unfold upper_bound.
  typeclasses eauto.
Qed.

Instance mub_finset_dec (hf : bool) {A : EffectivePlotkin hf} (M:finset A) (x:A) (Hinh:inh hf M) :
  Decision (minimal_upper_bound x M).
Proof.
  replace (minimal_upper_bound x M) with
    (upper_bound x M /\ (∀ b ∈ mub_closure M, upper_bound b M -> b ≤ x -> x ≤ b)).
  1: typeclasses eauto.
  unfold minimal_upper_bound.
  f_equal.
  unfold set_all.
  ext.
  split.
  2: easy.
  intros Hall b Hub Hle.
  destruct (mub_complete M b) as [b' [Hmub ?]]; auto.
  transitivity b' => //.
  apply Hall => //.
  3: now etransitivity.
  2: now apply Hmub.
  apply: mub_clos_mub ; eauto.
  apply mub_clos_incl.
Qed.

(**  We introduce the alternate characterization of Plotkin orders
     and preorders posessing enough normal sets.  The Plotkin->normal
     direction of equivalance is easy, but the other direction is rather
     involved.
  *)
Section normal_sets.
  Context (hf:bool) (A:EffPoset).

  (**  A set X is normal if it is h-inhabited and, for abitrary z,
       the intersection of X with { x | x ≤ z } is directed.
    *)
  Definition normal_set (X:finset A) :=
    (inh hf X) /\
    forall z, directed hf (finsubset (fun x => x ≤ z) X).

  (**  A preorder "has" normal sets if every h-inhabited set is inclosed in
       some finite normal set.
    *)
  Definition has_normals :=
    forall (X:finset A) (Hinh:inh hf X),
      { Z:finset A | X ⊆ Z /\ normal_set Z }.

End normal_sets.

Arguments normal_set _ {_} _.

(**  Plotkin orders have normal sets. *)

Lemma plt_has_normals (hf : bool) (A : EffectivePlotkin hf) : has_normals hf A.
Proof.
  red. intros X Xinh.
  exists (mub_closure X).
  split.
  1: now apply: mub_clos_incl.
  split.
  + apply inh_sub with X; auto.
    now apply: mub_clos_incl.
  + red; simpl; intros ??? Hsub.
    destruct (mub_complete M z) as (x& [Hmin]); auto ; cbn in *.
    1: now eapply incl_finsubset.
    exists x. split; auto.
    2: apply Hmin.
    rewrite finsubsetP ; split ; try easy.
    apply (mub_clos_mub X) with M; auto ; cbn.
    rewrite -> Hsub.
    now apply: finsubset_incl.
Qed.

  (**  Moreover, under the same conditions, we can calculate the set
       of minimal upper bounds of X.
    *)
Section normal_mubs.
  Context (hf : bool) {A : EffPoset} (Q:finset A) (HQ : normal_set hf Q)
    (X:finset A) (Hinh : inh hf X) (Hincl : X ⊆ Q).

  (**  Given a finite subset X of a normal set Q, we can compute the (finite) set of
       all upper bounds of X that lie in Q.  Furthermore, for each upper bound of X,
       there is some upper bound of X below it in Q.
      *)

  Lemma normal_has_ubs z : upper_bound z X -> ∃ m ∈ Q, upper_bound m X /\ m ≤ z.
  Proof.
    destruct HQ as [HQ' Hdir].
    intros Hz.
    destruct (Hdir z X) as [x [[]%finsubsetP]]; auto.
    - move => x Hx.
      rewrite finsubsetP.
      eauto.
    - now exists x.
  Qed.

  Lemma normal_all_mubs z : upper_bound z X ->
    forall m, minimal_upper_bound m X -> m ≤ z -> m ∈ Q.
  Proof.
    intros Hub m [? Hleast] Hle.
    destruct (normal_has_ubs m) as (m'&?&?);auto.
    enough (m = m') as -> by easy.
    apply ord_antisym.
    2: easy.
    now apply Hleast.
  Qed.

  Instance normal_sub_mub_dec x : Decision (minimal_upper_bound x X).
  Proof.
    destruct (decide (∃ y ∈ Q, upper_bound y X /\ y < x)) as [s|n].
    - right.
      destruct s as (m&?&?&?).
      intros [_ Hlub].
      now eapply lt_nle.
    - assert (∀ y ∈ Q, upper_bound y X -> y ≤ x -> y = x) as Heq.
      {
       intros y ???.
       apply (dec_stable _).
       intros ?.
       apply n.
       eexists ; now repeat split.
      }
      clear n.
      destruct (decide (upper_bound x X)).
      2: right ; intros [??] ; contradiction.
      left.
      red; intros.
      split; auto.
      intros.
      edestruct (normal_has_ubs b) as (m&?&?&?); auto.
      etransitivity ; tea.
      erewrite Heq ; eauto.
      1:reflexivity.
      now etransitivity.
  Qed.

  Let Y' := (finsubset (fun x => minimal_upper_bound x X) Q).

  Lemma normal_has_mubs z :
    upper_bound z X -> ∃ m ∈ Q, m ≤ z /\ minimal_upper_bound m X.
  Proof.
    intros Hz.
    destruct (normal_has_ubs z) as (m&Hm) ; auto.
    cut (forall (Y1 Y2:finset A), funion2 Y1 Y2 = (finsubset (fun x => upper_bound x X) Q)
          -> ∀ m ∈ Y2,
              (∀ y ∈ Y1, y ≤ m -> m ≤ y) ->
                m ≤ z -> exists m', m' ∈ Y2 /\ m' ≤ z /\ minimal_upper_bound m' X).
    { intros Hend.
      destruct (Hend fempty (finsubset (fun x => upper_bound x X) Q)) with m as (x&?%finsubsetP&?&?); auto.
      - ext.
        rewrite funion2P femptyP ; intuition.
      - rewrite finsubsetP ; intuition.
      - now intros ? ?%femptyP.
      - eexists ; intuition eauto.
    }
    clear m Hm.
    intros Y1 Y2.
    revert Y1.
    induction Y2 as [|a Y2 IH] using finset_ind ; simpl; intros Y1 Hunion m Hin HY1 Hle.
    1: by apply femptyP in Hin.
    destruct (decide (a ≤ m)) as [|Hnle] ; cycle -1.
    - destruct (IH (fcons a Y1)) with m as [m'] ; auto.
      + rewrite -Hunion.
        ext.
        rewrite !funion2P.
        intuition.
      + rewrite fconsP in Hin.
        destruct Hin as [->|] ; tea.
        now destruct Hnle.
      + intros ? [->|]%fconsP.
        all: intuition.
      + exists m'.
        intuition.
        now rewrite fconsP.
    - destruct (decide (∃ y ∈ (finsubset (fun x => upper_bound x X) Q), y < a))
        as [(m'&Hinm'&?&Hne)|] ; cycle -1.
      + exists a.
        split.
        1: now rewrite fconsP.
        split.
        1: now etransitivity.
        split.
        1: enough (a ∈ finsubset (fun x => upper_bound x X) Q) as ?%finsubsetP by easy.
        1: now rewrite -Hunion funion2P fconsP.
        * intros.
          apply (dec_stable _).
          intros Hnle.
          apply n.
          destruct (normal_has_ubs b) as (b'&?&?&?); auto.
          exists b'.
          split.
          1: now rewrite finsubsetP.
          split.
          1: now etransitivity.
          intros ->.
          intuition.
      + assert (m' ∈ Y2).
        {
          rewrite -Hunion funion2P fconsP in Hinm'.
          destruct Hinm' as [|[->|]].
          2-3: now intuition.
          exfalso.
          apply Hne, ord_antisym;auto.
          etransitivity ; tea.
          apply HY1;auto.
          now etransitivity.
        }
        destruct (IH (fcons a Y1)) with m' ; auto.
        * rewrite -Hunion.
          ext.
          rewrite !funion2P.
          intuition.
        * intros ? [->|]%fconsP; auto.
          intros.
          etransitivity ; tea.
          etransitivity ; tea.
          apply HY1 ; tea.
          repeat (etransitivity ; tea).
        * repeat (etransitivity ; tea).
        * exists x.
          rewrite fconsP.
          intuition.
  Qed.

End normal_mubs.

  (**  We can decide if a finite subset of a normal set is MUB closed.
    *)
  Lemma normal_sub_mub_closed_dec (hf : bool) (A : EffPoset) Q : normal_set hf Q ->
    forall (M:finset A), M ⊆ Q -> Decision (mub_closed hf A M).
  Proof.
    intros HQ M HM. 
    unfold mub_closed.
    replace (forall X : finset A, _) with
      (forall X:finset A, X ⊆ M -> inh hf X -> X ⊆ M -> forall x, minimal_upper_bound x X -> x ∈ M).
    2: ext ; now split.

    apply: finsubset_dec'.
    intros X. 
    destruct (decide (inh hf X)) as [Hinh|].
    2: now left; intro; contradiction.
    destruct (decide (X ⊆ M)) as [Hincl'|].
    2: now left ; intro ; contradiction.
    assert (X ⊆ Q) as Hincl by now etransitivity.
    pose proof (normal_sub_mub_dec _ Q HQ X Hinh Hincl).
    destruct (decide (∀ x ∈ (finsubset (fun x => minimal_upper_bound x X) Q), x ∈ M)) as [Hall|Hnall].
    + left.
      intros _ _ x Hx.
      edestruct (normal_has_mubs hf Q HQ X Hinh Hincl x) as (x'&?&?&?&?).
      1: now destruct Hx.
      enough (x = x') as -> by now apply Hall, finsubsetP.
      apply ord_antisym ; tea.
      now apply Hx.
    + right.
      move => /(_ Hinh Hincl') Hall.
      apply Hnall.
      rewrite /set_all.
      now setoid_rewrite finsubsetP.
  Qed.    
 
  (** We can calculate the (finite) set of all MUB closed finite subsets
      of a normal set.
    *)
  Lemma normal_set_mub_closed_sets (hf : bool) {A : EffPoset} Q  : normal_set hf Q ->
    { CLS : finset (finset A) | 
      forall X, X ∈ CLS <-> (inh hf X /\ X ⊆ Q /\ mub_closed hf A X) }.
  Proof.
    intros.
    assert (forall X : (finset A), X ∈ (finsubset (fun (X : finset A) => inh hf X) (fpow Q)) -> Decision (mub_closed hf A X)) as Hdec.
    {
      intros ? ?%finsubsetP.
      eapply normal_sub_mub_closed_dec ; tea.
      now rewrite -fpowP.
    }
    exists (finsubset_dep _ _ Hdec).
    intros X.
    rewrite finsubset_depP finsubsetP fpowP.
    intuition.
  Qed.

  (**  The intersection of any two MUB closed sets is itself MUB closed.
    *)
  Lemma mub_closed_intersect (hf : bool) (A : EffPoset) (X Y:finset A) :
    mub_closed hf A X -> mub_closed hf A Y ->
    mub_closed hf A (finter2 X Y).
  Proof.
    move => HX HY ? ? /finter2_incl Hincl x Hx.
    rewrite finter2P.
    split.
    - now apply: HX.
    - now apply: HY.
  Qed.

  (**  Any normal set is mub closed.
    *)
  Lemma normal_set_mub_closed (hf : bool) (A : EffPoset) Q : normal_set hf Q -> mub_closed hf A Q.
  Proof.
    intros ? M ?? x Hmub.
    unshelve edestruct (normal_has_mubs hf Q H M) as (MUBS&?&?&Hmub'); auto.
    1: apply Hmub.
    enough (x = MUBS) by now subst.
    apply ord_antisym ; tea.
    apply Hmub ; tea.
    apply Hmub'.
  Qed.

  (**  Given an h-inhabited finite subset of a normal set, we can compute
       the smallest MUB-closed superset.  This is done by taking the
       intersection of all the MUB-closed subsets of X that lie in Q.
    *)
  Lemma normal_set_mub_closure  (hf : bool) (A : EffPoset) Q : normal_set hf Q ->
    forall (M:finset A) (Minh : inh hf M), M ⊆ Q ->
      { CL:finset A | M ⊆ CL /\ mub_closed hf A CL /\
          forall CL':finset A, M ⊆ CL' -> mub_closed hf A CL' -> CL ⊆ CL' }.
  Proof.
    intros.
    destruct (normal_set_mub_closed_sets hf Q H) as [CLS ?]; auto.
    assert (Hsubdec : forall X:finset A, {M⊆X}+{~(M ⊆ X)}).
    { intros.
      destruct (finset_find_dec' A (fun z => z ∈ X)) with M; simpl.
      + intros. rewrite <- H1; auto.
      + apply finset_in_dec.
        constructor. apply eff_ord_dec; auto.
      + destruct s as [z [??]].
        right. intro. apply H3 in H1.
        contradiction.
      + left. red; auto.
    } 
    set (CLS' := finsubset (finset A) (fun X => M ⊆ X) Hsubdec CLS).
    exists (fin_list_intersect A OD CLS' Q).
    split.
    - red; intros.
      apply fin_list_intersect_elem.
      split.
        + apply H0; auto.
        + intros.
          unfold CLS' in H2.
          apply finsubset_elem in H2.
          * destruct H2. apply H3; auto.
          * intros. rewrite <- H4; auto.
    - split.
      + cut (forall x, x ∈ CLS' -> mub_closed hf A x).
        { generalize CLS'. clear -H.
          induction CLS'; intros.
          - simpl.
            apply normal_set_mub_closed; auto.
          - simpl.
            apply mub_closed_intersect.
            + apply H0.
              exists a; split; simpl; auto.
            + apply IHCLS'.
              intros. apply H0.
              destruct H1 as [q [??]]. exists q; split; simpl; auto.
        }
        intros.
        unfold CLS' in H1.
        apply finsubset_elem in H1.
        * destruct H1.
          apply i in H1.
          destruct H1 as [Hx [??]]; auto.
        * intros. rewrite <- H3; auto.
      + intros.
        red; intros.
        apply fin_list_intersect_elem in H3.
        destruct H3.
        assert (fin_intersect A OD CL' Q ∈ CLS').
        { unfold CLS'.
          apply finsubset_elem.
          - intros. rewrite <- H5; auto.
          - split; auto.
            + apply i.
              split.
              * destruct hf; auto.
                red in Minh. simpl.
                destruct Minh as [x ?].
                exists x.
                apply fin_intersect_elem. split; auto.
              * split; auto.
                ** red; intros.
                   apply fin_intersect_elem in H5.
                   destruct H5; auto.
                ** apply mub_closed_intersect; auto.
                   apply normal_set_mub_closed; auto.
            + red; intros.
              apply fin_intersect_elem.
              split; auto.
        } 
        apply H4 in H5.
        apply fin_intersect_elem in H5.
        destruct H5; auto.
  Qed.

  (**  In a MUB complete preorder, every MUB closed set is normal.
    *)
  Lemma mub_closed_normal_set : forall Q (HQ:inh hf Q),
    is_mub_complete hf A ->
    mub_closed hf A Q ->
    normal_set Q.
  Proof.
    intros. split; auto. repeat intro.
    set (Q' := finsubset A (fun x => x ≤ z) (fun x => eff_ord_dec A Heff x z) Q).
    destruct (H Q' z).
    - apply inh_sub with M; auto.
    - red; intros.
      unfold Q' in H2.
      apply finsubset_elem in H2.
      + destruct H2; auto.
      + intros. rewrite <- H4; auto.
    - destruct H2.
      assert (x ∈ Q).
      { apply (H0 Q'); auto.
        - apply inh_sub with M; auto.
        - unfold Q'; red; intros.
          apply finsubset_elem in H4.
          + destruct H4; auto.
          + intros. rewrite <- H6; auto.
      } 
      exists x. split; auto.
      + red; intros.
        destruct H2.
        apply H2.
        unfold Q'.
        apply finsubset_elem.
        * intros. rewrite <- H7; auto.
        * split; auto.
          ** apply H1 in H5.
             apply finsubset_elem in H5.
             *** destruct H5; auto.
             *** intros. rewrite <- H8; auto.
          ** apply H1 in H5.
             apply finsubset_elem in H5.
             *** destruct H5; auto.
             *** intros. rewrite <- H8; auto.
      + unfold Q'.
        apply finsubset_elem.
        * intros. rewrite <- H5; auto.
        * split; auto.
  Qed.

  Hypothesis Hnorm : has_normals.

  Lemma check_inh (X:finset A) : { X = nil /\ hf = true }+{ inh hf X }.
  Proof.
    destruct hf.
    - simpl.
      destruct X. left; auto.
      right. exists c. apply cons_elem; auto.
    - right. red. auto.
  Qed.

  (**  Define the MUB closure operation in a preorder with normal sets.
       Some slightly funny games are played here to ensure that the MUB
       closure operation is a total function even when hf = true.  In this
       case, the MUB closure of nil is nil; this works because nil is
       (vacuously) MUB closed when h = true.
    *)
  Definition norm_closure X :=
    match check_inh X with
    | left _ => nil
    | right Xinh =>
      match Hnorm X Xinh with
      | exist _ Q (conj HQ1 HQ2) => proj1_sig (normal_set_mub_closure Q HQ2 X Xinh HQ1)
      end
    end.

  (**  A preorder is Plotkin whenever it has normal sets.
    *)
  Program Definition norm_plt : plotkin_order hf A :=
    PlotkinOrder hf A _ norm_closure _ _ _.
  Next Obligation.
    red; intros.
    destruct (Hnorm M) as [Q [??]]; auto.
    destruct (normal_has_mubs Q H2 M H H1) as [MUBS [?[??]]].
    destruct (H5 x) as [m [?[??]]]; auto.
    exists m; split; auto.
  Qed.
  Next Obligation.
    repeat intro.
    unfold norm_closure.
    destruct (check_inh M).
    - destruct a0. subst M; auto.
    - destruct (Hnorm M i) as [Q [??]].
      destruct (normal_set_mub_closure Q n M i i0).
      simpl.
      destruct a0.
      apply H0. auto.
  Qed.    
  Next Obligation.
    repeat intro.
    unfold norm_closure in *.
    destruct (check_inh M).
    - destruct a. subst. rewrite H3 in H.
      destruct H. apply H0 in H.
      apply nil_elem in H. elim H.
    - destruct (Hnorm M i) as [Q [??]].
      destruct (normal_set_mub_closure Q n M i i0).
      simpl in *.
      destruct a. 
      destruct H3.
      apply H3 with M0; auto.
  Qed.    
  Next Obligation.
    repeat intro.
    unfold norm_closure in *.
    destruct (check_inh M).
    - apply nil_elem in H1. elim H1.
    - destruct (Hnorm M i) as [Q [??]].
      destruct (normal_set_mub_closure Q n M i i0).
      simpl in *.
      destruct a0 as [?[??]].
      apply H4; auto.
  Qed.    
End normal_sets.

(**  The product of two effective Plotkin orders has normal sets. *)
Lemma prod_has_normals hf (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HA:plotkin_order hf A)
  (HB:plotkin_order hf B) :
  has_normals (A×B) (effective_prod HAeff HBeff) hf.
Proof.
  red; intros.
  exists (finprod (mub_closure HA (image π₁ X))
                  (mub_closure HB (image π₂ X))).
  split.
  - red; intros.
    destruct a.
    apply finprod_elem.
    split.
    + apply mub_clos_incl.
      change c with (π₁#((c,c0):(A×B))).
      apply image_axiom1. auto.
    + apply mub_clos_incl.
      change c0 with (π₂#((c,c0):(A×B))).
      apply image_axiom1. auto.
  - apply mub_closed_normal_set.
    + destruct hf; auto.
      destruct Hinh as [x ?].
      exists x.
      destruct x as [a b].
      apply finprod_elem.
      split; apply mub_clos_incl; auto.
      * change a with (π₁#((a,b):A×B)).
        apply image_axiom1. auto.
      * change b with (π₂#((a,b):A×B)).
        apply image_axiom1. auto.

    + red. intros M x HMinh. intro.
      destruct x as [a b].
      destruct (mub_complete HA (image π₁ M) a).
      * apply inh_image; auto.
      * red; intros.
        apply image_axiom2 in H0.
        destruct H0 as [y [??]].
        apply H in H0.
        rewrite H1.
        destruct H0; auto.
      * destruct (mub_complete HB (image π₂ M) b).
        ** apply inh_image; auto.
        ** red; intros.
           apply image_axiom2 in H1.
           destruct H1 as [y [??]].
           apply H in H1.
           rewrite H2.
           destruct H1; auto.
        ** exists (x,x0).
           destruct H0. destruct H1.
           split; [ | split; auto ].
           split.
           *** red; intros.
               split.
               **** apply H0.
                    change (fst x1) with (π₁#x1). apply image_axiom1. auto.
               **** apply H1.
                    change (snd x1) with (π₂#x1). apply image_axiom1. auto.
           *** intros.
               split.
               **** destruct H0. apply H6; auto.
                    ***** red; intros.
                          apply image_axiom2 in H7.
                          destruct H7 as [y [??]].
                          apply H4 in H7.
                          rewrite H8. destruct H7; auto.
                    ***** destruct H5; auto.
               **** destruct H1. apply H6.
                    red; intros.
                    apply image_axiom2 in H7.
                    destruct H7 as [y [??]].
                    apply H4 in H7.
                    rewrite H8. destruct H7; auto.
                    destruct H5; auto.
    + red. intros M Minh. intros.
      destruct x.
      apply finprod_elem. split.
      * apply (mub_clos_mub HA (image π₁ X) ) with (image π₁ M).
        ** apply inh_image; auto.
        ** red; intros.
           apply image_axiom2 in H1. destruct H1 as [y [??]].
           apply H in H1.
           destruct y.
           apply finprod_elem in H1.
           destruct H1.
           rewrite H2; auto.
        ** destruct H0; split.
           *** red; intros.
               apply image_axiom2 in H2. destruct H2 as [y [??]].
               apply H0 in H2.
               rewrite H3. destruct H2; auto.
           *** intros.
               destruct (H1 (b,c0)).
               **** red; intros.
                    split.
                    ***** simpl.
                          apply H2.
                          change (fst x) with (π₁#x).
                          apply image_axiom1. auto.
                    ***** simpl.
                    apply H0 in H4.
                    destruct H4; auto.
               **** split; auto.
               **** simpl in *. auto.

      * apply (mub_clos_mub HB (image π₂ X)) with  (image π₂ M); auto.
        ** apply inh_image; auto.
        ** red; intros.
           apply image_axiom2 in H1. destruct H1 as [y [??]].
           apply H in H1.
           destruct y.
           apply finprod_elem in H1.
           destruct H1.
           rewrite H2; auto.
        ** destruct H0; split.
           *** red; intros.
               apply image_axiom2 in H2. destruct H2 as [y [??]].
               apply H0 in H2.
               rewrite H3. destruct H2; auto.
           *** intros.
               destruct (H1 (c,b)).
               **** red; intros.
                    split.
                    ***** simpl.
                          apply H0 in H4. destruct H4; auto.
                    ***** apply H2.
                    change (snd x) with (π₂#x).
                    apply image_axiom1. auto.
               **** split; auto.
               **** simpl in *. auto.
Qed.

(**  The product of two effective Plotkin orders is Plotkin. *)
Definition plotkin_prod hf (A B:preord)
  (HAeff:effective_order A) (HBeff:effective_order B)
  (HA:plotkin_order hf A) (HB:plotkin_order hf B)
  : plotkin_order hf (A×B)
  := norm_plt (A×B) (effective_prod HAeff HBeff) hf
         (prod_has_normals hf A B HAeff HBeff HA HB).


(** The disjoint union of two effective Plotkin orders has normal sets. *)
Lemma sum_has_normals hf (A B:preord)
  (HAeff:effective_order A)
  (HBeff:effective_order B)
  (HA:plotkin_order hf A)
  (HB:plotkin_order hf B) :
  has_normals (sum_preord A B) (effective_sum HAeff HBeff) hf.
Proof.
  hnf; intros.  
  set (L := left_finset A B X).
  set (R := right_finset A B X).
  destruct hf.
  
  - case_eq L.
    + intro.
      case_eq R.
      * intro.
        exfalso.
        destruct Hinh.
        destruct x.
        ** apply left_finset_elem in H1.
           unfold L in *.
           rewrite H in H1. apply nil_elem in H1. elim H1.
        ** apply right_finset_elem in H1.
           unfold R in *.
           rewrite H0 in H1. apply nil_elem in H1. elim H1.

      * intros c l HR.
        destruct (plt_has_normals B HBeff true HB R) as [Z' [??]].
        ** hnf. exists c. rewrite HR. apply cons_elem; auto.
        ** exists (finsum nil Z').
           split.
           *** hnf. intros.
               rewrite (left_right_finset_finsum A B) in H2.
               destruct a.
               **** apply finsum_left_elem in H2.
                    unfold L in H. rewrite H in H2.
                    apply nil_elem in H2. elim H2.
               **** apply finsum_right_elem in H2.
                    apply H0 in H2. 
                    apply finsum_right_elem. auto.
           *** split.
               **** exists (inr c).
                    apply finsum_right_elem. apply H0.
                    rewrite HR. apply cons_elem; auto.
               **** repeat intro.
                    destruct Hinh0 as [m Hm].
                    destruct m as [m|m].
                    ***** apply H2 in Hm.
                          apply finsubset_elem in Hm.
                          destruct Hm.
                          apply finsum_left_elem in H3.
                          apply nil_elem in H3. elim H3.
                          intros. rewrite <- H4; auto.
                    ***** { generalize (H2 (inr m) Hm).  
                            intros.
                            apply finsubset_elem in H3.
                            destruct H3.
                            apply finsum_right_elem in H3.
                            destruct z as [z|z]. elim H4.
                            destruct H1.
                            destruct (H5 z (right_finset A B M)) as [q [??]].
                            - exists m. apply right_finset_elem. auto.
                            - hnf; intros.
                              apply finsubset_elem.
                              intros. rewrite <- H7; auto.
                              apply right_finset_elem in H6.
                              apply H2 in H6.
                              apply finsubset_elem in H6.
                              destruct H6. split; auto.
                              apply finsum_right_elem in H6.
                              auto.
                              intros. rewrite <- H8. auto.
                            - apply finsubset_elem in H7. destruct H7.
                              exists (inr q). split.
                              + hnf; intros.
                                destruct x.
                                * apply H2 in H9.
                                  apply finsubset_elem in H9.
                                  destruct H9. elim H10.
                                  intros. rewrite <- H11; auto.
                                * apply H6.
                                  apply right_finset_elem. auto.
                              + apply finsubset_elem.
                                intros. rewrite <- H9; auto.
                                split; auto.
                                apply finsum_right_elem. auto.
                              + intros. rewrite <- H9. auto.
                            - intros. rewrite <- H5. auto.
                          } 
    + intros c l HL.
      case_eq R; intro.
      * destruct (plt_has_normals A HAeff true HA L) as [Z' [??]].
        ** hnf. exists c. rewrite HL. apply cons_elem; auto.
        ** exists (finsum Z' nil).
           split.
           *** hnf. intros.
               rewrite (left_right_finset_finsum A B) in H2.
               destruct a.
               **** apply finsum_left_elem in H2.
                    apply finsum_left_elem. auto.
               **** apply finsum_right_elem in H2.
                    unfold R in H. rewrite H in H2.
                    apply nil_elem in H2. elim H2.
           *** split.
               **** exists (inl c).
                    apply finsum_left_elem. apply H0.
                    rewrite HL. apply cons_elem; auto.
               **** repeat intro.
                    destruct Hinh0 as [m Hm].
                    destruct m as [m|m].
                    { generalize (H2 (inl m) Hm).  
                      intros.
                      apply finsubset_elem in H3.
                      destruct H3.
                      apply finsum_left_elem in H3.
                      destruct z as [z|z]. 2: elim H4.
                      destruct H1.
                      destruct (H5 z (left_finset A B M)) as [q [??]].
                      - exists m. apply left_finset_elem. auto.
                      - hnf; intros.
                        apply finsubset_elem.
                        intros. rewrite <- H7; auto.
                        apply left_finset_elem in H6.
                        apply H2 in H6.
                        apply finsubset_elem in H6.
                        destruct H6. split; auto.
                        apply finsum_left_elem in H6.
                        auto.
                        intros. rewrite <- H8. auto.
                      - apply finsubset_elem in H7. destruct H7.
                        exists (inl q). split.
                        + hnf; intros.
                          destruct x.
                          * apply H6.
                            apply left_finset_elem. auto.
                          * apply H2 in H9.
                            apply finsubset_elem in H9.
                            destruct H9. elim H10.
                            intros. rewrite <- H11; auto.
                        + apply finsubset_elem.
                          intros. rewrite <- H10; auto.
                          split; auto.
                          apply finsum_left_elem. auto.
                        + intros. rewrite <- H9. auto.
                      - intros. rewrite <- H5. auto.
                    }
                    apply H2 in Hm.
                    apply finsubset_elem in Hm.
                    destruct Hm.
                    apply finsum_right_elem in H3.
                    apply nil_elem in H3. elim H3.
                    intros. rewrite <- H4; auto.

      * intros l' HR.
        destruct (plt_has_normals A HAeff true HA L) as [ZL [??]].
        { exists c. rewrite HL. apply cons_elem; auto. }
        destruct (plt_has_normals B HBeff true HB R) as [ZR [??]].
        { exists c0. rewrite HR. apply cons_elem; auto. }
        exists (finsum ZL ZR).  
        split.
        ** hnf; intros.
           rewrite (left_right_finset_finsum A B) in H3.
           destruct a.
           *** apply finsum_left_elem in H3.
               apply H in H3.
               apply finsum_left_elem. auto.
           *** apply finsum_right_elem in H3.
               apply H1 in H3.
               apply finsum_right_elem. auto.
        ** hnf; intros.
           split.  
           *** exists (inl c).
               apply finsum_left_elem.
               apply H. rewrite HL. apply cons_elem; auto.
           *** repeat intro.
               destruct z as [z|z].
               **** destruct H0.
                    destruct (H4 z (left_finset A B M)).
                    ***** destruct Hinh0.
                          destruct x.
                          exists c1.
                          apply left_finset_elem. auto.
                          apply H3 in H5.
                          apply finsubset_elem in H5.
                          destruct H5. elim H6.
                          intros. rewrite <- H7; auto.
                    ***** hnf; simpl; intros.
                          apply left_finset_elem in H5.
                          apply H3 in H5.
                          apply finsubset_elem in H5.
                          destruct H5.
                          apply finsubset_elem.
                          intros. rewrite <- H7; auto.
                          split; auto.
                          apply finsum_left_elem in H5; auto.
                          intros. rewrite <- H7; auto.
                    ***** destruct H5. exists (inl x).
                          split.
                          { hnf; intros.
                            destruct x0.
                            apply H5.
                            apply left_finset_elem. auto.
                            apply H3 in H7.
                            apply finsubset_elem in H7.
                            destruct H7. elim H8.
                            intros. rewrite <- H9; auto.
                          }
                          apply finsubset_elem.
                          intros. rewrite <- H7; auto.
                          apply finsubset_elem in H6.
                          destruct H6. split; auto.
                          apply finsum_left_elem; auto.
                          intros. rewrite <- H8; auto.
               **** destruct H2.
                    destruct (H4 z (right_finset A B M)).
                    ***** destruct Hinh0 as [m Hm].
                          destruct m.
                          ****** apply H3 in Hm.
                                 apply finsubset_elem in Hm.
                                 destruct Hm. elim H6.
                                 intros. rewrite <- H6; auto.
                          ****** exists c1. apply right_finset_elem; auto.
                    ***** hnf; intros.
                          apply right_finset_elem in H5.
                          apply finsubset_elem.
                          intros. rewrite <- H6; auto.
                          apply H3 in H5.
                          apply finsubset_elem in H5.
                          destruct H5. split; auto.
                          apply finsum_right_elem in H5. auto.
                          intros. rewrite <- H7; auto.
                    ***** exists (inr x).
                          destruct H5. split.
                          ****** hnf; intros.
                                 destruct x0.
                                 ******* apply H3 in H7.
                                         apply finsubset_elem in H7.
                                         destruct H7. elim H8.
                                         intros. rewrite <- H9; auto.
                                 ******* apply H5. apply right_finset_elem; auto.
                          ****** apply finsubset_elem.
                                 intros. rewrite <- H8; auto.
                                 apply finsubset_elem in H6.
                                 destruct H6. split; auto.
                                 apply finsum_right_elem; auto.
                                 intros. rewrite <- H8; auto.
  
  - destruct (plt_has_normals A HAeff false HA L) as [ZL [??]]; [ hnf; auto |].
    destruct (plt_has_normals B HBeff false HB R) as [ZR [??]]; [ hnf; auto |].
    exists (finsum ZL ZR).  
    split.
    { hnf; intros.
      rewrite (left_right_finset_finsum A B) in H3.
      destruct a.
      - apply finsum_left_elem in H3.
        apply H in H3.
        apply finsum_left_elem. auto.
      - apply finsum_right_elem in H3.
        apply H1 in H3.
        apply finsum_right_elem. auto.
    } 
    hnf; intros.
    split; [ hnf; auto |].
    repeat intro.
    destruct z as [z|z].
    + destruct H0.
      destruct (H4 z (left_finset A B M)).
      * hnf; auto.
      * hnf; simpl; intros.
        apply left_finset_elem in H5.
        apply H3 in H5.
        apply finsubset_elem in H5.
        ** destruct H5.
           apply finsubset_elem.
           intros. rewrite <- H7; auto.
           split; auto.
           apply finsum_left_elem in H5; auto.
        ** intros. rewrite <- H7; auto.
      * destruct H5. exists (inl x).
        split.
        ** hnf; intros.
           destruct x0.
           *** apply H5.
               apply left_finset_elem. auto.
           *** apply H3 in H7.
               apply finsubset_elem in H7.
               destruct H7. elim H8.
               intros. rewrite <- H9; auto.
        ** apply finsubset_elem.
           intros. rewrite <- H8; auto.
           apply finsubset_elem in H6.
           *** destruct H6. split; auto.
               apply finsum_left_elem; auto.
           *** intros. rewrite <- H8; auto.
    + destruct H2.
      destruct (H4 z (right_finset A B M)).
      * hnf; auto.
      * hnf; intros.
        apply right_finset_elem in H5.
        apply finsubset_elem.
        intros. rewrite <- H6; auto.
        apply H3 in H5.
        apply finsubset_elem in H5.
        destruct H5. split; auto.
        apply finsum_right_elem in H5. auto.
        intros. rewrite <- H7; auto.
      * exists (inr x).
        destruct H5. split.
        ** hnf; intros.
           destruct x0.
           apply H3 in H7.
           apply finsubset_elem in H7. destruct H7. elim H8.
           intros. rewrite <- H9; auto.
           apply H5. apply right_finset_elem; auto.
        ** apply finsubset_elem.
           intros. rewrite <- H7; auto.
           apply finsubset_elem in H6.
           destruct H6. split; auto.
           apply finsum_right_elem; auto.
           intros. rewrite <- H8; auto.
Qed.

(** The disjoint union of two effective Plotkin orders is Plotkin. *)
Definition plotkin_sum hf (A B:preord)
  (HAeff:effective_order A) (HBeff:effective_order B)
  (HA:plotkin_order hf A) (HB:plotkin_order hf B)
  : plotkin_order hf (sum_preord A B)
  := norm_plt (sum_preord A B) 
         (effective_sum HAeff HBeff) hf
         (sum_has_normals hf A B HAeff HBeff HA HB).


(**  Next we show that adding a new bottom element to an effective
     Plotkin order yields another Plotkin order.
  *)
Fixpoint unlift_list {A} (x:list (option A)) :=
  match x with
  | nil => nil
  | None :: x' => unlift_list x'
  | Some a :: x' => a :: unlift_list x'
  end.

Lemma unlift_app A (l l':list (option A)) :
  unlift_list (l++l') = unlift_list l ++ unlift_list l'.
Proof.
  induction l; simpl; intuition.
  destruct a; simpl; auto.
  f_equal; auto.
Qed.

Lemma in_unlift A (l:list (option A)) x :
  In x (unlift_list l) <-> In (Some x) l.
Proof.
  induction l; simpl; intuition.
  - destruct a; simpl in *.
    intuition subst; auto.
    right; auto.
  - subst. simpl; auto.
  - destruct a; simpl; auto.
Qed.

Lemma incl_unlift A (l l':list (option A)) :
  List.incl l l' -> List.incl (unlift_list l) (unlift_list l').
Proof.
  induction l; repeat intro; simpl in *; intuition.
  destruct a; simpl in *; intuition subst; auto.
  - rewrite in_unlift.
    apply H; simpl; auto.
  - rewrite in_unlift.
    rewrite in_unlift in H1.
    apply H; simpl; auto.
  - apply IHl; auto.
    hnf; intros. apply H; simpl; auto.
Qed.

Definition lift_mub_closure hf (A:preord) (HA:plotkin_order hf A) (M:finset (lift A)) 
  : finset (lift A):=
  match unlift_list M with
  | nil => single None
  | X => None :: image (liftup A) (mub_closure HA X)
  end.

(** The lift preorder of had normal sets. *)
Lemma lift_has_normals hf1 hf2 (A:preord)
  (Heff:effective_order A)
  (Hplt:plotkin_order hf1 A) :
  has_normals (lift A) (effective_lift Heff) hf2.
Proof.
  red; intros.
  set (X' := unlift_list X : finset A).
  assert (forall a, a ∈ X' <-> Some a ∈ X).
  { intro; split; intros.
    - destruct H as [q [??]].
      apply in_unlift in H.
      exists (Some q). split; auto.
    - destruct H as [q [??]].
      destruct q.
      + exists c. split; auto.
        apply in_unlift. auto.
      + destruct H0. elim H0.
  } 
  exists (lift_mub_closure hf1 A Hplt X).
  split.
  - red; intros.
    unfold lift_mub_closure.
    case_eq (unlift_list X).
    + intros.
      destruct H0 as [q [??]].
      destruct a.
      * destruct q.
        ** assert (In c0 (unlift_list X)).
           { apply in_unlift. auto. }
           rewrite H1 in H3. elim H3.
        ** destruct H2. elim H2.
      * apply single_axiom; auto.
    + intros.
      destruct a.
      * apply cons_elem. right.
        apply image_axiom1'.
        exists c0. split; auto.
        apply mub_clos_incl.
        destruct H0 as [q [??]].
        destruct q.
        ** exists c1. split; auto.
           rewrite <- H1.
           apply in_unlift. auto.
        ** destruct H2. elim H2.
      * apply cons_elem; auto.

  - hnf; intros.
    split.
    + unfold lift_mub_closure.
      destruct hf2; simpl; auto.
      exists None.
      destruct (unlift_list X); simpl.
      * apply single_axiom. auto.
      * apply cons_elem; auto.
  
    + repeat intro.
      case_eq (unlift_list M); intros.
      * exists (None : lift A). split.
        ** hnf; intros.
           destruct x; auto.
           destruct H2 as [q [??]].
           destruct q.
           *** assert (In c0 (unlift_list M)).
               { apply in_unlift. auto. }
               rewrite H1 in H4. elim H4.
           *** destruct H3. elim H3.
        ** apply finsubset_elem.
           intuition. rewrite <- H2; auto.
           split; auto.
           *** unfold lift_mub_closure.
               destruct (unlift_list X); auto.
               apply single_axiom; auto.
               apply cons_elem; auto.
           *** red. simpl; auto.

      * destruct z.
        ** destruct (mub_complete Hplt (unlift_list M) c0) as [ub [??]].
           *** rewrite H1.
               destruct hf1; simpl; auto.
               exists c. apply cons_elem; auto.
           *** hnf; intros.
               assert (Some x ∈ M).
               **** destruct H2 as [q [??]].
                    apply in_unlift in H2.
                    exists (Some q). split; auto.
               **** generalize H3; intros.
                    apply H0 in H3.
                    apply finsubset_elem in H3.
                    destruct H3. auto.
                    intros. rewrite <- H6; auto.
           *** exists (Some ub).
               split.
               **** hnf; intros.
                    destruct H2.
                    destruct x; auto.
                    ***** assert (c1 ∈ (unlift_list M : finset A)).
                          { destruct H4 as [q [??]].
                            destruct q.
                            - exists c2.
                              split; auto.
                              apply in_unlift. auto.
                            - destruct H6. elim H6.
                          } 
                          apply H2 in H6. auto.
                    ***** red; simpl; auto.
               **** apply finsubset_elem.
                    intros. rewrite <- H4; auto.
                    split; auto.
                    unfold lift_mub_closure.
                    case_eq (unlift_list X).
                    ***** intros.
                          assert (Some c ∈ M).
                          { exists (Some c); split; auto.
                            apply in_unlift. rewrite H1. simpl; auto.
                          } 
                          apply H0 in H5.
                          apply finsubset_elem in H5.
                          destruct H5.
                          unfold lift_mub_closure in H5.
                          rewrite H4 in H5.
                          apply single_axiom in H5. destruct H5. elim H5.
                          intros. rewrite <- H7; auto.
                    ***** intros.
                          apply cons_elem. right.
                          apply image_axiom1'.
                          exists ub. split; auto.
                          rewrite <- H4.
                          apply mub_clos_mub with (unlift_list M); auto.
                          ****** rewrite H1.
                                 destruct hf1; simpl; auto.
                                 exists c. apply cons_elem; auto.

                          ****** hnf; intros.
                                 assert (Some a ∈ M).
                                 { destruct H5 as [q [??]].
                                   exists (Some q). split; auto.
                                   apply in_unlift; auto.
                                 } 
                                 apply H0 in H6.
                                 apply finsubset_elem in H6.
                                 destruct H6.
                                 unfold lift_mub_closure in H6.
                                 rewrite H4 in H6.
                                 rewrite <- H4 in H6.
                                 apply cons_elem in H6.
                                 destruct H6.
                                 destruct H6. elim H6.
                                 apply image_axiom2 in H6.
                                 destruct H6 as [y [??]].
                                 simpl in H8.
                                 apply member_eq with y; auto.
                                 intros. rewrite <- H8; auto.
  
        ** assert (Some c ∈ M).
           { exists (Some c); split; auto.
             apply in_unlift. rewrite H1. simpl; auto.
           } 
           apply H0 in H2.
           apply finsubset_elem in H2.
           destruct H2. elim H3.
           intros. rewrite <- H4. auto.
Qed.

(** The lift preorder of an effective Plotkin order is Plotkin. *)
Definition lift_plotkin hf1 hf2 (A:preord)
  (Hplt:plotkin_order hf1 A) 
  (Heff:effective_order A)
  : plotkin_order hf2 (lift A)
  := norm_plt (lift A) (effective_lift Heff) hf2
         (lift_has_normals hf1 hf2 A Heff Hplt).
