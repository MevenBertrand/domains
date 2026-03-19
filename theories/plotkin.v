(** * domains.plotkin: Plotkin orders and normal sets *)

From Stdlib Require Import List ssreflect ssrfun.
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
Definition mub_closed hf {A:Poset} (X:finset A) :=
  forall M:finset A, inh hf M -> M ⊆ X ->
    forall x:A, minimal_upper_bound x M -> x ∈ X.

(**  A Plotkin order is MUB complete and has a finite MUB closure
     operation.  Note, we explicitly require mub_closure to be
     the smallest MUB closure operation.  It is thus uniquely
     determined.  In fact, this requirement is not strictly necessary;
     given an arbitrary MUB closure operation, we can compute the
     minimal one.
  *)

#[primitive] HB.mixin Record IsPlotkin (hf : bool) (A : Type) of eff_poset A :=
  {
  #[canonical=no]mub_complete : is_mub_complete hf A ;
  #[canonical=no]mub_closure : finset A -> finset A ;
  #[canonical=no]mub_clos_incl : forall M:finset A, M ⊆ mub_closure M ;
  #[canonical=no]mub_clos_mub : forall (M:finset A), mub_closed hf (mub_closure M) ;
  #[canonical=no]mub_clos_smallest : forall (M X:finset A),
        M ⊆ X ->
        mub_closed hf X -> 
        mub_closure M ⊆ X
  }.


(**  We introduce the alternate characterization of Plotkin orders
     and preorders posessing enough normal sets.  The Plotkin->normal
     direction of equivalance is easy, but the other direction is rather
     involved. *)
  (**  A set X is normal if it is h-inhabited and, for abitrary z,
       the intersection of X with { x | x ≤ z } is directed.
    *)
  Definition normal_set (hf:bool) {A:EffPoset} (X:finset A) :=
    (inh hf X) /\
    forall z, directed hf (finsubset (fun x => x ≤ z) X).

(**  A preorder "has" normal sets if every h-inhabited set is inclosed in
       some finite normal set.
  *)
#[primitive] HB.factory Record HasNormals (hf : bool) (A : Type) of eff_poset A :=
  {
  has_normals : forall (X:finset A) (Hinh:inh hf X), { Z:finset A | X ⊆ Z /\ normal_set hf Z }
  }.

#[short(type="PlotkinOrder"),primitive]
HB.structure Definition effective_plotkin (hf : bool) :=
  {T of eff_poset T & IsPlotkin hf T}.

(**  MUB-closure is actually a closure operation: it is
     monotone, inclusive and idempotent.
  *)
Lemma mub_clos_mono hf (A:PlotkinOrder hf) (M N:finset A) :
    M ⊆ N -> mub_closure M ⊆ mub_closure N.
Proof.
  intros.
  apply mub_clos_smallest; auto.
  - etransitivity ; tea.
    now apply mub_clos_incl.
  - now apply mub_clos_mub.
Qed.

Lemma mub_clos_idem hf (A : PlotkinOrder hf) (M:finset A) :
    mub_closure M = mub_closure (mub_closure M).
Proof.
  ext. split.
  - apply mub_clos_incl.
  - apply mub_clos_smallest; auto.
    1: reflexivity.
    apply mub_clos_mub; auto.
Qed.

(** ** Plotkin orders have normal sets *)

Lemma plt_has_normals {hf} {A : PlotkinOrder hf} (X:finset A) (Hinh:inh hf X) :
  { Z:finset A | X ⊆ Z /\ normal_set hf Z }.
Proof.
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

(** ** Instances *)


(**  The empty preorder is Plotkin *)

Program Definition void_plotkin hf :=
  IsPlotkin.Build hf void _ (fun _ => fempty) _ _ _.
Solve Obligations of void_plotkin with (repeat intro; simpl in *; intuition).

HB.instance Definition _ hf := void_plotkin hf.

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

Instance upper_bound_dec {A : DecPoset} (M:finset A) (x:A) :
  Decision (upper_bound x M).
Proof.
  unfold upper_bound.
  typeclasses eauto.
Qed.

Instance mub_finset_dec {hf : bool} {A : PlotkinOrder hf} (M:finset A) (x:A) (Hinh:inh hf M) :
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

  (**  We can calculate the set of minimal upper bounds of X. *)
Section normal_mubs.
  Context {hf : bool} {A : EffPoset} (Q:finset A) (HQ : normal_set hf Q)
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
       eapply n.
       eexists ; now repeat split.
      }
      clear n.
      destruct (decide (upper_bound x X)).
      2: now right; intros [? _].
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
        as [(m'&Hinm'&?&Hne)|Hneg] ; cycle -1.
      + exists a.
        split.
        1: now rewrite fconsP.
        split.
        1: now etransitivity.
        split.
        1: enough (a ∈ finsubset (fun x => upper_bound x X) Q) as ?%finsubsetP by easy.
        1: now rewrite -Hunion funion2P fconsP.
        * intros.
          destruct (normal_has_ubs b) as (b'&?&?&?); auto.
          apply finset_not_ex in Hneg.
          specialize (Hneg b').
          rewrite finsubsetP lt_le_eq in Hneg.
          transitivity b' ; tea.
          rewrite Hneg ; auto.
          2: reflexivity.
          now etransitivity.
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
Lemma normal_sub_mub_closed_dec {hf : bool} {A : EffPoset} Q : normal_set hf Q ->
  forall (M:finset A), M ⊆ Q -> Decision (mub_closed hf M).
Proof.
  intros HQ M HM. 
  unfold mub_closed.
  replace (forall X : finset A, _) with
    (forall X:finset A, X ⊆ M -> inh hf X -> X ⊆ M -> forall x, minimal_upper_bound x X -> x ∈ M).
  2: ext ; now split.

  apply: finsubset_dec'.
  intros X. 
  destruct (decide (inh hf X)) as [Hinh|[-> ->]%not_inh].
  2: now left ; move => [? ] /femptyP.
  destruct (decide (X ⊆ M)) as [Hincl'|].
  2: now left ; intro ; contradiction.
  assert (X ⊆ Q) as Hincl by now etransitivity.
  pose proof (normal_sub_mub_dec Q HQ X Hinh Hincl).
  destruct (decide (∀ x ∈ (finsubset (fun x => minimal_upper_bound x X) Q), x ∈ M)) as [Hall|Hnall].
  + left.
    intros _ _ x Hx.
    edestruct (normal_has_mubs Q HQ X Hinh Hincl x) as (x'&?&?&?&?).
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

Lemma normal_set_mub_closed_sets {hf : bool} {A : EffPoset} Q  : normal_set hf Q ->
  { CLS : finset (finset A) | 
    forall X, X ∈ CLS <-> (inh hf X /\ X ⊆ Q /\ mub_closed hf X) }.
Proof.
  intros.
  assert (forall X : (finset A), X ∈ (finsubset (fun (X : finset A) => inh hf X) (fpow Q)) -> Decision (mub_closed hf X)) as Hdec.
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

(**  The intersection of any number MUB closed sets is itself MUB closed.
  *)

Lemma mub_closed_finter {hf : bool} {A : EffPoset} (XS : finset (finset A)) (Y : finset A) :
  mub_closed hf Y ->
  (∀ X ∈ XS, mub_closed hf X) ->
  mub_closed hf (finter Y XS).
Proof.
  move => HY HXS ? ? /finter_incl [HinclY HinclXS] x Hx.
  rewrite finterP.
  split.
  - now apply: HY.
  - intros X HX.
    now apply: HXS.
Qed.

Lemma mub_closed_finter2 {hf : bool} {A : EffPoset} (X Y : finset A) :
  mub_closed hf X -> mub_closed hf Y ->
  mub_closed hf (finter2 X Y).
Proof.
  move => HX HY ? ? /finter2_incl Hincl x Hx.
  rewrite finter2P.
  split.
  - now apply: HX.
  - now apply: HY.
Qed.

(**  Any normal set is mub closed.
  *)
Lemma normal_set_mub_closed {hf : bool} {A : EffPoset} (Q : finset A) : normal_set hf Q -> mub_closed hf Q.
Proof.
  intros ? M ?? x Hmub.
  unshelve edestruct (normal_has_mubs Q H M) as (MUBS&?&?&Hmub'); auto.
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
Lemma normal_set_mub_closure {hf : bool} {A : EffPoset} (Q : finset A) : normal_set hf Q ->
  forall (M:finset A) (Minh : inh hf M), M ⊆ Q ->
    { CL:finset A | M ⊆ CL /\ mub_closed hf CL /\
        forall CL':finset A, M ⊆ CL' -> mub_closed hf CL' -> CL ⊆ CL' }.
Proof.
  intros.
  destruct (normal_set_mub_closed_sets Q H) as [CLS HCLS]; auto.
  set (CLS' := finsubset (fun X : finset A => M ⊆ X) CLS).
  exists (finter Q CLS').
  split ; [|split].
  - intros ? Hin.
    rewrite finterP.
    split ; [easy|].
    intros Y HY.
    rewrite /CLS' finsubsetP in HY.
    now apply HY.
  - apply mub_closed_finter.
    1: now apply: normal_set_mub_closed.
    intros ? ?%finsubsetP.
    now apply HCLS.
  - move => CL' Hincl HCL' x /finterP [HQ HCLS'].
    enough (finter2 CL' Q ∈ CLS') as ?%HCLS'%finter2P by easy.
    rewrite /CLS' finsubsetP.
    split.
    2: now rewrite finter2_incl.
    apply HCLS ; split ; [|split].
    + destruct hf ; cbn in * ; try easy.
      destruct Minh.
      eexists.
      rewrite finter2P ; eauto.
    + intros ?.
      now rewrite finter2P.
    + apply mub_closed_finter2 ; auto.
      now apply normal_set_mub_closed. 
Qed.

(**  In a MUB complete preorder, every MUB closed set is normal.
  *)
Lemma mub_closed_normal_set {hf : bool} {A : EffPoset} (Q : finset A) :
  inh hf Q ->
  is_mub_complete hf A ->
  mub_closed hf Q ->
  normal_set hf Q.
Proof.
  intros Hinh Hcomp Hclos. split; auto. intros z M Hinh' Hincl.
  set (Q' := (finsubset (fun x => x ≤ z) Q)) in *.
  destruct (Hcomp Q' z) as (x&Hmub&?).
  - apply inh_sub with M; auto.
  - now intros ? []%finsubsetP.
  - assert (x ∈ Q).
    { apply (Hclos Q') ; auto.
      - apply inh_sub with M; auto.
      - apply finsubset_incl.
    } 
    exists x. split.
    1: now rewrite /Q' finsubsetP //.
    move => x' /Hincl.
    apply Hmub.
Qed.

(**  Define the MUB closure operation in a preorder with normal sets.
      Some slightly funny games are played here to ensure that the MUB
      closure operation is a total function even when hf = true.  In this
      case, the MUB closure of nil is nil; this works because nil is
      (vacuously) MUB closed when h = true.
  *)

HB.builders Context hf A of HasNormals hf A.

  Definition norm_closure (X : finset A) : finset A :=
    match (inh_dec A hf X) with
    | right _ => fempty
    | left Xinh =>
      match has_normals X Xinh with
      | exist _ Q (conj HQ1 HQ2) => proj1_sig (normal_set_mub_closure Q HQ2 X Xinh HQ1)
      end
    end.

  (**  A preorder is Plotkin whenever it has normal sets.
    *)
  Fact norm_mub_complete : is_mub_complete hf A.
  Proof.
    red; intros.
    destruct (has_normals M) as [Q [? Hnorm]]; auto.
    edestruct (normal_has_mubs Q Hnorm) ; tea.
    now eexists ; eauto.
  Qed.

  Fact norm_mub_clos_incl (M : finset A) : M ⊆ norm_closure M.
  Proof.
    rewrite /norm_closure.
    destruct inh_dec as [|[-> ->]%not_inh].
    2: reflexivity.
    intros x Hx.
    destruct (has_normals M _) as [Q [??]].
    destruct (normal_set_mub_closure Q n M _ _) as (?&Hincl&?&?).
    cbn in *.
    now apply Hincl.
  Qed.
  Fact norm_mub_clos_mub (M : finset A) : mub_closed hf (norm_closure M).
  Proof.
    intros M' Hinh Hincl ??.
    unfold norm_closure in *.
    destruct inh_dec as [|[-> ->]%not_inh] ; cbn in *.
    2: now destruct Hinh as [? ?%Hincl%femptyP].
    destruct (has_normals M _) as [Q [??]].
    destruct (normal_set_mub_closure Q n M _ _) as (?&?&Hclos&?).
    cbn in *.
    now apply Hclos with M'.
  Qed.

  Fact norm_mub_clos_smallest (M X : finset A) :
    M ⊆ X ->
    mub_closed hf X -> 
    (norm_closure M) ⊆ X.
  Proof.
    intros ?? x Hx.
    unfold norm_closure in *.
    destruct inh_dec as [|[-> ->]%not_inh] ; cbn in *.
    2: now apply femptyP in Hx.
    destruct (has_normals M _) as [Q [??]].
    destruct (normal_set_mub_closure Q n M _ _) as (?&?&?&Hin).
    cbn in *.
    now apply Hin.
  Qed.
  
  HB.instance Definition norm_plt :=
    IsPlotkin.Build hf A
      norm_mub_complete
      norm_closure
      norm_mub_clos_incl
      norm_mub_clos_mub
      norm_mub_clos_smallest.

HB.end.

Lemma mub_componentwise (A B : Poset) (M : finset (A*B)) (a : A) (b : B) :
  minimal_upper_bound (a,b) M <->
    (minimal_upper_bound a (image π₁ M)) /\ (minimal_upper_bound b (image π₂ M)).
Proof.
  split.
  - intros [Hub Hlub].
    split.
    all: split ; cbn in *.
    + move => a' /imageP /= [[a'' b''] [? ->]] /=.
      now enough ((a'',b'') ≤ (a,b)) as [].
    + intros a' ??.
      enough ((a,b) ≤ (a',b)) as [] by easy.
      apply Hlub.
      2: split ; solve [easy | reflexivity].
      move => [??] /dup [] /(image_fun π₁) ? /Hub [] /= *.
      now split.
    + move => a' /imageP /= [[a'' b''] [? ->]] /=.
      now enough ((a'',b'') ≤ (a,b)) as [].
    + intros b' ??.
      enough ((a,b) ≤ (a,b')) as [] by easy.
      apply Hlub.
      2: split ; solve [easy | reflexivity].
      move => [??] /dup [] /Hub [] /= ?? /(image_fun π₂) *.
      now split.
  - intros [[HubA HlubA] [HubB HlubB]].
    split ; cbn.
    + intros [a' b'].
      split ; cbn in * ; [apply HubA|apply HubB].
      all: rewrite imageP ; now eexists.
    + move => [a' b'] Hub' [] /= ? ?.
      split => /= ; [apply HlubA|apply HlubB] => //.
      all: move => ? /imageP /= [[a'' b'']] [Hin ->] /=.
      all: by apply Hub' in Hin as [].
Qed.

(**  The product of two effective Plotkin orders has normal sets. *)
Program Definition prod_has_normals hf (A B : PlotkinOrder hf) :=
  HasNormals.Build hf (A*B) _.
Next Obligation.
  change (finset _) with (finset ((A :> EffPoset) × B)) in *.
  change {| eff_poset.sort := A * B |} with ((A :> EffPoset) × B).
  exists (finprod (mub_closure (image π₁ X))
                  (mub_closure (image π₂ X))).
  split.
  - red; intros [a b] ?.
    rewrite finprodP.
    split.
    all: apply mub_clos_incl.
    all: rewrite imageP ; cbn.
    all: now eexists.
  - apply mub_closed_normal_set ; cbn.
    + destruct hf; auto ; cbn in *.
      destruct Hinh as [x ?].
      exists x.
      destruct x as [a b].
      rewrite finprodP.
      split; apply mub_clos_incl; auto.
      all: rewrite imageP /=.
      all: now eexists.
    + change (is_mub_complete hf ((A :> Poset) × B)).
      red. intros M [a b] HMinh Hmub.
      destruct (mub_complete (image π₁ M) a) as (xA&?&?).
      1: now apply inh_image.
      1:{
        move => ? /imageP /= [y [Hin ->]].
        apply Hmub in Hin ; apply Hin.
      }
      destruct (mub_complete (image π₂ M) b) as (xB&?&?).
      1: now apply inh_image.
      1:{
        move => ? /imageP /= [y [Hin ->]].
        apply Hmub in Hin ; apply Hin.
      }
      exists (xA,xB).
      split ; [|now split].
      now rewrite mub_componentwise.
    + move => M Minh Hincl [a b] /mub_componentwise [??].
      rewrite finprodP ; split.
      * apply (mub_clos_mub (image π₁ X)) with (image π₁ M) ; try easy.
        1: now apply inh_image.
        rewrite image_incl.
        red ; cbn.
        by move => [] /= ?? /Hincl /finprodP /= [??].
      * apply (mub_clos_mub (image π₂ X)) with (image π₂ M) ; try easy.
        1: now apply inh_image.
        rewrite image_incl.
        red ; cbn.
        by move => [] /= ?? /Hincl /finprodP /= [??].
Qed.

(**  The product of two effective Plotkin orders is Plotkin. *)
HB.instance Definition _ hf A B := prod_has_normals hf A B.

Lemma finsubset_le_left {A B : DecPoset} (a : A) (X : finset A) (Y : finset B) :
  finsubset (ord^~ (inl a)) (finsum X Y) = image ι₁ (finsubset (ord^~ a) X).
Proof.
  apply set_ext.
  intros [a'|b].
  all: rewrite finsubsetP imageP ?finsum_left_elem ?finsum_right_elem.
  - split.
    + intros [].
      eexists ; split ; [|reflexivity].
      now rewrite finsubsetP.
    + now move => [? []] /finsubsetP [??] [= ?] ; subst.
  - transitivity False.
    + apply neg_false.
      intros [? []].
    + symmetry ; apply neg_false.
      intros (?&?&[=]).
Qed.

Lemma finsubset_le_right {A B : DecPoset} (b : B) (X : finset A) (Y : finset B) :
  finsubset (ord^~ (inr b)) (finsum X Y) = image ι₂ (finsubset (ord^~ b) Y).
Proof.
  apply set_ext.
  intros [a|b'].
  all: rewrite finsubsetP imageP ?finsum_left_elem ?finsum_right_elem.
  - transitivity False.
    + apply neg_false.
      intros [? []].
    + symmetry ; apply neg_false.
      intros (?&?&[=]).
  - split.
    + intros [].
      eexists ; split ; [|reflexivity].
      now rewrite finsubsetP.
    + now move => [? []] /finsubsetP [??] [= ?] ; subst.
Qed.

Lemma directed_fempty {A : Poset} : directed true (fempty :> finset A).
Proof.
  move => ? /= [? ?] /incl_fempty ?.
  subst.
  exfalso.
  now eapply femptyP.
Qed.

(** The disjoint union of two effective Plotkin orders has normal sets. *)
Program Definition sum_has_normals hf (A B : PlotkinOrder hf) :=
  HasNormals.Build hf (A+B) _.
Next Obligation.
  change (finset _) with (finset ((A :> EffPoset) + B)%cat) in *.
  change {| eff_poset.sort := A + B |} with ((A :> EffPoset) + B)%cat.
  set (L := left_finset X).
  set (R := right_finset X).
  destruct hf ; cycle -1 ; cbn in *.
  - destruct (plt_has_normals L) as [ZL [? HL]]; [ hnf; auto |].
    destruct (plt_has_normals R) as [ZR [? HR]]; [ hnf; auto |].
    exists (finsum ZL ZR).  
    split.
    1: move => [] x ; now rewrite (left_right_finset_finsum X) ?finsum_left_elem ?finsum_right_elem.
    split ; [easy|].
    intros [a|b].
    + rewrite finsubset_le_left.
      apply: directed_image.
      apply HL.
    + rewrite finsubset_le_right.
      apply: directed_image.
      apply HR.
  - elim: (decide (inh true L)) => [Hinh' |/not_inh [e _]] ; cycle -1.
    2: elim: (decide (inh true R)) => [? |/not_inh [e _]] ; cycle -1.
    + assert (inh true R) as Hinh'.
      { 
        apply (dec_stable _) => /not_inh [e' _].
        subst L R.
        elim: Hinh => [[? /left_finsetP|? /right_finsetP]].
        all: by rewrite ?e ?e' => /femptyP.
      }
      destruct (plt_has_normals R Hinh') as [Z' [Hincl Hnorm]].
      exists (finsum fempty Z').
      split ; [|split].
      * move => [|] ?.
        1: by move => /left_finsetP ; rewrite -/L e femptyP.
        move => /right_finsetP /Hincl ?.
        by rewrite finsum_right_elem.
      * destruct Hinh'.
        eexists (inr _).
        rewrite finsum_right_elem.
        now apply Hincl.
      * move => [a|b].
        1: rewrite finsubset_le_left finsubset_fempty image_fempty ; now apply directed_fempty.
        rewrite finsubset_le_right.
        apply: directed_image.
        apply Hnorm.
    + destruct (plt_has_normals L Hinh') as [Z' [Hincl Hnorm]].
      exists (finsum Z' fempty).
      split ; [|split].
      * move => [|] ?.
        2: by move => /right_finsetP ; rewrite -/R e femptyP.
        move => /left_finsetP /Hincl ?.
        by rewrite finsum_left_elem.
      * destruct Hinh'.
        eexists (inl _).
        rewrite finsum_left_elem.
        now apply Hincl.
      * move => [a|b].
        2: rewrite finsubset_le_right finsubset_fempty image_fempty ; now apply directed_fempty.
        rewrite finsubset_le_left.
        apply: directed_image.
        apply Hnorm.

    + destruct (plt_has_normals L) as [ZL [? HL]] ; tea.
      destruct (plt_has_normals R) as [ZR [? HR]] ; tea.
      exists (finsum ZL ZR).
      split ; [|split].
      * by rewrite (left_right_finset_finsum X) incl_finsum.
      * destruct Hinh'.
        eexists (inl _).
        now rewrite finsum_left_elem.
      * intros [z|z].
        -- rewrite finsubset_le_left.
           apply: directed_image.
           apply HL.
        -- rewrite finsubset_le_right.
           apply: directed_image.
           apply HR.
Qed.

(** The disjoint union of two effective Plotkin orders is Plotkin. *)
HB.instance Definition _ hf A B := sum_has_normals hf A B.

(**  Next we show that adding a new bottom element to an effective
     Plotkin order yields another Plotkin order.
  *)
Program Definition unlift {A : Poset} : finset (lift A) -> finset A :=
 finfilter_map (fun (x : lift A) => x).

Lemma unliftP {A : Poset} (X : finset (lift A)) (x : A) : x ∈ unlift X <-> (liftup x) ∈ X.
Proof.
  rewrite /unlift finfilter_mapP /=.
  intuition eauto.
  now destruct H as (?&?&->).
Qed.

Definition lift_mub_closure hf {A:PlotkinOrder hf} (M:finset (lift A)) 
  : finset (lift A) :=
  if (decide (inh hf (unlift M)))
  then (fcons lift_bot (image liftup (mub_closure (unlift M :> finset A))))
  else single lift_bot.

Lemma bot_lift_mub_closure hf {A:PlotkinOrder hf} (M:finset (lift A)) :
  lift_bot ∈ lift_mub_closure hf M.
Proof.
  rewrite /lift_mub_closure.
  destruct decide.
  2: now rewrite singleP.
  now rewrite fconsP.
Qed.

(** The lift preorder of had normal sets. *)
Program Definition lift_has_normals hf1 hf2 (A:PlotkinOrder hf1) :=
  HasNormals.Build hf2 (lift A) _.
Next Obligation.
  assert (forall (t : lift A), t ≤ lift_bot -> t = None).
  {
    intros ? H.
    cbv in H.
    destruct t ; now cbn in *.
  }

  exists (lift_mub_closure hf1 X).
  split ; [|split] ; cbn.
  - intros [x|].
    2: intros ; now apply bot_lift_mub_closure.
    intros ?.
    rewrite /lift_mub_closure.
    rewrite decide_True.
    1: now apply elem_inh with x, unliftP.
    rewrite fconsP.
    right.
    apply: (image_fun liftup).
    now apply mub_clos_incl, unliftP.
  - unfold lift_mub_closure.
    destruct hf2; simpl; auto.
    exists lift_bot.
    now apply bot_lift_mub_closure.

  - move => z.
    move => M ?.
    destruct (decide ((unlift M) = fempty)) as [e|[m Hm]%finset_not_empty].
    + move => _.
      exists lift_bot ; split.
      * rewrite finsubsetP ; split ; [|now cbv].
        now apply bot_lift_mub_closure.
      * intros [|] ?.
        2: reflexivity.
        exfalso.
        eapply femptyP.
        rewrite <- e.
        now rewrite unliftP.
    + move => /incl_finsubset [] Hincl Hle.
      destruct z ; cycle -1.
      {
        replace (finsubset _ _) with (single (set := finset) (lift_bot (A := A))).
        1: now exists lift_bot ; split ; [rewrite singleP|].
        ext.
        rewrite finsubsetP !singleP.
        intuition (subst ; eauto using bot_lift_mub_closure).
        reflexivity.
      }
      edestruct (mub_complete (unlift M)) as [ub [[Hub]?]] ; tea.
      1: now eapply elem_inh.
      1: move => ? /unliftP /Hle Hle' ; exact Hle'.
      exists (Some ub) ; split ; cycle -1.
      1: move => [a|] ; [move => /unliftP /Hub|] ; now cbv.
      rewrite finsubsetP ; split ; [|assumption].
      assert (inh hf1 (unlift X)).
      {
        apply (dec_stable _) => ?.
        rewrite /lift_mub_closure decide_False in Hincl ; tea.
        apply unliftP, Hincl in Hm.
        rewrite singleP in Hm.
        now inversion Hm.
      }
      rewrite /lift_mub_closure decide_True // fconsP.
      right.
      apply: (image_fun liftup).
      eapply mub_clos_mub.
      3: now split.
      1: eauto.
      move => m' /unliftP Hm'.
      apply Hincl in Hm'.
      rewrite /lift_mub_closure decide_True // fconsP in Hm'.
      destruct Hm' as [Hm'|Hm'] ; [now inversion Hm'|].
      rewrite imageP in Hm'.
      destruct Hm' as (?&?&[= ->]).
      assumption.
Qed.

(** The lift preorder of an effective Plotkin order is Plotkin. *)
HB.instance Definition _ hf1 hf2 A := lift_has_normals hf1 hf2 A.
