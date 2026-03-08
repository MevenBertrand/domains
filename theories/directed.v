(** * domains.directed: Conditionally-inhabited sets and h-directed sets *)

From Stdlib Require Import ssreflect ssrfun Arith Lia.
From HB Require Import structures.
Require Import utils.all categories.all preord sets finsets colsets effective.


(**  A finite set is conditionally-inhabited for hf
     whenever hf is false; or when hf is true, the set
     is inhabited.

     This very odd little definition is the key to
     providing a uniform presentation of pointed and
     unpointed domains.
  *)

Definition inh {A:Poset} (hf:bool) (X:finset A) := 
  if hf then exists x, x ∈ X else True.

Instance inh_dec A hf (X:finset A) : Decision (inh hf X).
Proof.
  destruct hf; simpl; auto.
  2: now left.
  pattern X ; apply quot_rect_irr.
  2: typeclasses eauto.
  clear X.
  intros [|a].
  - right. intros [? H]. by rewrite finsetP /= in H.
  - left. exists a. now rewrite finsetP /=.
Qed.

Lemma inh_image {A B : Poset} hf (X:finset A) (f:A → B) :
  inh hf X <-> inh hf (image f X).
Proof.
  destruct hf; simpl.
  2: easy.
  setoid_rewrite imageP.
  split.
  - intros [] ; now repeat eexists.
  - intros (?&?&?) ; now eexists.
Qed.

Lemma inh_sub A hf (X Y:finset A) :
  X ⊆ Y -> inh hf X -> inh hf Y.
Proof.
  destruct hf; simpl; auto.
  intros ? [x ?].
  now exists x.
Qed.

Lemma elem_inh A hf (X:finset A) x : x ∈ X -> inh hf X.
Proof.
  intros. now destruct hf ; cbn.
Qed.

Lemma inh_emp A hf : inh (A := A) hf fempty -> hf = false.
Proof.
  destruct hf ; cbn.
  2: easy.
  move => [?].
  now rewrite femptyP.
Qed.

#[global] Hint Resolve inh_sub elem_inh : core.

(**  A subset of the image of a function is equal to the image
     of some subset of the set X.
  *)
Lemma finset_sub_image {A B : Poset} {set : SetTheory} 
  (f:A → B) (X: set A) (M : finset B) :
  M ⊆ image f X ->
  exists (M' : finset A), M = image f M' /\ M' ⊆ X.
Proof.
  induction M as [|b ? IHM] using finset_ind.
  - exists fempty ; split.
    2: apply fempty_incl.
    ext.
    rewrite imageP femptyP. setoid_rewrite femptyP.
    intuition.
  - intros Hincl.
    destruct IHM as [M' [??]].
    + intros x Hx.
      apply Hincl.
      now rewrite funion2P.
    + subst.
      assert (b ∈ image f X) as Hb.
      { apply Hincl.
        now rewrite funion2P fsingleP.
      }
      rewrite imageP in Hb.
      destruct Hb as [a [??]] ; subst.
      exists (funion2 (fsingle a) M').
      split.
      2: intros x ; rewrite funion2P fsingleP ; intuition (subst ; auto).
      ext.
      rewrite funion2P fsingleP !imageP.
      setoid_rewrite funion2P.
      setoid_rewrite fsingleP.
      split.
      * intros [->|(?&?&->)].
        all: now eexists.
      * intros (?&[->|]&->).
        1: now left.
        right.
        now eexists.
Qed.

(**  A directed preorder is an effective preorder where every finite set
     has an upper bound (that may be found constructively).
  *)

#[primitive] HB.mixin Record IsDirected (T : Type) of poset T := {
  choose_ub_set : forall M : finset T, { k | upper_bound k M }
  }.

#[short(type="Directed"),primitive]
HB.structure Definition directed_poset :=
  { T of eff_poset T & IsDirected T}.

Lemma choose_ub (I:Directed) (i j:I) :
  { k | i ≤ k /\ j ≤ k }.
Proof.
  destruct (choose_ub_set (funion2 (fsingle i) (fsingle j))) as [x hx] ; cbn in *.
  rewrite /upper_bound /= in hx.
  setoid_rewrite funion2P in hx.
  setoid_rewrite fsingleP in hx.
  exists x.
  intuition.
Qed.

(** A set X is h-directed when every h-inhabited finite
    subset has an upper bound in X.
  *)
Definition directed {set : SetTheory} {A:Poset} (hf:bool) (X:set A) :=
  forall (M:finset A) (Hinh:inh hf M),
    M ⊆ X -> ∃ x ∈ X, upper_bound x M.

(**  To prove a set X is directed, it suffices (and is necessary)
     that every pair of elements in X has an upper bound in X; and that
     X is inhabited when b = false.
  *)
Lemma prove_directed {set : SetTheory} {A:Poset} (hf:bool) (X:set A) :
  (if hf then True else exists x, x ∈ X) ->
  (∀ x ∈ X, ∀ y ∈ X, exists z, x ≤ z /\ y ≤ z /\ z ∈ X) ->
  directed hf X.
Proof.
  intros Hinh Hsup M.
  induction M as [|a M IHM] using finset_ind.
  - cbn; intros Hemp _.
    apply inh_emp in Hemp as ->.
    destruct Hinh as [].
    eexists ; split ; tea.
    now apply ub_emp.
  - intros _.
    destruct hf.
    1: destruct (decide (inh true M)).
    2:{
      assert (M = fempty) as ->.
      {
        ext.
        rewrite femptyP -neg_false.
        intros ?.
        apply n.
        now eexists.
      }
      rewrite funion2_incl single_incl.
      exists a.
      rewrite /upper_bound.
      split ; eauto.
      intros x.
      rewrite funion2P singleP femptyP.
      now intros [->|].
    }
    2: specialize (IHM I).
    all: intros h.
    all: rewrite funion2_incl single_incl in h.
    all: destruct IHM as (x&?&?) ; eauto.
    all: unfold set_ex.
    all: destruct (Hsup a ltac:(eauto) x) as (x'&?&?) ; eauto.
    all: exists x'.
    all: split ; eauto.
    all: rewrite /upper_bound.
    all: intros ?.
    all: rewrite funion2P singleP.
    all: intros [->|] ; [easy|].
    all: now transitivity x.
Qed.

(**  Directeness forms a set color. *)

Program Definition directed_hf_cl {set : SetTheory} (hf:bool) : color set :=
  {| color_prop := fun A X => directed hf X |}.
Next Obligation.
  intros ? ? Hincl.
  exists a.
  rewrite incl_single in Hincl.
  rewrite /upper_bound singleP.
  split ; [easy|].
  intros ; now apply rrefl.
Qed.
Next Obligation.
  intros ? ? Hincl.
  destruct (finset_sub_image _ _ _ Hincl) as [M' [??]] ; subst.
  destruct (H M') as [x [? Hub]]; auto.
  1: now rewrite inh_image.
  exists (f x); split; auto.
  1: now apply imageP.
  intros ?.
  rewrite imageP.
  intros (x'&?&->).
  now apply mon_mon, Hub.
Qed.
Next Obligation.
  apply prove_directed.
  - destruct hf ; auto ; cbn in *.
    destruct (H fempty) as (X&Hin&?); cbn.
    1-2: eauto using fempty_incl.
    specialize (H0 _ Hin).
    destruct (H0 fempty) as (x&?&?) ; cbn.
    1-2: eauto using fempty_incl.
    exists x.
    now rewrite unionP.
  - intros x [X1 [??]]%unionP y [X2 [??]]%unionP.
    destruct (H (fcons X1 (fcons X2 fempty))) as [X [HXin HXub]]; auto.
    + apply elem_inh with X1; auto.
      now rewrite !fconsP.
    + rewrite !fcons_incl.
      auto using fempty_incl.
    + destruct (H0 X HXin (fcons x (fcons y fempty))) as [z [? Hzub]]; auto.
      * eapply elem_inh; auto.
        now rewrite fconsP.
      * intros z.
        rewrite !fconsP femptyP.
        red in HXub.
        unshelve epose proof (HXub X1 _) as HX1.
        2: unshelve epose proof (HXub X2 _) as HX2.
        1-2: now rewrite !fconsP.
        rewrite !set_leP in HX1, HX2.
        now intros [->|[->|]] ; [..|easy].
      * exists z. split ; [|split].
        3: now rewrite unionP.
        all: apply Hzub.
        all: now rewrite !fconsP.
Qed.

Definition semidirected_cl {set : SetTheory} := directed_hf_cl (set := set) true.
Definition directed_cl {set : SetTheory} := directed_hf_cl (set := set) false.


(**  The preorder of natural numbers with their arithmetic ordering
     is an effective, directed preorder.
  *)

Program Definition _NatDirected := IsDirected.Build nat _.
Next Obligation.
  eexists (finset_lub 0 Nat.max _ _ _ _ M).
  apply finset_lub_lub.
  Unshelve.
  all: rewrite /= /ord /=.
  all: lia.
Qed.

HB.instance Definition _ := _NatDirected.