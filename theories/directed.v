(** * domains.directed: Conditionally-inhabited sets and h-directed sets *)

From Stdlib Require Import ssreflect.
From HB Require Import structures.
Require Import utils.all categories.all preord sets finsets effective.


(**  A finite set is conditionally-inhabited for hf
     whenever hf is false; or when hf is true, the set
     is inhabited.

     This very odd little definition is the key to
     providing a uniform presentation of pointed and
     unpointed domains.
  *)

Definition inh {A:Type} (hf:bool) (X:finset A) := 
  if hf then exists x, x ∈ X else True.

Instance inh_dec A hf (X:finset A) : Decision (inh hf X).
Proof.
  destruct hf; simpl; auto.
  2: now left.
  apply (quot_rect_dec (P := fun (X : finset A) => exists x : A, x ∈ X)).
  clear X.
  intros [|a].
  - right. intros [? H]. by rewrite finsetP /= in H.
  - left. exists a. now rewrite finsetP /=.
Qed.

Lemma inh_image A B hf (X:finset A) (f:A → B) :
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
Lemma finset_sub_image (A B : Poset) (set : SetTheory) 
  (f:A → B) (X: set A) (M : finset B) :
  M ⊆ image f X ->
  exists (M' : finset A), M = image f M' /\ M' ⊆ X.
Proof.
  induction M as [|b] using finset_ind.
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
    M ⊆ X -> exists x, upper_bound x M /\ x ∈ X.

(**  To prove a set X is directed, it suffices (and is necessary)
     that every pair of elements in X has an upper bound in X; and that
     X is inhabited when b = false.
  *)
Lemma prove_directed {set : SetTheory} {A:Poset} (hf:bool) (X:set A) :
  (if hf then True else exists x, x ∈ X) ->
  (forall x y, x ∈ X -> y ∈ X -> exists z, x ≤ z /\ y ≤ z /\ z ∈ X) ->
  directed hf X.
Proof.
  intros Hinh Hsup M.
  induction M using finset_ind.
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
    all: destruct (Hsup a x) as (x'&?&?) ; eauto.
    all: exists x'.
    all: split ; eauto.
    all: rewrite /upper_bound.
    all: intros ?.
    all: rewrite funion2P singleP.
    all: intros [->|] ; [easy|].
    all: now transitivity x.
Qed.

(**  Directeness forms a set color.
  *)
Program Definition directed_hf_cl (hf:bool) : color :=
  Color (fun SL A X => @directed SL A hf X) _ _ _ _.
Next Obligation.    
  repeat intro.
  destruct (H0 M) as [x [??]]; auto.
  - rewrite H; auto.
  - exists x. split.
    + hnf; intros.
      apply H2; auto.
    + rewrite <- H; auto.
Qed.
Next Obligation.
  repeat intro.
  exists a. split; auto.
  - hnf; intros. apply H in H0.
    apply single_axiom in H0. auto.
  - apply single_axiom; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct (finset_sub_image A B T f X M H0) as [M' [??]].
  destruct (H M') as [x [??]]; auto.
  - rewrite (inh_image A B hf M' f).
    apply inh_eq with M; auto.
  - exists (f#x); split; auto.
    + hnf; intros.
      rewrite H1 in H5.
      apply image_axiom2 in H5.
      destruct H5 as [y [??]].
      rewrite H6.
      apply Preord.axiom.
      apply H3. auto.
    + apply image_axiom1. auto.
Qed.
Next Obligation.
  intros.
  apply prove_directed.
  - case_eq hf; auto. intros.
    destruct (H nil) as [X [??]].
    + rewrite H1; hnf; auto.
    + hnf; intros. apply nil_elem in H2. elim H2.
    + destruct (H0 X H3 nil) as [x [??]].
      * rewrite H1; hnf; auto.
      * hnf; intros. apply nil_elem in H4. elim H4.
      * exists x. apply union_axiom; eauto.
  - intros.
    apply union_axiom in H1.
    apply union_axiom in H2.
    destruct H1 as [X1 [??]].
    destruct H2 as [X2 [??]].
    destruct (H (X1::X2::nil)%list) as [X [??]]; auto.
    + apply elem_inh with X1; auto.
      apply cons_elem; auto.
    + hnf; intros.
      apply cons_elem in H5. destruct H5; [ rewrite H5; auto |].
      apply cons_elem in H5. destruct H5; [ rewrite H5; auto |].
      apply nil_elem in H5; elim H5.
    + destruct (H0 X H6 (x::y::nil)%list) as [z [??]]; auto.
      * apply elem_inh with x; auto.
        apply cons_elem; auto.
      * hnf; intros.
        apply cons_elem in H7. destruct H7.
        ** rewrite H7; auto.
           assert (X1 ≤ X).
           { apply H5. apply cons_elem; auto. }
           apply H8. auto.
        ** apply cons_elem in H7. destruct H7.
           *** rewrite H7; auto.
               assert (X2 ≤ X).
               { apply H5.
                 apply cons_elem; right.
                 apply cons_elem; auto.
               }
               apply H8. auto.
           *** apply nil_elem in H7. elim H7.
      * exists z. split.
        ** apply H7. apply cons_elem; auto.
        ** split.
           *** apply H7.
               apply cons_elem; right.
               apply cons_elem; auto.
           *** apply union_axiom.
               exists X; split; auto.
Qed.

Definition semidirected_cl := directed_hf_cl true.
Definition directed_cl := directed_hf_cl false.


(**  The preorder of natural numbers with their arithmetic ordering
     is an effective, directed preorder.
  *)
From Stdlib Require Import Arith.
From Stdlib Require Import NArith.

Program Definition nat_ord := Preord.Pack nat (Preord.Mixin nat le _ _).
Solve Obligations with eauto with arith.
  
Program Definition nat_eff : effective_order nat_ord :=
  EffectiveOrder nat_ord le_dec (fun x => Some (N.to_nat x)) _.
Next Obligation.
  intros. exists (N.of_nat x).
  rewrite Nat2N.id. auto.
Qed.

Program Definition nat_dirord : directed_preord :=
  DirPreord nat_ord nat_eff _.
Next Obligation.  
  induction M.
  - exists 0. hnf; intros. apply nil_elem in H. elim H.
  - destruct IHM as [k ?].
    exists (max a k).
    hnf; intros.
    apply cons_elem in H. destruct H.
    + rewrite H.
      apply Nat.le_max_l.
    + transitivity k; [ apply u; auto |].
      apply Nat.le_max_r.
Qed.
