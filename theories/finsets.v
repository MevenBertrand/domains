(** * domains.finsets: the set theory of finite sets *)
From Stdlib Require Import List ssreflect ssrfun
  Relations Classes.RelationClasses Classes.Morphisms Lia.
From HB Require Import structures.

Require Import utils.all categories.all preord sets.

Open Scope general_if_scope.

(** Here we define the theory of finite sets.  Concretely,
    finite sets are represented by the extensional
    quotient of the list type. Singleton sets are given
    by one-element lists, union is defined by list
    concatenation and image is the stadard list map function.
  *)

(** ** Finite sets as a set theory *)

Definition list_ext A : relation (list A) := fun l l' => forall x, In x l <-> In x l'.

Instance list_ext_equiv {A} : Equivalence (list_ext A).
Proof.
  split.
  all: red ; unfold list_ext.
  1: easy.
  - intros * H **.
    split ; now apply H.
  - intros * H H' **.
    split ; intros ; first [apply H | apply H'].
    all: first [now apply H | now apply H'].
Qed.

Definition ffinset (A : Poset) : Type := quot (list_ext A).

Definition ffinlist {A : Poset} (l : list A) : ffinset A := to_quot l.

Instance Proper_In {A : Poset} (a : A) : Proper (list_ext A ==> eq) (In a).
Proof.
  cbv -[In iff].
  intros ; now ext.
Qed.

Definition fmember {A : Poset} (a : A) : (ffinset A) -> Prop := quot_rec (In a).

Lemma ffinsetP {A : Poset} (a : A) (l : list A) :
  fmember a (ffinlist l) <-> In a l.
Proof.
  by rewrite /fmember quot_rec_eq.
Qed.

Lemma finset_ext : IsExtMem ffinset (@fmember).
Proof.
  intros A f f'.
  induction f as [l] using quot_ind.
  induction f' as [l'] using quot_ind.
  intros H.
  apply quot_ext.
  intros x.
  by rewrite <- !ffinsetP.
Qed.

Definition finset : Poset -> Poset :=
  promote_set ffinset (@fmember) finset_ext.

HB.instance Definition _ : IsBaseSetTheory.axioms_ finset :=
  SetIncl ffinset (@fmember) finset_ext.

Definition finlist {A : Poset} (l : list A) : finset A := ffinlist l.

Lemma finsetP {A : Poset} (X : list A) (x : A) : x ∈ (finlist X) <-> In x X.
Proof.
  apply ffinsetP.
Qed.

#[global]Opaque finset.

(** ** Finite sets form a set theory *)

Instance Proper_map {A B : Type} (f : A -> B) :
  Proper (list_ext A ==> list_ext B) (map f).
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros l l' H b.
  rewrite !in_map_iff.
  now setoid_rewrite H.
Qed.

Definition fimage {A B : Poset} (f : A -> B) (X : finset A) : finset B :=
  quot_map (map f) X.

Lemma fimageP {A B : Poset} (f : A -> B) (X : finset A) (y : B) :
  fmember y (fimage f X) <-> exists x, fmember x X /\ y = f x.
Proof.
  induction X as [l] using quot_ind.
  rewrite /fmember /fimage quot_map_eq quot_rec_eq in_map_iff.
  setoid_rewrite quot_rec_eq.
  split.
  all: intros [] ; now eexists.
Qed.

(** *** Empty finset *)

Definition fempty {A : Poset} : finset A := finlist nil.

Lemma femptyP {A : Poset} {x : A} : x ∈ fempty <-> False.
Proof.
  split ; [..|easy].
  rewrite /fempty finsetP.
  apply in_nil.
Qed.

Lemma fempty_incl {set : SetTheory} X (Q:set X) :
  fempty ⊆ Q.
Proof.
  now intros ? ?%femptyP.
Qed.

Lemma incl_fempty {A : Poset} (X : finset A) : X ⊆ fempty -> X = fempty.
Proof.
  intros hincl.
  ext.
  split ; try apply hincl.
  now rewrite femptyP.
Qed.

Lemma ub_emp (X : Poset) (a:X) : upper_bound a fempty.
Proof.
  now intros ? ?%femptyP.
Qed.

(** *** Singleton finset *)

Definition fsingle {A : Poset} (a : A) : finset A := finlist (a :: nil).

Lemma fsingleP {A : Poset} (a a' : A) :
  a ∈ (fsingle a') <-> a = a'.
Proof.
  rewrite /fsingle finsetP /=.
  intuition.
Qed.

(** *** Binary union of finsets *)

Instance Proper_app {A} :
  Proper (list_ext A ==> list_ext A ==> list_ext A) (app (A:=A)).
Proof.
  intros.
  rewrite /Proper /respectful /list_ext /=.
  intros l1 l1' H1 l2 l2' H2 a.
  rewrite !in_app_iff !H1 !H2.
  reflexivity.
Qed.

Definition funion2 {A : Poset} (X Y : finset A) : finset A := quot_map2 (@app A) X Y.

Lemma funion2P {A} (f f' : finset A) (x : A) :
  x ∈ (funion2 f f') <-> x ∈ f \/ x ∈ f'.
Proof.
  induction f as [l] using quot_ind.
  induction f' as [l'] using quot_ind.
  now rewrite /funion2 quot_map2_eq !finsetP in_app_iff.
Qed.

Lemma funion2_incl {A} {set : SetTheory} (X X' : finset A) (Y : set A) :
  funion2 X X' ⊆ Y <-> X ⊆ Y /\ X' ⊆ Y.
Proof.
  rewrite /incl.
  setoid_rewrite funion2P.
  intuition.
Qed.

Fixpoint fconcat {A : Poset} (XS : list (finset A)) : finset A :=
  match XS with
  | nil => fempty
  | x :: XS => funion2 (fconcat XS) x
  end.

Lemma fconcatP {A} (XS : list (finset A)) (a : A) :
  a ∈ (fconcat XS) <-> (exists X, In X XS /\ a ∈ X).
Proof.
  induction XS ; cbn.
  - rewrite femptyP.
    split ; [done|..].
    now intros [].
  - rewrite funion2P IHXS.
    split.
    + intros [[X []]|].
      all: now eexists.
    + intros [X [[|] ?]] ; subst.
      1: easy.
      left ; now eexists.
Qed.

Instance Proper_fconcat {A} : Proper (list_ext (finset A) ==> eq) fconcat.
Proof.
  rewrite /Proper /respectful.
  intros l l' H.
  ext.
  rewrite !fconcatP.
  unfold list_ext in H.
  now setoid_rewrite H.
Qed.

Definition funion {A : Poset} (XS : finset (finset A)) : finset A :=
  quot_rec fconcat XS.

Lemma funionP {A : Poset} XS (a : A) :
  a ∈ (funion XS) <-> (exists X, X ∈ XS /\ a ∈ X).
Proof.
  induction XS as [l] using quot_ind.
  rewrite /funion quot_rec_eq fconcatP.
  setoid_rewrite finsetP.
  reflexivity.
Qed.

HB.instance Definition _ :=
  IsPreSetTheory.Build finset (@fsingle) (@fimage) (@funion).

HB.instance Definition _ :=
  IsSetTheory.Build finset (@fsingleP) (@fimageP) (@funionP).

(** ** Properties of finite sets *)

(** *** Decidability *)

Program Definition finset_dec (A:Poset) (e : (forall x y : A, {x = y} + {x <> y})) :
  set_dec finset A.
Proof.
  constructor.
  intros x X.
  pattern X.
  unshelve eapply quot_rect.
  - intros l.
    rewrite /member /= /fmember quot_rec_eq.
    now apply In_dec.
  - cbn.
    intros l l' ext.
    destruct (in_dec e x l') ; cbn in *.
    all: destruct (in_dec e x l) ; cbn in *.
    all: try solve [exfalso ; now edestruct ext].
    all: repeat match goal with | |- context[(eq_rec_r _ _ ?e)] => destruct e end ; cbn.
    all: destruct (quot_ext _ _ _) ; cbn.
    all: f_equal ; ext.
Qed.

(** ** More interesting finite sets *)

(** *** Adding an element to a finset *)

Definition fcons {A : Poset} (a : A) (X : finset A) : finset A :=
  funion2 (fsingle a) X.

Lemma fconsP {A:Poset} (a:A) (X:finset A) (x:A) :
  x ∈ fcons a X <-> a = x \/ x ∈ X.
Proof.
  rewrite /fcons funion2P fsingleP.
  intuition.
Qed.

Lemma fcons_subset (X:Poset) (x:X) (xs ys:finset X) :
  x ∈ ys -> xs ⊆ ys -> fcons x xs ⊆ ys.
Proof.
  now intros ? ? ? [->|]%fconsP.
Qed.

Lemma ub_fcons (X:Poset) (x:X) (xs:finset X) (a:X) :
  x ≤ a ->
  upper_bound a xs ->
  upper_bound a (fcons x xs).
Proof.
  rewrite /upper_bound.
  now intros ? ? ? [->|]%fconsP **.
Qed.

Lemma fcons_cons {A : Poset} (a : A) l : finlist (a :: l) = fcons a (finlist l).
Proof.
  ext.
  now rewrite finsetP /= -finsetP fconsP.
Qed.

Lemma fcons_incl {A : Poset} {set : SetTheory} (X : finset A) (a : A) (Y : set A) :
  fcons a X ⊆ Y <-> a ∈ Y /\ X ⊆ Y.
Proof.
  rewrite /incl.
  setoid_rewrite fconsP.
  intuition (subst ; auto).
Qed.
 
Program Definition fcons_mon {A : Poset} (x : A) : (finset A) → (finset A) :=
  {| mon_map := fcons x |}.
Next Obligation.
  intros Y Z Hincl.
  rewrite !set_leP in Hincl |- *.
  intros ?.
  rewrite !fconsP.
  intuition eauto.
Qed.

(** *** Induction *)

(** Remains of an attempt at an induction principle for finite sets, but
  the relevant version is too hard. The irrelevant version about, though,
  works fine. *)
Class Commutative {A : Type} {B : Type} (op : A -> A -> B) :=
  comm : forall x y, op x y = op y x.

Global Hint Mode Commutative ! ! ! : typeclass_instances.

Class Idempotent {A : Type} (op : A -> A -> A) :=
  idem : forall x, op x x = x.

Lemma finset_rec {A : Poset} (P : Type)
  (base : P)
  (into : A -> P)
  (rec : P -> P -> P)
  `{! Commutative rec} 
  `{! Idempotent rec} :
  finset A -> P.
Proof.
  unshelve eapply quot_rec.
  1: exact (fold_right (fun a => (rec (into a))) base).
Admitted.

Instance funion2_comm {A} : Commutative (@funion2 A).
Proof.
  intros ? ?.
  ext.
  rewrite !funion2P.
  intuition.
Qed.

Definition finset_ind {A} (P : finset A -> Prop) :
  P fempty ->
  (forall a X, P X -> P (fcons a X)) ->
  forall X, P X.
Proof.
  intros IH IH'.
  apply quot_ind.
  intros X.
  induction X.
  1: now apply IH.
  enough ((fcons a (to_quot X)) = to_quot (a :: X)) as <-
    by easy.
  ext.
  now rewrite fconsP !finsetP /=.
Qed.

(** *** Filter + map *)

Section FilterMap.
  Context {A B:Type} (f : A -> option B).

  Fixpoint filter_map (l:list A) : list B :=
    match l with
    | nil => nil
    | x::xs => let l := filter_map xs in match (f x) with | None => l | Some b => b :: l end
    end.

  Lemma filter_mapP (l : list A) b : In b (filter_map l) <-> exists a, In a l /\ f a = Some b.
  Proof.
    induction l ; cbn.
    1: intuition ; match goal with H : exists _, _ |- _ => now destruct H end.
    destruct (f a) eqn:e ; cbn in *.
    - rewrite IHl ; clear IHl.
      intuition (subst ; eauto) ;
        repeat (match goal with H : exists _, _ |- _ => destruct H end) ;
      intuition (subst ; eauto).
      left ; congruence.
    - rewrite IHl ; clear IHl.
      intuition (subst ; eauto) ;
          repeat (match goal with H : exists _, _ |- _ => destruct H end) ;
      intuition (subst ; eauto).
      congruence.
  Qed.

  Lemma filter_map_length l : length (filter_map l) <= length l.
  Proof.
    induction l as [|a]; cbn.
    1: reflexivity.
    destruct ((f a)) ; cbn ; lia.
  Qed.

  Lemma filter_map_length_lt l :
    (exists x, In x l /\ f x = None) ->
    length (filter_map l) < length l.
  Proof.
    intros [x [Hin HP]].
    induction l ; cbn in *.
    1: intuition.
    destruct Hin as [<-|Hin].
    all: destruct (f a) eqn:? ; cbn ; try solve [intuition | congruence].
    - pose proof (filter_map_length l) ; lia.
    - specialize (IHl Hin).
      lia.
  Qed.

  Instance filter_Proper : Proper (list_ext A ==> list_ext B) filter_map.
  Proof.
    intros ?? e ?.
    rewrite !filter_mapP.
    red in e.
    now setoid_rewrite e.
  Qed.

End FilterMap.

Existing Instance filter_Proper.

Definition finfilter_map {A B : Poset} (f : A -> option B) : finset A -> finset B :=
  quot_map (filter_map f).

Lemma finfilter_mapP {A B : Poset} (f : A -> option B) (X : finset A) (x : B) :
  x ∈ (finfilter_map f X) <->
  exists a, a ∈ X /\ (f a = Some x).
Proof.
  induction X as [X] using quot_ind.
  rewrite -/(finlist X) /finfilter_map quot_map_eq !finsetP filter_mapP.
  now setoid_rewrite finsetP.
Qed.

(** *** Subset **)

(** We can take the subset of a finite set if the
    predicate we wish to use to take the subset is decidable.
  *)

Section FinSubset.
  Context {A:Poset} (P : A -> Prop) {Hdec : forall x, Decision (P x)}.

  Definition finsubset : finset A -> finset A :=
    finfilter_map (fun x => if (Hdec x) then (Some x) else None).

  Lemma finsubsetP (X : finset A) x : x ∈ (finsubset X) <-> x ∈ X /\ P x.
  Proof.
    rewrite /finsubset finfilter_mapP.
    setoid_rewrite dec_Some.
    split.
    - intros (?&?&?&?) ; subst ; eauto.
    - intros ; eexists ; intuition eauto.
  Qed.

End FinSubset.

(** *** Cartesian product of finite sets *)

Instance Proper_prod {A B} :
  Proper (list_ext A ==> list_ext B ==> list_ext (A*B)) (@list_prod _ _).
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros * H * H' [].
  now rewrite !in_prod_iff H H'.
Qed.

Definition finprod {A B:Poset} (P:finset A) (Q:finset B) : finset (A*B) :=
  quot_map2 (@list_prod _ _) P Q.

Lemma finprodP A B (P:finset A) (Q:finset B) a b :
  (a,b) ∈ finprod P Q <-> (a ∈ P /\ b ∈ Q).
Proof.
  induction P using quot_ind.
  induction Q using quot_ind.
  now rewrite /finprod quot_map2_eq !finsetP in_prod_iff.
Qed.

(** *** Disjoint union of finite sets *)

Definition left_finset {A B : Poset} (X : finset (A + B)) : finset A :=
  finfilter_map (fun x => match x with | inl a => Some a | inr _ => None end) X.

Lemma left_finsetP {A B : Poset} (X : finset (A + B)) (a : A) :
  a ∈ left_finset X <-> (inl a) ∈ X.
Proof.
  rewrite /left_finset finfilter_mapP.
  split.
  - intros ([]&[]) ; solve [easy|congruence].
  - intros.
    now eexists (inl _).
Qed.

Definition right_finset {A B : Poset} (X : finset (A + B)) : finset B :=
  finfilter_map (fun x => match x with | inl _ => None | inr b => Some b end) X.

Lemma right_finsetP {A B : Poset} (X : finset (A + B)) (b : B) :
  b ∈ right_finset X <-> (inr b) ∈ X.
Proof.
  rewrite /right_finset finfilter_mapP.
  split.
  - intros ([]&[]) ; solve [easy|congruence].
  - intros.
    now eexists (inr _).
Qed.

Definition finsum {A B:Poset} (P:finset A) (Q:finset B) : finset (A + B) :=
  funion2 (image ι₁ P) (image ι₂ Q).

Lemma finsum_left_elem A B (P:finset A) (Q:finset B) a : 
  inl a ∈ finsum P Q <-> a ∈ P.
Proof.
  rewrite /finsum funion2P !imageP /=.
  split.
  - intros [[? [? [= ->]]]|[? []]] ; intuition congruence.
  - intros.
    left ; now eexists.
Qed.

Lemma finsum_right_elem A B (P:finset A) (Q:finset B) b :
  inr b ∈ finsum P Q <-> b ∈ Q.
Proof.
  rewrite /finsum funion2P !imageP /=.
  split.
  - intros [[? []]|[? [? [= ->]]]] ; intuition congruence.
  - intros.
    right ; now eexists.
Qed.

Lemma left_right_finset_finsum {A B : Poset} (X : finset (A + B)):
  X = finsum (left_finset X) (right_finset X).
Proof.
  apply set_ext.
  intros [|].
  all: by rewrite ?finsum_right_elem ?finsum_left_elem ?left_finsetP ?right_finsetP.
Qed.

(** ** Finsets of sets with decidable equality have decidable membership *)

Instance list_in_dec (A:EqTy) (X : list A) (x : A) : Decision (In x X).
Proof.
  induction X in x |- *  ; cbn.
  - now right.
  - destruct (IHX x).
    1: now left.
    destruct (eqdec a x).
    1: now left.
    right.
    intuition.
Qed.

Instance finset_in_dec (A:DecPoset) (X : finset A) (x : A) : Decision (x ∈ X).
Proof.
  apply quot_rect_dec ; clear.
  intros X.
  rewrite /Decision /member /=.
  destruct (decide (In x X)) ; [left|right].
  all: now rewrite ffinsetP.
Qed.

Section FinEqDec.
  Context {A : DecPoset}.

  (**  We can take the intersection of finite sets if the elements
      have decidable equality.
    *)

  Definition finter2 (X Y : finset A) : finset A := finsubset (fun x => x ∈ X) Y.

  Lemma finter2P X Y x :
    x ∈ finter2 X Y <-> (x ∈ X /\ x ∈ Y).
  Proof.
    rewrite /finter2 finsubsetP.
    intuition.
  Qed.

(**  We can remove an element from a finite set if the elements have
     decidable equality.
  *)

Definition fremove (x : A) : finset A -> finset A :=
  finsubset (fun y => y <> x) (Hdec := fun y => @Decision_neg _ (eqdec y x)).

  Lemma fremoveP (X : finset A) x y : y ∈ (fremove x X) <-> y ∈ X /\ (y <> x).
  Proof.
    by rewrite /fremove finsubsetP.
  Qed.

End FinEqDec.

(**  We can take the powerset of a finite set; that is, all finite
     subsets of a finite set.
  *)

Fixpoint fpow_list {A:Poset} (l:list A) : finset (finset A) :=
  match l with
  | nil => single (A := finset A) fempty
  | x :: xs =>
       let pow := fpow_list xs in
          funion2 pow (image (fcons_mon x) pow)
  end.

Lemma member_fcons {A : Poset} (a : A) M x :
  x ∈ (finlist (a :: M)) <-> a = x \/ x ∈ finlist M.
Proof.
  rewrite !finsetP /=.
  intuition.
Qed.

Lemma fpow_list_sound {A : Poset} (M : list A) (X: finset A) :
  X ∈ fpow_list M -> X ⊆ (finlist M).
Proof.
  induction M in X |- * ; cbn.
  - rewrite fsingleP => -> ? /femptyP //.
  - move => /funion2P [|] /=.
    + move => /IHM hincl ? /hincl.
      now rewrite member_fcons.
    + move => /imageP [? []] /IHM hincl -> ? /funion2P [/fsingleP ->|/hincl].
      all: now rewrite member_fcons.
Qed.

Lemma fpow_list_complete (A : DecPoset) (M : list A) (X: finset A) :
  X ⊆ finlist M -> X ∈ fpow_list M.
Proof.
  induction M in X |- * ; cbn.
  - move => /incl_fempty ->.
    now rewrite fsingleP.
  - intros hX.
    rewrite -/(member X _) funion2P.
    destruct (decide (a ∈ X)) as [hin|hin].
    + assert (X = fcons a (fremove a X)) as ->.
      {
        ext.
        destruct (eqdec t a) as [->|].
        1: transitivity True ; [|rewrite fconsP] ; intuition.
        rewrite fconsP fremoveP.
        intuition (subst ; auto).
      }
      right.
      apply fimageP.
      exists (fremove a X).
      split.
      2: reflexivity.
      apply IHM => x /fremoveP [] /hX /member_fcons [->|] //.
    + left.
      apply IHM => ? /dup [] /hX /member_fcons [<-|] //.
Qed.

Instance fpow_Proper {A : DecPoset} : Proper (list_ext A ==> eq) fpow_list.
Proof.
  intros ?? ?.
  ext.
  split => /fpow_list_sound.
  all: rewrite /incl ; setoid_rewrite finsetP ; intros.
  all: apply fpow_list_complete ; rewrite /incl => *.
  all: rewrite finsetP.
  all: now apply H.
Qed.

Definition fpow {A : DecPoset} : finset A -> finset (finset A) :=
  quot_rec fpow_list.

Lemma fpowP {A : DecPoset} (X Y : finset A) : Y ∈ fpow X <-> Y ⊆ X.
Proof.
  induction X using quot_ind.
  rewrite /fpow quot_rec_eq.
  split.
  - apply fpow_list_sound.
  - apply fpow_list_complete.
Qed.  

Section FinPredDec.
  Context {A : Poset} (P : A -> Prop) `{forall x, Decision (P x)}.

  (** ** Decidability facts of various kinds can be pushed into finite sets. *)

  (* The original formalisation had a sigma rather than an existential here,
    but this does not respect the relation on the quotient. Hopefully this
    will be enough. *)
  Lemma finset_find_dec_list (l : list A) :
    { z | In z l /\ P z } + {forall z, In z l -> ~P z}.
  Proof.
    induction l as [|a ?].
    - right ; cbn ; intuition.
    - destruct IHl as [[z []]|].
      1: left ; exists z ; cbn ; now intuition.
      destruct (decide (P a)).
      1: left ; exists a ; cbn ; now intuition.
      right.
      cbn ; intuition (subst ; eauto).
  Qed.

  Lemma finset_find_dec (M: finset A) :
    {exists z, z ∈ M /\ P z } + {forall z, z ∈ M -> ~P z}.
  Proof.
    pattern M.
    eapply (quot_rect_sumbool
      (P := fun (f : finset A) => exists z, z ∈ f /\ P z)
      (Q := (fun f : finset A => forall z, z ∈ f -> ~ (P z)))).
    2: intros ? [[? []]] ; now unfold not in *.
    intros l.
    destruct (finset_find_dec_list l) as [[? []]|] ; [left;eexists|right ; intros ?].
    all: now rewrite finsetP.
  Qed.

End FinPredDec.

Lemma finset_find_dec' {A} P `{forall x, Decision (P x)} (M:finset A) :
  {exists z, z ∈ M /\ ~(P z) } + {forall z, z ∈ M -> P z}.
Proof.
  destruct (finset_find_dec (fun (x : A) => ~(P x)) M) as [|].
  1: easy.
  right.
  intros z ?.
  destruct (decide (P z)).
  1: easy.
  exfalso ; intuition eauto.
Qed.

Lemma finsubset_dec {A : DecPoset}
  (P:(finset A) -> Prop)
  `{ Hdec : forall x:finset A, Decision (P x)}
  (M:finset A) :
    { exists X:finset A, X ⊆ M /\ P X} +
    { forall X:finset A, X ⊆ M -> ~P X}.
Proof.
  destruct (finset_find_dec P (fpow M)) as [e|h].
  - left.
    destruct e as [x []].
    exists x.
    split; auto.
    now apply fpowP.
  - right; intros.
    now apply h, fpowP.
Qed.

Lemma finsubset_dec' {A : DecPoset}
  (P:finset A -> Prop)
  `{ Hdec : forall x:finset A, Decision (P x)}
  (M:finset A) :
    { exists X:finset A, X ⊆ M /\ ~ P X} +
    { forall X:finset A, X ⊆ M -> P X}.
Proof.
  destruct (finset_find_dec' P (fpow M)) as [e|h].
  - left.
    destruct e as [x []].
    exists x.
    split; auto.
    now apply fpowP.
  - right; intros.
    now apply h, fpowP.
Qed.

(** ** Swelling

    This lemma is used to construct certain finite sets.
    It works by starting with some small set and adding new
    elements to it until it satisfies some completeness property
    of interest.  We know that the process must halt because
    every new element added is drawn from a finite set [M].

    Swelling is used to construct sets that are hard to get other
    ways, such as when the defining predicate is not decidable.
    
    The swelling techinque is essentially unique to constructive
    settings; in a classical setting one would simply use a set
    comprehension principle to define the desired finite subset.
  *)

Lemma list_length_ind {A} (P : list A -> Prop) :
  (forall l, (forall l', length l' < length l -> P l') -> P l) ->
  forall (l : list A), P l.
Proof.
  intros Hstep l.
  pose proof (le_n (length l)) as e.
  revert e.
  generalize (length l) at 2.
  intros n.
  revert l.
  induction n as [? IH] using Wf_nat.lt_wf_ind.
  intros.
  apply Hstep.
  intros.
  eapply (IH (length l')).
  all: lia.
Qed.

Definition filter {A} (P : A -> Prop) `{Hdec : forall x, Decision (P x)} (l:list A) : list A :=
  filter_map (fun x => if (Hdec x) then (Some x) else None) l.

Lemma filterP {A} (P : A -> Prop) `{Hdec : forall x, Decision (P x)} (l : list A) x :
  In x (filter P l) <-> In x l /\ P x.
Proof.
  rewrite /filter filter_mapP.
  setoid_rewrite dec_Some.
  split.
  - intros (?&?&?&?) ; subst ; eauto.
  - intros ; eexists ; intuition eauto.
Qed.

Lemma swelling_lemma {A : DecPoset}
  (M:finset A)
  (INV : finset A -> Prop)
  (P : finset A -> Prop) 

  (HP : forall (z : finset A), z ⊆ M -> INV z -> 
    P z \/ exists q, q ∈ M /\ q ∉ z /\ INV (fcons q z)) :

  (exists (z : finset A), z ⊆ M /\ INV z) ->
  exists (z : finset A), z ⊆ M /\ INV z /\ P z.
Proof.
  intros [z hz].
  revert hz.
  induction z as [z] using quot_ind.
  revert HP.
  induction M as [M] using quot_ind ; intros HP [hincl hinv].
  
  assert (exists M':list A,
    (forall (q : A), In q M' <-> In q M /\ ~ In q z)) as [M' hM'].
  {
    exists (filter (fun q => ~ In q z) M).
    intros q.
    rewrite filterP.
    reflexivity.
  }
  revert z hincl hinv hM'.

  induction M' as [M' IH] using 
    (well_founded_induction (Wf_nat.well_founded_ltof _ (@length _))).
  intros z hincl hinv hM'.

  destruct (HP (to_quot z)) as [|[q [?[? hinv']]]] ; eauto.

  set (x' := filter (fun x => x <> q) M').
  apply (IH x') with (q::z).
  - red; simpl. unfold x'.
    apply filter_map_length_lt.
    eexists.
    split.
    + apply hM'.
      now rewrite -!finsetP.
    + by destruct (Decision_neg _).
  - intros ?.
    rewrite finsetP /=.
    intros [->|] => //.
    now apply hincl, finsetP.
  - now rewrite -fcons_cons in hinv'.
  - intros q'.
    rewrite /x' filterP /= hM'.
    intuition.
Qed.