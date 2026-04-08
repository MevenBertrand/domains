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

Definition ffinset (A : PreOrder) : Type := quot (list_ext A).

Definition ffinlist {A : PreOrder} (l : list A) : ffinset A := to_quot l.

Instance Proper_In {A : PreOrder} (a : A) : Proper (list_ext A ==> eq) (In a).
Proof.
  cbv -[In iff].
  intros ; now ext.
Qed.

Definition fmember {A : PreOrder} (a : A) : (ffinset A) -> Prop := quot_rec (In a).

Lemma ffinsetP {A : PreOrder} (a : A) (l : list A) :
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

Definition finset : PreOrder -> Poset :=
  promote_set ffinset (@fmember) finset_ext.

HB.instance Definition _ : IsBaseSetTheory.axioms_ finset :=
  SetIncl ffinset (@fmember) finset_ext.

Definition finlist {A : PreOrder} (l : list A) : finset A := ffinlist l.

Lemma finsetP {A : PreOrder} (X : list A) (x : A) : x ∈ (finlist X) <-> In x X.
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

Definition fimage {A B : PreOrder} (f : A -> B) (X : finset A) : finset B :=
  quot_map (map f) X.

Lemma fimageP {A B : PreOrder} (f : A -> B) (X : finset A) (y : B) :
  fmember y (fimage f X) <-> exists x, fmember x X /\ y = f x.
Proof.
  induction X as [l] using quot_ind.
  rewrite /fmember /fimage quot_map_eq quot_rec_eq in_map_iff.
  setoid_rewrite quot_rec_eq.
  split.
  all: intros [] ; now eexists.
Qed.

(** *** Empty finset *)

Definition fempty {A : PreOrder} : finset A := finlist nil.

Lemma femptyP {A : PreOrder} {x : A} : x ∈ fempty <-> False.
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

Lemma incl_fempty {A : PreOrder} (X : finset A) : X ⊆ fempty -> X = fempty.
Proof.
  intros hincl.
  ext.
  split ; try apply hincl.
  now rewrite femptyP.
Qed.

Lemma ub_emp (X : PreOrder) (a:X) : upper_bound a fempty.
Proof.
  now intros ? ?%femptyP.
Qed.

(** *** Singleton finset *)

Definition fsingle {A : PreOrder} (a : A) : finset A := finlist (a :: nil).

Lemma fsingleP {A : PreOrder} (a a' : A) :
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

Definition funion2 {A : PreOrder} (X Y : finset A) : finset A := quot_map2 (@app A) X Y.

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
  rewrite /incl /set_all.
  setoid_rewrite funion2P.
  intuition.
Qed.

Fixpoint fconcat {A : PreOrder} (XS : list (finset A)) : finset A :=
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

Definition funion {A : PreOrder} (XS : finset (finset A)) : finset A :=
  quot_rec fconcat XS.

Lemma funionP {A : PreOrder} XS (a : A) :
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


Lemma image_fempty (X Y : PreOrder) (f : X ⤳ Y) : image f fempty = fempty.
Proof.
  ext.
  rewrite imageP.
  setoid_rewrite femptyP.
  intuition.
Qed.


(** ** Decidability *)

Instance list_in_dec (A:EqTy) (X : list A) (x : A) : Decision (In x X).
Proof.
  induction X in x |- *  ; cbn.
  - now right.
  - destruct (IHX x).
    1: now left.
    destruct (decide (a = x)).
    1: now left.
    right.
    intuition.
Qed.

Lemma finset_in_dec {A:DecPreOrd} (X : finset A) (x : A) : Decision (x ∈ X).
Proof.
  pattern X.
  apply quot_rect_irr ; clear.
  2: typeclasses eauto.
  intros X.
  rewrite /Decision /member /=.
  destruct (decide (In x X)) ; [left|right].
  all: now rewrite ffinsetP.
Qed.

Hint Extern 100 (Decision (_ ∈ _)) => (apply: finset_in_dec) : typeclass_instances. 

(** ** More interesting finite sets *)

(** *** Adding an element to a finset *)

Definition fcons {A : PreOrder} (a : A) (X : finset A) : finset A :=
  funion2 (fsingle a) X.

Lemma fconsP {A:PreOrder} (a:A) (X:finset A) (x:A) :
  x ∈ fcons a X <-> a = x \/ x ∈ X.
Proof.
  rewrite /fcons funion2P fsingleP.
  intuition.
Qed.

Lemma ub_fcons (X:PreOrder) (x:X) (xs:finset X) (a:X) :
  x ≤ a ->
  upper_bound a xs ->
  upper_bound a (fcons x xs).
Proof.
  rewrite /upper_bound.
  now intros ? ? ? [->|]%fconsP **.
Qed.

Lemma fcons_cons {A : PreOrder} (a : A) l : finlist (a :: l) = fcons a (finlist l).
Proof.
  ext.
  now rewrite finsetP /= -finsetP fconsP.
Qed.

Lemma fcons_incl {A : PreOrder} {set : SetTheory} (X : finset A) (a : A) (Y : set A) :
  fcons a X ⊆ Y <-> a ∈ Y /\ X ⊆ Y.
Proof.
  rewrite /incl /set_all.
  setoid_rewrite fconsP.
  intuition (subst ; auto).
Qed.
 
Program Definition fcons_mon {A : PreOrder} (x : A) : (finset A) ⤳ (finset A) :=
  {| mon_map := fcons x |}.
Next Obligation.
  intros Y Z Hincl.
  rewrite !set_leP in Hincl |- *.
  intros ?.
  rewrite !fconsP.
  intuition eauto.
Qed.

(** *** Induction *)

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

Definition finset_rect_irr {A} (P : finset A -> Type)
  `{forall (l : list A), ProofIrrel (P (finlist l))} :
  P fempty ->
  (forall a X, P X -> P (fcons a X)) ->
  forall X, P X.
Proof.
  intros IH IH'.
  apply quot_rect_irr.
  2: assumption.
  intros X.
  induction X.
  1: now apply IH.
  enough ((fcons a (to_quot X)) = to_quot (a :: X)) as <-
    by easy.
  ext.
  now rewrite fconsP !finsetP /=.
Qed.

(** An induction principle phrased in terms of least upper bound *)
Definition list_max {A : PreOrder} (min : A) (max : A -> A -> A) (l : list A) : A :=
  fold_right max min l.

Lemma list_lub {A : PreOrder} (min : A) (max : A -> A -> A) (l : list A) :
  (forall x, min ≤ x) ->
  (forall x y, x ≤ max x y) ->
  (forall x y, y ≤ max x y) ->
  (forall x y z, x ≤ z -> y ≤ z -> max x y ≤ z) ->
  least_upper_bound (list_max min max l) (finlist l).
Proof.
  intros Hmin Hmax_l Hmax_r Hmax_max.
  rewrite /least_upper_bound /upper_bound ; cbn. 
  induction l.
  - cbn.
    split.
    2: eauto.
    intros ? ?%finsetP.
    now exfalso.
  - cbn ; split.
    + intros x.
      rewrite finsetP /= -finsetP.
      intros [->| ].
      1: eauto.
      etransitivity.
      1: now apply IHl.
      eauto.
    + intros b Hle.
      apply Hmax_max.
      * specialize (Hle a).
        now rewrite finsetP /= in Hle.
      * apply IHl.
        intros ? Hin.
        apply Hle.
        now rewrite !finsetP in Hin |- * ; cbn.
Qed.

Program Definition finset_lub {A : Poset} (min : A) (max : A -> A -> A) :
  (forall x, min ≤ x) ->
  (forall x y, x ≤ max x y) ->
  (forall x y, y ≤ max x y) ->
  (forall x y z, x ≤ z -> y ≤ z -> max x y ≤ z) ->
  finset A -> A :=
  fun _ _ _ _ => (quot_rec (list_max min max) (p := _)).
Next Obligation.
  intros l l' Hext.
  assert (finlist l = finlist l') as e by now apply quot_ext.
  eapply lub_unique.
  1: now apply list_lub.
  rewrite e.
  now apply list_lub.
Qed.

Lemma finset_lub_lub {A : Poset} (min : A) (max : A -> A -> A)
  (Hmin : forall x, min ≤ x)
  (Hmax_l : forall x y, x ≤ max x y)
  (Hmax_r : forall x y, y ≤ max x y)
  (Hmax_max : forall x y z, x ≤ z -> y ≤ z -> max x y ≤ z) :
  forall M, least_upper_bound (finset_lub min max Hmin Hmax_l Hmax_r Hmax_max M) M.
Proof.
  intros M.
  induction M as [l] using quot_ind.
  rewrite /finset_lub quot_rec_eq.
  now apply list_lub.
Qed.

(** Another version, probably less useful, expressed in terms of a
  commutative associative idempotent operation *)

Section FinsetRec.
  Context
    {A : PreOrder} (base : A) (op : A -> A -> A)
    (Hcom : forall x y, op x y = op y x)
    (Hass : forall x y z, op x (op y z) = op (op x y) z)
    (Hidm : forall x, op x x = x).

  Notation list_fold := (fold_right op base).

  Lemma list_fold_in (l : list A) (x : A) : In x l -> op x (list_fold l) = list_fold l.
  Proof.
    intros Hin.
    induction l ; cbn in *.
    1: easy.
    destruct Hin as [->|].
    1: now rewrite Hass Hidm.
    rewrite Hass (Hcom x a) -Hass IHl //.
  Qed.

  Lemma list_fold_base (l : list A) : op base (list_fold l) = list_fold l.
  Proof.
    induction l ; cbn in *.
    1: apply Hidm.
    rewrite Hass (Hcom base a) -Hass IHl //.
  Qed.

  Lemma list_fold_incl (l l' : list A) :
    (forall x, In x l' -> In x l) ->
    list_fold (l' ++ l) = list_fold l.
  Proof.
    intros Hin.
    induction l' ; cbn.
    1: reflexivity.
    rewrite list_fold_in ?IHl' //.
    - apply in_app_iff.
      right.
      now apply Hin ; cbn.
    - intros.
      now apply Hin ; cbn.
  Qed.
  
  Lemma list_fold_app_cons (l l' : list A) (x : A) :
    list_fold (l' ++ (x :: l)) = op x (list_fold (l' ++ l)).
  Proof.
    induction l' ; cbn.
    1: reflexivity.
    rewrite IHl' Hass (Hcom a x) -Hass //.
  Qed.

  Lemma list_fold_app (l l' : list A) :
    list_fold (l' ++ l) = list_fold (l ++ l').
  Proof.
    induction l' ; cbn.
    1: now rewrite app_nil_r.
    rewrite list_fold_app_cons IHl' //.
  Qed.

  Lemma list_fold_unique : Proper (list_ext A ==> eq) list_fold.
  Proof.
    intros l l' Hext.
    red in Hext.
    rewrite -(list_fold_incl l l').
    1: firstorder.
    rewrite list_fold_app list_fold_incl //.
    firstorder.
  Qed.

  Definition finset_fold : finset A -> A := quot_rec list_fold (p := list_fold_unique).

  Lemma fold_single a : finset_fold (single a) = op a base.
  Proof.
    by rewrite /finset_fold /single /= /fsingle quot_rec_eq /=.
  Qed.

  Lemma fold_union2 X Y : finset_fold (funion2 X Y) = op (finset_fold X) (finset_fold Y).
  Proof.
    induction X as [l] using quot_ind.
    induction Y as [l'] using quot_ind.
    rewrite /finset_fold /funion2 quot_map2_eq !quot_rec_eq.
    rewrite fold_right_app.
    induction l ; cbn.
    1: now rewrite list_fold_base.
    now rewrite IHl Hass.
  Qed.

  Lemma fold_empty : finset_fold fempty = base.
  Proof.
    rewrite /finset_fold quot_rec_eq //.
  Qed.

End FinsetRec.

Definition finset_rec
  {A B : PreOrder} (base : B) (op : B -> B -> B) (into : A -> B)
    (Hcom : forall x y, op x y = op y x)
    (Hass : forall x y z, op x (op y z) = op (op x y) z)
    (Hidm : forall x, op x x = x) :
  finset A -> B := fun X => finset_fold base op Hcom Hass Hidm (fimage into X).

(** *** Filter + map *)

Section FilterMap.
  Context {A B:Type}.

  Fixpoint filter_map_dep (l:list A) : (forall (x : A), In x l -> option B) -> list B :=
    match l with
    | nil => fun _ => nil
    | x::xs => fun f => let l := filter_map_dep xs (fun x h => f x (or_intror h))
        in match (f x (or_introl erefl)) with | None => l | Some b => b :: l end
    end.

  Definition filter_map (f : A -> option B) (l:list A) : list B :=
    filter_map_dep l (fun x _ => f x).

  Lemma filter_map_depP (l : list A) (f : forall (x : A), In x l -> option B) b :
    In b (filter_map_dep l f) <-> exists a (h : In a l), f a h = Some b.
  Proof.
    induction l ; cbn.
    1: intuition ; match goal with H : exists _, _ |- _ => now destruct H end.
    destruct (f a _) eqn:e ; cbn in *.
    - rewrite IHl ; clear IHl.
      intuition (subst ; eauto).
      (match goal with H : exists _, _ |- _ => destruct H as (a'&[->|]&e') end) ;
      intuition (subst ; eauto).
      left.
      rewrite e in e'.
      congruence.
    - rewrite IHl ; clear IHl.
      intuition (subst ; eauto) ;
          repeat (match goal with H : exists _, _ |- _ => destruct H as (a'&[->|]&e') end) ;
      intuition (subst ; eauto).
      rewrite e in e'.
      congruence.
  Qed.

  Corollary filter_mapP (l : list A) (f : A -> option B) b :
    In b (filter_map f l) <-> exists a, In a l /\ f a = Some b.
  Proof.
    unfold filter_map.
    rewrite filter_map_depP.
    now intuition eauto.
  Qed.

  Lemma filter_map_length l f : length (filter_map_dep l f) <= length l.
  Proof.
    induction l as [|a] in f |- * ; cbn.
    1: reflexivity.
    destruct ((f a)) ; cbn.
    - now apply le_n_S.
    - etransitivity ; [eauto|].
      lia.  
  Qed.

  Lemma filter_map_length_lt l f :
    (exists x (h : In x l), f x h = None) ->
    (length (filter_map_dep l f) < length l)%nat.
  Proof.
    intros [x [Hin HP]].
    induction l in x, Hin, HP, f |- * ; cbn in *.
    1: intuition.
    destruct Hin as [<-|Hin].
    all: destruct (f a _) eqn:? ; cbn ; try solve [intuition | congruence].
    - pose proof (filter_map_length l (fun (x : A) (h : In x l) => f x (or_intror h))) ; lia.
    - now eapply le_n_S, IHl.
    - etransitivity.
      1: now eapply IHl.
      lia. 
  Qed.

  Instance filter_Proper f : Proper (list_ext A ==> list_ext B) (filter_map f).
  Proof.
    intros ?? e ?.
    rewrite !filter_mapP.
    red in e.
    now setoid_rewrite e.
  Qed.

End FilterMap.

Existing Instance filter_Proper.

#[local]Definition transp_lemma {A B C} (f : A -> B) {P : B -> Type} (F : forall x : A, P (f x) -> C)
  (x y : A) (e : f x = f y) (p : P (f y)) :
  (transport _ e (F x)) p = F x (transport _ (eq_sym e) p).
Proof.
  now destruct e.
Qed.

#[local]Definition transp_lemma' {A B C} {P : A -> B -> Type} (b b' : B) (e : b = b') 
  (F : forall x : A, P x b -> C)
  (a : A) (p : P a b') :
  transport _ e F a p = F a (transport _ (eq_sym e) p).
Proof.
  now destruct e.
Qed.

Definition finfilter_map_dep {A B : PreOrder} (X : finset A) (f : forall x, x ∈ X -> option B) : finset B.
Proof.
  revert f.
  set (F := fun (l : list A) (f : (forall x : A, x ∈ finlist l -> option B)) =>
    finlist (filter_map_dep l (fun x h => f x (snd (finsetP l x) h)))).
  pattern X.
  unshelve eapply quot_rect.
  1: exact F.
  intros l l' e ; cbn.
  apply fun_ext.
  intros f.
  rewrite transp_lemma.
  apply set_ext.
  intros b.
  rewrite /F !finsetP !filter_map_depP ; cbn.
  split ; intros (a&h&eq).
  all: exists a.
  - unshelve eexists.
    1: now apply e.
    rewrite -eq transp_lemma'.
    f_equal.
    ext.
  - unshelve eexists.
    1: now apply e.
    rewrite -eq transp_lemma'.
    f_equal.
    ext.
Defined.

Lemma finfilter_map_depP {A B : PreOrder} (X : finset A) (f : forall x, x ∈ X -> option B) (x : B) :
  x ∈ (finfilter_map_dep X f) <->
  exists a (h : a ∈ X), (f a h = Some x).
Proof.
  induction X as [X] using quot_ind.
  rewrite -/(finlist X) /finfilter_map_dep quot_rect_eq !finsetP filter_map_depP.
  split.
  all: intros (a&h&e).
  all: unshelve eexists a, _ ; [now apply finsetP|].
  all: rewrite -e.
  all: f_equal ; ext.
Qed.

Opaque finfilter_map_dep.

Definition finfilter_map {A B : PreOrder} (f : A -> option B) : finset A -> finset B :=
  quot_map (filter_map f).

Lemma finfilter_mapP {A B : PreOrder} (f : A -> option B) (X : finset A) (x : B) :
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
  Context {A:PreOrder} (P : A -> Prop) `{Hdec : forall x, Decision (P x)}.

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

  Lemma finsubset_fempty : finsubset fempty = fempty.
  Proof.
    ext.
    rewrite finsubsetP !femptyP ; intuition.
  Qed.

  Lemma finsubset_incl (X : finset A) : finsubset X ⊆ X.
  Proof.
    move => ? /finsubsetP [] //.
  Qed.

  Lemma incl_finsubset (X Y : finset A) : Y ⊆ finsubset X <-> (Y ⊆ X) /\ ∀ x ∈ Y, P x.
  Proof.
    rewrite /incl /set_all.
    setoid_rewrite finsubsetP.
    intuition eauto.
    all: now edestruct H.
  Qed.
  
End FinSubset.

Section FinSubsetDep.
  Context {A:PreOrder} (P : A -> Prop).

  Definition finsubset_dep (X : finset A) (Hdec : forall x, x ∈ X -> Decision (P x)) : finset A :=
    finfilter_map_dep X (fun x h => if (Hdec x h) then (Some x) else None).

  Lemma finsubset_depP (X : finset A) Hdec x : x ∈ (finsubset_dep X Hdec) <-> x ∈ X /\ P x.
  Proof.
    rewrite /finsubset_dep finfilter_map_depP.
    split.
    - intros (a&h&e).
      destruct (Hdec a h).
      2: congruence.
      now inversion e ; subst.
    - intros [Hin Hp] ; eexists x, Hin.
      now rewrite decide_True.
  Qed.
  
End FinSubsetDep.

(** *** Cartesian product of finite sets *)

Instance Proper_prod {A B} :
  Proper (list_ext A ==> list_ext B ==> list_ext (A*B)) (@list_prod _ _).
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros * H * H' [].
  now rewrite !in_prod_iff H H'.
Qed.

Definition finprod {A B:PreOrder} (P:finset A) (Q:finset B) : finset (A*B) :=
  quot_map2 (@list_prod _ _) P Q.

Lemma finprodP A B (P:finset A) (Q:finset B) a b :
  (a,b) ∈ finprod P Q <-> (a ∈ P /\ b ∈ Q).
Proof.
  induction P using quot_ind.
  induction Q using quot_ind.
  now rewrite /finprod quot_map2_eq !finsetP in_prod_iff.
Qed.

(** *** Disjoint union of finite sets *)

Definition left_finset {A B : PreOrder} (X : finset (A + B)) : finset A :=
  finfilter_map (fun x => match x with | inl a => Some a | inr _ => None end) X.

Lemma left_finsetP {A B : PreOrder} (X : finset (A + B)) (a : A) :
  a ∈ left_finset X <-> (inl a) ∈ X.
Proof.
  rewrite /left_finset finfilter_mapP.
  split.
  - intros ([]&[]) ; solve [easy|congruence].
  - intros.
    now eexists (inl _).
Qed.

Definition right_finset {A B : PreOrder} (X : finset (A + B)) : finset B :=
  finfilter_map (fun x => match x with | inl _ => None | inr b => Some b end) X.

Lemma right_finsetP {A B : PreOrder} (X : finset (A + B)) (b : B) :
  b ∈ right_finset X <-> (inr b) ∈ X.
Proof.
  rewrite /right_finset finfilter_mapP.
  split.
  - intros ([]&[]) ; solve [easy|congruence].
  - intros.
    now eexists (inr _).
Qed.

Definition finsum {A B:PreOrder} (P:finset A) (Q:finset B) : finset (A + B) :=
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

Lemma left_right_finset_finsum {A B : PreOrder} (X : finset (A + B)):
  X = finsum (left_finset X) (right_finset X).
Proof.
  apply set_ext.
  intros [|].
  all: by rewrite ?finsum_right_elem ?finsum_left_elem ?left_finsetP ?right_finsetP.
Qed.

Lemma incl_finsum {A B : PreOrder} (X X' : finset A) (Y Y' : finset B) :
  finsum X Y ⊆ finsum X' Y' <-> X ⊆ X' /\ Y ⊆ Y'.
Proof.
  rewrite /incl /set_all.
  split.
  - intros Hsum.
    split.
    + move => x.
      specialize (Hsum (inl x)).
      now rewrite !finsum_left_elem in Hsum.
    + move => x.
      specialize (Hsum (inr x)).
      now rewrite !finsum_right_elem in Hsum.
  - move => [Hl Hr] [a|b].
    + now rewrite !finsum_left_elem.
    + now rewrite !finsum_right_elem.
Qed.

Section FinEqDec.
  Context {A : DecPreOrd}.

  (**  We can take the intersection of finite sets if the elements
      have decidable equality.
    *)

  Definition finter2 (X Y : finset A) : finset A := finsubset (member^~ X) Y.

  Lemma finter2P X Y x :
    x ∈ finter2 X Y <-> (x ∈ X /\ x ∈ Y).
  Proof.
    rewrite /finter2 finsubsetP.
    intuition.
  Qed.

  Lemma finter2_incl (X Y Z : finset A) : X ⊆ finter2 Y Z <-> X ⊆ Y /\ X ⊆ Z.
  Proof.
    rewrite /incl /set_all.
    setoid_rewrite finter2P.
    split.
    - intros H ; split ; intros ; now apply H.
    - intuition.
  Qed.

  Fixpoint finter_list (X : finset A) (XS : list (finset A)) : finset A :=
  match XS with
  | nil => X
  | x :: XS => finter2 (finter_list X XS) x
  end.

  Lemma finter_listP (X : finset A) (XS : list (finset A)) (a : A) :
    a ∈ (finter_list X XS) <-> (a ∈ X /\ (forall Y, In Y XS -> a ∈ Y)).
  Proof.
    induction XS ; cbn.
    - intuition.
    - rewrite finter2P IHXS.
      intuition (subst ; auto).
  Qed.

  Instance Proper_finter_list X : Proper (list_ext (finset A) ==> eq) (finter_list X).
  Proof.
    rewrite /Proper /respectful.
    intros l l' H.
    ext.
    rewrite !finter_listP.
    unfold list_ext in H.
    now setoid_rewrite H.
  Qed.

  Definition finter (X : finset A) (XS : finset (finset A)) : finset A :=
    quot_rec (finter_list X) XS.

  Lemma finterP X XS (a : A) :
    a ∈ (finter X XS) <-> (a ∈ X /\ (∀ Y ∈ XS, a ∈ Y)).
  Proof.
    induction XS as [l] using quot_ind.
    rewrite /finter quot_rec_eq finter_listP /set_all.
    setoid_rewrite finsetP.
    reflexivity.
  Qed.


  Lemma finter_incl (X Y : finset A) (Z : finset (finset A)) :
    X ⊆ finter Y Z <-> (X ⊆ Y /\ ∀ z ∈ Z, X ⊆ z).
  Proof.
    rewrite /incl /set_all.
    setoid_rewrite finterP.
    rewrite /set_all.
    split.
    - intros H ; split.
      + now intros ? ?%H.
      + intros ; now apply H.  
    - intuition.
  Qed.

(**  We can remove an element from a finite set if the elements have
     decidable equality.
  *)

  Definition fremove (x : A) : finset A -> finset A := finsubset (fun y => y <> x).

  Lemma fremoveP (X : finset A) x y : y ∈ (fremove x X) <-> y ∈ X /\ (y <> x).
  Proof.
    by rewrite /fremove finsubsetP.
  Qed.

  Lemma fremove_incl (X : finset A) x : fremove x X ⊆ X.
  Proof.
    rewrite /incl /set_all ; intros ? ; now rewrite fremoveP.
  Qed.

End FinEqDec.

(**  We can take the powerset of a finite set; that is, all finite
     subsets of a finite set.
  *)

Fixpoint fpow_list {A:PreOrder} (l:list A) : finset (finset A) :=
  match l with
  | nil => single (A := finset A) fempty
  | x :: xs =>
       let pow := fpow_list xs in
          funion2 pow (image (fcons_mon x) pow)
  end.

Lemma member_fcons {A : PreOrder} (a : A) M x :
  x ∈ (finlist (a :: M)) <-> a = x \/ x ∈ finlist M.
Proof.
  rewrite !finsetP /=.
  intuition.
Qed.

Lemma fpow_list_sound {A : PreOrder} (M : list A) (X: finset A) :
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

Lemma fpow_list_complete (A : DecPreOrd) (M : list A) (X: finset A) :
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
        destruct (decide (t=a)) as [->|].
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

Instance fpow_Proper {A : DecPreOrd} : Proper (list_ext A ==> eq) fpow_list.
Proof.
  intros ?? ?.
  ext.
  split => /fpow_list_sound.
  all: rewrite /incl /set_all ; setoid_rewrite finsetP ; intros.
  all: apply fpow_list_complete ; rewrite /incl /set_all => *.
  all: rewrite finsetP.
  all: now apply H.
Qed.

Definition fpow {A : DecPreOrd} : finset A -> finset (finset A) :=
  quot_rec fpow_list.

Lemma fpowP {A : DecPreOrd} (X Y : finset A) : Y ∈ fpow X <-> Y ⊆ X.
Proof.
  induction X using quot_ind.
  rewrite /fpow quot_rec_eq.
  split.
  - apply fpow_list_sound.
  - apply fpow_list_complete.
Qed.  

(** ** Decidability facts of various kinds can be pushed into finite sets. *)

Section FinPredDec.
  Context {A : PreOrder} (P : A -> Prop).

  (* The original formalisation had a sigma rather than an existential here,
    but this does not respect the relation on the quotient. Hopefully this
    will be enough. *)
  Lemma finset_find_dec_list (l : list A) (Hdec : forall x, In x l -> Decision (P x)) :
    { z | In z l /\ P z } + {forall z, In z l -> ~P z}.
  Proof.
    induction l as [|a ?].
    - right ; cbn ; intuition.
    - destruct IHl as [[z []]|].
      + intros.
        apply Hdec.
        now cbn.
      + left ; exists z ; cbn ; now intuition.
      + assert (Decision (P a)) by (apply Hdec ; now cbn).
        destruct (decide (P a)).
        1: left ; exists a ; cbn ; now intuition.
        right.
        cbn ; intuition (subst ; eauto).
  Qed.

  Lemma finset_find_dec_dep (M : finset A) (Hdec : forall x, x ∈ M -> Decision (P x)) :
    Decision (∃ z ∈ M, P z).
  Proof.
    revert Hdec.
    pattern M.
    eapply quot_rect_irr.
    2: typeclasses eauto.
    intros l Hdec.
    destruct (finset_find_dec_list l) as [[? []]|].
    - intros.
      apply Hdec.
      now rewrite finsetP.
    - left;eexists.
      now rewrite finsetP.
    - right ; intros (?&[?%finsetP]).
      firstorder.
  Qed.

End FinPredDec.

#[global] Instance finset_find_dec {A : PreOrder} {P : A -> Prop}
  (M: finset A) `{forall x, Decision (P x)}: Decision (∃ z ∈ M, P z).
Proof.
  now apply finset_find_dec_dep.
Qed.

(* #[global] Instance finset_find_sum {A : PreOrder} (P : A -> Prop)
  (M: finset A) `{forall x, Decision (P x)} : Decision (∃ z ∈ M, P z).
Proof.
  apply DecisionDecSum.
  1: now apply finset_find_dec_dep.
  intros Hneg ???.
  apply Hneg ; now eexists.
Qed. *)

Lemma finset_all_dec_dep  {A : PreOrder} {P : A -> Prop}
  (M : finset A) (Hdec : forall x, x ∈ M -> Decision (P x)) :
  Decision (∀ z ∈ M, P z).
Proof.
  replace (∀ z ∈ M, P z) with (~(∃ z ∈ M, ~ (P z))).
  1: apply not_dec, finset_find_dec_dep ; intros ; now apply not_dec.
  rewrite /set_ex /set_all.
  ext.
  split.
  2: intuition eauto.
  intros Hn ??.
  apply (@dec_stable (P x)); auto.
  intros ?.
  apply Hn.
  now eexists.
Qed.

#[global]Instance finset_all_dec {A : PreOrder} {P : A -> Prop} `{forall x, Decision (P x)} (M: finset A)
  : Decision (∀ z ∈ M, P z).
Proof.
  now apply finset_all_dec_dep.
Qed.

(* #[global] Instance finset_all_sum {A : PreOrder} (P : A -> Prop)
  (M: finset A) `{forall x, Decision (P x)} : DecSum (∀ z ∈ M, P z) (∃ z ∈ M, ~ P z).
Proof.
  apply DecisionDecSum.
  1: typeclasses eauto.
  intros Hneg.
  apply (dec_stable _).
  intros Hneg'.
  apply Hneg.
  intros ??.
  apply (dec_stable _).
  intros ?.
  apply Hneg'.
  now eexists.
Qed. *)

Lemma finset_not_ex {A : PreOrder} {P : A -> Prop} `{forall x, Decision (P x)} (M: finset A)
  : ~ (∃ z ∈ M, P z) -> (∀ z ∈ M, ~ P z).
Proof.
  intros Hneg z Hz HP.
  apply Hneg.
  now eexists.
Qed.

Lemma finset_not_all {A : PreOrder} (P : A -> Prop) `{forall x, Decision (P x)} (M: finset A)
  : ~ (∀ z ∈ M, P z) -> (∃ z ∈ M, ~ P z).
Proof.
  intros Hneg.
  apply (dec_stable _).
  intros Hneg'.
  apply Hneg.
  intros ??.
  apply (dec_stable _).
  intros ?.
  apply Hneg'.
  now eexists.
Qed.

#[global]Instance fin_incl_dec {A : DecPreOrd} (X Y : finset A)
  : Decision (X ⊆ Y).
Proof.
  rewrite /incl.
  typeclasses eauto.
Qed.

#[global]Instance finset_empty {A : PreOrder} (M : finset A) : Decision (M = fempty).
Proof.
  pattern M.
  eapply quot_rect_irr.
  2: typeclasses eauto.
  intros [|a].
  1: now left.
  right.
  intros e.
  change (In a nil).
  now rewrite -finsetP -/fempty -e finsetP /=.
Qed.

Lemma finset_not_empty  {A : PreOrder} (M : finset A) :
  (M <> fempty) -> (exists x, x ∈ M).
Proof.
  pattern M.
  apply quot_rect_irr.
  2: typeclasses eauto.
  intros [|] ; cbn.
  1: now intros [].
  intros _.
  eexists.
  now rewrite finsetP /=.
Qed.

Instance finsubset_dec {A : DecPreOrd}
  (P:(finset A) -> Prop)
  `{ Hdec : forall x:finset A, Decision (P x)}
  (M:finset A) :
    Decision (exists X:finset A, X ⊆ M /\ P X).
Proof.
  replace (exists X : finset A, _) with (∃ z ∈ (fpow M), P z).
  1: typeclasses eauto.
  ext.
  unfold set_ex.
  setoid_rewrite fpowP.
  reflexivity.
Qed.

Instance finsubset_dec' {A : DecPreOrd}
  (P:(finset A) -> Prop)
  `{ Hdec : forall x:finset A, Decision (P x)}
  (M:finset A) :
    Decision (forall X:finset A, X ⊆ M -> P X).
Proof.
  replace (forall X : finset A, _) with (∀ z ∈ (fpow M), P z).
  1: typeclasses eauto.
  ext.
  unfold set_all.
  setoid_rewrite fpowP.
  reflexivity.
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
  (forall l, (forall l', length l' < length l -> P l') -> P l)%nat ->
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

Lemma swelling_lemma {A : DecPreOrd}
  (M:finset A)
  (INV : finset A -> Prop)
  (P : finset A -> Prop) 

  (HP : forall (z : finset A), z ⊆ M -> INV z -> 
    P z \/ ∃ q ∈ M, q ∉ z /\ INV (fcons q z)) :

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
    + now rewrite decide_False.
  - intros ?.
    rewrite finsetP /=.
    intros [->|] => //.
    now apply hincl, finsetP.
  - now rewrite -fcons_cons in hinv'.
  - intros q'.
    rewrite /x' filterP /= hM'.
    intuition.
Qed.