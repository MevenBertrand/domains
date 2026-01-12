(** * domains.finsets: the set theory of finite sets *)
From Stdlib Require Import List Program ssreflect ssrfun
  Relations Classes.RelationClasses Classes.Morphisms Decidable Lia.
From HB Require Import structures.

Require Import utils.all categories.all preord sets.

Open Scope general_if_scope.

(** Here we define the theory of finite sets.  Concretely,
    finite sets are represented by the extensional
    quotient of the list type. Singleton sets are given
    by one-element lists, union is defined by list
    concatenation and image is the stadard list map function.
  *)

(** ** Finite sets form a set theory *)

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

Definition finset (A : Type) : Type := quot (list_ext A).

Definition finlist {A : Type} (l : list A) : finset A := to_quot l.

Instance Proper_In {A} (a : A) : Proper (list_ext A ==> eq) (In a).
Proof.
  cbv -[In iff].
  intros ; now ext.
Qed.

Definition fmember {A : Type} (a : A) : (finset A) -> Prop := quot_rec (In a).

Lemma ffinsetP {A : Type} (a : A) (l : list A) :
  fmember a (finlist l) <-> In a l.
Proof.
  by rewrite /fmember quot_rec_eq.
Qed.

Lemma finset_ext {A : Type} (f f' : finset A) :
  (forall x, fmember x f <-> fmember x f') ->
  f = f'.
Proof.
  pattern f.
  apply quot_ind.
  intros l.
  pattern f'.
  apply quot_ind.
  intros l'.
  intros H.
  apply quot_ext.
  intros x.
  by rewrite <- !ffinsetP.
Qed.

Definition fsingle {A : Type} (a : A) : finset A := finlist (a :: nil).

Lemma fsingleP {A : Type} (a a' : A) :
  fmember a (fsingle a') <-> a = a'.
Proof.
  rewrite /fsingle ffinsetP /=.
  intuition.
Qed.

Instance map_In {A B : Type} (f : A -> B) :
  Proper (list_ext A ==> list_ext B) (map f).
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros l l' H b.
  rewrite !in_map_iff.
  split.
  all: intros [a [<- Hin]].
  all: eexists ; split ; [reflexivity|].
  all: now apply H.
Qed.

Definition fimage {A B : Type} (f : A -> B) (X : finset A) : finset B :=
  quot_map (map f) X.

Lemma fimageP {A B : Type} (f : A -> B) (X : finset A) (y : B) :
  fmember y (fimage f X) <-> exists x, fmember x X /\ y = f x.
Proof.
  pattern X.
  apply quot_ind.
  intros l.
  rewrite /fmember /fimage quot_map_eq quot_rec_eq in_map_iff.
  split.
  all: move => [x []].
  all: rewrite ?quot_rec_eq.
  all: exists x.
  all: rewrite ?quot_rec_eq ; now subst.
Qed.

Instance Proper_app {A} :
  Proper (list_ext A ==> list_ext A ==> list_ext A) (app (A:=A)).
Proof.
  intros.
  rewrite /Proper /respectful /list_ext /=.
  intros l1 l1' H1 l2 l2' H2 a.
  rewrite !in_app_iff !H1 !H2.
  reflexivity.
Qed.

Program Definition funion2 {A : Type} (X Y : finset A) : finset A :=
  quot_map2 (@app A) X Y.


Fixpoint fconcat {A : Type} (XS : list (finset A)) : finset A :=
  match XS with
  | nil => to_quot nil
  | x :: XS => funion2 (fconcat XS) x
  end.

Lemma ffunion2P {A} (f f' : finset A) (x : A) :
  fmember x (funion2 f f') <-> fmember x f \/ fmember x f'.
Proof.
  pattern f.
  apply quot_ind.
  intros l.
  pattern f'.
  apply quot_ind.
  intros l'.
  now rewrite /funion2 quot_map2_eq !ffinsetP in_app_iff.
Qed.

Lemma ffconcatP {A} (XS : list (finset A)) (a : A) :
  fmember a (fconcat XS) <-> (exists X, In X XS /\ fmember a X).
Proof.
  induction XS ; cbn.
  - rewrite /fmember quot_rec_eq.
    transitivity False.
    1: by split ; eauto using in_nil.
    split ; [done|..].
    now intros [].
  - rewrite ffunion2P IHXS.
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
  apply finset_ext.
  intros x.
  rewrite !ffconcatP.
  unfold list_ext in H.
  split ; intros [? []] ; eexists.
  all: now split ; [apply H|..].
Qed.

Definition funion {A : Type} (XS : finset (finset A)) : finset A :=
  quot_rec fconcat XS.

Lemma funionP {A : Type} (XS : finset (finset A)) a :
  fmember a (funion XS) <-> (exists X, fmember X XS /\ fmember a X).
Proof.
  pattern XS.
  apply quot_ind.
  intros l.
  rewrite /funion quot_rec_eq ffconcatP.
  split ; intros [? []] ; eexists.
  all: now split ; [apply ffinsetP|..].
Qed.

HB.instance Definition _ :=
  IsPreSetTheory.Build finset (@fmember) (@fsingle) (@fimage) (@funion).

HB.instance Definition _ :=
  IsSetTheory.Build finset
    (@finset_ext) (@fsingleP) (@funionP) (@fimageP).

Lemma finsetP {A} (X : list A) (x : A) : x ∈ (finlist X) <-> In x X.
Proof.
  apply ffinsetP.
Qed.

Lemma funion2P {A} (f f' : finset A) (x : A) :
  x ∈ (funion2 f f') <-> x ∈ f \/ x ∈ f'.
Proof.
  apply ffunion2P.
Qed.

Lemma fconcatP {A} (XS : list (finset A)) (a : A) :
  a ∈ (fconcat XS) <-> (exists X, In X XS /\ a ∈ X).
Proof.
  apply ffconcatP.
Qed.

(** ** Properties of finite sets *)

(** *** Decidability *)

Program Definition finset_dec (A:Type) (e : (forall x y : A, {x = y} + {x <> y})) :
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

(** ** Interesting finite sets *)

(** *** Empty set *)

Definition fempty {A : Type} : finset A := finlist nil.

Lemma femptyP {A : Type} {x : A} : x ∈ fempty <-> False.
Proof.
  split ; [..|easy].
  rewrite /fempty finsetP.
  apply in_nil.
Qed.

Lemma fempty_incl X (Q:finset X) :
  fempty ⊆ Q.
Proof.
  now intros ? ?%femptyP.
Qed.

Lemma incl_fempty {A} (X : finset A) : X ⊆ fempty -> X = fempty.
Proof.
  intros hincl.
  ext.
  split ; try apply hincl.
  now rewrite femptyP.
Qed.

Lemma ub_nil (X : Poset) (a:X) : upper_bound a fempty.
Proof.
  now intros ? ?%femptyP.
Qed.

Program Definition fcons {A : Type} (a : A) (X : finset A) : finset A :=
  quot_map (cons a) (e := _) X.
Next Obligation.
  rewrite /Proper /respectful /list_ext /=.
  intros ? x _ l l' e x'.
  now rewrite e.
Qed.

Lemma fconsP {A:Type} (a:A) (X:finset A) (x:A) :
  x ∈ fcons a X <-> a = x \/ x ∈ X.
Proof.
  pattern X.
  apply quot_ind.
  intros l.
  now rewrite /fcons /member /= /fmember quot_map_eq !quot_rec_eq /=.
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

(**  Cartesian product of finite sets *)

Instance Proper_prod {A B} : Proper (list_ext A ==> list_ext B ==> list_ext (A*B)) (@list_prod _ _).
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros * H * H' [].
  now rewrite !in_prod_iff H H'.
Qed.

Definition finprod {A B:Type} (P:finset A) (Q:finset B) : finset (A*B) :=
  quot_map2 (@list_prod _ _) P Q.

Lemma finprodP A B (P:finset A) (Q:finset B) a b :
  (a,b) ∈ finprod P Q <-> (a ∈ P /\ b ∈ Q).
Proof.
  pattern P ; apply quot_ind ; intros l.
  pattern Q ; apply quot_ind ; intros l'.
  now rewrite /finprod quot_map2_eq !finsetP in_prod_iff.
Qed.

(**  Disjoint union of finite sets *)

Fixpoint left_list {A B} (l : list (A + B)) : list A :=
  match l with
  | nil => nil
  | inl a :: l' => a :: left_list l'
  | inr _ :: l' => left_list l'
  end.

Lemma left_in {A B} (l : list (A + B)) (a : A) : In (inl a) l <-> In a (left_list l).
Proof.
  induction l as [|[a'|b]] ; cbn in * ; try easy.
  all: rewrite IHl.
  - enough ((inl a' = inl a) <-> (a' = a)) as -> by reflexivity.
    intuition congruence.
  - split ; try easy.
    intros [|] ; [congruence|easy].
Qed.  

Instance Proper_left {A B} : Proper (list_ext (A + B) ==> list_ext A) left_list.
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros * H ?.
  now rewrite -left_in H left_in.
Qed.

Definition left_finset {A B} (X : finset (A + B)) : finset A :=
  quot_map left_list X.

Lemma left_finsetP {A B} (X : finset (A + B)) (a : A) :
  a ∈ left_finset X <-> (inl a) ∈ X.
Proof.
  pattern X ; apply quot_ind ; intros l.
  now rewrite /left_finset quot_map_eq !finsetP left_in.
Qed.

Fixpoint right_list {A B} (l : list (A + B)) : list B :=
  match l with
  | nil => nil
  | inl _ :: l' => right_list l'
  | inr b :: l' => b :: right_list l'
  end.

Lemma right_in {A B} (l : list (A + B)) (b : B) : In (inr b) l <-> In b (right_list l).
Proof.
  induction l as [|[a|b']] ; cbn in * ; try easy.
  all: rewrite IHl.
  - split ; try easy.
    intros [|] ; [congruence|easy].
  - enough ((inr b' = inr b) <-> (b' = b)) as -> by reflexivity.
    intuition congruence.
Qed.  

Instance Proper_right {A B} : Proper (list_ext (A + B) ==> list_ext B) right_list.
Proof.
  rewrite /Proper /respectful /list_ext /=.
  intros * H ?.
  now rewrite -right_in H right_in.
Qed.

Definition right_finset {A B} (X : finset (A + B)) : finset B :=
  quot_map right_list X.

Lemma right_finsetP {A B} (X : finset (A + B)) (b : B) :
  b ∈ right_finset X <-> (inr b) ∈ X.
Proof.
  pattern X ; apply quot_ind ; intros l.
  now rewrite /right_finset quot_map_eq !finsetP right_in.
Qed.

Definition finsum {A B:Type} (P:finset A) (Q:finset B) : finset (A + B) :=
  funion2 (image inl P) (image inr Q).

Lemma finsum_left_elem A B (P:finset A) (Q:finset B) a : 
  inl a ∈ finsum P Q <-> a ∈ P.
Proof.
  rewrite /finsum funion2P !imageP.
  split.
  - intros [[? [? [= ->]]]|[? []]] ; intuition congruence.
  - intros.
    left ; now eexists.
Qed.

Lemma finsum_right_elem A B (P:finset A) (Q:finset B) b :
  inr b ∈ finsum P Q <-> b ∈ Q.
Proof.
  rewrite /finsum funion2P !imageP.
  split.
  - intros [[? []]|[? [? [= ->]]]] ; intuition congruence.
  - intros.
    right ; now eexists.
Qed.

Lemma left_right_finset_finsum A B (X : finset (A + B)):
  X = finsum (left_finset X) (right_finset X).
Proof.
  apply set_ext.
  intros [|].
  all: by rewrite ?finsum_right_elem ?finsum_left_elem ?left_finsetP ?right_finsetP.
Qed.

(** Finsets of sets with decidable equality have decidable membership *)

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

Instance finset_in_dec (A:EqTy) (X : finset A) (x : A) : Decision (x ∈ X).
Proof.
  apply quot_rect_dec ; clear.
  intros X.
  rewrite /Decision /member /=.
  destruct (decide (In x X)) ; [left|right].
  all: now rewrite ffinsetP.
Qed.

(**  We can take the subset of a finite set if the
     predicate we wish to use to take the subset is decidable.
  *)

Section finsubset.
  Context {A:Type} (P : A -> Prop) {Hdec : forall x, Decision (P x)}.

  Fixpoint filter (l:list A) : list A :=
    match l with
    | nil => nil 
    | x::xs => if (Hdec x) then x :: (filter xs) else filter xs
    end.

  Lemma filterP (l : list A) x : In x (filter l) <-> In x l /\ P x.
  Proof.
    induction l ; cbn -[member].
    1: now intuition auto.
    destruct (Hdec a).
    - cbn ; intuition (subst ; intuition auto).
    - intuition (subst ; intuition auto).
  Qed.

  Lemma filter_length l : length (filter l) <= length l.
  Proof.
    induction l as [|a]; cbn.
    1: reflexivity.
    destruct ((Hdec a)) ; cbn ; lia.
  Qed.

  Lemma filter_length_lt l : (exists x, In x l /\ ~ P x) -> length (filter l) < length l.
  Proof.
    intros [x [Hin HP]].
    induction l ; cbn in *.
    1: intuition.
    destruct Hin as [<-|Hin].
    all: destruct (Hdec a) ; cbn ; try solve [intuition].
    - pose proof (filter_length l) ; lia.
    - specialize (IHl Hin).
      lia.
  Qed.

  Instance filter_Proper : Proper (list_ext A ==> list_ext A) filter.
  Proof.
    intros ?? e ?.
    now rewrite !filterP e.
  Qed.

  Definition finsubset : finset A -> finset A := quot_map filter.

  Lemma finsubsetP (X : finset A) x : x ∈ (finsubset X) <-> x ∈ X /\ P x.
  Proof.
    pattern X.
    apply quot_ind.
    intros.
    now rewrite /finsubset quot_map_eq !finsetP filterP.
  Qed.

End finsubset.

Section FinEqDec.
  Context {A : EqTy}.

  (**  We can take the intersection of finite sets if the elements
      have decidable equality.
    *)

  Definition fin_intersect (X Y : finset A) : finset A := finsubset (fun x => x ∈ X) Y.

  Lemma fin_intersect_elem X Y x :
    x ∈ fin_intersect X Y <-> (x ∈ X /\ x ∈ Y).
  Proof.
    rewrite /fin_intersect finsubsetP.
    intuition.
  Qed.

(*
Definition fin_finsetPtersect 
  A Hdec (l:finset (finset A)) (Z:finset A) : finset A :=
  List.fold_right (fin_intersect A Hdec) Z l.

Lemma fin_finsetPtersect_elem : forall A Hdec l Z x,
  x ∈ fin_finsetPtersect A Hdec l Z <-> (x ∈ Z /\ forall X, X ∈ l -> x ∈ X).
Proof.
  induction l; simpl; intros.
  - intuition.
    destruct H0 as [?[??]]. elim H0.
  - split; intros.
    + apply fin_intersect_elem in H.
      destruct H.
      apply IHl in H0.
      intuition.
      destruct H0 as [q [??]].
      destruct H0.
      * subst q.
        rewrite H3; auto.
      * apply H2.
        exists q; split; simpl; auto.
    + apply fin_intersect_elem.
      split.
      * destruct H.
        apply H0.
        exists a; split; simpl; auto.
      * destruct H.
        apply IHl. split; auto.
        intros. apply H0.
        destruct H1 as [q [??]].
        exists q; split; simpl; auto.
Qed.
*)

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
Fixpoint fpow_list {A:Type} (l:list A) : finset (finset A) :=
  match l with
  | nil => fsingle fempty
  | x :: xs =>
       let pow := fpow_list xs in
          funion2 pow (fimage (funion2 (fsingle x)) pow)
  end.

Lemma member_fcons A (a : A) M x :
  x ∈ (finlist (a :: M)) <-> x = a \/ x ∈ finlist M.
Proof.
  rewrite !finsetP /=.
  intuition.
Qed.

Lemma fpow_list_sound {A} (M : list A) (X:finset A) :
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

Lemma fpow_list_complete (A : EqTy) (M : list A) (X:finset A) :
  X ⊆ (to_quot M :> finset A) -> X ∈ fpow_list M.
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
      1: now apply IHM => x /fremoveP [] /hX /member_fcons [|] //.
      ext.
      rewrite fconsP funion2P singleP.
      now intuition.
    + left.
      apply IHM => ? /dup [] /hX /member_fcons [->|] //.
Qed.

Instance fpow_Proper {A : EqTy} : Proper (list_ext A ==> eq) fpow_list.
Proof.
  intros ?? ?.
  ext.
  split => /fpow_list_sound.
  all: rewrite /finlist ; erewrite quot_ext ; [|solve [easy|now symmetry]].
  all: apply fpow_list_complete.
Qed.

Definition fpow {A : EqTy} : finset A -> finset (finset A) :=
  quot_rec fpow_list.

Lemma fpowP {A : EqTy} (X Y : finset A) : Y ∈ fpow X <-> Y ⊆ X.
Proof.
  pattern X.
  apply quot_ind.
  intros.
  rewrite /fpow quot_rec_eq.
  split.
  - apply fpow_list_sound.
  - apply fpow_list_complete.
Qed.  

Section FinPredDec.
  Context {A : Type} (P : A -> Prop) `{forall x, Decision (P x)}.

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

  Lemma finset_find_dec (M:finset A) :
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

Lemma finsubset_dec {A : EqTy}
  (P:finset A -> Prop)
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

Lemma finsubset_dec' {A : EqTy}
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

Lemma swelling_lemma {A : EqTy}
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
  pattern z ; apply quot_ind ; clear z.
  intros z.
  revert HP.
  pattern M ; apply quot_ind ; clear M ; intros M HP [hincl hinv].
  
  assert (exists M':list A,
    (forall (q : A), In q M' <-> In q M /\ ~ In q z)) as [M' hM'].
  {
    exists (filter (fun q => ~ In q z) M).
    intros q.
    rewrite filterP.
    now split.
  }
  revert z hincl hinv hM'.

  induction M' as [M' IH] using 
    (well_founded_induction (Wf_nat.well_founded_ltof _ (@length _))).
  intros z hincl hinv hM'.

  destruct (HP (to_quot z)) as [|[q [?[? hinv']]]] ; eauto.

  set (x' := filter (fun x => x <> q) M').
  apply (IH x') with (q::z).
  - red; simpl. unfold x'.
    apply filter_length_lt.
    eexists ; split.
    2: intuition reflexivity.
    apply hM'.
    now rewrite -!finsetP.
  - intros ?.
    rewrite finsetP /=.
    intros [->|] => //.
    now apply hincl, finsetP.
  - by rewrite /fcons quot_map_eq in hinv'.
  - intros q'.
    rewrite /x' filterP /= hM'.
    intuition.
Qed.
