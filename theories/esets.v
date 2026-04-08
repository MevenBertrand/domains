(** * domains.esets: the set theory of enumerable sets *)
From Stdlib Require Import Arith Arith.Cantor ssreflect ssrfun List
  Relations Classes.RelationClasses Classes.Morphisms Lia.
From HB Require Import structures.

Require Import utils.all nat_isos categories.all preord sets finsets.

(** ** Here we define the theory of "enumerable" sets.  Concretely,
       enumerable sets of [A] are represented by the extensional quotient
       of functions [nat -> option A].

       The singleton set is given by the constant function.  The image function
       is defined in the straightforward way as a composition of functions.
       Union is defined by using the isomorphism between [nat] and [N×N] defined
       in pairing.
  *)

Definition fun_member {A} (a : A) (X: nat -> option A) :=
  exists n, X n = Some a.

Definition funset_ext A : relation (nat -> option A) := fun X X' =>
  forall a, fun_member a X <-> fun_member a X'.

Instance funset_equiv {A} : Equivalence (funset_ext A).
Proof.
  split ; red ; unfold funset_ext in *.
  - easy.
  - intros * H **.
    now rewrite H.
  - intros * H H' **.
    now rewrite H H'.
Qed.

Definition eeset (A : PreOrder) : Type := quot (funset_ext A).
Definition eefun {A : PreOrder} (X : nat -> option A) : eeset A := to_quot X.

Instance Proper_fun_member {A : PreOrder} (a : A) : Proper (funset_ext A ==> eq) (fun_member a).
Proof.
  cbv -[iff fun_member].
  intros.
  now ext.
Qed.

Definition emember {A : PreOrder} (a : A) : (eeset A) -> Prop := quot_rec (fun_member a).

Lemma eesetP {A : PreOrder} (a : A) (X : nat -> option A) :
  emember a (eefun X) <-> exists n, (X n) = Some a.
Proof.
  by rewrite /member /= /emember quot_rec_eq /fun_member.
Qed.

Lemma eset_ext A (X X' : eeset A) :
  (forall a, emember a X <-> emember a X') ->
  X = X'.
Proof.
  induction X using quot_ind.
  induction X' using quot_ind.
  intros.
  apply quot_ext.
  rewrite /funset_ext /fun_member.
  intros.
  now rewrite -!eesetP.
Qed.

Definition eset : PreOrder -> Poset :=
  promote_set eeset (@emember) eset_ext.

HB.instance Definition _ : IsBaseSetTheory.axioms_ eset :=
  SetIncl eset (@emember) eset_ext.

Definition efun {A : PreOrder} (f : nat -> option A) : eset A := eefun f.

Lemma esetP {A : PreOrder} (a : A) (X : nat -> option A) :
  a ∈ (efun X) <-> exists n, (X n) = Some a.
Proof.
  apply eesetP.
Qed.

Definition esingle {A : PreOrder} (a : A) :  eset A := efun (fun n => Some a).

Lemma esingleP {A : PreOrder} (a a' : A) : emember a (esingle a') <-> a = a'.
Proof.
  rewrite /emember /esingle quot_rec_eq /fun_member.
  split.
  - now intros [_ [= ->]].
  - now intros -> ; exists (0%nat).
Qed.

(* Lemma countable_single A (a : A) : countable (single a).
Proof.
  exists (esingle a).
  intros.
  by rewrite esingleP singleP.
Qed. *)

Definition emap {A B} (f : A -> B) : (nat -> option A) -> nat -> option B :=
  (fun X n => option_map f (X n)).

Instance Proper_emap {A B} f : Proper (funset_ext A ==> funset_ext B) (emap f).
Proof.
  rewrite /Proper /funset_ext /fun_member /emap.
  eintros x y H b.
  split.
  all: intros [n [? [e ->]]%option_map_some].
  - edestruct H as [[n' e'] _].
    1: eauto.
    exists n'; by rewrite e'.
  - edestruct H as [_ [n' e']].
    1: eauto.
    exists n'; by rewrite e'.
Qed.

Definition eimage {A B : PreOrder} (f : A -> B) (X : eset A) : eset B :=
  quot_map (emap f) X.

Lemma emapP {A B : PreOrder} (f : A -> B) (X : nat -> option A) (y : B) :
  fun_member y (emap f X) <-> exists x, (fun_member x X) /\ y = f x.
Proof.
  split.
  - intros [n [? [e ->]]%option_map_some].
    eexists ; split ; [..|easy].
    rewrite /fun_member.
    now eexists.
  - intros [? [[n e] ->]].
    exists n.
    now rewrite /emap e //.
Qed.

Lemma eimageP {A B : PreOrder} (f : A -> B) (X : eset A) (y : B) :
  y ∈ (eimage f X) <-> exists x, (x ∈ X) /\ y = f x.
Proof.
  induction X using quot_ind.
  rewrite /eimage quot_map_eq /member /= /emember !quot_rec_eq emapP.
  split.
  all: move => [x []].
  all: rewrite ?quot_rec_eq.
  all: exists x.
  all: rewrite ?quot_rec_eq ; now subst.
Qed.

Definition fun_union {A} (XS : nat -> option (nat -> option A)) : nat -> option A :=
  fun n => let (p,q) := Cantor.of_nat n in
      match XS p with
      | None => None
      | Some P => P q
      end.

Lemma fun_unionP {A} (XS : nat -> option (nat -> option A)) a :
  fun_member a (fun_union XS) <->
    exists (X : nat -> option A), fun_member X XS /\ fun_member a X.
Proof.
  split.
  - intros [n Hn].
    rewrite /fun_union in Hn.
    destruct (Cantor.of_nat n) as [p q] eqn:en.
    destruct (XS p) as [X|] eqn:eX.
    2: now congruence.
    exists X.
    rewrite /fun_member.
    split ; eexists ; eassumption.
  - intros [X [[p Hp] [q Hq]]].
    rewrite /fun_member in Hp, Hq |- *.
    exists (Cantor.to_nat (p,q)).
    now rewrite /fun_union cancel_of_to Hp.
Qed.

Instance Proper_fun_union {A} :
  Proper (pointwise_relation nat (option_rel (funset_ext A)) ==> funset_ext A) fun_union.
Proof.
  intros f f' r a.
  rewrite /pointwise_relation /funset_ext /= in r. 
  rewrite !fun_unionP.
  split.
  all: intros (X&[n e]&Hin).
  all: specialize (r n) => /=.
  all: rewrite e in r => /=.
  1: destruct (f' n) as [X'|] eqn:? ; cbn in * ; [|easy].
  2: destruct (f n) as [X'|] eqn:? ; cbn in * ; [|easy].
  all: exists X' ; split ; [|now apply r].
  all: now eexists.
Qed.

Definition pull_quot_option {B : Type} {R : relation B} `{! Equivalence R} :
  option (quot R) -> quot (option_rel R) :=
  fun o =>
  match o with
  | Some v => quot_map Some v
  | None => to_quot None
  end.

Lemma pull_quot_option_some  {B : Type} {R : relation B} `{! Equivalence R}
  (b : B) (x : option (quot R)) :
  pull_quot_option x = to_quot (Some b) <-> x = Some (to_quot b).
Proof.
  split.
  - destruct x as [q|] ; cbn.
    + induction q as [b'] using quot_ind.
      rewrite quot_map_eq.
      intros e%quot_eq.
      cbn in e.
      now ext.
    + intros e%quot_eq.
      now cbn in e.
  - intros -> => /=.
    now rewrite quot_map_eq.
Qed.

Definition fun_eset_union {A} (XS : nat -> option (eset A)) : eset A :=
  quot_map fun_union (pull_quot_nat (pull_quot_option \o XS)).

Lemma fun_eset_unionP {A} (XS : nat -> option (eset A)) a :
  emember a (fun_eset_union XS) <->
    exists (X : eset A), fun_member X XS /\ emember a X.
Proof.
  rewrite /fun_eset_union.
  set (XS' := (pull_quot_nat (pull_quot_option \o XS))).
  assert (forall n, eval_quot XS' n = pull_quot_option (XS n)) as eXS'
    by rewrite /XS' pull_quot_nat_eq //.
  clearbody XS'.
  induction XS' as [XS'] using quot_ind.
  rewrite !quot_map_eq /emember quot_rec_eq fun_unionP.
  split.
  - intros (X&(n&HXin)&HinX).
    exists (to_quot X).
    rewrite quot_rec_eq.
    split ; [|easy].
    exists n.
    apply pull_quot_option_some.
    rewrite -eXS' eval_quot_eq /= HXin //.
  - intros (X&(n&HXin)&HinX).
    induction X as [X] using quot_ind.
    rewrite quot_rec_eq in HinX.
    apply pull_quot_option_some in HXin.
    rewrite -eXS' eval_quot_eq /= in HXin.
    apply quot_eq in HXin.
    destruct (XS' n) as [X'|] eqn:e => //.
    cbn in HXin.
    exists X'.
    split ; [now eexists|].
    now apply HXin.
Qed.

Instance Proper_fun_eset_union {A : PreOrder} : Proper (funset_ext (eset A) ==> eq) fun_eset_union.
Proof.
  intros ?? e.
  apply eset_ext.
  intros a.
  rewrite !fun_eset_unionP.
  unfold funset_ext in e.
  now setoid_rewrite e.
Qed.

Definition eunion {A : PreOrder} : eset (eset A) -> eset A := quot_rec fun_eset_union.

Lemma eunionP {A : PreOrder} XS (a : A) :
  emember a (eunion XS) <-> exists X, emember X XS /\ emember a X.
Proof.
  induction XS using quot_ind.
  rewrite /eunion !quot_rec_eq fun_eset_unionP.
  split.
  all: intros (X&[HX]) ; exists X ; split ; [|easy].
  2: red.
  all: apply (esetP (A := eset A)) ; eassumption.
Qed.

HB.instance Definition _ :=
  IsPreSetTheory.Build eset (@esingle) (@eimage) (@eunion).

HB.instance Definition _ :=
  IsSetTheory.Build eset (@esingleP) (@eimageP) (@eunionP).


(** Countable indefinite description was present in the original dev, but is not
  valid: it does not respect the setoid structure. It looks like it is not used
  anywhere. *)

(** ** Additional operations on enumerable sets. *)

(** The empty set is easily definable.  *)
Definition eempty {A:PreOrder} : eset A := efun (fun n => None).

Lemma eemptyP (A : PreOrder) (x : A) : x ∈ eempty <-> False.
Proof.
  rewrite /eempty esetP.
  split ; [|easy].
  intros [] ; congruence.
Qed.

(** Every list generates an enumerable set. *)
Definition elist {A:PreOrder} (l:list A) : eset A := efun (fun n => nth_error l n).

Lemma elistP {A:PreOrder} (l : list A) (x : A) : x ∈ (elist l) <-> In x l.
Proof.
  rewrite /elist esetP In_iff_nth_error.
  reflexivity.
Qed.

(** Thus every finite set gives an equivalent enumerable set *)
Instance Proper_elist {A:PreOrder} : Proper (list_ext A ==> eq) elist.
Proof.
  intros ?? e.
  apply set_ext ; intros.
  now rewrite !elistP e.
Qed.

Definition fset_eset {A} (f : finset A) : eset A := quot_rec elist f.

Lemma fset_esetP {A} (f : finset A) x : x ∈ (fset_eset f) <-> x ∈ f.
Proof.
  induction f using quot_ind.
  now rewrite /fset_eset quot_rec_eq elistP finsetP.
Qed.

(**  The intersection of enumerable sets can be defined if we have a decidable equality on the
     elements.
  *)

Definition fun_inter2 {A:EqTy} (P Q : nat -> option A) : nat -> option A :=
    fun n => let (p,q) := Cantor.of_nat n in 
       match P p, Q q with
       | Some x, Some y => if eqdec x y then Some x else None
       | _, _ => None
       end.

Lemma fun_inter2P {A:EqTy} (P Q : nat -> option A) x :
  fun_member x (fun_inter2 P Q) <-> (fun_member x P /\ fun_member x Q).
Proof.
  split.
  - intros [n Hn].
    rewrite /fun_inter2 in Hn.
    rewrite /fun_member.
    destruct (of_nat n) as (p,q) ; clear n.
    destruct (P p) as [a|] eqn:eP ; [|congruence].
    destruct (Q q) as [a'|] eqn:eQ ; [|congruence].
    destruct (eqdec a a') eqn:ea ; [subst|congruence].
    split ; eexists.
    all: now rewrite <- Hn.
  - intros [[p Hp] [q Hq]].
    exists (Cantor.to_nat (p,q)).
    now rewrite /fun_inter2 cancel_of_to Hp Hq eqdec_refl.
Qed.

Instance Proper_inter2 {A:DecPreOrd} : Proper (funset_ext A ==> funset_ext A ==> funset_ext A) fun_inter2.
Proof.
  intros ?? HP ?? HQ a.
  rewrite fun_inter2P HP HQ -fun_inter2P.
  reflexivity.
Qed.

Definition einter2 {A:DecPreOrd} : eset A -> eset A -> eset A := quot_map2 fun_inter2.

Lemma einter2P {A : DecPreOrd} (P Q : eset A) x : x ∈ (einter2 P Q) <-> (x ∈ P) /\ (x ∈ Q).
Proof.
  induction P using quot_ind.
  induction Q using quot_ind.
  rewrite /einter2 quot_map2_eq !esetP.
  setoid_rewrite fun_inter2P.
  rewrite /fun_member.
  reflexivity.
Qed.

Fixpoint list_inter {A:DecPreOrd} (X : eset A) (XS : list (eset A)) : eset A :=
  match XS with
  | nil => X
  | X' :: XS => einter2 X' (list_inter X XS)
  end.

Lemma list_interP {A:DecPreOrd} (X : eset A) (XS : list (eset A)) x :
  x ∈ (list_inter X XS) <-> (x ∈ X /\ (forall X', In X' XS -> x ∈ X')).
Proof.
  induction XS ; cbn.
  1: now intuition.
  rewrite einter2P IHXS.
  intuition (subst ; eauto).
Qed.

Instance Proper_list_inter {A:DecPreOrd} X : Proper (list_ext (eset A) ==> eq) (list_inter X).
Proof.
  intros ?? e.
  ext.
  rewrite !list_interP.
  red in e.
  now setoid_rewrite e.
Qed.

Definition finter {A:DecPreOrd} (X : eset A) (XS : finset (eset A)) : eset A :=
  quot_rec (list_inter X) XS.

Lemma finterP {A:DecPreOrd} (X : eset A) (XS : finset (eset A)) x :
  x ∈ (finter X XS) <-> (x ∈ X /\ (forall X', X' ∈ XS -> x ∈ X')).
Proof.
  induction XS as [XS] using quot_ind.
  rewrite /finter quot_rec_eq list_interP.
  setoid_rewrite finsetP.
  reflexivity.
Qed.

(**  We also have binary unions *)
Definition fun_union2 {A} (P: nat -> option A) (Q : nat -> option A) : nat -> option A :=
  fun n => match (sum_of_nat n) with
  | inl n' => P n'
  | inr n' => Q n'
  end.

Lemma fun_union2P {A} (P Q: nat -> option A) x :
  fun_member x (fun_union2 P Q) <-> (fun_member x P \/ fun_member x Q).
Proof.
  rewrite /fun_member.
  split.
  - intros [n Hn].
    rewrite /fun_union2 in Hn.
    destruct (sum_of_nat n) eqn:e.
    + left ; eexists ; eassumption.
    + right ; eexists ; eassumption.
  - rewrite /fun_union2.
    intros [[n HP]|[n HQ]].
    1: exists (sum_to_nat (inl n)).
    2: exists (sum_to_nat (inr n)).
    all: now rewrite cancel_of_to_sum.
Qed.

Instance Proper_fun_union2 {A : PreOrder} :
  Proper (funset_ext A ==> funset_ext A ==> funset_ext A) fun_union2.
Proof.
  intros ?? HP ?? HQ ?.
  now rewrite !fun_union2P HP HQ.
Qed.

Definition eunion2 {A}: eset A -> eset A -> eset A :=
  quot_map2 fun_union2.

Lemma eunion2P {A} (P Q : eset A) x : (x ∈ eunion2 P Q) <-> (x ∈ P) \/ (x ∈ Q).
Proof.
  induction P as [f] using quot_ind.
  induction Q as [g] using quot_ind.
  rewrite /eunion2 quot_map2_eq !esetP.
  setoid_rewrite fun_union2P.
  reflexivity.
Qed.

(** The disjoint union of two enumerable sets. *)
Definition esum {A B : PreOrder} (P : eset A) (Q : eset B) : eset (A + B) :=
  eunion2 (image (set := eset) ι₁ P) (image ι₂ Q).

Lemma esum_leftP A B (P:eset A) (Q:eset B) x :
  (inl x) ∈ (esum P Q) <-> x ∈ P.
Proof.
  rewrite /esum eunion2P !imageP.
  split.
  - now intros [[? [? [= ->]]]|[? [? [=]]]].
  - intros.
    left ; eexists ; eauto.
Qed.
    
Lemma esum_rightP A B (P:eset A) (Q:eset B) x :
  (inr x) ∈ (esum P Q) <-> x ∈ Q.
Proof.
  rewrite /esum eunion2P !imageP.
  split.
  - now intros [[? [? [=]]]|[? [? [= ->]]]].
  - intros.
    right ; eexists ; eauto.
Qed.

(** The binary product of enumerable sets *)
Definition fun_prod {A B} (P:nat -> option A) (Q:nat -> option B) :
  nat -> option (A * B) :=
  fun n => let (p,q) := (Cantor.of_nat n) in
    match P p, Q q with
    | Some x, Some y => Some (x,y)
    | _, _ => None
    end.

Lemma fun_prodP {A B} (P:nat -> option A) (Q:nat -> option B) x:
  fun_member x (fun_prod P Q) <-> fun_member (fst x) P /\ fun_member (snd x) Q.
Proof.
  destruct x.
  rewrite /fun_member.
  split.
  - rewrite /fun_prod.
    intros [n e].
    destruct (Cantor.of_nat n) as [p q], (P p) eqn:eP, (Q q) eqn:eQ ; try solve [congruence].
    inversion e ; subst ; clear e.
    now split ; eexists.
  - intros [[p Hp] [q Hq]].
    exists (Cantor.to_nat (p,q)).
    by rewrite /fun_prod cancel_of_to Hp Hq.
Qed.

Instance Proper_fun_prod {A B : PreOrder} :
  Proper (funset_ext A ==> funset_ext B ==> funset_ext (A * B)) fun_prod.
Proof.
  intros ?? HP ?? HQ ?.
  by rewrite !fun_prodP HP HQ.
Qed.

Definition eprod {A B}: eset A -> eset B -> eset (A*B) :=
  quot_map2 fun_prod.

Lemma eprodP {A B} (P : eset A) (Q : eset B) x : (x ∈ eprod P Q) <-> (fst x ∈ P) /\ (snd x ∈ Q).
Proof.
  induction P as [f] using quot_ind.
  induction Q as [g] using quot_ind.
  rewrite /eprod quot_map2_eq !esetP.
  setoid_rewrite fun_prodP.
  reflexivity.
Qed.

(** *** Filter + map *)

Section FilterMap.
  Context {A B:Type} (f : A -> option B).

  Definition filter_map_fun (g : nat -> option A) : nat -> option B :=
    (option_bind f) \o g.

  Lemma filter_map_funP (g : nat -> option A) b :
    fun_member b (filter_map_fun g) <-> exists a, fun_member a g /\ f a = Some b.
  Proof.
    rewrite /filter_map_fun /fun_member /=.
    split.
    - intros (n&?).
      destruct (g n) eqn:e ; cbn in *.
      2: congruence.
      now eexists.
    - intros (?&[? e]&?).
      eexists.
      now erewrite e. 
  Qed.

  Instance filter_Proper : Proper (funset_ext A ==> funset_ext B) filter_map_fun.
  Proof.
    intros ?? e ?.
    rewrite !filter_map_funP.
    red in e.
    now setoid_rewrite e.
  Qed.

End FilterMap.

Existing Instance filter_Proper.

Definition efilter_map {A B : PreOrder} (f : A -> option B) : eset A -> eset B :=
  quot_map (filter_map_fun f).

Lemma efilter_mapP {A B : PreOrder} (f : A -> option B) (X : eset A) (x : B) :
  x ∈ (efilter_map f X) <->
  exists a, a ∈ X /\ (f a = Some x).
Proof.
  induction X as [X] using quot_ind.
  rewrite -/(efun X) /efilter_map quot_map_eq !esetP.
  setoid_rewrite filter_map_funP.
  setoid_rewrite esetP.
  reflexivity.
Qed.

(** *** Subset **)

(** We can take the subset of a finite set if the
    predicate we wish to use to take the subset is decidable.
  *)

Section ESubset.
  Context {A:PreOrder} (P : A -> Prop) {Hdec : forall x, Decision (P x)}.

  Definition esubset_dec : eset A -> eset A :=
    efilter_map (fun x => if (Hdec x) then (Some x) else None).

  Lemma esubset_decP (X : eset A) x : x ∈ (esubset_dec X) <-> x ∈ X /\ P x.
  Proof.
    rewrite /esubset_dec efilter_mapP.
    setoid_rewrite dec_Some.
    split.
    - intros (?&?&?&?) ; subst ; eauto.
    - intros ; eexists ; intuition eauto.
  Qed.

End ESubset.

(**  The finite subets of an enumerable set are enumerable.
  *)

Fixpoint choose_finset {A : PreOrder} (X:nat -> option A) (n:nat) (z:nat) : finset A :=
  match n with
  | 0 => fempty
  | S n' => let (p,q) := Cantor.of_nat z in
              match X p with
              | None => choose_finset X n' q
              | Some a => fcons a (choose_finset X n' q)
              end
  end.

Lemma choose_finset_sound (A : PreOrder) (X : nat -> option A) n z : choose_finset X n z ⊆ efun X.
Proof.
  induction n in z |- * ; simpl; intros.
  - apply: fempty_incl.
  - destruct (of_nat z) as [p q] eqn: ez.
    destruct (X p) eqn:ep.
    + move => ? /fconsP [<- | /IHn] //.
      rewrite esetP.
      now eexists.
    + apply IHn.
Qed.

Lemma choose_finset_complete (A : PreOrder) (X : nat -> option A) (Y:finset A) :
  Y ⊆ (efun X) -> exists n, exists z, choose_finset X n z = Y.
Proof.
  induction Y as [|a Y IHY] using finset_ind.
  - exists 0, 0.
    reflexivity.
  - intros.
    edestruct IHY as [n [z HX]].
    + intros x Hx.
      now apply H, fconsP.
    + subst.
      assert (fun_member a X) as [p Hp]
        by now apply esetP, H, fconsP.
      exists (S n), (Cantor.to_nat (p,z)).
      cbn -[to_nat].
      now rewrite cancel_of_to Hp.
Qed.

Definition fun_fpow {A : PreOrder} (X:nat -> option A) : nat -> option (finset A) :=
  fun n => let (p,q) := (Cantor.of_nat n) in
    Some (choose_finset X p q).

Lemma fun_fpowP (A : PreOrder) (X:nat -> option A) (Q: finset A) :
  Q ⊆ (efun X) <-> Q ∈ (efun (A := finset A) (fun_fpow X)).
Proof.
  split.
  - move => /choose_finset_complete [n [z H]].
    rewrite /fun_fpow esetP /fun_member.
    exists (Cantor.to_nat (n,z)).
    now rewrite cancel_of_to H.
  - rewrite esetP /fun_fpow /fun_member => [[n ]].
    destruct (of_nat n) as [p q] => [= <-].
    now apply choose_finset_sound.
Qed.

Instance Proper_fun_fpow {A : PreOrder} : Proper (funset_ext A ==> funset_ext (finset A)) fun_fpow.
Proof.
  intros f g H X.
  rewrite /fun_member -!(esetP (A := finset A)) -!fun_fpowP.
  split.
  all: now move => H' ? /H' /esetP /H /esetP.
Qed.

Definition fpow {A} : eset A -> eset (finset A) := quot_map fun_fpow.

Lemma fpowP {A} (X : eset A) (Q : finset A) : Q ⊆ X <-> Q ∈ fpow X.
Proof.
  induction X using quot_ind.
  rewrite fun_fpowP /fpow quot_map_eq //.
Qed.

(*
Definition ne_finsubsets A (X:eset A) : eset (finset A) :=
  fun n => 
    let (p,q) := unpairing n in
    let l := choose_finset A X (nat.to_nat p) q in
    match l with
    | nil => None
    | _ => Some l
    end.

Lemma ne_finsubsets_complete : forall A (X:eset A) (Q:finset A),
  ((exists x, x ∈ Q) /\ Q ⊆ X) <-> Q ∈ ne_finsubsets A X.
Proof.
  intros. split; intros.
  - destruct H.
    apply choose_finset_in in H0.
    destruct H0 as [n [z ?]].
    exists (pairing (nat.of_nat n,z)).
    unfold ne_finsubsets.
    rewrite unpairing_pairing.
    rewrite Nat2N.id.
    case_eq (choose_finset A X n z).
    + intros.
      rewrite H1 in H0.
      destruct H0.
      destruct H as [x ?].
      destruct (H2 x); auto.
      destruct H3. elim H3.
    + intros.
      rewrite <- H1.
      auto.

  - destruct H as [z ?].
    unfold ne_finsubsets in H.
    case_eq (unpairing z); intros.
    rewrite H0 in H.
    case_eq (choose_finset A X (nat.to_nat n) n0); intros.
    + rewrite H1 in H. elim H.
    + rewrite H1 in H.
      split.
      * exists c.
        rewrite H.
        exists c; split; simpl; auto.
      * rewrite H. rewrite <- H1.
        apply choose_finset_sub.
Qed.
*)

(** ** Semidecidable predicates *)

(** A predicate is semidecidable if its truth is equal
     to the inhabitedness of an enumerable set.
  *)
Class SemiDec (P:Prop) :=
  { decset : eset unit
  ; decsetP : tt ∈ decset <-> P
  }.

Arguments decset _ {_}.

(**  Decidable predicates are semidecidable.
  *)
#[refine]Instance dec_semidec P `{!Decision P} : SemiDec P :=
  {| decset := (if (decide P) then single tt else eempty) ; decsetP := _ |}.
Proof.
  destruct (decide P).
  all: rewrite ?singleP ?eemptyP ; intuition.
Qed.

#[refine]Instance semidec_true : SemiDec True
  := {| decset := (single tt) ; decsetP := _ |}.
Proof.
  rewrite singleP ; intuition.
Qed.

#[refine]Instance semidec_false : SemiDec False
  := {| decset := eempty ; decsetP := _ |}.
Proof.
  now rewrite eemptyP.
Qed.

#[refine]Instance semidec_disj (P Q:Prop) `{HP : SemiDec P} `{HQ : SemiDec Q}
  : SemiDec (P \/ Q)
  := {| decset := (eunion2 (decset P) (decset Q)) ; decsetP := _|}.
Proof.
  now rewrite eunion2P !decsetP.
Qed.

#[refine]Instance semidec_conj (P Q:Prop) `{HP : SemiDec P} `{HQ : SemiDec Q}
  : SemiDec (P /\ Q)
  := {| decset := (einter2 (decset P) (decset Q)) ; decsetP := _|}.
Proof.
  now rewrite einter2P !decsetP.
Qed.

Program Definition semidec_in {A : DecPreOrd} (X:eset A) (x : A) : SemiDec (x ∈ X) :=
  {| decset := image (const_mon tt) (einter2 X (single x)) ; decsetP := _|}.
Next Obligation.
  rewrite imageP.
  split.
  - intros [? [Hin _]].
    rewrite einter2P singleP in Hin.
    now destruct Hin as [? ->].
  - eexists.
    split ; [|easy].
    now rewrite einter2P singleP.
Qed.

Hint Extern 100 (SemiDec (_ ∈ _)) => (apply: semidec_in) : typeclass_instances. 

#[refine]Instance semidec_all {A : DecPreOrd} (X:finset A) (P : A -> Prop) `{HP : forall a, SemiDec (P a)} :
  SemiDec (∀ a ∈ X, P a) :=
  {|
    decset :=
      image (const_mon tt) (finter (esingle tt)
        (fimage (fun a => decset (P a)) X)) ;
    decsetP := _
  |}.
Proof.
  rewrite imageP.
  setoid_rewrite finterP.
  setoid_rewrite fimageP.
  split.
  - intros ([]&[_ H]&_) a Hin.
    apply decsetP, H.
    now eexists.
  - intros.
    exists tt.
    repeat split.
    1: now rewrite singleP.
    intros ? (?&[]) ; subst.
    now apply decsetP.
Qed.

#[refine]Instance semidec_ex {A : DecPreOrd} (X:eset A) (P : A -> Prop) `{HP : forall a, SemiDec (P a)} :
  SemiDec (∃ a ∈ X, P a) :=
  {|
    decset :=
      image (const_mon tt) (union (eimage (fun a => decset (P a)) X)) ;
    decsetP := _
  |}.
Proof.
  rewrite imageP.
  setoid_rewrite unionP.
  setoid_rewrite eimageP.
  split.
  - intros ([]&(?&(?&?&?)&?)&_) ; subst.
    eexists ; split ; tea.
    now apply decsetP.
  - intros (?&[]).
    exists tt.
    repeat split.
    eexists ; split ; eauto.
    now apply decsetP.
Qed.

(** It is enough to have a *semi-decidable* proposition
  for the corresponding subset to be enumerable. *)

Definition esubset {A : DecPreOrd} (P:A -> Prop) 
  `{! forall a, SemiDec (P a)} (X:eset A) : eset A :=
    ∪ (eimage (fun (a : A) => (image (const_mon a) (decset (P a)))) X).

Lemma esubsetP {A : DecPreOrd} (P:A -> Prop)  `{! forall a, SemiDec (P a)} (X:eset A) (x : A) :
  x ∈ esubset P X <-> x ∈ X /\ P x.
Proof.
  rewrite /esubset unionP.
  setoid_rewrite eimageP.
  split.
  - intros (?&(?&?&?)&Him) ; subst.
    rewrite imageP /= in Him.
    destruct Him as ([]&?&<-).
    split ; [easy|].
    now apply decsetP.
  - intros [].
    exists (single x).
    split.
    2: now rewrite singleP.
    exists x ; split ; [easy|].
    ext.
    rewrite singleP imageP.
    split.
    + intros ->.
      exists tt.
      now rewrite decsetP.
    + now intros ([]&?&?).
Qed.

(** ** Enumerable relations *)

Definition erel (A B:PreOrder) := eset (A * B).

Definition erel_image {A : DecPreOrd} {B : PreOrder} (R : erel A B) (a : A) : eset B :=
  image π₂ (esubset_dec (fun x => a = (fst x)) R).

Lemma erel_imageP {A : DecPreOrd} {B : PreOrder} (R : erel A B) (x : A) (y : B) :
  y ∈ erel_image R x <-> (x,y) ∈ R.
Proof.
  rewrite /erel_image imageP.
  setoid_rewrite esubset_decP.
  split.
  - intros ([]&?) ; intuition (subst ; eauto).
  - now eexists.
Qed.

Definition erel_inv_image {A : PreOrder} {B : DecPreOrd} (R : erel A B) (b : B) : eset A :=
  image π₁ (esubset_dec (fun (x : A * B) => b = (snd x)) R).

Lemma erel_inv_imageP {A : PreOrder} {B : DecPreOrd} (R : erel A B) (x : A) (y : B) :
  x ∈ erel_inv_image R y <-> (x,y) ∈ R.
Proof.
  rewrite /erel_inv_image imageP.
  setoid_rewrite esubset_decP.
  split.
  - intros ([]&?) ; intuition (subst ; eauto).
  - now eexists.
Qed.