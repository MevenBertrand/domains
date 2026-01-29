(** * domains.esets: the set theory of enumerable sets *)
From Stdlib Require Import Arith Arith.Cantor ssreflect ssrfun List
  Relations Classes.RelationClasses Classes.Morphisms Lia.
From HB Require Import structures.

Require Import utils.all nat_isos categories.all preord sets finsets.

(**  * Here we define the theory of "enumerable" sets.  Concretely,
       enumerable sets of [A] are represented by the extensional quotient
       of functions [nat -> option A].

       The singleton set is given by the constant function.  The image function
       is defined in the straightforward way as a composition of functions.
       Union is defined by using the isomorphism between [nat] and [N×N] defined
       in pairing.
  *)

(* TODO move *)

Lemma option_map_some A B (f : A -> B) (a : option A) (b : B) :
  (option_map f a = Some b) ->
  exists a', a = Some a' /\ b = f a'.
Proof.
 destruct a ; cbn.
 2: congruence.
 intros [= <-].
 now eexists.
Qed.

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


Definition eset (A : Type) : Type := quot (funset_ext A).
Definition efun {A} (X : nat -> option A) : eset A := to_quot X.

Instance Proper_fun_member {A} (a : A) : Proper (funset_ext A ==> eq) (fun_member a).
Proof.
  cbv -[iff fun_member].
  intros.
  now ext.
Qed.

Definition emember {A} (a : A) : (eset A) -> Prop := quot_rec (fun_member a).

Lemma eesetP {A} (a : A) (X : nat -> option A) :
  emember a (efun X) <-> exists n, (X n) = Some a.
Proof.
  by rewrite /emember quot_rec_eq /fun_member.
Qed.

Lemma eset_ext {A} (X X' : eset A) :
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

Definition esingle {A} (a : A) :  eset A := efun (fun n => Some a).

Lemma esingleP {A} (a a' : A) : emember a (esingle a') <-> a = a'.
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

Definition eimage {A B} (f : A -> B) (X : eset A) : eset B :=
  quot_map (emap f) X.

Lemma emapP {A B : Type} (f : A -> B) (X : nat -> option A) (y : B) :
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

Lemma eimageP {A B : Type} (f : A -> B) (X : eset A) (y : B) :
  emember y (eimage f X) <-> exists x, (emember x X) /\ y = f x.
Proof.
  induction X using quot_ind.
  rewrite /eimage quot_map_eq /emember !quot_rec_eq emapP.
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

Instance Proper_fun_eset_union {A} : Proper (funset_ext (eset A) ==> eq) fun_eset_union.
Proof.
  intros ?? e.
  apply eset_ext.
  intros a.
  rewrite !fun_eset_unionP.
  split.
  all: intros (X&[]) ; exists X ; split ; try easy ; now apply e.
Qed.

Definition eunion {A} : eset (eset A) -> eset A := quot_rec fun_eset_union.

Lemma eunionP {A} XS a :
  emember a (eunion XS) <-> exists (X : eset A), emember X XS /\ emember a X.
Proof.
  induction XS using quot_ind.
  rewrite /eunion !quot_rec_eq fun_eset_unionP.
  split.
  all: intros (X&[HX]) ; exists X ; split ; [|easy].
  all: apply eesetP ; eassumption.
Qed.

HB.instance Definition _ :=
  IsPreSetTheory.Build eset (@emember) (@esingle) (@eimage) (@eunion).

HB.instance Definition _ :=
  IsSetTheory.Build eset
    (@eset_ext) (@esingleP) (@eimageP) (@eunionP).

Lemma esetP {A} (X : nat -> option A) (x : A) : x ∈ (efun X) <-> fun_member x X.
Proof.
  apply eesetP.
Qed.

(** Countable indefinite description was present in the original dev, but is not
  valid: it does not respect the setoid structure. It looks like it is not used
  anywhere. *)

(** ** Additional operations on enumerable sets. *)

(** The empty set is easily definable.  *)
Definition eempty {A:Type} : eset A := efun (fun n => None).

Lemma eemptyP (A : Type) (x : A) : x ∈ eempty <-> False.
Proof.
  rewrite /eempty esetP.
  split ; [|easy].
  intros [] ; congruence.
Qed.

(** Every list (qua finite set) generates an enumerable set. *)
Definition elist {A:Type} (l:list A) : eset A := efun (fun n => nth_error l n).

Lemma elistP {A} (l : list A) (x : A) : x ∈ (elist l) <-> In x l.
Proof.
  rewrite /elist esetP In_iff_nth_error.
  reflexivity.
Qed.

(**  The intersection of enumerable sets can be defined if we have a decidable equality on the
     elements.
  *)

Definition fun_intersection {A:EqTy} (P Q : nat -> option A) : nat -> option A :=
    fun n => let (p,q) := Cantor.of_nat n in 
       match P p, Q q with
       | Some x, Some y => if eqdec x y then Some x else None
       | _, _ => None
       end.

Lemma fun_intersectionP {A:EqTy} (P Q : nat -> option A) x :
  fun_member x (fun_intersection P Q) <-> (fun_member x P /\ fun_member x Q).
Proof.
  split.
  - intros [n Hn].
    rewrite /fun_intersection in Hn.
    rewrite /fun_member.
    destruct (of_nat n) as (p,q) ; clear n.
    destruct (P p) as [a|] eqn:eP ; [|congruence].
    destruct (Q q) as [a'|] eqn:eQ ; [|congruence].
    destruct (eqdec a a') eqn:ea ; [subst|congruence].
    split ; eexists.
    all: now rewrite <- Hn.
  - intros [[p Hp] [q Hq]].
    exists (Cantor.to_nat (p,q)).
    now rewrite /fun_intersection cancel_of_to Hp Hq eqdec_refl.
Qed.

Instance Proper_intersection {A:EqTy} : Proper (funset_ext A ==> funset_ext A ==> funset_ext A) fun_intersection.
Proof.
  intros ?? HP ?? HQ a.
  now rewrite fun_intersectionP HP HQ -fun_intersectionP.
Qed.

Definition eintersection {A:EqTy} : eset A -> eset A -> eset A := quot_map2 fun_intersection.

Lemma eintersectionP {A : EqTy} (P Q : eset A) x : x ∈ (eintersection P Q) <-> (x ∈ P) /\ (x ∈ Q).
Proof.
  induction P using quot_ind.
  induction Q using quot_ind.
  now rewrite /eintersection quot_map2_eq !esetP fun_intersectionP.
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

Instance Proper_fun_union2 {A} :
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
  rewrite /eunion2 quot_map2_eq !esetP fun_union2P //.
Qed.

(** The disjoint union of two enumerable sets. *)
Definition esum {A B} (P : eset A) (Q : eset B) : eset (A + B) :=
  eunion2 (image inl P) (image inr Q).

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

Instance Proper_fun_prod {A B} :
  Proper (funset_ext A ==> funset_ext B ==> funset_ext (A * B)) fun_prod.
Proof.
  intros ?? HP ?? HQ ?.
  by rewrite !fun_prodP HP HQ.
Qed.

Definition eprod {A B}: eset A -> eset B -> eset (A*B) :=
  quot_map2 fun_prod.

Lemma eprodP {A} (P Q : eset A) x : (x ∈ eprod P Q) <-> (fst x ∈ P) /\ (snd x ∈ Q).
Proof.
  induction P as [f] using quot_ind.
  induction Q as [g] using quot_ind.
  rewrite /eprod quot_map2_eq !esetP fun_prodP //.
Qed.

(**  The finite subets of an enumerable set are enumerable.
  *)

Fixpoint choose_finset {A} (X:nat -> option A) (n:nat) (z:nat) : finset A :=
  match n with
  | 0 => fempty
  | S n' => let (p,q) := Cantor.of_nat z in
              match X p with
              | None => choose_finset X n' q
              | Some a => fcons a (choose_finset X n' q)
              end
  end.

Lemma choose_finset_sound A (X : nat -> option A) n z : choose_finset X n z ⊆ efun X.
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

Lemma choose_finset_complete A (X : nat -> option A) (Q:finset A) :
  Q ⊆ (efun X) -> exists n, exists z, choose_finset X n z = Q.
Proof.
  induction Q as [l] using quot_ind.
  induction l.
  - exists 0, 0.
    reflexivity.
  - intros.
    edestruct IHl as [n [z HX]].
    + intros x Hx%finsetP.
      now apply H, finsetP ; cbn.
    + assert (fun_member a X) as [p Hp]
        by (now apply esetP, H, finsetP => /=).
      exists (S n), (Cantor.to_nat (p,z)).
      cbn -[to_nat].
      rewrite cancel_of_to Hp.
      ext.
      now rewrite fconsP HX member_fcons /finlist.
Qed.

Definition fun_fpow {A} (X:nat -> option A) : nat -> option (finset A) :=
  fun n => let (p,q) := (Cantor.of_nat n) in
    Some (choose_finset X p q).

Lemma fun_fpowP A (X:nat -> option A) (Q:finset A) :
  Q ⊆ (efun X) <-> Q ∈ (efun (fun_fpow X)).
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

Instance Proper_fun_fpow {A} : Proper (funset_ext A ==> funset_ext (finset A)) fun_fpow.
Proof.
  intros f g H X.
  rewrite -!esetP -!fun_fpowP.
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
  ; decset_correct : tt ∈ decset <-> P
  }.

(**  Decidable predicates are semidecidable.
  *)
#[refine]Instance dec_semidec P `{!Decision P} : SemiDec P :=
  {| decset := (if (decide P) then single tt else eempty) ; decset_correct := _ |}.
Proof.
  destruct (decide P).
  all: rewrite ?singleP ?eemptyP ; intuition.
Qed.

#[refine]Instance semidec_true : SemiDec True
  := {| decset := (single tt) ; decset_correct := _ |}.
Proof.
  rewrite singleP ; intuition.
Qed.

#[refine]Instance semidec_false : SemiDec False
  := {| decset := eempty ; decset_correct := _ |}.
Proof.
  now rewrite eemptyP.
Qed.

#[refine]Instance semidec_disj (P Q:Prop) `{HP : SemiDec P} `{HQ : SemiDec Q}
  : SemiDec (P \/ Q)
  := {| decset := (eunion2 HP.(decset) HQ.(decset)) ; decset_correct := _|}.
Proof.
  now rewrite eunion2P !decset_correct.
Qed.

#[refine]Instance semidec_conj (P Q:Prop) `{HP : SemiDec P} `{HQ : SemiDec Q}
  : SemiDec (P /\ Q)
  := {| decset := (eintersection HP.(decset) HQ.(decset)) ; decset_correct := _|}.
Proof.
  now rewrite eintersectionP !decset_correct.
Qed.

(* unnecessary by propext *)
(* Lemma semidec_iff (P Q:Prop) :
  (P <-> Q) ->
  SemiDec P -> SemiDec Q. *)

#[refine]Instance semidec_in {A : EqTy} (X:eset A) x : SemiDec (x ∈ X) :=
  {| decset := image (fun=> tt) (eintersection X (single x)) ; decset_correct := _|}.
Proof.
  rewrite imageP.
  split.
  - intros [? [Hin _]].
    rewrite eintersectionP singleP in Hin.
    now destruct Hin as [? ->].
  - eexists.
    split ; [|easy].
    now rewrite eintersectionP singleP.
Qed.

Fixpoint all_finset_setdec
  (A:preord) (DECSET:A -> eset unitpo) (X:finset A) : eset unitpo :=
  match X with
  | nil => single tt
  | x::xs => intersection (PREORD_EQ_DEC _ unitpo_dec)
                (DECSET x) (all_finset_setdec A DECSET xs)
  end.

Program Definition all_finset_semidec {A:preord} (P:A -> Prop) 
  (Hok : forall a b, a ≈ b -> P a -> P b)
  (H:forall a, semidec (P a)) (X:finset A)
  : semidec (forall a:A, a ∈ X -> P a)
  := Semidec _ (all_finset_setdec A (fun a => decset (P a) (H a)) X) _.
Next Obligation.
  intros. induction X.
  - simpl; intuition.
    apply nil_elem in H1. elim H1.
    apply single_axiom. auto.
  - split.
    + intros.
      simpl all_finset_setdec in H0.
      apply intersection_elem in H0.
      destruct H0.
      rewrite IHX in H2.
      apply cons_elem in H1. destruct H1.
      * rewrite decset_correct in H0.
        apply Hok with a; auto.
      * apply H2; auto.
    + intros.
      simpl. apply intersection_elem.
      split.
      * apply decset_correct.
        apply H0. apply cons_elem; auto.
      * apply IHX.
        intros. apply H0. apply cons_elem; auto.
Qed.

Fixpoint ex_finset_setdec
  (A:preord) (DECSET:A -> eset unitpo) (X:finset A) : eset unitpo :=
  match X with
  | nil => empty unitpo
  | x::xs => union2 (DECSET x) (ex_finset_setdec A DECSET xs)
  end.

Program Definition ex_finset_semidec {A:preord} (P:A -> Prop) 
  (Hok:forall a b, a ≈ b -> P a -> P b)
  (H:forall a, semidec (P a))
  (X:finset A)
  : semidec (exists a:A, a ∈ X /\ P a)
  := Semidec _ (ex_finset_setdec A (fun a => decset (P a) (H a)) X) _.
Next Obligation.
  intros. induction X.
  - split; simpl; intros.
    + apply empty_elem in H0. elim H0.
    + destruct H0 as [a [??]]. apply nil_elem in H0. elim H0.
  - split; simpl; intros.
    + apply union2_elem in H0.
      destruct H0.
      * rewrite decset_correct in H0.
        exists a. split; auto. apply cons_elem; auto.
      * rewrite IHX in H0.
        destruct H0 as [b [??]].
        exists b. split; auto.
        apply cons_elem; auto.
    + destruct H0 as [q[??]].
      apply cons_elem in H0. destruct H0.
      * apply union2_elem.
        left. apply decset_correct; auto.
        apply Hok with q; auto.
      * apply union2_elem.
        right. apply IHX.
        exists q. split; auto.
Qed.

Definition eimage' (A B:preord) (f:A -> B) (P:eset A) : eset B :=
  fun n => match P n with None => None | Some x => Some (f x) end.

Program Definition esubset {A:preord} (P:A -> Prop) 
  (H:forall a, semidec (P a)) (X:eset A) :=
  eset.eunion A 
    (eimage' _ _ (fun x => eimage' _ _ (fun _ => x) (decset (P x) (H x))) X).

Lemma esubset_elem (A:preord) (P:A->Prop) (dec:forall a, semidec (P a)) 
  (Hok:forall a b, a ≈ b -> P a -> P b)
  X x :
  x ∈ esubset P dec X <-> (x ∈ X /\ P x).
Proof.
  split; intros.
  - unfold esubset in H.
    apply union_axiom in H.
    destruct H as [Q [??]].
    destruct H as [n ?].
    unfold eimage' in H.
    case_eq (X n); intros.
    + rewrite H1 in H.
      destruct H.
      generalize H0.
      intros.
      apply H in H0.
      destruct H0 as [m ?].
      case_eq (decset (P c) (dec c) m); intros.
      * rewrite H4 in H0.
        split.
        ** exists n. rewrite H1. auto.
        ** apply Hok with c; auto.
           apply (decset_correct _ (dec c)).
           exists m. rewrite H4; auto.
           destruct c0; auto.
      * rewrite H4 in H0. elim H0.
    + rewrite H1 in H. elim H.

  - destruct H.
    unfold esubset.
    apply union_axiom.
    exists
      ((fun x0 : A =>
          eimage' unitpo A (fun _ : unitpo => x0) (decset (P x0) (dec x0))) x).
    split.
    + red; simpl. red.
      unfold eimage'. simpl.
      destruct H as [n ?].
      exists n.
      destruct (X n); auto.
      split; simpl; intros; red; simpl; intros.
      * destruct H1 as [m ?]. simpl in H1.
        case_eq (decset (P x) (dec x) m); intros.
        ** rewrite H2 in H1.
           assert (P x).
           { apply (decset_correct _ (dec x)).
             exists m. rewrite H2. destruct c0; auto.
           }
           assert (P c).
           { apply Hok with x; auto. }
           rewrite <- (decset_correct _ (dec c)) in H4.
           destruct H4 as [p ?].
           exists p. destruct (decset (P c) (dec c) p); auto.
           rewrite H1; auto.
        ** rewrite H2 in H1. elim H1.
      * destruct H1 as [m ?].
        case_eq (decset (P c) (dec c) m); intros.
        ** rewrite H2 in H1.
           assert (P c).
           { rewrite <- (decset_correct _ (dec c)).
             exists m. rewrite H2. destruct c0; auto.
           } 
           assert (P x).
           { apply Hok with c; auto. }
           rewrite <- (decset_correct _ (dec x)) in H4.
           destruct H4 as [p ?].
           exists p. destruct (decset (P x) (dec x) p); auto.
           rewrite H1; auto.
        ** rewrite H2 in H1. elim H1.

    + rewrite <- (decset_correct _ (dec x)) in H0.
      destruct H0 as [n ?].
      case_eq (decset _ (dec x) n); intros.
      * rewrite H1 in H0.
        exists n.
        unfold eimage'.
        rewrite H1. auto.
      * rewrite H1 in H0. elim H0.
Qed.

Definition esubset_dec (A:preord) (P:A -> Prop) (dec:forall x:A, {P x}+{~P x})
  (X:eset A) : eset A :=
  fun n => match X n with
           | None => None
           | Some a => 
               match dec a with
               | left H => Some a
               | right _ => None
               end
           end.

Lemma esubset_dec_elem : forall (A:preord) (P:A->Prop) dec X x,
  (forall x y, x ≈ y -> P x -> P y) ->
  (x ∈ esubset_dec A P dec X <-> (x ∈ X /\ P x)).
Proof.  
  intros. split; intros.
  - red in H0. simpl in H0.
    destruct H0 as [n ?].
    unfold esubset_dec in H0.
    case_eq (X n); intros.
    + rewrite H1 in H0.
      destruct (dec c).
      * split; auto.
        exists n. rewrite H1. auto.
        apply H with c; auto.
      * elim H0.
    + rewrite H1 in H0. elim H0.

  - destruct H0.
    destruct H0 as [n ?].
    exists n.
    unfold esubset_dec.
    destruct (X n); auto.
    destruct (dec c); auto.
    apply n0. apply H with x; auto.
Qed.

Definition erel (A B:preord) := eset (A × B).

Definition erel_image (A B:preord) (dec : ord_dec A) (R:erel A B) (x:A) : eset B :=
  image π₂ (esubset_dec
                    (A×B)
                    (fun p => π₁#p ≈ x)
                    (fun p => PREORD_EQ_DEC A dec (π₁#p) x) R).

Lemma erel_image_elem : forall A B dec R x y,
  y ∈ erel_image A B dec R x <-> (x,y) ∈ R.
Proof.  
  intros. split; intros.

  - unfold erel_image in H.
    apply image_axiom2 in H.
    destruct H as [p [??]].
    apply esubset_dec_elem in H.
    + destruct H.
      assert (p ≈ (x,y)).
      { destruct p; simpl in *.
        destruct H1.
        destruct H0.
        split; split; auto.
      }
      rewrite <- H2. auto.
    + intros.
      rewrite <- H2. auto.

  - unfold erel_image.
    change y with (π₂# ((x,y) : A×B)).
    apply image_axiom1.
    apply esubset_dec_elem.
    + intros. rewrite <- H0; auto.
    + split; auto.
Qed.

Definition erel_inv_image 
  (A B:preord) (dec : ord_dec B) (R:erel A B) (y:B) : eset A :=
  image π₁ (esubset_dec (A×B)
                    (fun p => π₂#p ≈ y)
                    (fun p => PREORD_EQ_DEC B dec (π₂#p) y) R).

Lemma erel_inv_image_elem : forall A B dec R x y,
  x ∈ erel_inv_image A B dec R y <-> (x,y) ∈ R.
Proof.  
  intros. split; intros.

  - unfold erel_inv_image in H.
    apply image_axiom2 in H.
    destruct H as [p [??]].
    apply esubset_dec_elem in H.
    + destruct H.
      assert (p ≈ (x,y)).
      { destruct p; simpl in *.
        destruct H1; destruct H0.
        split; split; auto.
      } 
      rewrite <- H2; auto.
    + intros. rewrite <- H2; auto.
  - unfold erel_inv_image.
    change x with (π₁# ((x,y) : A × B)).
    apply image_axiom1.
    apply esubset_dec_elem.
    + intros. rewrite <- H0; auto.
    + split; auto.
Qed.

(** * Weak countable choice 

     Countable indefinite description gives rise to a functional choice principle:
       "Every total enumerable relation gives rise to a (computable) function."

     There are two subtle points regarding the formal statemet: first,
     we need need to assume a decidable order on A (and thus decidable
     setoid equality); second, the choice function is _constructed_
     not just asserted to exist.

     This statement is weaker than the "standard" version of countable choice.
     In countable choice, the domain [A] is assumed to be countable,
     but the cardinality of the relation [R] is unconstrained.

     Here, we instead require [R] to be enumerable and [A] to have a decidable
     order.  Because [R] is total, this implies [A] is countable (and
     effective, as defined in "effective.v.")  Hence this statement is
     implied by countable choice (more precisely, a statement of countable choice
     that constructs a function, rather than merely asserting it to exist).
     This statement is _strictly_ weaker, as the usual version of
     countable choice is not provable in Coq.
  *)
Theorem weak_countable_choice (A B:preord) (HA:ord_dec A) (R:erel A B) :
  (forall a:A, exists b, (a,b) ∈ R) ->
  { f:A -> B | forall a, (a, f a) ∈ R }.
Proof.
  intros.

  assert (Hrng : forall a, einhabited (erel_image A B HA R a)).
  { intros. apply member_inhabited.
    destruct (H a) as [b ?]. exists b.
    apply erel_image_elem. auto.
  }
  exists (fun a => choose B (erel_image A B HA R a) (Hrng a)).

  intros.
  generalize (choose_elem B (erel_image A B HA R a) (Hrng a)).
  intros. apply erel_image_elem in H0.
  auto.
Qed.
