(** * fin_interface.v: Attempt at describing the interface of finite domain elements *)
From Stdlib Require Import Relations List Program ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.
Require Import utils.all categories.all preord sets finsets.

Open Scope general_if_scope.

Lemma True_decide P `{Decision P} : decide P -> P.
Proof.
  intros Hdec.
  by case_decide.
Qed.

Lemma neg_ex A (X : finset A) P `{! forall x, Decision (P x)} : ~ (∃ x ∈ X, P x) <-> (∀ x ∈ X, ~ P x).
Proof.
  split.
  - intros Hn x ? ?. apply Hn. now eexists.
  - intros Hall []. now eapply Hall.
Qed.

Lemma neg_ex_neg A (X : finset A) P `{! forall x, Decision (P x)} :
  ~ (∃ x ∈ X, ~ (P x)) <-> (∀ x ∈ X, P x).
Proof.
  rewrite neg_ex.
  split.
  all: intros ? ? **.
  1: now apply (dec_stable _).
  intros Hn ; now apply Hn.
Qed.

(** ** Interface for the type of finite domain elements *)

(** *** The carrier and its basic operations *)

Class DomainSupport : Type := {
  elt : DecPoset ; (** the type of finite domain elements *)
  finfun : DecPoset ; (** the type of finite domain functions *)

  (** Constructors for [elt] *)
  fbot : elt ;
  funiv : elt ;
  (*
  fnat : elt ;
  zero  : elt ;
  succ : elt -> elt ; *)
  fpi : elt -> finfun -> elt ;
  fabs : finfun -> elt ;

  (** Destructor for [finfun] *)
  fapp : finfun -> Monotone elt elt ;

  (** there is some identification happening! *)
  fabs_eq (f : finfun) : (forall a, fapp f a = fbot) <-> fabs f = fbot
}.

Notation fincode := (finset (elt*elt)).

(** *** Characterisation *)

(** The "other half" of a the structure: eliminator for [elt] and
  constructor for [finfun] *)

Definition compatible {A : PreOrder} (x y : A) :=
  exists u, x ≤ u /\ y ≤ u.

Definition pairwise_compatible {A : Poset}
  (f f' : finset (A * A)) :=
  ∀ p ∈ f, ∀ p' ∈ f',
    (compatible (fst p) (fst p') -> compatible (snd p) (snd p')).

Class ValidFun {A : Poset} (f : finset (A*A)) :=
  valid_fun : (pairwise_compatible f f).

Arguments ValidFun {_} _.

Variant elt_gen `{DomainSupport} : Type :=
  | gbot : elt_gen
  | guniv : elt_gen
  | gpi (a : elt) (b : finfun) : elt_gen
  | gabs (f : finfun) : (fabs f) <> fbot -> elt_gen.

Arguments gabs {_} f _.

Definition mk_elt `{DomainSupport} (g : elt_gen) : elt :=
  match g with
  | gbot => fbot
  | guniv => funiv
  | gpi a b => fpi a b
  | gabs f _ => fabs f
  end.

Class DomainUniversal (D : DomainSupport) : Type := {
  (** case-splitting for [elt] *)
  case_elt : elt -> elt_gen ;
  mk_case : forall g, case_elt (mk_elt g) = g ;
  case_mk : forall e, mk_elt (case_elt e) = e ;

  (** constructor for [finfun] *)
  mk_finfun (f : fincode) `{ValidFun _ f} : finfun ;

  (** characterisation of [finfun] *)
  case_finfun : forall (f : finfun),
    (exists f' (h : ValidFun f'), f = @mk_finfun f' h) ;

  (** characterisation of [app] *)
  mk_app (f : fincode) `{ValidFun _ f} (a : elt) :
    least_upper_bound
      (fapp (@mk_finfun f _) a)
      (image π₂ (finsubset (fun p => (fst p) ≤ a) f))
}.

(** Because lubs are unique, [mk_app] uniquely characterises
  [fapp (mk_finfun f h) a]. However, since we do not
  know that arbitrary lubs exist in [elt] (although in this particular case
  it does), we cannot write this as an equality, eg
  [fapp (mk_finfun f h) a = lub …], so it's easier to have an operation
  [fapp] + its characterisation *)

(** Note that we cannot expose a [case_finfun] function of type
  [finfun -> fincode] because this would not respect the quotient.
  We can only assert that such a thing exists *)

Arguments mk_finfun {D U} _ {_} : rename.
Arguments mk_app {D U} f {_} a : rename.

Lemma case_bot `{DomainUniversal} : case_elt fbot = gbot.
Proof.
  by rewrite -(mk_case gbot).
Qed.

Lemma case_univ `{DomainUniversal} : case_elt funiv = guniv.
Proof.
  by rewrite -(mk_case guniv).
Qed.

Lemma case_pi `{DomainUniversal} a b : case_elt (fpi a b) = gpi a b.
Proof.
  by rewrite -(mk_case (gpi _ _)).
Qed.

Lemma case_abs `{DomainUniversal} f (h : (fabs f) <> fbot) : case_elt (fabs f) = gabs f h.
Proof.
  by rewrite -(mk_case (gabs _ _)).
Qed.

Hint Rewrite @case_bot @case_univ @case_pi : elt.

Lemma pi_inj `{DomainUniversal} a b a' b' :
  (fpi a b) = (fpi a' b') ->
  a = a' /\ b = b'.
Proof.
  intros e.
  enough (gpi a b = gpi a' b') by (split ; congruence).
  rewrite -(mk_case (gpi a b)) -(mk_case (gpi a' b')) /= e //.
Qed.

Lemma noconf_univ_pi `{DomainUniversal} a b : (funiv) <> (fpi a b).
Proof.
  intros e.
  enough (guniv = gpi a b) by congruence.
  rewrite -(mk_case (guniv)) -(mk_case (gpi a b)) /= e //.
Qed.

Lemma noconf_univ_bot `{DomainUniversal} : (funiv) <> fbot.
Proof.
  intros e.
  enough (guniv = gbot) by congruence.
  rewrite -(mk_case (guniv)) -(mk_case (gbot)) /= e //.
Qed.

Lemma noconf_pi_bot `{DomainUniversal} a b : (fpi a b) <> fbot.
Proof.
  intros e.
  enough (gpi a b = gbot) by congruence.
  rewrite -(mk_case (gpi a b)) -(mk_case (gbot)) /= e //.
Qed.

Lemma finfun_app `{DomainUniversal} (f : fincode) `{ValidFun _ f} :
  ∀ p ∈ f, p.2 ≤ fapp (mk_finfun f) p.1.
Proof.
  intros p Hin.
  apply mk_app ; cbn.
  apply: (image_fun _ _ _ π₂).
  now rewrite finsubsetP.
Qed.

Lemma noconf_univ_abs `{DomainUniversal} f : funiv <> fabs f.
Proof.
  intros e.
  destruct (decide (fabs f = fbot)) as [|h].
  1: apply noconf_univ_bot ; now etransitivity.
  enough (guniv = (gabs f h)) by congruence.
  rewrite -(mk_case guniv) -(mk_case (gabs f h)) /= e //.
Qed.

Lemma noconf_pi_abs `{DomainUniversal} a b f : (fpi a b) <> fabs f.
Proof.
  intros e.
  destruct (decide (fabs f = fbot)) as [|h].
  1: eapply noconf_pi_bot ; now etransitivity.
  enough ((gpi a b) = (gabs f h)) by congruence.
  rewrite -(mk_case (gpi a b)) -(mk_case (gabs f h)) /= e //.
Qed.

(** *** Characterising the order *)

Definition gen_le `{DomainSupport} (e e' : elt_gen) : bool :=
  match e, e' with
  | gbot, _ => true
  | guniv, guniv => true
  | gpi a b, gpi a' b' => decide (a ≤ a' /\ b ≤ b')
  | gabs f _, gabs f' _ => decide (f ≤ f')
  | _, _ => false
  end.

Class DomainOrder (D : DomainSupport) (U : DomainUniversal D) : Type := {
  elt_leP (e e' : elt) : e ≤ e' <-> gen_le (case_elt e) (case_elt e') ;
  finfun_leP (f f' : finfun) : (f ≤ f') <-> (forall a, fapp f a ≤ fapp f' a)
}.

Lemma bot_least `{DomainOrder} (e : elt) : fbot ≤ e.
Proof.
  rewrite elt_leP.
  rewrite -/(mk_elt gbot) mk_case //=.
Qed.

Lemma le_bot_inv `{DomainOrder} (e : elt) : e ≤ fbot -> e = fbot.
Proof.
  intros. apply ord_antisym ; tea.
  apply bot_least.
Qed.

Lemma le_univ_inv `{DomainOrder} (e : elt) : e ≤ funiv -> e = fbot \/ e = funiv.
Proof.
  intros hle%elt_leP.
  autorewrite with elt in hle.
  rewrite -(case_mk e).
  destruct (case_elt e) ; cbn in * ; solve [done|easy].
Qed.

Lemma le_pi_inv `{DomainOrder} (e a : elt) (b : finfun) :
  e ≤ (fpi a b) ->
  e = fbot \/ exists a' b', e = fpi a' b' /\ a' ≤ a /\ b' ≤ b.
Proof.
  intros hle%elt_leP.
  autorewrite with elt in hle.
  rewrite -(case_mk e).
  destruct (case_elt e) ; cbn in * ; try solve [easy|done].
  apply True_decide in hle as [].
  right.
  now do 2 eexists.
Qed.

Lemma le_abs_inv `{DomainOrder} (e : elt) (f : finfun) :
  e ≤ (fabs f) ->
  e = fbot \/ e <> fbot /\ exists f', e = fabs f' /\ f' ≤ f.
Proof.
  intros hle.
  destruct (decide ((fabs f) = fbot)) as [e'|].
  - rewrite e' in hle.
    now apply le_bot_inv in hle.
  - apply elt_leP in hle.
    rewrite case_abs in hle.
    rewrite -(case_mk e).
    destruct (case_elt e) ; cbn in * ; try solve [easy|done].
    apply True_decide in hle.
    right.
    eauto.
Qed.

Lemma mk_finfun_le_inv `{DomainOrder} (f : fincode) `{ValidFun _ f} (f' : finfun) :
  (mk_finfun f ≤ f') <->
  (∀ p ∈ f, snd p ≤ fapp f' (fst p)).
Proof.
  split.
  - intros Hle p Hin.
    transitivity (fapp (mk_finfun f) p.1).
    2: by apply finfun_leP.
    now apply finfun_app.
  - intros Hle.
    apply finfun_leP.
    intros a.
    apply mk_app ; cbn.
    move => ? /imageP /= [x' []] /finsubsetP [? ?] ? ; subst.
    transitivity (fapp f' x'.1) ; auto.
    by apply mon_mon.
Qed.

Lemma finfun_ext `{DomainOrder} (f f' : finfun) : (forall a, fapp f a = fapp f' a) -> f = f'.
Proof.
  intros e.
  apply ord_antisym.
  all: apply finfun_leP ; intros.
  1: now rewrite e.
  now rewrite -e.
Qed.

Smpl Add (apply finfun_ext) : extensionality.

Instance emptyFun A : ValidFun (A := A) fempty.
Proof.
  by move => ? /femptyP //.
Qed.

Definition funbot `{DomainUniversal} : finfun := (mk_finfun fempty).

Lemma app_funbot `{DomainOrder} a : fapp funbot a = fbot.
Proof.
  apply le_bot_inv, mk_app ; cbn.
  move => ? /imageP [? []] /finsubsetP [] /femptyP //.
Qed.  

Lemma abs_funbot `{DomainOrder} : fabs funbot = fbot.
Proof.
  apply fabs_eq, app_funbot.
Qed.

Lemma app_bot_inv `{DomainOrder} (f : finfun) : (forall a, fapp f a ≤ fbot) -> f = funbot.
Proof.
  intros Ho.
  ext.
  rewrite app_funbot.
  now apply le_bot_inv.
Qed.

Lemma app_bot_mk_finfun `{DomainOrder} (f : fincode) `{ValidFun _ f} :
  (∀ p ∈ f, p.2 = fbot) -> mk_finfun f = funbot.
Proof.
  intros e.
  ext.
  rewrite app_funbot.
  apply le_bot_inv, mk_app.
  move => ? /imageP /= [x' []] /finsubsetP [? ?] ? ; subst.
  now rewrite e.
Qed.

Lemma app_bot_equiv `{DomainOrder} f :
  (forall a, fapp f a = fbot) <-> f = funbot.
Proof.
  split ; cycle -1.
  1: move => -> ; apply app_funbot.
  intros e.
  destruct (case_finfun f) as (f'&?&->).
  apply app_bot_mk_finfun.
  intros p Hin.
  apply le_bot_inv.
  etransitivity.
  1: now apply finfun_app.
  now rewrite e.
Qed.

Lemma noconf_funbot `{DomainOrder} f :
  (exists a, fapp f a <> fbot) <-> f <> funbot.
Proof.
  transitivity (~ (forall a, fapp f a = fbot)).
  2: apply not_iff_compat, app_bot_equiv.
  split.
  1: now intros [].
  intros Hall.
  destruct (case_finfun f) as (f'&?&->).
  enough (∃ x ∈ (image π₁ f'), fapp (mk_finfun f') x <> fbot) as (a&?&Hn')
    by now exists a.
  apply (dec_stable _).
  intros Hn.
  rewrite neg_ex_neg in Hn.
  eapply Hall, app_bot_equiv, app_bot_mk_finfun.
  intros p Hin ; cbn -[prod_projl] in *.
  apply le_bot_inv.
  erewrite <- Hn.
  1: now apply finfun_app.
  now apply: (image_fun _ _ _ π₁).
Qed.

Lemma noconf_abs_bot `{DomainOrder} f :
  (exists a, fapp f a <> fbot) <-> (fabs f) <> fbot.
Proof.
  rewrite noconf_funbot.
  apply not_iff_compat.
  by rewrite -fabs_eq -app_bot_equiv.
Qed.

(** *** Ranking *)

(** The main thing to note is that the rank cannot be defined as a function,
  as this would violate the quotient: a "bad" representation of a domain element
  could assign it a too high rank. Thus we express it as a relation, with the 
  intended meaning that [ranked e n] means that element [e] can be constructed
  in at most [n] steps. *)

Class DomainRanked (D : DomainSupport) (U : DomainUniversal D) (O : DomainOrder U) : Type := {
  ranked : elt -> nat -> Prop ;
  ranked_fun : finfun -> nat -> Prop ;

  (** all elements can be eventually reached at some rank *)
  all_ranked : forall (e : elt), exists (n : nat), ranked e n ;
  all_ranked_fun : forall (f : finfun), exists (n : nat), ranked_fun f n ;

  (** ranking for constructors and destructors *)
  ranked_bot (n : nat) : ranked fbot n ;
  ranked_zero e : ranked e 0 -> e = fbot ;
  ranked_univ (n : nat) : (exists m, n = S m) <-> ranked funiv n ;
  ranked_pi (a : elt) (b : finfun) n : (ranked a n /\ ranked_fun b n) <-> ranked (fpi a b) (S n) ;
  ranked_abs (f : finfun) n : fabs f <> fbot -> (ranked_fun f n) <-> (ranked (fabs f) (S n)) ;
  ranked_app (f : finfun) u n : ranked_fun f n -> ranked (fapp f u) n ;

  (** ranking and the order *)
  ranked_incr e m n : ranked e m -> m ≤ n -> ranked e n ;
  ranked_fun_incr f m n : ranked_fun f m -> m ≤ n -> ranked_fun f n ;
  ranked_decr e e' n : ranked e' n -> e ≤ e' -> ranked e n ;
  ranked_fun_decr f f' n : ranked_fun f' n -> f ≤ f' -> ranked_fun f n ;
  ranked_lub (es : finset elt) (e' : elt) n :
    least_upper_bound e' es -> (∀ e ∈ es, ranked e n) -> ranked e' n ;
  ranked_fun_lub (fs : finset finfun) (f' : finfun) n :
    least_upper_bound f' fs -> (∀ f ∈ fs, ranked_fun f n) -> ranked_fun f' n ; 
}.

Class FullDomain : Type := {
  domain_support :> DomainSupport ;
  domain_universal :> DomainUniversal domain_support ;
  domain_order :> DomainOrder domain_universal ;
  domain_ranked :> DomainRanked domain_order
  }.

Existing Instance domain_support.
Existing Instance domain_universal.
Existing Instance domain_order.
Existing Instance domain_ranked.

Lemma ranked_fun_zero `{FullDomain} f : ranked_fun f 0 -> f = funbot.
Proof.
  intros.
  apply app_bot_equiv.
  intros.
  by apply ranked_zero, ranked_app.
Qed.

(** A "weak" induction principle: no deep induction, and, for functions, only an
  induction hypothesis for the right-hand side. Is this enough? *)

Lemma elt_weak_ind `{FullDomain} (P : elt -> Prop) (Pfun : finfun -> Prop) :
  (P fbot) ->
  (P funiv) ->
  (forall a b, P a -> Pfun b -> P (fpi a b)) ->
  (forall f, Pfun f -> P (fabs f)) ->
  (forall (f : fincode) (h : ValidFun f), (∀ p ∈ f, P p.2) ->
    Pfun (mk_finfun f)) ->
  forall e, P e.
Proof.
  intros Hbot Huniv Hpi Habs Hfun.
  assert (forall n f, ranked_fun f n -> (forall e (m : nat), m ≤ n -> ranked e m -> P e) -> Pfun f)
    as IHfun.
  {
    intros n f Hf IH.
    destruct (case_finfun f) as (f'&?&->).
    apply Hfun.
    intros ?? ; cbn in *.
    eapply IH.
    1: reflexivity.
    eapply ranked_decr.
    2: now apply finfun_app.
    by apply ranked_app.
  }
  enough (forall n e, ranked e n -> P e) as Hind.
  {
   intros.
   destruct (all_ranked e) as [].
   now eapply Hind.
  }
  intros n e He.
  induction n as [|n IH] using Nat.strong_induction_le in e, He |- *.
  - apply ranked_zero in He as ->.
    assumption.
  - rewrite -(case_mk e) in He |- *.
    destruct (case_elt e) ; cbn in *.
    + apply Hbot.
    + apply Huniv.
    + apply ranked_pi in He as [].
      apply Hpi.
      1: now eapply IH.
      now eapply IHfun.
    + apply ranked_abs in He ; tea.
      apply Habs.
      now eapply IHfun.
Qed.

(** A variant, which gives an IH for the values of a [finfun] at any input *)
Lemma elt_weak_ind' `{FullDomain} (P : elt -> Prop) (Pfun : finfun -> Prop) :
  (P fbot) ->
  (P funiv) ->
  (forall a b, P a -> Pfun b -> P (fpi a b)) ->
  (forall f, Pfun f -> P (fabs f)) ->
  (forall (f : finfun), (forall a, P (fapp f a)) -> Pfun f) ->
  forall e, P e.
Proof.
  intros Hbot Huniv Hpi Habs Hfun.
  assert (forall n f, ranked_fun f n -> (forall e (m : nat), m ≤ n -> ranked e m -> P e) -> Pfun f)
    as IHfun.
  {
    intros n f Hf IH.
    apply Hfun.
    intros a.
    eapply IH.
    1: reflexivity.
    by apply ranked_app.
  }
  enough (forall n e, ranked e n -> P e) as Hind.
  {
   intros.
   destruct (all_ranked e) as [].
   now eapply Hind.
  }
  intros n e He.
  induction n as [|n IH] using Nat.strong_induction_le in e, He |- *.
  - apply ranked_zero in He as ->.
    assumption.
  - rewrite -(case_mk e) in He |- *.
    destruct (case_elt e) ; cbn in *.
    + apply Hbot.
    + apply Huniv.
    + apply ranked_pi in He as [].
      apply Hpi.
      1: now eapply IH.
      now eapply IHfun.
    + apply ranked_abs in He ; tea.
      apply Habs.
      now eapply IHfun.
Qed.

Inductive ind_le `{DomainSupport} : elt -> elt -> Prop :=
  | bot_le e : ind_le fbot e
  | univ_le : ind_le funiv funiv
  | pi_le a a' b b' :
      ind_le a a' ->
      (forall x, ind_le (fapp b x) (fapp b' x)) ->
      ind_le (fpi a b) (fpi a' b')
  | abs_le f f' : (forall x, ind_le (fapp f x) (fapp f' x)) -> ind_le (fabs f) (fabs f').

Lemma le_ind_le `{FullDomain} e e' : e ≤ e' -> ind_le e e'.
Proof.
  revert e'.
  pattern e.
  unshelve eapply elt_weak_ind'.
  1: exact (fun f => forall f', f ≤ f' -> forall x, ind_le (fapp f x) (fapp f' x)).
  - constructor.
  - move => e' /elt_leP /= Hle.
    autorewrite with elt in Hle ; cbn in Hle.
    rewrite -(case_mk e').
    destruct (case_elt e') ; cbn ; try done.
    constructor.
  - move => ?? IH IH' e' /elt_leP Hle.
    autorewrite with elt in Hle ; cbn in Hle.
    rewrite -(case_mk e').
    destruct (case_elt e') ; cbn ; try done.
    apply True_decide in Hle as [].
    now constructor.
  - move => f IH e' /elt_leP Hle.
    destruct (decide (fabs f = fbot)) as [->|].
    1: now constructor.
    unshelve erewrite case_abs in Hle => //.
    rewrite /= in Hle.
    rewrite -(case_mk e').
    destruct (case_elt e') ; cbn ; try done.
    apply True_decide in Hle.
    now constructor.
  - cbn ; intros f IH ? Hle ?.
    by apply IH, finfun_leP.
Qed.

(** ** Typing *)

Reserved Notation "'⊢' t '::' T" (at level 101, t at level 59).

Inductive fin_typing `{FullDomain} : elt -> elt -> Prop :=
  | Tbot A : ⊢ fbot :: A
  
  | TUniv : ⊢ funiv :: funiv
  
  | TPi (a : elt) (b : fincode) `{ValidFun _ b} :
    (∀ p ∈ b, (⊢ p.1 :: a) /\ (⊢ p.2 :: funiv)) ->
    ⊢ fpi a (mk_finfun b) :: funiv

  | TAbs (a : elt) (b : finfun) (f : fincode) `{ValidFun _ f} :
    (∀ p ∈ f, (⊢ p.1 :: a) /\ (⊢ p.2 :: fapp b p.1)) ->
    ⊢ fabs (mk_finfun f) :: fpi a b

  where "'⊢' t '::' A" := (fin_typing A t).


Lemma typing_bot_inv `{FullDomain} u :
  (⊢ u :: fbot) -> u = fbot.
Proof.
  intros Hty.
  inversion Hty ; subst ; cbn.
  all: try reflexivity.
  all: exfalso.
  - by apply noconf_univ_bot.
  - now eapply noconf_pi_bot.
Qed.

Lemma typing_univ_inv `{FullDomain} u :
  (⊢ u :: funiv) ->
  (u = fbot) \/ (u = funiv) \/
    exists (a : elt) (b : fincode) (h : ValidFun b),
      u = fpi a (mk_finfun b) /\
      (∀ p ∈ b, (⊢ p.1 :: a) /\ (⊢ p.2 :: funiv)).
Proof.
  intros Hty ; inversion Hty ; try easy.
  - subst.
    right ; right ; eauto.
  - exfalso.
    now eapply noconf_univ_pi.
Qed. 

Lemma typing_pi_inv `{FullDomain} u a b :
  (⊢ u :: fpi a b) ->
  exists (f : fincode) (h : ValidFun f),
    u = (fabs (mk_finfun f)) /\
    (∀ p ∈ f, (⊢ p.1 :: a) /\ (⊢ p.2 :: fapp b p.1)).
Proof.
  intros Hty.
  inversion Hty ; subst ; cbn.
  - eexists fempty, _.
    split.
    1: by rewrite abs_funbot.
    move => ? /femptyP //.
  - exfalso.
    now eapply noconf_univ_pi.
  - exfalso.
    now eapply noconf_univ_pi.
  - eapply pi_inj in H1 as [-> ->].
    eauto.
Qed.

Lemma typing_abs_inv `{FullDomain} u f :
  (⊢ u :: fabs f) ->
  u = fbot.
Proof.
  intros Hty.
  inversion Hty ; subst ; cbn ; try easy.
  - exfalso.
    now eapply noconf_univ_abs.
  - exfalso.
    now eapply noconf_univ_abs.
  - exfalso.
    now eapply noconf_pi_abs.
Qed.

Lemma typing_incr `{FullDomain} u a b :
  a ≤ b ->
  (⊢ u :: a) ->
  (⊢ u :: b).
Proof.
  intros h%le_ind_le h'.
  induction h in h', u |- *.
  - apply typing_bot_inv in h' ; subst.
    constructor.
  - apply typing_univ_inv in h' as [->|[->|(?&?&?&->&?)]].
    all: now constructor.
  - apply typing_pi_inv in h' as (f&?&?&Hf) ; subst.
    constructor.
    move => p Hin.
    specialize (Hf _ Hin) as [Ha Hb] ; cbn in *.
    eauto.
  - apply typing_abs_inv in h' ; subst.
    constructor.
Qed.

Lemma typing_lub `{FullDomain} (us : finset elt) (v : elt) (a : elt) :
  least_upper_bound v us ->
  (∀ u ∈ us, ⊢ u :: a) ->
  ⊢ v :: a.
Proof.
Admitted.

Lemma typing_app `{FullDomain} (w u a : elt) (b : finfun) :
  (⊢ w :: fpi a b) ->
  (⊢ u :: a) ->
  exists w', w = fabs w' /\ (⊢ fapp w' u :: fapp b u).
Proof.
  move => /typing_pi_inv [f [h []]] ? ; subst.
  move => Hf Hu.
  eexists ; split ; [reflexivity|].
  eapply typing_lub.
  1: now apply mk_app.
  move => ? /imageP /= [p []] /finsubsetP [Hin ?] ? ; subst.
  specialize (Hf _ Hin) as [].
  eapply typing_incr ; tea.
  now apply mon_mon.
Qed.