(** * fin_interface.v: Attempt at describing the interface of finite domain elements *)
From Stdlib Require Import Relations List Program ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.
Require Import utils.all categories.all preord sets finsets.

Open Scope general_if_scope.

(** ** The base carrier of a solution to the domain equation *)

Class DomainSupport : Type := {
  elt : DecPoset ; (** the type of finite domain elements *)
  finfun : DecPoset ; (** the type of finite domain functions *)

  (** Constructors for [elt] *)
  fbot : elt ;
  funiv : nat -> elt ;
  (*
  fnat : elt ;
  zero  : elt ;
  succ : elt -> elt ; *)
  fpi : elt -> finfun -> elt ;
  fabs : finfun -> elt ;

  (** Destructors for [finfun] *)
  fapp : finfun -> Monotone elt elt ;

  (** there is some identification happening! *)
  fabs_eq (f : finfun) : (forall a, fapp f a = fbot) <-> fabs f = fbot
}.

(** ** Characterisation *)

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
  | guniv (n : nat) : elt_gen
  | gpi (a : elt) (b : finfun) : elt_gen
  | gabs (f : finfun) : (fabs f) <> fbot -> elt_gen.

Arguments gabs {_} f _.

Definition mk_elt `{DomainSupport} (g : elt_gen) : elt :=
  match g with
  | gbot => fbot
  | guniv n => funiv n
  | gpi a b => fpi a b
  | gabs f _ => fabs f
  end.

Class DomainUniversal (D : DomainSupport) : Type := {
  (** case-splitting for [elt] *)
  case_elt : elt -> elt_gen ;
  mk_case : forall g, case_elt (mk_elt g) = g ;
  case_mk : forall e, mk_elt (case_elt e) = e ;

  (** constructor for [finfun] *)
  mk_finfun (f : finset (elt*elt)) `{ValidFun _ f} : finfun ;

  (** characterisation of [app] *)
  mk_app (f : finset (elt*elt)) `{ValidFun _ f} (a : elt) :
    least_upper_bound
      (fapp (@mk_finfun f _) a)
      (image π₂ (finsubset (fun p => (fst p) ≤ a) f))
}.

(** Because lubs are unique, [mk_app] uniquely characterises
  [fapp (mk_finfun f h) a]. However, since we do not
  know that arbitrary lubs exist (although in this case they
  actually do), we cannot write this as an equality, eg
  [fapp (mk_finfun f h) a = lub …], so it's easier to have an operation
  [fapp] + its characterisation *)

Arguments mk_finfun {D U} _ {_} : rename.
Arguments mk_app {D U} f {_} a : rename.

(* testing things are ok *)
Lemma noconf_univ_pi `{DomainUniversal} n a b : (funiv n) <> (fpi a b).
Proof.
  intros e.
  enough (guniv n = gpi a b) by congruence.
  rewrite -(mk_case (guniv n)) -(mk_case (gpi a b)) /= e //.
Qed.

Lemma noconf_bot_abs `{DomainUniversal} f :
  (exists a, fapp f a <> fbot) -> fabs f <> fbot.
Proof.
  intros hf e.
  rewrite -fabs_eq in e.
  destruct hf as [a ha].
  apply ha, e.
Qed.

Lemma app_lt `{DomainUniversal} (f : finset (elt*elt)) `{ValidFun _ f} (p : elt*elt) :
  p ∈ f -> p.2 ≤ fapp (mk_finfun f) p.1.
Proof.
  intros Hin.
  apply mk_app ; cbn.
  apply: (image_fun _ _ _ π₂).
  now rewrite finsubsetP.
Qed.

(** ** Characterising the order *)

Definition gen_le `{DomainSupport} (e e' : elt_gen) : bool :=
  match e, e' with
  | gbot, _ => true
  | guniv n, guniv n' => n =? n'
  | gpi a b, gpi a' b' => decide (a ≤ a' /\ b ≤ b')
  | gabs f _, gabs f' _ => decide (f ≤ f')
  | _, _ => false
  end.

Class DomainOrder (D : DomainSupport) (U : DomainUniversal D) : Type := {
  elt_leP (e e' : elt) : e ≤ e' <-> gen_le (case_elt e) (case_elt e') ;
  finfun_leP (f f' : finfun) : (f ≤ f') <-> (forall a, fapp f a ≤ fapp f' a)
}.

Lemma mk_finfun_leP `{DomainOrder} (f : finset (elt*elt)) `{ValidFun _ f} (f' : finfun) :
  (mk_finfun f ≤ f') <->
  (∀ p ∈ f, snd p ≤ fapp f' (fst p)).
Proof.
  split.
  - intros Hle p Hin.
    transitivity (fapp (mk_finfun f) p.1).
    2: by apply finfun_leP.
    apply (mk_app f) ; cbn.
    apply: (image_fun _ _ _ π₂).
    now rewrite finsubsetP.
  - intros Hle.
    apply finfun_leP.
    intros a.
    apply mk_app ; cbn.
    move => ? /imageP /= [x' []] /finsubsetP [? ?] ? ; subst.
    transitivity (fapp f' x'.1) ; auto.
    by apply mon_mon.
Qed.

(** ** Ranking *)

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

  (** ranking and the constructors *)
  ranked_bot (n : nat) : ranked fbot n ;
  ranked_univ (m n : nat) : ranked (funiv m) (S n) ;
  ranked_pi (a : elt) (b : finfun) n : ranked a n -> ranked_fun b n -> ranked (fpi a b) (S n) ;
  ranked_abs (f : finfun) n : ranked_fun f n -> ranked (fabs f) (S n) ;
  ranked_finfun (f : finset (elt*elt)) `{ValidFun _ f} n :
    ∀ p ∈ f, (ranked p.1 n /\ ranked p.2 n) -> ranked_fun (mk_finfun f) (S n) ;

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