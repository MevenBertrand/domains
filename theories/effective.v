(** * domains.effective: Effective preorders: those having enumerable carrier and decidable order *)
From Stdlib Require Import Relations ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories.all preord sets finsets esets.

(** ** Effective preorders *)

(** We define the notion of "effective" preorders: those
  for which the order relation is decidable and the
  members of the preorder are enumerable.
  *)

#[primitive]HB.mixin Record IsEnum T of poset T := {
  enum : eset T ;
  enumP : forall x : T, x ∈ enum ;
}.

#[short(type="EffPoset")]
HB.structure Definition eff_poset := { T of dec_poset T & IsEnum T}.

(** ** Decidability *)

#[deprecated(note="use finset_in_dec directly")]Lemma
  eff_in_dec {A:EffPoset} (M:finset A) (x:A) : Decision (x ∈ M).
Proof.
  intros. apply: finset_in_dec.
Qed.

(** ** Instances *)

(** *** Natural numbers *)

Program Definition _NatEnum := IsEnum.Build nat (efun (fun n => Some n)) _.
Next Obligation.
  apply esetP.
  now eexists.
Qed.

HB.instance Definition _ := _NatEnum.

(** *** Terminal preorder *)

Program Definition _EffUnit := IsEnum.Build unit (single tt) _.
Next Obligation.
  rewrite singleP.
  ext.
Qed.

HB.instance Definition _ := _EffUnit.

(** *** Binary product *)

Program Definition _ProdEnum (A B:EffPoset) := IsEnum.Build (A*B) (eprod enum enum) _.
Next Obligation.
  rewrite eprodP /=.
  split.
  all: apply enumP.
Qed.

HB.instance Definition _ (A B : EffPoset) := _ProdEnum A B.

(** *** Coproduct *)

Program Definition _SumEnum (A B:EffPoset) := IsEnum.Build (A+B) (esum enum enum) _.
Next Obligation.
  destruct x.
  - rewrite esum_leftP.
    apply enumP.
  - rewrite esum_rightP.
    apply enumP. 
Qed.

HB.instance Definition _ (A B : EffPoset) := _SumEnum A B.

(** *** Lift *)

Program Definition _LiftEnum (A : EffPoset) :=
  IsEnum.Build (lift A) (eunion2 (single lift_bot) (image liftup enum)) _.
Next Obligation.
  rewrite eunion2P imageP singleP.
  destruct x ; cbn.
  2: now left.
  right.
  eexists ; split.
  2: easy.
  now apply: enumP.
Qed.

HB.instance Definition _ (A : EffPoset) := _LiftEnum A.

(** ** Semi-decidability of effective existentials *)

Lemma semidec_eff (A:Type) (B : EffPoset) (P:A -> B -> Prop)
  `{forall a b, SemiDec (P a b)} a :
  SemiDec (ex (P a)).
Proof.
  replace (exists y, _) with (∃ y ∈ enum, P a y).
  1: typeclasses eauto.
  ext.
  split ; intros [] ; repeat eexists ; eauto.
  now apply: enumP.
Qed.