(** * domains.effective: Effective preorders: those having enumerable carrier and decidable order *)
From Stdlib Require Import Relations ssreflect ssrfun.
From HB Require Import structures.

Require Import utils.all categories.all preord sets finsets esets.

(** ** Effective preorders *)

(** We define the notion of "effective" preorders: those
  for which the order relation is decidable and the
  members of the preorder are enumerable.
  *)

#[primitive]HB.mixin Record IsPreEnum (T : Type) := {
  enum : eset T ;
}.

#[short(type="PreEnum")]
HB.structure Definition pre_enum := { T of IsPreEnum T }.

#[primitive]HB.mixin Record IsEnum T of pre_enum T := {
  enumP : forall x : T, x ∈ enum ;
}.

#[short(type="EnumTy")]
HB.structure Definition enum_ty := { T of IsPreEnum T & IsEnum T }.

#[short(type="EffPoset")]
HB.structure Definition eff_poset := { T of dec_poset T & enum_ty T}.

(** ** Decidability *)

#[deprecated(note="use finset_in_dec directly")]Lemma
  eff_in_dec {A:EffPoset} (M:finset A) (x:A) : { x ∈ M } + { x ∉ M }.
Proof.
  intros. apply finset_in_dec.
Qed.

(** ** Instances *)

(** *** Natural numbers *)

HB.instance Definition _ := IsPreEnum.Build nat (efun (fun n => Some n)).

Program Definition _NatEnum := IsEnum.Build nat _.
Next Obligation.
  apply esetP.
  now eexists.
Qed.

HB.instance Definition _ := _NatEnum.

(** *** Terminal preorder *)

HB.instance Definition _ := IsPreEnum.Build unit (single tt).

Program Definition _EffUnit := IsEnum.Build unit _.
Next Obligation.
  rewrite singleP.
  ext.
Qed.

HB.instance Definition _ := _EffUnit.

(** *** Binary product *)

HB.instance Definition _ (A B : PreEnum) := IsPreEnum.Build (A*B) (eprod enum enum).

Program Definition _ProdEnum (A B:EnumTy) := IsEnum.Build (A*B) _.
Next Obligation.
  rewrite eprodP /=.
  split.
  all: apply enumP.
Qed.

HB.instance Definition _ (A B : EnumTy) := _ProdEnum A B.

(** *** Coproduct *)

HB.instance Definition _ (A B : PreEnum) := IsPreEnum.Build (A+B) (esum enum enum).

Program Definition _SumEnum (A B:EnumTy) := IsEnum.Build (A+B) _.
Next Obligation.
  destruct x.
  - rewrite esum_leftP.
    apply enumP.
  - rewrite esum_rightP.
    apply enumP. 
Qed.

HB.instance Definition _ (A B : EnumTy) := _SumEnum A B.

(** *** Lift *)

HB.instance Definition _ (A : EffPoset) :=
  IsPreEnum.Build (lift A)
    (eunion2 (single lift_bot) (image liftup enum)).

Program Definition _LiftEnum (A : EffPoset) := IsEnum.Build (lift A) _.
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
  SemiDec (@ex B (P a)).
Proof.
  replace (exists y, _) with (exists y, y ∈ enum /\ P a y).
  1: apply: semidec_ex.
  ext.
  split ; intros [] ; repeat eexists ; eauto.
  now apply: enumP.
Qed.