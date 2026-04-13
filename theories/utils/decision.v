(** * domains.decision: structure for decidability predicates *)
From Stdlib Require Import ssreflect ssrbool Morphisms Relations RelationClasses.
From smpl Require Export Smpl.
From HB Require Import structures.
Require Import notations tactics basics.

Open Scope general_if_scope.

(** ** Decidable predicates *)
(** Inspired from stdpp's *)

Class Decision (P : Prop) := decide : {P} + {~P}.
#[global]Hint Mode Decision ! : typeclass_instances.
#[global]Arguments decide _ {_} : simpl never, assert.

Lemma dec_Some {A P} {Hdec : forall x, Decision (P x)} (a x : A) :
  ((if Hdec a then (Some a) else None) = Some x) <-> (x = a) /\ P a.
Proof.
  split.
  all: destruct (Hdec a) ; intuition (eauto ; congruence).
Qed.

(** ** Decidable equality *)

HB.mixin Record HasEqDec (T:Type) := {#[canonical=no]eqdec : forall x y:T, Decision (x = y)}.

#[short(type="EqTy"),primitive]
HB.structure Definition eqTy := {T of HasEqDec T}.

(** This is better than an instance [EqTyDec (A : EqTy) x y : Decision (x = y :> A)] because
  it will also fire if the carrier type is richer than [EqTy], in which case [apply:] will
  trigger canonical resolution *)
Hint Extern 100 (Decision (_ = _)) => (apply: eqdec) : typeclass_instances. 

(** ** Decidable properties *)

Lemma dec_stable P `{Decision P} : ~ ~ P -> P.
Proof. firstorder. Qed.

Lemma decide_True {A P} `{Decision P} (x y : A) :
  P -> (if decide P then x else y) = x.
Proof. destruct (decide P); tauto. Qed.
Lemma decide_False {A P} `{Decision P} (x y : A) :
  ~P -> (if decide P then x else y) = y.
Proof. destruct (decide P); tauto. Qed.
Lemma decide_ext {A} P Q `{Decision P, Decision Q} (x y : A) :
  (P <-> Q) -> (if decide P then x else y) = (if decide Q then x else y).
Proof. intros [??]. destruct (decide P), (decide Q); tauto. Qed.

Lemma decide_True_pi {P} `{Decision P, !ProofIrrel P} (HP : P) : decide P = left HP.
Proof. destruct (decide P); [|contradiction]. f_equal. apply proof_irrel. Qed.
Lemma decide_False_pi {P} `{Decision P, !ProofIrrel (~P)} (HP : ~P) : decide P = right HP.
Proof. destruct (decide P); [contradiction|]. f_equal. apply proof_irrel. Qed.

  (** The tactic [destruct_decide] destructs a sumbool [dec]. If one of the
components is double negated, it will try to remove the double negation. *)
Tactic Notation "destruct_decide" constr(dec) "as" ident(H) :=
  destruct dec as [H|H];
  try match type of H with
  | ~ ~ _ => apply dec_stable in H
  end.
Tactic Notation "destruct_decide" constr(dec) :=
  let H := fresh in destruct_decide dec as H.

(** The tactic [case_decide] performs case analysis on an arbitrary occurrence
of [decide] or [decide_rel] in the conclusion or hypotheses. *)
Tactic Notation "case_decide" "as" ident(Hd) :=
  match goal with
  | H : context [@decide ?P ?dec] |- _ =>
    destruct_decide (@decide P dec) as Hd
  | |- context [@decide ?P ?dec] =>
    destruct_decide (@decide P dec) as Hd
  end.
Tactic Notation "case_decide" :=
  let H := fresh in case_decide as H.

(** ** Decidable logic *)

#[global]Instance True_dec: Decision True | 1000 := left I.
#[global]Instance False_dec: Decision False | 1000 := right (False_rect False).

Section prop_dec.
  Context {P Q} `(P_dec : Decision P) `(Q_dec : Decision Q).

  #[global]Instance not_dec: Decision (~P).
  Proof. refine (if P_dec then right _ else left _); intuition. Defined.
  #[global]Instance and_dec: Decision (P /\ Q).
  Proof. refine (if P_dec then (if Q_dec then left _ else right _) else right _); intuition. Defined.
  #[global]Instance or_dec: Decision (P \/ Q).
  Proof. refine (if P_dec then left _ else (if Q_dec then left _ else right _)); intuition. Defined.
  #[global]Instance impl_dec: Decision (P -> Q).
  Proof. refine (if P_dec then (if Q_dec then left _ else right _) else left _); intuition. Defined.
End prop_dec.
#[global]Instance iff_dec {P Q} `(P_dec : Decision P) `(Q_dec : Decision Q) :
  Decision (P <-> Q) := and_dec _ _.

(** We can convert decidable propositions to booleans. *)
Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Lemma bool_decide_reflect P `{dec : Decision P} : reflect P (bool_decide P).
Proof. unfold bool_decide. destruct dec; [left|right]; assumption. Qed.

Lemma bool_decide_decide P `{!Decision P} :
  bool_decide P = if decide P then true else false.
Proof. reflexivity. Qed.
Lemma decide_bool_decide P {Hdec: Decision P} {X : Type} (x1 x2 : X):
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Proof. unfold bool_decide, decide. destruct Hdec; reflexivity. Qed.

Tactic Notation "case_bool_decide" "as" ident(Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  | |- context [@bool_decide ?P ?dec] =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" :=
  let H := fresh in case_bool_decide as H.

Lemma bool_decide_spec (P : Prop) {dec : Decision P} : bool_decide P <-> P.
Proof. unfold bool_decide. destruct dec ; simpl ; done. Qed.
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P -> P.
Proof. rewrite bool_decide_spec; trivial. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P -> bool_decide P.
Proof. rewrite bool_decide_spec; trivial. Qed.
Global Hint Resolve bool_decide_pack : core.

Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true <-> P.
Proof. case_bool_decide; intuition discriminate. Qed.
Lemma bool_decide_eq_false (P : Prop) `{Decision P} : bool_decide P = false <-> ~P.
Proof. case_bool_decide; intuition discriminate. Qed.
Lemma bool_decide_ext (P Q : Prop) `{Decision P, Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof. apply decide_ext. Qed.

Lemma bool_decide_eq_true_1 P `{!Decision P}: bool_decide P = true -> P.
Proof. apply bool_decide_eq_true. Qed.
Lemma bool_decide_eq_true_2 P `{!Decision P}: P -> bool_decide P = true.
Proof. apply bool_decide_eq_true. Qed.

Lemma bool_decide_eq_false_1 P `{!Decision P}: bool_decide P = false -> ~P.
Proof. apply bool_decide_eq_false. Qed.
Lemma bool_decide_eq_false_2 P `{!Decision P}: ~P -> bool_decide P = false.
Proof. apply bool_decide_eq_false. Qed.

Lemma bool_decide_True : bool_decide True = true.
Proof. reflexivity. Qed.
Lemma bool_decide_False : bool_decide False = false.
Proof. reflexivity. Qed.
Lemma bool_decide_not P `{Decision P} :
  bool_decide (~ P) = negb (bool_decide P).
Proof. repeat case_bool_decide; intuition. Qed.
Lemma bool_decide_or P Q `{Decision P, Decision Q} :
  bool_decide (P \/ Q) = bool_decide P || bool_decide Q.
Proof. repeat case_bool_decide; intuition. Qed.
Lemma bool_decide_and P Q `{Decision P, Decision Q} :
  bool_decide (P /\ Q) = bool_decide P && bool_decide Q.
Proof. repeat case_bool_decide; intuition. Qed.
Lemma bool_decide_impl P Q `{Decision P, Decision Q} :
  bool_decide (P -> Q) = implb (bool_decide P) (bool_decide Q).
Proof. repeat case_bool_decide; intuition. Qed.