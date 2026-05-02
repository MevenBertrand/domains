(* cf. EvalSubstitution.agda *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import syntax.syntax.
Require Import syntax.typing.
Require Import findom.
Require Import types.
Require Import raw_semantics.

Import SyntaxNotations.
Import SubstNotations.

Import Raw.

Open Scope syntax_scope.

(** * renaming preserves evaluation *)

Lemma EvalRel_ren n (M : Tm n) (ρ : Env n) a  
  m  (ξ : fin n -> fin m) (ρ' : Env m) :
  (forall x, ρ x = ρ' (ξ x)) ->
  EvalRel M⟨ξ⟩ ρ' a <-> EvalRel M ρ a.
Proof.
  move: m ξ ρ ρ' a.
  induction M.
  all: move=> m ξ ρ ρ' a EQ.
  all: try done.
  - cbn. rewrite <- EQ. done.
  - cbn. destruct a; try done.
    split. 
    all: move=> [i [a [WT [ER [Vf h]]]]].
    all: exists i, a.
    all: repeat split; eauto.
    all: try rewrite -> IHM1 in ER; try rewrite IHM1; eauto.
    all: move=> ui vi Ini.
    all: specialize (h ui vi Ini).
    all: destruct h as [x [Le [WT2 E2]]].
    all: exists x; repeat split; eauto.       
    rewrite <- (IHM2 _ (up_ren ξ) _ (x .: ρ')). eauto.
    auto_case.
    rewrite (IHM2 _ (up_ren ξ) (x .: ρ)); eauto.
    auto_case.
  - (* app *) cbn.
    destruct (is_bot a); try done.
    split.
    all: move=> [u [E1 E2]].
    all: exists u.
    rewrite -> IHM1 in E1; eauto.
    rewrite -> IHM2 in E2; eauto.
    rewrite -> IHM1 ; eauto.
    rewrite -> IHM2 ; eauto.
  - (* succ *)
    cbn.
    destruct (is_bot a); try done.
    split.
    all: move=> [Va [u [L E1]]].
    all: split; auto.
    all: exists u.
    all: split; auto.
    rewrite -> IHM in E1; eauto.
    rewrite -> IHM ; eauto.
  - (* tpi *)
    cbn.
    destruct a; try done.
    split.
    all: move=> [Va [i [WT [ER h]]]].
    all: split; auto.
    all: exists i.
    all: repeat split; auto.
    all: try rewrite IHM1 in ER; auto; try rewrite IHM1; auto.
    all: destruct h as [Nf|[Vf h]].
    all: try solve [left; eauto].
    all: right; split; eauto.
    all: move=> u v Inl.
    all: destruct (h u v Inl) as [x [Le [WTx E2]]].
    all: exists x; repeat split; auto.
    all: try rewrite IHM2 in E2; auto; try rewrite IHM2; eauto.
    all: auto_case.
Qed.


Lemma EvalRel_wk {n} (M : Tm n) (ρ : Env n) u v :
  EvalRel M ρ u -> EvalRel M⟨↑⟩ (v .: ρ) u.
Proof.
  rewrite -> EvalRel_ren with (ρ:=ρ); eauto.
Qed.

Lemma EvalRel_unwk {n} (M : Tm n) (ρ : Env n) u v :
  EvalRel M⟨↑⟩ (v .: ρ) u -> EvalRel M ρ u.
Proof.
  rewrite <- EvalRel_ren with (ρ:=ρ); eauto.
Qed.

(** * Semantic substitution *)

(*
EvalRel-subst : {h g : Nat} (sigma : Sub h g)
  (M : Expr g) (rho : EnvApprox h) (rho' : EnvApprox g) ->
  CoherentEnv rho ->
  SubRel sigma rho rho' ->
  (u : FinEl) -> EvalRel M rho' u -> EvalRel (substExpr sigma M) rho u
*)

Definition Sub h g := fin h -> Tm g.

Definition SubRel {h g} (σ : Sub h g) (ρ' : Env h) (ρ : Env g) := 
  forall i, EvalRel (σ i) ρ (ρ' i).

Lemma SubRel_lift {h g} (σ : Sub h g) ρ' ρ u :
  SubRel σ ρ ρ' -> 
  valid u -> 
  SubRel (⇑σ) (u .: ρ) (u .: ρ').
Proof.
  move=> SR Vu [f|]. 
  move: (SR f) => h1. 
  eapply EvalRel_wk; eauto.
  split; eauto using le_refl.
Qed.

Lemma EvalRel_subst {m n} (σ : Sub m n) (M : Tm m)
  (ρ : Env m) (ρ' : Env n)  u : 
  valid_env ρ -> valid_env ρ' -> SubRel σ ρ ρ' -> 
  EvalRel M ρ u -> EvalRel M[σ] ρ' u.
Proof.
  move: n σ ρ ρ' u.
  dependent induction M.
  all: rename n_Tm into m; try rename n into n1.
  all: move=> n σ ρ ρ' u Vρ Vρ' SR E.
  all: cbn in *.
  all: try solve [destruct (is_bot u); auto].
  - (* var *)
    move: (SR f) => h1. 
    eapply EvalRel_down; eauto.
  - (* abs *)
    destruct u; try done.
    move: E => [i [a [WT [E1 [Vf F]]]]].
    exists i, a. repeat split; eauto.
    move=> u v Inl.
    move: (F _ _ Inl) => [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, SubRel_lift.
  - (* app *)
    destruct (is_bot u); try done.
    move: E => [a [E1 E2]].
    eauto.
  - (* succ *)
    destruct (is_bot u); try done.
    move: E => [h1 [a [L1 E1]]].
    eauto.
  - (* tpi *)
    destruct u; try done.
    move: E => [Vu [i [WT [E1 [Nf|[Vf h1]]]]]].
    all: split; eauto.
    all: exists i; repeat split; eauto.
    right. repeat split; eauto.
    move=> ui vi Inl.
    destruct (h1 _ _ Inl) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, SubRel_lift.
Qed.

Lemma EvalRel_subst1_backwards {n} 
  (B : Tm (S n)) (M : Tm n) 
  (ρ : Env n) v u : 
  valid_env ρ -> 
  EvalRel M ρ v -> 
  EvalRel B (v .: ρ) u ->
  EvalRel B[M..] ρ u.
Proof.
  move=> Vρ E1 E2.
  eapply EvalRel_subst with (ρ := v .: ρ); 
    eauto using valid_cons, EvalRel_valid.
  unfold SubRel. auto_case.
  eauto using le_refl.
Qed.

(** * MaxRel *)

Definition MaxSubRel {h g} (σ : Sub h g) (ρ' : Env h) (ρ : Env g) := 
  forall i, forall u,  EvalRel (σ i) ρ u -> le u (ρ' i).

Lemma MaxSubRel_lift {h g} (σ : Sub h g) ρ' ρ u :
  MaxSubRel σ ρ ρ' -> 
  valid u -> 
  MaxSubRel (⇑σ) (u .: ρ) (u .: ρ').
Proof.
  move=> SR Vu [f|] v; cbn. 
  move: (SR f v) => h1 h2.
  eapply EvalRel_unwk in h2; eauto.
  eauto using le_refl.
Qed.

Lemma EvalRel_subst_forward_max {m n} (σ : Sub m n) (M : Tm m)
  (ρ : Env m) (ρ' : Env n)  u : 
  valid_env ρ -> valid_env ρ' -> MaxSubRel σ ρ ρ' -> 
  EvalRel M[σ] ρ' u -> EvalRel M ρ u.
Proof.
  move: n σ ρ ρ' u.
  dependent induction M.
  all: rename n_Tm into m; try rename n into n1.
  all: move=> n σ ρ ρ' u Vρ Vρ' SR E.
  all: cbn in *.
  all: try solve [destruct (is_bot u); auto].
  - (* var *)
    move: (SR f) => h1. 
    split; eauto using EvalRel_valid.
  - (* abs *)
    destruct u; try done.
    move: E => [i [a [WT [E1 [Vf F]]]]].
    exists i, a. repeat split; eauto.
    move=> u v Inl.
    move: (F _ _ Inl) => [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, MaxSubRel_lift.
  - (* app *)
    destruct (is_bot u); try done.
    move: E => [a [E1 E2]].
    eauto.
  - (* succ *)
    destruct (is_bot u); try done.
    move: E => [h1 [a [L1 E1]]].
    eauto.
  - (* tpi *)
    destruct u; try done.
    move: E => [Vu [i [WT [E1 [Nf|[Vf h1]]]]]].
    all: split; eauto.
    all: exists i; repeat split; eauto.
    right. repeat split; eauto.
    move=> ui vi Inl.
    destruct (h1 _ _ Inl) as [x [Le [WT2 E2]]].
    have Vx: valid x. eapply wt_valid_tm; eauto.
    exists x. 
    repeat split; eauto.
    eauto using valid_cons, MaxSubRel_lift.
Qed.

(* This lemma needs a lot of extra work *)

Lemma EvalRel_subst1_forward n (M : Tm (S n)) (N : Tm n) (ρ : Env n) u :
  valid_env ρ -> 
  EvalRel M[N..] ρ u -> 
  exists v, EvalRel N ρ v /\ EvalRel M (v .: ρ) u.
Admitted.

