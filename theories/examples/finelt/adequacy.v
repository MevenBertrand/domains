(* Fundamental theorem of the logical relation

   see Adequacy2.adga
 *)


From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.
Require Import utils.all.


Require Import syntax.syntax.
Require Import syntax.typing.
Require Import syntax.relations.

Require Import findom.
Import Raw.
Require Import types.
Require Import typing_semantics.
Require Import raw_semantics.
Require Import raw_validity2.
Require Import eval_substitution.

Open Scope subst_scope.
Import SubstNotations.
Import SyntaxNotations.


(* Fundamental theorem for the logical relation
   
   We want to show that well-typed terms are in the 
   relation.

   - If Γ |- M : A (typing) then


     if Γ |= ρ ~ σ  (ValSub)

          and  Γ |- σ  (typing_subst ctx_empty)

          and  Γ |= ρ  (fits)   


     for all u, a, such that h ∈ u : a   (wt)

        where [[M]]ρ = u  and [[A]]ρ = a  (EvalRel)

     we have

        Val u a M[σ] A[σ] h

   - If Γ |- M = N : A  (conv) 

     and  Γ |- σ1  Γ |- σ2 (typing_subst ctx_empty)

     and  Γ |= ρ  (fits)   

     and [[M]]ρ = u and [[N]]ρ = u and [[A]]ρ = a  (EvalRel)
 
     and h ∈ u : a   (wt)

     and Γ |= ρ ~ σ1 == σ2   (EqValSub)

     then

     EqVal u a M[σ1] N[σ2] A[σ] h
*)


(* A closing substitution: σ *)
Definition Sub m := fin m -> Tm O.

(* A valid closing substitution σ maps every term to one that 
   can be interpreted. *) 
Definition ValSub {g} (Γ : Ctx g) (ρ : Env g) (σ : Sub g)  : Prop := 
  forall i,
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a), 
      Val (σ i) (lookup i Γ)[σ] h. 


Lemma ValSub_empty : ValSub ctx_empty null null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) (σ : Sub g) A v (M : Tm 0): 
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a -> 
    Val M A[σ] h) -> 
    ValSub Γ ρ σ -> 
    ValSub (Γ ++ A) (v .: ρ) (M .: σ). 
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    admit.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
Admitted.

Definition EqValSub {g} (Γ : Ctx g) (ρ : Env g) 
  (σ1 : Sub g) (σ2 : Sub g)  : Prop := 
  forall i, 
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a), 
      EqVal (σ1 i) (σ2 i) (lookup i Γ)[σ1] h. 

Lemma EqValSub_empty : EqValSub ctx_empty null null null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {g} (Γ : Ctx g) (ρ : Env g) 
  (σ1 σ2 : Sub g) A v (M1 M2 : Tm 0): 
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a -> 
    EqVal M1 M2 A[σ1] h) -> 
    EqValSub Γ ρ σ1 σ2 -> 
    EqValSub (Γ ++ A) (v .: ρ) (M1 .: σ1) (M2 .: σ2). 
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    admit.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
Admitted.

Definition semantic_typing {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :=
  forall ρ σ (TS : typing_subst ctx_empty σ Γ) (F : fits Γ ρ) 
    (VS : ValSub Γ ρ σ), 
  forall u a (WT : wt u a), 
    EvalRel M ρ u -> 
    EvalRel A ρ a -> 
    Val M[σ] A[σ] WT.
Definition semantic_conv {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ σ (TS : typing_subst ctx_empty σ Γ) (F : fits Γ ρ)
    (VS : ValSub Γ ρ σ), 
  forall u a (WT : wt u a), 
    EvalRel M ρ u -> 
    EvalRel A ρ a -> 
    EqVal M[σ] N[σ] A[σ] WT. 
Definition semantic_conv2 {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ σ1 σ2 (TS1 : typing_subst ctx_empty σ1 Γ) 
            (TS2 : typing_subst ctx_empty σ2 Γ)
    (F : fits Γ ρ)
    (VS : EqValSub Γ ρ σ1 σ2), 
  forall u a (WT : wt u a), 
    EvalRel M ρ u -> 
    EvalRel A ρ a -> 
    EqVal M[σ1] N[σ2] A[σ1] WT. 

Lemma ValSub_EqValSub {n} (Γ : Ctx n) ρ σ : 
  ValSub Γ ρ σ ->
    EqValSub Γ ρ σ σ.
Proof.
  move=> VS.
  unfold EqValSub.
  move=> i u Vu LE a E1 h.
  specialize (VS i u Vu LE a E1 h).
  eapply Val_EqVal.
  auto.
Qed.

(* ------------------ semantic typing rules ----------- *)

Section SemanticTyping.

Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A) (at level 70, only printing).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv2 Γ M N A) 
                                    (at level 70, only printing).



Variable (n:nat) (Γ : Ctx n).

Lemma st_var (x : fin n) : 
  ctx Γ -> 
(* ------------------------- *)
  semantic_typing Γ (var x) (lookup x Γ).
Proof.
  move=> h. 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  cbn in *. move: Ex => [Vu1 Le1].
  specialize (VS x).
  eapply VS; eauto.
Qed.

Lemma st_conv M A B i : 
  typing Γ M A -> 
  semantic_typing Γ M A -> 
  conv Γ A B (Core.tuniv i) ->
  semantic_conv2 Γ A B (Core.tuniv i) ->
(* ------------------------- *)
  semantic_typing Γ M B.
Proof.
  move=> T1 h1 C2 h2. 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  specialize (h1 ρ σ TS FR VS).
  specialize (h1 _ _ WT1 Ex).
  specialize (h2 ρ σ σ TS TS FR).
  specialize (h2 (ValSub_EqValSub VS)).
  move: (typing_EvalRel T1 FR Ex) => hT1. unfold Typed in hT1.
  destruct hT1 as [v [a [LEu1 [Ev [wta Ea]]]]].
  have EA: EvalRel A ρ a1. { admit. } 
  have hA: wt a1 (tuniv i). { admit. } 
  eapply Val_EqVal_fwd.
  - eapply h1. eauto.
  - eapply EqVal_EqValTy.
    eapply (h2 _ _ hA); eauto.
    cbn. apply Nat.eqb_eq. reflexivity.
Admitted.

Lemma st_abs A B M i : 
  semantic_typing Γ A (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) B (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) M B ->
(* ------------------------- *)
  semantic_typing Γ (Core.abs A M) (Core.tpi A B).
Admitted.

Lemma st_app A B N M i : 
(*  typing Γ A (Core.tuniv i) -> 
  Γ ++ A |- B ∈ Core.tuniv i -> 
  Γ |- M ∈ (Core.tpi A B) -> 
  Γ |- N ∈ A  ->  *)
  semantic_typing Γ A (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) B (Core.tuniv i) -> 
  semantic_typing Γ M (Core.tpi A B) -> 
  semantic_typing Γ N A  -> 
(* ------------------------ *)
  semantic_typing Γ (Core.app M N) B[N..].
Proof.
  move=> h1 h2 h3 h4 (* h1' h2' h3' h4' *). 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  specialize (h1 ρ σ TS FR VS).
  specialize (h3 ρ σ TS FR VS).
  specialize (h4 ρ σ TS FR VS).
  cbn.
  cbn in Ex.
  destruct (Raw.is_bot u1) eqn:HB. 
  - (* EvalRel (app M N) is bot *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    destruct a; try done.
  - (* EvalRel (app M N) comes from an application *)
    move: Ex => [u0 [EM EN]].    
    move: (h3 (u0 ↦ u1)) => h3'.
    (* we need to get a type for (u0 |-> u1). *)
Admitted.
 

End SemanticTyping.


(* ===========================================================
   Translation of PiInjectivity.agda

   Corollary 6 (paper p.661): Pi injectivity.

   If conv Γ A₀ (tpi B₁ F₁) (tuniv i), then there exist B₀, F₀ with
     (1) HeadRed A₀ (tpi B₀ F₀)
     (2) conv Γ B₀ B₁ (tuniv i)
     (3) conv (Γ ++ B₀) F₀ F₁ (tuniv i)

   As a corollary (piInjectivity):
   conv Γ (tpi A₀ B₀) (tpi A₁ B₁) (tuniv i) implies
     conv Γ A₀ A₁ (tuniv i)  and  conv (Γ ++ A₀) B₀ B₁ (tuniv i).

   The full proof in Agda goes through adequacyEqSub2 applied at
   bot_env with idSub. The Coq Val/EqVal relations defined in
   raw_validity2.v live in ctx_empty (after closing substitution),
   so the analogous adequacy is not directly available; piConv
   below is therefore stated and admitted.
   =========================================================== *)

From Stdlib Require Import FunctionalExtensionality.

(* bot_env_lookup: bot_env always returns bot *)
Lemma bot_env_lookup {n} (i : fin n) : (@bot_env n) i = bot.
Proof. unfold bot_env. reflexivity. Qed.

(* bot_env at S n agrees with bot .: bot_env *)
Lemma bot_env_cons {n} : @bot_env (S n) = bot .: bot_env.
Proof. apply functional_extensionality. by case. Qed.

(* bot_env at 0 agrees with null *)
Lemma bot_env_null : @bot_env 0 = null.
Proof. apply functional_extensionality. by case. Qed.

(* fits Γ bot_env: trivially satisfied with a = bot, u = bot at every
   variable. Mirrors botEnv-fits in PiInjectivity.agda. *)
Lemma fits_bot_env {n} (Γ : Ctx n) : ctx Γ -> fits Γ bot_env.
Proof.
  induction 1.
  - rewrite bot_env_null. exact fits_empty.
  - rewrite bot_env_cons.
    eapply (@fits_cons _ _ _ _ bot bot i); eauto.
    + apply EvalRel_bot.
    + apply wt_bot. done.
    + apply wt_bot. done.
Qed.

(* evalRel_Pi_trivial: every Pi type evaluates to (tpi bot nil).
   Mirrors evalRel-Pi-trivial in PiInjectivity.agda. *)
Lemma evalRel_Pi_trivial {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n) :
  EvalRel (Core.tpi A B) ρ (tpi bot nil).
Proof.
  cbn.
  split; first by [].                      (* valid bot *)
  split; first by [].                      (* valid_fun nil *)
  exists 0.
  split.                                    (* wt bot (tuniv 0) *)
  { apply wt_bot. done. }
  split.                                    (* EvalRel A ρ bot *)
  { apply EvalRel_bot. }
  move=> u v IN. inversion IN.              (* EvalRel_fun B ρ bot nil: vacuous *)
Qed.

(* piConv (Corollary 6, parts 1–3):
   From conv Γ A₀ (tpi B₁ F₁) (tuniv i) extract HeadRed A₀ (tpi B₀ F₀)
   and conversions on the domain and codomain.

   In the Agda development the proof goes via adequacyEqSub2 applied at
   bot_env with idSub, unfolding the resulting EqValTyPi2 to read off
   the HeadRed and the conv judgments. The corresponding Coq adequacy
   for the EqVal/Val relations of raw_validity2.v has not yet been
   established, so this lemma is admitted here. *)
Lemma piConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) i :
  conv Γ A0 (Core.tpi B1 F1) (Core.tuniv i) ->
  exists B0 F0,
    HeadRed A0 (Core.tpi B0 F0)
    /\ conv Γ B0 B1 (Core.tuniv i)
    /\ conv (Γ ++ B0) F0 F1 (Core.tuniv i).
Proof.
Admitted.

(* piInjectivity (Corollary): from conv Γ (tpi A₀ B₀) (tpi A₁ B₁) U,
   extract domain and codomain conversions.
   Mirrors piInjectivity in PiInjectivity.agda. *)
Lemma piInjectivity {n} (Γ : Ctx n)
  (A0 A1 : Tm n) (B0 B1 : Tm (S n)) i :
  conv Γ (Core.tpi A0 B0) (Core.tpi A1 B1) (Core.tuniv i) ->
  conv Γ A0 A1 (Core.tuniv i) /\
  conv (Γ ++ A0) B0 B1 (Core.tuniv i).
Proof.
  move=> H.
  destruct (piConv H) as [B0' [F0' [HR [convD convC]]]].
  (* HR : HeadRed (tpi A0 B0) (tpi B0' F0').
     Pi is a head-normal form, so by determinacy of HeadRed on Pi
     we have B0' = A0 and F0' = B0. *)
  have [EQA EQB]: B0' = A0 /\ F0' = B0.
  { eapply HeadRed_tpi_det. exact HR. apply ms_refl. }
  subst B0' F0'.
  split; auto.
Qed.

