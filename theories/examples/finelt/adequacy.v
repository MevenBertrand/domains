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
      Val ctx_empty (σ i) (lookup i Γ)[σ] h.


Lemma ValSub_empty : ValSub ctx_empty null null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) (σ : Sub g) A v (M : Tm 0):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    Val ctx_empty M A[σ] h) ->
    ValSub Γ ρ σ ->
    ValSub (Γ ++ A) (v .: ρ) (M .: σ).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    apply EvalRel_unwk in E0.
    specialize (VS i u0 Vu0 Le0 a0 E0 WT0).
    rewrite renSubst_Tm. asimpl.
    done.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
    rewrite renSubst_Tm. asimpl.
    eapply hyp0; eauto.
Qed.

Definition EqValSub {g} (Γ : Ctx g) (ρ : Env g)
  (σ1 : Sub g) (σ2 : Sub g)  : Prop :=
  forall i,
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a),
      EqVal ctx_empty (σ1 i) (σ2 i) (lookup i Γ)[σ1] h.

Lemma EqValSub_empty : EqValSub ctx_empty null null null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {g} (Γ : Ctx g) (ρ : Env g)
  (σ1 σ2 : Sub g) A v (M1 M2 : Tm 0):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    EqVal ctx_empty M1 M2 A[σ1] h) ->
    EqValSub Γ ρ σ1 σ2 ->
    EqValSub (Γ ++ A) (v .: ρ) (M1 .: σ1) (M2 .: σ2).
Proof.
  intros hyp0 VS.
  unfold ValSub in *.
  move=> i u0 Vu0 Le0 a0 E0 WT0.
  destruct i as [i|].
  - (* succ case *) 
    cbn in *. asimpl.
    rewrite renSubst_Tm. asimpl.
    apply EvalRel_unwk in E0.
    eapply VS; eauto.
  - (* zero case *)
    cbn in *. asimpl.
    rewrite renSubst_Tm. asimpl.
    apply EvalRel_unwk in E0.
    eapply hyp0; eauto.
Qed.    

Definition semantic_typing {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :=
  forall ρ σ (TS : typing_subst ctx_empty σ Γ) (F : fits Γ ρ)
    (VS : ValSub Γ ρ σ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    Val ctx_empty M[σ] A[σ] WT.
Definition semantic_conv2 {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ σ1 σ2 (TS1 : typing_subst ctx_empty σ1 Γ)
            (TS2 : typing_subst ctx_empty σ2 Γ)
    (F : fits Γ ρ)
    (VS : EqValSub Γ ρ σ1 σ2),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    EqVal ctx_empty M[σ1] N[σ2] A[σ1] WT.

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

Definition semantic_conv {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ σ (TS : typing_subst ctx_empty σ Γ) (F : fits Γ ρ)
    (VS : ValSub Γ ρ σ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    EqVal ctx_empty M[σ] N[σ] A[σ] WT.


(* ------------------ semantic typing rules ----------- *)

Section SemanticTyping.

Local Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A) (at level 70, only printing).
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
  conv Γ A B (Core.tuniv i) ->
  semantic_typing Γ M A -> 
  semantic_conv2 Γ A B (Core.tuniv i) ->
(* ------------------------- *)
  semantic_typing Γ M B.
Proof.
  move=> T1 C2 h1 h2. 
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
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_typing Γ A (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) B (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) M B ->
(* ------------------------- *)
  semantic_typing Γ (Core.abs A M) (Core.tpi A B).
Admitted.

Lemma st_app A B N M i : 
  typing Γ A (Core.tuniv i) -> 
  typing (Γ ++ A) B (Core.tuniv i) -> 
  typing Γ M (Core.tpi A B) -> 
  typing Γ N A  -> 
  semantic_typing Γ A (Core.tuniv i) -> 
  semantic_typing (Γ ++ A) B (Core.tuniv i) -> 
  semantic_typing Γ M (Core.tpi A B) -> 
  semantic_typing Γ N A  -> 
(* ------------------------ *)
  semantic_typing Γ (Core.app M N) B[N..].
Proof.
  move=> T1 T2 T3 T4 h1 h2 h3 h4 (* h1' h2' h3' h4' *). 
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

(* t_nat: ctx Γ ⟹ tnat : tuniv 0 *)
Lemma st_nat :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tnat (Core.tuniv 0).
Proof. Admitted.

(* t_zero: ctx Γ ⟹ zero : tnat *)
Lemma st_zero :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.zero Core.tnat.
Proof. Admitted.

(* t_succ: M : tnat ⟹ succ M : tnat *)
Lemma st_succ M :
  typing Γ M Core.tnat ->
  semantic_typing Γ M Core.tnat ->
(* ------------------------- *)
  semantic_typing Γ (Core.succ M) Core.tnat.
Proof. Admitted.

(* t_nrec: T : (Γ ++ tnat) ⊢ tuniv i, M0 : T[zero..], M1 : tpi tnat (tpi T U⟨↑⟩)
   ⟹ nrec T M0 M1 : tpi tnat T *)
Lemma st_nrec (T U : Tm (S n)) M0 M1 i :
  typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  typing Γ M0 (T[Core.zero..]) ->
  U = T[rho] ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
(* ------------------------- *)
  semantic_typing Γ (Core.nrec T M0 M1) (Core.tpi Core.tnat T).
Proof. Admitted.

(* t_tpi: A : tuniv i, (Γ ++ A) ⊢ B : tuniv i ⟹ tpi A B : tuniv i *)
Lemma st_tpi A B i :
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_typing Γ A (Core.tuniv i) ->
  semantic_typing (Γ ++ A) B (Core.tuniv i) ->
(* ------------------------- *)
  semantic_typing Γ (Core.tpi A B) (Core.tuniv i).
Proof. Admitted.

(* t_cum: A : tuniv i, i < j ⟹ A : tuniv j *)
Lemma st_cum A i j :
  typing Γ A (Core.tuniv i) ->
  (i < j)%nat ->
  semantic_typing Γ A (Core.tuniv i) ->
(* ------------------------- *)
  semantic_typing Γ A (Core.tuniv j).
Proof. Admitted.

(* t_univ: ctx Γ, i < j ⟹ tuniv i : tuniv j *)
Lemma st_univ i j :
  ctx Γ ->
  (i < j)%nat ->
(* ------------------------- *)
  semantic_typing Γ (Core.tuniv i) (Core.tuniv j).
Proof. Admitted.


(* -------- semantic conversion rules -------- *)

(* c_conv: M ≡ N : A, A ≡ B : tuniv i ⟹ M ≡ N : B *)
Lemma sc_conv M N A B i :
  conv Γ M N A ->
  conv Γ A B (Core.tuniv i) ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ A B (Core.tuniv i) ->
(* ------------------------- *)
  semantic_conv2 Γ M N B.
Proof. Admitted.

(* c_refl: M : A ⟹ M ≡ M : A *)
Lemma sc_refl M A :
  typing Γ M A ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ M M A.
Proof. Admitted.

(* c_sym: M ≡ N : A ⟹ N ≡ M : A *)
Lemma sc_sym M N A :
  conv Γ M N A ->
  semantic_conv2 Γ M N A ->
(* ------------------------- *)
  semantic_conv2 Γ N M A.
Proof. Admitted.

(* c_trans: M ≡ N : A, N ≡ P : A ⟹ M ≡ P : A *)
Lemma sc_trans M N P A :
  conv Γ M N A ->
  conv Γ N P A ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ N P A ->
(* ------------------------- *)
  semantic_conv2 Γ M P A.
Proof. Admitted.

(* c_app1: N ≡ N' : (tpi A B), M : A ⟹ app N M ≡ app N' M : B[M..] *)
Lemma sc_app1 A B N N' M i :
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  conv Γ N N' (Core.tpi A B) ->
  typing Γ M A ->
  semantic_typing Γ A (Core.tuniv i) ->
  semantic_typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_conv2 Γ N N' (Core.tpi A B) ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N' M) B[M..].
Proof. Admitted.

(* c_app2: N : (tpi A B), M ≡ M' : A ⟹ app N M ≡ app N M' : B[M..] *)
Lemma sc_app2 A B N M M' i :
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  typing Γ N (Core.tpi A B) ->
  conv Γ M M' A ->
  semantic_typing Γ A (Core.tuniv i) ->
  semantic_typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_conv2 Γ M M' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N M') B[M..].
Proof. Admitted.

(* c_beta: A, B, body N, arg M ⟹ app (abs A N) M ≡ N[M..] : B[M..] *)
Lemma sc_beta A B M N i :
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  typing (Γ ++ A) N B ->
  typing Γ M A ->
  semantic_typing Γ A (Core.tuniv i) ->
  semantic_typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_typing (Γ ++ A) N B ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.abs A N) M) N[M..] B[M..].
Proof. Admitted.

(* c_eta: function extensionality *)
Lemma sc_eta A B (N N' : Tm n) i :
  typing Γ A (Core.tuniv i) ->
  typing (Γ ++ A) B (Core.tuniv i) ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
  semantic_typing Γ A (Core.tuniv i) ->
  semantic_typing (Γ ++ A) B (Core.tuniv i) ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_typing Γ N' (Core.tpi A B) ->
  semantic_conv2 (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                          (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
(* ------------------------- *)
  semantic_conv2 Γ N N' (Core.tpi A B).
Proof. Admitted.

(* c_nrec_Z: app (nrec T M0 M1) zero ≡ M0 : T[zero..] *)
Lemma sc_nrec_Z M0 M1 (T : Tm (S n)) i :
  typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) Core.zero) M0 T[Core.zero..].
Proof. Admitted.

(* c_nrec_S: app (nrec T M0 M1) (succ n) ≡ app (app M1 n) (app (nrec ...) n) : T[(succ n)..] *)
Lemma sc_nrec_S (T : Tm (S n)) M0 M1 (e : Tm n) i :
  typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T (Core.tuniv i) ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) (Core.succ e))
                   (Core.app (Core.app M1 e) (Core.app (Core.nrec T M0 M1) e))
                   T[(Core.succ e)..].
Proof. Admitted.

(* c_tuniv: M ≡ N : tuniv i, i < j ⟹ M ≡ N : tuniv j *)
Lemma sc_tuniv M N i j :
  conv Γ M N (Core.tuniv i) ->
  (i < j)%nat ->
  semantic_conv2 Γ M N (Core.tuniv i) ->
(* ------------------------- *)
  semantic_conv2 Γ M N (Core.tuniv j).
Proof. Admitted.

(* c_tpi: A0 ≡ A1 : tuniv i, B0 ≡ B1 : tuniv i ⟹ tpi A0 B0 ≡ tpi A1 B1 : tuniv i *)
Lemma sc_tpi A0 A1 (B0 B1 : Tm (S n)) i :
  conv Γ A0 A1 (Core.tuniv i) ->
  conv (Γ ++ A0) B0 B1 (Core.tuniv i) ->
  semantic_conv2 Γ A0 A1 (Core.tuniv i) ->
  semantic_conv2 (Γ ++ A0) B0 B1 (Core.tuniv i) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) (Core.tuniv i).
Proof. Admitted.


End SemanticTyping.


(*
------------------------------------------------------------------------
-- Part 6: Main mutual block — adequacySub2 / adequacyEqSub2 /
--                              adequacyConvSub2
--
-- These three theorems form the main "Theorem 2" of the paper
-- (p.660) and the central mutual block of Adequacy2.agda.  In the
-- Agda development they are a single TERMINATING mutual block; here
-- we state them as Theorems with proofs left admitted, and use the
-- previously defined semantic_typing / semantic_conv / semantic_conv2
-- to express their (unfolded) conclusions.
--
-- The Agda hypotheses translate as follows (with the source context
-- H instantiated to ctx_empty, i.e. closing substitutions):
--
--     HasType G M A             ≈  typing Γ M A
--     ConvTm   G M N A          ≈  conv   Γ M N A
--     σ : Sub h g               ≈  σ : Sub g  (= fin g -> Tm 0)
--     ρ : EnvApprox g           ≈  ρ : Env g
--     CoherentEnv ρ             ≈  valid_env ρ   (from fits_valid_env)
--     ValidSub2 H G σ ρ         ≈  ValSub Γ ρ σ
--     ValidConvSub2 H G σ σ' ρ  ≈  EqValSub Γ ρ σ σ'
--     Fits G ρ                  ≈  fits Γ ρ
--     WtSub H G σ               ≈  typing_subst ctx_empty σ Γ
--     WtConvSub H G σ σ'        ≈  (no Rocq counterpart yet — would
--                                  be a pointwise conv predicate)
--     WfCtx H                   ≈  trivial (H = ctx_empty)
--     FinMem u a                ≈  wt u a
--     Val2 H M[σ] A[σ] u a      ≈  Val M[σ] A[σ] (h : wt u a)
--     EqVal2 H M[σ] N[σ] A[σ]   ≈  EqVal M[σ] N[σ] A[σ] (h : wt u a)
------------------------------------------------------------------------
*)

(* adequacySub2 (Adequacy2.agda, p.660 Theorem 2 part 4):

       HasType G M A
     → CoherentEnv ρ, ValidSub2 H G σ ρ, Fits G ρ,
       WtSub H G σ, WfCtx H
     → (u : FinEl)  EvalRel M ρ u
     → (a : FinEl)  EvalRel A ρ a   FinMem u a
     → Val2 H M[σ] A[σ] u a

   Rocq: well-typed terms are semantically typed.                *)
Fixpoint adequacySub {g} (Γ : Ctx g) (M A : Tm g) :
  typing Γ M A -> semantic_typing Γ M A
with adequacyEqSub {g} (Γ : Ctx g) (M N A : Tm g) :
  conv Γ M N A -> semantic_conv2 Γ M N A.
Proof. 
  - move=> h. dependent destruction h.
    + eapply st_var; eauto.
    + eapply st_conv; eauto.
    + eapply st_abs; eauto.
    + eapply st_app; eauto.
    + eapply st_nat; eauto.
    + eapply st_zero; eauto.
    + eapply st_succ; eauto.
    + eapply st_nrec; eauto.
    + eapply st_tpi; eauto.
    + eapply st_cum; eauto.
    + eapply st_univ; eauto.
  - move=> h. dependent destruction h.
    + eapply sc_conv; eauto. 
    + eapply sc_refl; eauto. 
    + eapply sc_sym; eauto.
    + eapply sc_trans; eauto.
    + eapply sc_app1; eauto. 
    + eapply sc_app2; eauto.
    + eapply sc_beta; eauto.
    + eapply sc_eta; eauto.
    + eapply sc_nrec_Z; eauto.
    + eapply sc_nrec_S; eauto.
    + eapply sc_tuniv; eauto.
    + eapply sc_tpi; eauto.
Qed.

Corollary typing_adequacy (M A : Tm 0) u a (h : wt u a) :
  typing ctx_empty M A -> EvalRel M null u -> EvalRel A null a ->
  Val ctx_empty M A h.
Proof.
  move=> T EM EA.
  eapply adequacySub in T.
  unfold semantic_typing in T.
  specialize (T null null (typing_subst_null ctx_empty)
             fits_empty ValSub_empty).
  replace M[null] with M in T. replace A[null] with A in T.
  eapply T; eauto.
  auto_unfold. rewrite idSubst_Tm; eauto. done.
  auto_unfold. rewrite idSubst_Tm; eauto. done.
Qed.


Corollary conv_adequacy (M N A : Tm 0) u a (h : wt u a) :
  conv ctx_empty M N A -> EvalRel M null u -> EvalRel N null u ->
  EvalRel A null a ->
  EqVal ctx_empty M N A h.
Proof.
  move=> T EM EN EA. 
  eapply adequacyEqSub in T.
  unfold semantic_conv2 in T.
  specialize (T null null null
                (typing_subst_null ctx_empty)
                (typing_subst_null ctx_empty)
             fits_empty EqValSub_empty).
  replace M[null] with M in T.
  replace N[null] with N in T.
  replace A[null] with A in T.
  eapply T; eauto.
  auto_unfold. rewrite idSubst_Tm; eauto. done.
  auto_unfold. rewrite idSubst_Tm; eauto. done.
  auto_unfold. rewrite idSubst_Tm; eauto. done.
Qed.

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

   The Agda proof applies adequacyEqSub2 at botEnv with idSub (the
   n-ary identity substitution) and reads the result off through
   substExpr-id.  Our adequacyEqSub2 is defined for *closing*
   substitutions only (σ : fin g → Tm 0), so the same argument runs
   verbatim for closed Γ (i.e. n = 0, where idSub coincides with the
   empty closing substitution null).  The n > 0 case requires
   generalizing adequacyEqSub2 to non-empty target contexts and is
   admitted. *)
Lemma piConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) i :
  conv Γ A0 (Core.tpi B1 F1) (Core.tuniv i) ->
  exists B0 F0,
    HeadRed A0 (Core.tpi B0 F0)
    /\ conv Γ B0 B1 (Core.tuniv i)
    /\ conv (Γ ++ B0) F0 F1 (Core.tuniv i).
Proof.
  move=> Cv.
  destruct n as [|n].
  2: { (* n > 0: needs adequacy at non-empty target context. *) admit. }

  (* n = 0: Γ must be ctx_empty, so adequacyEqSub2 applies directly. *)
  dependent destruction Γ.

  (* Setup: ρ = null, σ = null (the unique closing sub from ctx_empty). *)
  pose ρ : Env 0 := null.
  pose σ : Sub 0 := null.
  have Fρ  : fits ctx_empty ρ.
  { exact fits_empty. }
  have TSσ : typing_subst ctx_empty σ ctx_empty.
  { apply typing_subst_null. }
  have VSσ : ValSub ctx_empty ρ σ.
  { unfold ValSub. by case. }

  (* Pick the witness u = (tpi bot nil) at type (tuniv i). *)
  pose u := tpi bot nil.
  have Vpi : valid (tpi bot nil) by [].
  have Hwt : wt u (tuniv i).
  { rewrite /u. apply: (@wt_tpi bot nil i).
    - move=> ?? IN; inversion IN.
    - move=> ?? IN; inversion IN.
    - apply: wt_bot; done.
    - exact: Vpi. }

  (* EvalRel for (tpi B1 F1) and (transported via conv) for A0. *)
  have EvalPi : EvalRel (Core.tpi B1 F1) ρ u.
  { rewrite /u. exact: evalRel_Pi_trivial. }
  have EvA0 : EvalRel A0 ρ u.
  { have IC : InvConv ctx_empty A0 (Core.tpi B1 F1) (Core.tuniv i) ρ.
    { eapply conv_EvalRel; eauto. }
    move: IC => [_ [_ [_ bwd]]]. apply: bwd. exact: EvalPi. }
  have EvUni : EvalRel (Core.tuniv i) ρ (tuniv i).
  { cbn. exact: PeanoNat.Nat.eqb_refl. }
(*
  (* Apply adequacyEqSub2 to the conversion at the chosen witness. *)
  pose proof
    (@adequacyEqSub2 0 ctx_empty A0 (Core.tpi B1 F1) (Core.tuniv i) Cv
       ρ σ TSσ Fρ VSσ
       u (tuniv i) Hwt EvA0 EvUni) as ev2.
  (* ev2 : EqVal A0[σ] (tpi B1 F1)[σ] (tuniv i)[σ] Hwt *)

  (* σ = null and the terms are closed, so M[σ] reduces to M. *)
  asimpl in ev2.

  (* EqVal at (tuniv i) unfolds to (ValTy /\ ValTy /\ EqValTy);
     EqValTy at u = (tpi bot nil) exposes the head reductions and
     the domain/codomain conversions. *)
  cbn in ev2. 
  destruct ev2 as [_ [_ EQTy]].
  cbn in EQTy.
  destruct EQTy as [_ [_ ExA]].
  destruct ExA as [A [B [HRA0 [A' [B' rest]]]]].
  destruct rest as [HRpi [convA [convB _]]].

  (* HRpi : HeadRed (tpi B1 F1) (tpi A' B') — Pi is a head-normal
     form, so A' = B1 and B' = F1 by determinacy. *)
  have [EQ1 EQ2] : A' = B1 /\ B' = F1.
  { eapply HeadRed_tpi_det; first exact: HRpi. exact: ms_refl. }
  subst A' B'.

  exists A, B. by repeat split. *)
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

