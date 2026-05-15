(* See Validity.agda *)

From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import syntax.syntax.
Require Import syntax.typing.
Require Import syntax.relations.


Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

(* single-step head reduction *)
Inductive HeadRed1 (n : nat) : Tm n -> Tm n -> Prop := 
 | hr_beta A M N :
    HeadRed1 (app (abs A M) N) M[N..]
 | hr_app  M1 M2 N :
    HeadRed1 M1 M2 -> 
    HeadRed1 (app M1 N) (app M2 N).

(* reflexive-transitive closure *)
Definition HeadRed (n : nat) : Tm n -> Tm n -> Prop := 
  multi (@HeadRed1 n).

Lemma ms_app {n:nat} (M1 M2 : Tm (S n)) N :
   HeadRed M1 M2 -> HeadRed (app M1 N) (app M2 N).
Proof.
  intro h.
  induction h; eauto. eapply ms_refl.
  eapply ms_trans; eauto. eapply hr_app; eauto.
Qed.

Lemma HeadRed1_det (n:nat) (M N P : Tm n) : 
  HeadRed1 M N -> HeadRed1 M P -> N = P.
Proof.
  move=> h1 h2.
  induction M.
  all: inversion h1; inversion h2; subst. 
  - inversion H3. done.
  - inversion H5.
  - inversion H2.
  - rewrite (@IHM1 M3 M5) ; eauto.
Qed.

Require Import findom.
Require Import types.
Require Import raw_semantics.
Require Import typing_semantics.
Require Import eval_substitution.


Import Raw.
    

(* Logical relation, defined by induction on (semantic type) a.
   We only need it for closed terms, so dropping the context and 
   specializing M's scope to 0.

   Swapped the order of arguments as we are pattern matching on 
   u and a to define sets of term * type pairs.

   As a is "more defined" this set becomes smaller. When we don't 
   know anything, i.e. a is bot, then we have the total set.

   If Val u a M A (h: wt u a) holds 
   then we know that 
     null |- M : A
 *)

(* Inversion lemmas for wt *)
Lemma wt_tpi_dom (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) (tuniv j) ->
  wt a (tuniv j).
move=>h. inversion h. done. Defined.
Lemma wt_tpi_cod_key (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) (tuniv j) ->
  (forall ui vi : elt, In (ui, vi) g -> wt ui a).
move=>h. inversion h. done. Defined.
Lemma wt_tpi_cod_elt (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) (tuniv j) ->
  (forall ui vi : elt, In (ui, vi) g -> wt vi (tuniv j)).
move=>h. inversion h. done. Defined.

Lemma wt_abs_key (a : elt) (f g : list (elt * elt)) :
  wt (abs f) (tpi a g) -> 
  (forall ui vi w : elt, In (ui, vi) f -> app g ui = Some w -> wt ui a).
move=>h. inversion h. done. Defined.

Lemma wt_abs_elt (a : elt) (f g : list (elt * elt)) :
  wt (abs f) (tpi a g) -> 
  (forall ui vi w : elt, In (ui, vi) f -> app g ui = Some w -> wt vi w).
move=>h. inversion h. done. Defined.

Lemma wt_succ_inv u:
  wt (succ u) tnat -> wt u tnat.
move=>h. inversion h. done. Defined.

(* Unary logical relation *)
Fixpoint Val (u : elt) (a: elt) 
  (M : Tm 0) (A : Tm 0) (h : wt u a) { struct h } : Prop := 
    typing ctx_empty M A 
    /\ 
      (match a return wt u _ -> Prop with 

      | bot => fun h => True
                
      | tuniv i => fun h =>
          HeadRed A (Core.tuniv i) /\
          (* This is ValTy *)
          (match u return wt _ (tuniv i) -> Prop with 
            | bot => fun h => True 
               
            | tpi b g => fun (h : wt (tpi b g) (tuniv i)) =>
              exists A1 B1, HeadRed M (Core.tpi A1 B1) 
              /\ @Val b (tuniv i) A1 (Core.tuniv i) (wt_tpi_dom h)
              /\ forall u v (IN : In (u,v) g) (M1 : Tm 0),
                  (* take related arguments *)
                  @Val u b M1 A1 (wt_tpi_cod_key h IN) ->
                  (* to related results *)
                  @Val v (tuniv i) B1[M1..] (Core.tuniv i)
                       (wt_tpi_cod_elt h IN)

            | tuniv j => fun h => 
              HeadRed M (Core.tuniv j)  

            | tnat => fun h =>
              HeadRed M (Core.tnat)  

            | _ => fun h => False 
            end) h

      | tpi b f => fun h => 
           exists A1 B1, HeadRed A (Core.tpi A1 B1) /\
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True 
           | abs g => fun (h : wt (abs g) (tpi b f)) => 
             exists M1, HeadRed M (Core.abs A1 M1) 
                 /\ forall u v (IN: In (u,v) g) w 
                     (APPf : app f u = Some w) (N : Tm 0), 
                 (* take related arguments *)
                 @Val u b N A1 (wt_abs_key h IN APPf) ->
                 (* to related results *)
                 @Val v w M1[N..] B1[N..]
                       (wt_abs_elt h IN APPf)

           | _ => fun h => False 
            end) h

      | tnat => fun h =>
          HeadRed A (Core.tnat) /\
          (match u return wt _ tnat -> Prop with 
               | zero => fun h => 
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat) => 
                 exists M1, HeadRed M (Core.succ M1)
                 /\ @Val v tnat M1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h.

(* Binary logical relation *)
Fixpoint EqVal (u : elt) (a: elt) 
  (M : Tm 0) (N : Tm 0) (A : Tm 0) (h : wt u a) { struct h } : Prop := 
    conv ctx_empty M N A 
    /\ 
      (match a return wt u _ -> Prop with 

      | bot => fun h => True
                
      | tuniv i => fun h =>
          HeadRed A (Core.tuniv i) /\
          (* This is ValTy *)
          (match u return wt _ (tuniv i) -> Prop with 
            | bot => fun h => True 
               
            | tpi b g => fun (h : wt (tpi b g) (tuniv i)) =>
              exists A1 B1, HeadRed M (Core.tpi A1 B1) 
              /\ exists A2 B2, HeadRed N (Core.tpi A2 B2)
              /\ @EqVal b (tuniv i) A1 A2 (Core.tuniv i) (wt_tpi_dom h)
              /\ forall u v (IN : In (u,v) g) (N1 N2 : Tm 0),
                  (* take related arguments *)
                  @EqVal u b N1 N2 A1 (wt_tpi_cod_key h IN) ->
                  (* to related results *)
                  @EqVal v (tuniv i) B1[N1..] B2[N2..] (Core.tuniv i)
                       (wt_tpi_cod_elt h IN)

            | tuniv j => fun h => 
              HeadRed M (Core.tuniv j)  

            | tnat => fun h =>
              HeadRed M (Core.tnat)  

            | _ => fun h => False 
            end) h

      | tpi b f => fun h => 
           exists A1 B1, HeadRed A (Core.tpi A1 B1) /\
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True 
           | abs g => fun (h : wt (abs g) (tpi b f)) => 
             exists M1, HeadRed M (Core.abs A1 M1) 
             /\ exists N1, HeadRed N (Core.abs A1 N1)
             /\ forall u v (IN: In (u,v) g) w 
                     (APPf : app f u = Some w) (M2 N2 : Tm 0), 
                 (* take related arguments *)
                 @EqVal u b M2 N2 A1 (wt_abs_key h IN APPf) ->
                 (* to related results *)
                 @EqVal v w M1[M2..] N1[N2..] B1[M2..]
                       (wt_abs_elt h IN APPf)

           | _ => fun h => False 
            end) h

      | tnat => fun h =>
          HeadRed A (Core.tnat) /\
          (match u return wt _ tnat -> Prop with 
               | zero => fun h => 
                 HeadRed M Core.zero
                 /\ HeadRed N Core.zero
               | succ v => fun (h : wt (succ v) tnat) => 
                 exists M1, HeadRed M (Core.succ M1)
                 /\ exists N1, HeadRed N (Core.succ N1)
                 /\ @EqVal v tnat M1 N1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h.


(* All terms in the relation have the right type. *)
Fixpoint Val_typing (u : elt) (a: elt) 
  (M : Tm 0) (A : Tm 0) (h : wt u a) :
  Val M A h -> typing ctx_empty M A.
Proof.
  dependent destruction h.
  all: move=> [h1 h2].
  all: done.
Qed.



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
    eapply VS; eauto.
    eapply EvalRel_unwk in E0; auto.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
Qed.    

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
    eapply VS; eauto.
    eapply EvalRel_unwk in E0; auto.
  - (* zero case *)
    cbn in *. asimpl.
    eapply EvalRel_unwk in E0; auto.
Qed.    

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

Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A) (at level 70).
Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv Γ M N A) (at level 70).

(* ------------------ semantic typing rules ----------- *)

Section SemanticTyping.

Variable (n:nat) (Γ : Ctx n).

Lemma st_var (x : fin n) : 
  ctx Γ -> 
(* ------------------------- *)
  Γ ⊨ var x ∈ lookup x Γ.
Proof.
  move=> h. 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  cbn in *. move: Ex => [Vu1 Le1].
  specialize (VS x).
  eapply VS; eauto.
Qed.

Lemma st_conv M A B i : 
  Γ ⊨ M ∈ A -> 
  Γ ⊨ A ≡ B ∈ Core.tuniv i ->
(* ------------------------- *)
  Γ ⊨ M ∈ B.
Proof.
  move=> h1 h2. 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  specialize (h1 ρ σ TS FR VS).
  specialize (h2 ρ σ TS FR VS).
Admitted.  

Lemma st_abs A B M i : 
  Γ ⊨ A ∈ Core.tuniv i -> 
  Γ ++ A ⊨ B ∈ Core.tuniv i -> 
  Γ ++ A ⊨ M ∈ B ->
(* ------------------------- *)
  Γ ⊨ Core.abs A M ∈ Core.tpi A B.
Admitted.

Lemma st_app A B N M i : 
(*  Γ |- A ∈ Core.tuniv i -> 
  Γ ++ A |- B ∈ Core.tuniv i -> 
  Γ |- M ∈ (Core.tpi A B) -> 
  Γ |- N ∈ A  ->  *)
  Γ ⊨ A ∈ Core.tuniv i -> 
  Γ ++ A ⊨ B ∈ Core.tuniv i -> 
  Γ ⊨ M ∈ (Core.tpi A B) -> 
  Γ ⊨ N ∈ A  -> 
(* ------------------------ *)
  Γ ⊨ Core.app M N ∈ B[N..].
Proof.
  move=> h1 h2 h3 h4 (* h1' h2' h3' h4' *). 
  move=> ρ σ TS FR VS u1 a1 WT1 Ex ER.
  specialize (h1 ρ σ TS FR VS).
(*   specialize (h2 ρ σ TS FR VS). *)
  specialize (h3 ρ σ TS FR VS).
  specialize (h4 ρ σ TS FR VS).
  cbn.
  cbn in Ex.
  destruct (is_bot u1) eqn:HB. 
  - (* EvalRel (app M N) is bot *)
    admit.
  - (* EvalRel (app M N) comes from an application *)
    move: Ex => [u0 [EM EN]].    
    move: (h3 (u0 ↦ u1)) => h3'.
    (* we need to get a type for (u0 |-> u1). *)
Admitted.
 

End SemanticTyping.


 
(* 
  -- Main bundled adequacy theorem
  adequacySub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->       (* syntax.typing *)
    (sigma : Sub h g) -> 
    (rho : EnvApprox g) ->  (* Env *)
    CoherentEnv rho ->  (* valid_env *)
    ValidSub2 H G sigma rho -> 
    Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    Val2 H (substExpr sigma M) (substExpr sigma A) u a

  -- Bundled adequacy for conversion
  adequacyEqSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M N A : Expr g} ->
    ConvTm G M N A ->
    (sigma : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho -> ValidSub2 H G sigma rho -> Fits G rho ->
    WtSub H G sigma -> WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A) u a

  -- Two-substitution adequacy
  adequacyConvSub2 : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {M A : Expr g} ->
    HasType G M A ->
    (sigma sigma' : Sub h g) -> (rho : EnvApprox g) ->
    CoherentEnv rho ->
    ValidSub2 H G sigma rho -> ValidSub2 H G sigma' rho ->
    ValidConvSub2 H G sigma sigma' rho ->
    Fits G rho ->
    WtSub H G sigma -> WtSub H G sigma' ->
    WtConvSub H G sigma sigma' ->
    WfCtx H ->
    (u : FinEl) -> EvalRel M rho u ->
    (a : FinEl) -> EvalRel A rho a -> FinMem u a ->
    EqVal2 H (substExpr sigma M) (substExpr sigma' M) (substExpr sigma A) u a

*)



  
