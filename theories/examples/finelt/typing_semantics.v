(* See LemmaForTS.agda/TypingSemantics.agda *)

(* Prove that well typed syntax produces well typed interpretations

i.e.  

G |- M : A and fits G ρ implies

    exists u a s.t. u : a, where [[M]]ρ = u and [[A]]ρ = a and 

G |- M = N : A and fits G ρ implies 

    exists u a s.t. u : a, where [[M]]ρ = u = [[N]]ρ

 *)

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

Open Scope syntax_scope.

Import Raw.

(*
------------------------------------------------------------------------
-- Part 1: Fits — well-typed finite environments
------------------------------------------------------------------------
*)

(* Theorem 1 *)

(*  ρ fits Γ if for all x : A in Γ we have 
                [[A]]ρ in Type and ρ(x) in [[A]]ρ. *)



Inductive fits : forall {n} (Γ:Ctx n) (ρ : Env n), Prop := 
  | fits_empty : fits ctx_empty null
  | fits_cons n (Γ : Ctx n) A ρ a u i : 
       typing Γ A (Core.tuniv i) ->
       EvalRel A ρ a ->
       wt a (tuniv i) ->
       wt u a ->
       fits Γ ρ ->
       fits (Γ ++ A) (u .: ρ).

Lemma fits_ctx {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ -> ctx Γ.
Proof.
  induction 1; eauto using ctx.
Qed.

Lemma fits_var {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ -> 
  forall x, 
  exists a i, typing Γ (lookup x Γ) (Core.tuniv i) /\
         EvalRel (lookup x Γ) ρ a /\
         wt a (tuniv i) /\
         wt (ρ x) a.
Proof.
  move=> h.
  induction h. done.
  auto_case.
  + destruct (IHh f) as [b [j [Ht [E [WT1 WT2]]]]].
    exists b. exists j.
    repeat split; auto.
    eapply renaming_typing with (A := Core.tuniv j); 
      eauto with renaming.
    eapply c_cons; eauto using typing_ctx.
    (* need a renaming lemma for EvalRel *)
    (* 
    E : EvalRel A ρ b
    ============================
    EvalRel (⟨↑⟩ A) (u .: ρ) b
     *)
    admit.
Admitted.


Lemma fits_tail {n} (Γ : Ctx n) (ρ : Env n) A u : 
  fits (Γ ++ A) (u .: ρ) -> fits Γ ρ.
move=> h. dependent destruction h; eauto.
Admitted.

Lemma fits_valid_env {n} (Γ : Ctx n)(ρ : Env n) :
  fits Γ ρ -> valid_env ρ.
Proof.
  induction 1.
  eapply valid_nil.
  eapply valid_cons; eauto.
  eapply wt_valid_tm; eauto.
Qed.

Hint Resolve fits_valid_env : valid typing.

Lemma wt_bot_inv u : wt u bot -> u = bot.
Proof. move=> h. inversion h. done. Qed. 

Lemma wt_down u a : wt u a -> forall u', le u' u -> wt u' a.
Proof.
  move=> h. induction h.
  all: move=> u' LE.
  all: destruct u'; try done.
  all: try solve [eapply wt_bot; eauto].
  - cbn in LE. apply Nat.eqb_eq in LE. subst.
    eapply wt_tuniv; eauto.
  - eapply wt_tnat.
  - eapply wt_zero.
  - rewrite le_succ in LE.  eapply wt_succ; eauto.
  - rewrite le_tpi in LE. move: LE => /andP. move=> [h1 h2].
    eapply wt_tpi; eauto.
    + move=> ui vi Inl.
  (* SCW: I don't know how to finish the proof at this 
     point, but I do need this for the theorem below *)
Admitted.

(*
------------------------------------------------------------------------
-- Part 2: Named invariants
------------------------------------------------------------------------
*)

(* Typed M A rho u : 
    exists u' = ⟦M⟧ρ and  u ≤ u' and exists a with u' : a and ⟦A⟧ρ = a
*)
Definition Typed {n:nat} (M : Tm n) (A : Tm n) ρ u := 
  exists u' , exists a', 
    le u u' /\ EvalRel M ρ u' /\ wt u' a' /\ EvalRel A ρ a'.

(* InvTyp G M A rho : for all u ≤ ⟦M⟧ρ, Typed M A rho u *)
Definition InvTyped 
  {n:nat} (Γ: Ctx n) (M : Tm n) (A : Tm n) (ρ : Env n) := 
  forall u, EvalRel M ρ u -> Typed M A ρ u.


(* InvConv G M N A rho : typing for both + bidirectional evaluation *)
Definition InvConv
  {n:nat} (Γ: Ctx n) (M : Tm n) (N: Tm n) (A : Tm n) (ρ : Env n) := 
  InvTyped Γ M A ρ 
  /\ InvTyped Γ N A ρ 
  /\ (forall u, EvalRel M ρ u -> EvalRel N ρ u) 
  /\ (forall u, EvalRel N ρ u -> EvalRel M ρ u). 

Fixpoint typing_EvalRel {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) 
   (h : typing Γ M A) {struct h} :
   forall ρ, fits Γ ρ -> InvTyped Γ M A ρ
with conv_EvalRel {n} (Γ : Ctx n) (M N : Tm n) (A : Tm n) 
   (h : conv Γ M N A) {struct h} :
  forall ρ, fits Γ ρ -> InvConv Γ M N A ρ.
Proof.
  - dependent destruction h.
    all: move=> ρ Fρ.
    + (* var *)
      unfold InvTyped, Typed.
      move=> u E.
      move: E => [Vu Lu].
      move: (fits_var Fρ x) => [a [i [hT [Ea [WT1 WT2]]]]].
      exists u. exists a.
      repeat split; 
      eauto using le_refl, EvalRel_valid with valid.
      eapply wt_down; eauto.
    + eapply typing_EvalRel with (ρ:=ρ) in h; eauto.
      eapply conv_EvalRel with (ρ:=ρ) in H; eauto.
      move: H => [h1 [h2 [h3 h4]]].
      move=> u EM.
      admit.
Admitted.
