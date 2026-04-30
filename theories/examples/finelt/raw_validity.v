From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require findom.
Require types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Module Raw.
  Include findom.Raw.
  Include types.
End Raw.

Module Valid. 
  Include findom.Valid.

  Definition wt (u a : Valid.elt) := 
    Raw.wt (projT1 u) (projT1 a).

  Definition is_bot (v : Valid.elt) : bool := 
    match projT1 v with 
    | Raw.bot => true
    | _ => false
    end.

  Definition is_abs (v : Valid.elt) : option Valid.finfun := 
    match v with 
    | existT _ (Raw.abs e) Vf => Some (existT _ e Vf)
    | _ => None
    end.

  Definition abs (f : finfun) : elt.
    exists (Raw.abs (projT1 f)).
    destruct f as [f Vf]. 
    eassumption.
  Defined.

  Definition finfun_app (f : finfun) (u : elt) : elt.
    destruct f as [f Vf].
    destruct u as [u Vu].
    destruct (Raw.app f u) eqn:h. 
    { apply Raw.valid_app in h; eauto.
      exists e. exact h. } 
    { assert False.
      destruct (Raw.valid_app_exists Vf Vu) as [w [Aw Vw]].
      rewrite Aw in h. done. done. } 
  Defined.

  Definition graph (f : finfun) : list (elt * elt).
    destruct f as [f Vf].
    move: (Raw.valid_fun_subterms Vf) => h.
    clear Vf.
    move: h.
    induction f as [|[u v]f].
    move=> h. exact nil.
    cbn.
    move=> /andP.
    move=> [/andP h1 h2]. 
    eapply cons. destruct h1 as [Vu Vv].
    eapply ((existT _ u Vu),(existT _ v Vv)).
    eapply IHf; eauto.
  Defined.

  Definition compatible_fun (f g : finfun) : bool := 
    Raw.compatible_fun (projT1 f) (projT1 g).

  Definition coherent_with (f:finfun) : elt * elt -> bool := 
    fun '(u, v) => 
    Raw.coherent_with (projT1 f) (projT1 u, projT1 v).

  Lemma In_graph_def (f : finfun) ui vi : 
    In (projT1 ui, projT1 vi) (projT1 f) <->
    In (ui, vi) (graph f).
  Proof.
    split.
    + destruct f as [rf Vf]. move: Vf.
      induction rf as [|[uj vj]f].
      all: move=> Vf.
      all: cbn [projT1].
    - move=> h. inversion h.
    - cbn [projT1] in IHf.
      move=> [EQ|h].
  Admitted.


  Lemma coherent_with_def f u v :
    (forallb 
      (fun '(uj, vj) => compatible u uj ==> compatible v vj) (graph f)) <->
    coherent_with f (u,v).
  Proof.
    split.
    - move=> /forallb_forall CF. 
      apply /forallb_forall.
      move=> [rui rvi] Inrf.
      have [ui E1]: { UI : elt & projT1 UI = rui }. 
      { destruct f as [rf Vf]. cbn in Inrf.
        have Vui: Raw.valid rui.
        move: (Raw.valid_fun_subterms Vf) => /forallb_forall VSt.
        specialize (VSt _ Inrf). cbn in VSt. 
        move: VSt=> /andP. eauto.
        exists (existT _ rui Vui). eauto. } 
      have [vi E2]: { VI : elt & projT1 VI = rvi }. 
      { destruct f as [rf Vf]. cbn in Inrf.
        have Vvi: Raw.valid rvi.
        move: (Raw.valid_fun_subterms Vf) => /forallb_forall VSt.
        specialize (VSt _ Inrf). cbn in VSt. 
        move: VSt=> /andP. eauto.
        exists (existT _ rvi Vvi). eauto. } 
      rewrite <- E1 in Inrf. rewrite <- E2 in Inrf.
      rewrite In_graph_def in Inrf.
      specialize (CF _ Inrf). cbn in CF. 
      destruct ui. destruct vi. unfold compatible in CF.
        cbn in CF. cbn in E1. cbn in E2. subst. done. 
    - move=> /forallb_forall CF. 
      apply /forallb_forall.
      move=> [ui vi] Ingf.
      rewrite <- In_graph_def in Ingf.
      destruct ui. destruct vi. cbn in Ingf.
      specialize (CF _ Ingf).
      unfold compatible. cbn. eapply CF.
  Qed.

  Lemma compatible_fun_def (f g : finfun) : 
    forallb (coherent_with g) (graph f) <-> 
    compatible_fun f g.
  Proof.
    split.
    - move=> /forallb_forall h.
      unfold compatible_fun, Raw.compatible_fun.
      apply /forallb_forall.
      move=> [ui vi] Inf.
  Admitted.

  Lemma le_fun_mono_arg f u1 u2 :
    le u1 u2 -> le (app f u1) (app f u2).
  Proof.
    move=> LE.
    destruct f as [f Vf].
    destruct u1 as [u1 Vu1].
    destruct u2 as [u2 Vu2].
    unfold le in LE. cbn [projT1] in LE. 
  Admitted.

End Valid.

(* ------------------------------------------------------- *)
Import Raw.


(* Theorem 1 *)

(*  ρ fits Γ if for all x : A in Γ we have [[A]]ρ in Type and ρ(x) in
El([[A ρ]]). *)

Inductive fits : forall {n} (Γ:Ctx n) (ρ : Env n), Prop := 
  | fits_empty : fits ctx_empty null
  | fits_cons n (Γ : Ctx n) A ρ a u i : 
       fits Γ ρ ->
       EvalRel A ρ a ->
       wt u (tuniv i) ->
       wt a u ->
       fits (Γ ++ A) (u .: ρ).
  

Fixpoint typing_EvalRel {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :
   typing Γ M A -> forall ρ a u, 
        fits Γ ρ -> EvalRel M ρ a -> EvalRel A ρ u -> wt a u
with typing_conv_EvalRel {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) :
   typing Γ M A -> forall ρ a u, 
        fits Γ ρ -> EvalRel M ρ a -> 
with 
   ctx_fits {n} (Γ : Ctx n) :
   ctx Γ -> forall ρ x, fits Γ ρ -> EvalRel (var x) ρ (ρ x).
Proof.
  move=>h.
  dependent destruction h.
  - move=> ρ a u FF Ety Etm.
    cbn in Ety. move: Ety => [Va Le].
    admit.
  - move=> ρ a u FF Ety Etm.
    
(*
-- Val G M A u a : term M has type A, with realizer u at code a, in context G
 Val : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
*)

Fixpoint Val (a: elt) (u : elt) : 
  forall {n: nat} (Γ : Ctx n) ( M : Tm n) (A : Tm n), Prop := 
    match a with 
    | bot => fun {n} Γ M A => True
    | tuniv i => match u with 
                  | tpi a g => fun {n} Γ M A => True
                  | tuniv j => fun {n} Γ M A => True
                  | tnat => fun {n} Γ M A => True
                  | _ => fun {n} Γ M A => True
                end
    | tpi b f => match u with 
(* Val G M A (FunEl g) (PiCode b f) = Pair (ValTy G A (PiCode b f)) (ValPi G M A g b f) *)
       | abs g => fun {n} Γ M A0 => 
          Val (tpi b f) (tuniv i) G A /\
          exists A, exists B, Red G M (Core.Pi A B) (Core.tuniv i) /\
          (f = nil \/ valid_fun f) /\
          (* (FinMemAllU f b) /\ *)
          Val b (tuniv i) G A /\
          (forall u v, In (u,v) f -> 
            forall (N : Tm n), Val u b G N A -> 
              Val v (tuniv i) G (B[N ..]) (Core.tuniv i))
                                          
       | _ => fun {n} Γ M A => True
       end
    | tnat => match u with 
             | zero => fun {n} Γ M A => True
             | succ v => fun {n} Γ M A => True
             | _ => fun {n} Γ M A => True
             end
    | _ => fun {n} Γ M A => True
    end.

destruct a eqn:Ea.
- exact True.  
- destruct u eqn:Eu.
  + exact True.
  + exact False.
  + exact False.
  + exact True.
  + destruct M eqn:EM.
