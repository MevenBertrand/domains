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

  Lemma le_valid_compatible w u v: 
    valid w -> le u w -> le v w -> compatible u v.
  Proof.
    move=> Vw Lu Lv.
    eapply comp_down; eauto.
    eapply compatible_sym.
    eapply comp_down; eauto.
    eapply compatible_refl; eauto.
  Qed.
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

  Definition is_tpi (v : Valid.elt) : option (Valid.elt * option Valid.finfun).
    destruct v as [a f].
    destruct a eqn:Ea.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - exact None.
    - apply Some.
      cbn in f.
      move:f => /andP [Ve h].
      split. exists a.
    match v with 
    | existT _ (Raw.tpi a nil) => Some (existT _ 

  Definition abs (f : finfun) : elt.
    exists (Raw.abs (projT1 f)).
    destruct f as [f Vf]. 
    eassumption.
  Defined.

  Definition app (f : finfun) (u : elt) : elt.
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

Import Valid.

(* Part 1: Finite environments *)

Definition Env n := fin n -> elt.

(* Part 2: EvalRel *)

Notation " a ↦ b " := (Valid.singleton a b) (at level 70).
Notation " a == b " := (Valid.eqb a b) (at level 70).
  
Fixpoint EvalRel {n} (t : Tm n) : Env n -> Valid.elt -> Prop := 
  match t return Env n -> Valid.elt -> Prop with 
  | var i => fun ρ b => Valid.le b (ρ i)
  | tuniv i => fun ρ b =>
             (* i.e. b == bot \/ b == tuniv i *)
             Valid.le b (Valid.tuniv i)
  | tnat => fun ρ b => 
             (* b == bot \/ b == tnat *)
             Valid.le b Valid.tnat
  | zero => fun ρ b => 
             Valid.le b Valid.zero
  | succ M => fun ρ b => 
               if Valid.is_bot b then True else
                 exists a, Valid.le b (Valid.succ a) /\ EvalRel M ρ a
  | tpi A B => fun ρ b => 
        if is_bot b then True
        else match is_tpi b with 
              | Some (a, ff) =>
                  exists i a', wt a (tuniv i) /\ EvalRel A ρ a /\
                    match ff with 
                    | Some g =>         
                        forall u v, In (u,v) (graph g) -> 
                               exists x, le x u /\ wt x a /\
                                      EvalRel B (x .: ρ) v
                    | None => True 
                    end
              | None => False
             end

         match projT1 b with 
         | Raw.bot => True
         | Raw.tpi a f =>              
             (exists a', EvalRel A ρ a' /\
                      forall u v, Raw.app f (projT1 u) = Some (projT1 v) -> 
                             exists (x : Valid.elt), 
                               Valid.le x u 
                               /\ wt (projT1 x) (projT1 a')
                               /\ EvalRel B (x .: ρ) v)
         | _ => False
         end
  | app M N => fun ρ b => 
         if Valid.is_bot b then True else 
            exists a, EvalRel M ρ (a ↦ b) /\ EvalRel N ρ a 
  | abs A M => fun ρ b => 
         match b with 
         | existT _ Raw.bot _ => True
         | existT _ (Raw.abs rg) Vg =>
             exists i a, Valid.wt a (Valid.tuniv i) /\ EvalRel A ρ a
                    /\ forall u v, In (u,v) (Valid.graph (existT _ rg Vg)) -> 
                             exists x, Valid.le x u 
                                  /\ Valid.wt x a
                                  /\ EvalRel M (x .: ρ) v
         | _ => False 
         end
  | nrec T M0 M1 => fun ρ b =>
         if Valid.is_bot b then True else False                  
  end.


(* monotonicity *)
Definition LeEnv {n} (ρ1 ρ2 : Env n) := 
  forall x, Valid.le (ρ1 x) (ρ2 x).

Lemma EvalRel_mono_env {n} (M : Tm n) (ρ ρ' : Env n) u :
  EvalRel M ρ u -> LeEnv ρ ρ' -> EvalRel M ρ' u.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: eauto.
  all: move=> h1 h2. 
  - (* M = x *)
    specialize (h2 f).
    eapply Valid.le_trans; eauto.
  - (* M = Abs M1 M2,  *)
    destruct u as [u Vu]. 
    destruct u eqn:Eq; try done.
    move: h1 => [i [a [WT [ER f]]]].
    exists i ,a. repeat split; eauto.
    move=> u1 v1 h3. 
    specialize (f u1 v1 h3).
    destruct f as [x [Lex [WT2 EM2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto.
    unfold LeEnv. move=> [y|]. cbn. eauto.
    cbn. eapply Valid.le_refl.
  - (* M = app M1 M2 *)
    destruct (Valid.is_bot u); try done.
    destruct h1 as [a [E1 E2]].
    exists a. split; eauto.
  - (* M = succ M *)
    destruct (Valid.is_bot u); try done.
    destruct h1 as [a [EQ1 E]].
    exists a. split; eauto.
  - (* M = tpi M1 M2 *)
    destruct (projT1 u); try done.
    destruct h1 as [a [E1 h3]].
    exists a. split; eauto.
    intros u1 v1 APP.
    specialize (h3 u1 v1 APP).
    destruct h3 as [x [Lx [WT E2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto.
    unfold LeEnv. move=> [y|]. cbn. eauto.
    cbn. eapply Valid.le_refl.
Qed.    



(* Lam-edgewise *)
Lemma lam_edgewise {n} {A : Tm n} {M ρ g} : 
  EvalRel (abs A M) ρ (Valid.abs g) -> 
  exists a, EvalRel A ρ a 
       /\ forall u v, In (u,v) (Valid.graph g) -> 
         exists x, wt (projT1 x) (projT1 a) /\ EvalRel M (x .: ρ) v.
Proof.
  move=> E1.
  destruct g as [g Vg].
  cbn [EvalRel projT1 Valid.abs] in E1.
  destruct E1 as [i [a [WT [EA body]]]].
  exists a. split; eauto.
  intros u v ein.
  destruct (Raw.valid_app_exists Vg (projT2 u)) as [rw [EQ Vw]].
  specialize (body u v ein).
  remember (existT (fun x => Raw.valid x) rw Vw) as w.
  destruct body as [x [Lex [WT2 ER2]]].
  exists x. split; eauto.
Qed.

Lemma EvalRel_bot {n} (M : Tm n) (ρ : Env n) : 
  EvalRel M ρ Valid.bot.
Proof.
  destruct M eqn:EQ; cbn; try done.
  (* var *) rewrite Valid.le_bot; eauto.
Qed.


Lemma EvalRel_compatible {n} (M : Tm n) :
  forall (ρ : Env n) (a b : Valid.elt),
  EvalRel M ρ a -> EvalRel M ρ b -> Raw.compatible (projT1 a) (projT1 b).
Proof.
  induction M.
  all: cbn [EvalRel].
  all: move=> ρ a b.
  - (* var *) 
    move=> /andP h1 /andP h2. 
    move: h1 => [C1 L1]. move: h2 => [C2 L2].
    destruct (ρ f) as [rf Vf]. cbn in *.
    eapply Raw.le_valid_compatible; eauto.
  - (* abs M1 M2 *)
    destruct a as [a Va]. destruct b as [b Vb].
    move=> h1 h2.
    destruct a; try done;
    destruct b; try done.
    destruct h1 as [i1 [a1 [WT1 [E1 F1]]]].
    destruct h2 as [i2 [a2 [WT2 [E2 F2]]]].
    cbn [projT1 Raw.compatible].
    apply /forallb_forall.
    move=> [ui vi] Ini.
    apply /forallb_forall. 
    move=> [uj vj] Inj.
    apply /implyP. move=> h1.
    move: (Raw.valid_fun_subterms Va) => /forallb_forall Vs1.
    specialize (Vs1 _ Ini). move: Vs1 => /andP [Vui Vvi].
    move: (Raw.valid_fun_subterms Vb) => /forallb_forall Vs2.

    have: valid ui.
(*
-- Val G M A u a : term M has type A, with realizer u at code a, in context G
 Val : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
*)

Fixpoint Val {n: nat} (Γ : Ctx n) ( M : Tm n) (A : Tm n)  (u : Raw.elt) (a : Raw.elt) : Prop.
destruct a eqn:Ea.
- exact True.  
- destruct u eqn:Eu.
  + exact True.
  + exact False.
  + exact False.
  + exact True.
  + destruct M eqn:EM.
