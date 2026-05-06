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

(* This information is *not* availble from wt
   TODO: update wt to include it
   (And: if we want to have a recursively defined wt
   we also need to update abs)
 *)
Lemma wt_abs_dom f a g : 
  wt (abs f) (tpi a g) -> exists i, wt a (tuniv i).
Proof.
move=> h. inversion h. subst.
Abort.

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


(* Logical relation, defined by induction on (semantic type) a.
   We only need it for closed terms, so dropping the context and 
   specializing M's scope to 0.

   As a is "more defined" this set becomes smaller. When we don't 
   know anything, i.e. a is bot, then we have the total set.

   NOT TRUE: If Val M A (h: wt u a) holds 
             then we know that null |- M : A
 *)

Module Rec.
Section Helpers.

Variable
  (Val   : Tm 0 -> Tm 0 -> forall u a, wt u a -> Prop)
  (EqVal : Tm 0 -> Tm 0 -> Tm 0 -> forall u a, wt u a -> Prop).

Definition PiEdgeVal 
  (A : Tm 0) (B : Tm 1) (b: elt) (f : list (elt * elt))
  i (h : wt (tpi b f) (tuniv i)) : Prop := 
   forall u v (IN : In (u,v) f) (N : Tm 0), 
      typing ctx_empty N A ->
      (* take related arguments *)
      Val N A (wt_tpi_cod_key h IN) ->
      (* to related results *)
      Val B[N..] (Core.tuniv i) (wt_tpi_cod_elt h IN).

Definition PiEdgeEq
  (A : Tm 0)(B:Tm 1) (b: elt) (f : list (elt * elt))
  i (h : wt (tpi b f) (tuniv i))  := 
  forall u v (IN : In (u,v) f) (N1 N2 : Tm 0), 
      conv ctx_empty N1 N2 A ->
      (* take related arguments *)
      EqVal N1 N2 A (wt_tpi_cod_key h IN) ->
      (* to related results *)
      EqVal B[N1..] B[N2..] (Core.tuniv i)
                         (wt_tpi_cod_elt h IN).
            
Definition PiAppVal M A0 B0 b f g (h : wt (abs g) (tpi b f)) := 
  forall u v (IN : In (u,v) g) 
  (P : Tm 0) t (APP: app f u = Some t),
    typing ctx_empty P A0 ->
    Val P A0 (wt_abs_key h IN APP) ->
    Val (Core.app M P) B0[P..] (wt_abs_elt h IN APP).

Definition PiAppEq M A0 B0 b f g (h : wt (abs g) (tpi b f)) := 
  forall u v (IN : In (u,v) g) 
  (N1 N2 : Tm 0) t (APP: app f u = Some t),
    conv ctx_empty N1 N2 A0 ->
    EqVal N1 N2 A0 (wt_abs_key h IN APP) ->
    EqVal (Core.app M N1) (Core.app M N2) B0[N1..] (wt_abs_elt h IN APP).

Definition PiAppEqVal M N A0 B0 b f g (h : wt (abs g) (tpi b f)) := 
 forall u v (IN : In (u,v) g) 
  (P : Tm 0) t (APP: app f u = Some t),
    typing ctx_empty P A0 ->
    Val P A0 (wt_abs_key h IN APP) ->
    EqVal (Core.app M P) (Core.app N P) B0[P..] (wt_abs_elt h IN APP).

Definition ValPi
  (M : Tm 0) (A : Tm 0) g b f (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppVal M A0 B0 h.

Definition EqValPi 
  (M : Tm 0) (N: Tm 0) (A : Tm 0) g b f (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppEqVal M N A0 B0 h.

Definition ValTy 
  (M : Tm 0) u i : wt u (tuniv i) -> Prop  := 
  match u return wt _ (tuniv i) -> Prop with 
  | tpi b g => 
      fun (h : wt (tpi b g) (tuniv i)) => 
        (* ValTyPi M (tuniv i) *)
        (* M reduces to a pi type *)
        exists A B, HeadRed M (Core.tpi A B) 

               (* the syntactic pi-type is well-typed *)
               /\ typing ctx_empty A (Core.tuniv i)
               /\ typing (ctx_empty ++ A) B (Core.tuniv i)

               (* the semantic pi-type is valid *)
               /\ valid (tpi b g)

               (* domain is in the relation *)
               /\ Val A (Core.tuniv i) (wt_tpi_dom h)

               /\ PiEdgeVal A B h /\ PiEdgeEq A B h

  | tnat => fun h => True
  | tuniv k => fun h => True 
  | _ => fun h => True
  end.


Fixpoint
  EqValTy M N (a : elt) i (h : wt a (tuniv i)) {struct h} : Prop := 
  (match a return wt _ (tuniv i) -> Prop with 
  | tpi b f => 
      fun (h : wt (tpi b f) (tuniv i))  => 
        ValTy M h /\ ValTy N h /\
        (* EqValTyPi Val EqVal EqValTy M N h *)
             (* both reduce to pi types *)
             exists A B, HeadRed M (Core.tpi A B) 
             /\ exists A' B', HeadRed N (Core.tpi A' B') 
             (* that are well-typed *)
             /\ conv ctx_empty A A' (Core.tuniv i)
             /\ conv (ctx_empty ++ A) B B' (Core.tuniv i)
             /\ valid (tpi b f)
             (* domain is in the relation *)
             /\ EqVal A A' (Core.tuniv i) (wt_tpi_dom h)
        /\ (* PiEdgeEqTy A B B' h *)
             (forall u v (IN : In (u,v) f) (P : Tm 0), 
                 typing ctx_empty P A ->
                 (* take related arguments *)
                 Val P A (wt_tpi_cod_key h IN) ->
                 (* to related results *)
                 EqValTy B[P..] B'[P..] (wt_tpi_cod_elt h IN))
  | _ => fun h => True
  end) h.

End Helpers.
End Rec.

Fixpoint Val 
  (M : Tm 0) (A : Tm 0) (u : elt) (a: elt) (h : wt u a) { struct h } : Prop := 
      (match a return wt u _ -> Prop with 

      | bot => fun h => True
                
      | tuniv i => fun (h : wt u (tuniv i)) => 
          Rec.ValTy Val EqVal M h

      | tpi b f => fun h => 
           (match u return wt _ (tpi b f) -> Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) => 
                        (* need to update wt if we want this *)
                        (* (ValTy Val (tpi b f) A (wt_abs_tpi h)) /\ *)
                        Rec.ValPi Val M A h

            | _ => fun h => True
            end) h

      | tnat => fun h =>
          HeadRed A (Core.tnat) /\
          (match u return wt _ tnat -> Prop with 
               | zero => fun h => 
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat) => 
                 exists M1, HeadRed M (Core.succ M1)
                 /\ Val M1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h
(* Binary logical relation *)
with EqVal 
  (M : Tm 0) (N : Tm 0) (A : Tm 0) (u : elt) (a: elt) (h : wt u a) { struct h } : Prop := 

     (match a return wt u _ -> Prop with 

      | bot => fun h => True
                
      | tuniv i => fun (h : wt u (tuniv i)) =>
                    
            Rec.ValTy Val EqVal M h 
          /\ Rec.ValTy Val EqVal N h 
          /\ Rec.EqValTy Val EqVal M N h
          
      | tpi b f => fun h => 
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True 
           | abs g => fun (h : wt (abs g) (tpi b f)) => 
                     
             (* this is not available *)
             (* ValTy Val EqVal A (wt_abs_dom h) *)
               Rec.ValPi Val M A h
             /\ Rec.ValPi Val N A h
             /\ Rec.EqValPi Val EqVal M N A h

           | _ => fun h => True
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
                 /\ EqVal M1 N1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h.

Notation ValTy := (@Rec.ValTy Val EqVal).
Notation EqValTy := (@Rec.EqValTy Val EqVal).
Notation PiEdgeVal := (@Rec.PiEdgeVal Val).
Notation PiEdgeEqVal := (@Rec.PiEdgeEq EqVal).
Notation PiAppVal := (@Rec.PiAppVal Val).
Notation PiAppEqVal := (@Rec.PiAppEqVal Val EqVal).
Notation ValPi := (@Rec.ValPi Val).
Notation EqValPi := (@Rec.EqValPi Val EqVal).

(* All terms in the relation have the right syntactic type. *)
Fixpoint Val_typing (u : elt) (a: elt) 
  (M : Tm 0) (A : Tm 0) (h : wt u a) :
  Val M A h -> typing ctx_empty M A.
Proof.
  dependent destruction h.
  all: move=> h1.
  all: cbn in h1.
  - destruct a; try done.
Abort.



Lemma EqValTy_EqVal A B a i (h : wt a (tuniv i)):
  EqValTy A B h ->
  EqVal A B (Core.tuniv i) h.
Proof.
  dependent destruction h; try done.
  all: cbn.
  all: move=> [hA [hB h1]].
  all: eauto.
Qed.

Lemma EqVal_EqValTy A B C a i (h : wt a (tuniv i)):
  EqVal A B C h ->
  EqValTy A B h.
Proof.
  dependent destruction h; try done.
  all: cbn in *.
  all: eauto.
Qed.

Fixpoint Val_EqVal M A u a (h : wt u a) {struct h} : 
  Val M A h -> EqVal M M A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  - destruct a; try done.
  - move=> [hA [M1 [h1 V1]]].
    split; auto.
    exists M1. split; auto.
    exists M1. split; auto.
  - move=>h1.  
    repeat split; eauto.
    clear A.
    destruct h1 as (A & B & HR & TA & TB & VPi & ValA & PEV & PEE).
    exists A, B. split; auto.
    exists A, B. split; auto.
    repeat split; auto.
    eapply c_refl; eauto.
    eapply c_refl; eauto.
    move=> u v IN P TP ValP.
    specialize (PEE u v IN P P ltac:(eapply c_refl;eauto)).
    apply Val_EqVal in ValP.
    specialize (PEE ValP).
    eapply EqVal_EqValTy. eauto.
  - move=> h1.
    repeat split; eauto.
    destruct h1 as (A0 & B & HR & PAV).
    exists A0, B. split; auto.
    unfold PiAppVal in PAV.
    unfold PiAppEqVal.
    move=> u v IN P t APP TM VP.
    specialize (PAV u v IN P t APP TM VP).
    eapply Val_EqVal; eauto. 
Qed.
    


Fixpoint EqVal_Val1 M N A u a (h : wt u a) {struct h} : 
  EqVal M N A h -> Val M A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  (* 2 nontrivial goals *)
  - destruct a; try done.
  - move=> [hA [M1 [h1 [N1 [h2 V1]]]]].
    split; auto.
    exists M1. split; auto.
    eauto.
Qed.


Fixpoint EqVal_Val2 M N A u a (h : wt u a) {struct h} : 
  EqVal M N A h -> Val N A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  (* 2 nontrivial goals *)
  - destruct a; try done.
  - move=> [hA [M1 [h1 [N1 [h2 V1]]]]].
    split; auto.
    exists N1. split; auto.
    eauto.
Qed.

(* 

  upVal2 : {n : Nat} (G : Ctx n) (M T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    Val2 G M T u a0 -> ValTy2 G T a1 ->
    Val2 G M T u a1
  upEqVal2 : {n : Nat} (G : Ctx n) (M N T : Expr n) (u a0 a1 : FinEl) ->
    LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 ->
    Coherent a0 -> Coherent a1 ->
    EqVal2 G M N T u a0 -> ValTy2 G T a1 ->
    EqVal2 G M N T u a1

*)

Fixpoint upVal M T u a0 a1 i 
  (h0 : wt u a0) (h1 : wt u a1) (ha1 : wt a1 (tuniv i)) {struct h0}:
  le a0 a1 -> Val M T h0 -> ValTy T ha1 -> Val M T h1
with upEqVal M N T u a0 a1 i 
  (h0 : wt u a0) (h1 : wt u a1) (ha1 : wt a1 (tuniv i)) {struct h0}:
  le a0 a1 -> EqVal M N T h0 -> ValTy T ha1 -> EqVal M N T h1
.
Proof.
  dependent destruction h0.
  + dependent destruction h1.
    move=> LE VB VT.
    cbn in VB. cbn.
    destruct a; destruct a0; cbn; auto. 
    all: dependent destruction ha1.
    all: cbn in LE; try done.
    all: cbn in VT.
    admit.
  + 
Admitted.

Fixpoint downVal M T u a0 a1 
  (h0 : wt u a0) (h1: wt u a1) {struct h1} : 
  le a0 a1 -> Val M T h1 -> Val M T h0
with downEqVal M N T u a0 a1 
  (h0 : wt u a0) (h1: wt u a1) {struct h1} : 
  le a0 a1 -> EqVal M N T h1 -> EqVal M N T h0.
Proof.
  - dependent destruction h1.
    all: dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto; done.
    + (* tnat *)
      all: move=> _ [RT [M1 [RM1 VM1]]].
      split. auto. exists M1. split. auto.
      eapply downVal with (a1 := tnat); eauto. 
    + (* tuniv *)
      admit.
    + move=> LE VM.
      rewrite le_tpi in LE. move: LE => /andP. move=> [LEa LEg].
      cbn in VM. cbn.
      unfold ValPi in *.
      move: VM => [A [B [RT PAV]]].
      exists A, B. split. auto.
      unfold PiAppVal in *.
      move=> u v IN P t APP TP VP.
      specialize (PAV u v IN P). 
      have Vg : valid_fun  g. admit.
      have Vg0 : valid_fun g0. admit.
      have Vu : valid u. admit.
      destruct (valid_app_exists Vg0 Vu) as [t0 [APP0 Vt0]].
      move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
      move: (wt_abs_key (wt_abs w1 w2 i i2) IN APP0) => h2.
      remember (wt_abs_elt (wt_abs w1 w2 i i2) IN APP0) as h3.
      eapply downVal with (a1 := t0)(h1:=h3). auto.
      rewrite Heqh3.
      eapply PAV; eauto.
Admitted.
      

Fixpoint Val_EqVal_fwd M A u a (h : wt u a) B i (h' : wt a (tuniv i))
  {struct h} :
  Val M A h -> EqValTy A B h' -> Val M B h
with EqVal_EqVal_fwd M N A u a (h : wt u a) B i (h' : wt a (tuniv i))
  {struct h} :
  EqVal M N A h -> EqValTy A B h' -> EqVal M N B h.  
Proof.
(*
  have EqValPi_EqVal_fwd : forall
      M A f a g (h : wt (abs f) (tpi a g)) B i (h' : wt a (tuniv i)),
   ValPi M A h -> EqValTy A B h' -> ValPi M B h.
  { 
    clear M A u a h B i h'.
    move=> M A f a g h B i h'.
    unfold ValPi.
    move=> [A0 [B0 [R0 PAV0]]] h1.
    admit.
  } *)
  - dependent destruction h.
    all: dependent destruction h'.
    all: cbn.
    all: eauto.    
    + (* tnat *)
      admit. (* !!!!! *)
    + (* zero *) 
      admit.
    + (* succ *)
      admit.
    + (* abs *)
      unfold ValPi.
      move=> [A0 [B0 [RA PAV]]].
      move=> [hA [hB hAB]].
      destruct hB as (A1 & B1 & RB & hB).
      exists A1, B1. split. exact RB.
      unfold PiAppVal.
      move=> u v IN P t APP tP VPA1.
Admitted.      

Fixpoint EqVal_sym M N A u a (h : wt u a) {struct h} : 
  EqVal M N A h -> EqVal N M A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  (* 4 nontrivial *)
  - destruct a; try done.
  - move=> [h1 [M1 [h2 [N1 [h3 E]]]]].
    repeat split; eauto.
    exists N1. eauto.
  - move=> [vpiM [vPiN [_ [_ h3]]]].
    repeat split; eauto.
    clear A.
    move: h3 => [A0 [B0 [R1 [A1 [B1 [R2 [T1 [T2 [Vt [EA PEE]]]]]]]]]].
    eexists. eexists.
    repeat split; eauto.
    eexists. eexists.
    repeat split; eauto.
    eapply c_sym; eauto.
    eapply c_sym; eauto.
    eapply ctx_conv_conv; eauto.
    move=> u v IN P TA1 VP.
    have TA0: typing ctx_empty P A0.
    { eauto using t_conv, c_sym. }
    specialize (PEE u v IN P TA0).
    eapply EqVal_EqValTy.
    eapply EqVal_sym; eauto.
    eapply EqValTy_EqVal; eauto.
    eapply PEE; eauto.
Admitted.

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

Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A) (at level 70).
Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv2 Γ M N A) (at level 70).

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
  specialize (h2 ρ σ σ TS TS FR).
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
  specialize (h3 ρ σ TS FR VS).
  specialize (h4 ρ σ TS FR VS).
  cbn.
  cbn in Ex.
  destruct (is_bot u1) eqn:HB. 
  - (* EvalRel (app M N) is bot *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    destruct a; try done.
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



  
