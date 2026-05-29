(* See Validity.agda *)

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

Lemma HeadRed_tpi_det (n:nat) (M : Tm n) A1 B1 A2 B2 : 
  HeadRed M (Core.tpi A1 B1) -> HeadRed M (Core.tpi A2 B2) ->
  A1 = A2 /\ B1 = B2.
Proof.
  move=> h1. move:A2 B2.
  dependent induction h1.
  all: move=> A2 B2 h2. 
  - inversion h2; subst. done. inversion H.
  - inversion h2; subst. inversion H.
    specialize (IHh1 _ _ ltac:(reflexivity) A2 B2).
    have EQ: e2 = e3. eapply HeadRed1_det; eauto.
    subst.
    eauto.
Qed.

Lemma HeadRed_tpi_eq {n}( A1 : Tm n) B1 A2 B2 :
   HeadRed (Core.tpi A1 B1) (Core.tpi A2 B2) -> 
   A1 = A2 /\ B1 = B2.
Proof. 
  move=> R1.
  have R2: HeadRed (Core.tpi A1 B1) (Core.tpi A1 B1).
  { eapply ms_refl. }
  eapply HeadRed_tpi_det; eauto.
Qed.

Lemma typing_app_inv n (Γ : Ctx n) M N A : 
 typing Γ (app M N) A -> 
      exists A1 , exists A2, typing Γ M (tpi A1 A2) /\ typing Γ N A1 /\ conv Γ A2[N..] A tuniv.
Proof. 
  move=> h.
  dependent induction h.
  - specialize (IHh M N ltac:(eauto)).
    destruct IHh as [A1 [A2 [TM [TN CC]]]].
    exists A1. exists A2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3 IHh4.
    exists A. exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply substitution_tm with (σ := N..) in h2. cbn in h2.
    eapply h2.
    eapply typing_subst_cons. asimpl. auto.
    eapply typing_subst_id. eapply typing_ctx; eauto.
    eapply typing_ctx; eauto.
Qed.

Lemma typing_abs_inv n (Γ : Ctx n) M A B: 
 typing Γ (abs A M) B -> 
      exists B2, typing (Γ ++ A) M B2 /\ conv Γ (tpi A B2) B tuniv.
Proof. 
  move=>h.
  dependent induction h.
  - specialize (IHh M A ltac:(eauto)).
    destruct IHh as [B2 [TM CC]].
    exists B2. repeat split; auto.
    eapply c_trans; eauto.
  - clear IHh1 IHh2 IHh3.
    exists B. repeat split; auto.
    eapply c_refl; eauto.
    eapply t_tpi; eauto.
Qed.


Lemma HeadRed1_conv {n} Γ (M N : Tm n) A :
  HeadRed1 M N -> typing Γ M A -> conv Γ M N A.
Proof.
  move=> h. induction h.
  - move=> T.
    destruct (typing_app_inv T) as [A1 [A2 [T1 [T3 C1]]]].
    destruct (typing_abs_inv T1) as [B2 [T2 C2]].
    eapply c_conv. 2: eassumption.
    eapply c_beta; eauto.
Abort.    

Require Import findom.
Require Import types.

Import Raw.


(*
(* Inversion lemmas for wt *)
Lemma wt_tpi_dom (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) tuniv ->
  wt a tuniv.
move=>h. inversion h. done. Defined.
Lemma wt_tpi_cod_key (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) tuniv ->
  (forall ui vi : elt, In (ui, vi) g -> wt ui a).
move=>h. inversion h. done. Defined.
Lemma wt_tpi_cod_elt (a : elt) (g : list (elt * elt)) (j : nat):
  wt (tpi a g) tuniv ->
  (forall ui vi : elt, In (ui, vi) g -> wt vi tuniv).
move=>h. inversion h. done. Defined.
*)

(* This information is *not* availble from wt
   TODO: update wt to include it
   (And: if we want to have a recursively defined wt
   we also need to update abs)
 *)
(*
Lemma wt_abs_dom f a g : 
  wt (abs f) (tpi a g) -> { i & wt a tuniv }.
Proof.
move=> h. inversion h. subst.
inversion H4. subst. eexists. eauto.
Qed.

Lemma wt_abs_tpi f a g : 
  wt (abs f) (tpi a g) -> { i &  wt (tpi a g) tuniv }.
move=> h. inversion h. subst. eexists. eauto.
Qed.
*)
(*
Lemma wt_abs_key (a : elt) (f g : list (elt * elt)) :
  wt (abs f) (tpi a g) -> 
  (forall ui vi : elt, In (ui, vi) f -> wt ui a).
move=>h. inversion h. done. Defined.

Lemma wt_abs_elt (a : elt) (f g : list (elt * elt)) :
  wt (abs f) (tpi a g) -> 
  (forall ui vi w : elt, In (ui, vi) f -> app g ui = Some w -> wt vi w).
move=>h. inversion h. done. Defined.
*)

Lemma wt_succ_inv u:
  wt (succ u) tnat -> wt u tnat.
move=>h. inversion h. done. Defined.


(* Logical relation, defined by recursion on the wt judgement for
   semantic elements. i.e. on the derivation of `wt u a`.

   The relation is parameterized by a typing context Γ : Ctx n.
   Terms M, N, A live at scope n; substitutions B[N..] close one
   variable, producing terms at scope n in the same context Γ.

   This is a coinductive definition. As u is "more defined" the
   set of syntactic terms in the relation becomes smaller.
   To begin, when u is bot, it is the total set.

*)

Definition ForallP {a} (p : a -> Prop) (l : list a) : Prop := 
  List.fold_right (fun x y => p x /\ y) True l.
Lemma ForallP_forall {a} p (l : list a) :
  ForallP p l <-> forall x, In x l -> p x.
Admitted.



Lemma wt_abs_ty g b f : 
  wt (abs g) (tpi b f) -> wt (tpi b f) tuniv.
Proof. 
  move=> h. inversion h. eauto.
Defined.


Lemma wt_abs_inv1 g a f : 
  wt (abs f) (tpi a g) ->     
  (forall u v, valid u -> app f u = Some v -> ~ is_bot v -> wt u a).
Proof. 
  move=> h. inversion h. eauto.
Defined.

Lemma wt_abs_inv2 g a f : 
  wt (abs f) (tpi a g) ->    
  (forall u v t, valid u -> app f u = Some v -> ~ is_bot v -> app g u = Some t -> wt v t). 
Proof. 
  move=> h. inversion h. eauto.
Defined.


Lemma wt_tpi_dom a g :
  wt (tpi a g) tuniv  -> wt a tuniv.
Proof.
  move=> h. inversion h. eauto.
Defined.


Lemma wt_tpi_inv1 a g :
  wt (tpi a g) tuniv -> 
  (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt u a).
Proof.
  move=> h. inversion h. eauto.
Defined.

Lemma wt_tpi_inv2 a g :
  wt (tpi a g) tuniv -> 
  (forall u v, valid u -> app g u = Some v -> ~ is_bot v -> wt v tuniv).
Proof.
  move=> h. inversion h. eauto.
Defined.


(* This module defines various helper operations on the logical
   relation. Each of these operations is parameterized by the
   two main fixpoints (Val and EqVal) which are polymorphic in
   the context size n and the typing context Γ.
*)
Module Rec.

Record F := MkF {
   Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop;
   EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop;
}.

Section Helpers.

Variable 
   Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop.
Variable
   EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop.


Definition  PiEdgeEq {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  (h : wt (tpi b f) tuniv) :=
  forall u v (Vu : valid u) 
      (APP: app f u = Some v) (NB: ~ is_bot v) 
      (N1 N2 : Tm n),
      conv Γ N1 N2 A ->
      (* take related arguments *)
      EqVal Γ N1 N2 A (wt_tpi_inv1 h Vu APP NB) ->
      (* to related results *)
      EqVal Γ B[N1..] B[N2..] Core.tuniv (wt_tpi_inv2 h Vu APP NB).

Definition PiAppVal {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) : Prop :=
  forall u v t (Vu : valid u) 
  (APP: app f u = Some v) (NB: ~ is_bot v) 
  (APPg : app g u = Some t)
  (P : Tm n), typing Γ P A0 -> 
              Val  Γ P A0 (wt_abs_inv1 h Vu APP NB) -> 
              Val  Γ (Core.app M P) B0[P..] 
                  (wt_abs_inv2 h Vu APP NB APPg). 

Definition PiAppEq {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g))  := 
  forall u v t (Vu : valid u) 
    (APP: app f u = Some v) (NB: ~ is_bot v) 
    (APPg : app g u = Some t)
    (N1 N2 : Tm n),
    conv Γ N1 N2 A0 ->
    EqVal  Γ N1 N2 A0 (wt_abs_inv1 h Vu APP NB) ->
    EqVal  Γ (Core.app M N1) (Core.app M N2) B0[N1..] 
          (wt_abs_inv2 h Vu APP NB APPg).
    
Definition PiAppEqVal {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt (abs f) (tpi b g)) :=
  forall  u v t (Vu : valid u) 
  (APP: app f u = Some v) (NB: ~ is_bot v) 
  (APPg : app g u = Some t) (P : Tm n),
        typing Γ P A0 ->
        Val  Γ P A0 (wt_abs_inv1 h Vu APP NB) ->
        EqVal  Γ (Core.app M P) (Core.app N P) B0[P..]
          (wt_abs_inv2 h Vu APP NB APPg).

Definition ValPi {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) g b f (h : wt (abs g) (tpi b f)):=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppVal Γ M A0 B0 h.

Definition EqValPi {n} (Γ : Ctx n)
  (M : Tm n) (N: Tm n) (A : Tm n) g b f 
  (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppEqVal Γ M N A0 B0 h.

Fixpoint ValTy {n} (Γ : Ctx n)
  (M : Tm n) u (h : wt u tuniv) {struct h} : Prop  :=

  let PiEdgeVal {n} (Γ : Ctx n)
        (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
        (h : wt (tpi b f) tuniv) : Prop := 
    forall u v (Vu : valid u) 
        (APP: app f u = Some v) (NB: ~ is_bot v) (WTu : wt u b)
        (N : Tm n), typing Γ N A ->
                    (* take related arguments *)
                    Val  Γ N A (wt_tpi_inv1 h Vu APP NB) ->
                    (* to related results *)
                    ValTy Γ B[N..] (wt_tpi_inv2 h Vu APP NB)
  in

  (match u return wt _ tuniv ->  Prop with
  | tpi b g =>
      fun (h : wt (tpi b g) tuniv) =>
        (* ValTyPi M tuniv *)
        (* M reduces to a pi type *)
        exists A B, HeadRed M (Core.tpi A B)

               (* the syntactic pi-type is well-typed *)              
               /\ typing Γ A Core.tuniv
               /\ typing (Γ ++ A) B Core.tuniv

               (* the semantic pi-type is valid *)
               /\ valid (tpi b g)

               (* domain (b) is in the relation *)
               /\ Val  Γ A Core.tuniv (wt_tpi_dom h)
                                          
               /\ PiEdgeVal Γ A B b g h 
               /\ PiEdgeEq Γ A B h

  | tnat => fun h1 => True
  | tuniv => fun h1  => True
  | _ => fun h1  => True
  end) h.


Fixpoint EqValTy {n} (Γ : Ctx n) M N (a : elt) (h : wt a tuniv) {struct h} :  Prop :=
  let PiEdgeEqTy {n} (Γ : Ctx n) 
  (A : Tm n) (B B' : Tm (S n)) b f (h : wt (tpi b f) tuniv)  := 
    forall u v (Vu : valid u) 
      (APP: app f u = Some v) (NB: ~ is_bot v) 
      (P : Tm n),
          typing Γ P A ->
          (* take related arguments *)
          Val  Γ P A (wt_tpi_inv1 h Vu APP NB) ->
          (* to related results *)
          EqValTy Γ B[P..] B'[P..] (wt_tpi_inv2 h Vu APP NB)
  in 
  (match a return wt _ tuniv ->  Prop with
  | tpi b f =>
      fun (h : wt (tpi b f) tuniv)  =>
        ValTy Γ M h  /\ ValTy Γ N h /\
        (* EqValTyPi Val EqVal EqValTy M N h *)
             (* both reduce to pi types *)
             exists A B, HeadRed M (Core.tpi A B)
             /\ exists A' B', HeadRed N (Core.tpi A' B')
             (* ... that are convertible *)
             /\ conv Γ A A' Core.tuniv 
             /\ conv (Γ ++ A) B B' Core.tuniv 
             /\ valid (tpi b f)
             (* ... and the domain is in the relation *)
             /\ EqVal  Γ A A' Core.tuniv  (wt_tpi_dom h) 
             /\ PiEdgeEqTy Γ A B B' _ _ h
  | _ => fun h => True
  end) h.

End Helpers.
End Rec.

Check Rec.ValTy.

Fixpoint Val {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a: elt) (h : wt u a)  
  { struct h } : Prop :=
      (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>
          Rec.ValTy (@Val) (@EqVal) Γ M h 

      | tpi b f => fun h  =>
           (match u return wt _ (tpi b f) ->  Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) =>
                        Rec.ValTy (@Val) (@EqVal) Γ A (wt_abs_ty h)
                      /\ Rec.ValPi (@Val) Γ M A h 

            | _ => fun h  => True
            end) h 

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h  =>
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat)  =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ Val Γ M1 Core.tnat (wt_succ_inv h) 
               | _ =>  fun h => True
               end) h
      | _ => fun h  => True
       end) h 
(* Binary logical relation *)
with EqVal {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a: elt) (h : wt u a) 
  { struct h } : Prop :=
       
     (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv => fun (h : wt u tuniv) =>

            Rec.ValTy (@Val) (@EqVal) Γ M h
          /\ Rec.ValTy (@Val) (@EqVal) Γ N h
          /\ Rec.EqValTy (@Val) (@EqVal) Γ M N h 

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs g) (tpi b f)) =>
               Rec.ValTy (@Val) (@EqVal) Γ A (wt_abs_ty h)
             /\ Rec.ValPi (@Val)  Γ M A h
             /\ Rec.ValPi (@Val)  Γ N A h
             /\ Rec.EqValPi (@Val) (@EqVal) Γ M N A h

           | _ => fun h => True
            end) h

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h =>
                 HeadRed M Core.zero
                 /\ HeadRed N Core.zero
               | succ v => fun (h : wt (succ v) tnat) =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ exists N1, HeadRed N (Core.succ N1)
                 /\ EqVal Γ M1 N1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h.



Arguments Val : clear implicits.
Arguments EqVal : clear implicits.

Notation PiAppVal := (@Rec.PiAppVal Val).
Notation ValTy    := (@Rec.ValTy Val EqVal).
Notation EqValTy  := (@Rec.EqValTy Val EqVal).
Notation ValPi    := (@Rec.ValPi Val).
Notation EqValPi  := (@Rec.EqValPi Val EqVal).
Notation PiEdgeEq := (@Rec.PiEdgeEq EqVal).
Notation PiAppEqVal := (@Rec.PiAppEqVal Val EqVal).

Arguments Val {_} _ _ _ {_}{_}.
Arguments EqVal {_} _ _ _ _ {_}{_}.


(* All terms in the relation have the right syntactic type.
 NOT TRUE*)
Fixpoint Val_typing {n} (Γ : Ctx n) (u : elt) (a: elt)
  (M : Tm n) (A : Tm n) (h : wt u a) :
  Val Γ M A h -> typing Γ M A.
Proof.
  dependent destruction h.
  all: move=> h1.
  all: cbn in h1.
  - destruct a; try done.
Abort.

(*
Lemma EqVal_tpi n (Γ:Ctx n) M N A f g a i u b (w : wt_pi_fun g a i) (h : wt a tuniv) (V : valid (tpi a g)) :
  (EqVal Γ M N A (wt_tpi w h V : wt u b)) =
      (match h return wt _ (tpi a g) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs f) (tpi a g)) =>
              match h with
              | wt_abs WTf Vf (wt_tpi _ WTa _) =>
                  Rec.ValTy Rec Γ A WTa
              | _ => True
              end
             /\ Rec.ValPi Rec Γ M A h
             /\ Rec.ValPi Rec Γ N A h
             /\ Rec.EqValPi Rec Γ M N A h
       end).
*)



(* ============================================================
   Val2-Bot, EqVal2-Bot: at u = bot, both relations are True.
   ============================================================ *)

Lemma Val_Bot {n} (Γ : Ctx n) (M A : Tm n) a (h : wt bot a) : Val Γ M A h.
Proof. dependent destruction h.
       destruct a eqn:EQa; try done.
Qed.

Lemma EqVal_Bot {n} (Γ : Ctx n) (M N A : Tm n) a (h : wt bot a) :
  EqVal Γ M N A h.
Proof.
dependent destruction h.
       destruct a eqn:EQa; try done.
Qed.


(* ============================================================
   Val <-> ValTy  and  EqVal <-> EqValTy
   ============================================================ *)

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a (h : wt a tuniv):
  EqValTy Γ A B h ->
  EqVal Γ A B Core.tuniv h.
Proof.
  dependent destruction h; try done.
  all: cbn.
  all: move=> [hA [hB h1]].
  all: eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a (h : wt a tuniv):
  EqVal Γ A B C h ->
  EqValTy Γ A B h.
Proof.
  dependent destruction h; try done.
  all: cbn in *.
  all: eauto.
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv):
  ValTy Γ A h ->
  Val Γ A Core.tuniv h.
Proof.
  dependent destruction h; try done.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a (h : wt a tuniv):
  Val Γ A Core.tuniv h ->
  ValTy Γ A h.
Proof.
  dependent destruction h; try done.
Qed.

                                  


(* ============================================================
   Diagonal embedding
   Val <-> EqVal  and  ValTy → EqValTy
   ============================================================ *)


Fixpoint Val_EqVal {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) {struct h} :
  Val Γ M A h -> EqVal Γ M M A h.
Proof.
+ dependent destruction h.
  all: cbn.
  all: eauto.
  - destruct a; try done.
  - 
    move=> [M1 [h1 V1]].
    exists M1. split; auto.
    exists M1. split; auto.
  - (* tpi *) 
    move=>h1.
    repeat split; eauto.
    clear A.
    destruct h1 as (A & B & HR &  TA & TB & VPi & ValA & PEV & PEE).
    exists A, B. split; auto.
    exists A, B. split; auto.
    repeat split; auto.
    eapply c_refl; eauto.
    eapply c_refl; eauto. 
    move=> u v Vu APP NB P TP VA.
    unfold PiEdgeEq in PEE.
    specialize (PEV u v Vu APP NB).
    specialize (PEE u v Vu APP NB).
    eapply EqVal_EqValTy.
    eapply PEE.
    eapply c_refl; eauto.
    cbn.
    eapply Val_EqVal. eapply VA.
  - (* abs *)
    move=> [HR PAV].
    inversion h. subst.
    repeat split; eauto.
    unfold Rec.ValPi in PAV.
    destruct PAV as [A0 [B0 [R1 PAV]]].
    unfold EqValPi.
    exists A0, B0. split; eauto.
    unfold PiAppEqVal.
    unfold PiAppVal in PAV.
    move=> u v t Vu APP NB APPg P TP VP.
    specialize (PAV u v t Vu APP NB APPg P TP VP).
    eapply Val_EqVal.
    cbn. cbn in PAV.
    auto.
Defined.


(* ValTy2-to-EqValTy2 *)
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u (h : wt u tuniv) :
  ValTy Γ M h -> EqValTy Γ M M h.
Proof.
  intros VT.
  eapply EqVal_EqValTy.
  eapply Val_EqVal.
  eapply ValTy_Val.
  auto.
Qed.


(* ============================================================
   Level 1 — projecting first and second parts of EqVal
   EqVal_Val1, EqVal_Val2
   ============================================================ *)


Fixpoint EqVal_Val1 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M N A h -> Val Γ M A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  (* 2 nontrivial goals *)
  - destruct a; try done.
  - move=> [M1 [h1 [N1 [h2 V1]]]].
    exists M1. split; auto.
    eauto.
Qed.


Fixpoint EqVal_Val2 {n} (Γ : Ctx n) (M N A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M N A h -> Val Γ N A h.
Proof.
  dependent destruction h.
  all: cbn.
  all: eauto.
  (* 2 nontrivial goals *)
  - destruct a; try done.
  - move=> [M1 [h1 [N1 [h2 V1]]]].
    exists N1. split; auto.
    eauto.
Qed.

(* ============================================================
   Level 1a — 
   Head reduction/expansion
   ============================================================ *)

Lemma HeadRed_expand {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M'  (Core.tpi A B) ->
  HeadRed M (Core.tpi A B).
Proof.
  move=> R HR.
  eapply ms_trans; eauto.
Qed.

Lemma HeadRed_contract {n} (M M' : Tm n) A B :
  HeadRed1 M M' ->
  HeadRed M  (Core.tpi A B) ->
  HeadRed M' (Core.tpi A B).
Proof.
Admitted.

Lemma ValTy_HeadRed1_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed1 M' M -> ValTy Γ M h -> ValTy Γ M' h.
Proof. 
  move=> R.
  dependent destruction h.
  all: cbn; try done.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0. exists B0.
  repeat split; eauto.
  eapply HeadRed_expand; eauto.
Qed.

(* ValTy2-headred-expand *)
Lemma ValTy_HeadRed_expand {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed M' M -> ValTy Γ M h -> ValTy Γ M' h.
Proof. 
  move=> R. induction R.
  - done.
  - move=> h1. specialize (IHR h1). 
    eapply ValTy_HeadRed1_expand in H; eauto.
Qed.

  

Lemma ValTy_HeadRed1_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed1 M M' -> ValTy Γ M h -> ValTy Γ M' h.
Proof. 
  move=> R. 
  dependent destruction h.
  all: cbn; try done.
  move=> [A0 [B0 [R0 [TA0 [TB0 [Vpi [VA [PEV PEE]]]]]]]].
  exists A0. exists B0.
  repeat split; eauto.
  eapply HeadRed_contract; eauto.
Qed.



(* ValTy2-headred-contract *)
Lemma ValTy_headred_contract {n} (Γ : Ctx n) (M M' : Tm n) u (h : wt u tuniv) :
  HeadRed M M' -> ValTy Γ M h -> ValTy Γ M' h.
Proof. 
  move=> R. induction R.
  - done.
  - admit.
Admitted.


(* ============================================================
   upValTy / downValTy — stated before the mutual block.

   Each is parameterized by the mutual-block lemma its proof
   relies on, so it can be applied inside the mutual block by
   passing the appropriate fixpoint reference at the call site.
   ============================================================ *)

(* downValTy: shrink the term-side element u (same type tuniv).
   Derivable from [restrictVal] of the mutual block. *)
Lemma downValTy_pre
  (restrictVal :
    forall n (Γ : Ctx n) (M T : Tm n) u u' a
           (h0 : wt u' a) (h1 : wt u a),
           le u' u -> Val Γ M T h1 -> Val Γ M T h0)
  {n} (Γ : Ctx n) (M : Tm n) u0 u1
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) :
  le u0 u1 -> ValTy Γ M h1 -> ValTy Γ M h0.
Proof.
  move=> LE VT1.
  apply Val_ValTy. apply ValTy_Val in VT1.
  eapply restrictVal; eauto.
Qed.


(* ============================================================
   down/up
   ============================================================ *)



Lemma upValPi : forall 
        (upVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                   (h0 : wt u a0) (h1 : wt u a1)  
                   (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv), 
            le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
        (downVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                     (h0 : wt u a0) (h1: wt u a1),
            le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0)
        f a g a0 g0 
        (LEa : le a a0) 
        (LEg : le_fun g g0)           
        (h  : wt (abs f) (tpi a g))
        (h0 : wt (abs f) (tpi a0 g0))
        (hUa1 : wt (tpi a0 g0) tuniv)
        {n} (Γ : Ctx n) (M T : Tm n),
        ValPi Γ M T h -> 
        ValTy Γ T hUa1 ->
        ValPi Γ M T h0.
Proof.
      move=> upVal downVal f a g a0 g0 LEa LEg h h0 hUa1 n Γ M T VP VTya1 .
      dependent destruction hUa1.
      destruct VTya1 as (Av & Bv & HRv & TAv & TBv & Vpi & VDv & PEV & PEE).        

      unfold Rec.ValPi in VP.
      destruct VP as (A0 & B0 & R1 & PAV).
      (* types are the same *)
      destruct (HeadRed_tpi_det HRv R1) as [-> ->].

      unfold Rec.ValPi.
      exists A0, B0.
      repeat split; try eassumption.
      move=> u v t0 Vu APP NB APPg0 N TN VN.
      cbn. cbn in VN.

      have WTpi : wt (tpi a g) tuniv.  eapply wt_ty_tuniv; eauto.
      have Vg: valid_fun g. eapply valid_tpi2. eauto with valid.
      have Vg0: valid_fun g0. eapply valid_tpi2. eauto with valid.
      destruct (valid_app_exists Vg Vu) as [t [APPg Vt]].
      have LEt: le t t0. { eapply (@le_fun_mono g g0 u); eauto. } 

      have WTt: wt t tuniv. 
      { destruct (is_bot t) eqn:EQ. destruct t; try done.
        eapply wt_bot. eapply wt_tuniv.
        inversion WTpi. eapply (H3 _ _ Vu); eauto. } 
      have WTv: wt v t.
      { inversion h. eapply (H3 u v t); eauto. } 
      have NBt: ~(is_bot t).
      { move=>IB. destruct t; try done. inversion WTv. subst. done. } 
      have NBt0: ~(is_bot t0).
      { move=>IB. destruct t0; destruct t; try done. }  
      have WTu: wt u a0. { eauto. } 

      unfold PiAppVal in PAV.
      specialize (PAV u v t Vu APP NB APPg N TN).
      specialize (PEV u t0 Vu APPg0 NBt0 WTu N TN).
      cbn in PAV.
      eapply upVal. 
        ++ eapply WTt. 
        ++ eapply LEt.
        ++ eapply PAV.
           eapply downVal. eapply LEa. eapply VN.
        ++ eapply ValTy_Val. 
           eapply PEV.
           cbn.
           erewrite (wt_unique (w u t0 Vu APPg0 NBt0)).
           eapply VN.
Defined.

Lemma downValPi : forall 
        (upVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                   (h0 : wt u a0) (h1 : wt u a1)  
                   (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv), 
            le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1)
        (downVal : forall {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
                     (h0 : wt u a0) (h1: wt u a1),
            le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0)
        f a g a0 g0 
        (LEa : le a a0) 
        (LEg : le_fun g g0)           
        (h  : wt (abs f) (tpi a g))
        (h0 : wt (abs f) (tpi a0 g0))
        (hUa : wt (tpi a g) tuniv)
        {n} (Γ : Ctx n) (M T : Tm n),
        ValPi Γ M T h0 -> 
        ValTy Γ T hUa ->
        ValPi Γ M T h.
Proof.
  move=> upVal downVal f a g a0 g0 LEa LEg h h0 hUa n Γ M T VP VT.
  unfold Rec.ValPi in VP.
  destruct VP as (A0 & B0 & R1 & PAV).
  unfold ValPi.
  exists A0, B0.
  repeat split; try eassumption.

  (* downPiAppVal *)
  move=> u v t Vu APP NB APPg N TN VN.
  cbn. cbn in VN.

  have WTpi : wt (tpi a g) tuniv.  eapply wt_ty_tuniv; eauto.
  have Vg: valid_fun g. eapply valid_tpi2. eauto with valid.
  have Vg0: valid_fun g0. eapply valid_tpi2. eauto with valid.
  destruct (valid_app_exists Vg0 Vu) as [t0 [APPg0 Vt0]].
  have LEt: le t t0. { eapply (@le_fun_mono g g0 u); eauto. } 

  have WTt: wt t tuniv. 
  { destruct (is_bot t) eqn:EQ. destruct t; try done.
    eapply wt_bot. eapply wt_tuniv.
    inversion WTpi. eapply (H3 _ _ Vu); eauto. } 
  have WTv: wt v t.
  { inversion h. eapply (H3 u v t); eauto. } 
  have NBt: ~(is_bot t).
  { move=>IB. destruct t; try done. inversion WTv. subst. done. } 
  have NBt0: ~(is_bot t0).
  { move=>IB. destruct t0; destruct t; try done. }  
  have WTa: wt a tuniv. inversion WTpi. done.
  unfold PiAppVal in PAV.
  specialize (PAV u v t0 Vu APP NB APPg0 N TN).

  cbn in PAV.
  eapply downVal. 
  ++ eapply LEt.
  ++ eapply PAV.
     eapply upVal. eapply WTa. eapply LEa. eapply VN.
Admitted.


(* Annoyingly, struct on first derivation is not enough. Need
   to do struct on *both* wt derivations simultaneously to
   show the termination of this proof.

   For now, admitting the termination check.
*)

(* upVal/upEqVal mirror the Agda upVal2/upEqVal2 signatures: they take
   the ValTy of the syntactic type T at the bigger universe-element a1
   as an extra argument (a "Val Γ T Core.tuniv hUa1", which by
   definitional unfolding is ValTy Γ T hUa1).                          *)
Fixpoint upVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1)  
  (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) {struct h1}:
  le a0 a1 -> Val Γ M T h0 -> Val Γ T Core.tuniv hUa1 -> Val Γ M T h1
with upEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1)  
  (hUa0 : wt a0 tuniv) (hUa1 : wt a1 tuniv) {struct h1}:
  le a0 a1 -> EqVal Γ M N T h0 -> Val Γ T Core.tuniv hUa1 -> EqVal Γ M N T h1
with downVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0
with downEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> EqVal Γ M N T h1 -> EqVal Γ M N T h0
with restrictVal {n} (Γ : Ctx n) (M T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> Val Γ M T h1 -> Val Γ M T h0
with restrictEqVal {n} (Γ : Ctx n) (M N T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.  
  - (* upVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto.
    + (* tnat *)
      move=> _ h3 _. cbn in h3. move: h3 => [M1 [RM1 VM1]].
      exists M1. split. auto. 
      cbn.
      rewrite (wt_unique h0 h1) in VM1.
      done.

    + (* tuniv <= tuniv *)
      move=> LE VT _.
      cbn [Val] in VT |- *.
      erewrite (wt_unique (wt_tpi h1 w1 w2 i0)).
      eapply VT.
      (* nothing to do here as only tuniv <= tuniv *)

    + (* tpi a g <= tpi a0 g0 *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE. apply andb_prop in LE. destruct LE as [LEa LEg].
      move=> VAL VTa1.
      split.
      * apply Val_ValTy in VTa1. 
        erewrite (wt_unique hUa1) in VTa1.
        eapply VTa1.
      * (* need to use VTa1 *)
        move: (Val_ValTy VTa1) => VTya1.
        (* also need VP *)
        cbn [Val] in VAL |- *. 
        destruct VAL as [VT VP].
        eapply (upValPi upVal downVal LEa LEg); eauto.

  - (* upEqVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto.
    + (* tnat *)
      move=> _ [M1 [RM1 [N1 [RN1 EVM]]]] _.
      exists M1. split. auto.
      exists N1. split. auto.
      rewrite (wt_unique h0 h1) in EVM.
      done.
    + (* tuniv <= tuniv *)
      move=> LE EqV VT.
      erewrite (wt_unique (wt_tpi h1 w1 w2 i0)).
      eapply EqV.

    + (* tpi a g <= tpi a0 g0 *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE. apply andb_prop in LE. destruct LE as [LEa LEg].
      move=> EqVAL VTa1.
      cbn [EqVal] in EqVAL |- *. 
      destruct EqVAL as (VT & VPM & VPN & EVP).

      apply Val_ValTy in VTa1. 
      erewrite (wt_unique hUa1) in VTa1.
      repeat split.
      * eapply VTa1.
      * eapply (upValPi upVal downVal LEa LEg); eauto. 
      * eapply (upValPi upVal downVal LEa LEg); eauto. 
      * (* need upEqValPi lemma *)
        admit. 

  - (* downVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto; done.
    + (* tnat *)
      move=> _ [M1 [RM1 VM1]].
      exists M1. split. auto.
      rewrite (wt_unique h1 h0) in VM1.
      done.
    + (* tuniv <= tuniv *)
      move=> _ VT.
      erewrite (wt_unique (wt_tpi h1 w1 w2 i0)) in VT.
      eapply VT.
    + (* tpi *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE. apply andb_prop in LE. destruct LE as [LEa LEg].
      move=> VAL.
      cbn [Val] in VAL |- *. 
      destruct VAL as (VT & VP).
      split.
      * eapply Val_ValTy.
        eapply ValTy_Val in VT.
        eapply restrictVal; eauto.
        rewrite le_tpi. rewrite LEa. rewrite LEg. done.
      * eapply (downValPi upVal downVal LEa LEg); eauto. 
        eapply Val_ValTy.
        eapply ValTy_Val in VT.
        eapply restrictVal; eauto.
        rewrite le_tpi. rewrite LEa. rewrite LEg. done.

  - (* downEqVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + destruct a; destruct a0; cbn; auto; done.
    + move=> _ [M1 [RM1 [N1 [RN1 EVM]]]].
      exists M1. split. auto.
      exists N1. split. auto.
      rewrite (wt_unique h1 h0) in EVM.
      done.
    + move=> _ EV.
      erewrite (wt_unique (wt_tpi h0 w w0 i)).
      eapply EV.
    + (* tpi *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE. apply andb_prop in LE. destruct LE as [LEa LEg].
      move=> VAL.
      cbn [EqVal] in VAL |- *. 
      destruct VAL as (VT & VPM & VPN & EVP).
      repeat split.
      * eapply Val_ValTy.
        eapply ValTy_Val in VT.
        eapply restrictVal; eauto.
        rewrite le_tpi. rewrite LEa. rewrite LEg. done.
      * eapply (downValPi upVal downVal LEa LEg); eauto. 
        eapply Val_ValTy.
        eapply ValTy_Val in VT.
        eapply restrictVal; eauto.
        rewrite le_tpi. rewrite LEa. rewrite LEg. done.
      * eapply (downValPi upVal downVal LEa LEg); eauto. 
        eapply Val_ValTy.
        eapply ValTy_Val in VT.
        eapply restrictVal; eauto.
        rewrite le_tpi. rewrite LEa. rewrite LEg. done.
      * (* downEqValPi *)
        admit.
  - (* restrictVal *)
    dependent destruction h1.
    (* bot <= bot *)
    1: { move=> LE. apply le_bot_inv in LE. subst.
         move=> h. erewrite (wt_unique h0). eapply h.
    } 
    all: dependent destruction h0.
    all: try solve [cbn; done].
    + (* succ <= succ *)
      rewrite le_succ. move => LE VM.
      destruct VM as [n1 [R1 T1]].
      exists n1. split; auto.
      cbn in T1 |- *. 
      eapply restrictVal; eassumption.
    + (* tpi a g <= tpi a0 g0 *)
      rewrite le_tpi.
      move=> /andP. move=> [LEa LEg].
      move=> VM.
      cbn [Val] in VM |- *.
      destruct VM as (A & B & R1 & TA & TB & Vtpi & VA & PEV & PEE).
      exists A. exists B. repeat split; eauto.
      * (* PEV *)
        move=> u v Vu APP NB WTu N TN VN.
        have Vg : valid_fun g. eapply valid_tpi2. eauto. 
        have Vg0 : valid_fun g0. eapply valid_tpi2. eauto. 
        destruct (valid_app_exists Vg0 Vu) as [v0 [APP0 Vv0]].
        move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEv.
        have NB0: ~ (is_bot v0). { destruct v0; destruct v; try done. } 
        have WTua0: wt u a0. eapply wt_le; eauto.
        specialize (PEV _ _  Vu APP0 NB0 WTua0 N TN).
        cbn in VN , PEV |- *.
        eapply Val_ValTy.
        eapply restrictVal; eauto.
        eapply ValTy_Val.
        eapply PEV.
        eapply upVal. 3: eassumption. 2: eassumption. eapply wt_ty_tuniv; eauto.
        eapply VA.
      * (* PEE *) 
        admit.
    + (* abs f <= abs f0 *)
      rewrite le_abs.
      move=> LEf VM.
      cbn in VM |- *.
      move: VM => [ VTT VPM].
      split.
      * erewrite (wt_unique h0). eapply VTT.
      * admit.
  - (* restrictEqVal *)
    admit.
Admitted.


(*


      move=> LE EV.
      cbn in EV |- *.
      destruct EV as [VTm [VTn EVT]].
      split; [|split].
      * destruct VTm as (Am & Bm & RAm & TAm & TBm & Vpim & VVm & PEVm & PEEm).
        rewrite (wt_pi_fun_unique w0 w) in PEVm, PEEm.
        rewrite (wt_unique h1 h0) in VVm.
        exists Am, Bm; repeat split; eassumption.
      * destruct VTn as (An & Bn & RAn & TAn & TBn & Vpin & VVn & PEVn & PEEn).
        rewrite (wt_pi_fun_unique w0 w) in PEVn, PEEn.
        rewrite (wt_unique h1 h0) in VVn.
        exists An, Bn; repeat split; eassumption.
      * cbn in EVT |- *.
        destruct EVT as (VTmE & VTnE & Ae & Be & RAe & Ae' & Be' & RAe' &
                         CA & CB & VTpie & EVD & PEET).
        split.
        { destruct VTmE as (AmE & BmE & RAmE & TAmE & TBmE & VpimE & VVmE & PEVmE & PEEmE).
          rewrite (wt_pi_fun_unique w0 w) in PEVmE, PEEmE.
          rewrite (wt_unique h1 h0) in VVmE.
          exists AmE, BmE; repeat split; eassumption. }
        split.
        { destruct VTnE as (AnE & BnE & RAnE & TAnE & TBnE & VpinE & VVnE & PEVnE & PEEnE).
          rewrite (wt_pi_fun_unique w0 w) in PEVnE, PEEnE.
          rewrite (wt_unique h1 h0) in VVnE.
          exists AnE, BnE; repeat split; eassumption. }
        exists Ae, Be; split; [exact RAe|].
        exists Ae', Be'; split; [exact RAe'|].
        rewrite (wt_pi_fun_unique w0 w) in PEET.
        rewrite (wt_unique h1 h0) in EVD.
        repeat split; eassumption.
    + (* tpi *)
      (* Mirror Agda Validity2.agda: downEqVal2 PiCode case.
         EqVal at (abs f) (tpi a g) is
            ValTy /\ ValPi M /\ ValPi N /\ EqValPi M N. *)
      have Vtpi : valid (tpi a g). eauto with valid.
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE.
      apply andb_prop in LE.
      destruct LE as [LEa LEg].
      move=> EVAL.
      cbn in EVAL.
      unfold Rec.ValPi, Rec.EqValPi in EVAL.
      destruct EVAL as [VT [VPM [VPN EPI]]].
      destruct VPM as [A0_M [B0_M [R_M PAV_M]]].
      destruct VPN as [A0_N [B0_N [R_N PAV_N]]].
      destruct EPI as [A0_E [B0_E [R_E PAEV]]].
      cbn. split; [|split; [|split]].
      * destruct VT as (Am & Bm & RAm & TAm & TBm & Vpim & VVm & PEVm & PEEm).
        exists Am, Bm.
        repeat split; try eassumption.
        eapply restrictVal; eauto.
        eapply downPiEdgeVal; eauto.
        eapply downPiEdgeEq; eauto.
      * unfold Rec.ValPi. exists A0_M, B0_M. split. exact R_M.
        eapply downPiAppVal; eauto.
      * unfold Rec.ValPi. exists A0_N, B0_N. split. exact R_N.
        eapply downPiAppVal; eauto.
      * unfold Rec.EqValPi. exists A0_E, B0_E. split. exact R_E.
        eapply downPiAppEqVal; eauto.
  - (* upPiAppVal: takes extra PiEdgeVal 
       at the bigger pi (mirror of Agda's piEV1). *)
    intros LE LEg piEV1 PA.
    dependent destruction h0.
    + (* wt_abs_nil *) dependent destruction h1. cbn. trivial.
    + (* wt_abs_cons *)
      dependent destruction h1.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * (* Tail recursion: pass the OUTER hPi0/hPi1 (unchanged, since g/b are
           preserved) and the TAIL h0/h1 (subderivations from dep destr). *)
        exact (@upPiAppVal _ _ _ _ _ _ _ _ _ _ hPi0 hPi1 h0 h1 LE LEg piEV1 PA_rec).
      * 
        move=> P TP VP1.
        move: (@downVal _ Γ P A0 ui a a0 w w1 LE VP1) => VP.
        specialize (PA_forall P TP VP).
        have Vg: valid_fun g. eapply valid_tpi2. eauto with valid.
        have Vg0: valid_fun g0. eapply valid_tpi2. eauto with valid.
        have LEt: le t t0.
        { eapply (@le_fun_mono g g0); eauto. 
          eauto with valid. } 
        have WTt0: wt t0 tuniv. eapply wt_ty_tuniv; eauto.
        have LEMMA : forall n (Γ : Ctx n) P A0 B0 g0 a0 ui t0
             (hPi1 : wt_pi_fun g0 a0)
             (piEV1 : PiEdgeVal Γ A0 B0 hPi1)
             (e0 : app g0 ui = Some t0)
             (w1 : wt ui a0)
             (WTt0 : wt t0 tuniv),
             (typing Γ P A0) -> 
             (Val Γ P A0 w1) ->
             Val Γ B0[P..] Core.tuniv WTt0.
        { clear. 
          move=> n Γ P A0 B0 g0.
          all: move=> a0 ui t0 hPi1 PEV APP w1 w2 T1 V1.
          - admit.
          - move=> APP w1 WTt0 TO VP.
            destruct a as [u v].
            inversion hPi1. subst. 
            rewrite app_cons_eq in APP.
        } 
        have ValT: Val Γ B0[P..] Core.tuniv WTt0.
        { eapply LEMMA; eauto.  } 
        eapply upVal. 2: exact LEt. 
        eapply wt_ty_tuniv; eauto.
        eauto.
        eauto.

  - (* downPiAppVal *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + dependent destruction h0.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * (* Tail recursion on the wt_abs_fun tails h0, h1 (subderivations). *)
        exact (@downPiAppVal _ _ _ _ _ _ _ _ _ _ h0 h1 LE LEg PA_rec).
      * admit.
  - (* upPiAppEq *)
    intros LE LEg PEV PA.
    dependent destruction h0.
    + dependent destruction h1. cbn. trivial.
    + dependent destruction h1.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * exact (@upPiAppEq _ _ _ _ _ _ _ _ _ _ hPi0 hPi1 h0 h1 LE LEg PEV PA_rec).
      * admit.
  - (* downPiAppEq *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + dependent destruction h0.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * exact (@downPiAppEq _ _ _ _ _ _ _ _ _ _ h0 h1 LE LEg PA_rec).
      * admit.
  - (* upPiAppEqVal *)
    intros LE LEg PEV PA.
    dependent destruction h0.
    + dependent destruction h1. cbn. trivial.
    + dependent destruction h1.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * exact (@upPiAppEqVal _ _ _ _ _ _ _ _ _ _ _ hPi0 hPi1 h0 h1 LE LEg PEV PA_rec).
      * admit.
  - (* downPiAppEqVal *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + dependent destruction h0.
      cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * exact (@downPiAppEqVal _ _ _ _ _ _ _ _ _ _ _ h0 h1 LE LEg PA_rec).
      * admit.
  - (* downPiEdgeVal *)
    intros LE LEf PE.
    dependent destruction h0.
    + (* wt_pi_nil: PiEdgeVal at nil is True *)
      cbn. trivial.
    + (* wt_pi_cons: needs to find a corresponding entry in h1 via le_fun;
         the forall-part also needs cross-witness Val transport. *)
      admit.
  - (* downPiEdgeEq *)
    intros LE LEf PE.
    dependent destruction h0.
    + cbn. trivial.
    + admit.
  - (* downPiEdgeEqTy *)
    intros LE LEf PE.
    dependent destruction h0.
    + cbn. trivial.
    + admit.
  - (* restrictVal: shrink the term-side u (same a, smaller u' ≤ u). *)
    admit.
  - (* restrictEqVal *)
    admit.
Admitted.


(* ---- down on ValTy / EqValTy ---- *)

(* downValTy2 *)
Lemma downValTy {n} (Γ : Ctx n) (M : Tm n) u0 u1 
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) :
  le u0 u1 -> ValTy Γ M h1 -> ValTy Γ M h0.
Proof.
    move=> LE VT1.
    eapply Val_ValTy.
    apply ValTy_Val in VT1.
    eapply restrictVal; eauto.
Qed.

(* downEqValTy2 *)
Lemma downEqValTy {n} (Γ : Ctx n) (M N : Tm n) u0 u1 
  (h0 : wt u0 tuniv) (h1 : wt u1 tuniv) :
  le u0 u1 -> EqValTy Γ M N h1 -> EqValTy Γ M N h0.
Proof.
    move=> LE VT1.
    eapply EqVal_EqValTy.
    apply EqValTy_EqVal in VT1.
    eapply restrictEqVal; eauto.
Qed.
*)


(* ValTy2-Sup: if a1 and a2 are universe-members and lub a1 a2 = Some a,
   ValTy at a1 and a2 lifts to ValTy at the lub. *)
Fixpoint ValTy_Sup {n} (Γ : Ctx n) (T : Tm n) a1 a2 a 
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) {struct h}:
  lub a1 a2 = Some a ->
  ValTy Γ T h1 -> ValTy Γ T h2 -> ValTy Γ T h.
Proof.
Abort.

(* EqValTy2-Sup *)
Lemma EqValTy_Sup {n} (Γ : Ctx n) (M N : Tm n) a1 a2 a 
  (h1 : wt a1 tuniv) (h2 : wt a2 tuniv) (h : wt a tuniv) :
  lub a1 a2 = Some a ->
  EqValTy Γ M N h1 -> EqValTy Γ M N h2 -> EqValTy Γ M N h.
Proof. 
Abort.


(* ----------------------------------------------------- *)

Fixpoint Val_EqVal_fwd {n} (Γ : Ctx n) (M A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv)
  {struct h} :
  Val Γ M A h -> EqValTy Γ A B h' -> Val Γ M B h
with EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n)  (h' : wt a tuniv)
  {struct h} :
  EqVal Γ M N A h -> EqValTy Γ A B h' -> EqVal Γ M N B h
with EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) { struct h } :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M1 A h
with EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M3 A h -> EqVal Γ M1 M3 A h.
Proof.
  - (* Val_EqVal_fwd *)
    move=> VM EVTA.
    dependent destruction h';
      dependent destruction h.
    all: try solve [cbn; try done].
    cbn [EqValTy] in EVTA.
    cbn in VM  |- *.
    move: EVTA => [VTA [VTB [A0 [B0 [R0 [A1 [B1 [R1 [CA [CB [Vtpi [EVA PEET]]]]]]]]]]]].
    split.
    * erewrite (wt_unique h). eapply VTB.
    * unfold ValPi.
      exists A1, B1. split; auto.
      unfold Rec.PiAppVal.
      move=> u v t Vu APP NB APPg P TP VP.
      specialize (PEET u t Vu APPg).
      move: (w0 u v t Vu APP NB APPg) => WTv.
      have NBt : ~ (is_bot t).
      { destruct v; destruct t; inversion WTv; try done. } 
      specialize (PEET NBt P). cbn in PEET |- *. cbn in VP. cbn in EVA.
      admit.
  - (* EqVal_EqVal_fwd *)
    admit.
  - (* EqVal_sym *)
    admit.
  - (* EqVal_trans *)
    admit.
Admitted.



(* EqValTy2-sym *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u (h : wt u tuniv) :
  EqValTy Γ M N h -> EqValTy Γ N M h.
Proof.
  move=>h1. eapply EqVal_EqValTy. eapply EqVal_sym.
  eapply EqValTy_EqVal. done.
Qed.

(* EqValTy2-trans *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u (h : wt u tuniv) :
  EqValTy Γ A B h -> EqValTy Γ B C h -> EqValTy Γ A C h.
Proof.
  move=> h1 h2.
  eapply EqVal_EqValTy. eapply EqVal_trans.
  eapply EqValTy_EqVal. eauto.
  eapply EqValTy_EqVal. eauto.
Qed.

(* ============================================================
   Translations of theorem statements from Validity2.agda
   ------------------------------------------------------------

   Translation conventions (Agda → Rocq):
     FinMem u a              ≈  wt u a
     FinMem b UCode          ≈  wt b tuniv         (some i)
     Coherent u              ≈  valid u                (implicit in wt)
     CoherentFun g           ≈  valid_fun g            (implicit in wt (abs g) ..)
     CoherentFunTail f       ≈  valid_fun f            (implicit in wt (tpi _ f) ..)
     FinMemFun g b f         ≈  wt (abs g) (tpi b f)
     FinMemAllU f b          ≈  wt (tpi b f) tuniv (codomains in U_i)
     LeCode u v              ≈  le u v
     LeFunCode f g           ≈  le_fun f g
     Comp u v                ≈  compatible u v
     Sup u v = w             ≈  lub u v = Some w
     Selection f u v         ≈  In (u, v) f
     EvalFun f u = v         ≈  app f u = Some v
     subst1 B N              ≈  B[N..]
     HasType / ConvTm        ≈  typing / conv
     HeadRed                 ≈  HeadRed (multi reduction)

   Closed terms (Tm 0) are used throughout.

   ------------------------------------------------------------
   Dependency stratification of the mutual block.

   The Agda mutual block of Validity2.agda decomposes into the
   following strongly-connected components, in topological order
   (a level may only call itself or earlier levels):

     Level 1 (no recursive calls in the mutual block):
       - EqVal_Val1                   (Val2-from-EqVal2-first)
       - EqVal_Val2                   (Val2-from-EqVal2-second)
       - ValTy_headred_expand         (ValTy2-headred-expand)
       - ValTy_headred_contract       (ValTy2-headred-contract)

     Level 2 (calls into Level 1 only):
       - EqValTy_headred_expand       (uses ValTy_headred_expand)
       - EqValTy_headred_contract     (uses ValTy_headred_contract)

     Level 3 (4-way SCC, plus dependencies on Levels 1-2):
       Val_beta_expand  ↔  ValPi_headred_expand
                        ↔  EqVal_headred_expand
                        ↔  EqValPi_headred_expand

     Level 4 (4-way SCC, plus dependencies on Levels 1-2):
       Val_headred_contract  ↔  ValPi_headred_contract
                             ↔  EqVal_headred_contract
                             ↔  EqValPi_headred_contract

     Level 5 (2-way SCC, independent of Levels 3-4):
       Val_EqVal  ↔  ValTy_EqValTy

     Level 6 (BIG SCC, ~30 lemmas, depends only on Levels 1, 5):
       { EqValTy_sym, EqValTy_trans, EqVal_sym, EqVal_trans,
         Val_EqVal_fwd, EqVal_EqVal_fwd, ValTy_Sup, EqValTy_Sup,
         downVal, downEqVal, downValTy, downEqValTy,
         upVal, upEqVal, restrictVal, restrictEqVal,
         downPiAppVal, downPiAppEq, downPiAppEqVal,
         upPiAppVal, upPiAppEq, upPiAppEqVal,
         transportPiEdgeVal_sel, transportPiEdgeEq_sel,
         transportPiEdgeEqTy_sel,
         restrictPiAppVal_sel, restrictPiAppEq_sel,
         restrictPiAppEqVal_sel,
         restrictVal_PiCode, restrictEqVal_PiCode }

     Cycles in Level 6 (sample):
       downVal → downValTy → transportPiEdgeVal_sel → upVal
              → upPiAppVal → downVal
       restrictVal → restrictVal_PiCode → restrictPiAppVal_sel
                   → restrictVal
       Val_EqVal_fwd → restrictVal → upPiAppVal → ... → Val_EqVal_fwd
   ============================================================ *)



(* ============================================================
   Level 2 — depends on Level 1
   ============================================================ *)

(* EqValTy2-headred-expand *)
Lemma EqValTy_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValTy Γ M1 M2 h -> EqValTy Γ M1' M2' h.
Proof. Admitted.

(* EqValTy2-headred-contract *)
Lemma EqValTy_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u 
  (h : wt u tuniv) :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValTy Γ M1 M2 h -> EqValTy Γ M1' M2' h.
Proof. Admitted.


(* ============================================================
   Level 3 — 4-way SCC for HeadRed expand on Val/EqVal/ValPi/EqValPi
   ============================================================ *)

(* Val2-beta-expand *)
Lemma Val_beta_expand {n} (Γ : Ctx n) (M M' T : Tm n) u a (h : wt u a) :
  HeadRed M' M -> Val Γ M T h -> Val Γ M' T h.
Proof. Admitted.

(* EqVal2-headred-expand *)
Lemma EqVal_headred_expand {n} (Γ : Ctx n) (M M' N N' T : Tm n) u a (h : wt u a) :
  HeadRed M' M -> HeadRed N' N ->
  EqVal Γ M N T h -> EqVal Γ M' N' T h.
Proof. Admitted.

(* ValPi2-headred-expand *)
Lemma ValPi_headred_expand {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M' M -> ValPi Γ M T h -> ValPi Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-expand *)
Lemma EqValPi_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValPi Γ M1 M2 T h -> EqValPi Γ M1' M2' T h.
Proof. Admitted.


(* ============================================================
   Level 4 — 4-way SCC for HeadRed contract
   ============================================================ *)

(* Val2-headred-contract *)
Lemma Val_headred_contract {n} (Γ : Ctx n) (M M' T : Tm n) u a (h : wt u a) :
  HeadRed M M' -> Val Γ M T h -> Val Γ M' T h.
Proof. Admitted.

(* EqVal2-headred-contract *)
Lemma EqVal_headred_contract {n} (Γ : Ctx n) (M M' N N' T : Tm n) u a (h : wt u a) :
  HeadRed M M' -> HeadRed N N' ->
  EqVal Γ M N T h -> EqVal Γ M' N' T h.
Proof. Admitted.

(* ValPi2-headred-contract *)
Lemma ValPi_headred_contract {n} (Γ : Ctx n) (M M' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M M' -> ValPi Γ M T h -> ValPi Γ M' T h.
Proof. Admitted.

(* EqValPi2-headred-contract *)
Lemma EqValPi_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' T : Tm n) b f g
  (h : wt (abs g) (tpi b f)) :
  HeadRed M1 M1' -> HeadRed M2 M2' ->
  EqValPi Γ M1 M2 T h -> EqValPi Γ M1' M2' T h.
Proof. Admitted.


