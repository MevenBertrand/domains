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

Require Import findom.
Require Import types.
Require Import raw_semantics.
Require Import typing_semantics.
Require Import eval_substitution.


Import Raw.
    

(*
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
*)

(* This information is *not* availble from wt
   TODO: update wt to include it
   (And: if we want to have a recursively defined wt
   we also need to update abs)
 *)

Lemma wt_abs_dom f a g : 
  wt (abs f) (tpi a g) -> { i & wt a (tuniv i) }.
Proof.
move=> h. inversion h. subst.
inversion H4. subst. eexists. eauto.
Qed.

Lemma wt_abs_tpi f a g : 
  wt (abs f) (tpi a g) -> { i &  wt (tpi a g) (tuniv i) }.
move=> h. inversion h. subst. eexists. eauto.
Qed.

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
   PiEdgeVal : forall {n} (Γ : Ctx n)
     (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
     i (h : wt_pi_fun f b i), Prop ;
   PiEdgeEq  : forall {n} (Γ : Ctx n)
                 (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
                 i (h : wt_pi_fun f b i), Prop;
   PiEdgeEqTy: forall {n} (Γ : Ctx n) (A:Tm n) (B B': Tm (S n))
                 b f i (h : wt_pi_fun b f i), Prop;
   PiAppVal: forall {n} (Γ : Ctx n)
     (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
     (h : wt_abs_fun g b f) , Prop;
   PiAppEq :forall {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt_abs_fun g b f), Prop;
PiAppEqVal : forall {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt_abs_fun g b f), Prop

}.


Section Helpers.

(*
Inductive wt : elt -> elt -> Set :=
    wt_bot : forall (a : elt) (i : nat), wt a (tuniv i) -> wt bot a
  | wt_tuniv : forall i j : nat, i < j -> wt (tuniv i) (tuniv j)
  | wt_tnat : forall j : nat, wt tnat (tuniv j)
  | wt_zero : wt zero tnat
  | wt_succ : forall u : elt, wt u tnat -> wt (succ u) tnat
  | wt_tpi : forall (a : elt) (g : list (elt * elt)) (j : nat),
             wt_pi_fun g a j -> wt a (tuniv j) -> valid (tpi a g) -> wt (tpi a g) (tuniv j)
  | wt_abs : forall (a : elt) (f g : list (elt * elt)) (i : nat),
             wt_abs_fun f a g -> valid (abs f) -> wt (tpi a g) (tuniv i) -> wt (abs f) (tpi a g)
  with wt_pi_fun : list (elt * elt) -> elt -> nat -> Set :=
    wt_pi_nil : forall (a : elt) (i : nat), wt_pi_fun nil a i
  | wt_pi_cons : forall (a ui vi : elt) (g : list (elt * elt)) (i : nat),
                 wt ui a -> wt vi (tuniv i) -> wt_pi_fun g a i -> wt_pi_fun ((ui, vi) :: g) a i
  with wt_abs_fun : list (elt * elt) -> elt -> list (elt * elt) -> Set :=
    wt_abs_nil : forall (a : elt) (g : list (elt * elt)), wt_abs_fun nil a g
  | wt_abs_cons : forall (ui vi : elt) (f : list (elt * elt)) (a : elt) (g : list (elt * elt))
                    (t : elt),
                  wt ui a ->
                  app g ui = Some t -> wt vi t -> wt_abs_fun f a g -> wt_abs_fun ((ui, vi) :: f) a g.
*)

Variable (Rec : F).
(*
  (Val   : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> forall u a, wt u a -> Prop)
  (EqVal : forall {n} (Γ : Ctx n),
              Tm n -> Tm n -> Tm n -> forall u a, wt u a -> Prop)
  (PiEdgeVal : forall {n} (Γ : Ctx n)
     (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
     i (h : wt_pi_fun f b i), Prop)
  (PiEdgeEq  : forall {n} (Γ : Ctx n)
                 (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
                 i (h : wt_pi_fun f b i), Prop)
  (PiEdgeEqTy: forall {n} (Γ : Ctx n) A B B' b f i (h : wt_pi_fun b f i), Prop).
*)

(*
Fixpoint PiEdgeVal {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  i (h : wt_pi_fun f b i) : Prop :=
  match h with 
  | wt_pi_nil _ _ => True
  | @wt_pi_cons a ui vi g i WTui WTvi WTf => 
      PiEdgeVal Γ A B WTf /\
      forall (N : Tm n),
        typing Γ N A ->
        (* take related arguments *)
        Val Γ N A WTui ->
        (* to related results *)
        Val Γ B[N..] (Core.tuniv i) WTvi  
  end.
*)




Lemma wt_abs_inv g b f : 
  wt (abs g) (tpi b f) -> wt_abs_fun g b f.
Proof. 
  move=> h. inversion h. eauto.
Defined.

Lemma wt_tpi_dom a g i:
  wt (tpi a g) (tuniv i) -> wt a (tuniv i).
Proof.
  move=> h. inversion h. eauto.
Defined.

Lemma wt_tpi_inv a g i:
  wt (tpi a g) (tuniv i) -> wt_pi_fun g a i.
Proof.
  move=> h. inversion h. eauto.
Defined.

Definition ValPi {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) g b f (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppVal Rec Γ M A0 B0 (wt_abs_inv h) .

Definition EqValPi {n} (Γ : Ctx n)
  (M : Tm n) (N: Tm n) (A : Tm n) g b f (h : wt (abs g) (tpi b f)) :=
  exists A0, exists B0, HeadRed A (Core.tpi A0 B0)
  /\ PiAppEqVal Rec Γ M N A0 B0 (wt_abs_inv h).

Definition ValTy {n} (Γ : Ctx n)
  (M : Tm n) u i : wt u (tuniv i) -> Prop  :=
  match u return wt _ (tuniv i) -> Prop with
  | tpi b g =>
      fun (h : wt (tpi b g) (tuniv i)) =>
        (* ValTyPi M (tuniv i) *)
        (* M reduces to a pi type *)
        exists A B, HeadRed M (Core.tpi A B)

               (* the syntactic pi-type is well-typed *)
               /\ typing Γ A (Core.tuniv i)
               /\ typing (Γ ++ A) B (Core.tuniv i)

               (* the semantic pi-type is valid *)
               /\ valid (tpi b g)

               (* domain is in the relation *)
               /\ Val Rec Γ A (Core.tuniv i) (wt_tpi_dom h)

               /\ PiEdgeVal Rec Γ A B (wt_tpi_inv h) /\ PiEdgeEq Rec Γ A B (wt_tpi_inv h)

  | tnat => fun h => True
  | tuniv k => fun h => True
  | _ => fun h => True
  end.

Fixpoint EqValTy {n} (Γ : Ctx n) M N (a : elt) i (h : wt a (tuniv i)) {struct h} : Prop :=
  (match a return wt _ (tuniv i) -> Prop with
  | tpi b f =>
      fun (h : wt (tpi b f) (tuniv i))  =>
        ValTy Γ M h /\ ValTy Γ N h /\
        (* EqValTyPi Val EqVal EqValTy M N h *)
             (* both reduce to pi types *)
             exists A B, HeadRed M (Core.tpi A B)
             /\ exists A' B', HeadRed N (Core.tpi A' B')
             (* ... that are well-typed *)
             /\ conv Γ A A' (Core.tuniv i)
             /\ conv (Γ ++ A) B B' (Core.tuniv i)
             /\ valid (tpi b f)
             (* ... and the domain is in the relation *)
             /\ EqVal Rec Γ A A' (Core.tuniv i) (wt_tpi_dom h)
        /\ PiEdgeEqTy Rec Γ A B B' (wt_tpi_inv h)
  | _ => fun h => True
  end) h.

End Helpers.
End Rec.

Fixpoint Val {n} (Γ : Ctx n)
  (M : Tm n) (A : Tm n) (u : elt) (a: elt) (h : wt u a) { struct h } : Prop :=
  let Rec := Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)
  (@PiAppVal) (@PiAppEq) (@PiAppEqVal) in
      (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv i => fun (h : wt u (tuniv i)) =>
          Rec.ValTy Rec Γ M h

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with

            | abs g => fun (h : wt (abs g) (tpi b f)) =>
                        match h with 
                        | wt_abs WTf Vf (wt_tpi _ WTb _) =>
                            Rec.ValTy Rec Γ A WTb
                        | _ => True
                        end
                        
                      /\ Rec.ValPi Rec Γ M A h

            | _ => fun h => True
            end) h

      | tnat => fun h =>
          (match u return wt _ tnat -> Prop with
               | zero => fun h =>
                 HeadRed M (Core.zero)
               | succ v => fun (h : wt (succ v) tnat) =>
                 exists M1, HeadRed M (Core.succ M1)
                 /\ Val Γ M1 Core.tnat (wt_succ_inv h)
               | _ =>  fun h => True
               end) h
      | _ => fun h => True
    end) h
(* Binary logical relation *)
with EqVal {n} (Γ : Ctx n)
  (M : Tm n) (N : Tm n) (A : Tm n) (u : elt) (a: elt) (h : wt u a) { struct h } : Prop :=
  let Rec := Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal) in
       
     (match a return wt u _ -> Prop with

      | bot => fun h => True

      | tuniv i => fun (h : wt u (tuniv i)) =>

            Rec.ValTy Rec Γ M h
          /\ Rec.ValTy Rec Γ N h
          /\ Rec.EqValTy Rec Γ M N h 

      | tpi b f => fun h =>
           (match u return wt _ (tpi b f) -> Prop with
           | bot => fun h => True
           | abs g => fun (h : wt (abs g) (tpi b f)) =>
              match h with 
              | wt_abs WTf Vf (wt_tpi _ WTa _) =>
                  Rec.ValTy Rec Γ A WTa
              | _ => True
              end
             /\  Rec.ValPi Rec Γ M A h
             /\ Rec.ValPi Rec Γ N A h
             /\ Rec.EqValPi Rec Γ M N A h

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
    end) h
with 
 PiEdgeVal {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  i (h : wt_pi_fun f b i) {struct h} : Prop :=
  let Rec := Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal) in

  match h with 
  | wt_pi_nil _ _ => True
  | @wt_pi_cons a ui vi g i WTui WTvi WTf => 
      PiEdgeVal Γ A B WTf /\
      forall (N : Tm n),
        typing Γ N A ->
        (* take related arguments *)
        Val Γ N A WTui ->
        (* to related results *)
        Val Γ B[N..] (Core.tuniv i) WTvi  
  end
with
  PiEdgeEq {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) (b: elt) (f : list (elt * elt))
  i (h : wt_pi_fun f b i) {struct h} :=

  match h with 
  | wt_pi_nil _ _ => True
  | @wt_pi_cons a ui vi g i WTui WTvi WTf => 
      PiEdgeEq Γ A B WTf /\
      forall (N1 N2 : Tm n),
      conv Γ N1 N2 A ->
      (* take related arguments *)
      EqVal Γ N1 N2 A WTui ->
      (* to related results *)
      EqVal Γ B[N1..] B[N2..] (Core.tuniv i) WTvi
  end
with
  PiEdgeEqTy {n} (Γ : Ctx n) A B B' b f i (h : wt_pi_fun b f i) 
    {struct h} := 
  let Rec := Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal) in

  match h with 
  | wt_pi_nil _ _ => True
  | @wt_pi_cons a ui vi g i WTui WTvi WTf => 
      PiEdgeEqTy Γ A B B' WTf /\
        forall (P : Tm n),
          typing Γ P A ->
          (* take related arguments *)
          Val Γ P A WTui ->
          (* to related results *)
          Rec.EqValTy Rec Γ B[P..] B'[P..] WTvi
  end
with PiAppVal {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt_abs_fun g b f) : Prop :=
  match h with 
  | wt_abs_nil _ _ => True
  | @wt_abs_cons  ui vi f a g t WTui APPu WTvi WTf => 
      PiAppVal Γ M A0 B0 WTf /\
      forall (P : Tm n),
        typing Γ P A0 ->
        Val Γ P A0 WTui ->
        Val Γ (Core.app M P) B0[P..] WTvi
  end
with PiAppEq {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt_abs_fun g b f) :=
  match h with 
  | wt_abs_nil _ _ => True
  | @wt_abs_cons  ui vi f a g t WTui APPu WTvi WTf => 
      PiAppEq Γ M A0 B0 WTf /\
      forall (N1 N2 : Tm n),
        conv Γ N1 N2 A0 ->
        EqVal Γ N1 N2 A0 WTui ->
        EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..] WTvi
  end
with PiAppEqVal {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g
  (h : wt_abs_fun g b f) :=
  match h with 
  | wt_abs_nil _ _ => True
  | @wt_abs_cons  ui vi f a g t WTui APPu WTvi WTf => 
      PiAppEqVal Γ M N A0 B0 WTf /\
      forall (P : Tm n),
        typing Γ P A0 ->
        Val Γ P A0 WTui ->
        EqVal Γ (Core.app M P) (Core.app N P) B0[P..] WTvi
  end.


Notation Rec := (Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal)).



Notation ValTy := (@Rec.ValTy Rec).
Notation EqValTy := (@Rec.EqValTy Rec).
Notation ValPi := (@Rec.ValPi
      {|
        Rec.Val := @Val;
        Rec.EqVal := @EqVal;
        Rec.PiEdgeVal := @PiEdgeVal;
        Rec.PiEdgeEq := @PiEdgeEq;
        Rec.PiEdgeEqTy := @PiEdgeEqTy;
        Rec.PiAppVal := @PiAppVal;
        Rec.PiAppEq := @PiAppEq;
        Rec.PiAppEqVal := @PiAppEqVal
      |}).
Notation EqValPi := (@Rec.EqValPi (Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal))).

(* All terms in the relation have the right syntactic type. *)
Fixpoint Val_typing {n} (Γ : Ctx n) (u : elt) (a: elt)
  (M : Tm n) (A : Tm n) (h : wt u a) :
  Val Γ M A h -> typing Γ M A.
Proof.
  dependent destruction h.
  all: move=> h1.
  all: cbn in h1.
  - destruct a; try done.
Abort.


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

Lemma EqValTy_EqVal {n} (Γ : Ctx n) (A B : Tm n) a i (h : wt a (tuniv i)):
  EqValTy Γ A B h ->
  EqVal Γ A B (Core.tuniv i) h.
Proof.
  dependent destruction h; try done.
  all: cbn.
  all: move=> [hA [hB h1]].
  all: eauto.
Qed.

Lemma EqVal_EqValTy {n} (Γ : Ctx n) (A B C : Tm n) a i (h : wt a (tuniv i)):
  EqVal Γ A B C h ->
  EqValTy Γ A B h.
Proof.
  dependent destruction h; try done.
  all: cbn in *.
  all: eauto.
Qed.

Lemma ValTy_Val {n} (Γ : Ctx n) (A : Tm n) a i (h : wt a (tuniv i)):
  ValTy Γ A h ->
  Val Γ A (Core.tuniv i) h.
Proof.
  dependent destruction h; try done.
Qed.

Lemma Val_ValTy {n} (Γ : Ctx n) (A : Tm n) a i (h : wt a (tuniv i)):
  Val Γ A (Core.tuniv i) h ->
  ValTy Γ A h.
Proof.
  dependent destruction h; try done.
Qed.


(* ============================================================
   Diagonal embedding
   Val <-> EqVal  and  ValTy → EqValTy
   ============================================================ *)


Fixpoint Val_EqVal {n} (Γ : Ctx n) (M A : Tm n) u a (h : wt u a) {struct h} :
  Val Γ M A h -> EqVal Γ M M A h
with PiEdgeEq_PiEdgeEqTy {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) b f i (h : wt_pi_fun b f i) {struct h} :
  PiEdgeEq Γ A B h ->
  PiEdgeEqTy Γ A B B h
with PiAppVal_PiAppEqVal {n} (Γ : Ctx n) (M : Tm n) (A : Tm n) (B : Tm (S n)) b f g
  (h : wt_abs_fun g b f) {struct h} : 
  PiAppVal Γ M A B h -> 
  PiAppEqVal Γ M M A B h.
Proof.
+ dependent destruction h.
  all: cbn.
  all: eauto.
  - destruct a; try done.
  - move=> [M1 [h1 V1]].
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
  - move=> h1.
    repeat split; eauto.
    destruct h1 as (HR & PAV).
    dependent destruction h.
    unfold Rec.ValPi in PAV.
    destruct PAV as [A0 [B0 [R1 PAV]]].
    unfold Rec.EqValPi.
    exists A0, B0. split; eauto.
    unfold Rec.PiAppEqVal.
    unfold Rec.PiAppVal in PAV.
    eauto.
+ (* EdgeEq *)
  dependent destruction h.
  - done.
  - move=> PEE. cbn in PEE.
    move: PEE => [PEE h1].
    cbn. split. eauto.
    move=> P TP VP.
    eapply EqVal_EqValTy.
    eapply h1; eauto.
    eapply c_refl. auto.
+ dependent destruction h.
  - done.
  - move=> PAV. cbn in PAV.
    move: PAV => [PAV h1].
    cbn. split. eauto.
    move=> P TP VP.
    eapply Val_EqVal. eapply h1; eauto.
Qed.


(* ValTy2-to-EqValTy2 *)
Lemma ValTy_EqValTy {n} (Γ : Ctx n) (M : Tm n) u i (h : wt u (tuniv i)) :
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


(* ValTy2-headred-expand *)
Lemma ValTy_headred_expand {n} (Γ : Ctx n) (M M' : Tm n) u i (h : wt u (tuniv i)) :
  HeadRed M' M -> ValTy Γ M h -> ValTy Γ M' h.
Proof. Admitted.

(* ValTy2-headred-contract *)
Lemma ValTy_headred_contract {n} (Γ : Ctx n) (M M' : Tm n) u i (h : wt u (tuniv i)) :
  HeadRed M M' -> ValTy Γ M h -> ValTy Γ M' h.
Proof. Admitted.


(* ============================================================
   down/up
   ============================================================ *)

(* Annoyingly, struct on first derivation is not enough. Need 
   to do struct on *both* wt derivations simultaneously to 
   show the termination of this proof. 

   For now, admitting the termination check.
*)

Fixpoint upVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) {struct u}:
  le a0 a1 -> Val Γ M T h0 -> Val Γ M T h1
with upEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) {struct u}:
  le a0 a1 -> EqVal Γ M N T h0 -> EqVal Γ M N T h1
with downVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct u} :
  le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0
with downEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct u} :
  le a0 a1 -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.
  - (* upVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto.
    + (* tnat *)
      move=> _ [M1 [RM1 VM1]].
      exists M1. split. auto.
      eapply upVal with (a1 := tnat); eauto. 
      done.
    + (* tuniv *)
      move=> LE VT.
      cbn in LE. 
      apply Nat.eqb_eq in LE. subst j0.
      admit. (* Need some proof irrelevance for wt *)
      (* eapply VT. *)
    + (* tpi *)
      rewrite le_tpi. cbn. unfold Rec.ValPi. 
      have upPiAppVal: 
        forall f g g0 n (Γ : Ctx n) (M A0 : Tm n) B0 a a0
          (h0 : wt (abs f) (tpi a g)) 
          (h1 : wt (abs f) (tpi a0 g0)),
          le_fun g g0 
          -> PiAppVal Γ M A0 B0 h0 
          -> PiAppVal Γ M A0 B0 h1.
      { admit. }

      move=> /andP. move=> [LEa LEg] [A [B [R1 PAV]]]. 

      move: (andb_prop _ _ i0) => [Va Vg]. 
      fold valid in Va.
      fold valid in Vg. fold (valid_fun g) in Vg.
      move: (andb_prop _ _ i2) => [Va0 Vg0]. 
      fold valid in Va0. 
      fold valid in Vg0. fold (valid_fun g0) in Vg0.

      exists A, B. split; auto.
      eapply upPiAppVal; eauto.
(*
      move=> u v INf P t0 APP0 TA VP.
      specialize (h1 u v INf P).
      have Vu : valid u. eauto with valid.
      destruct (valid_app_exists Vg Vu) as [t [APP Vt]].
      move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.

      cbn.
      eapply upVal. 
      Unshelve. eapply LEt. 2: { eapply (w0 _ _ _ INf APP). } 
      eapply h1. eapply TA.
      cbn.
      eapply downVal. eapply LEa. 
      Unshelve. cbn in VP. 2: { eapply (w1 _ _ _ INf APP0). }  
      eapply VP.
  *)    
  - (* upEqVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto.
    + (* tnat *)
      move=> _ [M1 [RM1 [N1 [RN1 VM1]]]].
      exists M1. split. auto.
      exists N1. split. auto.
      eapply upEqVal with (a1 := tnat); eauto. 
      done.
    + (* tuniv *)
      move=> LE VT.
      cbn in LE. 
      apply Nat.eqb_eq in LE. subst j0.
      have EQ: (wt_tpi w w0 h0 i = wt_tpi w1 w2 h1 i0) by ext.
      (* proof irrelevance for wt? this case doesn't use recursion *)
      rewrite <- EQ.
      eapply VT.
    + (* tpi *)
      rewrite le_tpi. cbn. unfold Rec.ValPi.
      move=> /andP. move=> [LEa LEg] 
                           [[A1 [B1 [R1 h1]]] [[A2 [B2 [R2 h2]]] h3]]. 

      have [EQ1 EQ2]: A1 = A2 /\ B1 = B2. eapply HeadRed_tpi_det; eauto.
      subst A2. subst B2.
      move: h3 => [A3 [B3 [R3 h3]]].
      have [EQ1 EQ2]: A1 = A3 /\ B1 = B3. eapply HeadRed_tpi_det; eauto.
      subst A3. subst B3.

      move: (andb_prop _ _ i0) => [Va Vg]. 
      fold valid in Va.
      fold valid in Vg. fold (valid_fun g) in Vg.
      move: (andb_prop _ _ i2) => [Va0 Vg0]. 
      fold valid in Va0. 
      fold valid in Vg0. fold (valid_fun g0) in Vg0.
      repeat split. 
      ++ exists A1, B1. split; auto.
         move=> u v INf P t0 APP0 TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg Vu) as [t [APP Vt]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         cbn.
         eapply upVal. eapply LEt. eapply h1. eapply TA.
         cbn.
         eapply downVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP.

      ++ exists A1, B1. split; auto.
         move=> u v INf P t0 APP0 TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg Vu) as [t [APP Vt]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         cbn.
         eapply upVal. eapply LEt. eapply h2.  eapply TA.
         cbn.
         eapply downVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP.

      ++ exists A1, B1. split; auto.
         move=> u v INf P t0 APP0 TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg Vu) as [t [APP Vt]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         eapply upEqVal. eapply LEt. eapply h3.  eapply TA.
         eapply downVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP.

  - (* downVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto; done.
    + (* tnat *)
      all: move=> _ [M1 [RM1 VM1]].
       exists M1. split. auto.
      eapply downVal with (a1 := tnat); eauto. 
    + (* tuniv *)
      move=> LE VT.
      cbn in LE. 
      apply Nat.eqb_eq in LE. subst j0.
      have EQ: (wt_tpi w w0 h0 i = wt_tpi w1 w2 h1 i0) by ext.
      rewrite EQ.
      eapply VT.
    + (* tpi *)
      rewrite le_tpi. cbn. unfold Rec.ValPi, Rec.PiAppVal.
      move=> /andP. move=> [LEa LEg] [A [B [R1 h1]]]. 

      move: (andb_prop _ _ i0) => [Va Vg]. 
      fold valid in Va.
      fold valid in Vg. fold (valid_fun g) in Vg.
      move: (andb_prop _ _ i2) => [Va0 Vg0]. 
      fold valid in Va0. 
      fold valid in Vg0. fold (valid_fun g0) in Vg0.

      exists A, B. split; auto.
      move=> u v INf P t APP TA VP.
      specialize (h1 u v INf P).
      have Vu : valid u. eauto with valid.
      destruct (valid_app_exists Vg0 Vu) as [t0 [APP0 Vt0]].
      move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
      eapply downVal. eapply LEt. eapply h1. eapply TA.
      eapply upVal. eapply LEa. eapply VP.
      Unshelve. eapply APP0.
  - (* downEqVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + destruct a; destruct a0; cbn; auto; done.
    + move=> _ [M1 [RM1 [N1 [RN1 VM1]]]].
      exists M1. split. auto.
      exists N1. split. auto.
      eapply downEqVal with (a1 := tnat); eauto.
    + (* tuniv *)
      move=> LE VT.
      cbn in LE. 
      apply Nat.eqb_eq in LE. subst j0.
      have EQ: (wt_tpi w w0 h0 i = wt_tpi w1 w2 h1 i0) by ext.
      (* proof irrelevance for wt? this case doesn't use recursion *)
      rewrite EQ.
      eapply VT.
    + (* tpi *)
      rewrite le_tpi. cbn. unfold Rec.ValPi.
      move=> /andP. move=> [LEa LEg] 
                           [[A1 [B1 [R1 h1]]] [[A2 [B2 [R2 h2]]] h3]]. 

      have [EQ1 EQ2]: A1 = A2 /\ B1 = B2. eapply HeadRed_tpi_det; eauto.
      subst A2. subst B2.
      move: h3 => [A3 [B3 [R3 h3]]].
      have [EQ1 EQ2]: A1 = A3 /\ B1 = B3. eapply HeadRed_tpi_det; eauto.
      subst A3. subst B3.

      move: (andb_prop _ _ i0) => [Va Vg]. 
      fold valid in Va.
      fold valid in Vg. fold (valid_fun g) in Vg.
      move: (andb_prop _ _ i2) => [Va0 Vg0]. 
      fold valid in Va0. 
      fold valid in Vg0. fold (valid_fun g0) in Vg0.
      repeat split. 
      ++ exists A1, B1. split; auto.
         move=> u v INf P t APP TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg0 Vu) as [t0 [APP0 Vt0]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         eapply downVal. eapply LEt. eapply h1. eapply TA.
         eapply upVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP0.

      ++ exists A1, B1. split; auto.
         move=> u v INf P t APP TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg0 Vu) as [t0 [APP0 Vt0]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         eapply downVal. eapply LEt. eapply h2.  eapply TA.
         eapply upVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP0.
      ++ exists A1, B1. split; auto.
         move=> u v INf P t APP TA VP.
         have Vu : valid u. eauto with valid.
         destruct (valid_app_exists Vg0 Vu) as [t0 [APP0 Vt0]].
         move: (le_fun_mono Vg Vg0 LEg Vu APP APP0) => LEt.
         eapply downEqVal. eapply LEt. eapply h3.  eapply TA.
         eapply upVal. eapply LEa. eapply VP.
         Unshelve. eapply INf. eapply APP0.
Admitted.
      


(* ---- restrictVal / restrictEqVal: shrink the term-side u ---- *)

(* restrictVal: same a, smaller u' ≤ u *)
Fixpoint restrictVal {n} (Γ : Ctx n) (M T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> Val Γ M T h1 -> Val Γ M T h0
with restrictEqVal {n} (Γ : Ctx n) (M N T : Tm n) u u' a
  (h0 : wt u' a) (h1 : wt u a) {struct h1} :
  le u' u -> EqVal Γ M N T h1 -> EqVal Γ M N T h0.
Proof.
  - dependent destruction h1.
    1 : { move=> h. apply le_bot_inv in h. subst.
          have EQ: h0 = wt_bot i. ext. subst. auto. }
    all: dependent destruction h0.
    all: try solve [cbn; eauto; try done].
    + rewrite le_succ. cbn.
      move=> LE [M1 [R1 V1]].
      exists M1. split; auto.
      eapply restrictVal; eauto.
    + rewrite le_tpi. cbn.
      move=> /andP. move=> [LEa LEf] [A [B [R1 [TA [TB [Vpi hT]]]]]].
      move: hT => [Va [PEV PEEV]].
      move: Vpi => /andP. fold (valid_fun g0).
      move=> [Va0 Vg0].
      exists A. exists B. repeat split; eauto.
      ++ move=> u v INg N TN VN. cbn in *.
         unfold Rec.PiEdgeVal in PEV.
 Admitted.


(* ---- down on ValTy / EqValTy ---- *)

(* downValTy2 *)
Lemma downValTy {n} (Γ : Ctx n) (M : Tm n) u0 u1 i
  (h0 : wt u0 (tuniv i)) (h1 : wt u1 (tuniv i)) :
  le u0 u1 -> ValTy Γ M h1 -> ValTy Γ M h0.
Proof.
    move=> LE VT1.
    eapply Val_ValTy.
    apply ValTy_Val in VT1.
    eapply restrictVal; eauto.
Qed.

(* downEqValTy2 *)
Lemma downEqValTy {n} (Γ : Ctx n) (M N : Tm n) u0 u1 i
  (h0 : wt u0 (tuniv i)) (h1 : wt u1 (tuniv i)) :
  le u0 u1 -> EqValTy Γ M N h1 -> EqValTy Γ M N h0.
Proof.
    move=> LE VT1.
    eapply EqVal_EqValTy.
    apply EqValTy_EqVal in VT1.
    eapply restrictEqVal; eauto.
Qed.


(* ---- Sup / lub ---- *)

(* ValTy2-Sup: if a1 and a2 are universe-members and lub a1 a2 = Some a,
   ValTy at a1 and a2 lifts to ValTy at the lub. *)
Fixpoint ValTy_Sup {n} (Γ : Ctx n) (T : Tm n) a1 a2 a i
  (h1 : wt a1 (tuniv i)) (h2 : wt a2 (tuniv i)) (h : wt a (tuniv i)) {struct h}:
  lub a1 a2 = Some a ->
  ValTy Γ T h1 -> ValTy Γ T h2 -> ValTy Γ T h.
Proof.
  move=> LUB V1 V2.
  unfold Rec.ValTy in *.
  destruct a; try done.
  destruct a1; destruct a2; inversion LUB; subst.
  - have EQ: (h2 = h). ext. subst. done.
  - destruct (n0 =? n1); try done.
  - destruct (lub a1 a2) eqn:LUBa; inversion H0.
  - have EQ: (h1 = h). ext. subst. done.
  - destruct (compatible_fun l0 l1) eqn:CPT.
    destruct (lub a1 a2) eqn:LUBa.
    all: inversion H0.
    subst.
    inversion h. subst.
    move: V1 => [A1 [B1 [R1 [TA1 [TB1 [VT1 hV1]]]]]].
    move: V2 => [A2 [B2 [R2 [TA2 [TB2 [VT2 hV2]]]]]].
    have [EQ1 EQ2]: (A1 = A2) /\ B1 = B2.
    eapply HeadRed_tpi_det; eauto. subst.
    exists A2. exists B2.
    repeat split; eauto.
    move: hV1 => [VA1 [PE1 PEE1]].
    move: hV2 => [VA2 [PE2 PEE2]].
Admitted.

(* EqValTy2-Sup *)
Lemma EqValTy_Sup {n} (Γ : Ctx n) (M N : Tm n) a1 a2 a i
  (h1 : wt a1 (tuniv i)) (h2 : wt a2 (tuniv i)) (h : wt a (tuniv i)) :
  lub a1 a2 = Some a ->
  EqValTy Γ M N h1 -> EqValTy Γ M N h2 -> EqValTy Γ M N h.
Proof. Admitted.


(* ----------------------------------------------------- *)

Fixpoint Val_EqVal_fwd {n} (Γ : Ctx n) (M A : Tm n) u a
  (h : wt u a) (B : Tm n) i (h' : wt a (tuniv i))
  {struct h} :
  Val Γ M A h -> EqValTy Γ A B h' -> Val Γ M B h
with EqVal_EqVal_fwd {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h : wt u a) (B : Tm n) i (h' : wt a (tuniv i))
  {struct h} :
  EqVal Γ M N A h -> EqValTy Γ A B h' -> EqVal Γ M N B h
with EqVal_sym {n} (Γ : Ctx n) (M1 M2 A : Tm n) u a (h : wt u a) { struct h } :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M1 A h
with EqVal_trans {n} (Γ : Ctx n) (M1 M2 M3 A : Tm n) u a (h : wt u a) {struct h} :
  EqVal Γ M1 M2 A h -> EqVal Γ M2 M3 A h -> EqVal Γ M1 M3 A h.
Proof.
  - (* Val_EqVal_fwd *)
    dependent destruction h.
    all: dependent destruction h'.
    all: cbn.
    all: eauto.
    + move=> [A' [B' [RA' PAV]]].
      move=> [hA [hB hAB]].
      destruct hA as (A0 & B0 & RA0 & hA).
      destruct hB as (A1 & B1 & RB1 & hB).
      have [EQ1 EQ2]: A' = A0 /\ B' = B0.
      eapply HeadRed_tpi_det; eauto. subst A'. subst B'. clear RA'.
      exists A1, B1. split. exact RB1.
      unfold Rec.PiAppVal. cbn.
      move=> u v IN P t APP tP VPA1.
      unfold Rec.PiAppVal in PAV.
      specialize (PAV u v IN P t APP).
      admit.
  - (* EqVal_EqVal_fwd *)
    admit.
  - (* EqVal_sym *)
    dependent destruction h.
    all: cbn.
    all: eauto.
    (* 4 nontrivial *)
    + destruct a; try done.
    + move=> [M3 [RM3 [N3 [RN2 EV3]]]].
      have EQ: (M3 = N3). admit. (* HeadRed_succ_det *)
      subst.
      exists N3. split; auto.
      exists N3. split; auto.
    + move=> [vpiM [vPiN [_ [_ h3]]]].
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
      have TA0: typing Γ P A0.
      { eauto using t_conv, c_sym. }
      specialize (PEE u v IN P TA0).
      eapply EqVal_EqValTy.
      eapply EqVal_sym; eauto.
      eapply EqValTy_EqVal; eauto.
      eapply PEE; eauto.
      eapply Val_EqVal_fwd. eapply VP.
      eapply EqVal_EqValTy.
      eapply EqVal_sym; eauto.
    + move=> [VP1 [VP2 EP1]].
      repeat split; auto.
      unfold Rec.EqValPi in *.
      move: EP1 => [A1 [A2 [R1 PAV]]].
      exists A1. exists A2.
      repeat split; auto.
      unfold Rec.PiAppEqVal in *.
      move=> u v IN P t APP TPA VP.
      specialize (PAV u v IN P t APP TPA VP).
      cbn in PAV. cbn.
      eapply EqVal_sym; eauto.
  - (* EqVal_trans *)
Admitted.



(* EqValTy2-sym *)
Lemma EqValTy_sym {n} (Γ : Ctx n) (M N : Tm n) u i (h : wt u (tuniv i)) :
  EqValTy Γ M N h -> EqValTy Γ N M h.
Proof.
  move=>h1. eapply EqVal_EqValTy. eapply EqVal_sym.
  eapply EqValTy_EqVal. done.
Qed.

(* EqValTy2-trans *)
Lemma EqValTy_trans {n} (Γ : Ctx n) (A B C : Tm n) u i (h : wt u (tuniv i)) :
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
     FinMem b UCode          ≈  wt b (tuniv i)         (some i)
     Coherent u              ≈  valid u                (implicit in wt)
     CoherentFun g           ≈  valid_fun g            (implicit in wt (abs g) ..)
     CoherentFunTail f       ≈  valid_fun f            (implicit in wt (tpi _ f) ..)
     FinMemFun g b f         ≈  wt (abs g) (tpi b f)
     FinMemAllU f b          ≈  wt (tpi b f) (tuniv i) (codomains in U_i)
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
Lemma EqValTy_headred_expand {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u i
  (h : wt u (tuniv i)) :
  HeadRed M1' M1 -> HeadRed M2' M2 ->
  EqValTy Γ M1 M2 h -> EqValTy Γ M1' M2' h.
Proof. Admitted.

(* EqValTy2-headred-contract *)
Lemma EqValTy_headred_contract {n} (Γ : Ctx n) (M1 M2 M1' M2' : Tm n) u i
  (h : wt u (tuniv i)) :
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




(* ============================================================
   Level 6 (BIG SCC) — symmetry, transitivity, fwd-along-EqValTy,
   sup, up/down, restrict, and all Pi helper lemmas.
   ============================================================ *)

(* ---- Symmetry / transitivity ---- *)







(* ---- Pi helper lemmas: down/up/transport/restrict on PiApp / PiEdge ---- *)

(* downPiAppVal2: PiAppVal at (b1, f1) transports down to (b0, f0)
   when b0 ≤ b1 and f0 ≤ f1, given that A0 is a type at b1. *)
Lemma downPiAppVal {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1 : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A0 hb1 ->
  PiAppVal Γ M A0 B0 h1 -> PiAppVal Γ M A0 B0 h0.
Proof. Admitted.

(* downPiAppEq2 *)
Lemma downPiAppEq {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1 : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A0 hb1 ->
  (* Agda PiAppEq2 (no Rocq notation yet); paraphrase: *)
  (forall u v (IN : In (u,v) g) (N1 N2 : Tm n) t (APP : app f1 u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h1 IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h1 IN APP)) ->
  (forall u v (IN : In (u,v) g) (N1 N2 : Tm n) t (APP : app f0 u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h0 IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h0 IN APP)).
Proof. Admitted.

(* downPiAppEqVal2 *)
Lemma downPiAppEqVal {n} (Γ : Ctx n) (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1 : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A0 hb1 ->
  PiAppEqVal Γ M N A0 B0 h1 -> PiAppEqVal Γ M N A0 B0 h0.
Proof. Admitted.

(* upPiAppVal2 *)
Lemma upPiAppVal {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  PiAppVal Γ M A0 B0 h0 -> PiAppVal Γ M A0 B0 h1.
Proof. Admitted.

(* upPiAppEq2 *)
Lemma upPiAppEq {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  (forall u v (IN : In (u,v) g) (N1 N2 : Tm n) t (APP : app f0 u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h0 IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h0 IN APP)) ->
  (forall u v (IN : In (u,v) g) (N1 N2 : Tm n) t (APP : app f1 u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h1 IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h1 IN APP)).
Proof. Admitted.

(* upPiAppEqVal2 *)
Lemma upPiAppEqVal {n} (Γ : Ctx n) (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b0 f0 b1 f1 g i
  (h0 : wt (abs g) (tpi b0 f0))
  (h1 : wt (abs g) (tpi b1 f1))
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  PiAppEqVal Γ M N A0 B0 h0 -> PiAppEqVal Γ M N A0 B0 h1.
Proof. Admitted.

(* transportPiEdgeVal2-sel: PiEdgeVal at (b1, f1) transports to (b0, f0)
   when b0 ≤ b1, f0 ≤ f1 and A is a type at b1. *)
Lemma transportPiEdgeVal_sel {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) b0 f0 b1 f1 i
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1  : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A hb1 ->
  PiEdgeVal Γ A B hPi1 -> PiEdgeVal Γ A B hPi0.
Proof. Admitted.

(* transportPiEdgeEq2-sel *)
Lemma transportPiEdgeEq_sel {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n)) b0 f0 b1 f1 i
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1  : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A hb1 ->
  PiEdgeEqVal Γ A B hPi1 -> PiEdgeEqVal Γ A B hPi0.
Proof. Admitted.

(* transportPiEdgeEqTy2-sel: PiEdgeEqTy at (b1, f1) transports to (b0, f0).
   PiEdgeEqTy is the inlined "for all P : A. EqValTy B[P..] B'[P..]" piece
   that appears inside Rec.EqValTy on the tpi case. *)
Lemma transportPiEdgeEqTy_sel {n} (Γ : Ctx n) (A : Tm n) (B B' : Tm (S n)) b0 f0 b1 f1 i
  (hPi0 : wt (tpi b0 f0) (tuniv i))
  (hPi1 : wt (tpi b1 f1) (tuniv i))
  (hb1  : wt b1 (tuniv i)) :
  le b0 b1 -> le_fun f0 f1 ->
  ValTy Γ A hb1 ->
  (forall u v (IN : In (u,v) f1) (P : Tm n),
      typing Γ P A ->
      Val Γ P A (wt_tpi_cod_key hPi1 IN) ->
      EqValTy Γ B[P..] B'[P..] (wt_tpi_cod_elt hPi1 IN)) ->
  (forall u v (IN : In (u,v) f0) (P : Tm n),
      typing Γ P A ->
      Val Γ P A (wt_tpi_cod_key hPi0 IN) ->
      EqValTy Γ B[P..] B'[P..] (wt_tpi_cod_elt hPi0 IN)).
Proof. Admitted.

(* restrictPiAppVal2-sel: restrict the function-domain g to a smaller g'. *)
Lemma restrictPiAppVal_sel {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g g' i
  (h  : wt (abs g)  (tpi b f))
  (h' : wt (abs g') (tpi b f))
  (hPi : wt (tpi b f) (tuniv i)) :
  le_fun g' g ->
  PiEdgeVal Γ A0 B0 hPi ->
  PiAppVal Γ M A0 B0 h -> PiAppVal Γ M A0 B0 h'.
Proof. Admitted.

(* restrictPiAppEq2-sel *)
Lemma restrictPiAppEq_sel {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g g' i
  (h  : wt (abs g)  (tpi b f))
  (h' : wt (abs g') (tpi b f))
  (hPi : wt (tpi b f) (tuniv i)) :
  le_fun g' g ->
  PiEdgeVal Γ A0 B0 hPi ->
  (forall u v (IN : In (u,v) g) (N1 N2 : Tm n) t (APP : app f u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h IN APP)) ->
  (forall u v (IN : In (u,v) g') (N1 N2 : Tm n) t (APP : app f u = Some t),
      typing Γ N1 A0 -> typing Γ N2 A0 ->
      conv Γ N1 N2 A0 ->
      EqVal Γ N1 N2 A0 (wt_abs_key h' IN APP) ->
      EqVal Γ (Core.app M N1) (Core.app M N2) B0[N1..]
            (wt_abs_elt h' IN APP)).
Proof. Admitted.

(* restrictPiAppEqVal2-sel *)
Lemma restrictPiAppEqVal_sel {n} (Γ : Ctx n) (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) b f g g' i
  (h  : wt (abs g)  (tpi b f))
  (h' : wt (abs g') (tpi b f))
  (hPi : wt (tpi b f) (tuniv i)) :
  le_fun g' g ->
  PiEdgeVal Γ A0 B0 hPi ->
  PiAppEqVal Γ M N A0 B0 h -> PiAppEqVal Γ M N A0 B0 h'.
Proof. Admitted.

(* restrictVal2-PiCode *)
Lemma restrictVal_PiCode {n} (Γ : Ctx n) (M T : Tm n) b f g g' i
  (h  : wt (abs g)  (tpi b f))
  (h' : wt (abs g') (tpi b f))
  (hPi : wt (tpi b f) (tuniv i)) :
  le_fun g' g ->
  ValTy Γ T hPi ->
  ValPi Γ M T h -> ValPi Γ M T h'.
Proof. Admitted.

(* restrictEqVal2-PiCode *)
Lemma restrictEqVal_PiCode {n} (Γ : Ctx n) (M N T : Tm n) b f g g' i
  (h  : wt (abs g)  (tpi b f))
  (h' : wt (abs g') (tpi b f))
  (hPi : wt (tpi b f) (tuniv i)) :
  le_fun g' g ->
  ValTy Γ T hPi ->
  EqValPi Γ M N T h -> EqValPi Γ M N T h'.
Proof. Admitted.

