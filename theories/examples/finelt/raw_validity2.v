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
               (* 
               /\ typing Γ A (Core.tuniv i)
               /\ typing (Γ ++ A) B (Core.tuniv i)
               *)

               (* the semantic pi-type is valid *)
               /\ valid (tpi b g)

               (* domain is in the relation *)
               /\ Val Rec Γ A (Core.tuniv i) (wt_tpi_dom h)

               /\ PiEdgeVal Rec Γ A B (wt_tpi_inv h) 
               /\ PiEdgeEq Rec Γ A B (wt_tpi_inv h)

  | tnat => fun h => True
  | tuniv k => fun h => True
  | _ => fun h => True
  end.

Definition EqValTy {n} (Γ : Ctx n) M N (a : elt) i (h : wt a (tuniv i))  : Prop :=
  (match a return wt _ (tuniv i) -> Prop with
  | tpi b f =>
      fun (h : wt (tpi b f) (tuniv i))  =>
        ValTy Γ M h /\ ValTy Γ N h /\
        (* EqValTyPi Val EqVal EqValTy M N h *)
             (* both reduce to pi types *)
             exists A B, HeadRed M (Core.tpi A B)
             /\ exists A' B', HeadRed N (Core.tpi A' B')
             (* ... that are convertible *)
             (* /\ conv Γ A A' (Core.tuniv i)
                /\ conv (Γ ++ A) B B' (Core.tuniv i) *)
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
             /\ Rec.ValPi Rec Γ M A h
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
Notation EqValPi := 
  (@Rec.EqValPi 
    (Rec.MkF (@Val) (@EqVal) (@PiEdgeVal) (@PiEdgeEq) (@PiEdgeEqTy)(@PiAppVal) (@PiAppEq) (@PiAppEqVal))).

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

(* Incomplete stub commented out — references undefined u, b, f, h1 and has no Proof block.

wt_tpi
     : forall (a : elt) (g : list (elt * elt)) (j : nat),
       wt_pi_fun g a j -> wt a (tuniv j) -> valid (tpi a g) -> wt (tpi a g) (tuniv j)

*)

(*
Lemma EqVal_tpi n (Γ:Ctx n) M N A f g a i u b (w : wt_pi_fun g a i) (h : wt a (tuniv i)) (V : valid (tpi a g)) :
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
    destruct h1 as (A & B & HR & (* TA & TB & *) VPi & ValA & PEV & PEE).
    exists A, B. split; auto.
    exists A, B. split; auto.
(*    repeat split; auto.
    eapply c_refl; eauto.
    eapply c_refl; eauto. *)
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
   Proof irrelevance for the mutual definitions
   ------------------------------------------------------------
   The tuniv case of upVal / downVal / upEqVal / downEqVal needs
   to bridge two wt_tpi witnesses with the same indices but
   different wt_pi_fun / wt-of-dom subderivations. ValTy at
   wt_tpi h calls back into Val (on the dom-wt) and into
   PiEdgeVal / PiEdgeEq (on the wt_pi_fun part), so we need
   proof irrelevance not just for Val/EqVal but for every member
   of the Val/EqVal/PiEdge*/PiApp* mutual block.

   These are stated as axioms (Admitted) — they are uniform
   "the relation does not depend on the derivation" facts about
   each predicate in the mutual block.
   ============================================================ *)

Lemma ValTy_cumul {n} (Γ : Ctx n) (A : Tm n) u i (h : wt u (tuniv i)) :
  forall j (h2 : wt u (tuniv j)), i <= j ->
  ValTy Γ A h -> ValTy Γ A h2.
Admitted.

(* Bidirectional cross-universe ValTy proof irrelevance.
   Required to bridge cases (wt_abs in Val/EqVal, wt_pi_cons in PiEdge)
   where two same-shaped wt witnesses sit at unrelated universe levels;
   the one-directional [ValTy_cumul] cannot go down. Strictly stronger
   than [ValTy_cumul]. *)
(*
Lemma ValTy_pirrel_cross {n} (Γ : Ctx n) (A : Tm n) u i j
  (h1 : wt u (tuniv i)) (h2 : wt u (tuniv j)) :
  ValTy Γ A h1 -> ValTy Γ A h2.
Admitted.

(* Cross-universe EqValTy proof irrelevance. Same motivation as
   [ValTy_pirrel_cross]: needed in PiEdgeEqTy / PiEdgeEq forall cases
   where the codomain witness sits at differing universe levels. *)
Lemma EqValTy_pirrel_cross {n} (Γ : Ctx n) (M N : Tm n) u i j
  (h1 : wt u (tuniv i)) (h2 : wt u (tuniv j)) :
  EqValTy Γ M N h1 -> EqValTy Γ M N h2.
Admitted.
*)

(* The pirrel statements are proven by mutual structural induction over
   the wt / wt_pi_fun / wt_abs_fun derivations. Cases where the inner
   wt_abs constructor yields two different existential universes (i in
   wt_abs's `wt (tpi a g) (tuniv i)` argument) cannot be bridged at
   this granularity and are admitted. *)
Fixpoint Val_pirrel {n} (Γ : Ctx n) (M A : Tm n) u a
  (h1 h2 : wt u a) {struct h1} :
  Val Γ M A h1 -> Val Γ M A h2
with EqVal_pirrel {n} (Γ : Ctx n) (M N A : Tm n) u a
  (h1 h2 : wt u a) {struct h1} :
  EqVal Γ M N A h1 -> EqVal Γ M N A h2
with PiEdgeVal_pirrel {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) b f i j
  (h1 : wt_pi_fun f b i) (h2: wt_pi_fun f b j) {struct h1} :
  PiEdgeVal Γ A B h1 -> PiEdgeVal Γ A B h2
with PiEdgeEq_pirrel {n} (Γ : Ctx n)
  (A : Tm n) (B : Tm (S n)) b f i j
  (h1 : wt_pi_fun f b i) (h2 : wt_pi_fun f b j){struct h1} :
  PiEdgeEq Γ A B h1 -> PiEdgeEq Γ A B h2
with PiEdgeEqTy_pirrel {n} (Γ : Ctx n)
  (A : Tm n) (B B' : Tm (S n)) b f i j
  (h1 : wt_pi_fun f b i) (h2 : wt_pi_fun f b j) {struct h1} :
  PiEdgeEqTy Γ A B B' h1 -> PiEdgeEqTy Γ A B B' h2
with PiAppVal_pirrel {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) f b g
  (h1 h2 : wt_abs_fun f b g) {struct h1} :
  PiAppVal Γ M A0 B0 h1 -> PiAppVal Γ M A0 B0 h2
with PiAppEq_pirrel {n} (Γ : Ctx n)
  (M : Tm n) (A0 : Tm n) (B0 : Tm (S n)) f b g
  (h1 h2 : wt_abs_fun f b g) {struct h1} :
  PiAppEq Γ M A0 B0 h1 -> PiAppEq Γ M A0 B0 h2
with PiAppEqVal_pirrel {n} (Γ : Ctx n)
  (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n)) f b g
  (h1 h2 : wt_abs_fun f b g) {struct h1} :
  PiAppEqVal Γ M N A0 B0 h1 -> PiAppEqVal Γ M N A0 B0 h2

with ValTy_pirrel_cross {n} (Γ : Ctx n) (A : Tm n) u i j
  (h1 : wt u (tuniv i)) (h2 : wt u (tuniv j)) :
  ValTy Γ A h1 -> ValTy Γ A h2
with EqValTy_pirrel_cross {n} (Γ : Ctx n) (M N : Tm n) u i j
  (h1 : wt u (tuniv i)) (h2 : wt u (tuniv j)) :
  EqValTy Γ M N h1 -> EqValTy Γ M N h2.
Proof.
  - (* Val_pirrel *)
    intros VAL.
    have 
      ValTy_pirrel : forall n (Γ : Ctx n) (A : Tm n) u i 
        (h1 : wt u (tuniv i)) j (h2 : wt u (tuniv j)),
        ValTy Γ A h1 -> ValTy Γ A h2.
    { 
      clear n Γ M A u a h1 h2 VAL.
      move=> n Γ A u i h1 j h2 VT.
      dependent destruction h1; dependent destruction h2.
      all: try solve [cbn; done].
      cbn in VT |- *.
      destruct VT as (A0 & B0 & R1 (* & T1 & T2 *) & VV & Vh1 & PEV & PEE).
      exists A0. exists B0. 
      split. exact R1.
(*      split. exact T1.
      split. exact T2. *)       
      admit.
(*      split. exact VV.
      split. eapply Val_pirrel; eauto.
      split. eapply PiEdgeVal_pirrel; eauto.
      eapply PiEdgeEq_pirrel; eauto. *)
    }
    dependent destruction h1; dependent destruction h2.
    + (* wt_bot *) destruct a; cbn in *; trivial.
    + (* wt_tuniv *) cbn in *; trivial.
    + (* wt_tnat *) cbn in *; trivial.
    + (* wt_zero *) cbn in *; exact VAL.
    + (* wt_succ *)
      cbn in *.
      destruct VAL as [M1 [HR VM1]].
      exists M1. split; [exact HR | eapply Val_pirrel; exact VM1].
    + (* wt_tpi *)
      cbn in *.
      destruct VAL as (A0 & B0 & HR (* & TA & TB *) & V & VD & PEV & PEE).
      exists A0, B0. split; [exact HR|].
      (* split; [exact TA|]. split; [exact TB|].  *)
         split; [exact V|].
      split; [eapply Val_pirrel; exact VD|].
      split; [eapply PiEdgeVal_pirrel; exact PEV
             |eapply PiEdgeEq_pirrel; exact PEE].
    + (* wt_abs: destruct inner wt_tpi to expose universes, bridge with cross-PI *)
      match goal with H : wt (tpi _ _) (tuniv _) |- _ => dependent destruction H end.
      match goal with H : wt (tpi _ _) (tuniv _) |- _ => dependent destruction H end.
      cbn in VAL |- *.
      destruct VAL as [VT VP].
      split.
      * eapply ValTy_pirrel_cross. exact VT.
      * destruct VP as (A0 & B0 & HR & PA).
        exists A0, B0. split; [exact HR|].
        eapply PiAppVal_pirrel. exact PA.
  - (* EqVal_pirrel *)
    intros EV.
    dependent destruction h1; dependent destruction h2.
    + (* wt_bot *) destruct a; cbn in *; trivial.
    + (* wt_tuniv *) cbn in *; exact EV.
    + (* wt_tnat *) cbn in *; trivial.
    + (* wt_zero *) cbn in *; exact EV.
    + (* wt_succ *)
      cbn in *.
      destruct EV as [M1 [HR1 [N1 [HR2 EV']]]].
      exists M1. split; [exact HR1|].
      exists N1. split; [exact HR2|].
      eapply EqVal_pirrel; exact EV'.
    + (* wt_tpi: same i, bridge ValTy x2 + EqValTy components *)
      cbn in EV |- *.
      fold (valid_fun g) in EV.
      destruct EV as [VTm [VTn EVT]].
      admit.
     

(*    split.  move: (ValTy_pirrel_cross Γ M w j 
      split; [eapply ValTy_pirrel_cross; exact VTm|].
      split; [eapply ValTy_pirrel_cross; exact VTn|].
      destruct EVT as (VTm' & VTn' & A0 & B0 & HRm & A0' & B0' & HRn
                       & TC1 & TC2 & VPI & EVD & PEET).
      split; [eapply ValTy_pirrel_cross; exact VTm'|].
      split; [eapply ValTy_pirrel_cross; exact VTn'|].
      exists A0, B0. split; [exact HRm|].
      exists A0', B0'. split; [exact HRn|].
      split; [exact TC1|]. split; [exact TC2|]. split; [exact VPI|].
      split.
      * eapply EqVal_pirrel; exact EVD.
      * eapply PiEdgeEqTy_pirrel; exact PEET. *)
    + (* wt_abs: bridge inner wt_tpi via cross-PI; recurse on ValPi/EqValPi parts *)
      match goal with H : wt (tpi _ _) (tuniv _) |- _ => dependent destruction H end.
      match goal with H : wt (tpi _ _) (tuniv _) |- _ => dependent destruction H end.
      cbn in EV |- *.
      destruct EV as [VT [VPm [VPn EVPm]]].
      destruct VPm as (A0 & B0 & HRm & PAm).
      destruct VPn as (A0' & B0' & HRn & PAn).
      destruct EVPm as (A0'' & B0'' & HRe & EPA).
      split; [eapply ValTy_pirrel_cross; exact VT|].
      split.
      { exists A0, B0. split; [exact HRm|]. eapply PiAppVal_pirrel; exact PAm. }
      split.
      { exists A0', B0'. split; [exact HRn|]. eapply PiAppVal_pirrel; exact PAn. }
      exists A0'', B0''. split; [exact HRe|]. eapply PiAppEqVal_pirrel; exact EPA.
  - (* PiEdgeVal_pirrel *)
    intros PE.
    dependent destruction h1; dependent destruction h2.
    + (* wt_pi_nil *) cbn. trivial.
    + (* wt_pi_cons *)
      cbn in PE. destruct PE as [PE_rec PE_forall].
      cbn. split.
      * eapply PiEdgeVal_pirrel; exact PE_rec.
      * intros N TN VN.
        (* Goal at cross-universe j; bridge via ValTy_pirrel_cross *)
        apply ValTy_Val.
        eapply ValTy_pirrel_cross.
        apply Val_ValTy.
        apply (PE_forall N TN).
        eapply Val_pirrel. exact VN.
  - (* PiEdgeEq_pirrel *)
    intros PE.
    dependent destruction h1; dependent destruction h2.
    + cbn. trivial.
    + cbn in PE. destruct PE as [PE_rec PE_forall].
      cbn. split.
      * eapply PiEdgeEq_pirrel; exact PE_rec.
      * intros N1 N2 CV EV.
        apply EqValTy_EqVal.
        eapply EqValTy_pirrel_cross.
        eapply EqVal_EqValTy.
        apply (PE_forall N1 N2 CV).
        eapply EqVal_pirrel. exact EV.
  - (* PiEdgeEqTy_pirrel *)
    intros PE.
    dependent destruction h1; dependent destruction h2.
    + cbn. trivial.
    + cbn in PE. destruct PE as [PE_rec PE_forall].
      cbn. split.
      * eapply PiEdgeEqTy_pirrel; exact PE_rec.
      * intros P TP VP.
        eapply EqValTy_pirrel_cross.
        apply (PE_forall P TP).
        eapply Val_pirrel. exact VP.
  - (* PiAppVal_pirrel *)
    intros PA.
    dependent destruction h1; dependent destruction h2.
    + cbn. trivial.
    + cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * eapply PiAppVal_pirrel; exact PA_rec.
      * intros P TP VP.
        (* Equate the two app g ui = Some _ witnesses to align cod-types. *)
        match goal with
        | E1 : app ?g0 ?u0 = Some ?t1,
          E2 : app ?g0 ?u0 = Some ?t2 |- _ => 
            assert (Heq : t1 = t2) by congruence;         
            try subst t1; try subst t2
        end.
        eapply Val_pirrel.
        apply (PA_forall P TP).
        eapply Val_pirrel. exact VP.
  - (* PiAppEq_pirrel *)
    intros PA.
    dependent destruction h1; dependent destruction h2.
    + cbn. trivial.
    + cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * eapply PiAppEq_pirrel; exact PA_rec.
      * intros N1 N2 CV EV.
        match goal with
        | E1 : app ?g0 ?u0 = Some ?t1,
          E2 : app ?g0 ?u0 = Some ?t2 |- _ =>
            assert (Heq : t1 = t2) by congruence;
            try subst t1; try subst t2 (* ; clear Heq *)
        end.
        eapply EqVal_pirrel.
        apply (PA_forall N1 N2 CV).
        eapply EqVal_pirrel. exact EV.
  - (* PiAppEqVal_pirrel *)
    intros PA.
    dependent destruction h1; dependent destruction h2.
    + cbn. trivial.
    + cbn in PA. destruct PA as [PA_rec PA_forall].
      cbn. split.
      * eapply PiAppEqVal_pirrel; exact PA_rec.
      * intros P TP VP.
        match goal with
        | E1 : app ?g0 ?u0 = Some ?t1,
          E2 : app ?g0 ?u0 = Some ?t2 |- _ =>
            assert (Heq : t1 = t2) by congruence;
            try subst t1; try subst t2 (* ; clear Heq *)
        end.
        eapply EqVal_pirrel.
        apply (PA_forall P TP).
        eapply Val_pirrel. exact VP.
Admitted.
(* Qed. *)


(* ============================================================
   down/up
   ============================================================ *)

(* Annoyingly, struct on first derivation is not enough. Need
   to do struct on *both* wt derivations simultaneously to
   show the termination of this proof.

   For now, admitting the termination check.
*)

(* upVal/upEqVal mirror the Agda upVal2/upEqVal2 signatures: they take
   the ValTy of the syntactic type T at the bigger universe-element a1
   as an extra argument (a "Val Γ T (Core.tuniv i) hUa1", which by
   definitional unfolding is ValTy Γ T hUa1).                          *)
Fixpoint upVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) i 
  (hUa0 : wt a0 (tuniv i)) (hUa1 : wt a1 (tuniv i)) {struct h1}:
  le a0 a1 -> Val Γ M T h0 -> Val Γ T (Core.tuniv i) hUa1 -> Val Γ M T h1
with upEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1 : wt u a1) i 
  (hUa0 : wt a0 (tuniv i)) (hUa1 : wt a1 (tuniv i)) {struct h1}:
  le a0 a1 -> EqVal Γ M N T h0 -> Val Γ T (Core.tuniv i) hUa1 -> EqVal Γ M N T h1
with downVal {n} (Γ : Ctx n) (M T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> Val Γ M T h1 -> Val Γ M T h0
with downEqVal {n} (Γ : Ctx n) (M N T : Tm n) u a0 a1
  (h0 : wt u a0) (h1: wt u a1) {struct h1} :
  le a0 a1 -> EqVal Γ M N T h1 -> EqVal Γ M N T h0
(* -------- Pi helper lemmas (mutual with Val/EqVal) --------
   The up* helpers mirror Agda's upPiAppVal2 / upPiAppEq2 / upPiAppEqVal2
   by additionally taking PiEdgeVal at the bigger pi (hPi1) — this
   supplies the ValTy of the codomain at the bigger universe-element,
   needed to invoke upVal/upEqVal on the codomain.                    *)
with upPiAppVal {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1 i (hPi : wt_pi_fun g0 b0 i) (hPi1 : wt_pi_fun g1 b1 i)
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h0} :
  le b0 b1 -> le_fun g0 g1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  PiAppVal Γ M A0 B0 h0 -> PiAppVal Γ M A0 B0 h1
with downPiAppVal {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h1} :
  le b0 b1 -> le_fun g0 g1 ->
  PiAppVal Γ M A0 B0 h1 -> PiAppVal Γ M A0 B0 h0
with upPiAppEq {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1 i (hPi0 : wt_pi_fun g0 b0 i) (hPi1 : wt_pi_fun g1 b1 i)
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h0} :
  le b0 b1 -> le_fun g0 g1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  PiAppEq Γ M A0 B0 h0 -> PiAppEq Γ M A0 B0 h1
with downPiAppEq {n} (Γ : Ctx n) (M : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h1} :
  le b0 b1 -> le_fun g0 g1 ->
  PiAppEq Γ M A0 B0 h1 -> PiAppEq Γ M A0 B0 h0
with upPiAppEqVal {n} (Γ : Ctx n) (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1 i (hPi0 : wt_pi_fun g0 b0 i) (hPi1 : wt_pi_fun g1 b1 i)
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h0} :
  le b0 b1 -> le_fun g0 g1 ->
  PiEdgeVal Γ A0 B0 hPi1 ->
  PiAppEqVal Γ M N A0 B0 h0 -> PiAppEqVal Γ M N A0 B0 h1
with downPiAppEqVal {n} (Γ : Ctx n) (M N : Tm n) (A0 : Tm n) (B0 : Tm (S n))
  f b0 b1 g0 g1
  (h0 : wt_abs_fun f b0 g0) (h1 : wt_abs_fun f b1 g1) {struct h1} :
  le b0 b1 -> le_fun g0 g1 ->
  PiAppEqVal Γ M N A0 B0 h1 -> PiAppEqVal Γ M N A0 B0 h0
with downPiEdgeVal {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  b0 b1 f0 f1 i
  (h0 : wt_pi_fun f0 b0 i) (h1 : wt_pi_fun f1 b1 i) {struct h0} :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeVal Γ A B h1 -> PiEdgeVal Γ A B h0
with downPiEdgeEq {n} (Γ : Ctx n) (A : Tm n) (B : Tm (S n))
  b0 b1 f0 f1 i
  (h0 : wt_pi_fun f0 b0 i) (h1 : wt_pi_fun f1 b1 i) {struct h0} :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeEq Γ A B h1 -> PiEdgeEq Γ A B h0
with downPiEdgeEqTy {n} (Γ : Ctx n) (A : Tm n) (B B' : Tm (S n))
  b0 b1 f0 f1 i
  (h0 : wt_pi_fun f0 b0 i) (h1 : wt_pi_fun f1 b1 i) {struct h0} :
  le b0 b1 -> le_fun f0 f1 ->
  PiEdgeEqTy Γ A B B' h1 -> PiEdgeEqTy Γ A B B' h0.
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
      eapply Val_pirrel; eauto.

    + (* tuniv *)
      move=> LE VT _.
      cbn in LE.
      apply Nat.eqb_eq in LE. subst j0.
      (* h0 and h1 are two wt_tpi derivations of (tpi a g) at (tuniv j).
         Val at either reduces to ValTy, whose substructure (Val on the
         dom-wt, PiEdgeVal/PiEdgeEq on the wt_pi_fun) differs only in the
         derivation choice. Bridge with the Val proof-irrelevance axiom. *)
      eapply Val_pirrel; exact VT.
    + (* tpi *)
      (* Mirror Agda Validity2.agda: upVal2 PiCode case.
         Use the new ValTy arg (Val Γ T (Core.tuniv i) hUa1) to supply
         the first conjunct of Val at h1 (ValTy at the bigger dom).
         Use upPiAppVal — passing PiEdgeVal extracted from the ValTy arg —
         for the ValPi part. *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE.
      apply andb_prop in LE.
      destruct LE as [LEa LEg].
      move=> VAL VTa1.
      cbn in VAL. 
      unfold Rec.ValPi in VAL.
      destruct VAL as [VT VP].
      destruct VP as [A0 [B0 [R1 PAV]]].
      cbn. split.
      * (* ValTy at WTb_h1 (the bigger pi's dom witness).
           The new ValTy arg VTa1 is at the WHOLE bigger pi (hUa1 : wt a1 (tuniv i)),
           not at the dom — they're structurally different. Bridging requires
           extracting the dom-Val from the pi-ValTy existentials + universe-aware
           proof irrelevance. Admit this bridging step. *)
        admit.
      * unfold Rec.ValPi. exists A0, B0. split. exact R1.
        (* Apply upPiAppVal with the new PiEdgeVal arg (extracted from VTa1) *)
        admit.
  - (* upEqVal *)
    dependent destruction h1;
    dependent destruction h0.
    all: try solve [cbn; eauto].
    + (* bot *)
      destruct a; destruct a0; cbn; auto.
    + (* tnat *)
      move=> _ [M1 [RM1 [N1 [RN1 VM1]]]] _.
      exists M1. split. auto.
      exists N1. split. auto.
      eapply upEqVal with (a1 := tnat) (i := 0) (hUa1 := wt_tnat 0); admit.
    + (* tuniv *)
      (* Bridge two wt_tpi witnesses at same indices via EqVal_pirrel. *)
      move=> LE EV _.
      cbn in LE.
      apply Nat.eqb_eq in LE. subst j0.
      eapply EqVal_pirrel; exact EV.
    + (* tpi *)
      (* Mirror Agda Validity2.agda: upEqVal2 PiCode case.
         EqVal at (abs f) (tpi a g) is ValTy /\ ValPi M /\ ValPi N /\ EqValPi M N.
         Use the new ValTy arg for the first conjunct; upPiAppVal /
         upPiAppEqVal (with PiEdgeVal from the arg) for the rest. *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE.
      apply andb_prop in LE.
      destruct LE as [LEa LEg].
      move=> EVAL VTa1.
      cbn in EVAL.
      unfold Rec.ValPi, Rec.EqValPi in EVAL.
      destruct EVAL as [VT [VPM [VPN EPI]]].
      destruct VPM as [A0_M [B0_M [R_M PAV_M]]].
      destruct VPN as [A0_N [B0_N [R_N PAV_N]]].
      destruct EPI as [A0_E [B0_E [R_E PAEV]]].
      cbn. split; [|split; [|split]].
      * admit. (* ValTy bridging *)
      * unfold Rec.ValPi. exists A0_M, B0_M. split. exact R_M. admit.
      * unfold Rec.ValPi. exists A0_N, B0_N. split. exact R_N. admit.
      * unfold Rec.EqValPi. exists A0_E, B0_E. split. exact R_E. admit.

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
      (* Bridge two wt_tpi witnesses at same indices via Val_pirrel. *)
      move=> LE VT.
      cbn in LE.
      apply Nat.eqb_eq in LE. subst j0.
      eapply Val_pirrel; exact VT.
    + (* tpi *)
      (* Mirror Agda Validity2.agda: downVal2 PiCode case.
         Convert Val at h1 (bigger pi a0/g0) to Val at h0 (smaller pi a/g):
           - downValTy on the domain ValTy   (admit: universe alignment)
           - downPiAppVal on the PiAppVal    (mutual)                       *)
      dependent destruction h0.
      dependent destruction h1.
      rewrite le_tpi.
      move=> LE.
      apply andb_prop in LE.
      destruct LE as [LEa LEg].
      move=> VAL.
      cbn in VAL.
      unfold Rec.ValPi in VAL.
      destruct VAL as [VT VP].
      destruct VP as [A0 [B0 [R1 PAV]]].
      cbn. split.
      * (* ValTy at smaller WTb_h0 from ValTy at WTb_h1.
           Mirrors Agda's `downValTy2 _ _ (PiCode b0 f0) (PiCode b1 f1) ...`.
           The Rocq `downValTy` requires identical universe indices on
           both wt witnesses; here `i` and `i1` are taken from h0/h1's
           wt_tpi destructions and are not syntactically equal, so this
           step also needs universe alignment (proof irrelevance for the
           universe index, beyond the same-index `Val_pirrel`). *)
        admit.
      * unfold Rec.ValPi. exists A0, B0. split. exact R1.
        eapply downPiAppVal; eauto.
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
      (* Bridge two wt_tpi witnesses at same indices via EqVal_pirrel. *)
      move=> LE EV.
      cbn in LE.
      apply Nat.eqb_eq in LE. subst j0.
      eapply EqVal_pirrel; exact EV.
    + (* tpi *)
      (* Mirror Agda Validity2.agda: downEqVal2 PiCode case.
         EqVal at (abs f) (tpi a g) is
            ValTy /\ ValPi M /\ ValPi N /\ EqValPi M N. *)
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
      * (* ValTy at smaller (proof irrelevance / universe alignment) *)
        admit.
      * unfold Rec.ValPi. exists A0_M, B0_M. split. exact R_M.
        eapply downPiAppVal; eauto.
      * unfold Rec.ValPi. exists A0_N, B0_N. split. exact R_N.
        eapply downPiAppVal; eauto.
      * unfold Rec.EqValPi. exists A0_E, B0_E. split. exact R_E.
        eapply downPiAppEqVal; eauto.
  - (* upPiAppVal: takes extra PiEdgeVal at the bigger pi (mirror of Agda's piEV1) *)
    intros LE LEg PEV PA.
    dependent destruction h0.
    + (* wt_abs_nil: PiAppVal at nil is True *)
      dependent destruction h1. cbn. trivial.
    + (* wt_abs_cons: recurse + forall-part using upVal (which needs ValTy at t1
         — obtained by applying PEV to the corresponding entry of the bigger pi). *)
      admit.
  - (* downPiAppVal: no extra arg (Agda's downVal2 doesn't need ValTy at a1) *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + admit.
  - (* upPiAppEq *)
    intros LE LEg PEV PA.
    dependent destruction h0.
    + dependent destruction h1. cbn. trivial.
    + admit.
  - (* downPiAppEq *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + admit.
  - (* upPiAppEqVal *)
    intros LE LEg PEV PA.
    dependent destruction h0.
    + dependent destruction h1. cbn. trivial.
    + admit.
  - (* downPiAppEqVal *)
    intros LE LEg PA.
    dependent destruction h1.
    + dependent destruction h0. cbn. trivial.
    + admit.
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
  - admit.
  - admit.
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
    admit.
  - (* EqVal_EqVal_fwd *)
    admit.
  - (* EqVal_sym *)
    admit.
  - (* EqVal_trans *)
    admit.
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







(* ---- Pi helper lemmas: down/up/transport/restrict on PiApp / PiEdge ----

   NOTE: The up/down PiAppVal / PiAppEq / PiAppEqVal lemmas, and the
   transport PiEdgeVal / PiEdgeEq / PiEdgeEqTy lemmas, are now part of
   the mutual Fixpoint block defining upVal / upEqVal / downVal / downEqVal
   above. The signatures there take wt_abs_fun / wt_pi_fun derivations
   directly (the underlying derivations of the wt judgment), instead of
   wt (abs g) (tpi b f) / wt (tpi b f) (tuniv i) — see the block above
   for the actual statements.

   The transport / restrict lemmas below remain as standalone (Admitted)
   stubs since they are not directly used by upVal / downVal. *)

(* The transport / restrict lemmas previously listed here referred to
   helper inversions (wt_abs_key, wt_abs_elt, wt_tpi_cod_key,
   wt_tpi_cod_elt) and a non-existent PiEdgeEqVal. Their signatures
   need to be rewritten in terms of wt_pi_fun / wt_abs_fun derivations
   directly (matching the mutual block above) before they can be
   re-stated as standalone lemmas. They are omitted here for now. *)

