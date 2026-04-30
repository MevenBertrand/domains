Require Import ssreflect.

Require Import syntax.
Require Export fintype.
Require Export fin_util.

Require Export Logic.FunctionalExtensionality.
Require Import Stdlib.Program.Equality.

Lemma ext_fin {n A}{f g: fin n -> A} : 
  (forall x, f x = g x) -> f = g.
eapply functional_extensionality.
Qed.

Import ScopedNotations.
Import SubstNotations.

Disable Notation "'__Tm'" (all).

(** Define a notation scope specific to this language. *)
Declare Scope syntax_scope.

Module SyntaxNotations.
Export ScopedNotations.
Notation "⇑" := (up_Tm_Tm) : syntax_scope.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Tm ↑) 
                    (only printing, at level 0) : syntax_scope.
End SyntaxNotations.
Import SyntaxNotations.

Create HintDb syntax.
Open Scope syntax_scope.


Inductive Ctx : nat -> Type := 
| ctx_empty    : Ctx 0
| ctx_extend n : Ctx n -> Tm n -> Ctx (S n).

Notation "Γ ++ A" := (ctx_extend _ Γ A) : syntax_scope.

Fixpoint lookup {n} (x : fin n) : Ctx n -> Tm n.
  destruct n; cbn in x. done.
  destruct x as [p|]. 
  - move=> tl.
    inversion tl. exact (lookup _ p X)⟨↑⟩.
  - move=> tl.
    inversion tl. exact (X0⟨↑⟩).
Defined.


(*
Definition Ctx n := fin n -> Tm n.

Definition Ctx_app {n} : Ctx n -> Tm n -> Ctx (S n) := 
  fun Γ A => ( A⟨↑⟩ .: (Γ >> ⟨↑⟩)).

Notation "Γ ++ A" := (Ctx_app Γ A).
*)


(* for nrec *)
Definition rho {n} : fin (S n) -> Tm (S n) := 
   (succ (var var_zero) .: var >> ⟨↑⟩).

Inductive typing : forall {n} (Γ : Ctx n), Tm n -> Tm n -> Prop := 
  | t_var n (Γ : Ctx n) x : 
    ctx Γ ->
    typing Γ (var x) (lookup x Γ)
  | t_conv n (Γ : Ctx n) M A B i : 
    typing Γ M A -> 
    conv Γ A B (tuniv i) -> 
    typing Γ M B
  | t_abs n (Γ : Ctx n) A B N i : 
    typing Γ A (tuniv i) ->
    typing (Γ ++ A) B (tuniv i) -> 
    typing (Γ ++ A) N B ->
    typing Γ (abs A N) (tpi A B)
  | t_app n (Γ : Ctx n) A B N M i : 
    typing Γ A (tuniv i) -> 
    typing (Γ ++ A) B (tuniv i) -> 
    typing Γ N (tpi A B) ->
    typing Γ M A -> 
    typing Γ (app N M) B[M..]
  (* natural numbers *)
  | t_nat n (Γ : Ctx n) : 
    typing Γ tnat (tuniv 0)
  | t_zero n (Γ : Ctx n) : 
    typing Γ zero tnat 
  | t_succ n (Γ : Ctx n) M : 
    typing Γ M tnat ->
    typing Γ (succ M) tnat 
  | t_nrec n (Γ : Ctx n) (T U : Tm (S n)) M0 M1 i :
    typing (Γ ++ tnat) T (tuniv i) ->
    typing Γ M0 (T[zero..]) ->
    U = T[rho] ->
    typing Γ M1 (tpi tnat (tpi T U⟨↑⟩ )) ->       
    typing Γ (nrec T M0 M1) (tpi tnat T)
  (* universes *)
  | t_tpi n (Γ : Ctx n) A B i : 
    typing Γ A (tuniv i) ->
    typing (Γ ++ A) B (tuniv i) -> 
    typing Γ (tpi A B) (tuniv i)
  | t_cum n (Γ : Ctx n) A i j :
    (* TODO: change this to <= ? *)
    typing Γ A (tuniv i) -> (i < j)%nat -> 
    typing Γ A (tuniv j)
  | t_univ n (Γ : Ctx n) i j : 
    (i < j)%nat ->
    typing Γ (tuniv i) (tuniv j)
with conv :forall {n} (Γ : Ctx n), Tm n -> Tm n -> Tm n -> Prop := 
  | c_conv n (Γ : Ctx n) M N A B i : 
    conv Γ M N A -> 
    conv Γ A B (tuniv i) ->
    conv Γ M N B
  | c_refl n (Γ : Ctx n) M A : 
    typing Γ M A ->
    conv Γ M M A 
  | c_trans n (Γ : Ctx n) M N P A  : 
    conv Γ M N A -> 
    conv Γ N P A -> 
    conv Γ M P A
  | c_app1 n (Γ : Ctx n) A B N N' M i : 
    typing Γ A (tuniv i) -> 
    typing (Γ ++ A) B (tuniv i) -> 
    conv Γ N N' (tpi A B) ->
    typing Γ M A ->
    conv Γ (app N M) (app N' M) B[M..]
  | c_app2 n (Γ : Ctx n) A B N M M' i  :          
    typing Γ A (tuniv i) -> 
    typing (Γ ++ A) B (tuniv i) -> 
    typing Γ N (tpi A B) ->
    conv Γ M M' A ->
    conv Γ (app N M) (app N M') B[M..]
  | c_beta n (Γ : Ctx n) A B M N i :
    typing Γ A (tuniv i) -> 
    typing (Γ ++ A) B (tuniv i) -> 
    typing (Γ ++ A) N B -> 
    typing Γ M A ->
    conv Γ (app (abs A N) M) N[M..] B[M..]
  | c_eta n (Γ : Ctx n) A B N N' i :
    typing Γ A (tuniv i) -> 
    typing (Γ ++ A) B (tuniv i) -> 
    typing Γ N (tpi A B) ->     
    typing Γ N' (tpi A B) ->     
    conv (Γ ++ A) (app N⟨↑⟩ (var var_zero))
      (app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
    conv Γ N N' (tpi A B)
  (* natural numbers: TODO add typing hyps *)
  | c_nrec_Z n (Γ : Ctx n) M0 M1 (T : Tm (S n)) i : 
    typing  (Γ ++ tnat) T (tuniv i) ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩ )) ->   
    conv Γ (app (nrec T M0 M1) zero) M0 T[zero..]
  | c_nrec_S n (Γ : Ctx n) T M0 M1 n i : 
    typing (Γ ++ tnat) T (tuniv i) ->
    typing Γ M0 (T[zero..]) ->
    typing Γ M1 (tpi tnat (tpi T T[rho]⟨↑⟩ )) ->    
    conv Γ (app (nrec T M0 M1) (succ n)) 
      (app (app M1 n) (app (nrec T M0 M1) n)) T[(succ n)..]
  | c_tuniv n (Γ : Ctx n) M N i j : 
    conv Γ M N (tuniv i) -> (i < j)%nat ->
    conv Γ M N (tuniv j)
  | c_tpi n (Γ : Ctx n) A0 A1 B0 B1 i :
    conv Γ A0 A1 (tuniv i) -> 
    conv (Γ ++ A0) B0 B1 (tuniv i) -> 
    conv Γ (tpi A0 B0) (tpi A1 B1) (tuniv i)
with ctx : forall {n}, Ctx n -> Prop :=
  | c_empty : ctx ctx_empty
  | c_cons n (Γ : Ctx n) A i : ctx Γ -> 
     typing Γ A (tuniv i) -> 
     ctx (Γ ++ A).


(*
Lemma ctx_extend {n} {Γ:Ctx n}{A:Tm n} :
  ctx Γ -> type Γ A -> ctx (Γ ++ A).
Proof. move=> [ih] hT. constructor.
       auto_case. 
*)

(** This version of t_var is easier to work with sometimes
    as it doesn't require the type to already be in the form 
    Γ x. *)
Definition t_var' {n} (Γ : Ctx n) x τ : 
  lookup x Γ = τ -> ctx Γ -> typing Γ (var x) τ.
intros <-. eapply t_var. Qed.
Definition t_app' {n} (Γ : Ctx n) (A : Tm n) 
  (B : Tm (S n)) (N M : Tm n) (C:Tm n) i :
       typing Γ A (tuniv i) ->
            typing (Γ ++ A) B (tuniv i) -> typing Γ N (tpi A B) 
       -> typing Γ M A 
       -> B[M..] = C
       -> typing Γ (app N M) C.
intros. subst. eapply t_app; eauto. Qed. 
Definition t_univ' {n} (Γ : Ctx n) A (i j : nat):
  i < j -> tuniv j = A -> 
  typing Γ (tuniv i) A.
intros h1 <-. eapply t_univ; eauto. Qed.
Definition t_cum' {n} (Γ : Ctx n) A i j B : 
    typing Γ A (tuniv i) -> (i < j)%nat -> 
    tuniv j = B ->
    typing Γ A B.
Proof. intros; subst; eauto using t_cum. Qed.

#[export] Hint Resolve t_var'  t_univ': syntax.

#[export] Hint Constructors typing conv : syntax.


Module Notations.
Notation "Γ |-e a ∈ A" := (typing Γ a A) (at level 70) : syntax_scope.
Notation "Γ |-e a ≡ b ∈ A" := (conv Γ a b A) (at level 70) : syntax_scope.
End Notations.

Open Scope syntax_scope.
Import Notations.

(** * Renaming and substitution properties *)

(* == RenTypes *)
(*
Definition typing_renaming {n} (Δ : fin n -> Tm n) 
  {m} (δ : fin m -> fin n)
  (Γ : fin m -> Tm m) : Prop := 
  forall i, Δ (δ i) = (Γ i)⟨δ⟩.
*)
Definition typing_renaming {n} (Δ : Ctx n) 
  {m} (δ : fin m -> fin n)
  (Γ : Ctx m) : Prop := 
  forall i, lookup (δ i) Δ  = (lookup i Γ)⟨δ⟩.


(** The identity renaming preserves the context *)
Lemma typing_renaming_id {n} (Δ : Ctx n) :
  typing_renaming Δ id Δ.
Proof. unfold typing_renaming. intros x. asimpl. done. Qed.

(** shift extends the context *)
Lemma typing_renaming_shift {n} (Γ : Ctx n) (τ : Tm n) :
    typing_renaming (Γ ++ τ) shift Γ.
Proof.
  unfold typing_renaming. intros x. asimpl. fsimpl. done. Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {n} (Δ : Ctx n) 
  {m} (Γ : Ctx m) (δ : fin m -> fin n) (τ : Tm m) :
  typing_renaming Δ δ Γ ->
  typing_renaming (Δ ++ τ⟨δ⟩) (up_ren δ) (Γ ++ τ).
Proof. intro h. unfold typing_renaming in *.
       auto_case; asimpl; try done.
       unfold ">>". rewrite h.
         asimpl. done.
Qed.

Create HintDb renaming.
#[export] Hint Resolve typing_renaming_lift 
  typing_renaming_id typing_renaming_shift : renaming.


Fixpoint renaming_typing {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) δ : 
  Γ |-e a ∈ A -> typing_renaming Δ δ Γ -> ctx Δ -> Δ |-e a⟨δ⟩ ∈ A⟨δ⟩
with renaming_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) δ : 
  Γ |-e a ≡ b ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ -> Δ |-e a⟨δ⟩ ≡ b⟨δ⟩ ∈ A⟨δ⟩
(*
with renaming_type {n} (Γ : Ctx n) A {m} (Δ:Ctx m) δ : 
  Γ |-τ A -> typing_renaming Δ δ Γ ->  ctx Δ -> Δ |-τ A⟨δ⟩
with renaming_type_conv {n} (Γ : Ctx n) A B {m} (Δ:Ctx m) δ : 
  Γ |-τ A ≡ B -> typing_renaming Δ δ Γ ->  ctx Δ -> Δ |-τ A⟨δ⟩ ≡ B⟨δ⟩
with ctx_extend {n} {Γ:Ctx n}{A:Tm n} :
  ctx Γ -> type Γ A -> ctx (Γ ++ A)
*).
Proof. 
  have renaming_typing': 
    forall n (Γ : Ctx n) a A {m} (Δ:Ctx m) δ B,
      Γ |-e a ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
         B = A⟨δ⟩ ->
         Δ |-e a⟨δ⟩ ∈ B.
  { admit. }
  have renaming_conv' :
    forall n (Γ : Ctx n) a b A {m} (Δ:Ctx m) δ B,
      Γ |-e a ≡ b ∈ A -> typing_renaming Δ δ Γ ->  ctx Δ ->
         B = A⟨δ⟩ ->
         Δ |-e a⟨δ⟩ ≡ b⟨δ⟩ ∈ B.
  { admit. } 
  (* typing *)
  - intros h tR wtΔ. 
    dependent destruction h; subst.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming; cbn].
    + (* var case *)
      eapply t_var'; eauto.
    + (* conv *) 
      econstructor; eauto with renaming.
      eapply renaming_conv'; eauto.
      cbn; eauto.
    + (* abs *)
      have EC: ctx (Δ ++ A ⟨δ⟩).
      { eapply c_cons; eauto with renaming.
        eapply renaming_typing in h1; eauto with renaming. } 
      eapply t_abs; eauto with renaming.
      eapply renaming_typing' in h1; eauto with renaming.
      cbn; eauto.
      eapply renaming_typing in h2; eauto with renaming.
    + (* app *) 
      have EC: ctx (Δ ++ A ⟨δ⟩).
      { eapply c_cons; eauto with renaming.
        eapply renaming_typing in h1; eauto with renaming. } 
      eapply t_app' with (B:=B⟨up_ren δ⟩); eauto with renaming. 
      eapply renaming_typing' in h1; eauto with renaming.
      cbn; eauto.
      eapply renaming_typing' in h2; eauto with renaming.
      eapply renaming_typing' in h3; eauto with renaming.
      asimpl.
      auto.
    + (* nrec *)
      have EC: ctx (Δ ++ tnat).
      { eapply c_cons; eauto with renaming.
        eapply t_nat; eauto. } 
      eapply t_nrec; eauto with renaming. 
      eapply renaming_typing' in h1; eauto with renaming.
      eapply typing_renaming_lift with (τ:=tnat) in tR; eauto.
      reflexivity.
      eapply renaming_typing' in h2; eauto. asimpl. eauto.
      eapply renaming_typing' in h3; eauto with renaming.
      asimpl. 
      f_equal. f_equal. 
      admit. (* ugh! *)
    + (* tpi *)
      eapply t_tpi; eauto with renaming.
      eapply renaming_typing'; eauto with renaming.
      eapply c_cons; eauto.
      eapply renaming_typing'; eauto with renaming.
      reflexivity.
    + (* tcum *)
      eapply t_cum'; eauto.
      eapply renaming_typing'; eauto. 
  (* conv *)
  - intros h tR tΔ.
    dependent destruction h; subst.
    all: asimpl.
    all: try solve [econstructor; eauto with renaming].
    + admit.
    + (* c_app1 *)
      admit.
    + (* c_app2 *)
      admit.
    + (* c_beta *)
      admit.
    + (* c_eta *)
      admit.
    + (* c_nrec_zero *)
      admit.
    + (* c_rec_succ *)
      admit.
    + (* c_cum *)
      admit.
    + (* c_tpi *)
      admit.
Admitted.    

(** Substution lemmas *)

Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, (Δ |-e (σ x) ∈ (lookup x Γ)[σ]).

Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null ctx_empty.
Proof. unfold typing_subst. auto_case. Qed.

Lemma typing_subst_id {n} (Δ : Ctx n) :
  ctx Δ -> typing_subst Δ var Δ.
Proof. move=>h. 
       unfold typing_subst. intro x. asimpl. econstructor; eauto. 
       Qed.

(*
Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 Δ |-e e ∈ τ -> typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (Γ ++ τ).
Proof. intros. unfold typing_subst in *. intros [y|]; asimpl; eauto. Qed.
*)
Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  ctx (Δ ++ τ[σ]) ->
  typing_subst Δ σ Γ -> typing_subst (Δ ++ τ[σ]) (⇑ σ) (Γ ++ τ).
Proof.
  unfold typing_subst in *.
  intros EC h.
  intro x. destruct x.
  + specialize (h f).
    cbn.
    eapply renaming_typing with (Δ := Δ ++ τ[σ])in h;
      eauto with renaming.
    asimpl in h. done.
  +  cbn. eapply t_var'; eauto.
     cbn. asimpl. eauto.
Qed.

(** Add the substitution lemmas as hints *)
#[export] Hint Resolve typing_subst_lift (* typing_subst_cons *)
             typing_subst_id typing_subst_null : rec.

Fixpoint
  substitution_tm {n} (Γ : Ctx n) a A {m} (Δ:Ctx m) σ : 
  Γ |-e a ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ |-e a[σ] ∈ A[σ]
with 
 substitution_conv {n} (Γ : Ctx n) a b A {m} (Δ:Ctx m) σ : 
  Γ |-e a ≡ b ∈ A -> typing_subst Δ σ Γ -> ctx Δ -> Δ |-e a[σ] ≡ b[σ] ∈ A[σ]
.
Proof.
  all: intros h tS tΔ.
  - dependent destruction h; subst.
    all: cbn; asimpl.
    all: try solve [econstructor; eauto with syntax].
    + unfold typing_subst in tS. eauto.
    + admit.
Admitted.



