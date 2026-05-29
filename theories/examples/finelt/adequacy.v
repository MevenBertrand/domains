(* Fundamental theorem of the logical relation

   see Adequacy2.adga


   There are no tricky termination arguments in this file. 
   (I hope!)
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


(* A substitution: σ *)
Definition Sub m n := fin m -> Tm n.

(* A valid substitution σ maps every term in ρ to one that 
   can be interpreted in Δ. *) 
Definition ValSub {n} (Δ : Ctx n) {g} (Γ : Ctx g) (σ : Sub g n) (ρ : Env g)    : Prop :=
  forall i,
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a),
      Val Δ (σ i) (lookup i Γ)[σ] h.

Lemma ValSub_empty {g} (Δ : Ctx g)(σ : Sub 0 g) : 
  ValSub Δ ctx_empty σ null.
unfold ValSub. done. Qed.

Lemma ValSub_cons {g} (Γ : Ctx g) (ρ : Env g) {h} (Δ : Ctx h) (σ : Sub g h) (A: Tm g) v (M : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    Val Δ M A[σ] h) ->
    ValSub Δ Γ σ ρ ->
    ValSub Δ (Γ ++ A) (M .: σ) (v .: ρ).
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

Definition EqValSub {h} {g} (Δ : Ctx h) (Γ : Ctx g) 
  (σ1 : Sub g h) (σ2 : Sub g h) (ρ : Env g) : Prop :=
  forall i,
  forall u, valid u -> le u (ρ i) ->
    forall a, EvalRel (lookup i Γ) ρ a ->
    forall (h : wt u a),
      EqVal Δ (σ1 i) (σ2 i) (lookup i Γ)[σ1] h.

  
Lemma EqValSub_empty {g} (Δ : Ctx g)(σ1 σ2 : Sub 0 g) : 
   EqValSub Δ ctx_empty  σ1 σ2 null.
unfold EqValSub. done. Qed.

Lemma EqValSub_cons {h} {g} (Δ : Ctx h) (Γ : Ctx g) (ρ : Env g)
  (σ1 σ2 : Sub g h) A v (M1 M2 : Tm h):
    (forall u, valid u -> le u v -> forall a (h : wt u a),
    EvalRel A ρ a ->
    EqVal Δ M1 M2 A[σ1] h) ->
    EqValSub Δ Γ σ1 σ2 ρ ->
    EqValSub Δ (Γ ++ A)  (M1 .: σ1) (M2 .: σ2) (v .: ρ).
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
  forall ρ m (Δ : Ctx m) (σ : Sub n m) (TS : typing_subst Δ σ Γ) (F : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    Val Δ M[σ] A[σ] WT.
Definition semantic_conv2 {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ  m (Δ : Ctx m) σ1 σ2 (TS1 : typing_subst Δ σ1 Γ)
    (TS2 : typing_subst Δ σ2 Γ)
    (F : fits Γ ρ)
    (VS : EqValSub Δ Γ σ1 σ2 ρ ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    EqVal Δ M[σ1] N[σ2] A[σ1] WT.

Lemma ValSub_EqValSub {n} (Γ : Ctx n) ρ {m} (Δ : Ctx m) σ : 
  ValSub Δ Γ σ ρ ->
    EqValSub Δ Γ σ σ ρ .
Proof.
  move=> VS.
  unfold EqValSub.
  move=> i u Vu LE a E1 h.
  specialize (VS i u Vu LE a E1 h).
  eapply Val_EqVal.
  auto.
Qed.

Definition semantic_conv {n} (Γ : Ctx n) (M N: Tm n) (A : Tm n) :=
  forall ρ m (Δ : Ctx m) σ (TS : typing_subst Δ σ Γ) (F : fits Γ ρ)
    (VS : ValSub Δ Γ σ ρ),
  forall u a (WT : wt u a),
    EvalRel M ρ u ->
    EvalRel A ρ a ->
    EqVal Δ M[σ] N[σ] A[σ] WT.


(* ============================================================
   Bridging lemmas needed by st_app.

   These mirror Adequacy2.agda's helpers:
   - Val_transport ≈ app-transport-Val2  (combines restrictVal + downVal)
   - EvalRel_Pi_app_type ≈ EvalRel-Pi-app-type
   - EvalRel_app_Comp    ≈ EvalRel-Comp
   ============================================================ *)

(* Val_transport: bridge Val along both a u-decrease AND an a-decrease.
   Internally chains:
     - wt_le on h' to get an intermediate witness wt u' a,
     - restrictVal to drop u: from h (wt u a) → intermediate (wt u' a),
     - downVal to drop a: from intermediate (wt u' a) → h' (wt u' a'). *)
Lemma Val_transport {n} (Γ : Ctx n) (M T : Tm n) u u' a a'
  (h : wt u a) (h' : wt u' a')
  (hUa : wt a tuniv) (hUa' : wt a' tuniv) :
  le u' u -> le a' a ->
  Val Γ M T h -> Val Γ M T h'.
Proof.
  move=> LEu LEa VH.
  have h'' : wt u' a by eapply wt_le; eauto.
  have VH'' : Val Γ M T h'' by eapply (@restrictVal _ Γ M T u u' a h'' h); eauto.
  eapply (@downVal _ Γ M T u' a' a h' h''); eauto.
Qed.


(* EvalRel_Pi_app_type: from EvalRel of a (Core.tpi A B) at semantic
   (tpi b f), the codomain B[N..] evaluates to the appropriate element
   of f for any compatible N.

   Statement mirrors Agda EvalRel-Pi-app-type:
     EvalRel (Core.tpi A B) ρ (tpi b f) →
     valid u → app f u = Some v → ¬ is_bot v → wt u b →
     EvalRel B[N..] ρ v
   where N evaluates appropriately to u in ρ.
   The exact phrasing depends on how we connect the syntactic substitution
   B[N..] with the semantic-function image (EvalFun f u). *)
Lemma EvalRel_Pi_app_type {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n)
  (b : elt) (f : list (elt * elt)) :
  EvalRel (Core.tpi A B) ρ (tpi b f) ->
  valid_env ρ ->
  forall u v,
    valid u -> app f u = Some v -> ~ is_bot v ->
    forall N, EvalRel N ρ u ->
    EvalRel B[N..] ρ v.
Proof. 
  move=> h Ve u v Vu APP NB N ER.
  cbn in h.
  move: h => [Vb [Vf [WTb [ERA h]]]].
Admitted.

(* EvalRel_app_Comp: two EvalRel results of the same term in the same
   environment are compatible (i.e., their lub exists).

   Mirrors Agda's EvalRel-Comp.  Specialized for applications, but the
   general statement applies to any term. *)
Lemma EvalRel_app_Comp {n} (M : Tm n) (ρ : Env n) (u v : elt) :
  valid_env ρ ->
  EvalRel M ρ u ->
  EvalRel M ρ v ->
  compatible u v.
Proof. Admitted.


(* ------------------ semantic typing rules ----------- *)

Section SemanticTyping.

Local Notation "Γ ⊨ M ∈ A" := (semantic_typing Γ M A).
Local Notation "Γ ⊨ M ≡ N ∈ A" := (semantic_conv2 Γ M N A).



Variable (n:nat) (Γ : Ctx n).

Lemma st_var (x : fin n) : 
  ctx Γ -> 
(* ------------------------- *)
  (semantic_typing Γ (var x) (lookup x Γ)).
Proof.
  move=> h. 
  move=> ρ m σ Δ TS FR VS u1 a1 WT1 Ex ER.
  cbn in *. move: Ex => [Vu1 Le1].
  specialize (VS x).
  eapply VS; eauto.
Qed.

Lemma st_conv M A B  : 
  typing Γ M A -> 
  conv Γ A B Core.tuniv ->
  semantic_typing Γ M A -> 
  semantic_conv2 Γ A B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ M B.
Proof.
  move=> T1 C2 h1 h2. 
  move=> ρ m Δ σ TS FR VS u1 a1 WT1 Ex Ea1.
  specialize (h1 ρ m Δ σ TS FR VS).
  specialize (h1 _ _ WT1 Ex).
  specialize (h2 ρ m Δ σ σ TS TS FR).
  specialize (h2 (ValSub_EqValSub VS)).
  move: (typing_EvalRel T1 FR Ex) => hT1. unfold Typed in hT1.
  destruct hT1 as [v [a [LEu1 [Ev [wta Ea]]]]].
  move: (conv_EvalRel C2 FR) => [TA [TB [EAB EBA]]]. 
  unfold InvTyped, Typed in TA , TB.
  destruct (TA _ Ea) as [a2 [ui [LEa2 [Ea2 [WTa2 Eui]]]]]. clear TA.
  destruct (TB _ Ea1) as [a3 [uj [LEa3 [Ea3 [WTa3 Euj]]]]]. clear TB.
Admitted.

Lemma st_abs A B M : 
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv -> 
  semantic_typing (Γ ++ A) B Core.tuniv -> 
  semantic_typing (Γ ++ A) M B ->
(* ------------------------- *)
  semantic_typing Γ (Core.abs A M) (Core.tpi A B).
Admitted.

Lemma st_app A B N M : 
  typing Γ A Core.tuniv -> 
  typing (Γ ++ A) B Core.tuniv -> 
  typing Γ M (Core.tpi A B) -> 
  typing Γ N A  -> 
  semantic_typing Γ A Core.tuniv -> 
  semantic_typing (Γ ++ A) B Core.tuniv -> 
  semantic_typing Γ M (Core.tpi A B) -> 
  semantic_typing Γ N A  -> 
(* ------------------------ *)
  semantic_typing Γ (Core.app M N) B[N..].
Proof.
  (* Variable naming follows Adequacy2.agda's [adequacySub2-App-core].
     Agda → Coq:
       dA dB d1 d2          ↦  T1 T2 T3 T4         (the four typings)
       semantic versions    ↦  s1 s2 s3 s4         (semantic_typings)
       u1                   ↦  u1                  (result element)
       ac1                  ↦  a1                  (result type elt)
       evAc1                ↦  ER                  (EvalRel of B[N..] at a1)
       v0                   ↦  v0                  (argument value)
       evA_v0               ↦  evA_v0              (EvalRel N ρ v0)
       evF_sing             ↦  evF_sing            (EvalRel M ρ (v0 ↦ u1))
       typed_f → u_big, a_pi, le_sing, evF_big, fm_big, evPi
       g_big, b_pi, f_pi    ↦  g_big, b_pi, f_pi   (post-destruct)
       typed_a → u_arg, ...
       pav_fun              ↦  pav_fun             (PiAppVal of u_big)
       val_arg              ↦  val_arg             (Val of N at u_arg)
       val_app_raw          ↦  val_app_raw         (PiAppVal applied)
   *)
  move=> T1 T2 T3 T4 s1 s2 s3 s4.
  move=> ρ m Δ σ TS FR VS u1 a1 WT1 Ex ER.
  specialize (s1 ρ m Δ σ TS FR VS).
  specialize (s3 ρ m Δ σ TS FR VS).
  specialize (s4 ρ m Δ σ TS FR VS).
  cbn in Ex.
  destruct (Raw.is_bot u1) eqn:HB.
  - (* EvalRel (app M N) is bot *)
    destruct u1; try done.
    dependent destruction WT1. cbn.
    destruct a; try done.
  -
    have TD : typing Δ N[σ] A[σ].
    { eapply substitution_tm; eauto. eapply typing_ctx; eauto. }

    (* EvalRel (app M N) decomposes: there is an argument value v0 such that
       M evaluates to the singleton (v0 ↦ u1) and N evaluates to v0. *)
    move: Ex => [v0 [evF_sing evA_v0]].

    (* Typed enlargement of the function via theorem1 (= typing_EvalRel). *)
    move: (typing_EvalRel T3 FR) => typed_f.
    unfold InvTyped in typed_f.
    move: (typed_f _ evF_sing) => [u_big [a_pi [wt_big [le_sing [evF_big evPi]]]]].
    clear typed_f.
    (* Only [abs g_big] is non-trivial. *)
    unfold singleton in le_sing. rewrite HB in le_sing.
    destruct u_big as [| | | | | | g_big]; try done.
    (* Decompose le_sing: (v0 ↦ u1) ≤ abs g_big forces an entry in g_big
       whose sup over keys ≤ v0 is ≥ u1. *)
    inversion wt_big. subst.
    rewrite le_abs in le_sing.
    cbn in le_sing.
    destruct (app g_big v0) eqn:APP_g_big_v0; try done.
    rewrite Bool.andb_true_r in le_sing.

    have Vg_big : valid_fun g_big by eauto with valid.
    (* From wt_big : wt (abs g_big) (tpi b_pi f_pi), the type-side f_pi is
       valid (it's the wt_abs's 4th arg, a wt (tpi _ _) tuniv). *)
    have Vu1 : valid u1 by eapply wt_valid_tm; eauto.
    have Vv0 : valid v0 by eapply EvalRel_valid; eauto.

    (* Typed enlargement of the argument. *)
    move: (typing_EvalRel T4 FR) => typed_a.
    move: (typed_a _ evA_v0) => [u_arg [t_arg [wt_arg [le_arg [evA_arg evT_arg]]]]].
    clear typed_a.
    have Vu_arg : valid u_arg by eauto with valid.

    (* Image of u_arg under g_big (term-side sup) and under the type-side
       function (renamed [f_pi] in Agda — here it is the [g] of wt_abs). *)
    destruct (valid_app_exists Vg_big Vu_arg) as [e_sup [APP_g_big_arg Ve_sup]].
    move: (le_valid_compatible Vu_arg le_arg) => C_arg.
    move: (le_fun_mono_arg Vg_big Vv0 Vu_arg C_arg le_arg APP_g_big_v0 APP_g_big_arg)
      => [_ le_e_sup].

    (* Type-side image of u_arg under the type-side function of the big pi
       (Agda calls it f_pi; here it is the [g] introduced by inversion of
       wt_big above).  We obtain its validity by chaining wt_valid_tm on
       the 4th wt_abs arg (wt (tpi _ g) tuniv) and then valid_tpi2. *)
    have Vf_pi : valid_fun g by eauto with valid.
    destruct (valid_app_exists Vf_pi Vu_arg) as [t_sup [APP_f_pi_arg Vt_sup]].
    (* Image of v0 under the same type-side function, for use with
       le_fun_mono_arg to establish [le t_sup_v0 t_sup]. *)
    destruct (valid_app_exists Vf_pi Vv0) as [t_sup_v0 [APP_f_pi_v0 Vt_sup_v0]].
    move: (le_fun_mono_arg Vf_pi Vv0 Vu_arg C_arg le_arg
             APP_f_pi_v0 APP_f_pi_arg) => [_ le_t_sup].

    (* Apply s3 (semantic_typing of M) at the big witness. *)
    specialize (s3 _ _ wt_big evF_big evPi).
    asimpl in s3.
    dependent destruction wt_big.
    cbn in s3.
    move: s3 => [vt_pi vpi_fun].
    (* Further destruct to expose the inner wt_tpi (b_pi, f_pi, ...). *)
    dependent destruction wt_big.
    apply ValTy_Val in vt_pi.
    cbn in vt_pi.
    destruct vt_pi as (A_pi & B_pi & red_pi & _ & _ & _ & vA_pi & piEV & piEE).
    unfold Rec.ValPi in vpi_fun.
    destruct vpi_fun as (A0 & B0 & red_fun & pav_fun).
    have red_refl : HeadRed (Core.tpi A[σ] B[⇑ (σ)]) (Core.tpi A[σ] B[⇑ (σ)])
      by eapply ms_refl; eauto.
    move: (HeadRed_tpi_det red_fun red_refl) => [eqA_self eqB_self].
    move: (HeadRed_tpi_det red_fun red_pi)   => [eqA_pi   eqB_pi].
    subst.

    (* Validity / non-bot facts. *)
    have NBu1 : ~ is_bot u1.
    { apply EvalRel_valid in evF_sing. unfold singleton in evF_sing.
      rewrite HB in evF_sing. cbn in evF_sing.
      destruct u1; try done. }
    have NBe   : ~ is_bot e by destruct u1; destruct e; try done.
    have NBe_sup : ~ is_bot e_sup by admit.

    (* From evPi : EvalRel (Core.tpi A B) ρ (tpi a g) we extract the EvalRel
       on the syntactic domain (used to apply s4 below). *)
    have evPi_copy : EvalRel (Core.tpi A B) ρ (tpi a g) by exact evPi.
    cbn in evPi.
    move: evPi => [_ [_ [evA_a _]]].
    (* evA_a : EvalRel A ρ a *)

    (* Step 1: pav_fun applied to (u_arg, e_sup, t_sup) and the syntactic
       argument N[σ].  Its remaining premise is a Val of N[σ] at A[σ]
       with the witness produced by wt_abs_inv1.                              *)
    specialize (pav_fun u_arg e_sup t_sup Vu_arg APP_g_big_arg NBe_sup
                        APP_f_pi_arg N[σ] TD).

    (* Step 2: discharge that premise via s4 (semantic_typing of N).
       The witness expected by pav_fun is equal to ours by wt_unique, so
       a single rewrite bridges them.                                       *)
    have WT_u_arg_a : wt u_arg a
      := w u_arg e_sup Vu_arg APP_g_big_arg NBe_sup.
    move: (s4 u_arg a WT_u_arg_a evA_arg evA_a) => Val_N.
    erewrite (wt_unique WT_u_arg_a) in Val_N.
    specialize (pav_fun Val_N).
    (* pav_fun : Val Δ (Core.app M[σ] N[σ]) B[⇑σ][N[σ]..] (wt_abs_inv2 ...) *)

    (* Step 3: bridge the syntactic substitution
         B[⇑σ][N[σ]..]  =  B[N..][σ]
       so pav_fun's conclusion is at the goal's syntactic type. *)
    have subst_comm : B[⇑ σ][N[σ]..] = B[N..][σ] by admit.
    rewrite subst_comm in pav_fun.

    (* Step 4: EvalRel_Pi_app_type — the codomain B[N..] evaluates to t_sup. *)
    have Vρ : valid_env ρ by eauto with valid.
    have NBt_sup : ~ is_bot t_sup by admit.
    have evB_t_sup : EvalRel B[N..] ρ t_sup
      by eapply EvalRel_Pi_app_type;
         [ exact evPi_copy | exact Vρ | exact Vu_arg
         | exact APP_f_pi_arg | exact NBt_sup | exact evA_arg ].

    (* Step 5: EvalRel_app_Comp — ER and evB_t_sup both witness EvalRel of
       B[N..] in ρ, so a1 and t_sup are compatible. *)
    have C_a1_t_sup : compatible a1 t_sup
      by eapply EvalRel_app_Comp; eauto.

    (* Steps 6, 7: derive [le a1 t_sup] and [le u1 e_sup]. *)
    have le_a1_t_sup : le a1 t_sup by admit.
    have le_u1_e_sup : le u1 e_sup by admit.

    (* Universe witnesses for Val_transport.
       - WT_t_sup_univ via w2 (the wt_tpi's output-typing forall), which
         needs ~ is_bot t_sup. *)
    have WT_t_sup_univ : wt t_sup tuniv
      := w2 u_arg t_sup Vu_arg APP_f_pi_arg NBt_sup.
    have WT_a1_univ   : wt a1 tuniv    by admit.   (* from h2 / typing of B at u_arg *)

    (* Step 8: Val_transport bridges
           Val ... (wt e_sup t_sup)  ↦  Val ... (wt u1 a1) = WT1.            *)
    (*
    eapply (Val_transport Δ (Core.app M[σ] N[σ]) B[N..][σ]
              e_sup u1 t_sup a1
              _ WT1
              WT_t_sup_univ WT_a1_univ
              le_u1_e_sup le_a1_t_sup).
    exact pav_fun. *)
Admitted.

(* t_nat: ctx Γ ⟹ tnat : tuniv 0 *)
Lemma st_nat :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tnat Core.tuniv.
Proof.
  move=> _ ρ m Δ σ TS FR VS u a WT EM EA.
  asimpl.
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = tnat *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt tnat bot impossible *) inversion WT.
    + (* a = tuniv n0; le (tuniv n0) (tuniv 0) ⟹ n0 = 0 *)
      dependent destruction WT. done.
Qed.

(* t_zero: ctx Γ ⟹ zero : tnat *)
Lemma st_zero :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.zero Core.tnat.
Proof.
  move=> _ ρ m Δ σ TS FR VS u a WT EM EA.
  asimpl.
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = zero *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt zero bot impossible *) inversion WT.
    + (* a = tnat *)
      dependent destruction WT.
      cbn. exact ms_refl.
Qed.

(* t_succ: M : tnat ⟹ succ M : tnat *)
Lemma st_succ M :
  typing Γ M Core.tnat ->
  semantic_typing Γ M Core.tnat ->
(* ------------------------- *)
  semantic_typing Γ (Core.succ M) Core.tnat.
Proof.
  move=> T1 ST ρ m Δ σ TS FR VS u a WT EM EA.
  asimpl.
  destruct (Raw.is_bot u) eqn:HU.
  { destruct u; try done. apply Val_Bot. }
  cbn in EM. rewrite HU in EM.
  move: EM => [Vu [a' [LEs EMa]]].
  destruct u as [| | | | | |]; cbn in HU; try done.
  destruct a; cbn in EA; try done.
  - (* a = bot: wt (succ v0) bot impossible *) inversion WT.
  - (* a = tnat *)
    dependent destruction WT. 
    cbn.
    exists M[σ]. split; first by apply ms_refl.
    rewrite le_succ in LEs.
    have EvM_v : EvalRel M ρ u.
    { eapply EvalRel_down with (u := a'); eauto.
      apply fits_valid_env in FR. exact FR. }
    have EvT : EvalRel Core.tnat ρ tnat by [].
    exact (ST ρ m Δ σ TS FR VS u tnat WT EvM_v EvT).
Qed.

(* t_nrec: T : (Γ ++ tnat) ⊢ tuniv i, M0 : T[zero..], M1 : tpi tnat (tpi T U⟨↑⟩)
   ⟹ nrec T M0 M1 : tpi tnat T *)
Lemma st_nrec (T U : Tm (S n)) M0 M1 :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  U = T[rho] ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T U⟨↑⟩)) ->
(* ------------------------- *)
  semantic_typing Γ (Core.nrec T M0 M1) (Core.tpi Core.tnat T).
Proof. Admitted.

(* t_tpi: A : tuniv i, (Γ ++ A) ⊢ B : tuniv i ⟹ tpi A B : tuniv i *)
Lemma st_tpi A B :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
(* ------------------------- *)
  semantic_typing Γ (Core.tpi A B) Core.tuniv.
Proof. Admitted.

Lemma st_univ :
  ctx Γ ->
(* ------------------------- *)
  semantic_typing Γ Core.tuniv Core.tuniv.
Proof.
  move=> _ ρ m Δ σ TS FR VS u a WT EM EA.
  asimpl.
  destruct u; cbn in EM; try done.
  - apply Val_Bot.
  - (* u = tuniv n0; le (tuniv n0) (tuniv i) ⟹ n0 = i *)
    destruct a; cbn in EA; try done.
    + (* a = bot: wt (tuniv n0) bot impossible *) inversion WT.
    + (* a = tuniv n1; le (tuniv n1) (tuniv j) ⟹ n1 = j *)
      dependent destruction WT.
      cbn. done.
Qed.


(* -------- semantic conversion rules -------- *)

(* c_conv: M ≡ N : A, A ≡ B : tuniv i ⟹ M ≡ N : B *)
Lemma sc_conv M N A B :
  conv Γ M N A ->
  conv Γ A B Core.tuniv ->
  semantic_conv2 Γ M N A ->
  semantic_conv2 Γ A B Core.tuniv ->
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
Lemma sc_app1 A B N N' M :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  conv Γ N N' (Core.tpi A B) ->
  typing Γ M A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_conv2 Γ N N' (Core.tpi A B) ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N' M) B[M..].
Proof. Admitted.

(* c_app2: N : (tpi A B), M ≡ M' : A ⟹ app N M ≡ app N M' : B[M..] *)
Lemma sc_app2 A B N M M' :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  conv Γ M M' A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_conv2 Γ M M' A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app N M) (Core.app N M') B[M..].
Proof. Admitted.

(* c_beta: A, B, body N, arg M ⟹ app (abs A N) M ≡ N[M..] : B[M..] *)
Lemma sc_beta A B M N :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing (Γ ++ A) N B ->
  typing Γ M A ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing (Γ ++ A) N B ->
  semantic_typing Γ M A ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.abs A N) M) N[M..] B[M..].
Proof. Admitted.

(* c_eta: function extensionality *)
Lemma sc_eta A B (N N' : Tm n) :
  typing Γ A Core.tuniv ->
  typing (Γ ++ A) B Core.tuniv ->
  typing Γ N (Core.tpi A B) ->
  typing Γ N' (Core.tpi A B) ->
  conv (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
  semantic_typing Γ A Core.tuniv ->
  semantic_typing (Γ ++ A) B Core.tuniv ->
  semantic_typing Γ N (Core.tpi A B) ->
  semantic_typing Γ N' (Core.tpi A B) ->
  semantic_conv2 (Γ ++ A) (Core.app N⟨↑⟩ (var var_zero))
                          (Core.app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
(* ------------------------- *)
  semantic_conv2 Γ N N' (Core.tpi A B).
Proof. Admitted.

(* c_nrec_Z: app (nrec T M0 M1) zero ≡ M0 : T[zero..] *)
Lemma sc_nrec_Z M0 M1 (T : Tm (S n)) :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) Core.zero) M0 T[Core.zero..].
Proof. Admitted.

(* c_nrec_S: app (nrec T M0 M1) (succ n) ≡ app (app M1 n) (app (nrec ...) n) : T[(succ n)..] *)
Lemma sc_nrec_S (T : Tm (S n)) M0 M1 (e : Tm n) :
  typing (Γ ++ Core.tnat) T Core.tuniv ->
  typing Γ M0 (T[Core.zero..]) ->
  typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
  semantic_typing (Γ ++ Core.tnat) T Core.tuniv ->
  semantic_typing Γ M0 (T[Core.zero..]) ->
  semantic_typing Γ M1 (Core.tpi Core.tnat (Core.tpi T T[rho]⟨↑⟩)) ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.app (Core.nrec T M0 M1) (Core.succ e))
                   (Core.app (Core.app M1 e) (Core.app (Core.nrec T M0 M1) e))
                   T[(Core.succ e)..].
Proof. Admitted.


Lemma sc_tuniv M N  :
  conv Γ M N Core.tuniv ->
  semantic_conv2 Γ M N Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ M N Core.tuniv.
Proof. Admitted.

(* c_tpi: A0 ≡ A1 : tuniv i, B0 ≡ B1 : tuniv i ⟹ tpi A0 B0 ≡ tpi A1 B1 : tuniv i *)
Lemma sc_tpi A0 A1 (B0 B1 : Tm (S n)) :
  conv Γ A0 A1 Core.tuniv ->
  conv (Γ ++ A0) B0 B1 Core.tuniv ->
  semantic_conv2 Γ A0 A1 Core.tuniv ->
  semantic_conv2 (Γ ++ A0) B0 B1 Core.tuniv ->
(* ------------------------- *)
  semantic_conv2 Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv.
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
--     WfCtx H                   ≈  ctx Γ
--     FinMem u a                ≈  wt u a
--     Val2 H M[σ] A[σ] u a      ≈  Val M[σ] A[σ] (h : wt u a)
u--     EqVal2 H M[σ] N[σ] A[σ]   ≈  EqVal M[σ] N[σ] A[σ] (h : wt u a)
------------------------------------------------------------------------
*)

(* adequacySub2 (Adequacy2.agda, p.660 Theorem 2 part 4):

       HasType G M A
     → CoherentEnv ρ, ValidSub2 H G σ ρ, Fits G ρ,
       WtSub H G σ, WfCtx H
     → (u : FinEl) -> EvalRel M ρ u
     → (a : FinEl) -> EvalRel A ρ a ->  FinMem u a
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

Definition empty {n} : fin 0 -> Tm n := 
  fun f => match f with end. 


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
    eapply (@fits_cons _ _ _ _ bot bot); eauto.
    + apply EvalRel_bot.
    + eapply wt_bot. eapply wt_tuniv.
    + eapply wt_bot. eapply wt_bot. eapply wt_tuniv. 
Qed.

Lemma ValSub_id n (Γ:Ctx n) :
  ValSub Γ Γ var bot_env.
Proof.
  unfold ValSub.
  move=> i u Vu LE a ER h.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  dependent destruction h.
  cbn.
  destruct a; done.
Qed.


Lemma EqValSub_id n (Γ:Ctx n) :
  EqValSub Γ Γ var var bot_env.
Proof.
  unfold EqValSub.
  move=> i u Vu LE a ER h.
  unfold bot_env in LE.
  apply le_bot_inv in LE. subst.
  dependent destruction h.
  cbn.
  destruct a; done.
Qed.

(* evalRel_Pi_trivial: every Pi type evaluates to (tpi bot nil).
   Mirrors evalRel-Pi-trivial in PiInjectivity.agda. *)
Lemma evalRel_Pi_trivial {n} (A : Tm n) (B : Tm (S n)) (ρ : Env n) :
  EvalRel (Core.tpi A B) ρ (tpi bot nil).
Proof.
  cbn.
  split; first by [].                      (* valid bot *)
  split; first by [].                      (* valid_fun nil *)
  split.                                    
  apply EvalRel_bot.
  exists bot.
  split.
  apply EvalRel_bot. 
  move=> u v IN APP. 
  exists bot. split.
  eapply wt_bot. eapply wt_bot. eapply wt_tuniv.
  split.
  rewrite le_bot. done.
  cbn in APP. inversion APP.
  apply EvalRel_bot.
Qed.

(* piConv (Corollary 6, parts 1–3):
   From conv Γ A₀ (tpi B₁ F₁) (tuniv i) extract HeadRed A₀ (tpi B₀ F₀)
   and conversions on the domain and codomain.
 *)
Lemma piConv {n} (Γ : Ctx n) (A0 : Tm n) (B1 : Tm n) (F1 : Tm (S n)) :
  conv Γ A0 (Core.tpi B1 F1) Core.tuniv ->
  exists B0 F0,
    HeadRed A0 (Core.tpi B0 F0)
    /\ conv Γ B0 B1 Core.tuniv
    /\ conv (Γ ++ B0) F0 F1 Core.tuniv.
Proof.
  move=> Cv.
  pose ρ : Env n := bot_env.
  pose σ : Sub n n := var.
  have CΓ : ctx Γ. 
  { eapply conv_ctx; eauto. } 
  have Fρ  : fits Γ ρ.
  { eapply fits_bot_env. eapply CΓ. }
  have TSσ : typing_subst Γ σ Γ.
  { apply typing_subst_id. eauto. }
  have VSσ : ValSub Γ Γ σ ρ.
  { eapply ValSub_id. }
  have EVSσ: EqValSub Γ Γ σ σ ρ.
  { eapply EqValSub_id. } 

  (* Pick the witness u = (tpi bot nil) at type (tuniv i). *)
  pose u := tpi bot nil.
  have Vpi : valid (tpi bot nil) by [].
  have Hwt : wt u (tuniv).
  { rewrite /u. apply: (@wt_tpi bot nil ).
    - econstructor; eauto. eapply wt_tuniv.
    - move => ui vi Vu APP NB.
      cbn in APP. inversion APP. subst. done.
    - move => ui vi Vu APP NB.
      cbn in APP. inversion APP. subst. done.
    - exact: Vpi. }

  (* EvalRel for (tpi B1 F1) and (transported via conv) for A0. *)
  have EvalPi : EvalRel (Core.tpi B1 F1) ρ u.
  { rewrite /u. exact: evalRel_Pi_trivial. }
  have EvA0 : EvalRel A0 ρ u.
  { have IC : InvConv Γ A0 (Core.tpi B1 F1) Core.tuniv ρ.
    { eapply conv_EvalRel; eauto. }
    move: IC => [_ [_ [_ bwd]]]. apply: bwd. exact: EvalPi. }
  have EvUni : EvalRel Core.tuniv ρ (tuniv).
  { cbn. auto. }

  (* Apply adequacyEqSub2 to the conversion at the chosen witness. *)
  move:
    (@adequacyEqSub _ Γ A0 (Core.tpi B1 F1) Core.tuniv Cv) => ev2.
  unfold semantic_conv2 in ev2.
  specialize (ev2 ρ _ Γ σ σ TSσ TSσ Fρ EVSσ
       u tuniv Hwt EvA0 EvUni) as ev2.
  (* ev2 : EqVal Γ A0[σ] (tpi B1 F1)[σ] (tuniv i)[σ] Hwt *)

  asimpl in ev2.

  (* EqVal at (tuniv i) unfolds to (ValTy /\ ValTy /\ EqValTy);
     EqValTy at u = (tpi bot nil) exposes the head reductions and
     the domain/codomain conversions. *)
  dependent destruction Hwt.
  cbn in ev2.

  destruct ev2 as [_ [_ EQTy]].
  cbn in EQTy.
  destruct EQTy as [_ [_ ExA]].
  destruct ExA as [A [B [HRA0 [A' [B' rest]]]]].
  destruct rest as [HRpi [convA [convB _]]].

  (* HRpi : HeadRed (tpi B1 F1) (tpi A' B') — Pi is a head-normal
     form, so A' = B1 and B' = F1 by determinacy. *)
  have [EQ1 EQ2] : A' = B1[σ] /\ B' = F1[⇑σ].
  { eapply HeadRed_tpi_det; first exact: HRpi. exact: ms_refl. }
  subst A' B'.

  exists A, B. repeat split. 
  subst σ. asimpl in HRA0. done.
  subst σ. asimpl in convA. done.
  subst σ. asimpl in convB. done.
Qed.

(* piInjectivity (Corollary): from conv Γ (tpi A₀ B₀) (tpi A₁ B₁) U,
   extract domain and codomain conversions.
   Mirrors piInjectivity in PiInjectivity.agda. *)
Lemma piInjectivity {n} (Γ : Ctx n)
  (A0 A1 : Tm n) (B0 B1 : Tm (S n)) :
  conv Γ (Core.tpi A0 B0) (Core.tpi A1 B1) Core.tuniv ->
  conv Γ A0 A1 Core.tuniv /\
  conv (Γ ++ A0) B0 B1 Core.tuniv.
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

