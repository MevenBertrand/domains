From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
From Stdlib Require Import Classes.RelationClasses 
  Classes.Morphisms Lia Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import findom.
Require Import types.
Require Import syntax.syntax.
Require Import syntax.typing.

Import SyntaxNotations.
Import SubstNotations.

Open Scope syntax_scope.

Import Raw.

(* ------------------------------------------------- *)

(* analogue of RawSemantics.agda.  

   Unlike the version in Figure 1 of the paper, this semantics 
   does not use finitary projection for some reason.

   Unlike the agda version, this version uses the 
   (u,v) in finfun's directly instead of relying on 
   selection.

*)

(* Part 1: Finite environments *)

Definition Env n := fin n -> elt.

  
(* Part 2: EvalRel *)

Notation " a ↦ b " := (singleton a b) (at level 70).
  
Fixpoint EvalRel {n} (t : Tm n) : Env n -> elt -> Prop := 
  let EvalRel_fun {n} (M : Tm (S n))
    : Env n -> elt -> list (elt * elt) -> Prop := 
    fun ρ a g => 
      forall u v, In (u,v) g -> 
       exists x, le x u /\ wt x a /\ EvalRel M (x .: ρ) v
  in 
  match t return Env n -> elt -> Prop with 
  | Core.var i => 
      fun ρ b => valid b /\ le b (ρ i)
  | Core.tuniv i => fun ρ b =>
             (* i.e. b == bot \/ b == tuniv i *)
             le b (tuniv i)
  | Core.tnat => fun ρ b => 
             (* b == bot \/ b == tnat *)
             le b tnat
  | Core.zero => fun ρ b => 
             le b zero
  | Core.succ M => fun ρ b => 
               if is_bot b then True else
                 valid b /\
                 exists a, le b (succ a) /\ EvalRel M ρ a
  | Core.tpi A B => fun ρ b =>
        match b with 
        | bot => True
        | tpi a g => 
            valid a 
            /\ valid_fun g
            /\ exists i, wt a (tuniv i) 
            /\ EvalRel A ρ a 
            /\ EvalRel_fun B ρ a g
        | _ => False
        end
  | Core.app M N => fun ρ b => 
         if is_bot b then True else 
            exists a, EvalRel M ρ (a ↦ b) /\ EvalRel N ρ a 
  | Core.abs A M => fun ρ b => 
         match b with 
         | bot => True
         
         | abs g => 
                valid_fun g 
              /\ ~~ is_nil g
              /\ exists i a, wt a (tuniv i) 
              /\ EvalRel A ρ a
              /\ EvalRel_fun M ρ a g
              
                
         | _ => False 
         end
  | nrec T M0 M1 => fun ρ b =>
         if is_bot b then True else False                  
  end.

Definition EvalRel_fun {n} (M : Tm (S n))
    : Env n -> elt -> list (elt * elt) -> Prop := 
    fun ρ a g => 
      forall u v, In (u,v) g -> 
       exists x, le x u /\ wt x a /\ EvalRel M (x .: ρ) v.

(** * validity *)


Definition valid_env {n} (ρ : Env n) :=
  forall x, valid (ρ x).

Lemma valid_nil : valid_env null.
  unfold valid_env. auto_case. Qed.
Lemma valid_cons n x (ρ : Env n) 
  : valid x -> valid_env ρ -> valid_env (x .: ρ).
Proof.  move=> Vx Vr. unfold valid_env. auto_case. Qed.

Hint Resolve valid_cons: valid.

  
Lemma EvalRel_valid {n} (M : Tm n) (ρ : Env n) (u : elt) : 
  EvalRel M ρ u -> valid u.
Proof.
  move: ρ u.
  induction M.
  all: move=> ρ u.
  all: cbn [EvalRel].
  - auto.
  - (* abs *)
    destruct u; try done.
    move=> [Vl [Nl [i [a [WT [E1 _]]]]]]. 
    cbn. apply /andP. split; eauto. 
  - destruct (is_bot u) eqn:h. 
    destruct u; try done.
    move=> [a [E1 E2]].
    apply IHM1 in E1.
    unfold singleton in E1.
    rewrite h in E1.
    cbn in E1.
    move: E1 => /andP. 
    move=> [h1 _]. move: h1 => /andP. move=> [h1 h2].
    move: h2 => /andP. move=> [h2 _]. move: h2 => /andP. auto.
  - destruct u; try done.
  - destruct (is_bot u) eqn:h.
    destruct u; try done.
    eauto.
  - (* nrec (fake case) *)
    destruct (is_bot u) eqn:h; try done.
    destruct u; try done.
  - destruct u; try done.
  - (* tpi *)
    destruct u; try done.
    move=> [Vu [Vf [i [WTu [E1 _]]]]].
    eapply valid_tpi_intro; eauto.
  - destruct u; try done.
Qed.

(** * monotonicity *)

Definition le_env {n} (ρ1 ρ2 : Env n) := 
  forall x, le (ρ1 x) (ρ2 x).
Lemma le_env_nil : le_env null null.
  unfold le_env. auto_case. Qed.
Lemma le_env_cons n u v (ρ1 ρ2 : Env n):
  le u v -> le_env ρ1 ρ2 -> le_env (u .: ρ1) (v .: ρ2).
Proof. move=> L1 L2. unfold le_env. auto_case. Qed.


Lemma EvalRel_mono_env {n} (M : Tm n) (ρ ρ' : Env n) u :
  EvalRel M ρ u -> valid_env ρ -> valid_env ρ' -> le_env ρ ρ' -> EvalRel M ρ' u.
Proof.
  dependent induction M.
  all: cbn [EvalRel].
  all: move=> h1 V1 V2 h2. 
  - (* M = x *)
    specialize (h2 f). specialize (V1 f). specialize (V2 f).
    move: h1 => [Vu h1]. 
    split; auto. eapply (le_trans Vu V1 V2); eauto.
  - (* M = Abs M1 M2,  *)
    destruct u ; try done. 
    move: h1 => [Vl [Nl [i [a [WT [ER f]]]]]].
    repeat split; eauto.
    exists i ,a. repeat split; eauto.
    move=> u1 v1 h3. 
    specialize (f u1 v1 h3).
    destruct f as [x [Lex [WT2 EM2]]].
    have Vx: valid x. eauto with valid.
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid. 
    eapply le_env_cons; eauto using le_refl.
  - (* M = app M1 M2 *)
    destruct (is_bot u); try done.
    destruct h1 as [a [E1 E2]].
    exists a. split; eauto.
  - (* M = zero *)
    destruct (is_bot u); try done.    
  - (* M = succ M *)
    destruct (is_bot u); try done.
    destruct h1 as [Vu [a [LE E]]].
    eapply IHM in E; eauto.
  - (* M = nrec *)
    destruct (is_bot u); try done.
  - (* M = tnat *)
    destruct (is_bot u); try done.
  - (* M = tpi M1 M2 *)
    destruct u; try done.
    destruct h1 as [Vu [Vl [i1 [WT1 [E1 h3]]]]].
    repeat split; eauto.
    exists i1. repeat split; eauto. 
    intros u1 v1 APP.
    specialize (h3 u1 v1 APP).
    destruct h3 as [x [Lx [WT E2]]].
    exists x. repeat split; eauto.
    eapply IHM2; eauto with valid.
    have Vx : valid x. eauto with valid.
    eapply le_env_cons; eauto using le_refl.
  - (* M = tuniv n *)
    destruct u; try done.
Qed.    



(* Lam-edgewise *)
Lemma lam_edgewise {n} {A : Tm n} {M ρ g} : 
  EvalRel (Core.abs A M) ρ (abs g) -> 
  exists a, EvalRel A ρ a 
       /\ forall u v, In (u,v) g -> 
         exists x, wt x a /\ EvalRel M (x .: ρ) v.
Proof.
  move=> E1.
  cbn [EvalRel] in E1.
  destruct E1 as [Vg [Ng [i [a [WT [EA body]]]]]].
  exists a. split; eauto.
  intros u v ein.
  have Vu: valid u. { eapply valid_fun_subterms in Vg.
  eapply forallb_forall in Vg. 2: eauto. cbn in Vg.
  move: Vg => /andP. auto. } 

  destruct (valid_app_exists Vg Vu) as [rw [EQ Vw]].
  specialize (body u v ein).
  destruct body as [x [Lex [WT2 ER2]]].
  exists x. split; eauto.
Qed.

Lemma EvalRel_bot {n} (M : Tm n) (ρ : Env n) : 
  EvalRel M ρ bot.
Proof.
  destruct M eqn:EQ; cbn; try done.
  (* var *) split; eauto. eapply le_bot; eauto.
Qed.


Lemma EvalRel_fun_compatible {n} (M : Tm (S n)) ρ a l b l0 
  (Vρ : valid_env ρ)
  (IHM : forall (ρ : Env (S n)) (a b : elt),
      valid_env ρ -> EvalRel M ρ a -> EvalRel M ρ b -> compatible a b)
  (Vl : valid_fun l)
  (h1 : EvalRel_fun M ρ a l)
  (Vl0 : valid_fun l0)
  (h2 : EvalRel_fun M ρ b l0) :
  compatible_fun l l0.
Proof. 
  intros.
  apply /forallb_forall.
  move=> [u1 v1] Inl.
  specialize (h1 _ _ Inl).
  move: h1 => [x1 [LE1 [WTx1 E21]]].
  apply /forallb_forall.
  move=> [u2 v2] Inl0.
  specialize (h2 _ _ Inl0).
  move: h2 => [x0 [LE0 [WTx0 E20]]].
    
  apply /implyP.
  move=> Cu.
  have Cx: compatible x1 x0.
  { move: (comp_down LE1 Cu) => C1.
      move: (compatible_sym C1) => C2.
      move: (comp_down LE0 C2) => C3.
      eapply compatible_sym. auto. } 

  destruct (compatible_lub_exists Cx) as [w LUB].
  have LT1 : le_env (x1 .: ρ) (w .: ρ).
  { unfold le_env. auto_case. 
      have Vf: valid (ρ f) by eapply Vρ.
      eapply le_refl; eauto. 
      eapply le_lub_left; eauto with valid. } 
  have LT0 : le_env (x0 .: ρ) (w .: ρ).
  { unfold le_env. auto_case. 
      have Vf: valid (ρ f) by eapply Vρ.
      eapply le_refl; eauto. 
      eapply le_lub_right; eauto with valid. } 
  have Vw : valid_env (w .: ρ).
  { unfold valid_env. auto_case. eauto with valid. } 
  have Vx1 : valid_env (x1 .: ρ).
  { unfold valid_env. auto_case. eauto with valid. } 
  have Vx0 : valid_env (x0 .: ρ).
  { unfold valid_env. auto_case. eauto with valid. } 
  
  move: (EvalRel_mono_env E21 Vx1 Vw LT1) => E31. 
  move: (EvalRel_mono_env E20 Vx0 Vw LT0) => E30. 
  eapply (IHM _ _ _ Vw E31 E30). 
Qed.


Lemma EvalRel_compatible {n} (M : Tm n) :
  forall (ρ : Env n) (a b : elt), valid_env ρ ->
  EvalRel M ρ a -> EvalRel M ρ b -> compatible a b.
Proof.
  induction M.
  all: cbn [EvalRel].
  all: move=> ρ a b Vρ.
  - (* var *) 
    move=> /andP h1 /andP h2. 
    move: h1 => /andP. move=> [C1 L1].
    move: h2 => /andP. move=> [C2 L2].
    specialize (Vρ f).
    eapply (Raw.le_valid_compatible_pair Vρ); eauto. 
  - (* abs M1 M2 *)
    destruct a; try done;
      destruct b; try done.

    move=> [i [a [WT1 [E1 h1]]]].
    move=> [i0 [b [WT2 [E2 h2]]]].
    cbn. 
    eapply EvalRel_fun_compatible; eauto.

  - (* app M1 M2 *)
    destruct (is_bot a) eqn:IBa; try done;
    destruct (is_bot b) eqn:IBb; try done.
    destruct a; try done.
    destruct b; try done.
    destruct a; try done. destruct b; done.
    destruct b; try done. destruct a; done.
    move=> [va [Ea1 Ea2]].
    move=> [vb [Eb1 Eb2]].
    move: (IHM1 _ _ _ Vρ Ea1 Eb1) => C1.
    move: (IHM2 _ _ _ Vρ Ea2 Eb2) => C2.
    unfold singleton in C1.
    rewrite IBa IBb in C1.
    cbn in C1.
    move: C1 => /andP. move=> [C1 _].
    move: C1 => /andP. move=> [C1 _].
    move: C1 => /implyP. move=> C1.
    eapply C1. eapply C2.
  - (* zero *)
    move=> L1 L2.
    destruct a; try done. destruct b; done.
    destruct b; try done.
  - (* succ M *)
    destruct (is_bot a) eqn:IBa; try done;
    destruct (is_bot b) eqn:IBb; try done.
    destruct a; try done. destruct b; done.
    destruct a; try done. destruct b; done.
    destruct b; try done. destruct a; done.
    move=> [Va [a0 [LEa Ea]]].
    move=> [Vb [b0 [LEb Eb]]].
    move: (IHM _ _ _ Vρ Ea Eb) => C.
    destruct a; try done.
    destruct b; try done.
    cbn. rewrite le_succ in LEa. rewrite le_succ in LEb.
    cbn in Va. cbn in Vb.
    move: (comp_down LEa C) => Ca.  
    move: (compatible_sym Ca) => CC.   
    move: (comp_down LEb CC) => Cb.
    eapply compatible_sym. eauto.
  - (* nrec *)
    destruct (is_bot a) eqn:IBa; try done;
    destruct (is_bot b) eqn:IBb; try done.
    destruct a; try done. destruct b; done.
  - (* tnat *)
    move=> LE1 LE2.
    destruct a; try done. destruct b; done.
    destruct b; done.
  - (* tpi *)
    destruct a; try done. destruct b; done.
    destruct b; try done.
    move=> [Va [Vl [ia [WTa [Ea h]]]]];
    move=> [Vb [Vl0 [ib [WTb [Eb ]]]]].
    cbn. erewrite IHM1; eauto. cbn.
      eapply EvalRel_fun_compatible; eauto.
  - (* tuniv *)
    move=> LE1 LE2.
    destruct a; try done. destruct b; done.
    destruct b; try done.
    cbn in *. apply Nat.eqb_eq in LE1. apply Nat.eqb_eq in LE2. 
    subst. eapply Nat.eqb_eq. done.
Qed.


Lemma EvalRel_down n (M : Tm n) (ρ : Env n) u u' :
  valid_env ρ -> valid u' -> 
  EvalRel M ρ u -> le u' u -> EvalRel M ρ u'.
Proof.
  move:ρ u u'.
  dependent induction M.
  all: move=> ρ u u' Vρ Vu' ER1 LE.
  all: have Vu1: valid u by eapply EvalRel_valid; eauto.
  all: cbn in ER1.
  all: cbn.

  - move: ER1 => [_ LE1].
    split; eauto. eapply le_trans; eauto.
  - (* abs *)
    destruct u; try done.
    destruct u'; try done.
    move: ER1 => [Vl [Nl [i [a [WTa [Ea h]]]]]].
    destruct u'; try done.
    move: Vu' => /andP. fold valid. fold (valid_fun l0). move=> [Vl0 Nl0].
    repeat split; eauto with valid. 
    exists i. exists a.  repeat split; eauto.
    move=> u v Inl0.
    rewrite le_abs in LE.
    unfold le_fun in LE.
    move: LE => /forallb_forall LE.
    specialize (LE _ Inl0). cbn in LE.
    destruct (app l u) eqn:APP; try done.
    
    have Vu: valid u.
      { 
         eapply valid_fun_subterms in Vl0.
         move: Vl0 => /forallb_forall. move=> VIn.
         specialize (VIn _ Inl0). 
         move: VIn => /andP. auto.
      }
    have Vv: valid v.
      { 
         eapply valid_fun_subterms in Vl0.
         move: Vl0 => /forallb_forall. move=> VIn.
         specialize (VIn _ Inl0). 
         move: VIn => /andP. auto.
      }
    have Ve: valid e. { eapply (@valid_app l u); eauto. } 

    move: e APP Ve Vl h LE.
    induction l as [|[ui vi]l].
    + intros. cbn in APP. inversion APP. subst.
      apply le_bot_inv in LE. subst.
      have NB: no_bot_result l0. {
        eapply valid_fun_no_bot. eapply Vl0.
      } 
      unfold no_bot_result in NB. 
      move: NB => /forallb_forall NB.
      specialize (NB _ Inl0). done.
    + move=> e APP Ve Vfl Inl Lve.
      rewrite app_cons_eq in APP.
      destruct (compatible ui u && le ui u) eqn:IN; try done.
      destruct (app l u) eqn:EqAPP; try done.
      ++ specialize (Inl ui vi ltac:(left;reflexivity)).
         move: Inl => [x [LEi [Wtx Evi]]].
         move: IN => /andP. move => [Cu LEu].
         exists x. repeat split; eauto.
         eapply (@le_trans x ui u); eauto with valid.
         have Vl: valid_fun l. eauto with valid.
         have Ve0: valid e0. eapply (@valid_app l u); eauto. 
(* not done or stuck, just tired *)
Admitted.

Lemma EvalRel_sup n (M : Tm n) (ρ : Env n) u u' v :
  valid_env ρ -> valid u -> valid u' -> compatible u u' -> 
  lub u u' = Some v ->
  EvalRel M ρ u -> EvalRel M ρ u' -> EvalRel M ρ v.
Proof.
(* by induction on M *)
Admitted.

Lemma EvalRel_compatible_ext {n} (M : Tm (S n)) ρ x1 x2 y1 y2 : 
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 -> 
  EvalRel M (x1 .: ρ) y1 -> 
  EvalRel M (x2 .: ρ) y2 -> 
  compatible y1 y2.
Proof.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = Some x}
    by  eapply compatible_lub_exists; eauto. 
  have Vx : valid x. eapply (valid_lub Vx1 Vx2); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_left; eauto. } 
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_right; eauto. } 

  eapply (EvalRel_compatible Vext); eauto.
Qed.  

Lemma EvalRel_ideal {n} (M : Tm (S n)) ρ x1 x2 y1 y2 : 
  valid_env ρ -> compatible x1 x2 -> valid x1 -> valid x2 -> 
  EvalRel M (x1 .: ρ) y1 -> 
  EvalRel M (x2 .: ρ) y2 -> 
  exists x y, lub x1 x2 = Some x /\ lub y1 y2 = Some y 
         /\ EvalRel M (x .: ρ) y.
  move=> Vρ CC Vx1 Vx2 E1 E2.
  have [x EQ] : { x & lub x1 x2 = Some x}
    by  eapply compatible_lub_exists; eauto. 
  have Vx : valid x. eapply (valid_lub Vx1 Vx2); eauto.
  have Vext : valid_env (x .: ρ). eauto with valid.
  have E1': EvalRel M (x .: ρ) y1.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_left; eauto. } 
  have E2': EvalRel M (x .: ρ) y2.
  eapply EvalRel_mono_env; eauto with valid.
  { unfold le_env. auto_case. eapply le_refl.
    eapply Vρ. eapply le_lub_right; eauto. } 
  have [y EQy] : { y & lub y1 y2 = Some y }.
  { eapply compatible_lub_exists.
    eapply (EvalRel_compatible Vext); eauto. }
  exists x. exists y.
  repeat split; auto.
  eapply EvalRel_sup with (u := y1)(u':=y2); eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_valid; eauto.
  eapply EvalRel_compatible; eauto.
Qed.

