
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.

From Equations Require Import Equations.

Require Import findom.

Import findom.Raw.


Lemma le_fun_mono h k u :
       valid_fun h -> valid_fun k ->
       le_fun h k -> valid u ->
       forall w1 w2, app h u = Some w1 -> app k u = Some w2 ->
                le w1 w2.
Proof.
  eapply OTL.le_fun_mono. eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_fun_mono_arg h u1 u2 :
       valid_fun h -> valid u1 -> valid u2 ->
       compatible u1 u2 -> le u1 u2 ->
       forall w1 w2, app h u1 = Some w1 -> app h u2 = Some w2 ->
                compatible w1 w2 /\ le w1 w2.
Proof.
  eapply OTL.le_fun_mono_arg with (k := max (max (rk_fun h) (rk u1)) (rk u2)).
  eapply OTL.OTLs. reflexivity.
Qed.

Lemma le_sup_lub u v w1 w2 :
 le u w2 -> le v w2 -> lub u v = Some w1 -> le w1 w2.
Proof.
  eapply OTL.le_sup_lub. eapply OTL.OTLs. reflexivity.
Qed.

(* The level of an element is its maximum universe level *)

Fixpoint level (u : elt) : nat :=
  let fix level_fun f :=
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (level vi) (level_fun tl)
    end in
  match u with 
  | bot => 0 
  | tnat => 0
  | tuniv k => k
  | zero => 0
  | succ v => level v
  | tpi a f => max (level a) (level_fun f)
  | abs f => level_fun f
  end.

Fixpoint level_fun (f : list (elt * elt)) :=
 match f with
      | nil => 0
      | (ui, vi) :: tl =>
          max (level vi) (level_fun tl)
 end.

Lemma level_fun_app f g : level_fun (f ++ g) = max (level_fun f) (level_fun g).
Proof. induction f as [|[ui vi]f].
       cbn. done.
       cbn. rewrite IHf. lia.
Qed.


Lemma level_lub u v w : 
  lub u v = Some w -> max (level u) (level v) = level w.
Proof.
  move: v w.
  induction u.
  all: move=> v w Lub.
  all: cbn; fold level_fun.
  - rewrite lub_bot_l in Lub. inversion Lub. done.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub; done.
    cbn in Lub. inversion Lub; done.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub. cbn. lia.
    cbn in Lub. destruct (n=?n0) eqn:E; try done. 
    rewrite Nat.eqb_eq in E. inversion Lub. cbn. subst. lia.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub; done.
    cbn in Lub. inversion Lub; done.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub. cbn. lia.
    cbn in Lub. destruct (lub u v) eqn:E; try done. inversion Lub. subst.
    cbn. eauto.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub. cbn. fold level_fun. lia.
    cbn in Lub.
    destruct (compatible_fun l l0); try done.
    destruct (lub u v) eqn:L1; try done. cbn in Lub. inversion Lub.
    cbn. fold level_fun. rewrite level_fun_app.
    specialize (IHu _ _ L1). lia.
  - destruct v; try done. rewrite lub_bot_r in Lub; inversion Lub. cbn. fold level_fun. lia.
    inversion Lub. 
    destruct (compatible_fun l l0); try done.
    inversion H0; subst. 
    cbn. fold level_fun.
    rewrite level_fun_app. lia.
Qed.

(*
Lemma level_lub_l u v w : 
  lub u v = Some w -> level u <= level w.
Proof.
  move: v w.
  induction u.
  all: move=> v w Lub.
  all: cbn; fold level_fun.
  all: try lia.
  - destruct v; try done. inversion Lub; done.
    cbn in Lub. destruct (n=?n0) eqn:E; try done.
    rewrite Nat.eqb_eq in E. inversion Lub. done.
  - destruct v; try done. inversion Lub; done.
    cbn in Lub. destruct (lub u v) eqn:E; try done. inversion Lub. subst.
    cbn. eauto.
  - destruct v; try done. inversion Lub; done.
    cbn in Lub.
    destruct (compatible_fun l l0); try done.
    destruct (lub u v) eqn:L1; try done. cbn in Lub. inversion Lub.
    cbn. fold level_fun. rewrite level_fun_app.
    specialize (IHu _ _ L1). lia.
  - destruct v; try done. inversion Lub; done.
    inversion Lub. 
    destruct (compatible_fun l l0); try done.
    inversion H0; subst. 
    cbn. fold level_fun.
    rewrite level_fun_app. lia.
Qed.


Lemma level_lub_r u v w : 
  lub u v = Some w -> level v <= level w.
Proof.
  move: u w.
  induction v.
  all: move=> u w Lub.
  all: cbn; fold level_fun.
  all: try lia.
  - destruct u; try done. inversion Lub; done.
    cbn in Lub. destruct (n0=?n) eqn:E; try done.
    rewrite Nat.eqb_eq in E. inversion Lub. subst. done.
  - destruct u; try done. inversion Lub; done.
    cbn in Lub. destruct (lub u v) eqn:E; try done. inversion Lub. subst.
    cbn. eauto.
  - destruct u; try done. inversion Lub; done.
    cbn in Lub.
    destruct (compatible_fun l0 l); try done.
    destruct (lub u v) eqn:L1; try done. cbn in Lub. inversion Lub.
    cbn. fold level_fun. rewrite level_fun_app.
    specialize (IHv _ _ L1). lia.
  - destruct u; try done. inversion Lub; done.
    inversion Lub. 
    destruct (compatible_fun l0 l); try done.
    inversion H0; subst. 
    cbn. fold level_fun.
    rewrite level_fun_app. lia.
Qed.
*)


(*
*)

Lemma level_app : forall f u w,
     app f u = Some w -> level w <= level_fun f.
Proof.
    move=> f.
    induction f as [|[ui vi]f].
    - cbn. move=> u w h. inversion h. subst. cbn. reflexivity.
    - move=> u w. rewrite app_spec. cbn. rewrite <- app_spec.
      move=> h. 
      destruct (compatible ui u && le ui u) eqn:h1.
      destruct (app f u) eqn:h2; try done.
      + have ih: level e <= level_fun f. eauto. 
        apply level_lub in h. rewrite <- h. lia.
      + eapply IHf in h. lia.
Qed.


Fixpoint level_le u v (L : le u v) {struct u} : 
  level u <= level v.
Proof.
  have level_fun_le : forall f g, 
      le_fun f g -> 
      level_fun f <= level_fun g.
  { induction f as [|[ui vi]f].
    cbn. lia.
    move=> g h.
    rewrite le_fun_cons in h.
    cbn.
    destruct (app g ui) eqn:h1; try done.
    move: h => /andP [Lvi Lf].
    specialize (IHf _ Lf).
    move: (level_le vi e Lvi) => h2.
    specialize (level_app h1).
    lia. 
  } 
  all: destruct u eqn:Eu.
  all: cbn.
  all: fold level_fun.
  all: try lia.
  - destruct v; try done. cbn in L.
    destruct (n =? n0) eqn:E; try done. 
    cbn. rewrite Nat.eqb_eq in E. subst. done.
  - destruct v; try done. cbn in L.
    cbn. 
    eapply level_le; eauto.
  - destruct v; try done.
    rewrite le_tpi in L.
    move: L => /andP [h1 h2].
    cbn. fold level_fun.
    eapply level_le in h1.
    eapply level_fun_le in h2.
    lia.
  - destruct v; try done.
    rewrite le_abs in L.
    eapply level_fun_le; auto.
(* Termination *)
Admitted.




(* -------------------------------------------------------------- *)

(** well typed elements:  (finMem) *)
Inductive wt : elt -> elt -> Prop := 
  | wt_bot a :
    valid a ->
    wt bot a 

  | wt_tuniv i j :
    (i < j)%nat -> 
    wt (tuniv i) (tuniv j)

  | wt_tnat j :
    wt tnat (tuniv j)

  | wt_zero : 
    wt zero tnat

  | wt_succ u : 
    wt u tnat -> 
    wt (succ u) tnat

  | wt_tpi a g j :
    (forall ui vi, 
        List.In (ui,vi) g -> wt ui a) -> 
    (forall ui vi, 
        List.In (ui,vi) g -> wt vi (tuniv j)) ->
    wt a (tuniv j) -> 
    (valid (tpi a g)) ->
    wt (tpi a g) (tuniv j)

  | wt_abs a f g :  
    (forall ui vi w, 
        List.In (ui,vi) f -> app g ui = Some w -> wt ui a) ->
    (forall ui vi w, 
        List.In (ui,vi) f -> app g ui = Some w -> wt vi w) ->
    (* make sure both tm and type are valid *)
    (valid (abs f)) ->
    (valid (tpi a g)) -> 
    wt (abs f) (tpi a g)
  .

Lemma wt_valid_tm u a : wt u a -> valid u.
induction 1; eauto.
Qed.

Lemma wt_valid_ty u a : wt u a -> valid a.
induction 1; eauto.
Qed.

Hint Resolve wt_valid_tm wt_valid_ty : valid.

(*
Lemma 2 
- If u : a and a <= b, then u : b.

- If u : a, v : a, and u and v are compatible, then u ∨ v : a
*)


Lemma wt_le u a : 
  wt u a -> forall b, le a b -> valid b -> wt u b.
Proof.
  move=> h.
  induction h; move=> b LE Vb.
  - eapply wt_bot; eauto. 
  - apply le_tuniv_inv in LE. subst. 
    eapply wt_tuniv; eauto.
  - apply le_tuniv_inv in LE. subst.
    eapply wt_tnat; eauto.
  - apply le_tnat_inv in LE. subst.
    eapply wt_zero; eauto.
  - eapply le_tnat_inv in LE. subst.
    eapply wt_succ; eauto.
  - apply le_tuniv_inv in LE. subst.    
    eapply wt_tpi; eauto.
  - destruct (le_tpi_inv LE) as [w [g1 [-> [LEu LEf]]]].
    move: Vb => /andP [Vw Vg1];
    fold valid in Vw, Vg1.
    fold (valid_fun g1) in Vg1.
    eapply wt_abs; eauto.
    + move=> ui vi w1i Inf A1i.
      have Vui: valid ui.
      { 
        cbn in H3.
        move: H3 => /andP [_ /forallb_forall h3].
        specialize (h3 _ Inf). move: h3 => /andP [Vui Vvi].
        done.        
      } 

      move: H4 => /andP [_ /orP [h4|h4]];
      fold valid valid_fun in h4.
      -- move: (valid_app_exists h4 Vui) => [wi [Ai Vwi]].
         move: Vg1 => /orP [Vg1|Ng1].
         move: (le_fun_mono h4 Vg1 LEf Vui Ai A1i) => LFM.
         eapply H0; eauto.
         (* g1 is nil *)
         destruct g1; try done.
         rewrite app_nil_eq in A1i. inversion A1i; subst.
         exfalso. eapply valid_fun_not_le_fun_nil; eauto.
      -- (* g is nil *)
         destruct g; try done.
         specialize (H0 ui vi bot Inf (app_nil_eq _)).
         eapply H0; eauto.

    + move=> ui vi w1i Inf A1i.
      have Vui: valid ui. 
      { move: H3 => /andP [_ /forallb_forall h3]; fold valid in h3.
        specialize (h3 _ Inf). move: h3 => /andP [Vui Vvi].
        done.
      }
      move: H4 => /andP [Va /orP [Vg|Vg]]; fold valid in Va, Vg.
      move: (valid_app_exists Vg Vui) => [wi [Ai Vwi]].
      move: Vg1 => /orP [Vg1|Vg1].
      move: (le_fun_mono Vg Vg1 LEf Vui Ai A1i) => LFM.
      eapply H2; eauto.
      eapply (valid_app Vg1 Vui); eauto.
      (* g1 is nil, g is not nil *)
      destruct g1; try done.
      exfalso. eapply valid_fun_not_le_fun_nil; eauto.
      (* g is nil, try cases for g1 *)
      destruct g; try done.
      move: Vg1 => /orP [Vg1|Vg1].
      (* g1 is non nil, and g is nil *)
      specialize (H2 _ _ bot Inf (app_nil_eq _)).
      eapply H2; eauto. eapply le_bot.
      eapply (valid_app (u:= ui)); eauto.
      (* both nil *)
      destruct g1; try done.
      rewrite app_nil_eq in A1i. inversion A1i.
      eapply H1; eauto.
    + apply /andP. fold valid (valid_fun g1).
      split; auto.
Qed. 

Lemma wt_lub u a : 
  wt u a -> (forall v w, wt v a -> lub u v = Some w -> 
                   wt w a).
Proof.
  move=> h. induction h.
  all: move=> v w Wtv LUB.
  all: inversion LUB; subst; try done.
  all: destruct v; try done.
  all: try solve [cbn in LUB; inversion LUB; 
                  subst; econstructor; eauto].
  - destruct (i =? n) eqn:EQ; try done.
    inversion H1. 
    eapply wt_tuniv. done.
  - destruct (lub u v) eqn:EQ; try done.
    cbn in H0. inversion H0. subst.
    inversion Wtv; subst.
    eapply wt_succ; eauto.
  - (* u = tpi a g, v=tpi v l *)
    destruct (compatible_fun g l) eqn:C1; try done.
    destruct (lub a v) eqn:L1; try done.
    inversion H5. clear H5.
    (* e = lub a v *)
    inversion Wtv; subst. clear Wtv.
    have Va : valid a. eauto with valid.
    have Vv : valid v. eauto with valid.
    have Ve : valid e. eauto with valid.
    eapply wt_tpi; eauto.
    + move=> ui vi InApp.
      destruct (in_app_or _ _ _ InApp) as [Ing|Inl].
      ++ (* tuple is in the original list *) 
         specialize (H0 _ _ Ing). 
         eapply wt_le; eauto.
         eapply le_lub_left; eauto.
         eapply lub_compatible; eauto.
      ++ (* tuple is in v *)
        specialize (H9 _ _ Inl). 
        eapply wt_le; eauto.
        eapply le_lub_right; eauto.
        eapply lub_compatible; eauto.
    + move=> ui vi InApp.
      destruct (in_app_or _ _ _ InApp) as [Ing|Inl]; eauto.
    + apply /andP. fold valid (valid_fun (g ++ l)).
      split. eauto.
      move: H3 => /andP [_ /orP [Vg|Vg]].
      fold valid (valid_fun g) in Vg.
      all: move: H11 => /andP [_ /orP [Vl|Vl]];
           fold valid (valid_fun l) in Vl.
      all: apply /orP.
      ++ left. eapply valid_append; eauto.
      ++ destruct l; try done.
         rewrite app_nil_r. left; auto.
      ++ destruct g; try done.
         cbn. left; auto.
      ++ destruct l; destruct g; try done.
         cbn. right; done.
  - (* u = abs f, v = abs l *)
    cbn in LUB.
    destruct (compatible_fun f l) eqn:C1; try done.
    inversion LUB; subst w; clear LUB.
    inversion Wtv as [| | | | | |a2 l2 g2 Hui2 Hvi2 Vabs2 Vtpi2]; subst;
      clear Wtv.
    have Vf : valid_fun f by cbn in H1.
    have Vl : valid_fun l by cbn in Vabs2.
    have Vfl : valid_fun (f ++ l) by eapply valid_append; eauto.
    eapply wt_abs; eauto.
    + move=> ui vi wi Inapp A.
      destruct (in_app_or _ _ _ Inapp) as [Inf|Inl]; eauto.
    + move=> ui vi wi Inapp A.
      destruct (in_app_or _ _ _ Inapp) as [Inf|Inl]; eauto.
Qed.

(* Corollary 2 If w : Πaf and u : a, then w(u) : f (u). *)

Lemma wt_abs_pred u v w b f :
  wt (abs ((u,v)::w)) (tpi b f) -> ~~is_nil w ->
  wt (abs w) (tpi b f).
Proof.
  move=> WT Nw. inversion WT. subst.
  move: H5 => /andP [Vb Vf]. fold valid in Vb , Vf.
  fold (valid_fun f) in Vf.
  move: (valid_fun_tail H4 Nw) => Vt.
  move: (valid_fun_head H4) => Vh.
    eapply wt_abs; eauto.
    + move=> uj vj wj Inj.
      eapply (H2 uj vj wj ltac:(right;eauto)).
    + move=> uj vj wj Inj.
      eapply (H3 uj vj wj ltac:(right;eauto)).
    + eapply wt_valid_ty; eauto.
Qed.

(* Helper: extract app f u and its validity when valid (tpi a f) holds. *)
Lemma app_tpi_valid a f u :
  valid (tpi a f) -> valid u ->
  forall t, app f u = Some t -> valid t.
Proof.
  move=> V Vu t A.
  cbn in V. move: V => /andP [_ /orP [Vf|Nf]].
  - fold (valid_fun f) in Vf. eapply valid_app; eauto.
  - destruct f; try done. cbn in A. inversion A. done.
Qed.

(* Helper: existence of app f u when valid (tpi a f) holds. *)
Lemma app_tpi_exists a f u :
  valid (tpi a f) -> valid u ->
  exists t, app f u = Some t /\ valid t.
Proof.
  move=> V Vu.
  cbn in V. move: V => /andP [_ /orP [Vf|Nf]].
  - fold (valid_fun f) in Vf. eapply valid_app_exists; eauto.
  - destruct f; try done. exists bot. cbn. auto.
Qed.

Lemma wt_app w a f :
  wt (abs w) (tpi a f) ->
  forall u r t, wt u a -> app w u = Some r -> app f u = Some t -> wt r t.
Proof.
  induction w as [|[ui vi] w'].
  - (* w = nil: app nil u = Some bot, so r = bot *)
    move=> WT u r t WTu A1 A2.
    rewrite app_nil_eq in A1. inversion A1. subst r.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vu : valid u by eauto with valid.
    have Vt : valid t by eapply app_tpi_valid; eauto.
    eapply wt_bot; eauto.
  - move=> WT u r t WTu A1 A2.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi a f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vw : valid_fun ((ui,vi) :: w') by done.
    have Vt : valid t. { eapply (app_tpi_valid Vtpi Vu A2). }
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    (* Extract per-entry typing info from WT *)
    inversion WT as [| | | | | |aX wX fX HuiAll HviAll VabsX VtpiX EwX EafX]; subst.
    (* HviAll: forall ui' vi' w0, In (ui',vi') ((ui,vi)::w') -> app f ui' = Some w0 -> wt vi' w0 *)
    (* Get app w' u = Some r' *)
    have [r' [Ar' Vr']] : exists r', app w' u = Some r' /\ valid r'.
    { destruct (~~ is_nil w') eqn:Nw.
      { eapply valid_app_exists; eauto using valid_fun_tail. }
      destruct w'; try done. exists bot; cbn; auto. }
    rewrite app_spec in A1. cbn in A1. rewrite <- app_spec in A1.
    rewrite Ar' in A1.
    (* r' is well-typed at t: either by IH (w' non-nil with wt_abs_pred) or r' = bot *)
    have WTr' : wt r' t.
    { destruct (~~ is_nil w') eqn:Nw.
      { have WTw' : wt (abs w') (tpi a f) by eapply wt_abs_pred; eauto.
        eapply IHw'; eauto. }
      destruct w'; try done. cbn in Ar'. inversion Ar'. subst r'.
      eapply wt_bot; eauto. }
    destruct (compatible ui u && le ui u) eqn:EQui.
    + (* ui compatible with u and ui <= u: r = lub vi r' *)
      move: EQui => /andP [Cui LEui].
      (* Get wi = app f ui and show wt vi wi *)
      have [wi [Awi Vwi]] : exists wi, app f ui = Some wi /\ valid wi
        by eapply app_tpi_exists; eauto.
      have WTvi_wi : wt vi wi by eapply HviAll; [left; reflexivity | eauto].
      (* wi <= t by monotonicity of app f (or trivially if f is nil) *)
      have LEwit : le wi t.
      { cbn in Vtpi. move: Vtpi => /andP [_ /orP [Vf|Nf]].
        { fold (valid_fun f) in Vf.
          have [_ LE] : compatible wi t /\ le wi t.
          { eapply le_fun_mono_arg with (h := f) (u1 := ui) (u2 := u); eauto. }
          exact LE. }
        destruct f; try done. cbn in Awi, A2.
        inversion Awi. inversion A2. subst. eapply le_bot. }
      have WTvi_t : wt vi t by eapply wt_le; eauto.
      eapply wt_lub with (u := vi) (v := r'); eauto.
    + (* no contribution from (ui,vi): r = r' *)
      inversion A1. subst r. done.
Qed.


(*
Lemma 3 If Πaf : Uk and f = (u1 → t1,...,un → tn), then ui : a and f (ui) : Uk. 

This version is not the same as it doesn't say anything 
intensional about f.

*)

Lemma lemma3_1 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi, In (ui,vi) f -> wt ui a.
Proof.
  intros.
  inversion H. eauto.
Qed.


Lemma wt_instantiate a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui w, wt ui a -> app f ui = Some w -> wt w (tuniv k).
Proof.
  induction f as [|[u v]f].
  all: move=> WT; inversion WT; subst; clear WT.
  all: move=> ui vi w. 
  - rewrite app_nil_eq. move=> EQ. inversion EQ. subst.
    eapply wt_bot; eauto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (compatible u ui && le u ui) eqn:EQ.
    + move=> LUB. destruct (app f ui) eqn:APP; try done.
      cbn [valid] in H5. fold (valid_fun ((u,v)::f)) in H5.
      move: H5 => /andP [Va /orP [Vuf|h]]; try done.
      have WTv : wt v (tuniv k). 
      { eapply H3; eauto. left. reflexivity. } 
      have WT: wt (tpi a f) (tuniv k).
      { destruct (~~ is_nil f) eqn:Nf.
        - eapply wt_tpi; eauto.
        move=> uj vj Infj. eapply H2; eauto. right; eauto.
        move=> uj vj Infj. eapply H3; eauto. right; eauto.
        apply /andP. fold valid. fold (valid_fun f).
        split; auto. apply /orP. left. eauto with valid.
      - destruct f; try done.
        eapply wt_tpi; eauto; try done.
        apply /andP. auto. 
    } 
    specialize (IHf WT).
    eapply wt_lub in LUB; eauto.
    + move=> APP.
      eapply IHf; eauto.
      eapply wt_tpi; eauto.
      move=> uj vj Infj. eapply H2; eauto. right; eauto.
      move=> uj vj Infj. eapply H3; eauto. right; eauto.
      move: H5 => /andP [Va Vf]. fold valid in Va, Vf.
      apply /andP. fold valid. split; auto.      
      move: Vf => /orP [h1|h1]; try done.
      fold (valid_fun f).
      destruct (is_nil f) eqn:Nf. 
      apply /orP. right. auto. 
      apply /orP. left. apply valid_fun_tail in h1; auto. 
      rewrite Nf. done.
Qed.

Lemma lemma3_2 a f k : 
  wt (tpi a f) (tuniv k) -> 
  forall ui vi w, In (ui,vi) f -> app f ui = Some w -> wt w (tuniv k).
Proof.
  intros.
  inversion H. subst.
  eapply wt_instantiate; eauto.
Qed.


(*
Lemma 4:

If w : Πaf and w = (u1 → t1,...,un → tn), then ui : a
and w(ui) : f (ui).
*)

Lemma lemma4_1 w a f :
  wt (abs w) (tpi a f) ->
  forall ui vi, In (ui, vi) w -> wt ui a.
Proof.
  move=> WT ui vi In.
  inversion WT as [| | | | | |aX wX fX HuiAll HviAll Vabs Vtpi]; subst.
  have Vw : valid_fun w by exact Vabs.
  have Vui : valid ui.
  { move: (valid_fun_subterms_prop Vw In) => [Vu _]. done. }
  destruct (app_tpi_exists Vtpi Vui) as [t [At Vt]].
  eapply HuiAll; eauto.
Qed.

Lemma lemma4_2 w a f :
  wt (abs w) (tpi a f) ->
  forall ui vi r t, In (ui, vi) w ->
           app w ui = Some r -> app f ui = Some t -> wt r t.
Proof.
  move=> WT ui vi r t In Aw Af.
  eapply wt_app; eauto.
  eapply lemma4_1; eauto.
Qed.



                                       
(*
 if u : a then lv(u) <= lv(a) and if u : Uk then lv(u) < k 
*)

Lemma wt_level u a :
  wt u a -> level u <= level a.
Proof.
  move=> h. 
  induction h.
  7: { 
    move: H H0 H1 H2.
    induction f as [|[ui vi]f].
    + cbn in *. move=> _ _ _ _. lia.
    + move=> Wta La Wtb Lb.
    cbn. fold level_fun. 
    have IH: level (abs f) <= level (tpi a g).
    { destruct (~~ is_nil f) eqn:Nf.
      + eapply valid_fun_tail in H3; eauto.
        { eapply IHf; eauto.
          - intros. eapply Wta. right. eauto. eauto.
          - intros. eapply La. right. eauto. eauto.
          - intros. eapply Wtb. right. eauto. eauto.
          - intros. eapply Lb. right. eauto. eauto.
        }     
      + destruct f; try done. cbn. lia.
    }        
    cbn in IH. fold level_fun in IH.
    move: H4 => /andP[ Va /orP [Vg|Ng]].
    fold valid in *. 
    - move: (valid_fun_head H3) => Vh.
      move: (key_valid Vh) => Vui.
      move: (val_valid Vh) => Vvi.
      move: (valid_app_exists Vg Vui) => [w [EQ Vw]].
      specialize (@Wta ui vi w ltac:(left;auto) EQ).
      specialize (@La ui vi w ltac:(left;auto) EQ).
      specialize (@Wtb ui vi w ltac:(left;auto) EQ).
      specialize (@Lb ui vi w ltac:(left;auto) EQ).
      eapply level_app in EQ.
      lia.
    -       
Admitted.


(*
Lemma 5 If w : Π b f and b <= a, then for any u : a there exists v : b such that v <= u and w(u) = w(v).

Proof We write w = (u1 → l1,...,un → ln) with ui : b and 
   li : f (ui). We then
have w(u) = w(v) 
   with v = ∨{ui | ui <= u} and v : b by Lemma 2.

*)

(* le u v (for valid v) implies compatible u v. *)
Lemma le_compatible u v : valid v -> le u v -> compatible u v.
Proof.
  move=> Vv LE.
  eapply comp_down; eauto. eapply compatible_refl; eauto.
Qed.

(* Stronger form: for any x with le v x and le x u, app w u = app w x. *)
Lemma app_down_strong w b f :
  wt (abs w) (tpi b f) -> forall u a,
      le b a ->
      wt u a ->
      exists v, wt v b /\ le v u /\
        (forall x, valid x -> le v x -> le x u -> app w u = app w x).
Proof.
  induction w as [|[ui vi] w'].
  - move=> WT. inversion WT. done.
  - move=> WT u a LE WTu.
    have Vu : valid u by eauto with valid.
    have Vtpi : valid (tpi b f) by eauto with valid.
    have Vabs : valid (abs ((ui,vi) :: w')) by eauto with valid.
    have Vb : valid b.
    { cbn in Vtpi. move: Vtpi => /andP [? _]. done. }
    have Vw : valid_fun ((ui,vi) :: w') by done.
    have Vui : valid ui by eapply key_valid; eauto using valid_fun_head.
    have Vvi : valid vi by eapply val_valid; eauto using valid_fun_head.
    have [wi [Awi Vwi]] : exists wi, app f ui = Some wi /\ valid wi
      by eapply app_tpi_exists; eauto.
    inversion WT as [| | | | | |aX wX fX Hui2 Hvi2 VabsX VtpiX]; subst.
    have WTui_b : wt ui b by eapply Hui2; [left; reflexivity | exact Awi].
    destruct (~~ is_nil w') eqn:Nw.
    + (* w' non-nil: use IH *)
      have WTw' : wt (abs w') (tpi b f) by eapply wt_abs_pred; eauto.
      destruct (IHw' WTw' u a LE WTu) as [v' [WTv' [LEv' IH2]]].
      have Vv' : valid v' by eapply wt_valid_tm; eauto.
      destruct (le ui u) eqn:LEui.
      * (* le ui u = true *)
        have Cui : compatible ui u by eapply le_compatible; eauto.
        have Cuiv' : compatible ui v'.
        { apply compatible_sym. eapply comp_down; eauto.
          apply compatible_sym; eauto. }
        destruct (compatible_lub_exists Cuiv') as [v_new EQv].
        have Vv_new : valid v_new. { eapply (valid_lub Vui Vv' EQv). }
        have LE_uivn : le ui v_new. { eapply (le_lub_left Cuiv' EQv Vui Vv'). }
        have LE_vvn : le v' v_new. { eapply (le_lub_right Cuiv' EQv Vui Vv'). }
        have LE_vnu : le v_new u. { eapply (@le_sup_lub ui v' v_new u LEui LEv' EQv). }
        have WT_vnew : wt v_new b. { eapply wt_lub; [exact WTui_b | exact WTv' | exact EQv]. }
        exists v_new. split; [|split]; eauto.
        move=> x Vx LE_vnx LE_xu.
        have LE_uix : le ui x by eapply le_trans with (v := v_new); eauto.
        have LE_v'x : le v' x by eapply le_trans with (v := v_new); eauto.
        have Cuix : compatible ui x by eapply le_compatible; eauto.
        have App_eq : app w' u = app w' x by apply IH2; eauto.
        rewrite app_spec. cbn. rewrite <- app_spec.
        rewrite Cui LEui Cuix LE_uix /=.
        rewrite App_eq. reflexivity.
      * (* le ui u = false *)
        exists v'. split; [|split]; eauto.
        move=> x Vx LE_v'x LE_xu.
        have LE_uix : le ui x = false.
        { destruct (le ui x) eqn:E; try reflexivity.
          have Luiu : le ui u by eapply le_trans with (v := x); eauto.
          rewrite LEui in Luiu. done. }
        have App_eq : app w' u = app w' x by apply IH2; eauto.
        rewrite app_spec. cbn. rewrite <- app_spec.
        rewrite LEui LE_uix !Bool.andb_false_r /=.
        exact App_eq.
    + (* w' nil *)
      destruct w'; try done.
      destruct (le ui u) eqn:LEui.
      * (* le ui u = true *)
        have Cui : compatible ui u by eapply le_compatible; eauto.
        exists ui. split; [|split]; eauto.
        move=> x Vx LE_uix LE_xu.
        have Cuix : compatible ui x by eapply le_compatible; eauto.
        rewrite app_spec. cbn.
        rewrite Cui LEui Cuix LE_uix /=.
        rewrite !lub_bot_r. reflexivity.
      * (* le ui u = false *)
        exists bot. split; [|split].
        -- eapply wt_bot; eauto.
        -- eapply le_bot.
        -- move=> x Vx LE_botx LE_xu.
           have LE_uix : le ui x = false.
           { destruct (le ui x) eqn:E; try reflexivity.
             have Luiu : le ui u by eapply le_trans with (v := x); eauto.
             rewrite LEui in Luiu. done. }
           rewrite app_spec. cbn.
           rewrite LEui LE_uix !Bool.andb_false_r /=.
           reflexivity.
Qed.

Lemma app_down w b f :
  wt (abs w) (tpi b f) -> forall u a,
      le b a ->
      wt u a -> exists v, wt v b /\ le v u /\ app w u = app w v.
Proof.
  move=> WT u a LE WTu.
  destruct (app_down_strong WT LE WTu) as [v [WTv [LEv HStr]]].
  have Vv : valid v by eapply wt_valid_tm; eauto.
  exists v. split; [|split]; eauto.
  eapply HStr; eauto. eapply le_refl; eauto.
Qed.


Inductive is_type : elt -> Prop :=
  | is_bot : is_type bot
  | is_tuniv i : is_type (tuniv i)
  | is_tnat : is_type tnat
  | is_tpi a f :
    valid (tpi a f) ->
    is_type a ->
    (forall u v, In (u,v) f -> wt u a) ->
    (forall u v, In (u,v) f -> is_type v) ->
    is_type (tpi a f).

Lemma is_type_valid a : is_type a -> valid a.
Proof.
  induction 1; cbn; auto.
Qed.

Hint Resolve is_type_valid : valid.

Lemma valid_tpi_inv a f :
  valid (tpi a f) -> valid a /\ (valid_fun f \/ is_nil f).
Proof.
  move=> V. cbn in V. move: V => /andP [Va Vf].
  split; [exact Va|].
  move: Vf => /orP [Vf|Nf]; [left|right]; done.
Qed.

Lemma valid_tpi_intro a f :
  valid a -> (valid_fun f \/ is_nil f) -> valid (tpi a f).
Proof.
  move=> Va H. cbn. apply /andP. split; [exact Va|].
  apply /orP. destruct H as [Vf|Nf]; [left|right]; done.
Qed.

(* 
If a : Uj , then a type. 
If a type, b type, and a,b are compatible, then a ∨ b type. 
If Π a (u1 → t1,...,un → tn) type and u1 → t1,...,un → tn is a
minimal description, then ui : a and ti type.
*)

Lemma wt_is_type a i :
  wt a (tuniv i) -> is_type a.
Proof.
  move=> h.
  remember (tuniv i) as t eqn:Ht.
  move: i Ht.
  induction h; move=> k Heq; try discriminate.
  - constructor.
  - constructor.
  - constructor.
  - inversion Heq; subst j.
    apply is_tpi.
    + eauto.
    + eauto.
    + eauto.
    + eauto.
Qed.

Lemma is_type_lub a b :
  is_type a -> is_type b -> forall c, lub a b = Some c -> is_type c.
Proof.
  move=> Ta. move: b.
  induction Ta as [ | i | | a0 f0 Va Ta0 IHa0 Hwt_f0 Hist_f0 IH_f0].
  - move=> b Tb c L. cbn in L. inversion L; subst. exact Tb.
  - move=> b Tb c L.
    inversion Tb; subst; cbn in L; try discriminate.
    + inversion L; subst. constructor.
    + destruct (i =? i0) eqn:E; try discriminate.
      inversion L; subst. constructor.
  - move=> b Tb c L.
    inversion Tb; subst; cbn in L; try discriminate.
    + inversion L; subst. constructor.
    + inversion L; subst. constructor.
  - move=> b Tb c L.
    inversion Tb as [| | | a1 f1 Va1_tpi Ta1 Hwt_f1 Hist_f1];
      subst; cbn in L; try discriminate.
    + inversion L; subst. eapply is_tpi; eauto.
    + destruct (compatible_fun f0 f1) eqn:CF; try discriminate.
      destruct (lub a0 a1) eqn:La; try discriminate.
      cbn in L. inversion L; subst c; clear L.
      have Va0 : valid a0 by eauto using is_type_valid.
      have Va1 : valid a1 by eauto using is_type_valid.
      have Ca : compatible a0 a1 by eapply lub_compatible; eauto.
      have Ve : valid e by exact: (valid_lub Va0 Va1 La).
      have LEae : le a0 e by exact: (le_lub_left Ca La Va0 Va1).
      have LEbe : le a1 e by exact: (le_lub_right Ca La Va0 Va1).
      have Te : is_type e by eapply IHa0; eauto.
      have Vres : valid (tpi e (f0 ++ f1)).
      { cbn. apply /andP. split; auto.
        cbn in Va, Va1_tpi.
        move: Va => /andP [_ VD0].
        move: Va1_tpi => /andP [_ VD1].
        move: VD0 => /orP [Vf0|Nf0].
        - move: VD1 => /orP [Vf1|Nf1].
          + apply /orP. left. eapply valid_append; eauto.
          + destruct f1; try done. rewrite app_nil_r.
            apply /orP. left. exact Vf0.
        - move: VD1 => /orP [Vf1|Nf1].
          + destruct f0; try done. cbn. apply /orP. left. exact Vf1.
          + destruct f0; destruct f1; done. }
      eapply is_tpi; eauto.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply wt_le; eauto.
        -- eapply wt_le; eauto.
      * move=> u v Inv. apply in_app_or in Inv. destruct Inv as [Inv|Inv].
        -- eapply Hist_f0; eauto.
        -- eapply Hist_f1; eauto.
Qed.

Lemma is_type_dom a f :
  is_type (tpi a f) -> is_type a.
Proof.
  move=> H. inversion H. done.
Qed.

Lemma is_type_cod a f :
  is_type (tpi a f) -> forall ui w, wt ui a -> app f ui = Some w -> is_type w.
Proof.
  induction f as [|[u v] f' IHf'].
  - move=> _ ui w _ A.
    rewrite app_nil_eq in A. inversion A; subst. constructor.
  - move=> Ttpi ui w Wtui A.
    inversion Ttpi as [| | |a2 f2 Vtpi Ta Hwt Hist]; subst.
    have Tf' : is_type (tpi a f').
    { have [Va Vu] := valid_tpi_inv Vtpi.
      have Vtf' : valid (tpi a f').
      { apply valid_tpi_intro; [exact Va|].
        destruct f' as [|[u2 v2] f''];
          [right; done|left; destruct Vu as [Vf|Nf]; [|done]; eapply valid_fun_tail; eauto]. }
      apply is_tpi; auto;
        move=> u' v' In'; [eapply Hwt|eapply Hist]; right; eauto. }
    rewrite app_spec in A. cbn in A. rewrite <- app_spec in A.
    destruct (compatible u ui && le u ui) eqn:E.
    + destruct (app f' ui) as [t|] eqn:Afp; try discriminate.
      have Tv : is_type v by eapply Hist; left; reflexivity.
      have Tt : is_type t by eapply IHf'; eauto.
      eapply is_type_lub; [exact Tv|exact Tt|exact A].
    + eapply IHf'; eauto.
Qed.
