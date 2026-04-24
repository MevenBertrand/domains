
From Stdlib Require Import Relations List Program
     ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import smpl.Smpl.

From Stdlib Require Import Classes.RelationClasses Classes.Morphisms Lia Arith.


Require Import utils.all.
Require Import categories.all.
Require Import preord.
Require Import categories.
Require Import sets.
Require Import finsets.
Require Import esets.
Require Import effective.
Require Import directed.

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

(* The level of an element is its maximum universe level *)

Fixpoint level (u : elt) : nat :=
  let fix level_fun f :=
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (level ui) (level vi)) (level_fun tl)
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
          max (max (level ui) (level vi)) (level_fun tl)
 end.


(* Compatible elements have the same universe level???
   No, this is not true b/c bot is compatible 
   with any term.
*)

Lemma compatible_level u v :
  compatible u v -> level u = level v.
Abort.

(* also not true because non-minimal functions can include high-level 
   arguments in their domains *)
Lemma level_fun_respects
  u (Vu : valid_fun u) v (Vv : valid_fun v) :
  eqb_fun u v -> 
  level_fun u = level_fun v.
Proof.
Abort.


(** well typed elements: raw version  (finMem) *)
(* TODO: make this relation imply validity (coherence) *)

(*
Fixpoint wt_check (u : elt) : elt option := 
  match u with 
  | bot     => Some (tuniv 0)
  | tuniv i => Some (tuniv (S i))
  | tnat    => Some (tuniv 0)
  | zero    => Some tnat
  | succ v  => match (wt a) with 
             | Some tnat => Some tnat
             | _ => None
             end
  | tpi b g => 
      match wt b with 
      | Some (tuniv bj) => 
          List.map (fun '(ui,vi) => 
            match (app g ui) with 
            | Some w => match (wt ui) with 
                       | Some tui => sub b tui
                       | None =>                 
     

match a with 
             | tuniv j => 
                 wt b (tuniv j) &&
                 forallb (fun '(ui, vi) => wt ui b && wt vi (tuniv j)) g &&
                 valid_fun g
             | _ => false 
             end
  | tabs f => match a with 
             | tpi b g => 
                 forallb (fun '(ui,vi) => 
                    wt ui a &&
                    match app g ui with 
                    | Some w => wt vi w
                    | None => false
                    end) g &&
                    valid_fun f &&
                    valid_fun g
             | _ => false
             end
  end.
  

Fixpoint wt (u : elt) (a : elt) : bool := 
  match u with 
  | bot => wt a (tuniv j)
  | tuniv i => match a with 
              | tuniv j => i <? j
              | _ => false
              end
  | tnat => match a with 
             | tuniv j => true
             | _ => false
           end
  | zero => match a with 
             | tnat => true
             | _ => false
           end
  | succ v => match a with 
             | tnat => wt v tnat
             | _ => false
             end
  | tpi b g => match a with 
             | tuniv j => 
                 wt b (tuniv j) &&
                 forallb (fun '(ui, vi) => wt ui b && wt vi (tuniv j)) g &&
                 valid_fun g
             | _ => false 
             end
  | tabs f => match a with 
             | tpi b g => 
                 forallb (fun '(ui,vi) => 
                    wt ui a &&
                    match app g ui with 
                    | Some w => wt vi w
                    | None => false
                    end) g &&
                    valid_fun f &&
                    valid_fun g
             | _ => false
             end
  end. *)

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
Lemma 3 If Πaf : Uk and f = (u1 → t1,...,un → tn) is minimal, then ui : a and f (ui) : Uk. 

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

If w : Πaf and w = (u1 → t1,...,un → tn) is minimal, then ui : a
and w(ui) : f (ui).
*)

Lemma lemma4_1 w a f : 
  wt (abs w) (tpi a f) -> 
  forall ui vi, In (ui, vi) w -> wt ui a.
Proof.
  move=> WT. inversion WT.
Admitted.

Lemma lemma4_2 w a f : 
  wt (abs w) (tpi a f) -> 
  forall ui vi r t, In (ui, vi) w ->
           app w ui = Some r -> app f ui = Some t -> wt r t.
Admitted.       

                                       
(*
 if u : a then lv(u) <= lv(a) and if u : Uk then lv(u) < k 
*)

Lemma wt_rk u a :
  wt u a -> level u <= level a.
Proof.
  move=> h. 
  induction h.
  7: { 
    cbn. fold level_fun.
Abort.


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
    is_type a -> 
    (forall u v, In (u,v) f -> wt u a) ->
    (forall u v, In (u,v) f -> is_type v) ->
    is_type (tpi a f).

(* 
If a : Uj , then a type. 
If a type, b type, and a,b are compatible, then a ∨ b type. 
If Π a (u1 → t1,...,un → tn) type and u1 → t1,...,un → tn is a
minimal description, then ui : a and ti type.
*)

Lemma wt_is_type a i : 
  wt a (tuniv i) -> is_type a.
Admitted.

Lemma is_type_lub a b :
  is_type a -> is_type b -> forall c, lub a b = Some c -> is_type c.
Admitted.

Lemma is_type_dom a f : 
  is_type (tpi a f) -> is_type a.
Admitted.

Lemma is_type_cod a f :
  is_type (tpi a f) -> forall ui w, wt ui a -> app f ui = Some w -> is_type w.
Admitted.
