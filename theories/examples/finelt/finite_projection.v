(* Finitary projection *)
(* cf. FinitaryProject.agda *)


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



(* if u has type a then return it else return bot *)
Fixpoint proj_tpi' (proj : elt -> elt -> elt) 
  (f : list (elt * elt)) 
  (a: elt) (b:elt)
   : list (elt * elt) := 
    match f with 
    | nil => nil 
    | cons (u,v) ps => 
        cons (proj u a, proj v b) (proj_tpi' proj ps a b)
    end.

Fixpoint proj_fun' (proj : elt -> elt -> elt)
  (g : list (elt * elt)) 
  (a : elt) (f : list (elt * elt)) 
  : list (elt * elt) := 
    match g with 
    | nil => nil 
    | cons (u,v) ps => 
        let x := proj u a  in
        let y := match app f x with 
                 | Some t => proj v t
                 | None => bot
                 end
        in
        cons (x, y) (proj_fun' proj ps a f)
    end.

Fixpoint proj' (k : nat) (u : elt) (a : elt) {struct k} : elt := 
  match a with 
  | bot => bot
  | tuniv i => match u with 
              | tnat => tnat
              | tuniv j => if (j <? i) then tuniv j else bot
              | tpi b f => 
                  match k with 
                  | S j => tpi (proj' j b (tuniv i))
                              (proj_tpi' (proj' j) f b (tuniv i))
                  | O   => tpi bot nil
                  end
              | _ => bot
              end
  | tpi a f => match u with 
              | abs g => match k with 
                  | S j => abs (proj_fun' (proj' j) g a f)
                  | O => bot
                        end
              | _ => bot
              end
  | tnat => match u with 
             | zero => zero
             | succ v => match k with 
                        | S j => succ (proj' j v tnat)
                        | O => bot
                        end
             | _ => bot
           end
  | _ => bot
  end
 .

Lemma rk_proj_enough : forall k u a, 
    rk u <= k -> 
    proj' k u a = proj' (rk u) u a.
Proof.
  elim /findom.strong_ind.
  move=> m ih.
  have ih_proj_tpi: forall f,
    forall k : nat,
    k < m -> forall a b, (rk_fun f) <= k -> 
            proj_tpi' (proj' k) f a b  = 
            proj_tpi' (proj' (rk_fun f)) f a b.
  { induction f as [|[u v]f].
    - intros. done.
    - intros k Lt a b. cbn.
      move=> Le.
      repeat rewrite ih; try lia.
      f_equal.
      repeat rewrite IHf; try lia. done.
  }
 have ih_proj_fun: forall g,
    forall k : nat,
    k < m -> forall a f, (rk_fun g) <= k -> 
            proj_fun' (proj' k) g a f = 
            proj_fun' (proj' (rk_fun g)) g a f.
  { induction g as [|[u v]g].
    - intros. done.
    - intros k Lt a f. cbn.
      move=> Le.
      repeat rewrite ih; try lia.
      f_equal. f_equal.
      destruct app; try done.
      repeat rewrite ih; try lia. done.
      repeat rewrite IHg; try lia. done.
  }
  move=> u a Le.
  destruct m.
  - destruct a; destruct u; cbn in *; auto.
    all: try lia.
  - destruct a eqn:Ea; destruct u eqn:Eu.
    all: try solve [cbn in *; auto].
    + (* a = tnat, u = succ e *) 
      cbn in *. f_equal.  
      rewrite ih; cbn; try lia.
      done.
    + (* u = tpi e l *)
      cbn in *. fold rk_fun in *.
      repeat rewrite ih; cbn; try lia.
      f_equal.
      repeat rewrite ih_proj_tpi; try lia.
      done.
    + (* u = abs l *)
      cbn in *. fold rk_fun in *.
      repeat rewrite ih_proj_fun; try lia.
      done.
Qed.

Lemma rk_proj_tpi_enough k f : 
  forall a b, (rk_fun f) <= k -> 
         proj_tpi' (proj' k) f a b  = 
           proj_tpi' (proj' (rk_fun f)) f a b.
Admitted.

Lemma rk_proj_fun_enough k g : 
  forall a f, (rk_fun g) <= k -> 
         proj_fun' (proj' k) g a f = 
           proj_fun' (proj' (rk_fun g)) g a f.
Proof.
Admitted.

Definition proj u : elt -> elt := proj' (rk u) u.
Definition proj_tpi f := proj_tpi' (proj' (rk_fun f)) f.
Definition proj_fun f := proj_fun' (proj' (rk_fun f)) f.

Lemma proj_bot_ty u : proj u bot = bot.
destruct u; try done.
Qed.

Lemma proj_bot_tm a : proj bot a = bot.
destruct a; try done.
Qed.

Lemma proj_tuniv i j : 
  proj (tuniv i) (tuniv j) = if i <? j then tuniv i else bot.
Proof.
  cbn. destruct j; try lia. done.
  destruct (i <=? j) eqn:LE; reflexivity.
Qed.

Lemma proj_tnat_tuniv j :
  proj tnat (tuniv j) = tnat.
Proof.
  reflexivity.
Qed.

Lemma proj_succ_tnat u : 
  proj (succ u) tnat = succ (proj u tnat).
Proof. 
  cbn. f_equal.
Qed.

Lemma proj_tpi_tuniv a f j  : 
  proj (tpi a f) (tuniv j) = 
    tpi (proj a (tuniv j)) (proj_tpi f a (tuniv j)). 
cbn. fold rk_fun. f_equal. rewrite rk_proj_enough. lia.
done.
rewrite rk_proj_tpi_enough. lia. done.
Qed.

Lemma proj_abs_tpi f a g :
  proj (abs f) (tpi a g) = abs (proj_fun f a g).
Proof.
  reflexivity.
Qed.

Lemma proj_forward a u : wt u a -> proj u a = u.
Proof.
  move=> h.
  induction h.
  all: try reflexivity.
  - rewrite proj_bot_tm. done.
  - rewrite proj_tuniv.  
    move: H => /Nat.ltb_spec0 H. rewrite H. done.
  - rewrite proj_succ_tnat. rewrite IHh. done.
  - rewrite proj_tpi_tuniv. rewrite IHh.
    f_equal.
    clear H H1 h H3 IHh.
    move: H0 H2.
    induction g as [|[u v]g].
    all: move=> Hui Hvi. cbn. done.
    move:(Hui u v ltac:(left; reflexivity)) => h1.
    move:(Hvi u v ltac:(left; reflexivity)) => h2.
    cbn.
    repeat rewrite rk_proj_enough; try lia.
    f_equal.
    fold (proj u). fold (proj v).
    rewrite h1. rewrite h2. done.
    rewrite rk_proj_tpi_enough. lia.
    fold (proj_tpi g). eapply IHg; eauto.
    move=> ui vi Ing. 
    eapply Hui; eauto. right; eauto.
    move=> ui vi Ing.
    eapply Hvi; eauto. right; eauto.
  - rewrite proj_abs_tpi. 
Admitted.


Lemma proj_backward u : forall a i , 
  valid u -> wt a (tuniv i) -> proj u a = u -> wt u a.
Proof.
  have LEMMA: forall k u, rk u <= k -> 
      forall a i , 
        valid u -> wt a (tuniv i) -> proj u a = u -> wt u a.             
  { 
    elim /findom.strong_ind. clear u.
    move=> m ih.
    move=> u RK a i Vu Wt EQ.
    dependent destruction u.
    - eapply wt_bot; eauto with valid.
    - destruct a; try done. 
      eapply wt_tnat; eauto.
    - destruct a; try done.
      rewrite  proj_tuniv in EQ. 
      destruct (n <? n0) eqn:LT; try done.
      inversion Wt. subst.
      eapply wt_tuniv; eauto. 
      rewrite Nat.ltb_lt in LT. done.
    - destruct a; try done.
      eapply wt_zero; eauto.
    - destruct a; try done.
      eapply wt_succ; eauto.
      rewrite proj_succ_tnat in EQ. inversion EQ. clear EQ.
      cbn in RK. rewrite H0.
      eapply (ih (rk u) ltac:(lia)); eauto.
    - admit.
    - admit.
  } 
  eapply LEMMA; eauto.
Admitted.
    
(* Lemma 2 *)
Lemma proj_valid a u : wt u a -> valid (proj u a).
move=> WT. rewrite proj_forward; eauto with valid.
Qed.

Hint Resolve proj_valid : valid.

(* Lemma 3 *)
(*
I don't understand the point here. *)
(*
Lemma proj_compatible u v a : 
  wt u a -> wt v a -> 
  compatible (proj u a) (proj v a).
move=> WTu WTv. repeat rewrite proj_forward; eauto.
*)
