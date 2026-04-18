(* Finite domain elements, *)

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


(* Library stuff *)

Lemma option_eta {A} (o:option A) : match o with Some x => Some x | None => None end = o.
destruct o; done.
Qed.

Lemma forall_ext {A} (f g : A -> bool) (l : list A)  :
  (forall x, List.In x l -> f x = g x) ->
  (forallb f l = forallb g l).
Proof.
  destruct forallb eqn:F1;  destruct (forallb g l) eqn:G1; firstorder.
  + move: F1 => /forallb_forall F1.
    move: (forallb_forall g l)=> [G2 G3].
    rewrite G1 in G3.
    symmetry.
    apply G3.
    intros x InX.
    rewrite <- H; eauto.
  + move: G1 => /forallb_forall G1.
    move: (forallb_forall f l)=> [F2 F3].
    rewrite F1 in F3.
    apply F3.
    intros x InX.
    rewrite -> H; eauto.
Qed.

Lemma list_max_In {A} f {l:list A} x k :  List.In x l -> List.list_max (map f l) <= k -> f x <= k.
Proof.
  induction l; cbn. done.
  intros h1 h2.
  destruct h1.
  - subst. lia.
  - eapply IHl; eauto.
    unfold List.list_max.
    lia.
Qed.

Lemma In_list_max {A} x {l :list A} {f : A -> nat} : In x l -> f x <= List.list_max (map f l).
Proof.
  induction l; cbn. done.
  move=> [h1|h2].
  subst. lia.
  apply IHl in h2.
  unfold List.list_max in h2.
  lia.
Qed.

Lemma andb_cong a b1 b2 : b1 = b2 -> a && b1 = a && b2.
intros ->. reflexivity.
Qed.

Lemma le_S_pred : forall m n, S m <= n -> exists j, n = S j /\ (m <= j).
    intros m n Le. 
    inversion Le; subst; eexists; split; eauto; try lia.
Qed.

(* If we fold with a monoid, then we can decompose appends into sub folds *)
Lemma fold_right_app : 
  forall {A : Type} (base : A) (op : A -> A -> A),
  (forall y : A, op base y = y) -> 
  (forall x y z : A, op x (op y z) = op (op x y) z) -> 
  forall l l' : list A, fold_right op base (l ++ l') = op (fold_right op base l) (fold_right op base l').
Proof.
  intros A base op idL assoc.
  induction l; move=> l'.
  cbn. rewrite idL. done.
  cbn. rewrite IHl.
  rewrite assoc. done.
Qed.


Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k)%nat -> P m) -> forall n, P n.
Proof. intro h. 
       induction n as [ n IHn ] using    
                        (well_founded_induction lt_wf). eauto. Qed.

Module Raw.

(* Finite elements: raw form.

   Functions are represented as finite mappings from 
   arguments to results.

 *)
Inductive elt := 
  | bot   : elt 
  | tnat  : elt 
  | tuniv : nat -> elt
  | zero  : elt
  | succ  : elt -> elt
  | tpi   : elt -> list (elt * elt) -> elt
  | abs   : list (elt * elt) -> elt.

Fixpoint eqb (u v : elt) : bool := 
  let fix fun_eqb f g := 
    match f , g with 
    | nil , nil => true
    | (u1 , v1) :: f , (u2 , v2) :: g => eqb u1 u2 && eqb v1 v2 && fun_eqb f g
    | _ , _ => false
    end in
  match u , v with 
  | bot , bot => true
  | tnat , tnat => true
  | tuniv k , tuniv l => k =? l
  | zero , zero => true 
  | succ u , succ v => eqb u v 
  | tpi a f , tpi b g => eqb a b && fun_eqb f g
  | abs f , abs g => fun_eqb f g
  | _ , _ => false
  end.

Fixpoint fun_eqb f g := 
 match f , g with 
    | nil , nil => true
    | (u1 , v1) :: f , (u2 , v2) :: g => eqb u1 u2 && eqb v1 v2 && fun_eqb f g
    | _ , _ => false
    end.

Fixpoint eqb_eq u {struct u} : forall v, eqb u v <-> u = v.
have fun_eqb_eq: forall f g, fun_eqb f g <-> f = g.
{ induction f.
  clear eqb_eq.
  move=> g. destruct g. cbn. done. cbn. done.
  move=> g. destruct g. destruct a as [u1 v1]. clear eqb_eq. cbn. done.
  destruct a as [u1 v1]. destruct p as [u2 v2]. cbn.
  move: (eqb_eq u1 u2) => [h1 h1'].
  move: (eqb_eq v1 v2) => [h2 h2'].
  move: (eqb_eq u1 u1) => [h4 h4'].
  move: (eqb_eq v1 v1) => [h5 h5'].
  clear eqb_eq.
  move: (IHf g) => [h3 h3'].
  split. move=> /andP [/andP [E2 E3] E1].
  repeat f_equal; eauto. 
  move=> h. inversion h. subst.
  rewrite h1'. auto. rewrite h2'. auto. rewrite h3'. auto. 
  reflexivity.
} 
move=> v. destruct u; destruct v.
all: cbn; try done. 
- split. 
  move=> h. apply (Nat.eqb_eq n n0) in h. f_equal. done.
  move=> h. inversion h. apply Nat.eqb_refl.
- split. rewrite eqb_eq. move=> ->. done.
  move: (eqb_eq u v) => h1.
  move: (eqb_eq u u) => h2.
  move=> h3. inversion h3. subst. rewrite h2. done.
- fold fun_eqb. split.
  move=> /andP [h1 h2]. rewrite eqb_eq in h1. rewrite fun_eqb_eq in h2. subst. done.
  move: (eqb_eq u v) => h1.
  move: (eqb_eq u u) => h2.
  move: (fun_eqb_eq l l0) => h3.
  move: (fun_eqb_eq l l) => h4.
  move=> h5. inversion h5. subst.
  apply /andP. rewrite h2. rewrite h4. auto.
- fold fun_eqb. split.
  move=> h. rewrite fun_eqb_eq in h. subst. done.
  move: (fun_eqb_eq l l0) => h3.
  move: (fun_eqb_eq l l) => h4.
  move=> h5. inversion h5. subst.
  rewrite h4. auto.
Admitted.

Lemma eqb_refl  : forall u, eqb u u. Admitted.
Lemma eqb_sym   : forall u v, eqb u v -> eqb v u. Admitted.
Lemma eqb_trans : forall u v w, eqb u v -> eqb v w -> eqb u w. Admitted.


(* structural recursion principle for elt *)
Definition elt_rect' :=
fun (P : elt -> Type) 
  (Pf : list (elt * elt) -> Type) 
  (f : P bot) (f0 : P tnat) (f1 : forall n : nat, P (tuniv n)) 
  (f2 : P zero) (f3 : forall e : elt, P e -> P (succ e))
  (f4 : forall e : elt, P e -> forall l : list (elt * elt), Pf l -> P (tpi e l))
  (f5 : forall l : list (elt * elt), Pf l -> P (abs l))
  (fnil : Pf nil) 
  (fcons : forall u v l, P u -> P v -> Pf l -> Pf ((u,v)::l)) =>
fix F (e : elt) : P e :=
  let fix Ff (l : list (elt * elt)) : Pf l := 
    match l as f0 return Pf f0 with 
    | nil => fnil 
    | ((u,v)::t) => fcons _ _ _ (F u) (F v) (Ff t)
    end in
  match e as e0 return (P e0) with
  | bot => f
  | tnat => f0
  | tuniv n => f1 n
  | zero => f2
  | succ e0 => f3 e0 (F e0)
  | tpi e0 l => f4 e0 (F e0) l (Ff l)
  | abs l => f5 l (Ff l)
  end.


Derive NoConfusion NoConfusionHom Subterm for elt.


(* The rank of a term is the maximum depth of its tree.

   NB: original definition is:
   rk(f) = 1 + max(rk(ui), rk(f (ui))) if 
   f = (u1 → v1,...,ul → vl) is minimal and l > 0. 
   Below, we define it over all terms, including invalid ones.

 Properties of rank:
   [rk_lub]    rk(u ∨ v)  = max(rk(u), rk(v)) 
   [rk_app]    rk(f (u)) <= rk(f) for all u
 *)

Fixpoint rk (u : elt) : nat :=
  let fix rk_fun f :=
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (rk ui) (rk vi)) (rk_fun tl)
    end in
  match u with 
  | bot => 0 
  | tnat => 1
  | tuniv k => 1
  | zero => 1 
  | succ v => 1 + rk v
  | tpi a f => 1 + (max (rk a) (rk_fun f))
  | abs f => 1 + rk_fun f
  end.

Fixpoint rk_fun (f : list (elt * elt)) := 
    match f with
      | nil => 0
      | (ui, vi) :: tl => max (max (rk ui) (rk vi)) (rk_fun tl)
    end.


(* We can only compute the lub of compatible functions.
   compatible -> Comp
 *)
Fixpoint compatible u v {struct u} : bool := 
  let compatible_fun (f g : list (elt * elt)) : bool :=
    List.forallb (fun '(ui,vi) => 
      List.forallb (fun '(uj,vj) => 
         (compatible ui uj) ==> (compatible vi vj)) g) f
  in
  match u , v with 
  | _ , bot => true
  | bot , _ => true
  | tnat , tnat => true
  | zero , zero => true
  | succ u , succ v => compatible u v
  | tpi a f , tpi b g => 
      (compatible a b) && (compatible_fun f g)
  | abs f , abs g => compatible_fun f g 
  | tuniv i , tuniv j => Nat.eqb i j
  | _ , _ => false
  end.

Definition coherent_with f '(u, v) := 
  forallb (fun '(uj,vj) => compatible u uj ==> compatible v vj) f.

Definition compatible_fun (f g : list (elt * elt)) : bool :=
  List.forallb (fun '(ui,vi) => 
     List.forallb (fun '(uj,vj) => 
       (compatible ui uj) ==> (compatible vi vj)) g) f.


Lemma compatible_fun_spec f g : 
  compatible_fun f g = List.forallb (coherent_with g) f.
reflexivity.
Qed.

Definition lub_fun (f g : list (elt * elt)) : list (elt * elt) := 
  (f ++ g).



(* Least upper bound of two terms *)
(* This function is only defined on compatible elements *)
(* Maybe: just return bot instead of None *)
Fixpoint lub (u v : elt) : option elt :=
  match u, v with
  | bot,    v    => Some v
  | u,      bot  => Some u
  | tnat,   tnat => Some tnat
  | zero,   zero => Some zero
  | tuniv i, tuniv j =>
      if Nat.eqb i j then Some (tuniv i) else None
  | succ u, succ v =>
      option_map succ (lub u v)
  | tpi a f, tpi b g =>
      if compatible_fun f g
      then option_map (fun c => tpi c (f ++ g)) (lub a b)
      else None
  | abs f, abs g =>
      if compatible_fun f g then Some (abs (f ++ g)) else None
  | _, _ => None
  end.

Definition lub_opt (o1 : option elt) (o2: option elt) : option elt := 
  match o1,o2 with 
    | Some e1 , Some e2 => lub e1 e2
    | _ , _ => None
  end.

Definition lub_list_opt : list (option elt) -> option elt := 
  List.fold_right lub_opt (Some bot).

(* Fold lub over a list of elements. *)
Definition lub_list (xs : list elt) : option elt := 
  lub_list_opt (List.map Some xs).   


(* --------------------------------------------------------- *)

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

(* --------------------------------------------------------- *)

Fixpoint list_ap {A B } (f : list (A -> B)) (x : list A) : list B := 
  List.flat_map (fun x1 => List.flat_map (fun x2 => (x1 x2 :: nil)) x) f.

Definition list_map2 {A B C} (f : A -> B -> C) (x : list A) (y : list B) : list C := 
  list_ap (List.map f x) y.

(* first nat is level, second is rank *)
Parameter level_rk_enum : nat -> nat -> list elt.

Axiom level_rk_enum_sound : 
  forall k r e, List.In e (level_rk_enum k r) -> rk e <= r /\ level e <= k.
Axiom level_rk_enum_complete : 
  forall k r e, rk e <= r -> level e <= k -> List.In e (level_rk_enum k r).



(* Work on enumerating all elements of a certain level/rank
Fixpoint level_rk_enum (k : nat) (r : nat) : list elt := 
  let fix rk_enum r := 
      (* enumerate all functions of complexity (k,r) *)
      let fix rk_enum_fun r : list (list (elt * elt))
        := match r with 
           | 0 => nil 
           | S n => let q := rk_enum r in     (* all rank r elements *)
                   let p := rk_enum_fun n in (* all rank n functions *)
                   let qp := list_map2 pair q q in (* all pairs of rank n elements *)
                   p  
           end 

      in      
      match r with 
      | 0 => ( bot :: nil) 
      | 1 => ( bot :: tnat :: tuniv k :: zero :: 
              succ bot :: tpi bot (rk_enum_fun 0) :: abs (rk_enum_fun 0) :: nil )
      | S n => let p := rk_enum n in 
              let q := rk_enum_fun n in
              List.map succ p ++ 
                list_map2 tpi p q ++ 
                List.map abs q ++ p
      end
  in match k with 
       | 0 => rk_enum r 
       | S m => rk_enum r ++ level_rk_enum m r
     end
  .

Fixpoint level_rk_enum_complete k r : 
  forall e, rk e <= r -> level e <= k -> List.In e (level_rk_enum k r).
Proof.
  have rk_enum_complete : 
    forall e, rk e <= r -> level e = k -> List.In e (level_rk_enum k r).
  { 
    induction r; intros e h1 h2. 
    - destruct e; cbn in h1; cbn in h2; subst; cbn; try lia.
      left; auto.
    - destruct r. 
      + (* r = 1 *)
        destruct e; cbn in h1; cbn in h2; subst; try lia; cbn.
        all: fold level_fun.
        * left; done.
        * right. left. done.
        * admit.
        * right. right. right. left. done. 
        * destruct e; cbn in h1; cbn; try done.
*)      



(* For finite functions, when do we have f <= g ?
   We want an extensional definition that says:
   forall x, app f x <= app g x 
   However, we also want a decidable definition. 
   so we look at all of the (ui,vi) in f and see what they do in g.
*) 


(* The termination metric for this definition is (max (rk u) (rk v)). *)
(* NB: cannot use equations as it doesn't support mutual definitions *)
Fixpoint le' (u v : elt) k : bool := 
  let app g ui m : option elt := 
    lub_list (List.map (fun '(uj,vj) => 
                          if compatible uj ui && le' uj ui m then vj else bot) g) in
      
  let le_fun f g m := 
    List.forallb (fun '(ui,vi) => match (app g ui m) with 
                               | Some v => le' vi v m
                               | None => false
                               end) f 
  in
  match u , v with 
  | bot , _ => true
  | tnat , tnat => true
  | zero , zero => true
  | succ u0 , succ v0 => 
      match k with 
      | 0 => false 
      | S m => le' u0 v0 m
      end
  | tpi a f , tpi b g => 
      match k with 
      | 0 => false 
      | S m => (le' a b m) && (le_fun f g m)
      end
  | tuniv i , tuniv j => Nat.eqb i j
  | abs f , abs g => 
      match k with 
      | 0 => false 
      | S m => le_fun f g m
      end
  (* do we need this case? *)
  (*
  | abs f , bot => 
      match k with 
      | 0 => false
      | S m => List.forallb (fun '(ui,vi) => le' vi bot m) f
      end *)
  | _ , _ => false
  end.

(* leFinEl *)
Definition le (u v : elt) := le' u v (max (rk u) (rk v)).

Definition app' (f : list (elt * elt)) (u : elt) m : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if compatible ui u && le' ui u m then vi else bot) f).

(* EvalFun *)
Definition app (f : list (elt * elt)) (u : elt) : option elt := 
   lub_list (List.map (fun '(ui,vi) => 
                         if compatible ui u && le ui u then vi else bot) f).

Definition le_fun' f g m := 
  List.forallb (fun '(ui,vi) => 
                  match (app' g ui m) with 
                  | Some v => le' vi v m
                  | None => false
                  end) f.
(* leFun *)
Definition le_fun f g := 
  List.forallb (fun '(ui,vi) => 
                  match (app g ui) with 
                  | Some v => le vi v 
                  | None => false
                  end) f.

Definition lt u v := le u v && ~~(le v u).
Definition sem_eqb (u v:elt) := le u v && le v u.
Definition sem_eqb_fun f g := le_fun f g && le_fun g f.

(***** EXAMPLES *******)

Definition one  := succ zero.
(* identity function, but only defined on 0 *)
Definition id0  : elt := abs ((zero,zero) :: nil).
(* identity function, only defined on 0 and 1 *)
Definition id01 : elt := abs ((zero,zero) :: (one, one) :: nil). 
(* the second has strictly more information than the first *)
Lemma le_id0_id01 : lt id0 id01.
Proof. reflexivity. Qed.

(* note we have some contravariance in our information 
   ordering.
   a function that takes the second as an argument is strictly 
   smaller than one that takes the first.
 *)
Example example_le_fun : 
  lt (abs ((id01,zero) :: nil)) (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.


(* the mapping id01->0 is redundant because it is subsumed by 
   id0->0. *)
Example example_redundant : 
  sem_eqb (abs ((id01,zero) :: (id0, zero) :: nil)) 
          (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.


(* identity function, only defined on 0 and U0. 
   NOTE: This element is semantically ill-typed. *)
Definition id_0U0  : elt := 
  abs ((zero,zero) :: (tuniv 0,tuniv 0) :: nil).

(* even though it is ill-typed, we can include it as a subterm 
   of a term that equivalent to a well-typed term. *)
Example example_redundant_illtyped_typed : 
  sem_eqb (abs ((id_0U0,zero) :: (id0, zero) :: nil)) 
          (abs ((id0, zero) :: nil)).
Proof. reflexivity. Qed.

(* Therefore, we will need to require minimal descriptions of 
   functions if we hope to make our typing relation stable under 
   equivalence. And hope that this is enough to rule out ill-typed
   examples like the one above. 

   The property that we want is that if two elements are minimal
   and equivalent then they are mutually typeable. 
 *)

(* --------------------------------------------------------- *)

(* Minimality: how can we reason about it? *)


(* Should we use sem_eqb or eqb? *)
Fixpoint remove (u:elt) (v:elt) (f : list (elt * elt)) := 
  match f with 
  | nil => nil
  | (ui,vi) :: f' => if eqb u ui && eqb v vi then remove u v f'
                   else (ui,vi) :: remove u v f'
  end.

(* This seems pretty difficult to work with... *)
Definition minimal (f : list (elt * elt)) : bool := 
  forallb (fun '(ui,vi) => 
             sem_eqb_fun f (remove ui vi f)) f.

(* NOTE: Steve points out that 
           [(zero, bot)] is minimal because we
           cannot have an empty list *)


(* --------------------------------------------------------- *)


(* inductive version of app *)
Fixpoint app_alt (f : list (elt * elt)) (u : elt) : option elt := 
  match f with
  | nil => Some bot
  | ((ui,vi) :: tail) => 
      let appt := app_alt tail u in 
      if compatible ui u && (le ui u) then
        match appt with 
        | Some t => lub vi t | None => None end else appt
  end.

Lemma app_spec : app = app_alt.
Proof.
Admitted. 
(*
  smpl extensionality.
  induction x.
  - smpl extensionality. cbn. auto.
  - smpl extensionality. intros u.
    destruct a as [ui vi].
    cbn.
    destruct (le ui u) eqn:LE.
    + rewrite <- IHx. 
      reflexivity.
    + rewrite <- IHx.
      unfold basics.option_bind. 
      replace (lub bot) with (Some (A:=elt)). 
      2: { smpl extensionality. intro y. reflexivity. } 
      rewrite option_eta.
      reflexivity.
Qed. 
*)


(* --------------------------------------------------------- *)

(** * Theory about rk *)

Lemma In_rk_fun1 {ui vi l} : In (ui, vi) l -> rk ui <= rk_fun l.
induction l.
- intro h. inversion h.
- intros [->|h1].
  + cbn. lia.
  + destruct a as [uj vj]. cbn.
    apply IHl in h1. lia.
Qed.

Lemma In_rk_fun2 {ui vi l} : In (ui, vi) l -> rk vi <= rk_fun l.
induction l.
- intro h. inversion h.
- intros [->|h1].
  + cbn. lia.
  + destruct a as [uj vj]. cbn.
    apply IHl in h1. lia.
Qed.

Lemma rk_fun_app {f g} : 
  rk_fun (f ++ g) = max (rk_fun f) (rk_fun g).
Proof.
  induction f.
  all: cbn. done.
  destruct a as [u v].
  rewrite IHf.
  lia.
Qed.

Lemma rk_lub u v w : 
  lub u v = Some w -> rk w = max (rk u) (rk v).
Proof.
  move: v w.
  induction u.
  all: intros v w.
  all: cbn.
  all: destruct v.
  all: intros h; inversion h; subst.
  all: cbn; auto.
  - destruct PeanoNat.Nat.eqb; inversion h. cbn. reflexivity.
  - destruct (lub u v) eqn:LU; cbn in h; inversion h. 
    cbn. f_equal. eauto. 
  - fold rk_fun.
    destruct (lub u v) eqn:LU;
    destruct compatible_fun eqn:C; 
    inversion h.
    cbn. fold rk_fun. f_equal.
    apply IHu in LU. rewrite LU.
    rewrite rk_fun_app. 
    lia.
  - destruct compatible_fun eqn:C. 2: done.
    inversion h. cbn.
    f_equal. fold rk_fun.
    rewrite rk_fun_app. 
    reflexivity.
Qed.

Lemma rk_lub_list xs u : 
  lub_list xs = Some u -> rk u = List.list_max (List.map rk xs).
Proof.  
  move: u.
  induction xs.
  - intros u h; inversion h. subst. done.
  - cbn; intros u h. unfold lub_list_opt, lub_opt in h. 
    destruct fold_right eqn:L. 2: done.
    cbn in h. 
    apply IHxs in L. unfold List.list_max in L. rewrite <- L.
    eapply rk_lub.
    done.
Qed.    

(* 
   rk(f(u)) <= rk(f) for all u   
*)
Lemma rk_app': forall m f u w, 
       app' f u m = Some w -> rk w <= rk_fun f.
Proof.
    intros m f u w.
    unfold app'.
    intros h. rewrite (rk_lub_list h). clear h.
    induction f.
    - cbn. auto.
    - destruct a as [ui vi]. cbn.
      eapply Nat.max_le_compat.
      2: { eapply IHf. } 
      destruct (compatible ui u && le' ui u m). 
      lia. cbn. lia.
Qed.


(*
Fixpoint compatible_fun' (f : list (elt * elt)) : Prop :=
  match f with 
  | nil => true
  | (ui,vi) :: ft => 
      compatible_fun' ft /\
      forall u, le ui u -> forall w, app ft u = Some w -> compatible vi w 
  end.

Lemma compatible_fun_compatible_fun' f :
  compatible_fun f f -> compatible_fun' f.
Proof. 
  induction f. done.
  destruct a as [ui vi].
  move=> /andP [/andP [h1 h2]] /forallb_forall h3.
  have Cf: compatible_fun f f.
  { apply /forallb_forall.
    move=> [uj vj] Inj.
    specialize (h3 _ Inj). cbn in h3.
    move: h3 => /andP [h3 h4]. eapply h4.
  } 
  cbn. split; auto.
  move=> u Le w APP.
Abort.
*)

(** * Raw Theory about compatibility *)

(* This is more difficult than it should be. Need to prove
   it by strong induction on the depth of both terms. 
*)
Lemma compatible_sym : forall u v, compatible u v -> compatible v u.
Proof.
  have LEMMA: 
     forall (k : nat) (u v : elt), 
       Init.Nat.max (rk u) (rk v) <= k -> 
       compatible u v -> compatible v u.
  { 
    elim /strong_ind.
    move=> m ih.
    have LEMMA2 : 
          forall f g, (max (rk_fun f) (rk_fun g) < m)%nat -> 
          compatible_fun f g -> compatible_fun g f.
      {
        move=> f g Le2 /forallb_forall h2. 
        apply /forallb_forall.
        intros [ui vi] Inl0.  
        apply /forallb_forall.
        intros [uj vj] Inl.
        apply /implyP.
        specialize (h2 _ Inl). cbn in h2.
        move: h2 => /forallb_forall h2.
        specialize (h2 _ Inl0). cbn in h2.
        move: h2 => /implyP h2.
        move: (In_rk_fun2 Inl) => Levj. 
        move: (In_rk_fun2 Inl0) => Levi. 
        intro x. eapply ih; eauto. lia.
        eapply h2.
        eapply ih; eauto. 
        move: (In_rk_fun1 Inl) => Leuj. 
        move: (In_rk_fun1 Inl0) => Leui. 
        lia.
      }
    
    move=>u v Le. 
    destruct u; destruct v; cbn in *; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m0 [-> LL]] end.
    - cbn. rewrite PeanoNat.Nat.eqb_sym. done.
    - eauto.
    - fold rk_fun in *.
      move=> /andP [h1 h2].
      apply /andP; split.
      + eapply ih; eauto. lia.
      + move: h2. eapply LEMMA2; eauto. lia.
    - fold rk_fun in *.
      eapply LEMMA2; eauto.
  } 
  move=> u v. eapply LEMMA; eauto.
Qed.  

Lemma compatible_fun_sym : 
  forall f g, compatible_fun f g -> compatible_fun g f.
Proof.
  move=> f g /forallb_forall h2. 
  apply /forallb_forall.
  intros [ui vi] Inl0.  
  apply /forallb_forall.
  intros [uj vj] Inl.
  apply /implyP.
  specialize (h2 _ Inl). cbn in h2.
  move: h2 => /forallb_forall h2.
  specialize (h2 _ Inl0). cbn in h2.
  move: h2 => /implyP h2.
  move: (In_rk_fun2 Inl) => Levj. 
  move: (In_rk_fun2 Inl0) => Levi. 
  intro x. eapply compatible_sym; eauto. 
  eapply h2.
  eapply compatible_sym; eauto. 
Qed.


(* NB: compatibility is not transtive because of bot *)
(* NB: only valid functions are compatible *)

(* Terms that are compatible have a least upper bound *)
Lemma compatible_lub_exists u v : 
  compatible u v -> { w & lub u v = Some w }.
Proof.
  move: v.
  induction u.
  all: destruct v; cbn.
  all: intro h; try done.
  all: try solve [eexists; eauto].
  - rewrite h.
    eexists; eauto.
  - edestruct IHu as [w ->]; eauto.
    eexists; cbn; eauto.
  - move: h => /andP [h1 h2].
    edestruct IHu as [w ->]; eauto.
    exists (tpi w (l ++ l0)).
    rewrite /compatible_fun h2.
    cbn; eauto.
  - eexists.   
    rewrite /compatible_fun h.
    cbn; eauto.
Qed.

Lemma lub_compatible u v w : 
  lub u v = Some w -> compatible u v.
Proof.
  move: v w.
  induction u.
  all: intros v w h.
  all: destruct v; try done.
  all: cbn in h.
  - destruct (n =? n0) eqn:h1; done.
  - destruct (lub u v) eqn:h1; try done.
    cbn. cbn in h. eauto.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    erewrite IHu; eauto. 
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
Qed.

Lemma lub_None_not_compatible u v : 
  lub u v = None -> ~~ (compatible u v).
Proof.
  move: v.
  induction u.
  all: intros v h.
  all: destruct v; try done.
  all: cbn in h.
  - destruct (n =? n0) eqn:h1; try done.
    cbn. rewrite h1. done.
  - destruct (lub u v) eqn:h1; try done.
    cbn. cbn in h. eauto.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    rewrite negb_and. rewrite IHu. auto. done.
    fold (compatible_fun l l0).
    rewrite negb_and. rewrite h1. cbn. apply orbT.
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
    fold (compatible_fun l l0).
    rewrite h1. done.
Qed.


Lemma not_compatible_lub_None u v : 
  ~~ (compatible u v) -> lub u v = None.
Proof.
  move: v.
  induction u.
  all: intros v h.
  all: destruct v; try done.
  - destruct (n =? n0) eqn:h1.
    cbn in h. rewrite h1 in h. done.
    cbn in h. cbn. rewrite h1. done.
  - destruct (lub u v) eqn:h1; cbn in h.
    apply IHu in h. rewrite h in h1. done.
    apply IHu in h. cbn. rewrite h1. done.
  - cbn. destruct (compatible_fun l l0) eqn:h1; try done.
    destruct (lub u v) eqn:h2; try done.
    cbn in h. rewrite negb_and in h. 
    move: h => /orP [h|h].
    + apply IHu in h. rewrite h2 in h. done.
    + fold (compatible_fun l l0) in h.
      rewrite h1 in h. done.
  - cbn.
    destruct (compatible_fun l l0) eqn:h1; try done.
    cbn in h.
    fold (compatible_fun l l0) in h.
    rewrite h1 in h. done.
Qed.
  
Lemma compatible_cons_def u v l l0 :
  compatible_fun ((u, v) :: l) l0 = 
  forallb (fun '(uj,vj) => compatible u uj ==> compatible v vj) l0 &&
  compatible_fun l l0 .
Proof. 
  cbn. f_equal.
Qed.

(* A single entry is compatible with f *)
Lemma compatible_cons u v f g :
  (forall uj vj, In (uj,vj) g -> compatible u uj -> compatible v vj) ->
  compatible_fun f g ->
  compatible_fun ((u,v)::f) g.
Proof.
  intros h1 h2.
  rewrite compatible_cons_def.
  apply /andP.
  split; auto.
  apply /forallb_forall. 
  intros x Ing. destruct x. specialize (h1 _ _ Ing).
  apply /implyP.
  done.
Qed.

Lemma compatible_append : forall h g f, 
      compatible_fun h f -> 
      compatible_fun h g -> 
      compatible_fun h (f ++ g).
Proof.
  induction h; intros g f.
  - cbn. auto.
  - destruct a as [u v]. cbn.
    move=> /andP [h1 h2].
    move: h1 => /forallb_forall h1.
    move: h2 => /forallb_forall h2.
    move=> /andP [/forallb_forall h3 /forallb_forall h4].
    apply /andP. split.
    -- apply /forallb_forall.
       move=> x Inx. 
       destruct (in_app_or _ _ _ Inx) as [h5|h5].
    + apply h1. done.
    + eauto.
    -- apply /forallb_forall.
       move=> [ui vi] Inh.
       rewrite forallb_app.
       apply /andP. split. 
       eapply (h2 _ Inh).
       eapply (h4 _ Inh).
Qed.


(* comp_Sup *)
Lemma lub_compatible_trans u v w x: 
  lub u v = Some w -> 
  compatible x u -> 
  compatible x v -> 
  compatible x w.
Proof.
  move: v w x.
  induction u.
  all: move => v w x.
  all: destruct v; move=>h; inversion h; try done.
  - destruct (n =? n0) eqn:h1; try done.
    inversion H0. subst. auto.
  - destruct (lub u v) eqn:h1; try done.
    cbn in H0. inversion H0. subst.
    destruct x; try done. cbn.
    eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub u v) eqn:h2. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    move=> /andP [hu hl].
    move=> /andP [hv hl0].
    apply /andP. split.
    eauto.
    fold (compatible_fun l1 l) in hl.
    fold (compatible_fun l1 l0) in hl0.
    eapply compatible_append; eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    eapply compatible_append; eauto.
Qed.


Lemma compatible_append_assoc: forall l l0 l1,
        compatible_fun l l0 -> 
        compatible_fun l0 l1 ->
        compatible_fun l (l0 ++ l1) = compatible_fun (l ++ l0) l1.
Proof.
  induction l; intros l0 l1 h1 h2.
  rewrite app_nil_l. rewrite h2. done.
  destruct a as [u v].
  cbn.
  fold (compatible_fun l (l0 ++ l1)).
  fold (compatible_fun (l ++ l0) l1).
  rewrite compatible_cons_def in h1.
  move: h1 => /andP [h1 h3]. 
  rewrite IHl; auto.
  f_equal.
  induction l0. cbn. done.
  destruct a as [uk vk].
  rewrite compatible_cons_def in h2.
  move: h2 => /andP [h2 h4].
  apply compatible_fun_sym in h3. 
  rewrite compatible_cons_def in h3.
  move: h3 => /andP [h3 h5].
  cbn in h1.
  move: h1 => /andP [h1 h1'].
  apply compatible_fun_sym in h5.
  specialize (IHl0 ltac:(eauto) ltac:(eauto) ltac:(eauto)).
  cbn.
  rewrite IHl0.
  rewrite h1. cbn.
  done.
Qed.

Lemma lub_opt_idL o : lub_opt (Some bot) o = o.
cbn. destruct o; done.
Qed.

Lemma lub_bot_l e : lub bot e = Some e.
reflexivity.
Qed.

Lemma lub_bot_r e : lub e bot = Some e.
destruct e; reflexivity.
Qed.

(* Sup-assoc *)
Lemma lub_assoc u v w w1 w2 : 
  lub u v = Some w1 -> 
  lub v w = Some w2 ->
  lub w1 w = lub u w2.
Proof.
  move: v w w1 w2.
  induction u.
  all: move=> e0 e1 w w1 h h1.
  all: destruct e0; cbn in *.
  all: destruct e1; cbn in *.
  all: inversion h; subst.
  all: inversion h1; subst.
  all: cbn; try done.
  + destruct (n =? n0); try done. inversion h. cbn. done.
  + destruct (n =? n0) eqn:E1; try done. inversion h. cbn.
    destruct (n0 =? n1) eqn:E2; try done. inversion h1. rewrite E1.
    rewrite Nat.eqb_eq in E1. rewrite Nat.eqb_eq in E2. subst.
    rewrite Nat.eqb_refl. done.
  + destruct (lub u e0) as [w0|]; try done. inversion h. subst. clear h.
      cbn. done.
    + destruct (lub u e0) as [w0|] eqn:L0; try done. inversion h. subst. clear h.
      destruct (lub e0 e1) as [w2|] eqn:L1; try done. inversion h1. subst. clear h1.
      clear H0 H1.
      move: (IHu _ _ _ _ L0 L1) => h2. 
      cbn. rewrite h2. done.
    + destruct (compatible_fun l l0) eqn:C; try done.
      destruct (lub u e0) eqn:E; try done. cbn in h. inversion h. cbn. done.
    + destruct (compatible_fun l l0) eqn:C1; try done.
      destruct (compatible_fun l0 l1) eqn:C2; try done.
      destruct (lub u e0) eqn:E; try done.
      destruct (lub e0 e1) eqn:E1; try done.
      cbn in h1. cbn in H1.
      inversion H0. subst. inversion H1. subst.
      rewrite compatible_append_assoc; eauto.
      cbn. rewrite app_assoc.
      destruct (compatible_fun (l ++ l0)); try done.
      move: (IHu _ _ _ _ E E1) => h3. rewrite h3.
      done.
    + (* abs *)
      destruct (compatible_fun l l0) eqn:C; try done.
      inversion h. cbn. done.
    + (* abs *)
      destruct (compatible_fun l l0) eqn:C1; try done.
      destruct (compatible_fun l0 l1) eqn:C2; try done.
      inversion H0. subst. inversion H1. subst.
      rewrite compatible_append_assoc; eauto.
      cbn. rewrite app_assoc. done.
Qed.


(* If coherent_with g x = false, then coherent_with (g++h) x = false.
   Follows because coherent_with (g++h) x = coherent_with g x && coherent_with h x. *)
Lemma coherent_with_app_l (x : elt * elt) g h :
  coherent_with g x = false ->
  coherent_with (g ++ h) x = false.
Proof.
  destruct x as [u v]. unfold coherent_with.
  rewrite forallb_app. move=> ->. done.
Qed.

(* If compatible_fun g f = false, then compatible_fun (h++g) f = false.
   Follows because compatible_fun (h++g) f = compatible_fun h f && compatible_fun g f. *)
Lemma compatible_fun_app_r (h g f : list (elt * elt)) :
  compatible_fun g f = false ->
  compatible_fun (h ++ g) f = false.
Proof.
  unfold compatible_fun. rewrite forallb_app.
  move=> h1.
  apply /andP. move=> [h2 h3].
  rewrite h1 in h3.
  done.
Qed.

(* If compatible_fun f g = false, then compatible_fun f (g++h) = false.
   Follows because coherent_with (g++h) x = coherent_with g x && ..., so if
   some entry of f fails coherent_with g, it also fails coherent_with (g++h). *)
Lemma compatible_fun_app_l (f g h : list (elt * elt)) :
  compatible_fun f g = false ->
  compatible_fun f (g ++ h) = false.
Proof.
  induction f as [| [u v] f IHf].
  - done.
  - unfold compatible_fun. cbn.
    move=> Hf.
    fold (compatible_fun f (g ++ h)).
    apply /andP. move=> [h1 h2].
    rewrite Bool.andb_false_iff in Hf.
    fold (coherent_with (g ++ h) (u, v)) in h1.
    fold (coherent_with g (u, v)) in Hf.
    fold (compatible_fun f g) in Hf.
    destruct Hf. 
    + move: (coherent_with_app_l h H) => h3.
      rewrite h1 in h3. done.
    + apply IHf in H. rewrite h2 in H. done.
Qed.

Lemma lub_None_sym u v : lub u v = None -> lub v u = None.
Proof.
  move: v.
  induction u.
  all: move=> v; destruct v; move=> h; inversion h; cbn; try done.
  - rewrite H0.
    rewrite Nat.eqb_sym.
    destruct (n =? n0) eqn:h1. rewrite Nat.eqb_eq in h1. subst. done. done.
  - destruct (lub u v) eqn:h1. done. rewrite IHu; auto.
  - admit.
  - destruct (compatible_fun l l0) eqn:h1. done.
    destruct (compatible_fun l0 l) eqn:h2.
    + apply compatible_fun_sym in h2. rewrite h1 in h2. done.
    + done.
Admitted.

Lemma lub_assoc_None v : forall e w1 w2,
  lub v e = Some w1 ->
  lub e w2 = None ->
  lub w1 w2 = None.
Proof.  
  induction v.
  all: move=> e w1 w2 L1 L2.
  all: destruct e; cbn in *; inversion L1; subst.
  all: inversion L2; subst.
  all: try solve [destruct w2; try done].
  - (* univ *) 
    destruct (n =? n0) eqn:E1; try done. 
    rewrite Nat.eqb_eq in E1. subst. inversion L1. subst.
    cbn. done.
  - (* succ *) 
    destruct (lub v e) eqn:LUB; try done.
    destruct w2 eqn:h2.
    all: try solve [subst; cbn in *; inversion L1; cbn; done].
    (* only succ case remains *)
    cbn in *. inversion L1; subst; clear L1. clear H0.
    cbn. f_equal.
    destruct (lub e e1) eqn:E1. done.
    eapply IHv; eauto.
  - (* tpi *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub v e) eqn:h2; try done.
    inversion L1; subst. clear L1 H0.
    destruct w2 eqn:h3.
    all: try solve [cbn in *; done].
    cbn in *.
    destruct (compatible_fun l0 l1) eqn:h4.
    + destruct (compatible_fun (l ++ l0) l1) eqn:h5.
      destruct (lub e e1) eqn:h6. inversion L2.
      erewrite IHv; eauto. rewrite L2. done.
    + destruct (compatible_fun (l ++ l0) l1) eqn:h5. 2: done.
      move: (compatible_fun_app_r l h4) => h6. rewrite h6 in h5. done.
  - (* tabs *)
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct w2 eqn:h2.
    all: inversion L2; clear L2.
    all: inversion L1; cbn; try done.
    subst; clear L1 H0.
    destruct (compatible_fun l0 l1) eqn:h2. done. clear H1 H2.
    destruct (compatible_fun (l ++ l0) l1) eqn:h3. 2: done.
    move: (compatible_fun_app_r l h2) => h4. rewrite h3 in h4. done.
Qed.


Lemma lub_opt_assoc u v w :
  lub_opt (lub_opt u v) w = lub_opt u (lub_opt v w).
Proof.
  destruct u; destruct v; destruct w; cbn; try done.
  all: destruct (lub e e0) as [xy|] eqn:h; cbn; try done.
  all: destruct (lub e0 e1) as [yz|] eqn:h1; cbn; try done.
  - (* all lubs are defined: lub xy e1 = lub e yz *)
    eapply lub_assoc; eauto.
  - (* lub e e0 = Some xy, lub e0 e1 = None: need lub xy e1 = None *)
    eapply lub_assoc_None; eauto.
  - admit.
Admitted.
      

Lemma lub_list_app l1 l2 o1 o2 : 
  lub_list l1 = o1 ->
  lub_list l2 = o2 ->
  lub_list (l1 ++ l2) = lub_opt o1 o2.
Proof.
unfold lub_list. rewrite map_app.
unfold lub_list_opt.
rewrite fold_right_app. move=> y. eapply lub_opt_idL. intros. rewrite lub_opt_assoc. done.
move=> h1 h2.
rewrite h1. rewrite h2.
done.
Qed.

(* -------------------------------------- *)


(* all pairs of elements in l are compatible *)
Definition pairwise_compatible (l : list elt) : bool :=
  forallb (fun x => forallb (fun y => compatible x y) l) l.


Lemma le_bot v : le bot v.
destruct v; reflexivity.
Qed.

Lemma le_bot' v m : le' bot v m.
destruct v; destruct m; reflexivity.
Qed.


Lemma list_lub_compatible_trans l x w: 
  lub_list l = Some w -> (forallb (compatible x) l) -> compatible x w.
Proof.
  move:w.
  induction l.
  - move=> w h. inversion h. subst.
    destruct x; try done.
  - move=> w h.
    cbn in h. cbn. 
    fold (lub_list l) in h.
    move=> /andP [h1 h2].
    destruct (lub_list l) eqn:h3. 2: done.
    specialize (IHl _ ltac:(eauto) h2).
    cbn in h.
    eapply lub_compatible_trans; eauto.
Qed.

(* if that is the case, then the lub exists *)
Lemma pairwise_lub_exists l : 
  pairwise_compatible l -> 
  { w | lub_list l = Some w }.
Proof.
  induction l.
  - cbn. move=> h. eauto.
  - cbn.
    move=> /andP [/andP [_ h1] /forallb_forall h2]. 
    destruct IHl as [w0 EQ].
    apply /forallb_forall. move=> x xIn. specialize (h2 x xIn).
    move: h2 => /andP [h2 h3]. done. 
    unfold lub_list in EQ. rewrite EQ. fold (lub_list l) in EQ.
    cbn. 
    move: (list_lub_compatible_trans EQ h1) => h3. 
    destruct (compatible_lub_exists h3) as [w h4].
    exists w. eauto. 
Qed.

(* --------------------------------------------------------- *)

(** * Raw Theory about le (totality, reduction) *)

Local Lemma rk_le_enough : forall k u v,
  max (rk u) (rk v) <= k -> 
  le' u v (max (rk u) (rk v)) = (le' u v k).
Proof.
  elim /strong_ind.
  move=> m ih u v Le.
  destruct m.
  - destruct u; destruct v; cbn in *; auto.
    all: try lia.
  - have LEM1:
      forall g ui r, r <= m -> (max (rk_fun g) (rk ui)) <= r ->
                app' g ui r = app' g ui m.
      { subst. 
        move=> g ui r Le1 Le2.
        unfold app'.
        f_equal.
        eapply map_ext_in.
        move=> [uj vj] Ing.
        move: (In_rk_fun1 Ing) => h1.
        move: (In_rk_fun2 Ing) => h2.
        rewrite <- ih; try lia.
        rewrite <- (ih m); try lia.
        reflexivity.
      }
      have LEM2: 
        forall l l0 r, 
          max (rk_fun l) (rk_fun l0) <= r -> r <= m -> 
          le_fun' l l0 r = le_fun' l l0 m.
      {
        subst. 
        move=> f g r Le1 Le2.
        eapply forall_ext.
        move=> [ui vi] Inl.
        move: (In_rk_fun1 Inl) => h1.
        move: (In_rk_fun2 Inl) => h2.
        rewrite LEM1; try lia.
        destruct app' eqn:EA; try done.
        move: (rk_app' EA) => Le3.
        rewrite <- ih; try lia.
        rewrite <- (ih m); try lia.
        auto.
      } 

    destruct u; destruct v. 
    all: try solve [cbn in *; auto].  
    all: cbn in *.
    all: fold rk_fun in *.
    + erewrite (ih m); eauto. lia.
    + rewrite <- ih; try lia. rewrite <- (ih m); try lia.
      f_equal.
      eapply LEM2; try lia.
    + eapply LEM2; try lia.
Qed.


Local Lemma rk_app_enough :
      forall r g ui, 
        (max (rk_fun g) (rk ui)) <= r ->
        app' g ui r = app' g ui (max (rk_fun g) (rk ui)).
  move=> r g ui Le1.
  unfold app'.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  rewrite <- rk_le_enough; try lia.
  rewrite <- (rk_le_enough (k := Init.Nat.max (rk_fun g) (rk ui))); try lia.
  reflexivity.
Qed.

Local Lemma rk_fun_enough : 
        forall r l l0, 
          max (rk_fun l) (rk_fun l0) <= r ->
          le_fun' l l0 r = le_fun' l l0 (max (rk_fun l) (rk_fun l0)).
Proof.
  move=> r f g Le1.
  eapply forall_ext.
  move=> [ui vi] Inl.
  move: (In_rk_fun1 Inl) => h1.
  move: (In_rk_fun2 Inl) => h2.
  rewrite rk_app_enough; try lia.
  rewrite (rk_app_enough (r:=Init.Nat.max (rk_fun f) (rk_fun g))); 
    try lia.
  destruct app' eqn:EA; try done.
  move: (rk_app' EA) => Le3.
  rewrite <- rk_le_enough; try lia.
  rewrite <- (rk_le_enough (k:=Init.Nat.max (rk_fun f) (rk_fun g))); try lia.
  auto.
Qed. 


Lemma app'_app :
  forall r g ui, (max (rk_fun g) (rk ui)) <= r -> 
            app' g ui r = app g ui.
Proof.
  intros.
  unfold app.
  unfold app'.
  f_equal.
  eapply map_ext_in.
  move=> [uj vj] Ing.
  move: (In_rk_fun1 Ing) => h1.
  move: (In_rk_fun2 Ing) => h2.
  unfold le.
  rewrite <- rk_le_enough; try lia.
  done.
Qed.


Lemma le_fun'_le_fun r l l0 :
  max (rk_fun l) (rk_fun l0) <= r ->
  le_fun' l l0 r = le_fun l l0.
Proof.
  intros h. unfold le_fun', le_fun.
  eapply forall_ext.
  move=> [ui vi] Inl.
  move: (In_rk_fun1 Inl) => h1.
  move: (In_rk_fun2 Inl) => h2.
  rewrite <- (app'_app (r := r)); try lia.
  destruct app' eqn:Ev; try done.
  move: (rk_app' Ev) => h3.
  unfold le.
  rewrite <- rk_le_enough; try lia. 
  done.
Qed.


Lemma le_succ u v : le (succ u) (succ v) = le u v.
Proof.
  reflexivity.
Qed.

Lemma le_tpi a f b g : le (tpi a f) (tpi b g) = 
  (le a b) && (le_fun f g).
Proof.
  unfold le.
  change (rk (tpi a f)) with (S (max (rk a) (rk_fun f))).
  change (rk (tpi b g)) with (S (max (rk b) (rk_fun g))).
  rewrite <- Nat.succ_max_distr.
  cbn.
  remember (max (rk a) (rk_fun f)) as r1.
  remember (max (rk b) (rk_fun g)) as r2.
  remember (max r1 r2) as r.
  f_equal.
  rewrite <- rk_le_enough. done. lia.
  erewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.

Lemma le_abs f g : le (abs f) (abs g) = le_fun f g.
  unfold le. cbn. fold rk_fun.
  remember (max (rk_fun f) (rk_fun g)) as r.
  rewrite <- (le_fun'_le_fun (r:=r)). 2: lia.
  reflexivity.
Qed.  

Lemma le_fun'_cons ui vi f g m : 
  le_fun' ((ui, vi) :: f) g m = 
     (match app' g ui m with 
      | Some v => le' vi v m
      | None => false
      end) && le_fun' f g m.                 
Proof.
  cbn. f_equal.
Qed.

Lemma le_cons u1 v1 l1 l2 : 
 le_fun ((u1, v1) :: l1) l2 = 
   (match (app l2 u1) with 
    | Some w => le v1 w && le_fun l1 l2 
    | None => false
    end).
Proof.
  cbn.
  destruct (app l2 u1) eqn: h. 2: reflexivity.
  f_equal.
Qed.

Lemma rk_app : forall f u w, 
       app f u = Some w -> rk w <= rk_fun f.
Proof.
  intros.
  rewrite <- (app'_app ltac:(reflexivity)) in H.
  eapply rk_app'. eauto.
Qed.


(* --------------------------------------------------------- *)


(* We want finite functions to *not* include bot.

   A valid finite function is 

   - compatible with itself. 
     i.e. all compatible args produce compatible results

   - does not include bot as a result

   - is not an empty list

   - includes only valid args and results

   A term is valid when all of its subterms are valid, including
   functions.

  valid -> Coherent
*)

Definition no_bot_result (f : list (elt * elt)) := 
  List.forallb (fun p => ~~ (le (snd p) bot)) f.

Definition is_nil {A} (f : list A) := 
  match f with | nil => true | _ => false end.

Fixpoint valid u : bool := 
  let valid_fun f := 
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (~~ is_nil f) &&
    (List.forallb (fun '(ui,vi) => 
                     (valid ui) && (valid vi)) f)
  in
  match u with 
  | abs f => valid_fun f
  | tpi a f => valid a && valid_fun f
  | succ v => valid v
  | _ => true
  end.

Definition valid_fun f := 
    (compatible_fun f f) &&
    (no_bot_result f) &&
    (~~ is_nil f) &&
    (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f).


(* if a non-nil function is valid, we can sometimes get a valid tail. *)

Lemma valid_fun_tail u v f :
  valid_fun ((u,v) :: f) -> 
  (~~ is_nil f -> valid_fun f).
Proof.
  move=> /andP [/andP [/andP [h1 h2] _] h3]. 
  rewrite compatible_cons_def in h1.
  cbn in *.
  move: h1 => /andP [/andP [h1 h9] h5].
  move: h2 => /andP [h2 h8].
  move: h3 => /andP [/andP [h3 h7] h6].
  move=> h4.
  apply /andP; split; auto.
  apply /andP; split; auto.
  apply /andP; split; auto.
  unfold compatible_fun in *.
  apply forallb_forall.
  move: h5 => /forallb_forall h5.
  move=> [ui vi] Inf. specialize (h5 _ Inf). cbn in h5.
  move: h5 => /andP [_ h5]. done.
Qed.

Record CFT u v f : Prop := 
  mkCFT { key_valid  : valid u;
          val_valid  : valid v;
          val_nbot   : ~~ le v bot;
          compat     : coherent_with f (u,v)
    }.

Lemma valid_fun_head u v f :
   valid_fun ((u,v) :: f) -> CFT u v f.
Proof. 
  move=> /andP [/andP [/andP [h1 h2] _] h3]. 
  rewrite compatible_cons_def in h1.
  cbn in *.
  move: h1 => /andP [/andP [h1 h9] h5].
  move: h2 => /andP [h2 h8].
  move: h3 => /andP [/andP [h3 h7] h6].
  constructor; eauto.
Qed.

Lemma valid_fun_compatible f :
  valid_fun f -> compatible_fun f f.
Proof.  move=> /andP [/andP [/andP [h1 h2] h4] h3].  auto. Qed.

Lemma valid_fun_no_bot f :
  valid_fun f -> no_bot_result f.
Proof.  move=> /andP [/andP [/andP [ h1 h2] h4] h3].  auto. Qed.

Lemma valid_fun_nonnil f :
  valid_fun f -> ~~ is_nil f.
Proof.  move=> /andP [/andP [/andP [_ h2] h4] h3].  auto. Qed.

Lemma valid_fun_subterms f :
  valid_fun f -> 
  forallb (fun '(ui,vi) => valid ui && valid vi) f.
Proof.
  move=> /andP [/andP [h2 h4] h3].
  done.
Qed.

Lemma valid_fun_subterms_prop f:
  valid_fun f ->
  forall ui vi, In (ui,vi) f -> (valid ui) /\ (valid vi).
Proof. move => /valid_fun_subterms h3.
       move: h3 => /forallb_forall h3.
       move=> ui vi Inf.
       specialize (h3 _ Inf). cbn in h3.
       move: h3 => /andP [h3 h5].
       auto.
Qed.

Create HintDb valid.
Hint Resolve valid_fun_compatible valid_fun_no_bot valid_fun_nonnil valid_fun_subterms : valid.


(* Lemmas about valid terms *)

(* Compatibility is (only) reflexive for valid terms. *)
Lemma compatible_refl u : valid u -> compatible u u.
Proof.
  induction u.
  all: cbn.
  all: auto.
  - intro h. apply PeanoNat.Nat.eqb_refl.
  - move=> /andP [Vu Vf].   
    apply /andP. split; eauto using valid.    
    eapply valid_fun_compatible; eauto.
  - move=> Vf. 
    eapply valid_fun_compatible; eauto.
Qed.


Lemma no_bot_result_app : forall f g, no_bot_result f ->
                   no_bot_result g ->
                   no_bot_result (f ++ g).
Proof. intros f g Nf Ng.
      unfold no_bot_result in *.
      rewrite forallb_app.
      apply /andP. done.
Qed.

Lemma app_append f g u o1 o2: 
  app f u = o1 -> app g u = o2 -> 
  app (f ++ g) u = lub_opt o1 o2.
Proof.
  move=>h1. move=> h2.
  unfold app in *.
  rewrite map_app.
  erewrite lub_list_app; eauto. 
Qed.

(* If we have a non-bot result from application, there must be 
   some tuple in the function that triggered it. *)
(*
Lemma app_inv g u e : 
  no_bot_result g -> 
  app g u = Some e ->
  ~~ (le e bot) ->
  exists ui, exists vi, List.In (ui,vi) g /\ le ui u.
Proof.
  move: u e.
  rewrite app_spec.
  induction g as [|[ui vi]t].
  all: intros u e NR AA NB.
  - cbn in AA. inversion AA. subst. done.
  - cbn in AA. 
    destruct (le ui u) eqn:h2.
    destruct (app_alt t u) eqn:h4. 2: done.
    exists ui. exists vi. split. left. done. done.
    cbn in NR. move: NR => /andP [ _ NR].
    specialize (IHt _ _ NR AA NB).
    destruct IHt as [uj [vj [h1 h3]]].  
    exists uj. exists vj. split. right. done. done.
Qed. *)


(* We can append compatible functions together *)
Definition valid_append f g : 
    valid_fun f 
  -> valid_fun g 
  -> compatible_fun f g 
  -> valid_fun (f ++ g).
Proof.
  move=> /andP [/andP [/andP [Cf Nbf] Nf] Vf] 
        /andP [/andP [/andP [Cg Nbg] Ng] Vg] Cfg.
  apply /andP; split. apply /andP; split. apply /andP; split.
  - unfold compatible_fun in *.
    apply forallb_forall. 
    move=> [ui vi] Ini.
    apply forallb_forall.
    move=> [uj vj] Inj.
    move: Cf => /forallb_forall Cf. 
    move: Cg => /forallb_forall Cg.
    move: Cfg => /forallb_forall Cfg.
    destruct (in_app_or _ _ _ Ini) as [Ifi|Igi];
    destruct (in_app_or _ _ _ Inj) as [Ifj|Igj];
    try move: (Cf _ Ifi) => /forallb_forall Cfi; 
    try move: (Cf _ Ifj) => /forallb_forall Cfj;
    try move: (Cg _ Igi) => /forallb_forall Cgi;
    try move: (Cg _ Igj) => /forallb_forall Cgj.
    + eapply (Cfi _ Ifj).
    + specialize (Cfg _ Ifi). cbn in Cfg.
      move: Cfg => /forallb_forall Cfg.
      specialize (Cfg _ Igj). cbn in Cfg.
      done.
    + specialize (Cfg _ Ifj). cbn in Cfg.
      move: Cfg => /forallb_forall Cfg.
      specialize (Cfg _ Igi). cbn in Cfg.
      move: Cfg => /implyP Cfg.
      apply /implyP. move=> x.
      apply compatible_sym. apply Cfg.  
      apply compatible_sym. auto.
    + eapply (Cgi _ Igj).
  - apply no_bot_result_app; auto. 
  - destruct f; try done.
  - clear Cf Cg Cfg Nf Ng.
    induction f; cbn in *. done.
    destruct a as [u v].
    move: Vf => /andP [h1 h2].
    apply /andP. split. done.
    rewrite forallb_app.
    apply /andP; split; auto.
Qed.

(* The lub of valid elements is valid *)
Lemma valid_lub u v w : valid u -> valid v -> 
                        lub u v = Some w -> valid w.
Proof.
  move: v w.
  induction u.
  all: intros v w Vu Vw h.
  all: destruct v; cbn in h, Vu, Vw; inversion h; subst; try done.
  - destruct Nat.eqb; inversion h. done.
  - destruct (lub u v) eqn:EQ; inversion h. cbn. 
    eapply IHu; eauto.
  - move: Vu => /andP [Vu h1].
    move: Vw => /andP [Vw h3].
    destruct (compatible_fun l l0) eqn:Co. 2: done.
    destruct (lub u v) eqn:LUB. 2: done.
    inversion h. cbn. clear h H0.
    apply /andP. split; eauto.
    eapply valid_append; eauto.
  - destruct (compatible_fun l l0) eqn:Co. 2: done.
    inversion h. cbn.
    eapply valid_append; eauto.
Qed.


Lemma valid_lub_list f : forall u e, 
  (List.forallb (fun '(ui,vi) => (valid ui) && (valid vi)) f) -> valid u ->
  lub_list_opt (map Some (map (fun '(ui, vi) => if compatible ui u && le ui u then vi else bot) f)) =
    Some e -> 
  valid e.
Proof.
  induction f as [|[ui vi]f].
  all: cbn; move=> u e Vf Vu LL.
  - inversion LL. done.
  - move: Vf => /andP [/andP [Vui Vvi] Vf].
    destruct lub_list_opt eqn: h2. 2: done.
    specialize (IHf _ _ Vf Vu h2).
    destruct (compatible ui u && le ui u) eqn: h3.
    ++ eapply valid_lub in LL; eauto.
    ++ cbn in LL. inversion LL. subst. clear LL. done.
Qed.

Lemma valid_app f u w : valid_fun f -> valid u -> app f u = Some w -> valid w.
Proof.
  move: u w.
  induction f as [|[ui vi]f].
  all: cbn; move=> u w Vf Vu App.
  - inversion App; done.
  - destruct lub_list_opt eqn:h1. 2: done.
    have Ve: valid e. 
    { destruct (~~ is_nil f) eqn:h3.
      + eapply valid_lub_list in h1; eauto.
        eapply valid_fun_subterms; eauto.
        eapply valid_fun_tail; eauto.
      + destruct f; try done. cbn in h1. inversion h1. done.
    }
    destruct (compatible ui u && le ui u) eqn:h2.
    + apply valid_lub in App; eauto using val_valid, valid_fun_head. 
    + cbn in App. inversion App; subst; eauto.
Qed.

(* ------------------------------------------------------- *)

(* Inversion lemmas for le *)

Lemma le_bot_inv : forall u, le u bot -> u = bot.
Proof.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.

Lemma le_tnat_inv : forall u, le tnat u -> u = tnat.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.


Lemma le_zero_inv : forall u, le zero u -> u = zero.
  induction u.
  all: move=> LE1.
  all: cbn in LE1; try done.
Qed.

Lemma le_univ_inv : forall u i, le (tuniv i) u -> u = tuniv i.
  induction u.
  all: move=> i LE1.
  all: cbn in LE1; try done.
  apply Nat.eqb_eq in LE1. subst. done.
Qed.

Lemma le_succ_inv : forall u v, le (succ u) v -> 
                           exists w, v = succ w /\ le u w.
Proof.
  induction u.
  all: move=> v LE1.
  all: try solve [destruct v; cbn; try done; eexists; split; eauto]. 
Qed.

Lemma le_tpi_inv : forall v u f, 
    le (tpi u f) v -> exists w g, v = tpi w g /\ le u w /\ le_fun f g.
Proof.
  destruct v.
  all: move=> u f LE.
  all: try solve [cbn in LE; try done].
  rewrite le_tpi in LE. move: LE => /andP [h1 h2].
  eexists; repeat split; eauto.
Qed.

Lemma le_abs_inv : forall v f, 
    le (abs f) v -> exists g, v = abs g /\ le_fun f g.
Proof.
  destruct v.
  all: move=> f LE.
  all: try solve [cbn in LE; try done].
  rewrite le_abs in LE. 
  eexists; repeat split; eauto.
Qed.


(*
(* comp_sup *)
Lemma lub_compatible_trans u v w x: 
  lub u v = Some w -> compatible x u -> compatible x v -> compatible x w.
Proof.
  move: v w x.
  induction u.
  all: move => v w x.
  all: destruct v; move=>h; inversion h; try done.
  - destruct (n =? n0) eqn:h1; try done.
    inversion H0. subst. auto.
  - destruct (lub u v) eqn:h1; try done.
    cbn in H0. inversion H0. subst.
    destruct x; try done. cbn.
    eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    destruct (lub u v) eqn:h2. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    move=> /andP [hu hl].
    move=> /andP [hv hl0].
    apply /andP. split.
    eauto.
    fold (compatible_fun l1 l) in hl.
    fold (compatible_fun l1 l0) in hl0.
    eapply compatible_append; eauto.
  - cbn in h. destruct x; try done. destruct w; done. 
    destruct (compatible_fun l l0) eqn:h1. 2: done.
    cbn in h. inversion h. subst.
    cbn.
    eapply compatible_append; eauto.
Qed. *)

(* ------------------------------------------------------- *)


Lemma le_fun_tail ui vi f g :
  le_fun ((ui,vi) :: f) g -> le_fun f g.
Proof.
  move=> /forallb_forall h.
  unfold le_fun.
  apply forallb_forall.
  move=> [uj vj] Inf.
  move: (h (uj,vj) ltac:(right; eauto)) => h1.
  done.
Qed.

Lemma le_fun_app_bot f u : 
  le_fun f nil -> (app f u) = Some bot.
Proof.
  induction f as [|[ui vi] f]. cbn. done.
  move=> h1.
  move: (le_fun_tail h1) => h3.
  move: h1 => /andP [h1 _].
  cbn.
  cbn in h1.
  apply le_bot_inv in h1. subst.
  apply IHf in h3.
  unfold app in h3.
  unfold lub_list in h3.
  cbn.
  rewrite h3.
  destruct (compatible ui u && le ui u); done. 
Qed.

Lemma le_fun_nil_compatible f g : 
  le_fun f nil -> compatible_fun f g.
Proof.
  induction f as [|[ui vi] f].
  intro h. done.
  move=> h. 
  move: (le_fun_tail h) => h1.
  move: h => /andP [h _].
  rewrite le_fun_app_bot in h. done.
  apply IHf in h1.
  apply /andP. split. 2: eapply h1.
  apply le_bot_inv in h. subst.
  apply forallb_forall.
  intros [uj vj] Ing.
  apply /implyP. intro h2.
  destruct vj; done.
Qed.

(* comp-sup-sym *)
Lemma compatible_lub a b v w : 
  compatible a v -> compatible b v -> 
  lub a b = Some w -> compatible w v.
Proof.
  move => h1 h2 LUB.
  eapply compatible_sym.
  eapply lub_compatible_trans; eauto.
  eapply compatible_sym; auto.
  eapply compatible_sym; auto.
Qed.

(*

Lemma le_fun_trans_bot f g : 
  le_fun f g -> le_fun g nil -> le_fun f nil.
Proof.
  unfold le_fun.
  move=> /forallb_forall h1.
  move=> /forallb_forall h2.
  apply forallb_forall.
  move=> [ui vi] Inf. 
  specialize (h1 _ Inf). cbn in h1.
  rewrite app_spec. cbn.
  destruct (app g ui) eqn:Ag. 2: done.
  unfold app in Ag.
  have h: { e = bot } + { e <> bot }. admit.
  destruct h as [h|h]. subst. done.
  have [uj [vj [Ing [Leu [Lev NE]]]]]:
    exists uj, exists vj, In (uj, vj) g 
                /\ le uj ui /\ le vj e /\ vj <> bot.
  admit.
  specialize (h2 _ Ing). cbn in h2.
  apply le_bot_inv in h2. subst. 
  done.
Admitted.


Lemma le_fun_nil_compatible f  : le_fun f nil -> forall g, compatible_fun f g.
Admitted.
*)

  
(* ------------------------------------------------------- *)

(*
------------------------------------------------------------------------
-- Part 7f: Comp-down — downward closure of compatibility
--
-- LeCode u u' -> Comp u' v -> Comp u v
*)


Lemma comp_down : 
  forall u u' v, le u u' -> compatible u' v -> compatible u v.
Proof. 
  have LEMMA:
    forall k u u' v, max (rk u) (rk u') <= k -> 
                le u u' -> compatible u' v -> compatible u v.
  { 
    elim /strong_ind.
    move=> m ih.
    have LEMMA0 :
      (*
      EvalFun-guarded-comp : 
        (h : FinFun) (xi : FinEl) (t : Pair FinEl FinEl) ->
        CompFun h (cons t nil) -> Comp xi (fst t) ->
        Comp (EvalFun h xi) (snd t) *)
      forall h xi u w v, 
        (max (rk xi) (rk_fun h) < m)%nat ->
        coherent_with h (u,v) -> 
        compatible xi u -> 
        app h xi = Some w ->
        compatible w v.
    {
      induction h as [|[ui vi] h].
      all: move=> xi u w v RK CH CU APP.
      - cbn in *. inversion APP. subst. cbn. destruct v; done.
      - cbn in CH. move: CH => /andP [h1 h2].
        rewrite app_spec in APP. cbn in APP.
        destruct (compatible ui xi && le ui xi) eqn:LE.
        + destruct app_alt eqn:A; try done. 
          rewrite <- app_spec in A.
          cbn in RK.
          specialize (ih _ RK).
          move: LE => /andP [CC LE].
          (* use comp_down with ui xi and u *)
          move: (ih ui xi u ltac:(lia) LE CU) => h3.
          (* IH for the list *)
          specialize (IHh xi u e v ltac:(lia) h2 CU A).
          move: (@lub_compatible_trans vi e w v APP) => LC.
          eapply compatible_sym. eapply LC.
          move: h1 => /implyP h1. eapply h1. eapply compatible_sym. auto.
          eapply compatible_sym. auto.
        + eapply (IHh xi u w v); eauto.
          cbn in RK. lia.
          rewrite app_spec. done.
    }

    have LEMMA1 : 
      (* Transitivity: LeFunCode g h + CompFun h j -> CompFun g j *)
      (forall g h j, (max (rk_fun g) (rk_fun h) < m)%nat ->
        le_fun g h -> compatible_fun h j -> compatible_fun g j).
    { 
      move=> g.
      induction g as [|[ui vi]g]. done.
      move=> h j RK LE  CF.
      cbn in RK. 
      cbn in LE. move: LE => /andP [LE1 LE2].
      destruct (app h ui) eqn:h2; try done.

      eapply compatible_cons.
      2: { eapply IHg; eauto. lia. }
      (* show coherent_with j (ui,vi) *)
      (*  build-CompStepFun : (s : Pair FinEl FinEl) (j h : FinFun) ->
          LeCode (snd s) (EvalFun h (fst s)) -> CompFun h j -> CompStepFun s j *)
      have build_CompStepFun: forall j,
          compatible_fun h j -> coherent_with j (ui,vi).
      {
        clear j LE2 IHg CF.
        induction j as [|[u v] j].
        move=> CF. done.
        move=> /forallb_forall CF.
        have CJ: (compatible_fun h j).
          { unfold compatible_fun.
          apply forallb_forall. move=> x Inh.
          specialize (CF _ Inh). destruct x as [uk vk]. 
          cbn in CF. 
          move: CF => /andP [h3 h4]. eapply h4. } 
        apply IHj in CJ.
        unfold coherent_with. 
        cbn. apply /andP. split. 2: auto.
        apply /implyP. move => h1.
        move: (LEMMA0 h ui u e v ltac:(lia)) => L0.
        have CH: coherent_with h (u,v).
        { unfold coherent_with. apply forallb_forall.
          move=> [uh vh] Inx. specialize (CF _ Inx).
          cbn in CF. move: CF => /andP [h3 h4].
          apply /implyP. move=> h5.
          eapply compatible_sym. move: h3 => /implyP h3.
          eapply h3. eapply compatible_sym. eauto.
        }
        specialize (L0 CH h1 h2).
        eapply ih. 3: eauto. 3: auto. 2: reflexivity. 
        move: (rk_app h2) => RK2.
        lia.
      }
      specialize (build_CompStepFun _ CF).
      unfold coherent_with in build_CompStepFun.
      move: build_CompStepFun => /forallb_forall CSF.
      move=> uj vj Inj. specialize (CSF _ Inj). cbn in CSF.
      move: CSF => /implyP CSF.
      done.
    } 
 
    move=> u u' v Le.
    destruct u eqn:Eu; destruct u' eqn:Eu'.
    all: try solve [cbn in *; done].
    all: destruct v eqn:Ev; try done.
    all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m0 [-> LL]] end.    
    - subst; cbn. 
      move=> /Nat.eqb_spec -> /Nat.eqb_spec ->. eapply Nat.eqb_refl.
    - rewrite le_succ. cbn in *.
      eapply ih; eauto. 
    - rewrite le_tpi.      
      move=> /andP [h1 h2].
      cbn. fold (compatible_fun l0 l1). fold (compatible_fun l l1).
      move=> /andP [h3 h4].
      cbn in Le. fold rk_fun in Le.
      apply /andP. split. 
      eapply ih; eauto. lia.
      eapply LEMMA1; eauto. lia.
    - rewrite le_abs. 
      cbn. fold (compatible_fun l0 l1). fold (compatible_fun l l1).
      cbn in Le. fold rk_fun in Le.
      eapply LEMMA1; eauto. 
  } 
  move=> u u' v. eapply LEMMA. eauto.
Qed.

(*
-- CoherentWith distributes over append
coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
*)

Lemma coherent_with_append f p g : 
  coherent_with f p -> coherent_with g p -> coherent_with (f ++ g) p.
Proof.
  move:g.
  induction f as [|[ui vi]f].
  all: move=> g CF CG.
  all: cbn. done.
  destruct p as [u v].
  apply /andP.
  move: CF => /andP [h1 h2].
  split; eauto.
Qed.



(*
------------------------------------------------------------------------
-- Part 7h: Coherent-EvalFun
--
-- Comp-value-EvalFun: proved using LeCode-Comp and comp-Sup.

 Comp-value-EvalFun : (q : Pair FinEl FinEl) 
    (rest : FinFun) (xi : FinEl) ->
    LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
    CoherentWith q rest -> CompStepFun q rest ->
    Comp (snd q) (EvalFun rest xi)
*)

Lemma Comp_value_app f : forall u v xi w,
  compatible u xi ->
  coherent_with f (u,v) -> 
  app f xi = Some w ->
  compatible v w.
Proof.
  induction f as [|[ui vi] h].
  all: move=> u v xi w CC CH APP.
  - cbn in *. inversion APP. subst. cbn. destruct v; done.
  - cbn in CH. move: CH => /andP [/implyP h1 h2].
    rewrite app_spec in APP. cbn in APP. rewrite <- app_spec in APP. 
    destruct (compatible ui xi && le ui xi) eqn:LE2. 2: eapply IHh; eauto.
    destruct app eqn:A; try done. 
    specialize (IHh u v xi e CC h2 A).
    move: LE2 => /andP [CC2 LE2].
    move: (@lub_compatible_trans vi e w v APP) => LC.
    eapply LC; eauto.
    eapply h1.
    eapply compatible_sym.
    eapply (@comp_down ui xi u LE2).
    eapply compatible_sym.
    auto.
Qed.

Lemma valid_app_exists {f u} :
  valid_fun f ->
  valid u -> 
  exists w, app f u = Some w /\ valid w.
Proof.
  move: u.
  induction f as [|[ui vi]f].
  all: move=> u Vf Vu.
  - exists bot. cbn. split; auto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (~~ is_nil f) eqn:h1.
    + specialize (IHf u ltac:(eauto using valid_fun_tail) Vu).
      destruct (compatible ui u && le ui u) eqn:LE1; auto.
      move: LE1 => /andP [CC1 LE1].
      destruct IHf as [w [APP vw]].
      rewrite APP.
      have CC: (compatible vi w).
      { 
        eapply Comp_value_app in CC1; eauto.
        eapply compat. eapply valid_fun_head. eauto.
      } 
      destruct (compatible_lub_exists CC) as [w1 EQ].
      exists w1. split. done.
      eapply valid_lub in EQ; eauto.
      eauto using val_valid, valid_fun_head.
    + destruct f; try done.
      destruct (compatible ui u && le ui u) eqn:LE1.
      ++ cbn. exists vi. rewrite lub_bot_r. split. done.
         eauto using val_valid, valid_fun_head.         
      ++ cbn. exists bot. done.
Qed.

Lemma valid_app_compatible f u :
  valid_fun f -> 
  valid u -> 
  exists w, app f u = Some w /\ valid w /\ 
         (* basically coherent_with f (u,w) *)
         (forall ui vi, In (ui,vi) f -> compatible ui u && le ui u -> compatible vi w).
Proof.
  move: u.
  induction f as [|[ui vi]f].
  all: move=> u Vf Vu.
  - exists bot. cbn. split; auto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    destruct (~~ is_nil f) eqn:h1.
    + specialize (IHf u ltac:(eauto using valid_fun_tail) Vu).
      destruct IHf as [w [APP [vw CA]]].
      destruct (compatible ui u && le ui u) eqn:LE1; auto.
      ++ (* ui is compatible with u, so vi is part of w *)
         move: LE1 => /andP [CC1 LE1].
         rewrite APP.
         have CC: (compatible vi w).
         { 
           eapply Comp_value_app in CC1; eauto.
           eapply compat. eapply valid_fun_head. eauto.
         } 
         destruct (compatible_lub_exists CC) as [w1 EQ].
         exists w1. split. done.
         split.
         eapply valid_lub in EQ; eauto.
         eauto using val_valid, valid_fun_head.
         move=> uj vj [h2|h2]. 
         -- inversion h2. subst. move=> _.
            move: (@lub_compatible_trans vj w w1 vj EQ)=> h3.
            eapply h3.
            eapply compatible_refl. eapply val_valid. eapply valid_fun_head. eauto.
            eauto.
         -- specialize (CA _ _ h2). move=> h3. specialize (CA h3).
            move: h3 => /andP [h3 h7].
            move: (@lub_compatible_trans vi w w1 vj EQ)=> h4.
            eapply h4.
            move: (compat (valid_fun_head Vf)) => /forallb_forall h5.
            specialize (h5 _ h2). cbn in h5. move: h5 => /implyP h5.
            eapply compatible_sym.
            eapply h5.
            move: (@comp_down ui u) => h6. eapply h6; eauto.
            eapply compatible_sym. eauto.
            eauto.
       ++ exists w. repeat split; eauto.
          move=> uj vj [h2|h2].
          --- move=> h3. inversion h2; subst uj. subst vj. clear h2. 
              rewrite LE1 in h3. done.
          --- move=> h3. eapply CA; eauto.
     + destruct f; try done.
      destruct (compatible ui u && le ui u) eqn:LE1.
      ++ cbn. exists vi. rewrite lub_bot_r. repeat split. 
         eauto using val_valid, valid_fun_head.         
         move=> uj vj [h|h]. 2: done. inversion h. subst.
         move=> h2. eapply compatible_refl. eauto using val_valid, valid_fun_head.
      ++ cbn. exists bot. repeat split; eauto.
         move=> uj vj [h|h]. 2: done. inversion h. subst.
         move=> h2. destruct vj; done.
Qed.


(* Need to know not just that the app exists, but 
   that it is *compatible* with v. 
   Intuitively, w is the lub of several elements in f that includes v.
 *)
Lemma valid_app_cons_compatible f u v :
  le u u -> 
  valid_fun ((u,v) :: f) -> exists w, app f u = Some w /\ valid w /\ compatible w v.
Proof.
  move=> LE h.
  have Vu: valid u. eauto using key_valid, valid_fun_head.
  move: (valid_app_compatible h Vu) =>  [w [EQ [Vw h3]]].
  specialize (h3 u v ltac:(left; eauto)). 
  rewrite app_spec in EQ. cbn in EQ. rewrite <- app_spec in EQ.
  rewrite compatible_refl in EQ; eauto. cbn in EQ.
  rewrite LE in EQ.
  destruct (app f u) eqn:h2. 2: done.
  exists e. 
  split; eauto. split. 
  -- destruct (~~ is_nil f) eqn:h4.
     ++ move: (valid_fun_tail h h4) => h5.    
        eapply (valid_app h5 Vu); eauto.
     ++ destruct f ; try done. cbn in h2. inversion h2. done.
  -- eapply compatible_sym. eapply lub_compatible; eauto.
Qed.

(*
-----------------------------------------------------------------------
-- Part 7h: Coherent-Sup and Coherent-EvalFun
------------------------------------------------------------------------

-- comp-EvalFun: evaluations of compatible functions at the same point
-- are compatible.
{-# TERMINATING #-}
mutual
  comp-EvalFun : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Comp (EvalFun k xi) (EvalFun h xi)
*)

Lemma compatible_app k : forall h xi w1 w2,
  compatible_fun k h -> 
  app k xi = Some w1 -> 
  app h xi = Some w2 -> compatible w1 w2.
Proof.
  induction k as [|[ui vi] k].
  all: move=> h xi w1 w2 CF A1 A2.
  - cbn in A1. inversion A1. subst. destruct w2; done.
  - cbn in CF. move: CF => /andP [h1 h2].
    rewrite app_spec in A1. cbn in A1. rewrite <- app_spec in A1.
    destruct (compatible ui xi && le ui xi) eqn:LE. 2: { eapply IHk; eauto. } 
    destruct (app k xi) eqn:A3. 2: done.
    specialize (IHk _ _ _ _ h2 A3 A2).
    apply compatible_sym in IHk. apply compatible_sym.
    move: (@lub_compatible_trans vi e w1 w2 A1) => h3.
    eapply h3; eauto.
    move: LE => /andP [CC LE].
    move: (@Comp_value_app h ui vi xi w2 CC) => h4.
    eapply compatible_sym.
    eapply h4; eauto.
Qed.

  

(* 
 EvalFun-append-eq : (k h : FinFun) (xi : FinEl) ->
    CompFun k h -> CoherentFunTail k -> Coherent xi ->
    Eq (EvalFun (append k h) xi) (Sup (EvalFun k xi) (EvalFun h xi))
*)
Lemma app_append_eq k : forall h xi, compatible_fun k h -> 
  forall w1 w2, app k xi = Some w1 -> 
           app h xi = Some w2 ->
  exists w, app (k ++ h) xi = Some w /\ lub w1 w2 = Some w.
Proof.
  induction k as [|[u v]k].
  all: move=> h xi CF w1 w2 AP1 AP2.
  - move: (@le_fun_app_bot nil xi ltac:(done)) => h1. 
    rewrite h1 in AP1. inversion AP1. subst. clear AP1.
    rewrite app_nil_l. rewrite AP2. cbn. exists w2.  eauto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite app_spec in AP1. cbn in AP1. rewrite <- app_spec in AP1.
    move: CF => /andP [h1 h2].
    destruct (compatible u xi && le u xi) eqn:LE.
    + destruct (app k xi) eqn:A3; try done.
      edestruct IHk as [w [E1 E2]]; eauto.
      clear h2. rewrite E1.
      (* at this point we have 

                    w1    (k+h)[xi]=w
                   /   \  /     \
                 v   k[xi]=e    h[xi]=w2

         we need to show that  lub v w == lub w1 w2
           i.e. lub v w == lub v (lub e w2)
                        == lub (lub v e) w2
                        == lub w1 w2

       *)
      admit.
    + admit. (* erewrite IHk; eauto. *)
Abort.


Lemma app_append_eq k : forall h xi, compatible_fun k h -> 
  forall w1 w2, app k xi = Some w1 -> 
           app h xi = Some w2 ->
  app (k ++ h) xi = lub w1 w2.
Proof.
  induction k as [|[u v]k].
  all: move=> h xi CF w1 w2 AP1 AP2.
  - move: (@le_fun_app_bot nil xi ltac:(done)) => h1. 
    rewrite h1 in AP1. inversion AP1. subst. clear AP1.
    rewrite app_nil_l. rewrite AP2. cbn.  eauto.
  - rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite app_spec in AP1. cbn in AP1. rewrite <- app_spec in AP1.
    move: CF => /andP [h1 h2].
    destruct (compatible u xi && le u xi) eqn:LE.
    + destruct (app k xi) eqn:A3; try done.
      erewrite IHk; eauto. clear h2.
      destruct (lub e w2) eqn:L4.
      move: (lub_assoc AP1 L4) => h2. rewrite h2. done.
      move: (lub_assoc_None AP1 L4) => h2. rewrite h2. done.
    + erewrite IHk; eauto. 
Qed.


(*
------------------------------------------------------------------------
-- Part 7i: Order-theoretic lemmas
--
*)

(* 
*LeCode-refl : (a : FinEl) -> Coherent a -> LeCode a a
**LeFunCode-refl : (g : FinFun) -> CoherentFunTail g -> LeFunCode g g
* LeCode-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a ->    Coherent b ->
    LeCode a (Sup a b)
LeCode-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    LeCode b (Sup a b)
* LeCode-trans : (x y z : FinEl) -> Coherent x -> Coherent y -> Coherent z ->
    LeCode x y -> LeCode y z -> LeCode x z
LeFunCode-trans : (g h k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CoherentFunTail k ->
    LeFunCode g h -> LeFunCode h k -> LeFunCode g k
LeFunCode-nil-any : (g k : FinFun) ->
    CoherentFunTail g -> CoherentFunTail k -> LeFunCode g nil -> LeFunCode g k
EvalFun-mon : (h k : FinFun) (u : FinEl) ->
    CoherentFunTail h -> CoherentFunTail k -> Coherent u ->
    LeFunCode h k -> LeCode (EvalFun h u) (EvalFun k u)

 -- Sup is LUB: a ≤ c and b ≤ c implies Sup a b ≤ c
** LeCode-Sup-lub : (a b c : FinEl) -> LeCode a c -> LeCode b c ->
    LeCode (Sup a b) c
LeFunCode-append-combine : (g h k : FinFun) ->
    LeFunCode g k -> LeFunCode h k -> LeFunCode (append g h) k
** LeFunCode-append-left : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode g (append g h)
LeFunCode-append-right : (g h : FinFun) -> CompFun g h ->
    CoherentFunTail g -> CoherentFunTail h ->
    LeFunCode h (append g h)
*)

Record OrderTheoreticLemmas k := MkLemmas { 
  le_refl : forall a, rk a <= k -> valid a -> le a a ;

  le_lub_left : forall a b, max (rk a) (rk b) <= k -> 
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le a w ;

  le_lub_right : forall a b, max (rk a) (rk b) <= k -> 
     compatible a b -> forall w, lub a b = Some w -> 
     valid a -> valid b -> le b w ;

  le_trans : forall u v w, max (rk u) (rk v) <= k -> 
     valid u -> valid v -> valid w -> le u v -> le v w -> le u w ;

  (* lub is the Least Upper Bound *)
  le_sup_lub : forall u v w1 w2, le u w2 -> le v w2 -> lub u v = Some w1 ->
                            le w1 w2

}.


Lemma OTLs : forall k, OrderTheoreticLemmas k.
Proof.
  elim /strong_ind.
  move=> m ih.

  have le_fun_mono_arg:
    forall h u1 u2, (max (max (rk_fun h) (rk u1)) (rk u2) < m)%nat -> 
           valid_fun h -> valid u1 -> valid u2 ->
           forall w1 w2, app h u1 = Some w1 -> app h u2 = Some w2 -> 
                    le w1 w2.
  { admit. }


  have le_fun_mono : 
    forall h k u, (max (max (rk_fun h) (rk_fun k)) (rk u) < m)%nat -> 
           valid_fun h -> valid_fun k -> 
           le_fun h k -> valid u ->  
           forall w1 w2, app h u = Some w1 -> app k u = Some w2 -> 
                    le w1 w2.
  { 
    induction h as [|[ui vi]h].
    all: move=> k u RK Vf Vk LE Vu w1 w2 EQ A2.
    - inversion EQ. done.
    - rewrite app_spec in EQ. cbn in EQ. rewrite <- app_spec in EQ.
      cbn in RK. move: (rk_app A2) => Rw2.
      have Leu: le u u. { eapply le_refl. eapply (ih _ RK). lia. eauto. }
      have Leui: le ui ui. { eapply le_refl. eapply (ih _ RK). lia.
             eauto using key_valid, valid_fun_head. }

      destruct (compatible ui u && le ui u) eqn:LEui.
      + move: LEui => /andP [Cui LEui].
        have Vui: valid ui. eauto using valid_fun_head, key_valid.
        have Vvi: valid vi. eauto using valid_fun_head, val_valid.

        destruct (~~ is_nil h) eqn:Nh.
        ++ have Vh: valid_fun h. eauto using valid_fun_tail.

           move: LE => /andP [L1 L2]. cbn in RK.
           (* L1: k[ui] <= v   
              L2: h     <= k  *)

           destruct (valid_app_compatible Vh Vu) as 
             [e1 [A1 [Ve1 CC1]]].
           rewrite A1 in EQ.
           move: (rk_app A1) => Re.

           destruct (valid_app_compatible Vk Vu) as 
             [e3 [A3 [Ve2 _]]]. rewrite A2 in A3. 
           inversion A3. subst e3. clear A3.

           destruct (valid_app_compatible Vk Vui) as 
             [e4 [A4 [Ve4 _]]]. rewrite A4 in L1.

           move: (rk_app A4) => Re4.

           destruct (valid_app_cons_compatible Leui Vf) as
             [e5 [A5 [Ve5 _]]].

           have L3: le e1 w2.
           { eapply (IHh k u); eauto. lia. } 

           have L4: le e4 w2.
           { eapply (le_fun_mono_arg k ui u); eauto. lia. }

           have L5: le vi w2.
           { eapply (le_trans (ih _ RK)(v:=e4)); eauto. lia. } 

           eapply (le_sup_lub (ih _ RK) L5 L3); eauto.

        ++ destruct h; try done.
           cbn in EQ. inversion EQ. clear EQ. 
           rewrite lub_bot_r in H0. inversion H0. subst. clear H0.
           cbn in LE. destruct (app k ui) eqn:A1. 2: done.
           move: LE => /andP [L1 _].
           have L2: le e w2.
           { eapply (le_fun_mono_arg k ui u); eauto. lia. } 

           move: (rk_app A1) => Re.
           move: (le_trans (ih _ RK)(u:=w1)(v:=e)(w:=w2)) => h. 
           eapply h; eauto using valid_app. lia.

      + destruct (~~ is_nil h) eqn:Nh.
        ++ eapply IHh; eauto.        
           cbn in RK; lia.
           eauto using valid_fun_tail.
           cbn in LE. move: LE => /andP [_ LE]. eapply LE.
        ++ destruct h; try done.
           inversion EQ. eapply le_bot.
  }

  have le_fun_cons_right : 
    forall f u v, (max (rk_fun f) (max (rk u) (rk v)) < m)%nat ->
           valid_fun f -> valid u -> valid v 
           -> coherent_with f (u,v) -> le_fun f ((u,v) :: f).
  {
    admit.
  } 

  have le_fun_extend_left : 
    forall f g, (max (rk_fun f) (rk_fun g) < m)%nat ->
           valid_fun f -> valid_fun g 
           -> compatible_fun f g -> le_fun f (f ++ g).
  {
    induction f as [|[u v]f].
    all: move=> g RK Vf Vg Cfg. done.
    cbn in RK.
    specialize (ih _ RK). 
    specialize (IHf g ltac:(lia)).
    rewrite le_cons.
    rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite compatible_cons_def in Cfg.
    fold (coherent_with g (u, v)) in Cfg.
    have Vu : valid u. eauto using key_valid, valid_fun_head.
    have Vv : valid v. eauto using val_valid, valid_fun_head.

    move: Cfg => /andP [h1 Cfg].
    have CU: compatible u u. eapply compatible_refl; eauto.
    have LU: le u u. eapply le_refl; eauto. lia.
    rewrite CU.
    rewrite LU.
    cbn.
    destruct (~~ is_nil f) eqn:Nf.
    have Vt: valid_fun f. eapply valid_fun_tail; eauto.
    destruct (valid_app_exists Vt Vu) as [w1 [EQ1 Vw1]].
    destruct (valid_app_exists Vg Vu) as [w2 [EQ2 Vw2]].
    move: (app_append_eq Cfg EQ1 EQ2) => EQ3. 
    admit.
    admit.
  } 

  have le_fun_refl f :
    (rk_fun f < m)%nat -> valid_fun f -> le_fun f f.
  {
    induction f as [|[u v]f].
    all: move=> RK Vf. done. 
    cbn in RK.
    have Vu: valid u. eauto using valid_fun_head, key_valid.
    have Vv: valid v. eauto using valid_fun_head, val_valid.
    rewrite le_cons.
    rewrite app_spec. cbn. rewrite <- app_spec.
    rewrite compatible_refl; eauto.
    erewrite le_refl; eauto. 2: lia.
    cbn. 
    destruct (~~ is_nil f) eqn:Nf.
    + move: (valid_fun_tail Vf Nf) => Vt.
      have LEu: le u u. eapply le_refl; eauto. lia.
      destruct (valid_app_cons_compatible LEu Vf) as [w [E1 [Vw Cw]]].
      rewrite E1.
      apply compatible_sym in Cw.
      destruct (compatible_lub_exists Cw) as [w0 Lub].
      rewrite Lub.
      apply rk_app in E1.
      erewrite le_lub_left; eauto. 2: lia. cbn.
      have Lf: le_fun f f. eapply IHf; eauto. lia.
      eapply (le_fun_cons_right f u v); eauto. lia.
      eapply compat. eapply valid_fun_head; eauto.
    + destruct f; try done.
      cbn. rewrite lub_bot_r.
      erewrite le_refl; eauto. lia.
  }

  have le_fun_trans : 
    forall g h k, (max (max (rk_fun g) (rk_fun h)) (rk_fun k) < m)%nat -> 
             valid_fun g -> valid_fun h -> valid_fun k ->
             le_fun g h -> le_fun h k -> le_fun g k.
     { 
       induction g as [|[u v]g].
       all: move=>h k RK Vug Vh Vk h1 h2.
       - done.
       - move: h1 => /andP [h1 Lgh]. 
         have Vu: valid u. eauto using key_valid, valid_fun_head.
         have Vv: valid v. eauto using val_valid, valid_fun_head.
         apply /andP. split.
         + clear IHg Lgh.
           (* use le_trans for u,v *)
           destruct (valid_app_compatible Vh Vu) as [wh [Ahu [Vwh Cwh]]].
           rewrite Ahu in h1. 
           destruct (valid_app_compatible Vk Vu) as [wk [Aku [Vwk Cwk]]].
           rewrite Aku.
           have: le wh wk.
           { unfold le_fun in h2.
             move: h2 => /forallb_forall h2. 
           specialize (h2 
           have h3: le u u. eapply le_refl; eauto. cbn. lia.
           destruct (valid_app_cons_compatible h3 Vug) as
             [wg' [Agu [Vwg' Cwg']]]. clear h3.
           destruct (compatible_lub_exists Cwg') as [wg EQ].
           move: (rk_app Agu) => RKwg.
           move: (@le_lub_right _ (ih _ RK) wg' v ltac:(cbn;lia)
                     Cwg' _ EQ ltac:(eauto) ltac:(auto)) => LE.

         + destruct (~~ is_nil g) eqn:Nf.
           (* use ih for g for tail of list *) 
           have Vg: valid_fun g. eauto using valid_fun_tail.
           cbn in RK. specialize (IHg h k ltac:(lia) Vg Vh Vk Lgh h2).
           clear Lgh h2.
           apply /andP; split; auto.
         

      apply /forallb_forall. move=> [ui vi] Inf.
      specialize (h1 _ Inf). cbn in h1.
      destruct (app g ui) eqn:EQg; try done.

      have Vui: valid ui. {
        move: Vf => /andP [_ /forallb_forall Vf].
        specialize (Vf _ Inf). cbn in Vf.
        move: Vf => /andP [Vu Vv]. done.
      }
      move: (valid_app_exists Vh Vui) => [w [EQ Vw]].
      rewrite EQ.
      admit.
     } 

  constructor.

  - (* le_refl *)
    move=> a RK Va.
    destruct a.
    all: cbn in RK.
    all: try solve [cbn;done].
    + cbn. eapply Nat.eqb_refl.
    + rewrite le_succ. 
      specialize (ih (rk a)).
      eapply le_refl; eauto.
    + fold rk_fun in RK. rewrite le_tpi.
      move: Va => /andP [Va Vl]. fold valid in Va.
      fold valid in Vl.
      specialize (ih (max (rk a) (rk_fun l))).
      apply /andP. split. eapply le_refl; eauto. lia.
      eapply le_fun_refl; eauto. lia.
    + rewrite le_abs.
      cbn in Va.
      eapply le_fun_refl; eauto.

  - (* le_lub_left *)
    move=> u.
    induction u.
    all: move=> v RK Cu w h Vu Vv.
    all: try solve [destruct w; try done].
    all: try solve [destruct v; inversion h; subst; auto].
    + (* univ *)
    destruct v; inversion h; subst; cbn in *. 
    apply Nat.eqb_refl. 
    destruct (n =? n0) eqn:EQ; try done.
    inversion H0. cbn. apply Nat.eqb_refl.
    + (* succ *)
    destruct v; inversion h; subst; cbn in *. 
    ++ (* needs le_refl *) eapply le_refl; eauto. 
    ++ destruct (lub u v) eqn:EQ; try done. 
      inversion H0. subst. cbn. eapply IHu; eauto. lia.
     (* tpi *)
    + cbn in RK. fold rk_fun in RK.
      move: Vu => /andP [h1 h2].
      fold valid in *. fold (valid_fun l) in h2.
      destruct v; cbn in h; inversion h; subst; cbn in RK.      
      ++ (* needs le_refl *)
        rewrite le_tpi.
        apply /andP. split. eapply le_refl; eauto.  lia.
        eapply le_fun_refl; eauto. lia.
      ++ destruct (compatible_fun l l0) eqn:E. 2: done.
         destruct (lub u v) eqn:E2. 2: done.
         cbn in h. inversion h. 
         move: Vv => /andP [Vv Vl0].
         fold valid in *. fold (valid_fun l0) in Vl0.
         move: Cu => /andP [Cu Cl]. 
         fold compatible in *. 
         rewrite le_tpi. apply /andP. split; eauto. 
         eapply le_lub_left; eauto. lia.
         eapply le_fun_extend_left; eauto. fold rk_fun in RK. lia.
    + (* abs *)
      destruct v; cbn in h; inversion h; subst.
      ++ cbn in Vu. 
         rewrite le_abs. eapply le_fun_refl; eauto.
      ++ destruct (compatible_fun l l0) eqn:E. 2: done.
         cbn in h. inversion h.
         rewrite le_abs. 
         cbn in RK. fold rk_fun in RK.
         eapply le_fun_extend_left; eauto. 

  - (* le_lub_right *)
    admit.

  - (* le_trans *)
    admit.

Admitted.

Qed.


eapply le_refl.



(* check out: Comp-value-EvalFun *)



(* all of these lemmas have holes in them. maybe they need to be proven 
   simultaneously??? *)

Axiom le_refl : forall u, valid u -> le u u.

Axiom le_fun_refl : forall f, valid_fun f -> le_fun f f. 

Axiom valid_app_exists : forall f u,
  valid_fun f -> valid u ->
  { w | app f u = Some w }.

Axiom le_fun_extend :
  forall f g, 
  valid_fun f -> valid_fun g -> compatible_fun f g -> le_fun f (f ++ g).

Axiom le_trans : 
  forall u v w, valid u -> valid v -> valid w -> le u v -> le v w -> le u w.

Axiom lub_le_l : forall u v w, valid u -> valid v -> 
                          lub u v = Some w -> le u w = true.

(*
(* If an application is defined, and is not bot, then there 
   must be some tuple in the finite function that contributes to it. 
   If it is bot, then maybe there is no tuple.
   *)

Axiom tuple_exists : forall g u w, 
    valid u -> valid w -> 
    app_alt g u = Some w -> w <> bot ->
     exists ui, exists vi, In (ui,vi) g /\ le vi w /\ le ui u.
Lemma tuple_exists' g u w : 
  valid u -> valid w -> 
  app_alt g u = Some w -> w <> bot ->
     exists ui, exists vi, In (ui,vi) g /\ le vi w /\ le ui u.
Proof.
  move:u w.
  induction g.
  cbn. 
  - move=> u w Vu Vw h. inversion h. done.
  - move=> u w Vu Vw h Ne. cbn in h.
    destruct a as [ui vi].
    destruct (app_alt g u) eqn: h1. 2: { destruct (le ui u); done. } 
    destruct (le ui u) eqn: h2.
    + exists ui. exists vi. split; auto. left. done. split.
      eapply lub_le_l. admit. admit. eauto. auto.
    + inversion h. subst. 
      destruct (IHg _ _ Vu Vw h1 Ne) as [uj [vj [h3 h4]]].
      exists uj. exists vj.
      split. right. auto. auto.
Admitted.
*)

(* application is total for compatible functions *)
Lemma valid_app_exists' f u :
  valid_fun f -> valid u -> { w | app f u = Some w }.
Proof.
  move=> Vf Vu.
  move: (valid_fun_compatible Vf) => Cf.
  unfold app.
  remember (map (fun '(ui,vi) => if le ui u then vi else bot) f) as l.
  eapply pairwise_lub_exists.
  subst. 
  unfold pairwise_compatible.
  have Cff: compatible_fun f f. exact Cf.
  unfold compatible_fun in Cf.
  move: Cf => /forallb_forall Cf.
  apply /forallb_forall.
  move=> x Inx. 
  rewrite in_map_iff in Inx.
  destruct Inx as [[ui vi] [h1 h2]].
  specialize (Cf _ h2). cbn in Cf.
  move: Cf => /forallb_forall Cf.
  apply /forallb_forall.
  move=> y Iny. 
  rewrite in_map_iff in Iny.
  destruct Iny as [[uj vj] [h3 h4]].
  specialize (Cf _ h4). cbn in Cf.
  destruct (le ui u) eqn:h5; 
  destruct (le uj u) eqn:h6; subst; cbn.
  move: Cf => /implyP Cf.
  eapply Cf.
  eapply bounded_compatible; eauto.
  destruct x; done.
  destruct y; done.
  done.
Qed.

(*
Lemma valid_pairwise f u : 
  valid_fun f -> 
  pairwise_compatible 
    (map (fun '(ui, vi) => if le ui u then vi else bot) f). 
Proof.
  move=> Vf.
  remember (map (fun '(ui, vi) => if le ui u then vi else bot) f) as g.
  unfold pairwise_compatible.
  apply /forallb_forall. 
  move=> x Ingx.
  have Ingx': In x g. auto.
  apply /forallb_forall.
  move=> y Ingy.
  have Ingy': In y g. auto.
  subst.
  rewrite -> in_map_iff in Ingx'.
  rewrite -> in_map_iff in Ingy'.
  move: Ingx' => [[ux vx] [hx1 hx2]].
  move: Ingy' => [[uy vy] [hy1 hy2]].
  move: (valid_fun_compatible Vf) => /forallb_forall Cf. 
  specialize (Cf _ hx2). cbn in Cf.
  move: Cf => /forallb_forall Cf.
  specialize (Cf _ hy2). cbn in Cf.
  move: Cf => /implyP Cf.
  destruct (le ux u) eqn:h3;
    destruct (le uy u) eqn:h4; subst.
  - eapply Cf.
    eapply bounded_compatible; eauto.
  - destruct x; done.
  - destruct y; done.
  - done.
Qed.
*)

Lemma valid_tpi a f : 
  valid (tpi a f) = valid a && valid_fun f.
reflexivity. Qed.

(** le is trainsitive *)
Lemma le_trans' : 
  forall u v w, valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
Proof.
  have lemma: 
    forall k, forall u v w, max (rk u) (rk v) <= k ->
                  valid u -> valid v -> valid w -> le u v -> le v w -> le u w.
  {
    elim /strong_ind.
    move=> m ih.
    have lemma2: forall f g h, (max (rk_fun f) (rk_fun g) < m)%nat -> 
                 valid_fun f -> valid_fun g -> valid_fun h ->
                 le_fun f g -> le_fun g h -> le_fun f h.
     { 
      move=> f g h M Vf Vg Vh /forallb_forall h1 /forallb_forall h2.
      apply /forallb_forall. move=> [ui vi] Inf.
      specialize (h1 _ Inf). cbn in h1.
      destruct (app g ui) eqn:EQg; try done.
      unfold app in EQg.
      have Vui: valid ui. { admit.  } 
      move: (valid_app_exists Vh Vui) => [w EQ].
      rewrite EQ.
      admit.
     }
    move=> u v w h Vu Vv Vw L1 L2.
    destruct u; destruct v; destruct w; try done.
    - admit.
    - rewrite le_succ in L1. rewrite le_succ in L2.
      cbn in h. rewrite le_succ.
      eapply ih; eauto.
    - rewrite le_tpi in L1. 
      move: L1 => /andP [L1 L3].
      rewrite le_tpi in L2.
      move: L2 => /andP [L2 L4].
      rewrite valid_tpi in Vu. 
      move: Vu => /andP [Vu Vl]. 
      rewrite valid_tpi in Vv. 
      move: Vv => /andP [Vv Vl0]. 
      rewrite valid_tpi in Vw. 
      move: Vw => /andP [Vw Vl1]. 

      cbn in h. fold rk_fun in h.
      
      rewrite le_tpi.
      erewrite ih; eauto. cbn. 
      eapply lemma2; eauto. all: try lia.
      all: admit.
    - rewrite le_abs in L1. rewrite le_abs in L2.
      rewrite le_abs. eapply lemma2; eauto. 
      cbn in h. fold rk_fun in h. 
      all: admit.
  } 
  intros. eapply lemma; eauto.
Admitted.


Lemma le_fun_extend' :
  forall f g, 
  valid_fun f -> valid_fun g -> compatible_fun f g -> le_fun f (f ++ g).
Proof.
  move=> f g Vf Vg Cfg. 
  unfold le_fun.
  apply /forallb_forall.
  move=> [u v] Inf.
  have Vu: valid u. admit.
  have Vv: valid v. admit.
  have [fu [h1 [h2 Vfu]]] : exists e, app f u = Some e /\ le v e /\ valid e.
  { move: (le_fun_refl Vf) => /forallb_forall h. 
    specialize (h _ Inf). cbn in h.
    destruct (app f u) eqn:h1.
    exists e. repeat split; eauto. admit. done. } 
  erewrite app_append; try reflexivity.
  destruct (valid_app_exists (u := u) Vg) as [gu EQ]; auto.
  have lemma: forall f g u,
    compatible_fun f g -> 
    app f u = Some fu ->
    app g u = Some gu -> 
    compatible fu gu.
  { clear.
    admit.
  }
  move: (lemma _ _ _ Cfg h1 EQ) => CC.
  destruct (compatible_lub_exists CC) as [w h3].
  rewrite h1. rewrite EQ. cbn. rewrite h3.
  eapply (le_trans (u:=v) (v:=fu) (w:=w)); eauto.
  admit. (* valid w *)
  eapply (lub_le_l (u:= fu) (v:=gu) (w:=w)); eauto.
  admit. (* valid gu *)
Admitted.


(** valid functions are reflexive **)
Lemma le_fun_refl' : 
  forall f, valid_fun f -> le_fun f f.
Proof.
  move=> f Vf.
  apply /forallb_forall. move=> [u v] Inf.
  have Vu: valid u. admit.
  have Vv: valid v. admit.
  move: (valid_app_exists Vf Vu) => [w EQ]. rewrite EQ.
  rewrite app_spec in EQ.
  move: EQ Inf.
  induction f.
  - cbn. done.
  - destruct a as [ui vi]. cbn.
    move=> h.
Admitted.

(* lub is an upper bound for its left argument *)
Lemma lub_le_l' : 
  forall u v w, valid u -> valid v -> lub u v = Some w -> le u w = true.
Proof.
  induction u.
  all: move=> v w Vu Vv h.
  all: try solve [destruct w; try done].
  all: try solve [destruct v; inversion h; subst; auto].
  - (* univ *)
    destruct v; inversion h; subst; cbn in *. 
    apply Nat.eqb_refl. 
    destruct (n =? n0) eqn:EQ; try done.
    inversion H0. cbn. apply Nat.eqb_refl.
  - (* succ *)
    destruct v; inversion h; subst; cbn in *. 
    + (* needs le_refl *) eapply le_refl; eauto. 
    + destruct (lub u v) eqn:EQ; try done. 
      inversion H0. subst. cbn. eapply IHu; eauto.
  - (* tpi *)
    destruct v; cbn in h; inversion h; subst.
    + (* needs le_refl *) eapply le_refl; eauto.
    + destruct (compatible_fun l l0) eqn:E. 2: done.
      destruct (lub u v) eqn:E2. 2: done.
      cbn in h. inversion h. 
      move: Vu => /andP [Vu Vl]. 
      move: Vv => /andP [Vv Vl0].
      fold valid in *. fold (valid_fun l) in Vl. fold (valid_fun l0) in Vl0.
      rewrite le_tpi. apply /andP. split; eauto. 
      (* needs le_fun_extend *)
      eapply le_fun_extend; eauto.
  - (* abs *)
    destruct v; cbn in h; inversion h; subst.
    + (* needs le_refl *) eapply le_refl; eauto.
    + destruct (compatible_fun l l0) eqn:E. 2: done.
      cbn in h. inversion h.
      rewrite le_abs. eapply le_fun_extend; eauto.
Qed.


(* This isn't quite right yet. *)
Lemma bounded_compatible': forall u ui uj, 
    le ui u -> le uj u -> compatible ui uj.
have lemma:
  forall k, forall u ui uj, max (rk ui) (max (rk uj) (rk u)) <= k ->
                  le ui u -> le uj u -> compatible ui uj.
  {
  elim /strong_ind. move=> m ih.
  have lemma :
    forall f fi fj,
      (max (rk_fun fi) (max (rk_fun fj) (rk_fun f)) < m)%nat ->
                  le_fun fi f -> le_fun fj f -> compatible_fun fi fj.
  {
    move=> f fi fj h hi hj.
    unfold compatible_fun.
    apply /forallb_forall.
    move=> [ui vi] Infi.
    apply /forallb_forall.
    move=> [uj vj] Infj.
    apply /implyP. move=> Ci.
    move: hi => /forallb_forall hi.
    specialize (hi _ Infi). cbn in hi.
    move: hj => /forallb_forall hj.
    specialize (hj _ Infj). cbn in hj.
    destruct (app f ui) eqn:Ai. 2: done.
    destruct (app f uj) eqn:Aj. 2: done.
    move: (rk_app Ai) => rke.
    move: (rk_app Aj) => rke0.
    admit. (* ???? *)
  } 
  move=> u ui uj Le h1 h2.
  destruct ui; destruct uj; destruct u; try done. 
  - cbn. cbn in h1. cbn in h2. admit. (* ok *)
  - cbn in h1. cbn in h2. cbn. eapply ih; eauto. cbn in Le. lia.
  - rewrite le_tpi in h1. rewrite le_tpi in h2. cbn.
    cbn in Le. fold rk_fun in Le.
    move: h1 => /andP [h11 h12].
    move: h2 => /andP [h21 h22].
    apply /andP. split.
    eapply ih; eauto. lia.
    eapply lemma; eauto. lia.
  - rewrite le_abs in h1. rewrite le_abs in h2.
    cbn. cbn in Le. fold rk_fun in Le.
    eapply lemma; eauto. 
  } 
  intros; eapply lemma; eauto.
Admitted.

(* -------------------------------------------- *)



(* -------------------------------------------- *)

Inductive bound : elt -> nat -> Prop := 
  | b_bot n : bound bot n
  | b_tnat n : bound tnat (S n)
  | b_tuniv k n : bound (tuniv k) (S n)
  | b_zero n : bound zero (S n)
  | b_succ u n : bound u n -> bound (succ u) (S n)
  | b_tpi u f n : 
    bound u n -> bound_fun f n 
              -> bound (tpi u f) (S n)
  | b_abs f n : bound_fun f n
              -> bound (abs f) (S n) 
with bound_fun : list (elt * elt) -> nat -> Prop := 
  | b_nil n : bound_fun nil n
  | b_cons ui vi f n :
    bound ui n -> bound vi n -> bound_fun f n ->
    bound_fun ((ui,vi)::f) n.

Lemma rk_bounded (u:elt) : forall k, rk u <= k -> bound u k.
  eapply elt_rect' with 
    (P := fun u => forall k, rk u <= k -> bound u k)
    (Pf := fun f => forall k, rk_fun f <= k -> bound_fun f k).
  all: intros k; intros.
  all: cbn in *.
  all: try match goal with [ H : S _ <=  _ |- _ ] => 
        destruct (le_S_pred H) as [m [-> LL]] end.
  all: try solve [econstructor; eauto].
  all: fold rk_fun in *.
  - econstructor. eapply H. lia. eapply H0. lia.
  - econstructor. eapply H; lia. eapply H0; lia. eapply H1; lia.
Qed.

(* -------------------------------------------- *)


(** False things *)

(* le terms have le ranks: Not TRUE!  

      abs [(3,bot)] <= abs [(1,bot)]

      abs [(id01,0)] <= [(id0,0)]

 *)
Lemma rk_le : forall k, forall u v, 
    max (rk u) (rk v) <= k -> le' u v k -> rk u <= rk v.
Proof.
  elim /strong_ind.
  move=> n ih.
  have L2: forall m f g, (m < n)%nat -> 
       max (rk_fun f) (rk_fun g) <= m ->
       le_fun' f g m -> rk_fun f <= rk_fun g.
  { 
    intros m f. 
    induction f. intros g Le1 Le2 h1. cbn. lia.
    intros g Le1 Le2 h1. destruct a as [u1 v1].
    cbn in *. fold (le_fun' f g m) in h1.   
    destruct (app' g u1 m) eqn:EA; try done.
    move: (rk_app' EA) => Le3. 
    destruct (le' v1 e m) eqn:Le4; try done.
    rewrite Bool.andb_true_l in h1. 
    apply IHf in h1; try lia.
    apply ih in Le4; try lia; auto.
Abort.    



Definition is_bot e : { e = bot } + { e <> bot }.
Proof. destruct e. 
all: try solve [right; done].
left; done.
Qed.


(* NB: this is not true, but the results are sem_eqb....
   lub [(0,0)] [(1,1)] = [(0,0) ; (1,1)]
   lub [(1,1)] [(0,0)] = [(1,1) ; (0,0)]
 *)
Lemma lub_sym : forall u v w, lub u v = Some w -> lub v u = Some w.
Proof.
  induction u.
  all: move=> v w h.
  all: destruct v; try done.
  all: cbn; cbn in h.
  - rewrite Nat.eqb_sym. 
    destruct (n =? n0) eqn:h1; try done.
    apply Nat.eqb_eq in h1. subst. done.
  - destruct (lub u v) eqn:h1; try done.
    cbn in h. inversion h. rewrite H0.
    apply IHu in h1. rewrite h1. cbn. done.
  - destruct (compatible_fun l l0) eqn:h1; try done.
    apply compatible_fun_sym in h1.
    rewrite h1.
    destruct (lub u v) eqn:h2; try done.
    cbn in h. inversion h. clear h.
    apply IHu in h2. rewrite h2.
    cbn. 
Abort.



(* tail could be nil *)
Lemma valid_fun_tail a f : valid_fun (a :: f) -> valid_fun f.
Proof.
  unfold valid_fun. destruct a as [ui vi].
  cbn.
  move=> /andP [/andP [/andP [C1 C1'] C2] F1].
  move: F1 => /andP [/andP [Vui Vvi] h]. 
  apply /andP. split; auto.
  unfold compatible_fun.
Abort.

(* Do we need f to be minimal for this to hold? Yes! 
   Otherwise nothing stops us from having 
   (u, w) and (ui, wi) both in f 
*)
Lemma lemma1 f u ui w wi: 
  valid_fun f -> 
  le u ui -> u <> ui -> 
  app f u = Some w -> 
  app f ui = Some wi -> 
  le w wi /\ w <> wi.
Proof.
  intros Vf Lu Ne APu Api.
  move: Vf => /andP [/andP [h1 _] _ ].
  unfold app in *.
Abort.

(* Compatible elements have the same universe level???
   No, this is not true b/c bot is compatible 
   with any term.

Lemma compatible_level u v :
  compatible u v -> level u = level v.
Abort.

*)



(*
Lemma le_app ui vi f: 
   In (ui, vi) f -> forall w, app f ui = Some w -> le vi w.
Proof.
  move=>Leui. 
  induction f; intro h. done.
  move: h=>[->|h] w.
  - (* found ui,vi *)
    rewrite app_spec. cbn. clear IHf.
    rewrite Leui. 
    destruct (app_alt f ui) eqn:h2. 2: done.
    eapply lub_le_l.
  - (* elsewhere *) 
    move: (IHf h) => ih.
    rewrite app_spec. cbn.
    destruct a as [uj vj].
    destruct (app_alt f ui) eqn:h2. 
    + destruct (le uj ui) eqn:h3. 
      move=> h4. 
      rewrite app_spec in ih.
      specialize (ih _ h2).
      eapply lub_sym in h4.
      eapply lub_le_l in h4.
      
    all: try solve[move=>h4; inversion h4].
    move=>h4.
    rewrite app_spec in IHf.
*)


(* --------------------------------------------------- *)

Definition eqb_fun f1 f2 := 
  le_fun f1 f2 && le_fun f2 f1.

Lemma level_fun_respects
  u (Vu : valid_fun u) v (Vv : valid_fun v) :
  eqb_fun u v -> 
  level_fun u = level_fun v.
Proof.
Admitted.

Lemma level_respects u (Vu : valid u) v (Vv : valid v) : 
  eqb u v -> level u = level v. 
Admitted.

Lemma rk_respects u (Vu : valid u) v (Vv : valid v) : 
  eqb u v -> rk u = rk v. 
Admitted.

Lemma le_respects u1 u2 (Vu1 : valid u1) (Vu2 : valid u2)
  v1 v2 (Vv1 : valid v1) (Vv2 : valid v2) : 
  eqb u1 u2 -> eqb v1 v2 -> le u1 v1 = le u2 v2. 
Admitted.

Lemma app_respects u1 u2 (Vu1 : valid_fun u1) (Vu2 : valid_fun u2)
  v1 v2 (Vv1 : valid v1) (Vv2 : valid v2) :  
  eqb_fun u1 u2 -> eqb v1 v2 -> app u1 v1 = app u2 v2. 
Admitted.


(** well typed elements: raw version *)
(* TODO: make this relation imply validity *)

Inductive wt : elt -> elt -> Prop := 
  | wt_bot a j :
    wt a (tuniv j) ->
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
    wt a (tuniv j) -> 
    (forall ui vi, List.In (ui,vi) g -> wt ui a /\ wt vi (tuniv j)) ->
    valid_fun g ->
    wt (tpi a g) (tuniv j)

  | wt_tabs a f g w :     
    (forall ui vi, List.In (ui,vi) f -> app g ui = Some w -> wt ui a /\ wt vi w) ->
    valid_fun f ->
    valid_fun g -> 
    wt (abs f) (tpi a g)
  .

Lemma wt_valid u a : wt u a -> valid u /\ valid a.
Admitted.

Lemma wt_code u a : wt u a -> exists j, wt a (tuniv j).
Admitted.


End Raw.

(* -------------------------------------------------------- *)

(* Module of valid finite functions *)
Module Valid.

Definition elt := 
  { u : Raw.elt & Raw.valid u }.
Definition finfun := 
  { f : list (Raw.elt * Raw.elt) & Raw.valid_fun f }.

Definition bot : elt. exists Raw.bot. auto. Defined.
Definition tnat : elt. exists Raw.tnat. auto. Defined.
Definition tuniv (j: nat) : elt. exists (Raw.tuniv j). auto. Defined.
Definition zero : elt. exists Raw.zero. auto. Defined.
Definition succ (u : elt) : elt.
exists (Raw.succ (projT1 u)). cbn. eapply projT2. Defined.
Definition tpi (a : elt) (f : finfun) : elt.
exists (Raw.tpi (projT1 a) (projT1 f)).
cbn. apply /andP. split. eapply projT2.
destruct f as [rf h1]. cbn.
unfold Raw.valid_fun in h1. eapply h1.
Defined.
Definition tabs (f : finfun) : elt.
exists (Raw.abs (projT1 f)). destruct f as [rf h1]. cbn. eapply h1.
Defined.

Definition compatible (u v : elt) := 
  Raw.compatible (projT1 u) (projT1 v).

(** * le *)

Definition lub (u v : elt) (h : compatible u v) : elt. 
Proof.
  destruct (Raw.compatible_lub_exists h) as [w Lw].
  exists w. eapply (Raw.valid_lub (projT2 u) (projT2 v) Lw).
Defined.

Lemma lub_bot_l : forall v h, @lub bot v h = v.
move=> [rv Vv] h. cbn in h. destruct rv.
unfold lub. destruct Raw.compatible_lub_exists.
cbn in e. inversion e. subst. 
Admitted.

Lemma lub_bot_r : forall v h, @lub v bot h = v.
Admitted.

Lemma lub_tuniv k h : @lub (tuniv k) (tuniv k) h = tuniv k.
Admitted.

(** * le *)

Definition le (u v : elt) : bool :=
  Raw.le (projT1 u) (projT1 v).

Definition le_fun (u v : finfun) : bool :=
  Raw.le_fun (projT1 u) (projT1 v).

Lemma le_bot : forall u, le bot u = true.
move=> [ru Vu]. unfold le. cbn. destruct ru.
all: reflexivity.
Qed.

Lemma le_tnat : le tnat tnat = true.
Admitted.

(** equal *)

Definition veq (u : elt) (v: elt) : Prop := 
  Raw.eqb (projT1 u) (projT1 v).
Definition veq_fun (u v : finfun) : Prop := 
  le_fun u v && le_fun v u.

Lemma veq_bot_inv u : veq bot u -> u = bot.
Proof.
  intro h. unfold veq in h. 
  destruct u as [ru Vu].
  cbn in h.
  destruct ru; cbn in h; try done.
  unfold bot.
  f_equal.
  ext.
Qed.

Lemma veq_zero_inv u : veq zero u -> u = zero.
Proof. 
  destruct u as [ru Vu]. unfold zero, veq. cbn.
  destruct ru; cbn; try done.
  intro h.
  f_equal.
  ext.
Qed.

Lemma veq_succ_inv u v : veq (succ u) v -> 
                         exists u', v = succ u' /\ veq u u.
Proof.
  destruct v as [rv Vv]. unfold veq. cbn.
  destruct rv; cbn; try done.
  unfold Raw.eqb. repeat rewrite Raw.le_succ.
  cbn in Vv.
  exists (existT _ rv Vv).
  f_equal.
  ext.
Admitted.


(** application *)

Definition In_fun (w : elt * elt) (f : finfun) :=
  let '(u,v):= w in 
  List.In ((projT1 u), (projT1 v)) (projT1 f).

Definition app (f : finfun) (v : elt) : elt.
  move: f => [rf Vf].
  move: v => [rv Vv].
  destruct (Raw.valid_app_exists Vf Vv) as [w h].
  exists w. eapply Raw.valid_app; eauto.
Defined.

(* If a property holds for all mappings of a finfun, 
   then it holds for all mappings of any other equivalent 
   finfun. 

NB: this seems unlikely to be true. Do we need requirements on P?

 *)
Lemma In_fun_respects g1 g2 (P : elt -> elt -> Prop) :
  veq_fun g1 g2 ->
    (forall ui vi, In_fun (ui,vi) g1 -> P ui vi) <->
    (forall ui vi, In_fun (ui,vi) g2 -> P ui vi).
Admitted.

(** well typed elements *)

Inductive wt : elt -> elt -> Prop := 
  | wt_bot a j :
    wt a (tuniv j) ->
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
    wt a (tuniv j) -> 
    (forall ui vi, In_fun (ui,vi) g -> wt ui a /\ wt vi (tuniv j)) ->
    wt (tpi a g) (tuniv j)

  | wt_tabs a f g : 
    (forall ui vi, In_fun (ui,vi) f -> wt ui a /\ wt vi (app g ui)) ->
    wt (tabs f) (tpi a g)
  .


(*
If u : a and a b, then u : b. If u : a, v : a, and u and v are compatible,
then u ∨ v : a.

Lemma lemma2 : 

Lemma wt_le1 u1 a : 
  wt u1 a -> forall u2, le u2 u1 -> wt u2 a.
Proof.
  induction 1; intros u2 h.
  - have INV: (u2 = bot). admit. subst. constructor.
  - have INV: (u2 = bot \/ u2 = tuniv i). admit.
    destruct INV; subst. constructor. constructor. auto.
  - have INV: (u2 = bot \/ u2 = tnat). admit.
    destruct INV; subst. constructor. constructor. 
  - have INV: (u2 = bot \/ u2 = zero). admit.
    destruct INV; subst. constructor. constructor. 
  - have INV: (u2 = bot \/ (exists v2, u2 = succ v2 /\ le v2 u)). admit.
    destruct INV; subst. constructor. 
    move: H0 => [v2 [-> h1]].
    constructor; eauto.
  - have INV: (u2 = bot \/ 
                 exists a2, exists g2, u2 = tpi a2 g2 /\ 
                               le a2 a /\ le_fun g2 g). admit.
    destruct INV; subst. constructor. 
    move: H1 => [a2 [g2 [-> [h1 h2]]]].
    constructor; eauto.
    move=> ui vi Ing2.
    clear IHwt.
    have lemma: forall g1 g2, 
      le_fun g1 g2 -> 
      forall ui vi, In_fun (ui,vi) g1 -> 
               exists uj, exists vj, In_fun (uj,vj) g2 /\ le ui uj 
                           /\ le vi (app g2 ui) /\ le vj (app g2 ui).
    admit.
    specialize (lemma g2 g h2 _ _ Ing2).
    move: lemma => [uj [vj [Ing [L1 [L2 L3]]]]].
    destruct (H0 _ _ Ing) as [WT1 WT2].
    
Lemma wt_bot_veq u a b : 
  veq bot u -> veq a b -> wt bot a -> wt u b.
Proof.
  intros e1 e2 h1.
  inversion h1. subst.
Admitted.  


End Valid.

#[export] Instance eq_elt_equivalence : Equivalence Valid.veq.
unfold Valid.veq.
constructor.
- intros [u Vu].
  cbn.
Admitted.

#[export] Instance eqfun_elt_equivalence : Equivalence Valid.veq_fun.
Admitted.

Instance Proper_app : Proper (Valid.veq_fun ==> Valid.veq ==> Logic.eq) Valid.app.
intros x y Exy. intros w v Ewv.
Admitted.


Instance Proper_wt : Proper (Valid.veq ==> Valid.veq ==> Logic.eq) Valid.wt.
Proof. 
  intros u1 u2 Equ a1 a2 Eqa.
Admitted.


Module Q.

Definition elt  := quot Valid.veq. 

Definition finfun := quot Valid.veq_fun.

Parameter valid_fun : list (elt * elt) -> Prop.

Parameter to_finfun : forall (l : list (elt * elt)), valid_fun l -> finfun.


Definition bot  : elt. exact (to_quot Valid.bot). Defined.
Definition zero : elt. Admitted.
Definition succ : elt -> elt. Admitted.
Definition tpi : elt -> finfun -> elt. Admitted.
Definition abs : finfun -> elt. Admitted.
Definition tuniv : nat -> elt. Admitted.
Definition tnat : elt. exact (to_quot Valid.tnat). Defined.

Definition compatible : elt -> elt -> bool. Admitted.
Definition lub : forall u v, compatible u v -> elt. Admitted.
Definition app : finfun -> elt -> elt. Admitted.
Definition le : elt -> elt -> Prop. Admitted.
Definition le_fun : finfun -> finfun -> Prop. Admitted.

Definition complexity : elt -> nat.
Admitted.
  

(* needed for induction principle *)
Definition app_valid (f : list (elt * elt)) (Vf : valid_fun f) (u : elt) : elt. Admitted.

Definition le_fun_valid :
  forall (f g : list (elt * elt)) (Vf : valid_fun f) (Vg : valid_fun g), bool.
Admitted. 
(*  List.forallb (fun '(ui,vi) => lub (app_valid Vg ui) vi) f. *)

Definition eq_fun (f : Valid.finfun) (g : Valid.finfun) := 
  forall (u : Valid.elt), Valid.veq (Valid.app f u) (Valid.app g u).


Definition elt_ind : forall (P : elt -> Prop) (Pf : finfun -> Prop), 
    (P bot) ->
    (P zero) -> 
    (forall e, P e -> P (succ e)) ->
    (forall f, Pf f -> P (abs f)) -> 
    (forall e f, P e -> Pf f -> P (tpi e f)) -> 
    P tnat ->
    (forall k, P (tuniv k)) ->
    (forall l (Vf: valid_fun l), (forall u v, In (u,v) l -> P u /\ P v) -> Pf (to_finfun Vf)) ->
    forall e, (P e) /\ forall f, Pf f.
Admitted.

(* not provable (yet!) *)
(*
Definition elt_rectNonDep : forall (P : Type) (Pf : Type), 
    P ->
    P  -> 
    (elt -> P -> P) ->
    (Pf -> P) -> 
    (P -> Pf -> P) -> 
    P ->
    (nat -> P) ->
    (H : forall f (Vf: valid_fun f), (g : list (P * P)) -> Pf) ->
    (forall f (Vf: valid_fun f) g (Vg: valid_fun g) 
       (to_finfun Vf) = (to_finfun Vg) ->
       forall (Ef Eg : list(P * P)),
        (H Vf Ef) = (H Vg Eg)) ->
    (elt -> P) /\ (finfun -> Pf).
Abort. *)

(*
Definition elt_rect : forall (P : elt -> Type) (Pf : finfun -> Type), 
    (P bot) ->
    (P zero) -> 
    (forall e, P e -> P (succ e)) ->
    (forall f, Pf f -> P (abs f)) -> 
    (forall e f, P e -> Pf f -> P (tpi e f)) -> 
    P tnat ->
    (forall k, P (tuniv k)) ->
    (H : forall l (Vf: valid_fun l), (forall u v, In (u,v) l -> P u * P v) -> Pf (to_finfun Vf))) ->
    (forall f (Vf: valid_fun f) g (Vg: valid_fun g) 
       (to_finfun Vf) = (to_finfun Vg) ->
       (Ef : forall u v, In (u,v) f -> P u * Pv)
       (Eg : forall u v, In (u,v) g -> P u * Pv), 
        (H Vf Ef) = (H Vg Eg)) ->
    forall e, (P e) * forall f, Pf f.
*)


(* Section 3 *)
Inductive wt : elt -> elt -> Prop := 
  | wt_fun f (Vf : valid_fun f) a g : 
    (forall ui vi, List.In (ui,vi) f ->
              wt ui a /\ wt vi (app g ui)) ->
    wt (abs (@to_finfun f Vf)) (tpi a g).

Inductive type : elt -> Prop := .

End Q.
