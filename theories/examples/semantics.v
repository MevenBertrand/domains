Require Import syntax.
Require Export fintype.

Require Import findom.

Import ScopedNotations.
Import SubstNotations.

Check Valid.elt.

Module Type DOMAIN.
  (* NOTE: sets are closed under lubs *)
  Definition elt : Type    := Valid.elt -> Prop.

  (* proj d u := lub (u /\ w | w in d) *)
  Definition proj : elt -> Valid.elt -> Valid.elt.
    Admitted.

  (* 
  Lemma proj_lower : forall d u,  proj d u <= u. Admitted.
  *)

  Lemma proj_idem  : forall d u, proj d (proj d u) = proj d u. Admitted.

  (* what restrictions do we have on the finfuns? *)
  Definition funelt : Type := Valid.finfun -> Prop.
  Axiom apply : forall (f : funelt) (u : elt), elt. (* ???? *) 
   
  Axiom tnat   : elt.
  Axiom tuniv  : nat -> elt.
  Axiom zero   : elt.
  Axiom succ   : elt -> elt.
  Axiom abs    : (elt -> elt) -> elt.
  Axiom tpi    : elt -> (elt -> elt) -> elt.
  Axiom app    : elt -> elt -> elt.
    

  Axiom bot    : elt.
  Axiom le     : elt -> elt -> Prop.

  (* type test: p A a returns a when a : A and ??? *)
  Axiom p     : elt -> elt -> elt. 
End DOMAIN.

Module Denot (D : DOMAIN).

(* somehow we need some restrictions on the functions for 
   abs and tpi *)
Fixpoint denot {n} (t : Tm n)(ρ : fin n -> D.elt) : D.elt := 
  match t with 
  | var x   => ρ x 
  | app M N => D.app (denot M ρ) (denot N ρ)
  | tnat    => D.tnat
  | tuniv i => D.tuniv i
  | zero    => D.zero
  | succ M  => D.succ (denot M ρ)
  | abs A M => D.abs  (fun u => denot M (D.p (denot A ρ) u .: ρ))
  | tpi A B => D.tpi  (denot A ρ) 
                (fun u => denot B (D.p (denot A ρ) u .: ρ))
  | nrec _ m0 m1 => D.bot
  end.

(* --------------------------------- *)

Definition Ctx n := fin n -> Tm n.

(* for nrec *)
Definition rho {n} : fin (S n) -> Tm (S n) := 
   (succ (var var_zero) .: var >> ⟨↑⟩).

Definition Ctx_app {n} : Ctx n -> Tm n -> Ctx (S n) := 
  fun Γ A => ( A⟨↑⟩ .: (Γ >> ⟨↑⟩)).

Notation "Γ ++ A" := (Ctx_app Γ A).

Inductive typing {n} (Γ : Ctx n) : Tm n -> Tm n -> Prop := 
  | tvar x : 
    ctx Γ ->
    typing Γ (var x) (Γ x)
  | t_conv M A B : 
    typing Γ M A -> 
    type_conv Γ A B -> 
    typing Γ M B
  | t_abs A B N : 
    type Γ A -> 
    type (Γ ++ A) B ->
    typing (Γ ++ A) N B ->
    typing Γ (abs A N) (tpi A B)
  | t_app A B N M : 
    type Γ A -> 
    type (Γ ++ A) B -> 
    typing Γ N (tpi A B) ->
    typing Γ M A -> 
    typing Γ (app N M) B[M..]
  (* natural numbers *)
  | t_nat : 
    typing Γ tnat (tuniv 0)
  | t_zero : 
    typing Γ zero tnat 
  | t_succ M : 
    typing Γ M tnat ->
    typing Γ (succ M) tnat 
  | t_rec (T U : Tm (S n)) M0 M1 :
    type   (Γ ++ tnat) T ->
    typing Γ M0 (T[zero..]) ->
    U = T[rho] ->
    typing Γ M1 (tpi tnat (tpi T U⟨↑⟩ )) ->       
    typing Γ (nrec T M0 M1) (tpi tnat T)
  (* universes *)
  | t_tpi A B i : 
    typing Γ A (tuniv i) ->
    typing (Γ ++ A) B (tuniv i) -> 
    typing Γ (tpi A B) (tuniv i)
  | t_cum A i j : 
    typing Γ A (tuniv i) -> (i < j)%nat -> 
    typing Γ A (tuniv j)
  | t_univ i j : 
    (i < j)%nat ->
    typing Γ (tuniv i) (tuniv j)
with type {n} (Γ : Ctx n) : Tm n -> Prop := 
  | ty_pi A B : 
    type Γ A -> 
    type (Γ ++ A) B -> 
    type Γ (tpi A B)
  (* universes *)
  | ty_univ A i : 
    typing Γ A (tuniv i) -> 
    type Γ A
with type_conv {n} (Γ : Ctx n) : Tm n -> Tm n -> Prop := 
  | tc_refl A : type_conv Γ A A
  | tc_trans A B C : 
    type_conv Γ A B -> type_conv Γ B C -> type_conv Γ A C 
  | tc_tpi A0 A1 B0 B1 :
    type_conv Γ A0 A1 ->
    type_conv (Γ ++ A0) B0 B1 -> 
    type_conv Γ (tpi A0 B0) (tpi A1 B1)
  | tc_univ M N i : 
    conv Γ M N (tuniv i) ->
    type_conv Γ M N 
with conv {n} (Γ : Ctx n) : Tm n -> Tm n -> Tm n -> Prop := 
  | c_conv M N A B : 
    conv Γ M N A -> 
    type_conv Γ A B  ->
    conv Γ M N B
  | c_refl M A : 
    typing Γ M A ->
    conv Γ M M A 
  | c_trans M N P A  : 
    conv Γ M N A -> 
    conv Γ N P A -> 
    conv Γ M P A
  | c_app1 A B N N' M : 
    type Γ A -> 
    type (Γ ++ A) B -> 
    conv Γ N N' (tpi A B) ->
    typing Γ M A ->
    conv Γ (app N M) (app N' M) B[M..]
  | c_app2 A B N M M'  :          
    type Γ A -> 
    type (Γ ++ A) B -> 
    typing Γ N (tpi A B) ->
    conv Γ M M' A ->
    conv Γ (app N M) (app N M') B[M..]
  | c_beta A B M N :
    type Γ A -> 
    type (Γ ++ A) B -> 
    typing (Γ ++ A) N B -> 
    typing Γ M A ->
    conv Γ (app (abs A N) M) N[M..] B[M..]
  | c_eta A B N N' :
    type Γ A -> 
    type (Γ ++ A) B -> 
    typing Γ N (tpi A B) ->     
    typing Γ N' (tpi A B) ->     
    conv (Γ ++ A) (app N⟨↑⟩ (var var_zero)) (app N'⟨↑⟩ (var var_zero)) A⟨↑⟩ ->
    conv Γ N N' (tpi A B)
  (* natural numbers: TODO add typing hyps *)
  | c_nrec_Z T M0 M1 A : 
    conv Γ (app (nrec T M0 M1) zero) M0 A 
  | c_nrec_S T M0 M1 n A : 
    conv Γ (app (nrec T M0 M1) (succ n)) 
      (app (app M1 n) (app (nrec T M0 M1) n)) A
  | c_univ M N i j : 
    conv Γ M N (tuniv i) -> (i < j)%nat ->
    conv Γ M N (tuniv j)
  | c_pi A0 A1 B0 B1 i :
    conv Γ A0 A1 (tuniv i) -> 
    conv (Γ ++ A0) B0 B1 (tuniv i) -> 
    conv Γ (tpi A0 B0) (tpi A1 B1) (tuniv i)
with ctx {n} (Γ : Ctx n) : Prop :=
  | t_ctx : 
    (forall n, type Γ (Γ n)) ->
    ctx Γ.
  

(* k is the complexity of a *)
Fixpoint LR_type (a : D.elt) (k : nat) : tm zero -> Prop := 
with LR_conv (a : D.elt) : tm zero -> tm zero -> Prop.
