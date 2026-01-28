(** * domains.nat_isos: isomorphims between sets built from [nat]. *)
From Stdlib Require Import Arith Lia ssreflect.

(** ** Pairing *)
(** We can use the pairing function from Arith.Cantor: [Cantor.to_nat] and [Cantor.from_nat],
  giving an iso between [nat] and [nat -> nat]. *)
From Stdlib Require Export Arith.Cantor.

(** ** Sum *)
(** Building an iso between [nat] and [nat + nat]. *)

Definition sum_to_nat (s : nat + nat) : nat :=
  match s with
  | inl n => 2*n
  | inr n => 2*n + 1
  end.

Definition sum_of_nat (n : nat) : nat + nat :=
  match (Nat.modulo n 2) with
  | 0 => inl (Nat.div n 2)
  | S _ => inr (Nat.div n 2)
  end.


Lemma cancel_of_to_sum s : sum_of_nat (sum_to_nat s) = s.
Proof.
  rewrite /sum_of_nat /sum_to_nat.
  destruct s.
  - rewrite Nat.mul_comm Nat.Div0.mod_mul Nat.div_mul //=.
  - rewrite Nat.mul_comm Nat.add_comm Nat.Div0.mod_add Nat.div_add //=.
Qed.

Lemma cancel_to_of_sum n : sum_to_nat (sum_of_nat n) = n.
Proof.
  rewrite /sum_of_nat /sum_to_nat.
  destruct (n mod 2) as [|n'] eqn:e.
  - rewrite {2}(Nat.div_mod_eq n 2) e.
    lia.
  - rewrite {2}(Nat.div_mod_eq n 2) e.
    f_equal.
    enough (S n' = 1) by lia.
    rewrite -e.
    pose proof (Nat.mod_upper_bound n 2).
    lia.
Qed.