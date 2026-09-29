From Stdlib Require Import Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.rocq Require Import PvsNPProofAttempt.
Import Complexity.Complexity.

Example zero_is_polynomial : PolynomiallyBounded (fun _ => 0).
Proof. exact polynomiallyBounded_zero. Qed.

Example constant_is_polynomial : PolynomiallyBounded (fun _ => 42).
Proof. exact (polynomiallyBounded_const 42). Qed.

Example linear_is_polynomial : PolynomiallyBounded (fun n => n + 1).
Proof. exact polynomiallyBounded_succ. Qed.

Example local_linear_is_polynomial :
  PvsNPProofAttempt.PvsNPProofAttempt.isPolynomial (fun n => n + 1).
Proof. exact polynomiallyBounded_succ. Qed.

Example sum_is_polynomial :
  PolynomiallyBounded (fun n => n * n + 3 * n + 7).
Proof.
  apply (polynomiallyBounded_add (fun n => n * n + 3 * n) (fun _ => 7)).
  - apply (polynomiallyBounded_add (fun n => n * n) (fun n => 3 * n)).
    + exists 1, 2. intro n. simpl. nia.
    + exists 3, 1. intro n. simpl. nia.
  - apply polynomiallyBounded_const.
Qed.

Example composition_is_polynomial :
  PolynomiallyBounded (fun n => (n + 1 + 1) * (n + 1 + 1)).
Proof.
  apply (polynomiallyBounded_comp
    (fun m => (m + 1) * (m + 1)) (fun n => n + 1)).
  - apply polynomiallyBounded_mul; apply polynomiallyBounded_succ.
  - apply polynomiallyBounded_succ.
Qed.
