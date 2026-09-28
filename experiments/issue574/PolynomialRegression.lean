import proofs.complexity.lean.Complexity
import proofs.attempts.MeyerAttempt
import proofs.experiments.lean.PvsNPProofAttempt

-- This failed before the shared bound was introduced: at n = 0, n + 1 = 1
-- while c * 0 ^ k = 0 for every positive k.
example : PvsNPProofAttempt.isPolynomial (fun n => n + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

-- The former exponent-only predicate rejected 42 already at n = 1.
example : IsPolynomialTime (fun _ => 42) :=
  Complexity.polynomiallyBounded_const 42

example : Complexity.PolynomiallyBounded (fun _ => 0) :=
  Complexity.polynomiallyBounded_zero

example : Complexity.PolynomiallyBounded (fun n => n ^ 2 + 3 * n + 7) := by
  have hsq : Complexity.PolynomiallyBounded (fun n => n ^ 2) := by
    refine ⟨1, 2, ?_⟩
    intro n
    simpa using Nat.pow_le_pow_left (Nat.le_succ n) 2
  have hlin : Complexity.PolynomiallyBounded (fun n => 3 * n) := by
    refine ⟨3, 1, ?_⟩
    intro n
    simpa using Nat.mul_le_mul_left 3 (Nat.le_succ n)
  exact (hsq.add hlin).add (Complexity.polynomiallyBounded_const 7)

example : Complexity.PolynomiallyBounded (fun n => (n + 2) * (n + 2)) := by
  have hlin := Complexity.polynomiallyBounded_succ
  have hsq := hlin.mul hlin
  have hcomp := hsq.comp hlin
  simpa [Function.comp] using hcomp
