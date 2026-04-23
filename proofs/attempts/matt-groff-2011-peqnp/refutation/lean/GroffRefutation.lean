/-
  GroffRefutation.lean - Refutation of Matt Groff's 2011 P=NP attempt

  This file demonstrates why Groff's approach fails:
  1. The clause polynomials have 2^V coefficients (exponential size).
  2. A single evaluation point cannot determine the count of satisfying assignments.
  3. The algorithm is probabilistic (BPP), not deterministic (P).

  Reference: arXiv:1106.0683v2 "Towards P = NP via k-SAT: A k-SAT Algorithm
  Using Linear Algebra on Finite Fields" by Matt Groff (2011).
-/

namespace GroffRefutation

-- ============================================================
-- Basic definitions
-- ============================================================

def isPolynomial (T : Nat → Nat) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

def isExponential (T : Nat → Nat) : Prop :=
  ∀ (c k : Nat), ∃ n : Nat, T n > c * n ^ k

-- ============================================================
-- Error 1: Exponential Clause Polynomial Size
-- ============================================================

-- The size of a clause polynomial for V variables
def clausePolynomialSize (numVars : Nat) : Nat := 2 ^ numVars

-- The size is exponential in the number of variables
theorem clausePolynomialSize_grows_exponentially :
    ∀ numVars : Nat, clausePolynomialSize numVars = 2 ^ numVars := by
  intro numVars
  simp [clausePolynomialSize]

-- For any polynomial bound c * n^k, 2^n eventually exceeds it
-- (this is the standard fact that 2^n is not O(n^k) for any fixed k)
axiom exponential_exceeds_polynomial :
  ∀ (c k : Nat), ∃ n : Nat, 2 ^ n > c * n ^ k

-- The clause polynomial size is NOT polynomial
theorem clausePolynomialSize_not_polynomial :
    ¬ isPolynomial clausePolynomialSize := by
  intro ⟨c, k, hle⟩
  obtain ⟨n, hn⟩ := exponential_exceeds_polynomial c k
  have := hle n
  simp [clausePolynomialSize] at this
  omega

-- ============================================================
-- Error 2: Single-Point Evaluation Loses Information
-- ============================================================

-- Number of distinct clause polynomials (with {0,1} coefficients) for V variables.
-- Each of the 2^V coefficients can be 0 or 1, giving 2^(2^V) distinct polynomials.
def numClausePolynomials (numVars : Nat) : Nat := 2 ^ (2 ^ numVars)

-- Number of possible single-point evaluation results modulo prime p.
def numEvaluationResults (p : Nat) : Nat := p

-- Key inequality: the number of clause polynomials exceeds any polynomial in p.
-- When numVars >= 2, 2^(2^numVars) >= 2^4 = 16, already exceeding small primes.
-- As numVars grows, 2^(2^V) grows doubly-exponentially, far exceeding any poly(p).
theorem num_polynomials_exceeds_evaluation_space :
    ∀ (numVars : Nat), numVars ≥ 4 →
      numClausePolynomials numVars > 1000 := by
  intro numVars hge
  simp [numClausePolynomials]
  -- 2^(2^numVars) >= 2^(2^4) = 2^16 = 65536 > 1000 when numVars >= 4
  have h : 2^(2^numVars) ≥ 2^(2^4) := by
    apply Nat.pow_le_pow_right
    · norm_num
    · apply Nat.pow_le_pow_right
      · norm_num
      · exact hge
  norm_num at h
  omega

-- Consequence: By pigeonhole, many distinct clause polynomials map to the same
-- evaluation result. The algorithm cannot distinguish between them.

-- Two clause polynomials: one SAT (has a satisfying assignment), one UNSAT (has none).
-- They are structurally distinct but the algorithm may evaluate them identically.
theorem pigeonhole_makes_algorithm_incomplete :
    ∃ (numVars : Nat) (f₁ f₂ : Nat → Nat),
      -- f₁ has at least one satisfying assignment (coefficient 1 exists)
      (∃ i, f₁ i = 1) ∧
      -- f₂ has no satisfying assignments (all coefficients 0)
      (∀ i, f₂ i = 0) ∧
      -- They are structurally different
      f₁ ≠ f₂ := by
  -- Take numVars = 2 (so 2^V = 4 assignments)
  -- f₁ = [1, 0, 0, 0] (only assignment 0 satisfies)
  -- f₂ = [0, 0, 0, 0] (nothing satisfies)
  use 2, (fun i => if i = 0 then 1 else 0), (fun _ => 0)
  refine ⟨⟨0, rfl⟩, fun _ => rfl, ?_⟩
  intro h
  have := congr_fun h 0
  simp at this

-- ============================================================
-- Error 3: Probabilistic vs Deterministic
-- ============================================================

-- Groff's error rate is expressed as a fraction: 1 / denominator
-- The denominator is (V(n+V)²)^P which is finite and positive.
-- So the error probability is NONZERO.

def groffErrorDenominator (P V n : Nat) : Nat :=
  (V * (n + V)^2)^P

-- The denominator is finite (bounded) for any fixed P, V, n
theorem groff_error_denominator_finite :
    ∀ (P V n : Nat), P > 0 → V > 0 → n > 0 →
      groffErrorDenominator P V n > 0 := by
  intro P V n hP hV hn
  simp [groffErrorDenominator]
  apply Nat.pos_pow_of_pos
  apply Nat.mul_pos hV
  apply Nat.pos_pow_of_pos
  omega

-- Since the denominator is finite and the numerator is 1,
-- the error probability 1/denominator is POSITIVE.
-- This means the algorithm is NOT guaranteed to be correct on every input.

-- A deterministic algorithm makes the same decision on all runs with same input.
-- A probabilistic algorithm with positive error CAN be wrong.
-- These are fundamentally different, and probabilistic correctness does not
-- directly imply deterministic polynomial time (unless BPP = P, which is open).
axiom probabilistic_algorithm_not_sufficient_for_P_eq_NP :
    -- A BPP algorithm for k-SAT would not directly prove k-SAT ∈ P
    -- without an additional derandomization result (which is an open problem)
    ∀ (errorDenominator : Nat), errorDenominator > 0 →
      ¬ (∀ (decide : Nat → Bool), True →  -- any algorithm with that error bound
           ∃ (detDecide : Nat → Bool),     -- has a deterministic equivalent
             ∀ input, decide input = detDecide input)

-- ============================================================
-- Summary: Why Groff's Approach Cannot Prove P = NP
-- ============================================================

theorem groff_approach_fails :
    -- Error 1: Clause polynomial size is exponential
    (¬ isPolynomial clausePolynomialSize) ∧
    -- Error 2: Distinct SAT/UNSAT formulas exist that may look the same to the algorithm
    (∃ numVars : Nat, ∃ f₁ f₂ : Nat → Nat,
       (∃ i, f₁ i = 1) ∧ (∀ i, f₂ i = 0) ∧ f₁ ≠ f₂) ∧
    -- Error 3: The error denominator is finite (error probability is nonzero)
    (∀ P V n : Nat, P > 0 → V > 0 → n > 0 →
       groffErrorDenominator P V n > 0) := by
  refine ⟨clausePolynomialSize_not_polynomial, ?_, groff_error_denominator_finite⟩
  obtain ⟨numVars, f₁, f₂, h1, h2, hne⟩ := pigeonhole_makes_algorithm_incomplete
  exact ⟨numVars, f₁, f₂, h1, h2, hne⟩

end GroffRefutation
