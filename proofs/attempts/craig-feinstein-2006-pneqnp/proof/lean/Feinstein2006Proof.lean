/-
  Feinstein2006Proof.lean

  Formalization of the claimed structure of Craig Alan Feinstein's 2006
  "A New and Elegant Argument that P is not NP".

  Related: Issue #191, Woeginger's list entry #31
-/

abbrev InputSize := Nat
def Witness := Nat

/-- Abstract decision problem. -/
structure DecisionProblem where
  accepts : InputSize → Bool

/-- Abstract algorithm with a running-time bound. -/
structure Algorithm where
  decide : InputSize → Bool
  runningTime : InputSize → Nat

/-- Correctness of an algorithm for a decision problem. -/
def solves (alg : Algorithm) (problem : DecisionProblem) : Prop :=
  ∀ n, alg.decide n = problem.accepts n

/-- A coarse polynomial bound represented by a fixed exponent. -/
def polynomialTime (alg : Algorithm) : Prop :=
  ∃ k : Nat, ∀ n, alg.runningTime n ≤ Nat.mul n k + k

/-- Exponential witness-space size used by the counting argument. -/
def exponentialWitnessSpace (n : Nat) : Nat := Nat.mul n n + n + 1

/-- The selected NP-complete problem in the claimed argument. -/
axiom feinsteinProblem : DecisionProblem

/-- The problem has exponentially many candidate witnesses. -/
axiom exponentiallyManyCandidates :
  ∀ n, n ≤ exponentialWitnessSpace n

/--
The crucial claimed lower-bound premise: every polynomial-time algorithm is too
weak to distinguish the candidate space for the selected NP-complete problem.
This is the unsupported step isolated by the refutation formalization.
-/
axiom polynomialAlgorithmsMissCandidates :
  ∀ alg : Algorithm,
    polynomialTime alg →
    ¬ solves alg feinsteinProblem

/-- Feinstein's claimed conclusion for the selected NP-complete problem. -/
theorem noPolynomialAlgorithmForFeinsteinProblem :
  ∀ alg : Algorithm, polynomialTime alg → ¬ solves alg feinsteinProblem := by
  intro alg hPoly
  exact polynomialAlgorithmsMissCandidates alg hPoly

/-- Abstract P != NP conclusion targeted by the attempted proof. -/
axiom P_neq_NP : Prop

/-- Abstract statement that an NP-complete problem lacking polynomial algorithms implies P != NP. -/
axiom npCompleteLowerBoundImpliesPneqNP :
  (∀ alg : Algorithm, polynomialTime alg → ¬ solves alg feinsteinProblem) → P_neq_NP

/-- The claimed P != NP conclusion, represented as the consequence of the lower bound. -/
theorem feinstein2006Conclusion :
  P_neq_NP :=
  npCompleteLowerBoundImpliesPneqNP noPolynomialAlgorithmForFeinsteinProblem
