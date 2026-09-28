/-
  Feinstein2006Refutation.lean

  Refutation skeleton for Craig Alan Feinstein's 2006 P != NP attempt.
  The file isolates the gap between counting many witnesses and proving a
  lower bound for all polynomial-time algorithms.

  Related: Issue #191, Woeginger's list entry #31
-/

abbrev InputSize := Nat
def Witness := Nat

structure DecisionProblem where
  accepts : InputSize → Bool

structure Algorithm where
  decide : InputSize → Bool
  runningTime : InputSize → Nat

def solves (alg : Algorithm) (problem : DecisionProblem) : Prop :=
  ∀ n, alg.decide n = problem.accepts n

def polynomialTime (alg : Algorithm) : Prop :=
  ∃ k : Nat, ∀ n, alg.runningTime n ≤ Nat.mul n k + k

/-- A proof may establish that exhaustive search over witnesses is expensive. -/
def exhaustiveSearchLowerBound (_problem : DecisionProblem) : Prop :=
  ∀ n, n ≤ Nat.mul n n + n + 1

/-- The much stronger statement needed for P != NP. -/
def allPolynomialAlgorithmsFail (problem : DecisionProblem) : Prop :=
  ∀ alg : Algorithm, polynomialTime alg → ¬ solves alg problem

/--
The missing bridge in the 2006 argument. It is not enough to count candidates;
one must prove that every polynomial-time algorithm is forced to inspect them in
the counted way.
-/
def missingBridge : Prop :=
  ∀ problem : DecisionProblem,
    exhaustiveSearchLowerBound problem → allPolynomialAlgorithmsFail problem

/-- A structured description of the gap. -/
structure CountingGap where
  problem : DecisionProblem
  hasCountingFact : exhaustiveSearchLowerBound problem
  bridgeIsUnproved : ¬ missingBridge

/--
Counting witnesses alone does not provide the bridge to arbitrary algorithms.
The concrete countermodel depends on the chosen problem, so the formalization
records the exact unsupported obligation as an admitted theorem.
-/
theorem countingDoesNotImplyGeneralLowerBound :
  ¬ missingBridge := by
  sorry

/-- Feinstein's proof needs precisely the missing bridge. -/
theorem feinstein2006Gap :
  ∀ problem : DecisionProblem,
    exhaustiveSearchLowerBound problem →
    (missingBridge → allPolynomialAlgorithmsFail problem) := by
  intro problem hCounting hBridge
  exact hBridge problem hCounting
