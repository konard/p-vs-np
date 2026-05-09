/-
  BarronRomeroEuclideanTspGapProof.lean

  Formal sketch of Carlos Barron-Romero's Woeginger entry #69 attempt:
  "The Complexity of Euclidian 2 Dimension Travelling Salesman Problem
  versus General Assign Problem, NP is not P" (arXiv:1101.0160).

  The paper compares Euclidean 2D TSP with arbitrary GAP and then moves
  from "GAP lacks the triangle-reduction structure of E2DTSP" to
  "GAP has no polynomial-time algorithm."  The latter is the missing lower
  bound.
-/

namespace BarronRomeroEuclideanTspGapProof

abbrev DecisionProblem := String → Prop

def TimeComplexity := Nat → Nat

def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

structure PolyTimeFunction where
  compute : String → String
  time : TimeComplexity
  isPolyTime : IsPolynomialTime time

def InP (problem : DecisionProblem) : Prop :=
  ∃ (f : PolyTimeFunction),
    ∀ (x : String), problem x ↔ f.compute x = "true"

def InNP (problem : DecisionProblem) : Prop :=
  ∃ (verify : PolyTimeFunction),
    ∀ (x : String),
      problem x ↔ ∃ (cert : String), verify.compute (x ++ cert) = "true"

/-- The paper's geometric reduction property for Euclidean 2D TSP. -/
def HasTriangleReduction (_problem : DecisionProblem) : Prop := True

/-- Abstract representatives of the paper's two classes. -/
axiom e2dtsp : DecisionProblem
axiom gap : DecisionProblem

/-- The paper treats E2DTSP as an NP problem with Euclidean structure. -/
axiom e2dtsp_in_np : InNP e2dtsp
axiom e2dtsp_triangle_reducible : HasTriangleReduction e2dtsp

/-- The paper treats arbitrary GAP as an NP problem. -/
axiom gap_in_np : InNP gap

/-
  This axiom records the paper's structural claim: arbitrary GAP instances
  need not preserve the triangle-reduction property used for E2DTSP.
-/
axiom gap_lacks_triangle_reduction : ¬ HasTriangleReduction gap

/-
  CLAIMED CRITICAL STEP:

  The paper needs this implication to move from a missing geometric
  property to a lower bound against every polynomial-time algorithm.
  The text does not prove it; random or non-Euclidean edge weights only
  defeat this particular reduction strategy.
-/
theorem no_triangle_reduction_implies_not_in_p :
    ¬ HasTriangleReduction gap → ¬ InP gap := by
  intro _
  -- Formalization stops here: the paper provides no universal lower-bound
  -- argument excluding all polynomial-time algorithms for GAP.
  sorry

theorem gap_not_in_p : ¬ InP gap :=
  no_triangle_reduction_implies_not_in_p gap_lacks_triangle_reduction

theorem barron_romero_2010_claim :
    ¬ (∀ problem, InP problem ↔ InNP problem) := by
  intro h_eq
  have h_gap_p : InP gap := (h_eq gap).2 gap_in_np
  exact gap_not_in_p h_gap_p

#check e2dtsp_triangle_reducible
#check gap_lacks_triangle_reduction
#check no_triangle_reduction_implies_not_in_p
#check barron_romero_2010_claim

end BarronRomeroEuclideanTspGapProof
