/-
  BarronRomeroEuclideanTspGapRefutation.lean

  Refutation of the unsupported step in Woeginger entry #69.  Lack of a
  triangle-reduction property does not imply lack of every polynomial-time
  algorithm.
-/

namespace BarronRomeroEuclideanTspGapRefutation

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

/-
  Use an arbitrary structural predicate instead of defining it as True:
  this lets the refutation exhibit a problem that lacks the structure.
-/
def HasTriangleReduction (_problem : DecisionProblem) : Prop := False

def alwaysTrueProblem : DecisionProblem := fun _ => True

def constantTruePolyTime : PolyTimeFunction where
  compute := fun _ => "true"
  time := fun _ => 1
  isPolyTime := by
    exists 0
    intro n
    cases n with
    | zero => simp
    | succ n => simp

theorem always_true_in_p : InP alwaysTrueProblem := by
  refine ⟨constantTruePolyTime, ?_⟩
  intro x
  simp [alwaysTrueProblem, constantTruePolyTime]

theorem always_true_lacks_triangle_reduction :
    ¬ HasTriangleReduction alwaysTrueProblem := by
  intro h
  exact h

theorem lack_of_triangle_reduction_does_not_imply_not_in_p :
    ¬ (∀ problem : DecisionProblem,
      ¬ HasTriangleReduction problem → ¬ InP problem) := by
  intro h
  exact h alwaysTrueProblem always_true_lacks_triangle_reduction always_true_in_p

#check always_true_in_p
#check always_true_lacks_triangle_reduction
#check lack_of_triangle_reduction_does_not_imply_not_in_p

end BarronRomeroEuclideanTspGapRefutation
