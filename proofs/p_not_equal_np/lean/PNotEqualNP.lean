import proofs.complexity.lean.Complexity

/-!
Conditional tests for P ≠ NP over the shared finite machine semantics.
NP-completeness and SAT membership are explicit premises: this file contains
no axiom asserting either of them and no runtime-free reduction function.
-/

namespace PNotEqualNP

abbrev DecisionProblem := Complexity.Language
abbrev TuringMachine := Complexity.Machine
abbrev InP := Complexity.InP
abbrev InNP := Complexity.InNP

def P_equals_NP : Prop := ∀ problem, InP problem ↔ InNP problem
def P_not_equals_NP : Prop := ¬P_equals_NP

theorem P_subset_NP (problem : DecisionProblem) :
    InP problem → InNP problem := Complexity.pSubsetNP problem

theorem test_existence_of_hard_problem :
    P_not_equals_NP ↔ ∃ problem, InNP problem ∧ ¬InP problem := by
  constructor
  · intro hneq
    apply Classical.byContradiction
    intro hnone
    apply hneq
    intro problem
    constructor
    · exact P_subset_NP problem
    · intro hnp
      apply Classical.byContradiction
      intro hnotp
      exact hnone ⟨problem, hnp, hnotp⟩
  · rintro ⟨problem, hnp, hnotp⟩ heq
    exact hnotp ((heq problem).mpr hnp)

/-- An NP-completeness claim must include a separate proof of NP membership.
    A sound polynomial reduction formalization is not assumed here. -/
theorem test_NP_complete_not_in_P
    (IsNPComplete : DecisionProblem → Prop)
    (complete_in_NP : ∀ problem, IsNPComplete problem → InNP problem) :
    (∃ problem, IsNPComplete problem ∧ ¬InP problem) →
    P_not_equals_NP := by
  rintro ⟨problem, hcomplete, hnotp⟩
  exact test_existence_of_hard_problem.mpr
    ⟨problem, complete_in_NP problem hcomplete, hnotp⟩

theorem test_SAT_not_in_P (sat : DecisionProblem)
    (sat_in_NP : InNP sat) : ¬InP sat → P_not_equals_NP := by
  intro hnotp
  exact test_existence_of_hard_problem.mpr ⟨sat, sat_in_NP, hnotp⟩

/-- A lower bound quantifies over every finite machine and every polynomial
    bound, and refers to actual halting runs of that machine. -/
def HasSuperPolynomialLowerBound (problem : DecisionProblem) : Prop :=
  ∀ (machine : TuringMachine) (bound : Complexity.Polynomial),
    ¬(∀ x, ∃ t b,
      t ≤ bound.eval x.length ∧
      Complexity.Run machine (Complexity.initial x) t b ∧
      (problem x = true ↔ b = true))

theorem test_super_polynomial_lower_bound :
    (∃ problem, InNP problem ∧ HasSuperPolynomialLowerBound problem) →
    P_not_equals_NP := by
  rintro ⟨problem, hnp, hlower⟩
  apply test_existence_of_hard_problem.mpr
  refine ⟨problem, hnp, ?_⟩
  rintro ⟨p, hp⟩
  apply hlower p.machine p.bound
  intro x
  obtain ⟨t, b, ht, hr⟩ := p.terminates x
  refine ⟨t, b, ht, hr, ?_⟩
  rw [← hp]
  exact p.correct x t b hr

structure ProofOfPNotEqualNP where
  proves : P_not_equals_NP

/-- Proof validation is the type checker checking `proves`, not this value. -/
def verifyPNotEqualNPProof (_proof : ProofOfPNotEqualNP) : Bool := true

theorem checkProblemWitness (problem : DecisionProblem)
    (h_np : InNP problem) (h_not_p : ¬InP problem) : ProofOfPNotEqualNP :=
  ⟨test_existence_of_hard_problem.mpr ⟨problem, h_np, h_not_p⟩⟩

theorem checkSATWitness (sat : DecisionProblem)
    (h_sat_np : InNP sat) (h_sat_not_p : ¬InP sat) : ProofOfPNotEqualNP :=
  ⟨test_SAT_not_in_P sat h_sat_np h_sat_not_p⟩

#print axioms test_existence_of_hard_problem

end PNotEqualNP
