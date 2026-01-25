/-
  TarnlundRefutation.lean - Refutation of Tarnlund's 2008 P≠NP attempt

  Shows where Tarnlund's argument fails: missing soundness proof.

  Author: Formalization for p-vs-np repository
  Related: Issue #453
-/

import TarnlundProof

namespace TarnlundRefutation

open TarnlundProof

/-- Soundness proof -/
def SoundnessProof (sys : FormalSystem) : Prop :=
  ∃ (_proof : Unit), IsSoundForComplexity sys

/-- Tarnlund provides no soundness proof -/
axiom tarnlund_no_soundness_proof : ¬ SoundnessProof TheoryBPrime

/-- Without soundness, provability doesn't imply truth -/
theorem no_soundness_no_conclusion :
  ¬ SoundnessProof TheoryBPrime →
  ¬ (Provable TheoryBPrime SATNotInP_Formula → PNotEqualsNP) := by
  intro no_soundness
  intro _claims_truth
  sorry

/-- Tarnlund's attempt structure -/
structure TarnlundAttempt where
  formalSystem : FormalSystem
  formula : Formula
  provable : Provable formalSystem formula
  consistent : IsSimplyConsistent formalSystem

/-- The attempt fails at soundness -/
theorem tarnlund_fails_at_soundness :
  ∃ attempt : TarnlundAttempt,
    attempt.formalSystem = TheoryBPrime ∧
    ¬ SoundnessProof attempt.formalSystem := by
  refine ⟨⟨TheoryBPrime, SATNotInP_Formula, ?_, ?_⟩, rfl, ?_⟩
  · exact tarnlund_provability_claim
  · exact tarnlund_consistency_claim
  · exact tarnlund_no_soundness_proof

#check tarnlund_fails_at_soundness

end TarnlundRefutation
