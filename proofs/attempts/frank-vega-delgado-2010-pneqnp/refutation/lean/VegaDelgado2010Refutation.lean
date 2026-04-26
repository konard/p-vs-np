/-
  VegaDelgado2010Refutation.lean - Refutation of Vega Delgado's November 2010 P≠NP proof attempt

  The paper's gap is the unsupported implication from CERTIFYING ∈ P to
  an undecidable language in NP.
-/

namespace VegaDelgado2010Refutation

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

def Decidable (problem : DecisionProblem) : Prop :=
  ∃ (decider : String → Bool), ∀ (x : String), problem x ↔ decider x = true

def Undecidable (problem : DecisionProblem) : Prop :=
  ¬ Decidable problem

axiom certifyingProblem : DecisionProblem
axiom certifying_in_np : InNP certifyingProblem
axiom np_languages_are_decidable : ∀ problem, InNP problem → Decidable problem

/-
  The proof attempt needs this implication, but does not provide it.
  We keep it as an admitted statement in the refutation to document the exact gap.
-/
theorem certifying_in_p_implies_undecidable_np :
    InP certifyingProblem → ∃ (bad : DecisionProblem), Undecidable bad ∧ InNP bad := by
  intro _
  sorry

theorem undecidable_not_in_np : ∀ problem, Undecidable problem → ¬ InNP problem := by
  intro problem h_undec h_np
  exact h_undec (np_languages_are_decidable problem h_np)

theorem certifying_gap_is_the_issue :
    InP certifyingProblem → False := by
  intro h_p
  rcases certifying_in_p_implies_undecidable_np h_p with ⟨bad, h_bad_undec, h_bad_np⟩
  exact undecidable_not_in_np bad h_bad_undec h_bad_np

/-
  This theorem records the exact place where the paper would need a new,
  genuinely nontrivial computability argument.
-/

#check certifyingProblem
#check certifying_in_np
#check certifying_in_p_implies_undecidable_np
#check undecidable_not_in_np
#check certifying_gap_is_the_issue

end VegaDelgado2010Refutation
