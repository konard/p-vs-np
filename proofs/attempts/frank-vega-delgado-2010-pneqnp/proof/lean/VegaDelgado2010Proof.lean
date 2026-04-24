/-
  VegaDelgado2010Proof.lean - Formalization of Vega Delgado'"'"'s November 2010 P≠NP attempt

  This file formalizes the CERTIFYING argument from the 2010 paper
  "A Solution to the P versus NP Problem" (Woeginger entry #68).

  The paper claims that a CERTIFYING problem lies in NP and that if it were
  in P then some undecidable language would be forced into NP.
  The missing implication is the critical gap.
-/

namespace VegaDelgado2010ProofAttempt

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

/-
  CERTIFYING is kept abstract here because the paper does not provide a Lean-ready
  machine encoding.  The formalization only needs the logical role of the problem.
-/
axiom certifyingProblem : DecisionProblem

/-
  The paper treats CERTIFYING as an NP-style problem.  We model that as an axiom
  because the concrete machine encoding is not part of the repository'"'"'s formal core.
-/
axiom certifying_in_np : InNP certifyingProblem

/-
  Standard computability fact: NP languages are decidable.  We use it as an axiom
  because the repository does not import a full library of complexity-class theorems.
-/
axiom np_languages_are_decidable : ∀ problem, InNP problem → Decidable problem

/-
  CLAIMED CRITICAL STEP:

  Vega Delgado argues that if CERTIFYING were in P, then some undecidable language
  would belong to NP.  This is the unsupported step.
-/
theorem certifying_in_p_implies_undecidable_np :
    InP certifyingProblem → ∃ (bad : DecisionProblem), Undecidable bad ∧ InNP bad := by
  intro _
  -- The paper does not supply the missing reduction here.
  sorry

theorem certifying_not_in_p : ¬ InP certifyingProblem := by
  intro h_p
  rcases certifying_in_p_implies_undecidable_np h_p with ⟨bad, h_bad_undec, h_bad_np⟩
  exact h_bad_undec (np_languages_are_decidable bad h_bad_np)

theorem vega_delgado_2010_claim :
    ¬ (∀ problem, InP problem ↔ InNP problem) := by
  intro h_eq
  have h_certifying_p : InP certifyingProblem := (h_eq certifyingProblem).2 certifying_in_np
  exact certifying_not_in_p h_certifying_p

/-
  SUMMARY OF THE GAP

  The paper'"'"'s intended contradiction needs:
    CERTIFYING ∈ P → ∃ bad, Undecidable bad ∧ InNP bad

  That implication is the unresolved part of the proof.
-/

#check certifyingProblem
#check certifying_in_np
#check certifying_in_p_implies_undecidable_np
#check certifying_not_in_p
#check vega_delgado_2010_claim

end VegaDelgado2010ProofAttempt
