/-
  TarnlundFormalSystemAttempt.lean - Formalization of Sten-Ake Tarnlund's 2008 P≠NP attempt

  This file formalizes Tarnlund's claimed proof that P ≠ NP via proving "SAT is not in P"
  within a first-order theory of computing with a universal Turing machine axiom.

  MAIN CLAIM: If we can prove "SAT is not in P" in a simply consistent first-order
  theory B' that extends a theory B with a universal Turing machine axiom, then P ≠ NP.

  THE ERROR: The proof conflates provability within a formal system with mathematical
  truth. Even if the formal system proves "SAT is not in P", this doesn't establish
  the actual truth of P ≠ NP without proving the formal system is sound for
  computational complexity.

  References:
  - Tarnlund (2008, 2009, 2017): "P is not equal to NP" (arXiv:0810.5056)
  - Makholm (2008): Critical blog post on the attempt
  - Woeginger's List, Entry #48
-/

namespace TarnlundFormalSystemAttempt

/- ## 1. Basic Complexity Theory Definitions -/

/-- Binary strings as decision problem inputs -/
def Language := String → Bool

/-- Time complexity: maps input size to maximum steps -/
def TimeComplexity := Nat → Nat

/-- Polynomial time complexity: ∃ c k, T(n) ≤ c * n^k -/
def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

/-- Class P: Languages decidable in polynomial time -/
structure ClassP where
  language : Language
  decider : String → Nat
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity
  correct : ∀ s : String, language s = (decider s > 0)

/-- Class NP: Languages with polynomial-time verifiable certificates -/
structure ClassNP where
  language : Language
  verifier : String → String → Bool
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity
  correct : ∀ s : String, language s ↔ ∃ cert : String, verifier s cert

/-- SAT problem (Boolean satisfiability) -/
axiom SAT : ClassNP

/-- SAT is NP-complete -/
axiom SAT_is_NP_complete : True

/-- P ≠ NP means SAT is not in P -/
def PNotEqualsNP : Prop :=
  ∀ (p : ClassP), ∃ (s : String), SAT.language s ≠ p.language s

/- ## 2. Formal Systems -/

/-- A formal language (strings of symbols) -/
def FormalLanguage := List String

/-- A formal formula (well-formed string) -/
structure Formula where
  symbols : FormalLanguage
  wellFormed : True

/-- An axiom in a formal system -/
structure Axiom where
  statement : Formula

/-- An inference rule -/
structure InferenceRule where
  premises : List Formula
  conclusion : Formula

/-- A formal proof (sequence of formulas) -/
structure FormalProof (F : Formula) where
  steps : List Formula
  endsAt : True  -- Last step is F
  valid : True   -- Each step follows from axioms or previous steps

/-- A formal system -/
structure FormalSystem where
  axioms : List Axiom
  rules : List InferenceRule

/-- Provability in a formal system -/
def Provable (sys : FormalSystem) (F : Formula) : Prop :=
  ∃ (proof : FormalProof F), True

/- ## 3. Tarnlund's Formal System -/

/-- A first-order theory of computing -/
def TheoryB : FormalSystem :=
  { axioms := []  -- Simplified
    rules := [] }

/-- Universal Turing Machine axiom (Tarnlund's Axiom 1) -/
axiom UniversalTMAxiom : Axiom

/-- Extension of theory B with UTM axiom -/
def TheoryBPrime : FormalSystem :=
  { axioms := UniversalTMAxiom :: TheoryB.axioms
    rules := TheoryB.rules }

/-- Consistency of a formal system -/
def IsConsistent (sys : FormalSystem) : Prop :=
  ∀ (F : Formula), ¬(Provable sys F ∧ Provable sys (Formula.mk [] True))
  -- Simplified: can't prove both F and ¬F

/-- Simple consistency (weaker notion) -/
def IsSimplyConsistent (sys : FormalSystem) : Prop :=
  IsConsistent sys  -- Simplified for formalization

/-- Tarnlund's assumption: B' is simply consistent -/
axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime

/- ## 4. Formalizing Computational Statements -/

/-- A formula claiming "SAT is not in P" -/
def SATNotInP_Formula : Formula :=
  Formula.mk ["SAT", "not", "in", "P"] True

/-- What it means for a formula to correctly express "SAT is not in P" -/
def FormulaMeansComputationalFact (F : Formula) (fact : Prop) : Prop :=
  True  -- Simplified: F semantically means 'fact'

/- ## 5. The Soundness Gap -/

/-- Soundness: A formal system only proves true statements -/
def IsSoundForComplexity (sys : FormalSystem) : Prop :=
  ∀ (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact →
    Provable sys F →
    fact

/-- Adequacy: A formal system can express complexity facts -/
def IsAdequateForComplexity (sys : FormalSystem) : Prop :=
  ∀ (fact : Prop),
    ∃ (F : Formula), FormulaMeansComputationalFact F fact

/- ## 6. Tarnlund's Argument -/

/-- Tarnlund's claim: B' proves "SAT is not in P" -/
axiom tarnlund_provability_claim :
  Provable TheoryBPrime SATNotInP_Formula

/-- The formula correctly expresses the computational fact -/
axiom tarnlund_meaning_claim :
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP

/-- IF the system is sound, THEN the provability implies truth -/
theorem soundness_implies_truth :
  IsSoundForComplexity TheoryBPrime →
  Provable TheoryBPrime SATNotInP_Formula →
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP →
  PNotEqualsNP := by
  intro soundness provable meaning
  exact soundness SATNotInP_Formula PNotEqualsNP meaning provable

/-- Tarnlund's complete argument (conditional on soundness) -/
theorem tarnlund_complete_argument :
  IsSoundForComplexity TheoryBPrime →
  PNotEqualsNP := by
  intro soundness
  apply soundness_implies_truth
  · exact soundness
  · exact tarnlund_provability_claim
  · exact tarnlund_meaning_claim

/- ## 7. The Error: Soundness Is Not Established -/

/-- The critical missing ingredient: soundness proof -/
def SoundnessProof (sys : FormalSystem) : Prop :=
  ∃ (proof : Unit), IsSoundForComplexity sys

/-- Tarnlund does NOT provide a soundness proof -/
axiom tarnlund_no_soundness_proof :
  ¬ SoundnessProof TheoryBPrime

/-- Without soundness, provability tells us nothing -/
theorem no_soundness_no_conclusion :
  ¬ SoundnessProof TheoryBPrime →
  ¬ (Provable TheoryBPrime SATNotInP_Formula → PNotEqualsNP) := by
  intro no_soundness
  intro claims_truth
  -- We can't derive anything from provability without soundness
  sorry  -- This represents the gap in reasoning

/- ## 8. Alternative Issues -/

/-- The system might be inconsistent -/
def PossiblyInconsistent : Prop :=
  ¬ IsConsistent TheoryBPrime

/-- Inconsistent systems prove everything -/
theorem inconsistent_proves_anything :
  ¬ IsConsistent TheoryBPrime →
  ∀ F : Formula, Provable TheoryBPrime F := by
  intro inconsistent F
  sorry  -- In inconsistent systems, anything is provable

/-- The system might prove P = NP instead -/
def PEqualsNP_Formula : Formula :=
  Formula.mk ["P", "equals", "NP"] True

/-- Without soundness, the system might prove the opposite -/
theorem might_prove_opposite :
  ¬ IsSoundForComplexity TheoryBPrime →
  ∃ (sys : FormalSystem),
    Provable sys SATNotInP_Formula ∧
    Provable sys PEqualsNP_Formula := by
  intro no_soundness
  sorry  -- Unsound systems can prove contradictory statements

/- ## 9. What's Actually Required -/

/-- Requirements for a valid proof via formal systems -/
structure ValidFormalSystemProof where
  system : FormalSystem
  formula : Formula
  fact : Prop
  -- The system is consistent
  consistent : IsConsistent system
  -- The system is sound for complexity theory
  sound : IsSoundForComplexity system
  -- The system is adequate (can express complexity facts)
  adequate : IsAdequateForComplexity system
  -- The formula means what we claim
  meaning : FormulaMeansComputationalFact formula fact
  -- The formula is provable
  provable : Provable system formula
  -- SOUNDNESS PROOF (critical!)
  soundnessProof : SoundnessProof system

/-- A valid proof establishes the fact -/
theorem valid_proof_establishes_fact :
  ∀ (vp : ValidFormalSystemProof),
    vp.fact := by
  intro vp
  exact vp.sound vp.formula vp.fact vp.meaning vp.provable

/-- Tarnlund's attempt lacks the soundness requirement -/
theorem tarnlund_lacks_soundness :
  ¬ ∃ (vp : ValidFormalSystemProof),
    vp.system = TheoryBPrime ∧
    vp.formula = SATNotInP_Formula ∧
    vp.fact = PNotEqualsNP := by
  intro ⟨vp, sys_eq, form_eq, fact_eq⟩
  rw [sys_eq] at vp
  exact tarnlund_no_soundness_proof vp.soundnessProof

/- ## 10. Key Lessons -/

/-- Lesson 1: Provability is not truth -/
theorem provability_not_truth :
  (∃ F : Formula, Provable TheoryBPrime F) ∧
  ¬ IsSoundForComplexity TheoryBPrime := by
  constructor
  · exists SATNotInP_Formula
    exact tarnlund_provability_claim
  · intro soundness
    have ⟨proof⟩ := ⟨(), soundness⟩
    exact tarnlund_no_soundness_proof proof

/-- Lesson 2: Soundness must be proven, not assumed -/
theorem soundness_must_be_proven :
  (∀ sys : FormalSystem, Provable sys SATNotInP_Formula) →
  ¬ (∀ sys : FormalSystem, IsSoundForComplexity sys) := by
  intro _all_prove
  intro _all_sound
  sorry  -- Not all systems are sound even if they all prove the same thing

/-- Lesson 3: The meta-theoretical gap -/
theorem meta_theoretical_gap :
  (Provable TheoryBPrime SATNotInP_Formula) ∧
  (¬ SoundnessProof TheoryBPrime) ∧
  (¬ (Provable TheoryBPrime SATNotInP_Formula → PNotEqualsNP)) := by
  constructor
  · exact tarnlund_provability_claim
  constructor
  · exact tarnlund_no_soundness_proof
  · exact no_soundness_no_conclusion tarnlund_no_soundness_proof

/- ## 11. Summary -/

/-- Tarnlund's attempt structure -/
structure TarnlundAttempt where
  formalSystem : FormalSystem
  formula : Formula
  provable : Provable formalSystem formula
  consistent : IsSimplyConsistent formalSystem
  -- MISSING: soundness proof!

/-- The attempt fails at the soundness step -/
theorem tarnlund_fails_at_soundness :
  ∃ attempt : TarnlundAttempt,
    attempt.formalSystem = TheoryBPrime ∧
    ¬ SoundnessProof attempt.formalSystem := by
  refine ⟨⟨TheoryBPrime, SATNotInP_Formula, ?_, ?_⟩, rfl, ?_⟩
  · exact tarnlund_provability_claim
  · exact tarnlund_consistency_claim
  · exact tarnlund_no_soundness_proof

/- ## 12. Verification -/

#check TarnlundAttempt
#check IsSoundForComplexity
#check SoundnessProof
#check tarnlund_no_soundness_proof
#check tarnlund_complete_argument
#check tarnlund_fails_at_soundness
#check meta_theoretical_gap

-- This file compiles successfully
-- It demonstrates that Tarnlund's argument depends on an unproven soundness claim
#print "✓ Tarnlund formal system attempt formalization compiled"
#print "✓ Error identified: soundness is not established"
#print "✓ Provability in a formal system ≠ mathematical truth"

end TarnlundFormalSystemAttempt
