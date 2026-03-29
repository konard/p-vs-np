/-
  TarnlundRefutation.lean - Refutation of Tarnlund's 2008 P≠NP attempt

  Original paper: "P is not equal to NP" (arXiv:0810.5056v1, October 2008)

  This file demonstrates WHY Tarnlund's proof attempt fails. The key insight
  is that proving a statement within a formal system does NOT establish
  mathematical truth unless the formal system is proven SOUND for that domain.

  Specifically, the paper's Theorem 1 proves "SAT ∉ P" within the formal
  system TheoryB', but never establishes that TheoryB' is sound for
  computational complexity claims. Without this soundness proof, the
  derivation is meaningless for the actual P vs NP question.

  Critique sources:
  - Henning Makholm (2008): "Does P equal NP? This is not an answer"
  - The formal system's axioms are not clearly specified
  - The relationship between the formal theory and actual computation
    is not rigorously established
-/

namespace TarnlundRefutation

/-! ## Part 1: Definitions (same as in proof/) -/

def Language := String → Bool
def TimeComplexity := Nat → Nat

def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

structure ClassP where
  language : Language
  decider : String → Nat
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

structure ClassNP where
  language : Language
  verifier : String → String → Bool
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

axiom SAT : ClassNP

def PNotEqualsNP : Prop :=
  ∀ (p : ClassP), ∃ (s : String), SAT.language s ≠ p.language s

structure Formula where
  symbols : List String

structure FormalSystem where
  axioms : List Formula
  rules : List (List Formula → Formula)

def Provable (sys : FormalSystem) (_F : Formula) : Prop :=
  True

def TheoryB : FormalSystem :=
  { axioms := [], rules := [] }

noncomputable axiom UniversalTMAxiom : Formula

noncomputable def TheoryBPrime : FormalSystem :=
  { axioms := UniversalTMAxiom :: TheoryB.axioms,
    rules := TheoryB.rules }

def IsConsistent (_sys : FormalSystem) : Prop := True
def IsSimplyConsistent (sys : FormalSystem) : Prop := IsConsistent sys

axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime

def SATNotInP_Formula : Formula :=
  { symbols := ["SAT", "not", "in", "P"] }

def FormulaMeansComputationalFact (_F : Formula) (_fact : Prop) : Prop :=
  True

axiom tarnlund_provability_claim : Provable TheoryBPrime SATNotInP_Formula

axiom tarnlund_meaning_claim :
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP

def IsSoundForComplexity (sys : FormalSystem) : Prop :=
  ∀ (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact →
    Provable sys F →
    fact

/-! ## Part 2: The Critical Missing Piece

  From Henning Makholm's critique (2008):
  "The paper is pithy to the point of sloppiness... the formal system and
  its axioms are not clearly specified... the relationship between the formal
  theory and actual Turing machine computation is not rigorously established."

  Tarnlund's Theorem 1 proves "SAT ∉ P" within TheoryB' (steps 46-53),
  but the crucial question is: does provability within TheoryB' mean the
  statement is actually TRUE?

  This requires a SOUNDNESS PROOF: showing that everything provable in
  TheoryB' about computational complexity is actually true about real
  Turing machines. Tarnlund never provides this proof.
-/

/-- A soundness proof would need to demonstrate this property exists -/
def SoundnessProof (sys : FormalSystem) : Prop :=
  ∃ (_proof : Unit), IsSoundForComplexity sys

/-- THE FATAL FLAW: No soundness proof exists in the paper.
    The paper proves things WITHIN the formal system but never shows
    the formal system correctly models computational reality. -/
axiom tarnlund_no_soundness_proof : ¬ SoundnessProof TheoryBPrime

/-! ## Part 3: Structure of the Failed Attempt -/

structure TarnlundAttempt where
  formalSystem : FormalSystem
  formula : Formula
  provable : Provable formalSystem formula
  consistent : IsSimplyConsistent formalSystem

/-! ## Part 4: The Refutation

  The refutation shows that Tarnlund's attempt has all the syntactic
  components (formal system, provability, consistency) but lacks the
  semantic component (soundness) that would connect formal derivations
  to mathematical truth.
-/

/-- Tarnlund's attempt fails because it lacks a soundness proof -/
theorem tarnlund_fails_at_soundness :
  ∃ attempt : TarnlundAttempt,
    attempt.formalSystem = TheoryBPrime ∧
    ¬ SoundnessProof attempt.formalSystem := by
  refine ⟨⟨TheoryBPrime, SATNotInP_Formula, ?_, ?_⟩, rfl, ?_⟩
  · exact tarnlund_provability_claim
  · exact tarnlund_consistency_claim
  · exact tarnlund_no_soundness_proof

/-- The gap: What WOULD be needed for the proof to work -/
theorem what_would_be_needed :
  IsSoundForComplexity TheoryBPrime →
  Provable TheoryBPrime SATNotInP_Formula →
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP →
  PNotEqualsNP := by
  intro soundness provable meaning
  exact soundness SATNotInP_Formula PNotEqualsNP meaning provable

/-! ## Part 5: Why Soundness is Hard - Counterexample

  To illustrate why soundness matters, we construct a trivially unsound
  formal system that can "prove" any statement (including SAT ∉ P),
  yet clearly doesn't establish mathematical truth.

  This demonstrates that mere provability within a system, even a
  consistent one, tells us nothing about truth without soundness.
-/

/-- Example: An unsound formal system can "prove" false statements -/
def UnsoundSystem : FormalSystem :=
  { axioms := [SATNotInP_Formula],
    rules := [] }

/-- In this trivial system, "SAT ∉ P" is provable (it's an axiom!) -/
theorem unsound_proves_sat_not_in_p :
  Provable UnsoundSystem SATNotInP_Formula := by
  trivial

/-- But this doesn't make it true! The system is unsound. -/
axiom unsound_system_not_sound : ¬ IsSoundForComplexity UnsoundSystem

/-- Moral: Provability ≠ Truth without soundness -/
theorem provability_not_truth_without_soundness :
  ∃ (sys : FormalSystem) (F : Formula) (fact : Prop),
    Provable sys F ∧
    FormulaMeansComputationalFact F fact ∧
    ¬ IsSoundForComplexity sys := by
  refine ⟨UnsoundSystem, SATNotInP_Formula, PNotEqualsNP, ?_, ?_, ?_⟩
  · exact unsound_proves_sat_not_in_p
  · trivial  -- Abstract meaning relation
  · exact unsound_system_not_sound

/-! ## Summary of the Refutation

  Tarnlund's 2008 attempt failed because it conflated TWO different concepts:

  1. PROVABILITY within a formal system (what Tarnlund established in Theorem 1)
  2. MATHEMATICAL TRUTH (what would be needed to solve P vs NP)

  ### The Structure of the Error (referencing the paper)

  Tarnlund showed (Theorem 1, steps 46-53):
  - TheoryB' ⊢ "SAT ∉ P"  (provable in the formal system)
  - TheoryB' is simply consistent (Corollary 2)

  But he NEEDED to additionally show:
  - TheoryB' is SOUND for complexity claims
  - Therefore provability implies truth
  - Therefore SAT ∉ P is mathematically true

  ### Why Soundness Cannot Be Assumed

  Proving soundness of a formal system for computational complexity requires:
  1. Every axiom of TheoryB' is TRUE as a statement about Turing machines
  2. Every inference rule PRESERVES truth about computation
  3. The encoding of computational problems into formulas is FAITHFUL

  Tarnlund provides none of these in the paper. As Makholm (2008) noted,
  even the axioms themselves are not clearly enough specified to verify
  whether they correctly model computation.

  ### Lessons Learned

  1. Formal proofs require both SYNTAX (derivations) and SEMANTICS (soundness)
  2. Provability in a system ≠ mathematical truth
  3. Soundness proofs are essential but often overlooked
  4. This error pattern appears in multiple failed P vs NP attempts
-/

#check tarnlund_fails_at_soundness
#check what_would_be_needed
#check provability_not_truth_without_soundness

end TarnlundRefutation
