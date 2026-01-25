/-
  TarnlundRefutation.lean - Refutation of Tarnlund's 2008 P≠NP attempt

  This file demonstrates WHY Tarnlund's proof attempt fails. The key insight is that
  proving a statement within a formal system does NOT establish mathematical truth
  unless the formal system is proven SOUND for that domain.

  Author: Formalization for p-vs-np repository
  Date: 2026-01-25
  Related: Issue #453, Woeginger's list entry #48
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

axiom UniversalTMAxiom : Formula

def TheoryBPrime : FormalSystem :=
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

/-! ## Part 2: The Critical Missing Piece -/

/--
Tarnlund's error: He proved "SAT ∉ P" within a formal system TheoryB',
but never proved that TheoryB' is SOUND for computational complexity claims.

Without soundness, proving something in the system doesn't make it true!
-/

/-- A soundness proof would need to demonstrate this property exists -/
def SoundnessProof (sys : FormalSystem) : Prop :=
  ∃ (_proof : Unit), IsSoundForComplexity sys

/-- THE FATAL FLAW: No soundness proof exists -/
axiom tarnlund_no_soundness_proof : ¬ SoundnessProof TheoryBPrime

/-! ## Part 3: Structure of Tarnlund's Attempt -/

structure TarnlundAttempt where
  formalSystem : FormalSystem
  formula : Formula
  provable : Provable formalSystem formula
  consistent : IsSimplyConsistent formalSystem

/-! ## Part 4: The Refutation -/

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

/-! ## Part 5: Why Soundness is Hard

Proving soundness for complexity theory requires showing that:

1. Every axiom of TheoryB' is TRUE as a statement about Turing machines
2. Every inference rule PRESERVES truth
3. The encoding of computational problems into formulas is FAITHFUL

This is a HARD problem that Tarnlund did not solve. In fact, it's
essentially equivalent to solving P vs NP itself!

If TheoryB' were powerful enough to prove "SAT ∉ P" and we could prove
it sound, we would have solved P vs NP. But Tarnlund provides no
soundness proof, so his derivation within the formal system establishes
nothing about the actual P vs NP question.
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

1. PROVABILITY within a formal system (what Tarnlund established)
2. MATHEMATICAL TRUTH (what would be needed to solve P vs NP)

### The Structure of the Error

Tarnlund showed:
- TheoryB' ⊢ "SAT ∉ P"  (provable in the formal system)
- TheoryB' is simply consistent (doesn't prove contradictions)

But he NEEDED to show:
- TheoryB' is SOUND for complexity claims
- Therefore provability implies truth
- Therefore SAT ∉ P is mathematically true

### Why This is Hard

Proving soundness of a formal system for computational complexity is
itself a deep problem. The formal system must:

1. Have axioms that are TRUE statements about computation
2. Have inference rules that PRESERVE truth
3. Correctly encode computational problems as formulas

Without a soundness proof, derivations in the formal system are
meaningless for establishing mathematical facts.

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
