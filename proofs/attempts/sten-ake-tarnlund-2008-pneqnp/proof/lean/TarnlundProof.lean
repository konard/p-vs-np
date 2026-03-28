/-
  TarnlundProof.lean - Forward Formalization of Tarnlund's 2008 P≠NP Proof Attempt

  This file formalizes the structure of Sten-Ake Tarnlund's 2008 attempted proof
  of P ≠ NP via a first-order theory of computing.

  Original paper: "P is not equal to NP" (arXiv:0810.5056v1, October 2008)

  The proof claims to show SAT ∉ P by contradiction using:
  1. A first-order theory B with axiom B characterizing a universal Turing machine
  2. A relationship between computing time and proof complexity (Lemma 3)
  3. Haken's theorem on resolution proof complexity of pigeonhole formulas

  This formalization captures what Tarnlund CLAIMED, showing each step of the
  original paper as Lean definitions and axioms.
-/

namespace TarnlundProof

/-! ## Section 1: Introduction - Overview of the Argument

  From the paper (Section 1):
  "SAT ∉ P is true, theorem 1, and provable, corollary 9, in a simply consistent
  extension B' of a first order theory B of computing, with a single finite axiom
  B characterizing a universal Turing machine."
-/

/-! ## Section 2: A Theory of Computing

  From the paper (Section 2):
  "Before applying the axiomatic method to computing complexity, a first order
  theory B of computing, with a single finite axiom B characterizing a universal
  Turing machine, is presented."
-/

/-- Binary strings as inputs -/
def Language := String → Bool

/-- Time complexity function -/
def TimeComplexity := Nat → Nat

/-- Polynomial time (Definition 8: p(a) for c·|a|^q some c q ∈ ℕ) -/
def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

/-- Class P: polynomial-time decidable languages -/
structure ClassP where
  language : Language
  decider : String → Nat
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

/-- Class NP: polynomial-time verifiable languages -/
structure ClassNP where
  language : Language
  verifier : String → String → Bool
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

/-- SAT problem (axiomatically NP-complete) -/
axiom SAT : ClassNP

/-- P ≠ NP statement -/
def PNotEqualsNP : Prop :=
  ∀ (p : ClassP), ∃ (s : String), SAT.language s ≠ p.language s

/-! ## Section 2: Formal System Definitions

  From the paper:
  "Syntactically, there are two predicate symbols of B written T(i, a, u), and
  U(x, s, z, q, j, i, u)."
-/

/-- A formula in the formal system (Definition 3) -/
structure Formula where
  symbols : List String

/-- A formal system with axioms and inference rules -/
structure FormalSystem where
  axioms : List Formula
  rules : List (List Formula → Formula)

/-- Provability in a formal system -/
def Provable (sys : FormalSystem) (_F : Formula) : Prop :=
  True  -- Abstract provability relation

/-! ## Theory B and Axiom B (Axiom 1)

  From the paper (Axiom 1):
  "B for ∀ T(i, a, u) ⊃ U(∅, ∅, a.∅, 1, i, i, u) ..."
  The axiom has six sentences (17)-(22) characterizing a universal Turing machine.
-/

/-- Theory B (Tarnlund's base formal system) -/
def TheoryB : FormalSystem :=
  { axioms := [], rules := [] }

/-- Universal Turing Machine axiom (Axiom 1, sentences 17-22) -/
noncomputable axiom UniversalTMAxiom : Formula

/-- Theory B' (Theory B + Universal TM axiom, simply consistent extension) -/
noncomputable def TheoryBPrime : FormalSystem :=
  { axioms := UniversalTMAxiom :: TheoryB.axioms,
    rules := TheoryB.rules }

/-! ## Section 2: Consistency Claims

  From the paper (Corollary 2):
  "Theory B is simply consistent in U i.e., there is no contradiction"
-/

/-- Consistency of a formal system -/
def IsConsistent (_sys : FormalSystem) : Prop := True  -- Abstract consistency

/-- Simple consistency (Definition from Kleene 1967) -/
def IsSimplyConsistent (sys : FormalSystem) : Prop := IsConsistent sys

/-- Tarnlund claims TheoryB' is simply consistent (Corollary 2) -/
axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime

/-! ## Section 2: Lemma 1

  From the paper:
  "Lemma 1: ∃uT(i, a, u) ⊃ ⊢ B → ∃uT(i, a, u) any i ∈ M a ∈ L."
  If a computation terminates, it is provable in theory B.
-/

/-- Lemma 1: True computations are provable in theory B -/
axiom lemma1_computations_provable :
  ∀ (F : Formula), Provable TheoryBPrime F

/-! ## Section 3: Computing Time (Definitions 6-15)

  From the paper (Definition 15):
  "SAT ∈ P for ⊢ B → ∃u T(i, F.∅, u) in p(F) some i ∈ U any F ∈ F."
-/

/-- Formula representing "SAT ∉ P" -/
def SATNotInP_Formula : Formula :=
  { symbols := ["SAT", "not", "in", "P"] }

/-- What it means for a formula to represent a computational fact -/
def FormulaMeansComputationalFact (_F : Formula) (_fact : Prop) : Prop :=
  True  -- Abstract meaning relation

/-- Tarnlund claims to prove "SAT ∉ P" in TheoryB' (Theorem 1) -/
axiom tarnlund_provability_claim : Provable TheoryBPrime SATNotInP_Formula

/-- The formula is claimed to mean P ≠ NP -/
axiom tarnlund_meaning_claim :
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP

/-! ## Section 4: Computing Time and Proof Complexity

  From the paper (Lemma 3):
  "⊢ B → T(i, ¬F.∅, ∅.1) in p(F) ⊃ Y(i, F, n) ∧ n ≤ c·|F|^q"

  This is the principal lemma establishing the relationship between
  computing time and proof complexity.
-/

/-- Y(i, F, n) formula - Definition 20
    Y(i, F, n) for (Q₀ ⊃ F) ∧ Qₙ ∧ ⋀₁≤k≤n (Qₖ ⊃ Qₖ₋₁)
    This represents the propositional formula that relates computing time
    to a chain of implications leading to the tautology F. -/
def Y_formula (_i : Nat) (_F : Formula) (_n : Nat) : Prop := True

/-- Lemma 3 (Principal Lemma):
    If computing time is polynomial, then Y(i, F, n) holds with polynomial n.
    This is the key claim linking computing time to proof complexity. -/
axiom lemma3_computing_time_proof_complexity :
  ∀ (i : Nat) (F : Formula) (n : Nat),
    Y_formula i F n

/-! ## Section 4.1: Proof Complexity and Haken's Theorem

  From the paper:
  "Every resolution proof of PFₙ contains at least cⁿ different clauses
  for c > 1 some c ∈ ℝ any sufficiently large n ∈ ℕ" (Haken 1985)
-/

/-- Resolution provability (Definition 22) -/
def ResolutionProvable (_F : Formula) (_size : Nat) : Prop := True

/-- Haken's theorem: resolution proofs of pigeonhole formulas require
    exponentially many clauses -/
axiom hakens_theorem :
  ∀ (m : Nat), ∃ (minSize : Nat),
    (∀ (k : Nat), minSize > k * m ^ k) ∧
    ∀ (size : Nat), size < minSize → ¬ ResolutionProvable
      { symbols := ["PF", toString m] } size

/-! ## Main Results: Theorem 1 and Theorem 2

  From the paper (Theorem 1 proof, steps 46-53):
  ⋆ SAT ∈ P (assumption for contradiction)
  ⋆ ⊢ B → T(i, ¬F.∅, ∅.1) in p(F)  (Corollary 5)
  ⋆ Y(i, PFₘ, n) ∧ n ≤ c·|PFₘ|^q  (Lemma 3)
  ⋆ ⊢_R PFₘ in p(PFₘ)  (from Y formula)
  ⋆ ¬(⊢_R PFₘ in p(PFₘ))  (Haken's theorem - CONTRADICTION)
  ⋆ SAT ∉ P
-/

/-- Soundness for computational complexity: provability implies truth -/
def IsSoundForComplexity (sys : FormalSystem) : Prop :=
  ∀ (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact →
    Provable sys F →
    fact

/-- IF soundness holds, THEN the proof works (Theorem 1 structure)
    This captures the VALID part of Tarnlund's argument:
    given soundness + provability + meaning, the conclusion follows. -/
theorem soundness_implies_truth :
  IsSoundForComplexity TheoryBPrime →
  Provable TheoryBPrime SATNotInP_Formula →
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP →
  PNotEqualsNP := by
  intro soundness provable meaning
  exact soundness SATNotInP_Formula PNotEqualsNP meaning provable

/-! ## Summary of Tarnlund's Claimed Proof Structure

  Tarnlund's approach:
  1. ✓ Defines a formal system TheoryB' (Section 2, Axiom 1)
  2. ✓ Claims TheoryB' is simply consistent (Corollary 2)
  3. ✓ Establishes computing time / proof complexity relationship (Lemma 3)
  4. ✓ Uses Haken's theorem for contradiction (Theorem 1 proof)
  5. ✗ MISSING: Proof that TheoryB' is SOUND for complexity claims

  The gap: Without soundness, provability in the system doesn't establish
  mathematical truth. The proof proves SAT ∉ P WITHIN the formal system,
  but never shows that this formal system correctly models reality.

  NOTE: We cannot formalize the soundness proof because it does not exist
  in Tarnlund's paper. This is the critical gap identified in the refutation.
-/

#check soundness_implies_truth
#check PNotEqualsNP
#check IsSoundForComplexity

end TarnlundProof
