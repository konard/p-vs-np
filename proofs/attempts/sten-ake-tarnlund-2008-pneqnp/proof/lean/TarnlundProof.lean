/-
  TarnlundProof.lean - Formalization of Tarnlund's 2008 P≠NP proof attempt structure

  This file formalizes the CLAIMED proof structure.

  Author: Formalization for p-vs-np repository
  Related: Issue #453
-/

namespace TarnlundProof

/-- Binary strings as inputs -/
def Language := String → Bool

/-- Time complexity function -/
def TimeComplexity := Nat → Nat

/-- Polynomial time -/
def isPolynomial (T : TimeComplexity) : Prop :=
  ∃ (c k : Nat), ∀ n : Nat, T n ≤ c * n ^ k

/-- Class P -/
structure ClassP where
  language : Language
  decider : String → Nat
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

/-- Class NP -/
structure ClassNP where
  language : Language
  verifier : String → String → Bool
  timeComplexity : TimeComplexity
  isPoly : isPolynomial timeComplexity

/-- SAT problem -/
axiom SAT : ClassNP

/-- P ≠ NP -/
def PNotEqualsNP : Prop :=
  ∀ (p : ClassP), ∃ (s : String), SAT.language s ≠ p.language s

/-- Formal formula -/
structure Formula where
  symbols : List String
  wellFormed : True

/-- Formal system -/
structure FormalSystem where
  axioms : List Formula
  rules : List (List Formula → Formula)

/-- Provability -/
def Provable (sys : FormalSystem) (F : Formula) : Prop :=
  True

/-- Theory B -/
def TheoryB : FormalSystem :=
  { axioms := [], rules := [] }

/-- Universal Turing Machine axiom -/
axiom UniversalTMAxiom : Formula

/-- Theory B' -/
def TheoryBPrime : FormalSystem :=
  { axioms := UniversalTMAxiom :: TheoryB.axioms
    rules := TheoryB.rules }

/-- Consistency -/
def IsConsistent (sys : FormalSystem) : Prop := True

/-- Simple consistency -/
def IsSimplyConsistent (sys : FormalSystem) : Prop := IsConsistent sys

axiom tarnlund_consistency_claim : IsSimplyConsistent TheoryBPrime

/-- Formula for "SAT is not in P" -/
def SATNotInP_Formula : Formula :=
  Formula.mk ["SAT", "not", "in", "P"] True

/-- What a formula means -/
def FormulaMeansComputationalFact (F : Formula) (fact : Prop) : Prop := True

axiom tarnlund_provability_claim : Provable TheoryBPrime SATNotInP_Formula

axiom tarnlund_meaning_claim :
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP

/-- Soundness -/
def IsSoundForComplexity (sys : FormalSystem) : Prop :=
  ∀ (F : Formula) (fact : Prop),
    FormulaMeansComputationalFact F fact →
    Provable sys F →
    fact

/-- IF soundness, THEN truth -/
theorem soundness_implies_truth :
  IsSoundForComplexity TheoryBPrime →
  Provable TheoryBPrime SATNotInP_Formula →
  FormulaMeansComputationalFact SATNotInP_Formula PNotEqualsNP →
  PNotEqualsNP := by
  intro soundness provable meaning
  exact soundness SATNotInP_Formula PNotEqualsNP meaning provable

#check soundness_implies_truth

end TarnlundProof
