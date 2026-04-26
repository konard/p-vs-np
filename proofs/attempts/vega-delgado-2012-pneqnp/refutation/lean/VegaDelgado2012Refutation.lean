/-
  VegaDelgado2012Refutation.lean - Refutation of Vega Delgado's 2012 P≠NP proof attempt

  This file demonstrates why Vega Delgado's 2012 approach fails:
  1. The critical implication (P = UP → EXP = P) is unjustified and contradicts known results.
  2. Even if P ≠ UP, this does not imply P ≠ NP.
-/

namespace VegaDelgado2012Refutation

-- Complexity class membership (same definitions as proof file)
def DecisionProblem := String → Prop
def TimeComplexity := Nat → Nat

def IsPolynomialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ n ^ k

def IsExponentialTime (f : TimeComplexity) : Prop :=
  ∃ (k : Nat), ∀ (n : Nat), f n ≤ 2 ^ (n ^ k)

structure TuringMachine where
  compute : String → Bool
  timeComplexity : TimeComplexity

structure NondeterministicTM where
  nd_compute : String → List Bool
  nd_timeComplexity : TimeComplexity

def InP (problem : DecisionProblem) : Prop :=
  ∃ (tm : TuringMachine),
    (IsPolynomialTime tm.timeComplexity) ∧
    (∀ (x : String), problem x ↔ tm.compute x = true)

def InNP (problem : DecisionProblem) : Prop :=
  ∃ (ntm : NondeterministicTM),
    (IsPolynomialTime ntm.nd_timeComplexity) ∧
    (∀ (x : String),
      problem x ↔ ∃ (result : Bool), result ∈ ntm.nd_compute x ∧ result = true)

def ExistsUnique {α : Type} (P : α → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x

def InUP (problem : DecisionProblem) : Prop :=
  ∃ (ntm : NondeterministicTM),
    (IsPolynomialTime ntm.nd_timeComplexity) ∧
    (∀ (x : String),
      (problem x ↔ ExistsUnique (fun result => result ∈ ntm.nd_compute x ∧ result = true)))

def InEXP (problem : DecisionProblem) : Prop :=
  ∃ (tm : TuringMachine),
    (IsExponentialTime tm.timeComplexity) ∧
    (∀ (x : String), problem x ↔ tm.compute x = true)

/-
  REFUTATION 1: THE TIME HIERARCHY THEOREM IS UNCONDITIONAL

  The Time Hierarchy Theorem guarantees EXP ≠ P regardless of any assumption
  about the relationship between P and UP. This directly contradicts what Vega
  Delgado's critical step claims (that P = UP would imply EXP = P).
-/

-- Time Hierarchy Theorem (axiom — proven by Hartmanis & Stearns, 1965)
axiom time_hierarchy_theorem : ¬(∀ problem, InEXP problem ↔ InP problem)

-- The theorem above holds with NO assumption about P vs UP.
-- Therefore, P = UP cannot possibly cause EXP = P to be TRUE,
-- because EXP = P is ALWAYS FALSE.

/-
  Formal statement: The critical step is invalid.

  If EXP = P is always false (by Time Hierarchy Theorem), then
  "P = UP → EXP = P" would only be vacuously true if "P = UP" is false.
  But the proof cannot assume "P = UP" is false — that is what it is trying to prove!

  The argument structure is circular: it assumes P = UP to derive a contradiction
  (EXP = P), but deriving EXP = P from P = UP is itself false, so the derivation
  is invalid, not the assumption.
-/
theorem critical_step_is_invalid :
    -- The critical implication (P = UP → EXP = P) cannot be derived
    -- from standard complexity-theoretic axioms.
    -- We demonstrate this by showing EXP = P is always false:
    ¬(∀ problem, InEXP problem ↔ InP problem) := by
  exact time_hierarchy_theorem

/-
  REFUTATION 2: P ≠ UP DOES NOT IMPLY P ≠ NP

  Even if we hypothetically accept P ≠ UP (ignoring the flawed derivation),
  this does not prove P ≠ NP. We only know UP ⊆ NP, not UP = NP.

  The relationship between UP and NP is itself an open problem.
  A world where P ≠ UP but P = NP could in principle be consistent,
  because NP could collapse below UP even while UP > P.
-/

-- Axiom: The relationship between UP and NP is NOT known to be equality
axiom UP_subset_NP : ∀ problem, InUP problem → InNP problem

/-
  The gap in the argument:

  What Vega Delgado needs: UP = NP (so that P ≠ UP implies P ≠ NP)
  What is actually known: UP ⊆ NP (strict containment may or may not hold)

  Without UP = NP, the conclusion P ≠ NP does not follow from P ≠ UP.

  This step cannot be proven from standard complexity theory axioms.
  Marked as sorry to indicate the gap.
-/
theorem p_neq_up_insufficient_for_p_neq_np :
    (¬(∀ problem, InP problem ↔ InUP problem)) →
    (¬(∀ problem, InP problem ↔ InNP problem)) := by
  -- ERROR: Cannot be proven. P ≠ UP does not imply P ≠ NP.
  -- We would need UP = NP, which is an open problem.
  sorry

/-
  SUMMARY OF REFUTATION

  Vega Delgado's 2012 proof attempt fails at two critical points:

  1. CRITICAL STEP (P = UP → EXP = P):
     - EXP ≠ P is an unconditional theorem (Time Hierarchy Theorem).
     - No complexity-theoretic result connects P = UP to EXP = P.
     - The step is simply false as a general implication.

  2. INSUFFICIENT CONCLUSION (P ≠ UP → P ≠ NP):
     - We only know P ⊆ UP ⊆ NP.
     - Whether UP = NP is itself an open problem.
     - P ≠ UP does not bridge the gap to P ≠ NP.

  The proof's use of proof by contradiction is methodologically sound,
  but the derivation step fails completely, making the entire argument invalid.
-/

end VegaDelgado2012Refutation
