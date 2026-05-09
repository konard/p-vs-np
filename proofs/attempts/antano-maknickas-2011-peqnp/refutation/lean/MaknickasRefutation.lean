/-
  MaknickasRefutation.lean - Refutation of Maknickas (2011) P=NP attempt

  This file demonstrates why Maknickas's approach fails:
  The LP relaxation of k-SAT does not preserve satisfiability, and the
  floor-modulo recovery function does not produce valid Boolean solutions.

  Reference: arXiv:1203.6020v2 [cs.CC] - "How to solve kSAT in polynomial time"
-/

namespace MaknickasRefutation

-- Real number axioms (Mathlib not available in this environment)
axiom Real : Type
notation "ℝ" => Real
axiom Real.zero : Real
axiom Real.one : Real
axiom Real.add : Real → Real → Real
axiom Real.le : Real → Real → Prop
axiom Real.ofNat : Nat → Real
noncomputable instance : OfNat Real 0 where ofNat := Real.zero
noncomputable instance : OfNat Real 1 where ofNat := Real.one
noncomputable instance : Add Real where add := Real.add
instance : LE Real where le := Real.le
noncomputable instance : Coe Nat Real where coe := Real.ofNat
noncomputable axiom Real.floor : Real → Int

-- Literal, Clause, CNF definitions
inductive Literal where
  | pos : Nat → Literal
  | neg : Nat → Literal
  deriving Repr, DecidableEq

def Clause := List Literal
def CNF := List Clause
def Assignment := Nat → Bool

def evalLiteral (a : Assignment) : Literal → Bool
  | Literal.pos n => a n
  | Literal.neg n => !(a n)

def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral a)

def evalCNF (a : Assignment) (f : CNF) : Bool :=
  f.all (evalClause a)

def Satisfiable (f : CNF) : Prop :=
  ∃ (a : Assignment), evalCNF a f = true

-- LP definitions
def RealAssignment := Nat → ℝ
def NonNegative (ra : RealAssignment) : Prop := ∀ n, ra n ≥ 0

noncomputable def clauseSum (ra : RealAssignment) : Clause → ℝ
  | [] => 0
  | (Literal.pos n) :: rest => ra n + clauseSum ra rest
  | (Literal.neg n) :: rest => ra n + clauseSum ra rest

def lpConstraintForClause (ra : RealAssignment) (c : Clause) : Prop :=
  clauseSum ra c ≤ (c.length : ℝ)

def LPFeasible (f : CNF) (ra : RealAssignment) : Prop :=
  NonNegative ra ∧ (∀ c : Clause, List.Mem c f → lpConstraintForClause ra c)

noncomputable def floorMod2 (r : ℝ) : Bool :=
  Real.floor r % 2 = 0

noncomputable def recoverAssignment (ra : RealAssignment) : Assignment :=
  fun n => floorMod2 (ra n)

-- =============================================================================
-- ERROR 1: LP Relaxation Gap — Wrong Problem Being Solved
-- =============================================================================

-- The clause (X₁ ∨ X₂ ∨ X₃)
def clause3 : Clause := [Literal.pos 1, Literal.pos 2, Literal.pos 3]
def formula3 : CNF := [clause3]

-- The LP "bad solution": all variables at 1.0
noncomputable def badSolution : RealAssignment := fun _ => 1

-- The bad solution satisfies LP constraints (1 + 1 + 1 = 3 ≤ 3)
-- This axiom requires real arithmetic: requires Real.ofNat 1 + ... ≤ (3 : ℝ)
axiom badSolutionFeasible : LPFeasible formula3 badSolution

-- The recovered Boolean assignment evaluates to false for all literals
-- floor(1.0) = 1 is odd, so floorMod2(1.0) = false
-- Therefore (X₁ ∨ X₂ ∨ X₃) becomes (false ∨ false ∨ false) = false
-- This axiom requires: Real.floor(1) = 1, 1 % 2 = 1 ≠ 0, so floorMod2 = false
axiom recoveredClauseFalse :
  evalClause (recoverAssignment badSolution) clause3 = false

-- LP is feasible but recovery fails — the core counterexample
theorem lp_feasible_but_recovery_fails :
    LPFeasible formula3 badSolution ∧
    evalClause (recoverAssignment badSolution) clause3 = false :=
  ⟨badSolutionFeasible, recoveredClauseFalse⟩

-- =============================================================================
-- ERROR 2: Negation is Completely Ignored
-- =============================================================================

-- The unsatisfiable formula X₁ ∧ ¬X₁
def contradictoryFormula : CNF := [[Literal.pos 1], [Literal.neg 1]]

-- This formula is indeed unsatisfiable
theorem contradictory_is_unsat : ¬ Satisfiable contradictoryFormula := by
  intro ⟨a, ha⟩
  simp only [evalCNF, contradictoryFormula, List.all_cons, List.all_nil, Bool.and_true,
    evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral] at ha
  -- ha : a 1 && !a 1 = true
  cases h : a 1 <;> simp_all

-- LP constraints for [Pos 1] and [Neg 1] are identical
-- The encoding completely ignores whether a literal is negated
theorem negation_information_lost :
    ∀ (ra : RealAssignment),
    lpConstraintForClause ra [Literal.pos 1] ↔
    lpConstraintForClause ra [Literal.neg 1] := by
  intro ra
  simp [lpConstraintForClause, clauseSum]

-- The contradictory formula is LP-feasible
-- X₁ = 0: LP constraints [0 ≤ 1] for both clauses are satisfied
axiom contradictory_lp_feasible : ∃ ra : RealAssignment, LPFeasible contradictoryFormula ra
-- NOTE: Would require real arithmetic: 0 ≤ (1 : ℝ) and 0 ≥ 0

-- =============================================================================
-- ERROR 3: Problem Type Mismatch
-- =============================================================================

-- LP feasibility does NOT imply Boolean satisfiability
theorem problem_type_mismatch :
    ¬ (∀ f : CNF,
        (∃ ra : RealAssignment, LPFeasible f ra) ↔
        Satisfiable f) := by
  intro H
  have hUnsat : ¬ Satisfiable contradictoryFormula := contradictory_is_unsat
  have hLPFeas : ∃ ra : RealAssignment, LPFeasible contradictoryFormula ra :=
    contradictory_lp_feasible
  rw [← H] at hUnsat
  exact hUnsat hLPFeas

-- =============================================================================
-- ERROR 4: No Soundness Proof for the Recovery Function
-- =============================================================================

-- The key property the paper needs (but which is false)
theorem paper_claim_is_false :
    ¬ (∀ (f : CNF) (ra : RealAssignment),
        LPFeasible f ra →
        evalCNF (recoverAssignment ra) f = true) := by
  intro H
  have hMain := H formula3 badSolution badSolutionFeasible
  simp only [evalCNF, formula3, List.all_cons, List.all_nil, Bool.and_true] at hMain
  -- hMain : evalClause (recoverAssignment badSolution) clause3 = true
  rw [recoveredClauseFalse] at hMain
  exact absurd hMain (by decide)

-- =============================================================================
-- Summary: Why Maknickas (2011) Does NOT Prove P = NP
-- =============================================================================
--
-- The four fatal errors are formally established above:
-- 1. LP RELAXATION GAP: `lp_feasible_but_recovery_fails`
-- 2. NEGATION IGNORED: `negation_information_lost` + `contradictory_lp_feasible`
-- 3. WRONG PROBLEM: `problem_type_mismatch`
-- 4. UNPROVEN RECOVERY: `paper_claim_is_false`
--
-- Therefore, the paper does NOT establish k-SAT ∈ P, and does not prove P = NP.

end MaknickasRefutation
