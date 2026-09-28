import proofs.complexity.lean.Complexity
/-
  WeissRefutation.lean - Refutation of Angela Weiss's 2011 P=NP attempt

  This file proves that the number of assignments, and the leaves of a full
  binary cut tree, grow faster than every polynomial. These counting facts
  alone do not establish a lower bound for a KE algorithm or a compressed
  representation. Such a conclusion needs a separate link to the algorithm.
-/

namespace WeissRefutation2011

-- ============================================================
-- Basic Definitions (mirroring the proof file)
-- ============================================================

abbrev Var := Nat

inductive Literal where
  | pos : Var → Literal
  | neg : Var → Literal
deriving DecidableEq, Repr

def Assignment := Var → Bool

def evalLiteral (α : Assignment) : Literal → Bool
  | Literal.pos v => α v
  | Literal.neg v => !α v

-- ============================================================
-- Complexity Definitions
-- ============================================================

def isPolynomial (T : Nat → Nat) : Prop :=
  Complexity.PolynomiallyBounded T

def isExponential (T : Nat → Nat) : Prop :=
  ∃ base : Nat, base > 1 ∧ ∀ c k : Nat, ∃ n : Nat, T n > c * n ^ k

-- ============================================================
-- Counting complete assignments
-- ============================================================

-- The number of complete variable assignments for n variables is 2^n
def numAssignments (numVars : Nat) : Nat := 2 ^ numVars

-- For m ≥ 4, m² ≤ 2^m. We use this to bound the polynomial exponent.
private theorem square_le_two_pow (t : Nat) :
    (t + 4) * (t + 4) ≤ 2 ^ (t + 4) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have hmul : 3 * (t + 4) ≤ (t + 4) * (t + 4) :=
      Nat.mul_le_mul_right (t + 4) (by omega : 3 ≤ t + 4)
    rw [show Nat.succ t + 4 = (t + 4) + 1 by omega, Nat.pow_succ]
    have hstep : ((t + 4) + 1) * ((t + 4) + 1) ≤
        ((t + 4) * (t + 4)) * 2 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    exact Nat.le_trans hstep (Nat.mul_le_mul_right 2 ih)

private theorem self_le_two_pow (c : Nat) : c ≤ 2 ^ c := by
  induction c with
  | zero => decide
  | succ c ih =>
    rw [Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega

-- Choose m = c + k + 8 and n = 2^m. Then
-- c + m*k < m² ≤ 2^m, hence c*n^k ≤ 2^(c+m*k) < 2^n.
theorem numAssignments_exponential : isExponential numAssignments := by
  refine ⟨2, by decide, ?_⟩
  intro c k
  let m := c + k + 8
  have hm : m ≥ 4 := by dsimp [m]; omega
  have hsq : m * m ≤ 2 ^ m := by
    have h := square_le_two_pow (m - 4)
    simpa [Nat.sub_add_cancel hm] using h
  have hkm : m * (k + 1) ≤ m * m :=
    Nat.mul_le_mul_left m (by dsimp [m]; omega : k + 1 ≤ m)
  have hless : c + m * k < 2 ^ m := by
    have hc : c < m := by dsimp [m]; omega
    rw [Nat.mul_add, Nat.mul_one] at hkm
    omega
  refine ⟨2 ^ m, ?_⟩
  have hpow : 2 ^ (c + m * k) < 2 ^ (2 ^ m) :=
    Nat.pow_lt_pow_of_lt (by decide) hless
  have hcoeff : c * 2 ^ (m * k) ≤ 2 ^ (c + m * k) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (self_le_two_pow c)
  change c * (2 ^ m) ^ k < 2 ^ (2 ^ m)
  rw [← Nat.pow_mul]
  exact Nat.lt_of_le_of_lt hcoeff hpow

-- ============================================================
-- A lower bound for any particular algorithm needs an additional premise.
-- ============================================================

theorem enumerating_all_assignments_is_exponential (work : Nat → Nat)
    (henumerates : ∀ n, numAssignments n ≤ work n) : isExponential work := by
  obtain ⟨base, hbase, hcount⟩ := numAssignments_exponential
  refine ⟨base, hbase, ?_⟩
  intro c k
  obtain ⟨n, hn⟩ := hcount c k
  exact ⟨n, Nat.lt_of_lt_of_le hn (henumerates n)⟩

-- ============================================================
-- A full binary tree of n unconditional cuts has 2^n leaves.
-- ============================================================

def fullCutTreeLeafCount (numVars : Nat) : Nat := 2 ^ numVars

-- This counts a full cut tree. It does not say a KE solver must build one.
theorem full_ke_cut_tree_exponential : isExponential fullCutTreeLeafCount := by
  exact numAssignments_exponential

-- ============================================================
-- Summary of the two counts
-- ============================================================

theorem counting_facts_for_weiss :
    -- Complete assignments grow exponentially.
    isExponential numAssignments ∧
    -- So do leaves of a full cut tree.
    isExponential fullCutTreeLeafCount := by
  constructor
  · exact numAssignments_exponential
  · exact full_ke_cut_tree_exponential

-- ============================================================
-- What Weiss Would Need to Prove
-- ============================================================

-- A lower bound for the actual KE algorithm would require a proved premise
-- such as henumerates above, derived from its concrete operational semantics.
-- Assignment counting does not supply that premise.
end WeissRefutation2011
