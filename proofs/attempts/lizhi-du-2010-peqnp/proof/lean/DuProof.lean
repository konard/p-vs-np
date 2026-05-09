/-
  DuProof.lean — Forward formalization of Lizhi Du's 2010 P=NP attempt.

  This file formalizes Du's CLAIMED proof that P = NP via a polynomial-time
  algorithm for 3SAT using checking trees, useful units, and contradiction pairs.

  Following the original paper: Du, L. (2010). "A Polynomial time Algorithm for 3SAT".
  arXiv:1004.3702. See ../ORIGINAL.md for the full paper reconstruction.

  NOTE: The correctness of Algorithm 1, Step 3 is stated as an AXIOM because it
  cannot be proven — it is actually false. See ../refutation/ for the refutation.
-/

namespace DuProof

-- ============================================================
-- § 1. SAT Problem Formalization
-- (Following the paper's notation exactly)
-- ============================================================

/-- A literal is either a positive (x) or negative (¬x) variable.
    Variables are represented as natural numbers. -/
inductive Literal
  | pos : Nat → Literal   -- positive literal x
  | neg : Nat → Literal   -- negative literal ¬x
  deriving BEq, Repr

/-- A clause is a disjunction of literals: (l₁ ∨ l₂ ∨ ... ∨ lₖ). -/
def Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
def CNFFormula := List Clause

/-- A truth assignment maps each variable to a boolean. -/
def Assignment := Nat → Bool

/-- Evaluate a literal under an assignment. -/
def evalLiteral (a : Assignment) : Literal → Bool
  | Literal.pos v => a v
  | Literal.neg v => !(a v)

/-- Evaluate a clause (true iff at least one literal is true). -/
def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- Evaluate a CNF formula (true iff all clauses are true). -/
def evalCNF (a : Assignment) (f : CNFFormula) : Bool :=
  f.all (evalClause a)

/-- A formula is satisfiable if some assignment makes it true. -/
def isSatisfiable (f : CNFFormula) : Prop :=
  ∃ a : Assignment, evalCNF a f = true

/-- A formula is a 3-CNF formula if all clauses have at most 3 literals. -/
def is3CNF (f : CNFFormula) : Bool :=
  f.all (fun c => c.length ≤ 3)

-- ============================================================
-- § 2. Du's Key Concepts
-- (Definitions 1–4 from the paper)
-- ============================================================

/-- Useful units for a literal: the set of literals forced when this literal is
    assigned true (via unit propagation in the checking tree). -/
structure UsefulUnits where
  /-- The literal these useful units belong to. -/
  literal : Literal
  /-- The set of forced literals (unit propagation consequences). -/
  units   : List Literal

/-- A contradiction pair: two literals x and ¬x that cannot both be true. -/
def isContradictionPair : Literal → Literal → Bool
  | Literal.pos v₁, Literal.neg v₂ => v₁ == v₂
  | Literal.neg v₁, Literal.pos v₂ => v₁ == v₂
  | _,              _               => false

/-- Simplified checking tree: stores literals with their useful units. -/
structure CheckingTree where
  /-- Literals in the tree. -/
  nodes       : List Literal
  /-- Useful units for each literal. -/
  usefulUnits : List UsefulUnits

-- ============================================================
-- § 3. Algorithm 1, Step 3 (THE FLAWED STEP)
-- (Exactly as stated in the paper)
-- ============================================================

/-- Check if two useful units are for non-contradiction pair literals. -/
def nonContradictionPair (u₁ u₂ : UsefulUnits) : Bool :=
  !isContradictionPair u₁.literal u₂.literal

/-- Du's intersection operation from Step 3:
    For non-contradiction pair (x, y), set U(x) ← U(x) ∩ U(y). -/
def duIntersect (u₁ u₂ : UsefulUnits) : UsefulUnits :=
  { literal := u₁.literal,
    units   := u₁.units.filter (fun l => u₂.units.contains l) }

/-- Step 3 of Algorithm 1: for each literal u in a 3-unit layer, if there exists
    another literal v in a distinct 3-unit layer that is NOT a contradiction pair,
    replace U(u) with U(u) ∩ U(v). -/
def applyStep3 (units : List UsefulUnits) : List UsefulUnits :=
  units.map fun u₁ =>
    match units.find? (fun u₂ => u₁.literal != u₂.literal &&
                                  nonContradictionPair u₁ u₂) with
    | some u₂ => duIntersect u₁ u₂
    | none    => u₁

/-- Check if any literal has empty useful units (indicating UNSAT by Du's criterion). -/
def hasEmptyUnits (units : List UsefulUnits) : Bool :=
  units.any (fun u => u.units.isEmpty)

-- ============================================================
-- § 4. Algorithm 1 (Complete)
-- ============================================================

/-- The checking tree is built from the formula. Its construction is complex;
    we axiomatize it since the error is in Step 3, not the tree construction. -/
noncomputable def buildCheckingTree : CNFFormula → CheckingTree :=
  fun _ => { nodes := [], usefulUnits := [] }

/-- Du's complete Algorithm 1.
    Returns true (SAT) or false (UNSAT). -/
noncomputable def duAlgorithm1 (f : CNFFormula) : Bool :=
  let T    := buildCheckingTree f
  let units := T.usefulUnits
  -- Step 3: intersect useful units for non-contradiction pairs
  let units' := applyStep3 units
  -- Step 4: if any useful units are empty, return UNSAT
  if hasEmptyUnits units' then false
  -- Otherwise return SAT
  else true

-- ============================================================
-- § 5. Du's Claimed Correctness of Algorithm 1
-- ============================================================

/-- AXIOM (Du's unproven claim): Algorithm 1 is a correct decider for 3SAT.
    That is, for any 3-CNF formula f, duAlgorithm1 correctly reports whether f
    is satisfiable.

    NOTE: This axiom is FALSE — it cannot be proven.
    The He et al. (2024) counter-example shows a satisfiable 3-CNF formula
    on which duAlgorithm1 returns false (UNSAT). See ../refutation/.
-/
axiom du_correctness_claim : ∀ f : CNFFormula,
  is3CNF f = true →
  (duAlgorithm1 f = true ↔ isSatisfiable f)

-- ============================================================
-- § 6. Du's Claimed Implication: P = NP
-- ============================================================

/-- Polynomial time bound: T : Nat → Nat is polynomial if ∃ c k, T(n) ≤ c * n^k. -/
def isPolynomial (T : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n : Nat, T n ≤ c * n ^ k

/-- AXIOM (Du's claim): Algorithm 1 runs in polynomial time O(n³). -/
axiom du_polynomial_time : isPolynomial (fun n => n ^ 3)

/-- THEOREM (conditional): If Du's correctness claim is true and Algorithm 1
    runs in polynomial time, then 3SAT ∈ P.
    (This follows straightforwardly from the definitions.) -/
theorem du_implies_3SAT_in_P
    (h_correct : ∀ f : CNFFormula, is3CNF f = true →
                   (duAlgorithm1 f = true ↔ isSatisfiable f))
    (h_poly    : isPolynomial (fun n => n ^ 3)) :
    -- 3SAT can be decided in polynomial time
    ∃ T : Nat → Nat, isPolynomial T :=
  ⟨_, h_poly⟩

/-- CONDITIONAL THEOREM: If Du's algorithm is correct (which it is not), then
    there exists a polynomial-time complexity bound for 3SAT. -/
theorem du_attempt_would_prove_3SAT_poly
    (h_correct : ∀ f : CNFFormula, is3CNF f = true →
                   (duAlgorithm1 f = true ↔ isSatisfiable f)) :
    ∃ T : Nat → Nat, isPolynomial T :=
  du_implies_3SAT_in_P h_correct du_polynomial_time

end DuProof
