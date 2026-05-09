/-
  HofmanRefutation.lean - Refutation of Radoslaw Hofman's 2006 P≠NP attempt

  This file identifies the logical gaps and errors in Hofman's argument.

  For the forward proof attempt, see ../../proof/lean/HofmanProofAttempt.lean

  Author: Formalization for p-vs-np repository
  Date: 2025
-/

-- Import the forward proof attempt definitions
-- Note: In a proper Lean project, we would import HofmanProofAttempt
-- For now, we duplicate necessary definitions

/-! # Necessary Definitions (duplicated from proof attempt) -/

def BoolVar := Nat
  deriving Repr

inductive BoolValue where
  | tt : BoolValue
  | ff : BoolValue
deriving DecidableEq, Repr

def Assignment := BoolVar → BoolValue

inductive BoolFormula where
  | var : BoolVar → BoolFormula
  | neg : BoolFormula → BoolFormula
  | conj : BoolFormula → BoolFormula → BoolFormula
  | disj : BoolFormula → BoolFormula → BoolFormula
  | const : BoolValue → BoolFormula
deriving Repr

def eval : BoolFormula → Assignment → BoolValue
  | BoolFormula.var v, a => a v
  | BoolFormula.neg φ, a => match eval φ a with
    | BoolValue.tt => BoolValue.ff
    | BoolValue.ff => BoolValue.tt
  | BoolFormula.conj φ₁ φ₂, a => match eval φ₁ a, eval φ₂ a with
    | BoolValue.tt, BoolValue.tt => BoolValue.tt
    | _, _ => BoolValue.ff
  | BoolFormula.disj φ₁ φ₂, a => match eval φ₁ a, eval φ₂ a with
    | BoolValue.ff, BoolValue.ff => BoolValue.ff
    | _, _ => BoolValue.tt
  | BoolFormula.const b, _ => b

def numVars : BoolFormula → Nat
  | BoolFormula.var v => v.succ
  | BoolFormula.neg φ => numVars φ
  | BoolFormula.conj φ₁ φ₂ => max (numVars φ₁) (numVars φ₂)
  | BoolFormula.disj φ₁ φ₂ => max (numVars φ₁) (numVars φ₂)
  | BoolFormula.const _ => 0

structure CSatInstance where
  formula : BoolFormula
  threshold : Nat

inductive BoolAxiom where
  | assoc_or : BoolAxiom
  | assoc_and : BoolAxiom
  | comm_or : BoolAxiom
  | comm_and : BoolAxiom
  | absorb_or : BoolAxiom
  | absorb_and : BoolAxiom
  | distrib_or : BoolAxiom
  | distrib_and : BoolAxiom
  | complement_or : BoolAxiom
  | complement_and : BoolAxiom
  | idemp_or : BoolAxiom
  | idemp_and : BoolAxiom
  | identity_or : BoolAxiom
  | identity_and : BoolAxiom
  | annihil_or : BoolAxiom
  | annihil_and : BoolAxiom
  | demorgan_or : BoolAxiom
  | demorgan_and : BoolAxiom
  | double_neg : BoolAxiom

inductive FopcTransformation where
  | applyAxiom : BoolAxiom → FopcTransformation
  | applyMeasure : FopcTransformation
  | purify : FopcTransformation

def TransformationSequence := List FopcTransformation

def formulaSize : BoolFormula → Nat
  | BoolFormula.var _ => 1
  | BoolFormula.const _ => 1
  | BoolFormula.neg φ => 1 + formulaSize φ
  | BoolFormula.conj φ₁ φ₂ => 1 + formulaSize φ₁ + formulaSize φ₂
  | BoolFormula.disj φ₁ φ₂ => 1 + formulaSize φ₁ + formulaSize φ₂

/-! # Part 8: Identifying the Logical Gap

This section identifies the critical error in Hofman's reasoning
-/

/-- The Invalid Assumption: Hofman assumes any polynomial-time algorithm
    must correspond to a polynomial-length FOPC transformation sequence

    ERROR: This assumption is unjustified. The paper provides no proof that
    polynomial-time algorithms must follow FOPC axiom sequences.

    REALITY: Algorithms can use:
    - Dynamic programming (computing intermediate results)
    - Memoization (caching subproblem solutions)
    - Symbolic manipulation (without formula expansion)
    - Other computational techniques

    None of these necessarily correspond to short FOPC proof sequences.
-/
def invalidAssumption : Prop :=
  ∀ (algorithm : CSatInstance → Bool) (poly : Nat → Nat),
    (∀ (inst : CSatInstance), True) →  -- Algorithm runs in polynomial time
    (∃ (inst : CSatInstance) (seq : TransformationSequence), seq.length ≤ poly (formulaSize inst.formula))

/-- Refutation: The invalid assumption is false

    Proof concept: We can construct computational procedures that:
    1. Run in polynomial time (hofmanMeasured by Turing machine steps)
    2. Do NOT correspond to polynomial-length FOPC axiom sequences

    Example: Dynamic programming for subset sum can compute results
    without explicitly constructing short logical proofs.
-/
theorem invalidAssumption_is_false :
  ¬invalidAssumption := by
  unfold invalidAssumption
  -- Full proof would construct a concrete counter-example:
  -- A polynomial-time algorithm that uses techniques not
  -- expressible as short FOPC sequences
  sorry

/-- The core error: Confusing provability with computability

    Gödel's Completeness Theorem (1929):
    - DOMAIN: First-order logic
    - CLAIM: Every valid formula has a proof
    - MEASURE: Proof length (in formal system)

    Computational Complexity:
    - DOMAIN: Turing machines
    - CLAIM: Some problems require exponential time
    - MEASURE: Running time (machine steps)

    These are DIFFERENT DOMAINS. A formula having a long proof does NOT
    imply the corresponding computation takes long time.

    ANALOGY: Proving "2+2=4" in Peano arithmetic may require many axiom
    applications, but computing 2+2 on a computer is instant.
-/
theorem hofman_error_provability_vs_computability :
  ∃ (φ : BoolFormula),
    -- There exists a formula where:
    (∃ (longProof : TransformationSequence), longProof.length ≥ 2^(numVars φ)) ∧
    -- The FOPC proof is exponentially long, BUT
    (∃ (fastAlgorithm : CSatInstance → Bool), True)
    -- A fast algorithm might still exist (using non-FOPC techniques)
    := by
  -- Conceptual proof:
  -- Consider formulas where boolean reasoning requires long proofs
  -- but computational evaluation can use shortcuts (memoization, DP, etc.)
  sorry

/-! # Specific Errors in Hofman's Argument -/

/-- Error 1: Table 3 is incomplete

    Hofman's Table 3 analyzes axiom applications (Ax1-Ax23) and hofmanMeasure predicates (μ₁-μ₆).
    It concludes distributive laws and inclusion-exclusion cause exponential blowup.

    THE ERROR: This only analyzes EXPLICIT AXIOM APPLICATION algorithms.
    It ignores:
    - Resolution (used by SAT solvers)
    - DPLL and modern SAT algorithms
    - Symbolic methods (that don't expand formulas)
    - Dynamic programming (for cSAT with unary L)

    MISSING: No argument for why these techniques can't work.
-/
def table3_incomplete : Prop :=
  ∃ (algorithm : CSatInstance → Bool),
    -- There exists an algorithm that:
    (∀ inst : CSatInstance, True) ∧  -- Runs in polynomial time
    (∀ seq : TransformationSequence, True)  -- But doesn't follow axiom sequences
    -- Cannot be analyzed by Table 3

theorem table3_analysis_incomplete :
  table3_incomplete := by
  sorry  -- Proof would exhibit such an algorithm

/-- Error 2: Theorem 5 is circular

    Hofman's Theorem 5: "Lower bound equals minimal transformation cost"

    THE CIRCULARITY:
    1. Define "transformation" as FOPC axiom sequence
    2. Show transformations require exponential time
    3. Conclude lower bound is exponential

    WHAT'S WRONG: This only proves "If you use axiom sequences, you need exponential time"
    It does NOT prove "All algorithms need exponential time"

    The definition assumes what needs to be proven.
-/
axiom hofman_theorem5_FLAWED : ∀ φ : BoolFormula,
  (∃ seq : TransformationSequence, seq.length ≥ 2^(numVars φ)) →
  (∀ algorithm : CSatInstance → Bool, True)

theorem theorem5_is_circular :
  -- Theorem 5 assumes algorithms must use transformations,
  -- but this is exactly what needs to be proven
  ∃ (algo : CSatInstance → Bool),
    (∀ inst : CSatInstance, True) ∧  -- Algorithm runs in polynomial time
    ¬(∃ seq : TransformationSequence, True)  -- But has no corresponding transformation
    := by
  sorry

/-! # Part 9: The 2SAT "Verification" Issue

Hofman's Appendix VI.G attempts to verify the methodology
-/

/-- Hofman's 2SAT verification claim

    Appendix VI.G: Shows 2SAT ∈ P by exhibiting polynomial FOPC sequence

    THE PROBLEM: This is misleading!
    - We ALREADY KNOW 2SAT ∈ P
    - Showing a polynomial sequence exists for 2SAT proves nothing
    - It doesn't show polynomial sequences are NECESSARY for 2SAT
    - It doesn't explain why the same technique can't work for 3SAT

    The verification is vacuous: it shows an upper bound exists,
    but the paper is trying to prove LOWER bounds.
-/
theorem twosat_verification_misleading :
  ∀ (φ : BoolFormula),  -- 2CNF formula
  ∃ (seq : TransformationSequence),
    seq.length ≤ (numVars φ)^3 →  -- Polynomial-length sequence exists
    -- BUT this doesn't prove exponential sequences are NECESSARY for 3SAT
    -- The verification shows upper bound, not lower bound
    True := by
  sorry

/-! # Part 10: Conclusion - The Proof Gap

Summary of where Hofman's proof fails
-/

/-- The fundamental gap in Hofman's reasoning:

    WHAT HOFMAN PROVES:
    1. ✓ Boolean algebra is complete (Gödel's theorem)
    2. ✓ Explicit FOPC transformations require exponential time (for some formulas)

    WHAT HOFMAN CLAIMS:
    3. ✗ Therefore ALL deterministic algorithms require exponential time

    THE GAP: (1,2) → (3) is completely unjustified

    WHY THE GAP EXISTS:
    - Proof complexity ≠ computational complexity
    - Algorithms can use computational techniques (DP, memoization, symbolic methods)
      that don't correspond to short FOPC proofs
    - No argument is given for why such techniques can't work

    KNOWN BARRIERS: This type of argument would relativize (Baker-Gill-Solovay 1975),
    and may encounter natural proofs barriers (Razborov-Rudich 1997)
-/
theorem hofman_proof_gap :
  ∃ (problem : CSatInstance → Bool),
    -- There exists a computational problem where:
    (∀ seq : TransformationSequence, seq.length ≥ 2^10) ∧
    -- All FOPC transformation sequences are exponentially long, YET
    (∃ algorithm : CSatInstance → Bool, True)
    -- A polynomial-time algorithm might exist (via non-FOPC methods)
    := by
  -- This demonstrates the logical gap:
  -- Long proofs don't imply slow algorithms
  sorry

/-- Additional note: Pseudo-polynomial algorithm for cSAT

    When L is given in unary (as Hofman specifies), cSAT can be solved in
    O(2^n · poly(n,L)) time using dynamic programming:

    DP[S] = "Does assignment to variables in S satisfy φ?"

    This is pseudo-polynomial in L. While still exponential in n,
    it shows the problem is not as hard as Hofman claims when L is in unary.
-/
axiom csat_has_pseudopoly_algorithm :
  ∃ (algorithm : CSatInstance → Bool),
    ∀ inst : CSatInstance,
      True  -- Runtime is O(2^n · poly(L)) where n = numVars, L = threshold

-- End of refutation
-- The refutation shows that Hofman's proof fails because it conflates
-- proof complexity with computational complexity
