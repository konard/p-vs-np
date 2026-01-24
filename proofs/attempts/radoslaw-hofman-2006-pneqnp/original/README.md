# Original Proof Idea: Radoslaw Hofman (2006) - P≠NP

## The Claim

Radoslaw Hofman claims to prove **P ≠ NP** by establishing an exponential lower bound on the deterministic time complexity of the counted Boolean satisfiability problem (cSAT).

## The Core Approach

### Step 1: Define the cSAT Problem

Hofman defines the **counted Boolean satisfiability problem (cSAT)**:

**Input:**
- A Boolean formula φ in conjunctive normal form (CNF) with n variables
- A threshold L (written in unary, so its value contributes to input size)

**Question:** Does φ have at least L satisfying assignments?

**Key Properties:**
- cSAT ∈ NP: A nondeterministic Turing machine can guess L satisfying assignments and verify them in O(L·n) time
- cSAT is NP-complete: Reduce from SAT by setting L=1

### Step 2: Define the Measure Predicate μ

The paper introduces a predicate μ that counts the number of satisfying assignments using inclusion-exclusion:

- μ(FALSE) = 0
- μ(TRUE) = 2ⁿ
- μ(variable) = 2ⁿ⁻¹
- μ(¬φ) = 2ⁿ - μ(φ)
- μ(φ₁ ∨ φ₂) = μ(φ₁) + μ(φ₂) - μ(φ₁ ∧ φ₂)

The cSAT decision reduces to: "Is μ(φ) ≥ L?"

### Step 3: Appeal to Completeness of Boolean Algebra

Hofman invokes **Gödel's Completeness Theorem** for first-order logic:

> "Boolean algebra is a complete first-order theory. Every valid formula can be proven using axioms and inference rules (modus ponens, universal generalization)."

From this, he argues:
- Any deterministic algorithm solving cSAT must correspond to a sequence of transformations: φ → φ₁ → φ₂ → ... → TRUE/FALSE
- These transformations must be expressible in first-order predicate calculus (FOPC)
- Each transformation applies one of the Boolean algebra axioms (Ax1-Ax23) or the measure predicate

### Step 4: Analyze Transformation Costs (Table 3)

The paper analyzes each possible axiom and measure predicate application, claiming:

**Distributive Laws (Ax9, Ax10):**
- Ax9: a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)
- Ax10: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)

When applied to formulas with m₁ and m₂ terms, these laws cause multiplicative growth: the result has O(m₁ · m₂) terms.

**Measure Predicate for Disjunction (μ₆):**
- Computing μ(φ₁ ∨ φ₂ ∨ ... ∨ φₘ) using inclusion-exclusion requires evaluating 2ᵐ terms
- This causes exponential blowup in the number of operations

**Purifying Functions:**
- Any polynomial-time simplification (removing duplicates, constant folding, etc.) can only reduce formula size by polynomial factors
- This cannot overcome the exponential growth from distributive laws and inclusion-exclusion

### Step 5: Claim Exponential Lower Bound

From the transformation analysis, Hofman concludes:

1. **Theorem 5**: "The lower bound on computational complexity is equal to the minimal usage of resources for the best possible transformation of the formula in this language."

2. **Corollary**: Since all FOPC transformations require exponential time (due to distributive law blowup or inclusion-exclusion), any deterministic algorithm solving cSAT requires exponential time.

3. **Conclusion**: cSAT ∉ P, but cSAT ∈ NP, therefore P ≠ NP.

### Step 6: Address Large DTMs and Oracles

In Section H, Hofman anticipates the objection: "What if a Turing machine has a very large finite set of axioms, oracles, or transformation rules?"

He argues (**Theorem 6**):
- Even with an exponentially large finite set of "transformation patterns" TA, a deterministic machine cannot solve cSAT for arbitrarily large inputs
- As input size n grows, the number of distinct formulas grows faster than any fixed finite set can cover
- Therefore, even Large DTMs (LDTMs) cannot achieve polynomial time

### Step 7: Characterize Nondeterminism

The paper concludes that any polynomial-time solver for NP-complete problems must be "nondeterministic," interpreted as:
- Having an infinite number of objects
- Performing "lucky guessing"
- Being fundamentally different from deterministic computation

## Why This Approach Seemed Promising

The argument has several appealing features:

1. **Formal Foundation**: It builds on established results in logic (Gödel's Completeness Theorem) rather than ad hoc complexity arguments.

2. **Comprehensive Analysis**: Table 3 systematically analyzes all possible Boolean algebra axioms and transformation rules.

3. **Concrete Problem**: cSAT is a well-defined NP-complete problem with clear computational properties.

4. **Oracle Barriers**: Section H attempts to address the possibility of enhanced computational models.

5. **Verification Attempt**: Appendix VI.G claims to verify the methodology by showing 2SAT ∈ P via polynomial FOPC sequences.

## The Fundamental Problems

However, this approach contains critical flaws (detailed in the refutation):

1. **Confusion Between Provability and Computability**: Gödel's Completeness Theorem is about *logical provability*, not *computational complexity*. These are fundamentally different domains.

2. **Invalid Restriction to FOPC**: The paper assumes algorithms must follow FOPC axiom sequences, but provides no justification. Algorithms can use computational techniques (dynamic programming, memoization, symbolic manipulation) that don't map to short FOPC proofs.

3. **Incomplete Algorithm Space**: Table 3 only analyzes explicit axiom applications. It ignores algorithmic approaches like resolution, DPLL, or symbolic methods that don't expand formulas.

4. **Circular Lower Bound**: Theorem 5 defines the lower bound as "minimal transformation cost," then shows transformations are expensive—but this only proves transformations are expensive, not that all algorithms are expensive.

5. **LDTM Argument Fails**: Theorem 6 shows finite pattern sets can't cover all inputs—trivially true, but irrelevant. Algorithms *compute* answers; they don't use lookup tables.

6. **Mischaracterized Nondeterminism**: Nondeterministic Turing machines are well-defined computational models, not "infinite objects" or "lucky guessing."

## Historical Context

This paper was:
- Submitted to arXiv in April 2007 (arXiv:0704.0514)
- Revised in June 2007
- Received a "Certificate of Merit" at ICCS2007
- Listed as entry #34 on Woeginger's P vs NP page

The author also made similar claims about other famous problems (Collatz conjecture, Riemann Hypothesis) being unprovable, using analogous reasoning.

## References

- Hofman, R. (2007). "Complexity Considerations, cSAT Lower Bound". arXiv:0704.0514v2
- Gödel, K. (1929). "Über die Vollständigkeit des Logikkalküls" (On the Completeness of the Calculus of Logic)
- Woeginger, G. J. "The P-versus-NP page" - Entry #34

---

For a detailed analysis of where the proof fails, see [`../refutation/README.md`](../refutation/README.md).

For the original paper, see [`paper/hofman-2006.pdf`](paper/hofman-2006.pdf).
