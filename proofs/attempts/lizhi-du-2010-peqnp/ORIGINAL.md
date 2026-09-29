# Original Paper: A Polynomial time Algorithm for 3SAT

**Author:** Lizhi Du
**Year:** 2010
**arXiv ID:** 1004.3702
**URL:** https://arxiv.org/abs/1004.3702
**Woeginger's List:** Entry #60

---

## Abstract (from arXiv)

> "We introduce checking trees, long unit paths, contradiction unit pairs, and 2-unit/3-unit layers for a CNF formula. We devise an algorithm to determine the satisfiability of a 3-SAT formula in polynomial time. If this algorithm is correct, since 3-SAT is NP-complete, P = NP."

---

## Section 1: Introduction

The paper starts by noting the distinction between 2SAT (in P) and 3SAT (NP-complete). Du observes that 2SAT can be solved efficiently using unit propagation and implication graphs, and proposes extending this to 3SAT via checking trees.

**Core Observation:** In 2-CNF formulas, each clause (x ∨ y) can be written as (¬x → y) and (¬y → x), forming an implication graph. The satisfiability of a 2-CNF formula can be decided by checking for cycles in this graph (specifically, whether a variable and its negation are in the same strongly connected component).

**Du's Extension Claim:** For 3-CNF formulas, a similar structure (checking trees + useful units) can be built and analyzed to decide satisfiability in polynomial time.

---

## Section 2: Key Definitions

### Definition 1: Checking Tree

Given a 3-CNF formula φ, the checking tree T(φ) is constructed as follows:

For each literal ℓ in φ, we track how assigning ℓ = true propagates through the formula. A checking tree is a rooted tree where:
- The root is a chosen literal (the "assumption")
- Child nodes are literals that are forced by the parent's assignment
- Edges represent unit propagation (when a clause is reduced to a unit)

**2-unit layers** contain literals arising from 2-clauses (after one literal is eliminated).
**3-unit layers** contain literals arising from 3-clauses.

### Definition 2: Useful Units

For a literal x in the checking tree T, the useful units U(x) are the set of literals that would be forced (via unit propagation in T) if x is assigned true.

Formally:
- U(x) = {y : y is in a unit clause created by assuming x = true and propagating}

### Definition 3: Contradiction Unit Pair

Two literals x and y form a **contradiction unit pair** (or contradiction pair) if x = ¬y. That is, if both x and y are forced by some assumption, the formula is unsatisfiable under that assumption.

### Definition 4: Long Unit Path

A long unit path is a path in the checking tree from root to leaf, representing a chain of forced assignments under the root assumption.

---

## Section 3: Algorithm 1

```
Algorithm 1: Du's 3SAT Decision Algorithm
Input:  A 3-CNF formula φ
Output: SAT or UNSAT

Step 1: Build the checking tree T for φ.

Step 2: Compute useful units U(x) for each literal x in T.
        If any contradiction pair (x, ¬x) appears in the same layer,
        return UNSAT.

Step 3: For all pairs (x, y) in distinct 3-unit layers that are NOT
        contradiction pairs of T:

        U(x) ← U(x) ∩ U(y)
        U(y) ← U(x) ∩ U(y)

        (i.e., replace the useful units of x and y with their intersection)

Step 4: If any literal z has U(z) = ∅ (empty useful units), return UNSAT.

Step 5: Check remaining structure for contradiction pairs.
        If found, return UNSAT.
        Otherwise, return SAT.
```

**Note:** Step 3 is the critical step where the error occurs (see refutation/).

---

## Section 4: Correctness Argument

Du's correctness argument proceeds roughly as follows:

**Claim:** After applying Step 3, the intersection operation preserves exactly those assignments that are compatible with all non-contradiction pairs in the 3-unit layers.

**Reasoning:**
1. If (x, y) are in distinct 3-unit layers and are not a contradiction pair, then any valid satisfying assignment must make both x and y "consistent."
2. Therefore, the valid assignments for x must be compatible with the valid assignments for y.
3. The intersection U(x) ∩ U(y) captures exactly these compatible assignments.

**The Flaw:** Step 3 incorrectly assumes that valid assignments for x and y must share useful units. In fact, a valid satisfying assignment may use only the assignments in U(x) or only the assignments in U(y), without needing any overlap. Taking the intersection prematurely eliminates valid solution branches.

---

## Section 5: Complexity Analysis

Du claims Algorithm 1 runs in polynomial time:

- Building the checking tree: O(n²) where n = number of literals
- Computing useful units: O(n²)
- Step 3 (pairwise intersections): O(n³) in the worst case
- Steps 4–5 (checking empties and contradictions): O(n)

**Claimed total:** O(n³) — polynomial in the size of the formula.

Since the 2SAT check at the end also runs in linear time, the overall algorithm is claimed to be polynomial.

---

## Section 6: Claimed Implication (P = NP)

Since 3SAT is NP-complete (Cook, 1971):
- Every NP problem reduces (in polynomial time) to 3SAT
- If 3SAT ∈ P, then every NP problem is in P
- Therefore P = NP

Du's final claim: "Since Algorithm 1 solves 3SAT in polynomial time, P = NP."

---

## Critical Flaw Identified by He et al. (2024)

He, Y. et al. (arXiv:2404.04395) identify the following specific flaw:

**In Step 3**, the intersection U(x) ∩ U(y) is taken for all non-contradiction pairs (x, y) in distinct 3-unit layers.

**The Counter-Example** (simplified):

Consider the formula:
```
φ = (s ∨ t ∨ ¬c) ∧ (¬s ∨ ¬t ∨ r) ∧ C₁ ∧ ... ∧ Cₙ ∧ (a ∨ b ∨ c)
```
where C₁, ..., Cₙ are any clauses satisfying the assumptions of Algorithm 1.

**What Algorithm 1 does:**
1. Builds the checking tree
2. When checking if (c, α) is a contradiction pair, removes ¬c and ¬α from T
3. Applies Step 3: forces s and t to be eliminated from α's useful units via intersection with another literal's (empty) useful units
4. U(α) becomes ∅
5. Returns UNSAT

**What is actually true:** φ is satisfiable (e.g., assign s = true, t = false, c = true, r = false, a = true).

**Conclusion:** Du's algorithm produces a **false negative** — it incorrectly declares a satisfiable formula to be unsatisfiable.

This creates an infinite family of counter-examples (for all valid choices of C₁, ..., Cₙ), definitively refuting the algorithm's correctness.

---

## References

[1] Du, L. (2010). "A Polynomial time Algorithm for 3SAT". arXiv:1004.3702.
    Available at: https://arxiv.org/abs/1004.3702

[2] He, Y. et al. (2024). "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'".
    arXiv:2404.04395. Available at: https://arxiv.org/abs/2404.04395

[3] Cook, S. A. (1971). "The complexity of theorem-proving procedures".
    Proceedings of STOC 1971, pp. 151–158.

[4] Aspvall, B., Plass, M. F., & Tarjan, R. E. (1979).
    "A linear-time algorithm for testing the truth of certain quantified boolean formulas".
    Information Processing Letters, 8(3), 121–123.
    (The linear-time 2SAT algorithm Du relies on)
