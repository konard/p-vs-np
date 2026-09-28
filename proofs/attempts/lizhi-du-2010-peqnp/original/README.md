# Original Paper: A Polynomial time Algorithm for 3SAT

**Author:** Lizhi Du
**Year:** 2010 (submitted April 12, 2010; ongoing revisions through 2025)
**arXiv ID:** [1004.3702](https://arxiv.org/abs/1004.3702)
**Subject Classification:** Computer Science - Computational Complexity (cs.CC)
**Woeginger's List:** Entry #60

---

## Abstract

The paper claims to solve the P vs NP problem by providing a polynomial-time algorithm for 3SAT. The approach introduces novel concepts including "checking trees, long unit paths, contradiction unit pairs, and 2-unit/3-unit layers" to transform 3SAT problems into 2SAT instances (which are solvable in polynomial time).

The author's claim: if Algorithm 1 is correct, since 3SAT is NP-complete, P equals NP.

---

## Paper Summary

### Core Concepts Introduced

Du introduces four key concepts to analyze 3SAT formulas:

1. **Checking Trees**: A tree structure built from a 3-CNF formula to represent its logical dependencies. Each node in the tree is a literal, and the tree encodes how literals constrain each other in the formula.

2. **Long Unit Paths**: Paths through the checking tree that follow unit propagation chains. These represent forced assignments when certain literals are assumed.

3. **Contradiction Unit Pairs**: Pairs of literals (x, ¬x) that, if they both appear in the same unit layer, would make the formula unsatisfiable. These serve as witnesses to unsatisfiability.

4. **2-unit and 3-unit Layers**: Structural classification of literals in the checking tree. A 2-unit layer contains literals derived from 2-clauses; a 3-unit layer contains literals derived from 3-clauses.

### Algorithm 1 Overview

The algorithm processes a 3-CNF formula φ as follows:

**Input:** A 3-CNF formula φ
**Output:** SAT or UNSAT

**Step 1:** Build a checking tree T for φ.

**Step 2:** Compute "useful units" for each literal in the checking tree — the set of literals that would be forced (propagated) if that literal is assigned true.

**Step 3 (THE FLAWED STEP):** For all pairs of literals (x, y) that appear in distinct 3-unit layers and are NOT contradiction pairs of T:
- Set useful_units(x) ← useful_units(x) ∩ useful_units(y)
- Set useful_units(y) ← useful_units(x) ∩ useful_units(y)

**Step 4:** If any literal's useful units become empty after Step 3, return UNSAT.

**Step 5:** Check for contradiction pairs in the updated structure. If found, return UNSAT; otherwise return SAT.

### Claimed Reduction to 2SAT

The core argument is that after processing through Algorithm 1, the satisfiability of the 3-CNF formula can be decided by examining the resulting 2SAT structure (the useful units after intersection). Since 2SAT is in P, this would give a polynomial-time algorithm for 3SAT.

### Claimed Complexity

The paper claims Algorithm 1 runs in polynomial time, though it does not give a precise complexity bound. Since 2SAT can be solved in O(n + m) time (where n is variables and m is clauses), the claimed algorithm would run in polynomial time overall.

---

## Key Mathematical Objects

### Checking Tree

```
T = (V, E, label)
where:
  V = literals that appear in φ
  E = edges representing unit propagation dependencies
  label assigns each node to a layer (2-unit or 3-unit)
```

### Useful Units

For a literal x, useful_units(x) is the set of literals that are "forced" (via unit propagation) when x is assigned true in the checking tree.

### Contradiction Pair

Two literals (x, y) form a contradiction pair if x = ¬y, meaning they cannot both be true simultaneously.

### The Intersection in Step 3

For non-contradiction pairs (x, y) in distinct 3-unit layers:

```
useful_units(x) ← useful_units(x) ∩ useful_units(y)
useful_units(y) ← useful_units(x) ∩ useful_units(y)
```

This intersection is claimed to preserve all valid satisfying assignments while eliminating invalid ones.

---

## Revision History

The paper has undergone an extraordinary number of revisions:

- **v1**: April 12, 2010 — Initial submission
- **v2–v10**: 2010 — Early revisions addressing initial feedback
- **v11–v50**: 2011–2019 — Ongoing revisions attempting to fix identified issues
- **v51–v95**: 2020–2025 — Further revisions; v95 submitted December 22, 2025

Despite 95 revisions over 15 years, the paper has not been accepted in peer-reviewed venues, and the fundamental flaw in Algorithm 1, Step 3 identified by He et al. (2024) remains unresolved.

---

## Stated Implications

Since 3SAT is NP-complete (Cook-Levin Theorem, 1971):
- If Algorithm 1 correctly solves 3SAT in polynomial time
- Then all NP problems can be solved in polynomial time
- Therefore P = NP

The author explicitly acknowledges this conditional: the proof of P = NP depends entirely on the correctness of Algorithm 1.

---

## References

[1] Du, L. (2010). "A Polynomial time Algorithm for 3SAT". arXiv:1004.3702.
Available at: https://arxiv.org/abs/1004.3702

[2] He, Y. et al. (2024). "A Critique of Du's 'A Polynomial-Time Algorithm for 3-SAT'". arXiv:2404.04395.
Available at: https://arxiv.org/abs/2404.04395

[3] Cook, S. A. (1971). "The complexity of theorem-proving procedures". STOC 1971, pp. 151–158.

[4] Woeginger's P vs NP List, Entry #60.
Available at: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
