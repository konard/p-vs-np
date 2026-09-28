# Refutation: Why Jiang's 2009 P=NP Attempt Fails

## Summary

Jiang's attempt contains multiple critical errors that prevent the argument from establishing P = NP. This directory formalizes these refutations.

## The Fatal Errors

### Error 1: Vague Problem Definition (MSP)

**The Problem**: Jiang's MSP (Multistage Graph Simple Path) problem is not rigorously defined.

- Several symbols and operations appear without formal definition
- The precise input/output specification is unclear
- The claimed equivalence between HC instances and MSP instances cannot be verified

**Why This is Fatal**: Without a rigorous definition of MSP, it is impossible to:
- Verify that the reduction HC → MSP is correct
- Verify that the algorithm for MSP is correct
- Even determine what complexity class MSP belongs to

**Formalized**: `msp_definition_is_vague` axiom in refutation files

---

### Error 2: MSP May Be in P (Wrong Complexity Class)

**The Problem**: If MSP ∈ P (polynomial time), then the reduction HC → MSP is useless.

**Key Observation** (from Hacker News discussion):
> "Jiang's labelled multistage graphs correspond to partially ordered sets, and finding Hamiltonian cycles in their comparability graphs is known not to be NP-complete."

**Why This is Fatal**: For Jiang's argument to work:
- HC ≤_p MSP (HC polynomially reduces to MSP) must hold
- MSP ∈ P (MSP has a polynomial algorithm) must hold
- These two conditions are **contradictory** unless P = NP (which is what we're trying to prove!)

If MSP ∈ P, then we already have HC ≤_p MSP only if HC ∈ P. But assuming HC ∈ P is exactly what we need to prove — circular reasoning!

**Formalized**: `wrong_direction_theorem` in refutation files

---

### Error 3: Experimental Evidence ≠ Mathematical Proof

**The Problem**: The paper's "proof" of algorithm correctness is:
> "The algorithm has been tested on more than 5 × 10⁷ instances and always gives the correct answer."

**Why This is Fatal**:
1. A finite number of correct test cases cannot prove universal correctness
2. Many incorrect polynomial-time algorithms for NP-hard problems pass extensive testing
3. The author himself acknowledges: "Although there is no broad consensus with proving the correctness"

**Historical Parallel**: Many false proofs have appeared correct on all tested cases:
- Testing n = 1, 2, ..., N does not prove a property holds for all n
- Counterexamples may exist at sizes far larger than tested

**Formalized**: `experiments_not_proof_theorem` in refutation files

---

### Error 4: The Reduction Direction Argument

**The Underlying Logic Error**:

To prove P = NP via the strategy "HC reduces to problem X, and X ∈ P", we need:
1. HC ≤_p X: Every HC instance can be transformed to an X instance in polynomial time, such that HC instance has answer YES iff X instance has answer YES
2. X ∈ P: X has a polynomial-time algorithm

From (1) and (2), we get: HC instance → transform → X instance → polynomial algorithm → answer for HC

**The Problem**: Step (1) requires that HC instances MAP TO X instances such that the SAME ANSWER is preserved. If X ∈ P but the answer for X is always determined differently than for HC, then (1) cannot hold unless HC ∈ P (which requires proof).

The circular nature: "Reduce HC to X, solve X" only works when X is genuinely NP-complete and you have a genuine polynomial algorithm for X — which would disprove the hypothesis P ≠ NP.

**Formalized**: `reduction_requires_hardness_theorem` in refutation files

---

## Why No Formal Counterexample Exists

Unlike some P=NP attempts where an explicit counterexample (a graph where the algorithm fails) can be constructed, Jiang's attempt is vague enough that:
- The MSP problem definition is not precise enough to construct a counterexample
- The algorithm description is not precise enough to execute it and find a failure case
- The reduction construction is not precise enough to verify

This vagueness itself constitutes a refutation: an extraordinary claim requires extraordinary precision.

## Formalization Contents

- `lean/JiangRefutation.lean` - Lean 4 refutation
- `rocq/JiangRefutation.v` - Rocq refutation

Both files formalize:
1. Why experimental evidence is insufficient for a mathematical proof
2. Why the vague MSP definition makes the argument unverifiable
3. Why reducing HC to a problem in P would be circular (if MSP ∈ P)
4. Key lessons about rigorous mathematical proof in complexity theory

## See Also

- [`../original/README.md`](../original/README.md) - Original attempt description
- [`../proof/README.md`](../proof/README.md) - Forward proof formalization with marked gaps
