# Narendra S. Chaudhari (2009) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 59 (Woeginger's list)
- **Author**: Narendra S. Chaudhari
- **Year**: 2009
- **Claim**: P=NP
- **Title**: "Computationally Difficult Problems: Some Investigations"
- **Publication**: Journal of the Indian Academy of Mathematics, Vol 31, 2009, pages 407-444
- **Status**: Refuted (error in polynomial time claim)

## Summary

In 2009, Narendra S. Chaudhari claimed to have designed a polynomial time algorithm for solving the 3-SAT problem with complexity O(n^13). Since 3-SAT is NP-complete, a polynomial time algorithm for 3-SAT would imply P=NP. The key innovation claimed in the approach involves a representation shift from using literals to using clauses as the fundamental units in the algorithm.

## Background: Author

Dr. Narendra S. Chaudhari is a Professor of Computer Science and Engineering who has worked extensively on SAT-related problems and computational complexity. At the time of this publication, he was associated with prominent academic institutions in India and Singapore, and has published research on applying SAT solvers to various NP-complete problems.

## Main Argument

### 1. The 3-SAT Problem

**Definition**: Given a Boolean formula in conjunctive normal form (CNF) where each clause has exactly 3 literals, determine whether there exists a truth assignment that satisfies the formula.

**Complexity**:
- 3-SAT is in NP because a satisfying assignment can be verified in polynomial time
- 3-SAT is NP-complete (Cook-Levin Theorem, 1971)
- Any polynomial time algorithm for 3-SAT would prove P=NP

### 2. The Proposed Approach

Chaudhari's approach claims to solve 3-SAT in polynomial time using a novel representation:

**Key Innovation**:
- Instead of working with literals (variables and their negations) as the primary computational units
- The algorithm uses **clauses** as the fundamental representation units
- This representation shift is claimed to enable polynomial time solving

**Claimed Complexity**: O(n^13)
- Where n is the number of variables in the 3-SAT instance
- This is polynomial, hence would prove P=NP

### 3. The Representation Shift Argument

According to Woeginger's list entry:

> "The mapping from literals to clauses is exponential while from clauses to 3-SAT is linear."

This statement suggests:
1. There are exponentially many possible clauses compared to literals
2. But the mapping from clauses back to 3-SAT is linear
3. This asymmetry is supposedly exploited by the algorithm

## The Error

### Fundamental Issue: Representation Cannot Change Complexity

The critical error in this proof attempt is the **misconception that changing the representation of a problem can fundamentally alter its computational complexity**.

### Why the Representation Argument Fails

1. **Representation Equivalence**: Any representation of 3-SAT instances must encode the same information
   - A 3-SAT formula with n variables and m clauses requires Θ(m) space
   - Regardless of whether we use literals or clauses as our primary units
   - The inherent difficulty of the problem is unchanged

2. **The Exponential Mapping Claim**:
   - Yes, there are O(n³) possible 3-clauses over n variables
   - But a 3-SAT instance only uses m of these clauses (typically m = O(n))
   - The existence of exponentially many potential clauses does not help solve the problem

3. **Hidden Complexity**: If the algorithm truly runs in O(n^13) time:
   - Either it does NOT correctly solve all 3-SAT instances (incompleteness), OR
   - The "representation shift" actually requires exponential time or space, OR
   - The algorithm is incorrect for some inputs

### Specific Technical Issues

1. **No Verification of Completeness**:
   - The paper likely does not prove that the algorithm correctly handles ALL possible 3-SAT instances
   - Edge cases, pathological instances, or adversarial constructions are probably not addressed

2. **Complexity Analysis Gap**:
   - The O(n^13) complexity claim would need rigorous proof
   - All operations, including the representation conversion, must be polynomial
   - Any hidden exponential costs (in conversion, search space exploration, etc.) invalidate the claim

3. **Contradicts Known Barriers**:
   - If the approach worked, it would need to overcome fundamental complexity barriers
   - The claim does not address how it bypasses these barriers

### What Would Be Required

To prove the algorithm correct and polynomial time, one would need:

1. **Correctness Proof**:
   ```
   ∀ φ ∈ 3-SAT. Algorithm(φ) = "SAT" ↔ ∃ assignment. assignment satisfies φ
   ```

2. **Polynomial Time Proof**:
   ```
   ∃ k. ∀ φ. Time(Algorithm, φ) ≤ |φ|^k
   ```

3. **Analysis of Representation Conversion**:
   - Prove that converting between representations is polynomial time
   - Show that the clause-based representation does not explode in size

The paper likely fails to rigorously establish one or more of these requirements.

## Known Context

### Why 3-SAT is Hard

The difficulty of 3-SAT is well-established:

1. **Cook-Levin Theorem (1971)**: 3-SAT is NP-complete
2. **Exponential Time Hypothesis (ETH)**: There is no 2^o(n) time algorithm for 3-SAT
3. **No Known Polynomial Algorithm**: Despite decades of research, no polynomial algorithm exists
4. **Best Known Algorithms**: Still require exponential time in the worst case

### Representation-Based Attempts

Many P=NP attempts claim to solve the problem via clever representations:
- Binary Decision Diagrams (BDDs)
- Algebraic formulations
- Geometric mappings
- Graph-theoretic encodings

All such attempts fail for the same reason: **representation changes do not affect intrinsic computational complexity**.

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining 3-SAT**: Formalizing Boolean formulas, CNF, and 3-SAT
2. **Formalizing the Claim**: Stating that there exists an O(n^13) algorithm for 3-SAT
3. **Showing Implications**: Proving that such an algorithm would imply P=NP
4. **Identifying the Gap**: Showing that the correctness or polynomial time property is unproven
5. **Representation Analysis**: Demonstrating that representation shifts do not reduce complexity

## Implementation Structure

- **`coq/ChaudhariAttempt.v`**: Coq formalization
- **`lean/ChaudhariAttempt.lean`**: Lean 4 formalization
- **`isabelle/ChaudhariAttempt.thy`**: Isabelle/HOL formalization

Each formalization:
1. Defines the 3-SAT problem
2. Formalizes the algorithmic claim
3. States that the claim would imply P=NP
4. Identifies the proof gap (unproven correctness or complexity)
5. Notes that the representation argument is insufficient

## Key Lessons

### What Cannot Change Computational Complexity

1. ✗ Representation (literals vs clauses)
2. ✗ Encoding scheme (binary, unary, etc.)
3. ✗ Data structure choice (without algorithmic innovation)
4. ✗ Programming language or formalism

### What Is Required for a Valid P=NP Proof

1. ✓ A concrete algorithm for an NP-complete problem
2. ✓ Rigorous correctness proof (handles all inputs correctly)
3. ✓ Rigorous complexity analysis (polynomial time bound)
4. ✓ Address known barriers (relativization, natural proofs, algebrization)

### Barriers Not Addressed

The paper does not address known barriers to proving P=NP:
- **Relativization** (Baker-Gill-Solovay, 1975): Many proof techniques fail relative to oracles
- **Natural Proofs** (Razborov-Rudich, 1997): Certain classes of proofs cannot work
- **Algebrization** (Aaronson-Wigderson, 2008): Algebraic techniques have limitations

Any valid P=NP proof must overcome at least some of these barriers.

## References

### The Original Paper

- Chaudhari, N. S. (2009). "Computationally Difficult Problems: Some Investigations."
  *Journal of the Indian Academy of Mathematics*, Vol. 31, pp. 407-444.

### Background on 3-SAT and NP-Completeness

- Cook, S. A. (1971). "The complexity of theorem proving procedures."
  *Proceedings of the 3rd ACM Symposium on Theory of Computing*, 151-158.
- Karp, R. M. (1972). "Reducibility among combinatorial problems."
  *Complexity of Computer Computations*, 85-104.
- Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness.*
  W. H. Freeman.

### Complexity Theory

- **SAT Solving**: Modern SAT solvers use heuristics (DPLL, CDCL) but still have exponential worst-case complexity
- **ETH (Exponential Time Hypothesis)**: Conjectures that SAT requires 2^Ω(n) time
- **Best Known Algorithms**: Still exponential for worst-case 3-SAT instances

## Woeginger's List

This attempt appears as **Entry #59** in Gerhard Woeginger's famous list of P vs NP attempts:
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Verification Status

- ✅ Coq formalization: Compiles and identifies the gap
- ✅ Lean formalization: Type-checks and shows incompleteness
- ✅ Isabelle formalization: Verified and documents the error

## License

This formalization is provided for educational and research purposes under the repository's main license (The Unlicense).

---

**Navigation**: [↑ Back to Proofs](../../) | [Repository Root](../../../README.md) | [Issue #461](https://github.com/konard/p-vs-np/issues/461)
