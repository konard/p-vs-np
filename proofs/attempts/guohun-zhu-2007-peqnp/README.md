# Guohun Zhu (2007) - P=NP Attempt

**Attempt ID**: 40
**Author**: Guohun Zhu
**Year**: 2007
**Claim**: P=NP
**Paper**: [arXiv:0704.0309v3](http://arxiv.org/abs/0704.0309v3) - "The Complexity of HCP in Digraphs with Degree Bound Two"
**Status**: **INVALID** - Critical error in counting argument and proof structure

---

## Summary

In July 2007, Guohun Zhu claimed to prove P=NP by providing a polynomial-time algorithm for the Hamiltonian Cycle Problem (HCP) in directed graphs with degree bound two. The paper constructs a bijection between directed graphs and balanced bipartite graphs, then argues that enumerating perfect matchings in the bipartite graph yields Hamiltonian cycles in polynomial time.

## Main Argument

### 1. Problem Definition

Zhu focuses on **Γ digraphs**: strongly connected directed graphs where each vertex has:
- In-degree: 1 ≤ d⁻(v) ≤ 2
- Out-degree: 1 ≤ d⁺(v) ≤ 2

The Hamiltonian Cycle Problem for such graphs is known to be NP-complete (Plesník, 1978).

### 2. The Projector Graph Construction (Theorem 1)

Given a Γ digraph D with incidence matrix C, Zhu constructs:
- Split C into C⁺ (positive entries) and C⁻ (negative entries)
- Build projector matrix: F = [C⁺; -C⁻] (vertically stacked)
- F represents a balanced bipartite graph G(X,Y;E) where:
  - |X| = |Y| = n (vertices)
  - Each vertex has degree 1 or 2
  - G has at most n/4 components of length 4

### 3. Hamiltonian Cycle ↔ Perfect Matching (Theorem 2)

**Theorem 2**: A Γ digraph D has a Hamiltonian cycle if and only if its projector graph G has a perfect matching M such that r(C') = n-1, where C' is the incidence matrix of the subgraph induced by edges corresponding to M.

**Key Insight**: If the rank condition is satisfied, the matching maps back to a Hamiltonian cycle.

### 4. The Counting Argument (Lemma 4 - THE CRITICAL ERROR)

**Lemma 4** (Page 7): *"The maximal number of labeled perfect matchings in a projector graph G is 2^(n/4), but the maximal number of unlabeled perfect matchings in a projector graph G is n/2."*

**The Claim**: Since there are at most n/2 non-isomorphic perfect matchings to check, and each can be verified in O(n³) time, the total complexity is O(n⁴).

### 5. The Algorithm (Theorem 3)

**Theorem 3**: Finding a Hamiltonian cycle in a Γ digraph can be done in O(n⁴) time by:
1. Constructing the projector graph G (polynomial time)
2. Enumerating all n/2 non-isomorphic perfect matchings
3. For each matching M, checking if r(F⁻¹(M)) = n-1
4. If yes, F⁻¹(M) is a Hamiltonian cycle

### 6. Extension and Conclusion

**Theorem 6**: The result extends to all digraphs with degree bound two (not just strongly connected).

**Theorem 7**: Since HCP in digraphs with degree bound two is NP-complete, and we can solve it in polynomial time, P=NP.

## The Error

### Location of the Error

**The error is in Lemma 4 (page 7) and the entire counting/enumeration argument.**

### What Goes Wrong

#### Error 1: Incorrect Counting of Perfect Matchings

**The Claim**: "The maximal number of unlabeled perfect matchings in a projector graph G is n/2."

**Why This Is Wrong**:

1. **Components with C₄ cycles**: Zhu claims there are at most n/4 components of length 4 in G.

2. **Two matchings per C₄**: Each 4-cycle has exactly 2 distinct perfect matchings.

3. **Faulty isomorphism reasoning**: Zhu argues that in the "unlabeled" case, matchings that differ only in which components use which matching are "isomorphic" and should be counted as one.

4. **The Mathematical Error**: Even if each C₄ component has 2 choices, with k = n/4 such components, the number of distinct perfect matchings is 2^k = 2^(n/4), NOT n/2.

5. **What Zhu Misses**: The paper confuses:
   - **Graph isomorphism** (structural equivalence of matchings)
   - **Combinatorial counting** (distinct matchings that may need enumeration)

   Even if some matchings are "isomorphic," they still represent different arc selections in the original digraph and must be checked separately.

#### Error 2: No Polynomial-Time Enumeration Algorithm

**The Critical Gap**: Zhu provides equations (10-11) for recursively updating matchings, but:

1. **No proof of completeness**: The recursive procedure is not proven to enumerate all relevant non-isomorphic matchings.

2. **No polynomial bound**: Even if there were n/2 matchings (which is false), there's no algorithm given to enumerate them in polynomial total time.

3. **NP-hardness of counting**: Counting perfect matchings in bipartite graphs is #P-complete. While finding ONE perfect matching is polynomial (Hopcroft-Karp), finding ALL matchings is exponential.

4. **The monotonicity claim**: Zhu claims the function r(F⁻¹(M)) is "monotonic" over a "poset" of matchings, but:
   - No formal definition of this poset is given
   - No proof that this ordering allows efficient enumeration
   - The claim is asserted without justification

#### Error 3: Exponential Growth in General Case

**What Actually Happens**:

- **Small components**: If G consists mostly of small cycles (C₄, C₆, etc.), the number of perfect matchings grows exponentially with the number of components.

- **Worst case**: A graph with k disjoint C₄ cycles has 2^k perfect matchings. For k = n/4, this is 2^(n/4) ≈ 1.189^n, which is exponential, not polynomial.

- **The n/2 bound**: The claim that "2 * (n/4) = n/2" conflates:
  - 2 (choices per component) + n/4 (number of components) ≠ 2 × n/4 ≠ n/2
  - The correct count is 2^(n/4), which is multiplicative, not additive.

### Why The Proof Fails

**Core Issue**: The paper fundamentally misunderstands combinatorial counting:

- ✓ Correct: Each C₄ component has 2 perfect matchings
- ✓ Correct: There are at most n/4 such components
- ✗ **WRONG**: 2^(n/4) matchings ≠ n/2 matchings
- ✗ **WRONG**: No polynomial-time enumeration algorithm provided
- ✗ **WRONG**: The "isomorphism" argument doesn't reduce exponential to linear

**What Would Be Needed**:

To make this approach work, Zhu would need to:

1. Prove that the number of matchings to check is polynomial (currently false)
2. Provide an algorithm to enumerate all relevant matchings in polynomial time (currently missing)
3. Show that the rank-checking approach doesn't miss any Hamiltonian cycles (currently unproven)

None of these are accomplished in the paper.

### Specific Technical Issues

1. **Equation (9) - Binary coding**: The coding scheme maps each matching to a binary string, but this doesn't help if there are exponentially many strings.

2. **Proposition 1** (Page 7): "If code(M₁) = code(M₂), then r(F⁻¹(M₁)) = r(F⁻¹(M₂))" - this is correct but irrelevant to the complexity analysis.

3. **Equations (10-12)**: The recursive update M(t+1) = ... lacks:
   - Formal definition of the ⊗ operation
   - Proof of termination
   - Proof that all matchings are enumerated
   - Complexity analysis

4. **Section 5.2 - Extension to degree-2 graphs**: The vertex-splitting technique doubles the graph size, but this doesn't fix the fundamental counting error.

## Known Refutations

While no formal published refutation exists specifically for this paper (it received minimal attention), the claim contradicts:

1. **Basic combinatorics**: 2^(n/4) is exponential, not O(n)
2. **Complexity theory**: If HCP on degree-2 digraphs were in P, P=NP would have been proven
3. **The P≠NP consensus**: The overwhelming belief backed by extensive evidence

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the constructions**: Formalizing Γ digraphs, projector graphs, and the bijection
2. **Formalizing Lemma 4**: Stating precisely what the paper claims about matching counts
3. **Counterexample**: Showing that a graph with k disjoint C₄ cycles has 2^k matchings, not 2k
4. **Identifying the gap**: The paper provides no polynomial-time enumeration algorithm
5. **Noting impossibility**: If such an algorithm existed, P=NP would follow, but the proof is incomplete

## Implementation Structure

- **`lean/ZhuAttempt.lean`**: Lean 4 formalization
- **`coq/ZhuAttempt.v`**: Coq formalization
- **`isabelle/ZhuAttempt.thy`**: Isabelle/HOL formalization
- **`paper/zhu-2007.pdf`**: Original paper from arXiv

Each formalization:
1. Defines Γ digraphs and the projector graph construction
2. Formalizes the bijection between matchings and cycle sets
3. Models the counting error in Lemma 4
4. Provides a counterexample showing exponential matching count
5. Notes that the enumeration algorithm is underspecified
6. Concludes the proof is invalid

## Key Lessons

### What the Paper Got Right

1. ✓ The projector graph construction is valid
2. ✓ Theorem 1: The bijection F: D → G is correctly defined
3. ✓ Theorem 2: The correspondence between Hamiltonian cycles and certain perfect matchings is correct
4. ✓ The rank condition r(C') = n-1 correctly identifies strong connectivity

### What the Paper Got Wrong

1. ✗ Lemma 4: The counting argument is fundamentally flawed
2. ✗ The number of matchings is 2^(n/4), not n/2
3. ✗ No polynomial-time enumeration algorithm is provided
4. ✗ The "isomorphism" argument doesn't reduce complexity
5. ✗ Invalid conclusion that P=NP

### Barriers Not Addressed

The paper does not address known barriers to proving P=NP:
- **Relativization** (Baker-Gill-Solovay, 1975)
- **Natural Proofs** (Razborov-Rudich, 1997)
- **Algebrization** (Aaronson-Wigderson, 2008)

If the matching-based approach worked, it would need to explain how it overcomes these barriers.

## The Fundamental Issue

**Why This Approach Cannot Work**:

The paper essentially claims:
> "We can solve an NP-complete problem by checking polynomially many cases."

But the number of cases is actually exponential. The error is a simple arithmetic mistake:
- **Paper claims**: n/4 components × 2 choices = n/2 matchings (addition/linear)
- **Reality**: n/4 components × 2 choices = 2^(n/4) matchings (exponentiation)

This is a critical misunderstanding of combinatorial explosion, which is the very reason NP-complete problems are hard.

## References

### The Original Paper

- Zhu, G. (2007). "The Complexity of HCP in Digraphs with Degree Bound Two." arXiv:0704.0309v3 [cs.CC]
  - URL: https://arxiv.org/abs/0704.0309

### Background

- Cook, S. A. (1971). "The complexity of theorem proving procedures." *Proceedings of the 3rd ACM Symposium on Theory of Computing*, 151-158.
- Karp, R. M. (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, 85-104.
- Plesník, J. (1978). "The NP-Completeness of the Hamiltonian Cycle Problem in Planar Digraphs with Degree Bound Two." *Information Processing Letters*, 8(4), 199-201.

### Relevant Theory

- **Hamiltonian Cycle**: NP-complete (Karp, 1972)
- **Perfect Matching**: Polynomial-time for bipartite graphs (Hopcroft-Karp, 1973)
- **Counting Matchings**: #P-complete (Valiant, 1979)
- **Graph Isomorphism**: Not known to be in P or NP-complete

## Woeginger's List

This attempt appears as **Entry #40** in Gerhard Woeginger's famous list of P vs NP attempts:
- URL: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Listed as: Guohun Zhu (2007) - P=NP claim via Hamiltonian cycles in degree-bounded digraphs

## Verification Status

- ✅ Coq formalization: Identifies the counting error and gap in enumeration
- ✅ Lean formalization: Provides counterexample with exponential matchings
- ✅ Isabelle formalization: Formalizes the invalid proof step

## License

This formalization is provided for educational and research purposes under the repository's main license (The Unlicense).

---

**Navigation**: [↑ Back to Proofs](../../) | [Repository Root](../../../README.md) | [Issue #445](https://github.com/konard/p-vs-np/issues/445)
