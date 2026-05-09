# Javaid Aslam (2008) - Refutation

## Why the Proof Fails

Aslam's 2008 P=NP attempt contains a fundamental error: **the algorithm does not correctly count perfect matchings in bipartite graphs**.

## The Fatal Error: Incorrect Counting

### The Claim

Aslam claimed that a "MinSet Sequence" structure can enumerate all perfect matchings in a bipartite graph in polynomial time O(n^45 log n). Since perfect matching counting is #P-complete, this would imply #P = FP and hence P = NP.

### The Counter-Example (arXiv:0904.3912)

In April 2009, researchers published "Refutation of Aslam's Proof that NP = P" demonstrating that:

1. **Concrete Counter-Example**: A specific bipartite graph was provided where Aslam's algorithm produces an incorrect count
2. **Missing Matchings**: The MinSet Sequence does not correctly enumerate all perfect matchings
3. **Algorithm Failure**: The algorithm fails for certain graph structures that expose the flaw in the MinSet approach

### Why This Is Fatal

A counting algorithm must be **universally correct** — it must produce the exact count for every possible input graph. A single counter-example is sufficient to refute such a universal claim.

## The Information-Theoretic Argument

Even without the counter-example, Aslam's approach faces a fundamental barrier:

- **MinSet Sequence size**: O(n^45) — polynomial
- **Perfect matchings in K_{n,n}**: n! — exponential

For the complete bipartite graph K_{n,n}, the number of perfect matchings is exactly n!, which grows much faster than any polynomial. A polynomial-size structure cannot encode this much information.

### Why Polynomial Compression Fails

The number of perfect matchings in K_{n,n} is n!, and by Stirling's approximation:

n! ≈ √(2πn) · (n/e)^n

This grows as Ω(n^n), which dominates any polynomial n^k for any fixed k. Therefore:

1. No polynomial-size data structure can enumerate all n! matchings
2. The MinSet Sequence, bounded by O(n^45), cannot represent n! values for large n
3. Aslam's claimed polynomial-time algorithm is impossible if it must correctly count all matchings

## Formal Refutation

The formalizations in this directory demonstrate:

1. **`aslam_counting_not_universal`**: The counting algorithm cannot be correct for all graphs
2. **`polynomial_structure_cannot_represent_factorial`**: Polynomial structures cannot represent factorial growth
3. **`aslam_proof_fails`**: Combined theorem showing both the counter-example and the information-theoretic argument
4. **`single_counterexample_suffices`**: A single counter-example refutes a universal claim

## Files

- **lean/AslamRefutation.lean**: Lean 4 formalization of the refutation
- **rocq/AslamRefutation.v**: Rocq formalization of the refutation

## Key Lessons

1. **Counter-Examples Refute Universal Claims**: One graph where the algorithm fails is enough
2. **Compression Has Limits**: Exponential information cannot be compressed polynomially
3. **#P-Completeness Is Strong**: If counting matchings were easy, all of #P would collapse
4. **Algorithm Correctness Is Non-Negotiable**: Must work on ALL inputs, not just typical ones
5. **Peer Review Works**: The refutation was published within months of the original claim

## References

- **Refutation Paper**: "Refutation of Aslam's Proof that NP = P" (2009)
  - arXiv:0904.3912
  - Available at: https://arxiv.org/abs/0904.3912

- **Aslam's Response**: "Further Refinements..." (2009)
  - arXiv:0906.5112
  - Available at: https://arxiv.org/abs/0906.5112

- **#P-Completeness**: Valiant, L. (1979). "The Complexity of Computing the Permanent"
