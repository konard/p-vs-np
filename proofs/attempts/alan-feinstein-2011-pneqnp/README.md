# Alan Feinstein (2011) - P≠NP Proof Attempt

**Attempt ID**: 78 (Woeginger's List)
**Author**: Craig Alan Feinstein
**Year**: 2011 (arxiv version from 2006-2011)
**Claim**: P ≠ NP
**Status**: **REFUTED**

## Overview

In November 2011, Craig Alan Feinstein claimed to prove that P is not equal to NP by showing that the Traveling Salesman Problem (TSP) cannot be solved in polynomial time on a classical computer. The argument is surprisingly short and focuses on establishing a lower bound for TSP.

## Source

- **Paper**: "The Computational Complexity of the Traveling Salesman Problem"
- **arXiv**: [cs/0611082](http://arxiv.org/abs/cs/0611082)
- **Versions**: Initial submission November 17, 2006; v5 November 16, 2011; v6 February 1, 2012
- **Woeginger's List**: Entry #78 (note: some sources list as #82)
- **Refutation**: [arXiv:0706.2035](https://arxiv.org/abs/0706.2035) - "Critique of Feinstein's Proof that P is not Equal to NP"

## Main Argument

### Feinstein's Approach

Feinstein's proof attempts to establish that P ≠ NP through the following argument:

1. **Focus on TSP**: The Traveling Salesman Problem is NP-hard
2. **Lower Bound Claim**: Any deterministic exact algorithm for TSP requires Θ(2^n) time
3. **Justification**:
   - TSP solutions require evaluating all possible subsets of cities
   - Uses a recursive relationship computing Δ(S, i), representing the shortest path visiting cities in subset S
   - Claims the algorithm must examine Θ(2^n) subsets
4. **Conclusion**: Since TSP is in NP and requires exponential time, P ≠ NP

### Key Technical Claims

- The proof analyzes the well-known Held-Karp dynamic programming algorithm (1962)
- Claims this algorithm is optimal in the sense that no polynomial-time algorithm exists
- Attempts to show that the exponential lower bound is necessary, not just the best known upper bound

## The Error

### Primary Flaw: Confusing Lower Bounds with Upper Bounds

The fundamental error in Feinstein's proof is confusing algorithmic analysis:

1. **Upper Bound vs. Lower Bound**:
   - The Held-Karp algorithm provides an O(2^n · n²) **upper bound** on TSP
   - This shows TSP can be solved in exponential time
   - It does NOT prove that TSP cannot be solved faster

2. **Lack of Lower Bound Proof**:
   - Feinstein assumes that because we must "consider" 2^n subsets, this is a lower bound
   - However, this reasoning is informal and non-rigorous
   - There is no proof that a different algorithmic approach couldn't avoid examining all subsets
   - Many problems have known algorithms that seem to require checking all possibilities, yet clever techniques find shortcuts

3. **Incorrect Use of Reduction**:
   - The critique paper (arXiv:0706.2035) identifies "incorrect use of reduction"
   - Feinstein makes "incorrect assumptions about the complexity of a problem"
   - The reasoning about problem complexity based on reductions is fundamentally flawed

### Why This Error is Common

This type of error appears frequently in attempted P vs NP proofs:

- **Intuition vs. Proof**: It's intuitive that TSP "seems" to require checking all possibilities
- **Best Known ≠ Best Possible**: The best known algorithm is not necessarily optimal
- **Lower Bounds are Hard**: Proving lower bounds is precisely what makes P vs NP so difficult
- **Informal Reasoning**: Phrases like "must consider all subsets" are often informal, not rigorous mathematical statements

### What Would Be Needed for a Valid Proof

To validly prove TSP requires exponential time, one would need:

1. **Rigorous Lower Bound**: Prove that ANY algorithm solving TSP must use at least Ω(2^εn) operations for some ε > 0
2. **Universal Quantification**: Show this holds for ALL possible algorithms, not just known ones
3. **Formal Model**: Work in a precise computational model (e.g., Turing machines, circuits, algebraic computation)
4. **Barrier Awareness**: Address or circumvent known barriers:
   - Relativization (Baker-Gill-Solovay, 1975)
   - Natural Proofs (Razborov-Rudich, 1997)
   - Algebrization (Aaronson-Wigderson, 2008)

## Formalization Strategy

Our formalization in Rocq, Lean, and Isabelle will:

1. **Model TSP**: Define the Traveling Salesman Problem formally
2. **Model the Held-Karp Algorithm**: Formalize the dynamic programming approach
3. **Formalize the Upper Bound**: Prove the algorithm runs in O(2^n · n²) time
4. **Expose the Gap**: Show where the claimed lower bound proof fails
5. **Use Admitted/sorry/oops**: Mark the unproven lower bound claim

### Structure of Formalization

Each proof assistant implementation includes:

- `DecisionProblem`: Abstract type for decision problems
- `TSP`: Concrete TSP problem definition
- `HeldKarpAlgorithm`: Formalization of the dynamic programming approach
- `UpperBoundProof`: Theorem that algorithm runs in exponential time
- `LowerBoundClaim`: **INCOMPLETE** - The claimed lower bound (left as admitted)
- `FeinsteinsArgument`: Structure showing the gap in reasoning

## Educational Value

This formalization demonstrates:

1. **Difference between bounds**:
   - Upper bounds (what we can do)
   - Lower bounds (what we cannot do)

2. **Burden of proof**:
   - Showing an algorithm exists is constructive
   - Showing no algorithm exists requires universal proof

3. **Common proof errors**:
   - Confusing "best known" with "optimal"
   - Informal reasoning about "must consider all cases"
   - Lack of rigorous lower bound proofs

4. **Barriers to progress**:
   - Why lower bounds are so difficult
   - What makes P vs NP hard

## References

### Primary Sources
- Feinstein, C. A. (2011). "The Computational Complexity of the Traveling Salesman Problem." arXiv:cs/0611082
- Critique: "Critique of Feinstein's Proof that P is not Equal to NP." arXiv:0706.2035

### Background on TSP
- Held, M., & Karp, R. M. (1962). "A Dynamic Programming Approach to Sequencing Problems." Journal of SIAM
- Bellman, R. (1962). "Dynamic Programming Treatment of the Travelling Salesman Problem"

### P vs NP Barriers
- Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP Question." SIAM J. Comput.
- Razborov, A. A., & Rudich, S. (1997). "Natural Proofs." J. Comput. System Sci.
- Aaronson, S., & Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory." STOC

### Complexity Theory
- Arora, S., & Barak, B. (2009). Computational Complexity: A Modern Approach
- Papadimitriou, C. H., & Steiglitz, K. (1998). Combinatorial Optimization: Algorithms and Complexity

## File Structure

```
proofs/attempts/alan-feinstein-2011-pneqnp/
├── README.md (this file)
├── rocq/
│   └── FeinsteinsProof.v
├── lean/
│   └── FeinsteinsProof.lean
└── isabelle/
    └── FeinsteinsProof.thy
```

## Status

- ✅ Paper analyzed and error identified
- 🚧 Rocq formalization: In progress
- 🚧 Lean formalization: In progress
- 🚧 Isabelle formalization: In progress

## License

This formalization is provided for educational purposes. See repository [LICENSE](../../../LICENSE).

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../../attempts/)
