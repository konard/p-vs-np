# Hanlin Liu (2014) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../) | [Issue #47](https://github.com/konard/p-vs-np/issues/47)

---

## Metadata

- **Attempt ID**: 101 (Woeginger's list)
- **Author**: Hanlin Liu (刘汉林)
- **Year**: January 2014
- **Claim**: P = NP
- **Method**: Polynomial-time algorithm for Hamiltonian Circuit Problem
- **Claimed Complexity**: O(|V|^9)
- **Status**: ❌ **WITHDRAWN by author** (October 31, 2018)
- **Woeginger Entry**: #101 (https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## Paper Reference

- **Title**: "A Algorithm for the Hamilton Circuit Problem"
- **arXiv**: [1401.6423](http://arxiv.org/abs/1401.6423)
- **Submission History**: 8 versions (v1-v8) from January 2014 to October 2018
- **Final Status**: Withdrawn by author on October 31, 2018
- **PDF Availability**: ❌ Not available (withdrawn)

## Summary

Hanlin Liu attempted to establish P=NP by constructing a polynomial-time algorithm for the Hamiltonian Circuit Problem in a graph G=(V,E). The Hamiltonian Circuit Problem is known to be NP-complete (proven by Karp in 1972), so a polynomial-time solution would indeed imply P=NP.

The claimed time complexity was O(|V|^9), where |V| is the number of vertices in the graph. If correct, this would represent a breakthrough result solving one of the most important open problems in mathematics and computer science.

## Main Argument/Approach

Due to the paper being withdrawn and the PDF no longer being available, the specific algorithmic details cannot be analyzed. However, the general approach was to:

1. Design an algorithm for finding Hamiltonian circuits in arbitrary graphs
2. Prove the algorithm runs in polynomial time (specifically O(|V|^9))
3. Conclude that since Hamiltonian Circuit is NP-complete, this implies P=NP

## Known Refutation

### Author's Own Assessment

The most direct refutation comes from **the author himself**. In the final version (v8) before withdrawal, Liu Hanlin explicitly stated:

> "In this article, we try to find a algorithm for the hamilton circuit problem. Unfortunately, it can not cover all cases of hamilton circuit problem. So, it is a failed attempt"

### The Error in the Proof

Based on the author's admission, the fundamental error is:

**Incomplete Case Coverage**: The proposed algorithm does not correctly handle all possible graph structures. A valid polynomial-time algorithm for an NP-complete problem must:
- Correctly solve ALL instances of the problem
- Return correct answers for every possible input
- Run in polynomial time for all cases

The author acknowledged that the algorithm "can not cover all cases," meaning:
- Some graph structures were not properly handled
- The algorithm may fail, give incorrect results, or run in super-polynomial time on certain inputs
- The proof of P=NP was therefore incomplete and invalid

### Historical Context

This is a common pattern in failed P vs NP attempts:
1. An algorithm is proposed for an NP-complete problem
2. The algorithm works correctly on many (even most) test cases
3. However, edge cases or specific graph structures reveal the algorithm's limitations
4. The algorithm either:
   - Gives incorrect results on some inputs
   - Requires exponential time on certain instances
   - Contains logical gaps in its correctness proof

### Why This Matters

For a proof of P=NP to be valid, the algorithm must:
- ✅ Be polynomial-time for **all** instances (not just "most" or "many")
- ✅ Be correct for **all** instances (100% accuracy, not probabilistic)
- ✅ Have a rigorous mathematical proof of both correctness and time complexity
- ✅ Address known barriers (relativization, natural proofs, algebrization)

Liu's attempt failed the first two requirements by not covering all cases.

## Formalization Strategy

Since the original paper is withdrawn and unavailable, our formalization focuses on the **general structure** of such attempts and why they fail. We formalize:

### 1. Hamiltonian Circuit Problem Definition
- Formal definition of graphs, paths, and circuits
- Specification of when a circuit is Hamiltonian
- Encoding as a decision problem

### 2. The Claim Structure
```
Claim: ∃ Algorithm A such that:
  1. A solves Hamiltonian Circuit Problem
  2. A runs in time O(|V|^9) for all inputs
  3. A is correct for all inputs
```

### 3. The Gap/Error
```
Reality: The proposed algorithm A fails because:
  ∃ Graph G such that:
    A(G) is incorrect OR
    A(G) runs in super-polynomial time OR
    A(G) does not terminate
```

### 4. Lesson for Future Attempts
We formalize the requirement that any valid P=NP proof via an algorithmic approach must prove correctness and polynomial-time complexity **for all possible inputs**, not just for a subset.

## Implementations

### Coq (`coq/HanlinLiu2014.v`)
- Defines graph structures and Hamiltonian circuits
- Formalizes the claim of polynomial-time solvability
- Proves that incomplete case coverage invalidates the proof
- Uses classical logic and standard library

### Lean 4 (`lean/HanlinLiu2014.lean`)
- Type-safe encoding of graphs and decision problems
- Dependent types for correctness proofs
- Demonstrates why partial algorithms don't prove P=NP
- Integration with repository's Lean infrastructure

### Isabelle/HOL (`isabelle/HanlinLiu2014.thy`)
- Higher-order logic formalization
- Record types for algorithms and their properties
- Proof that universal correctness is required
- Compatible with repository's Isabelle/HOL setup

## Educational Value

This formalization serves several purposes:

1. **Demonstrates common failure modes**: Many P vs NP attempts fail by not covering all cases
2. **Importance of rigorous proof**: Informal testing on examples is insufficient
3. **Respect for author transparency**: Liu's honest acknowledgment of failure is scientifically valuable
4. **Template for analyzing attempts**: This structure can be reused for other failed attempts

## Timeline

- **January 2014**: Initial submission (v1) to arXiv
- **2014-2018**: Multiple revisions (v2-v7)
- **October 31, 2018**: Final version (v8) submitted with withdrawal notice
- **October 31, 2018**: Paper officially withdrawn by author

## Related Work

### NP-Completeness of Hamiltonian Circuit
- **Karp (1972)**: "Reducibility Among Combinatorial Problems" - proved Hamiltonian Circuit is NP-complete
- **Garey & Johnson (1979)**: *Computers and Intractability* - comprehensive treatment

### Known Algorithms
- **Exact algorithms**:
  - Held-Karp algorithm: O(n^2 * 2^n) via dynamic programming
  - Best known: O(1.657^n) (Björklund, 2014)
- **Heuristic algorithms**: Various approximations and metaheuristics (no worst-case guarantees)
- **Special cases**: Polynomial-time algorithms exist for specific graph classes (planar graphs with restrictions, etc.)

## Verification

To verify the formalizations:

```bash
# Coq
cd coq
coqc HanlinLiu2014.v

# Lean 4
cd lean
lake build

# Isabelle/HOL
cd isabelle
isabelle build -D .
```

## References

### Primary Source
- Liu, H. (2014). "A Algorithm for the Hamilton Circuit Problem." arXiv:1401.6423 [Withdrawn]

### Hamiltonian Circuit Problem
- Karp, R. M. (1972). "Reducibility Among Combinatorial Problems." *Complexity of Computer Computations*, pp. 85-103.
- Garey, M. R., & Johnson, D. S. (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*. W. H. Freeman.

### Woeginger's List
- Woeginger, G. J. "The P versus NP Page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### General P vs NP
- Cook, S. A. (2000). "The P versus NP Problem." Clay Mathematics Institute. https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf
- Arora, S., & Barak, B. (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.

## Acknowledgments

We acknowledge Hanlin Liu's scientific integrity in transparently withdrawing the paper and acknowledging its limitations. This honesty is valuable for the research community and serves as an educational example.

## License

See repository [LICENSE](../../../LICENSE) file.

## Status

- ✅ Documentation: Complete
- ✅ Coq formalization: Complete
- ✅ Lean formalization: Complete
- ✅ Isabelle formalization: Complete
- ✅ Error identification: Complete (author's own admission)

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Documentation](../../../P_VS_NP_TASK_DESCRIPTION.md) | [All Attempts](../)
