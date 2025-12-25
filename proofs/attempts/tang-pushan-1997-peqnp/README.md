# Tang Pushan (1997) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 3 (from Woeginger's list)
- **Author**: Tang Pushan (唐普山)
- **Co-authors**: Huang Zhijun (黄志军)
- **Year**: 1997-1998
- **Claim**: P=NP
- **Approach**: Polynomial-time algorithm for CLIQUE problem
- **Status**: Refuted

## Summary

Around 1997, Tang Pushan claimed to have solved the P versus NP problem by providing a polynomial-time algorithm for the CLIQUE problem, one of Karp's 21 original NP-complete problems. Since CLIQUE is NP-complete, a polynomial-time algorithm for it would imply P=NP. The proposed algorithm was called HEWN (Hierarchical Edge-Weighted Network).

## Papers

1. **Tang Pushan** (1997). "An algorithm with polynomial time complexity for finding clique in a graph". *Proceedings of 5th International Conference on CAD&CG*, Shenzhen, P.R. China, pp. 500-505.

2. **Tang Pushan and Huang Zhijun** (1998). "HEWN: A polynomial algorithm for CLIQUE problem". *Journal of Computer Science & Technology* 13(Supplement), pp. 33-44.

## The Main Argument

Tang Pushan claimed that the HEWN algorithm could solve the CLIQUE problem in polynomial time. The CLIQUE problem asks: given a graph G = (V, E) and an integer k, does G contain a clique of size k or larger?

Since CLIQUE is known to be NP-complete (proven by Richard Karp in 1972), a polynomial-time algorithm for CLIQUE would immediately imply P=NP through the following reasoning:

1. CLIQUE is NP-complete
2. If CLIQUE ∈ P, then by NP-completeness, all problems in NP reduce to CLIQUE in polynomial time
3. Therefore, if CLIQUE can be solved in polynomial time, all NP problems can be solved in polynomial time
4. Thus, P=NP

### Key Claims
- The HEWN algorithm could find maximum cliques in polynomial time
- This would prove P=NP, as CLIQUE is NP-complete
- The approach used hierarchical edge-weighted networks to organize the search

## Known Refutation

**Refuters**: Zhu Daming (朱大铭), Luan Junfeng (栾军峰), and M. A. Shaohan (马少瀚)
**Affiliation**: Shandong University, China
**Year**: 2001
**Paper**: "Hardness and methods to solve CLIQUE". *Journal of Computer Science and Technology* 16, pp. 388-391. DOI: [10.1007/BF02948987](https://doi.org/10.1007/BF02948987)

### The Refutation

The refutation paper by Zhu, Luan, and Shaohan demonstrated that:

1. **Time Complexity Analysis Error**: The actual time complexity of the HEWN algorithm is **O(C_j · 2^(j-n))**, where:
   - n = number of vertices in the graph
   - j = size of the maximum clique
   - C_j = a combinatorial factor

2. **Exponential, Not Polynomial**: This complexity is exponential in j (when j grows with n), not polynomial. The algorithm only provides polynomial-time performance when j is fixed and small relative to n.

3. **Heuristic, Not Algorithm**: The HEWN approach is better characterized as a heuristic or practical method for finding cliques in certain graphs, but it does **not** provide a polynomial-time guarantee for all instances.

## The Error in the Proof

The fundamental error in Tang Pushan's approach lies in the **time complexity analysis**:

### What Went Wrong

1. **Incomplete Analysis**: The original papers either miscounted the number of operations or failed to account for the exponential growth in certain problem instances.

2. **Hidden Exponential Factor**: The algorithm contains a factor that grows exponentially with the clique size. When the clique size j is Θ(n) (which can occur in graphs), the algorithm requires exponential time.

3. **Confusion of Cases**: The algorithm may perform well on certain structured graphs where cliques are small or easy to find, but this does not extend to the worst-case complexity for all graphs. This is a common type of error: confusing heuristic algorithms (which work well in practice on many instances) with worst-case polynomial-time algorithms (which must work correctly on ALL instances within polynomial time).

4. **NP-Completeness Ignored**: The claim ignores the fundamental nature of NP-completeness. If the HEWN algorithm truly ran in polynomial time for all instances, it would not only solve CLIQUE but also all other NP-complete problems via polynomial-time reductions.

### Formal Error

**Claimed**: T(n) = O(n^c) for some constant c (polynomial time)
**Actual**: T(n,j) = O(C_j · 2^(j-n)) where j can be Θ(n) (exponential time in worst case)

The error is a **complexity analysis mistake** - confusing fixed-parameter polynomial complexity with worst-case polynomial-time complexity. Specifically:
- When `j` is **constant** (fixed): `T(n) = O(n)` — **Polynomial** ✓
- When `j = Θ(n)` (worst case): `T(n) = O(n · 2^n)` — **Exponential** ✗

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the CLIQUE problem formally** as a decision problem in Coq, Lean, and Isabelle
2. **Establishing that CLIQUE is NP-complete** (from standard complexity theory)
3. **Modeling what a polynomial-time algorithm must satisfy**:
   - Must terminate in polynomial time for ALL inputs
   - Must produce correct answers for ALL inputs
4. **Proving the actual complexity** of the HEWN approach:
   - Polynomial when j is constant
   - Exponential when j = Θ(n)
5. **Demonstrating the gap**: Showing where the complexity analysis fails and why the claim is refuted

## Formal Proofs

This attempt is formalized in three proof assistants:

- **[Coq](coq/TangPushan.v)**: Formalization using Coq's computational logic
- **[Lean](lean/TangPushan.lean)**: Formalization using Lean 4's dependent type theory
- **[Isabelle/HOL](isabelle/TangPushan.thy)**: Formalization using Isabelle's higher-order logic

Each formalization:
1. Defines the CLIQUE problem formally
2. States the requirements for a polynomial-time algorithm
3. Proves polynomial behavior for fixed j
4. Proves exponential behavior when j = n
5. Demonstrates the contradiction in Tang's claim

## Category of Error

This attempt falls into the category of **"Complexity Analysis Errors"**:
- Miscounting operations
- Ignoring exponential factors
- Confusing worst-case with average-case or fixed-parameter complexity
- Overgeneralizing from special cases

## Key Lessons

1. **Heuristics ≠ Algorithms**: A method that works well in practice is not the same as a provably correct polynomial-time algorithm
2. **Worst-case vs Average-case**: Complexity theory is concerned with worst-case behavior, not average or typical performance
3. **Fixed-parameter ≠ Worst-case**: An algorithm that is polynomial for fixed parameter values is NOT the same as an algorithm that is polynomial in the worst case for all inputs
4. **Rigor Required**: Claims of P=NP require rigorous mathematical proofs of polynomial-time bounds for all instances
5. **NP-completeness as a double-edged sword**: While showing a problem is NP-complete immediately implies P=NP if you solve it in polynomial time, this also means the problem is expected to be very hard

## Historical Context

This is entry #3 on Woeginger's list of P vs NP attempts. It represents a common type of error in complexity theory: proposing an algorithm that works well in practice or on certain instances, but incorrectly claiming polynomial worst-case time complexity.

## Related Work

- **Karp, R. M.** (1972). "Reducibility among combinatorial problems". In R. E. Miller and J. W. Thatcher (editors). *Complexity of Computer Computations*, pp. 85-103. Shows CLIQUE is NP-complete
- **Garey, M. R., & Johnson, D. S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*. Comprehensive reference on NP-completeness
- **Woeginger, G. J.** "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## See Also

- [P vs NP Problem Description](../../../P_VS_NP_TASK_DESCRIPTION.md)
- [ERROR_ANALYSIS.md](ERROR_ANALYSIS.md) - Detailed complexity analysis and common patterns
- [Basic Proofs in Coq](../../basic/coq/Basic.v)
- [Basic Proofs in Lean](../../basic/lean/Basic.lean)
- [Basic Proofs in Isabelle](../../basic/isabelle/Basic.thy)

## Source

- Entry #3 from Woeginger's list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Part of Issue #44: Test all P vs NP attempts formally

## License

This formalization is provided for research and educational purposes. See repository [LICENSE](../../../LICENSE) file.

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../../P_VS_NP_TASK_DESCRIPTION.md) | [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md)

**Note**: This formalization is part of an educational effort to understand common errors in P vs NP attempts and to practice formal verification of complexity-theoretic claims.
