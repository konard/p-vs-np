# Tang Pushan (1997) - P=NP Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 3 (from Woeginger's list)
- **Author**: Tang Pushan (with Huang Zhijun on second paper)
- **Year**: 1997-1998
- **Claim**: P=NP
- **Approach**: Polynomial-time algorithm for CLIQUE problem
- **Status**: Refuted

## Summary

Around 1997, Tang Pushan claimed to have discovered a polynomial-time algorithm for the CLIQUE problem, which would imply P=NP since CLIQUE is NP-complete. The claim was published in two papers:

1. **Tang Pushan** (1997). "An algorithm with polynomial time complexity for finding clique in a graph." *Proceedings of 5th International Conference on CAD&CG*, Shenzhen, P.R. China, pp. 500-505.

2. **Tang Pushan and Huang Zhijun** (1998). "HEWN: A polynomial algorithm for CLIQUE problem." *Journal of Computer Science & Technology* 13(Supplement), pp. 33-44.

The proposed algorithm was called HEWN (Hierarchical Edge-Weighted Network).

## The Main Argument

Tang Pushan claimed that the HEWN algorithm could solve the CLIQUE problem in polynomial time. Since CLIQUE is known to be NP-complete (proven by Richard Karp in 1972), a polynomial-time algorithm for CLIQUE would immediately imply P=NP through the following reasoning:

1. CLIQUE is NP-complete
2. If CLIQUE ∈ P, then by NP-completeness, all problems in NP reduce to CLIQUE in polynomial time
3. Therefore, if CLIQUE can be solved in polynomial time, all NP problems can be solved in polynomial time
4. Thus, P=NP

## Known Refutation

The claim was refuted by **Zhu Daming, Luan Junfeng, and M. A. Shaohan** in their paper:

**Zhu, D., Luan, J., & Ma, S.** (2001). "Hardness and methods to solve CLIQUE." *Journal of Computer Science & Technology* 16(6), pp. 554-559. DOI: [10.1007/BF02948987](https://doi.org/10.1007/BF02948987)

## The Error in the Proof

Based on the refutation paper by Zhu et al. (2001), the fundamental error in Tang Pushan's work is:

**The HEWN algorithm is a heuristic method, not a true polynomial-time algorithm.**

Specifically:
- The algorithm may provide useful results in practice for some instances
- However, it does not guarantee polynomial-time worst-case performance for all instances of the CLIQUE problem
- The analysis claiming polynomial time complexity was incorrect
- The algorithm lacks a rigorous proof that it solves all instances of CLIQUE in polynomial time

This is a common type of error in claimed P=NP proofs: confusing heuristic algorithms (which work well in practice on many instances) with worst-case polynomial-time algorithms (which must work correctly on ALL instances within polynomial time).

## Formalization Strategy

Our formalization demonstrates the error by:

1. **Defining the CLIQUE problem formally** as a decision problem
2. **Establishing that CLIQUE is NP-complete** (from standard complexity theory)
3. **Modeling what a polynomial-time algorithm must satisfy**:
   - Must terminate in polynomial time for ALL inputs
   - Must produce correct answers for ALL inputs
4. **Showing the gap**: A heuristic that works on some instances is insufficient
5. **Demonstrating that without a verified proof of polynomial-time worst-case behavior**, the claim P=NP cannot be established

## Formal Proofs

This attempt is formalized in three proof assistants:

- **[Coq](coq/TangPushan1997.v)**: Formalization using Coq's computational logic
- **[Lean](lean/TangPushan1997.lean)**: Formalization using Lean 4's dependent type theory
- **[Isabelle/HOL](isabelle/TangPushan1997.thy)**: Formalization using Isabelle's higher-order logic

Each formalization:
1. Defines the CLIQUE problem formally
2. States the requirements for a polynomial-time algorithm
3. Explains why heuristic approaches are insufficient
4. Demonstrates the logical gap in claiming P=NP from an unverified heuristic

## Key Lessons

1. **Heuristics ≠ Algorithms**: A method that works well in practice is not the same as a provably correct polynomial-time algorithm
2. **Worst-case vs Average-case**: Complexity theory is concerned with worst-case behavior, not average or typical performance
3. **Rigor Required**: Claims of P=NP require rigorous mathematical proofs of polynomial-time bounds for all instances
4. **NP-completeness as a double-edged sword**: While showing a problem is NP-complete immediately implies P=NP if you solve it in polynomial time, this also means the problem is expected to be very hard

## Related Work

- **Karp, R.** (1972). "Reducibility among combinatorial problems." Shows CLIQUE is NP-complete
- **Garey, M. R., & Johnson, D. S.** (1979). *Computers and Intractability: A Guide to the Theory of NP-Completeness*. Comprehensive reference on NP-completeness

## Source

- Entry #3 from Woeginger's list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Part of Issue #44: Test all P vs NP attempts formally

## License

This formalization is provided for research and educational purposes. See repository [LICENSE](../../../LICENSE) file.

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P_VS_NP_TASK_DESCRIPTION.md](../../../P_VS_NP_TASK_DESCRIPTION.md) | [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md)
