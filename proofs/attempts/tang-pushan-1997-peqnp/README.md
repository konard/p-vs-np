# Tang Pushan (1997) - P=NP Attempt

**Attempt ID**: 3
**Author**: Tang Pushan (唐普山)
**Co-authors**: Huang Zhijun (黄志军)
**Year**: 1997-1998
**Claim**: P=NP
**Status**: **Refuted**

## Summary

Around 1997, Tang Pushan claimed to have solved the P versus NP problem by providing a polynomial-time algorithm for the CLIQUE problem, one of Karp's 21 original NP-complete problems. Since CLIQUE is NP-complete, a polynomial-time algorithm for it would imply P=NP. The proposed algorithm was called HEWN (Hierarchical Edge-Weighted Network).

## Papers

1. **Tang Pushan** (1997). "An algorithm with polynomial time complexity for finding clique in a graph". *Proceedings of 5th International Conference on CAD&CG*, Shenzhen, P.R. China, pp. 500-505.

2. **Tang Pushan and Huang Zhijun** (1998). "HEWN: A polynomial algorithm for CLIQUE problem". *Journal of Computer Science & Technology* 13(Supplement), pp. 33-44.

## The Main Argument

Tang Pushan proposed the HEWN (Hierarchical Edge-Weighted Network) algorithm as a polynomial-time solution to the maximum clique problem. The CLIQUE problem asks: given a graph G = (V, E) and an integer k, does G contain a clique of size k or larger?

The algorithm claimed to solve this NP-complete problem in polynomial time by using a hierarchical structure with edge weights to systematically find maximum cliques.

### Key Claims
- The HEWN algorithm could find maximum cliques in polynomial time
- This would prove P=NP, as CLIQUE is NP-complete
- The approach used hierarchical edge-weighted networks to organize the search

## Known Refutation

**Refuters**: Zhu Daming (朱大铭), Luan Junfeng (栾军峰), and M. A. Shaohan (马少瀚)
**Affiliation**: Shandong University, China
**Year**: 2001
**Paper**: "Hardness and methods to solve CLIQUE". *Journal of Computer Science and Technology* 16, pp. 388-391.

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

3. **Confusion of Cases**: The algorithm may perform well on certain structured graphs where cliques are small or easy to find, but this does not extend to the worst-case complexity for all graphs.

4. **NP-Completeness Ignored**: The claim ignores the fundamental nature of NP-completeness. If the HEWN algorithm truly ran in polynomial time for all instances, it would not only solve CLIQUE but also all other NP-complete problems via polynomial-time reductions.

### Formal Error

**Claimed**: T(n) = O(n^c) for some constant c (polynomial time)
**Actual**: T(n,j) = O(C_j · 2^(j-n)) where j can be Θ(n) (exponential time in worst case)

The error is a **complexity analysis mistake** - confusing average-case or restricted-case performance with worst-case polynomial-time complexity.

## Formalization Goal

The formalizations in this directory aim to:

1. **Define the CLIQUE problem formally** in Coq, Lean, and Isabelle
2. **Model the claims** of the HEWN algorithm
3. **Prove the impossibility** of the claimed polynomial-time complexity (assuming P≠NP)
4. **Demonstrate the actual exponential complexity** of the approach
5. **Show where the complexity analysis fails**

## Category of Error

This attempt falls into the category of **"Complexity Analysis Errors"**:
- Miscounting operations
- Ignoring exponential factors
- Confusing worst-case with average-case complexity
- Overgeneralizing from special cases

## Historical Context

This is entry #3 on Woeginger's list of P vs NP attempts. It represents a common type of error in complexity theory: proposing an algorithm that works well in practice or on certain instances, but incorrectly claiming polynomial worst-case time complexity.

## References

- Woeginger, G. J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- Zhu Daming, Luan Junfeng, and M. A. Shaohan (2001). "Hardness and methods to solve CLIQUE". *Journal of Computer Science and Technology* 16, pp. 388-391. DOI: 10.1007/BF02948987
- Karp, R. M. (1972). "Reducibility among combinatorial problems". In R. E. Miller and J. W. Thatcher (editors). *Complexity of Computer Computations*, pp. 85-103.

## See Also

- [P vs NP Problem Description](../../../P_VS_NP_TASK_DESCRIPTION.md)
- [Basic Proofs in Coq](../../basic/coq/Basic.v)
- [Basic Proofs in Lean](../../basic/lean/Basic.lean)
- [Basic Proofs in Isabelle](../../basic/isabelle/Basic.thy)

---

**Note**: This formalization is part of an educational effort to understand common errors in P vs NP attempts and to practice formal verification of complexity-theoretic claims.
