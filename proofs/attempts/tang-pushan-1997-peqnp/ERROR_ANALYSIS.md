# Error Analysis: Tang Pushan's HEWN Algorithm

## Overview

This document provides a detailed analysis of the error in Tang Pushan's claimed polynomial-time algorithm for the CLIQUE problem.

## The Claim

**Tang Pushan (1997-1998)** claimed to have developed a polynomial-time algorithm called HEWN (Hierarchical Edge-Weighted Network) that solves the maximum clique problem.

### Why This Would Matter
- The CLIQUE problem is NP-complete (proven by Karp in 1972)
- A polynomial-time algorithm for any NP-complete problem implies P=NP
- This would be one of the most important discoveries in computer science
- Worth $1 million (Clay Mathematics Institute Millennium Prize)

## The Error

### Type of Error
**Complexity Analysis Mistake** - Specifically, confusion between fixed-parameter complexity and worst-case complexity.

### What Went Wrong

#### 1. Actual Time Complexity

The HEWN algorithm, when properly analyzed, has time complexity:

```
T(n, j) = O(C_j · 2^(j-n))
```

Where:
- **n** = number of vertices in the graph
- **j** = size of the maximum clique
- **C_j** = combinatorial factor (approximately a binomial coefficient)

#### 2. Two Different Scenarios

**Scenario A: Small Fixed j (j is constant)**
- If j ≤ k for some constant k, then 2^j is also constant
- T(n, k) = O(n · 2^k) = O(n) since 2^k is constant
- **Result**: Polynomial time! ✓

**Scenario B: Large j (j grows with n)**
- In worst case, j can be Θ(n) (e.g., complete graph has clique of size n)
- T(n, n) = O(n · 2^n)
- **Result**: Exponential time! ✗

#### 3. The Confusion

Tang Pushan appears to have:
1. Observed that HEWN works well for graphs with small cliques
2. Analyzed the complexity assuming j is bounded by a constant
3. Concluded the algorithm is polynomial-time
4. **Failed to consider worst-case behavior** when j can be large

### Mathematical Formalization

#### Claimed:
```
∀n, T(n) = O(n^c) for some constant c
```
(Polynomial time for all inputs)

#### Actual:
```
T(n, j) = O(n · 2^j)

When j = O(1): T(n) = O(n)           [Polynomial]
When j = Θ(n): T(n) = O(n · 2^n)     [Exponential]
```

### Why This Is Wrong for NP-Completeness

For an algorithm to prove P=NP, it must run in polynomial time **in the worst case** for **all** instances:

1. **NP-complete problems can have large solutions**
   - Some graphs have cliques of size Θ(n)
   - The algorithm must handle these efficiently

2. **Worst-case analysis is required**
   - Average-case polynomial time ≠ P
   - Best-case polynomial time ≠ P
   - Only worst-case polynomial time = P

3. **The exponential factor cannot be ignored**
   - Even if most instances run quickly
   - Even if the exponential only appears for "rare" inputs
   - The existence of exponential-time cases means not in P

## The Refutation

**Zhu Daming, Luan Junfeng, and M. A. Shaohan (2001)** published a refutation showing:

1. **Correct complexity analysis**: T(n,j) = O(C_j · 2^(j-n))
2. **Exponential worst-case**: When j = n, this is exponential
3. **Heuristic, not algorithm**: HEWN is better characterized as a heuristic that works well on certain instances, not a polynomial-time algorithm for all instances

### Key Quote from Refutation
> "The improved algorithm, HEWN (hierarchical edge-weighted network), only provides a heuristic or useful method, but cannot be called a polynomial algorithm."

## Common Pattern

This error represents a **common pattern** in failed P vs NP attempts:

### Category: "Fast in Practice" Algorithms

1. **Algorithm works well empirically**
   - Solves many real-world instances quickly
   - Appears polynomial on test cases
   - May even be optimal for certain input distributions

2. **Incomplete complexity analysis**
   - Analysis focuses on typical cases
   - Ignores or underestimates worst-case behavior
   - Hidden exponential factors in edge cases

3. **Overgeneralization**
   - Concludes polynomial time for all instances
   - Claims to solve NP-complete problem
   - Claims P=NP

### Why This Happens

1. **Practical vs. Theoretical**
   - Real-world instances often have special structure
   - NP-complete problems can be easy "on average"
   - Worst-case instances may be rare in practice

2. **Complexity analysis is hard**
   - Easy to miss hidden exponential factors
   - Parameter dependencies can be subtle
   - Recurrence relations can be tricky

3. **Optimism bias**
   - Researchers want the algorithm to work
   - May focus on positive results
   - May not thoroughly test worst cases

## Lessons Learned

### For Complexity Analysis

1. **Always consider worst case**
   - Identify the hardest possible input
   - Ensure analysis covers all scenarios
   - Don't assume parameters are small

2. **Watch for hidden parameters**
   - Complexity should be in terms of input size
   - Parameters like "clique size j" matter
   - If j can be Θ(n), it's not hidden

3. **Exponential factors matter**
   - 2^j is NOT constant unless j is constant
   - Binomial coefficients C(n,k) can be exponential
   - These factors cannot be ignored

### For NP-Completeness Claims

1. **P=NP is extremely unlikely**
   - 50+ years of failed attempts
   - Known barriers (relativization, natural proofs, algebrization)
   - Should approach any claim with healthy skepticism

2. **Check for common errors**
   - Complexity analysis mistakes (like this one)
   - Incorrect reduction proofs
   - Misunderstanding of NP-completeness
   - Ignoring known barriers

3. **Peer review is essential**
   - Have experts check the analysis
   - Test on worst-case instances
   - Formalize in proof assistants

## Formalization Results

This attempt has been formalized in three proof assistants:

1. **Rocq** ([TangPushan.v](rocq/TangPushan.v))
   - Formalizes CLIQUE problem
   - Proves HEWN polynomial for fixed j
   - Proves HEWN exponential when j=n
   - Demonstrates the refutation

2. **Lean 4** ([TangPushan.lean](lean/TangPushan.lean))
   - Similar formalization
   - Uses Lean's tactics for proofs
   - Shows complexity analysis error

3. **Isabelle/HOL** ([TangPushan.thy](isabelle/TangPushan.thy))
   - Complete formalization
   - Uses Isabelle's automation
   - Includes detailed error analysis

All three formalizations identify the same core error: **confusion between fixed-parameter polynomial time and worst-case polynomial time**.

## References

1. **Original Papers**:
   - Tang Pushan (1997). "An algorithm with polynomial time complexity for finding clique in a graph". *Proceedings of 5th International Conference on CAD&CG*, pp. 500-505.
   - Tang Pushan and Huang Zhijun (1998). "HEWN: A polynomial algorithm for CLIQUE problem". *Journal of Computer Science & Technology* 13(Supplement), pp. 33-44.

2. **Refutation**:
   - Zhu Daming, Luan Junfeng, and M. A. Shaohan (2001). "Hardness and methods to solve CLIQUE". *Journal of Computer Science and Technology* 16, pp. 388-391. DOI: 10.1007/BF02948987

3. **Background**:
   - Karp, R. M. (1972). "Reducibility among combinatorial problems". *Complexity of Computer Computations*, pp. 85-103.
   - Woeginger, G. J. "The P-versus-NP page". https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

## Conclusion

Tang Pushan's HEWN algorithm represents a **complexity analysis error**: claiming polynomial worst-case time complexity while the algorithm actually has exponential worst-case time complexity when the clique size parameter can grow with the input size.

**Key Insight**: An algorithm that is polynomial in n for **fixed** parameter j is NOT the same as an algorithm that is polynomial for **all** values of n and j.

This is a valuable educational example of a common pitfall in complexity analysis and NP-completeness research.
