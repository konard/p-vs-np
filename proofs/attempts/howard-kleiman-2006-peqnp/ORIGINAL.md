# Original Paper: The Asymmetric Traveling Salesman Problem

**Author:** Howard Kleiman
**Year:** 2006 (submitted December 5, 2006; revised December 9, 2006)
**arXiv ID:** [math.CO/0612114](https://arxiv.org/abs/math.CO/0612114)
**Subject Classification:** General Mathematics (math.GM); MSC: 05-XX
**Woeginger's List:** Entry #37

---

## Abstract

The paper proposes a polynomial-time algorithm for solving the Asymmetric Traveling Salesman Problem (ATSP) by building on work by Jonker and Volgenannt. The approach transforms an n×n asymmetric cost matrix into a 2n×2n symmetric matrix with special properties, then applies a modified Floyd-Warshall algorithm to find an optimal tour.

The author acknowledges: "If the proof of theorem 1 in section II is correct, since the asymmetric traveling salesman problem is NP-hard, P would equal NP."

---

## Paper Summary

### I. Introduction

Starting with M(a), an n×n asymmetric cost matrix, Jonker and Volgenannt [1] transformed it into a 2n × 2n symmetric cost matrix, M(s), where M(s) has unusual properties. One such property is that an optimal tour in M(s) yields an optimal tour in M(a).

Modifying M(s), the paper applies the modified Floyd-Warshall algorithm given in [2] to M(s). Let T be a tour that is an upper bound for an optimal tour in M(a). Due to the structure of M(s), the claim is that we either can always obtain an optimal tour in M(s) that is derived from only one minimal positively-valued cycle in σ_T^(-1)M whose value is less than |T| (i.e., we don't have to link circuits), or else T = T_OPT. Thus, the paper claims we can obtain an optimal tour in M(a) in at most polynomial running time.

**Critical Statement:** "If the proof of theorem 1 in section II is correct, since the asymmetric traveling salesman problem is NP-hard, P would equal NP."

### II. A Theorem

**Theorem 1.**

Let M(a) be an n×n asymmetric cost matrix where a_ii = ∞, i = 1,2,...,n. Using a modified version of the symmetric cost matrix, M(s), obtained by Jonker and Volgenannt [1] as well as a result of Kleiman in [2] and the use of the modified F-W algorithm, we prove that we always can obtain an optimal solution to M(a) in polynomial time.

**Proof Outline:**

1. **Normalization:** If M(a) contains a non-positive entry, let m be the smallest value of all the entries in M(a). Add -m+1 to each entry of M(a) so that each entry now has a positive value.

2. **Matrix Construction:**
   - Let M_∞ be an n×n matrix each of whose entries is ∞
   - Change each diagonal entry of M(a) into 0 to obtain the matrix M(a)_d
   - Define M(a)_d^T as the transpose of M(a)_d
   - Define the 2n × 2n symmetric matrix as:
     ```
     M(s) = [ M_∞        M(a)_d   ]
            [ M(a)_d^T   M_∞      ]
     ```

3. **Upper Bound Tour:** Use any algorithm that yields an upper bound, say T_UPPERBOUND = (t_1, t_2, ..., t_n), for an optimal tour in M(a).

4. **Tour Transformation:** Replace T_UPPERBOUND by T = (t_1, t_{2+n}, t_2, t_{3+n}, t_3, ..., t_n, t_{1+n}) in M(s). By construction, |(t_{i+n}, t_i)| = 0, i = 1,2,...,n in M(s).

5. **Cycle Decomposition:** It follows that the product of (t_{i+n}, t_i) equals σ_T where each 2-cycle (t_{i+n}, t_i) has a value of 0. We can always use a product of 2-cycles (edges) to obtain M(s)^(-1) - σ_T.

6. **Acceptable Paths:** An acceptable path in M(s) consists alternately of non-zero and zero arcs. We cannot link acceptable cycles of the kind found in M(s) since by linking by deleting two arcs of form (t_{i+n}, t_i) or (t_i, t_{i+n}), we obtain a circuit containing two consecutive non-zero-valued directed edges.

7. **Modified Floyd-Warshall Application:** Using the modified F-W algorithm, each cycle from a to b obtained in M(s) has a value no greater than any other cycle from a to b. Thus, using the modified F-W algorithm, there is only one way that we could obtain T_FWOPT of M(s): one minimal positively-valued acceptable cycle containing n arcs whose value is less than |T| or – if one can't be found, T_UPPERBOUND = T_FWOPT = T_OPT.

8. **Complexity Claim:** The modified F-W algorithm when used for obtaining acceptable paths always obtains all acceptable paths in at most O(n⁴) running time. Since each such cycle is obtained using the modified F-W algorithm – together with an algorithm to ensure that an acceptable path obtained stays acceptable which requires backtracking in only a smaller number of cases than otherwise – we can obtain such a minimal positively-valued acceptable cycle containing n points of value less than |T| (if it exists) in polynomial time.

   **Reasoning:** The Floyd-Warshall algorithm has O(n³) running time. Thus, even backtracking in every case, would raise the running time to at most O(n⁴).

### III. The Construction of σ_T^(-1)(M(s))

In the original M(a), a_ii = ∞, i = 1,2,...,n.

- In J-V M(a), a_ii = -M' where M' is the largest value of a nondiagonal entry in M(a)
- In M(a)_d, a_ii = 0
- M(a)_d is used in the construction of M(s)

In order that an optimal tour of M(s) yields an optimal tour of M(a), all arcs used in acceptable paths must belong to either M(a)_d or M(a)_d^T.

By applying σ_T^(-1) to the columns of M(s), we obtain a matrix whose diagonal elements all have the value zero, while all other entries have a positive value. This is because σ_T^(-1)(M(s)) = σ_T^(-1)(M(s))^(-).

It follows that all acceptable paths contain only positive values, implying that all acceptable cycles have positive values.

---

## Key Mathematical Objects

### Asymmetric Cost Matrix
```
M(a) = [ a_11  ...  a_1n ]
       [  ⋮    ⋱    ⋮   ]
       [ a_n1  ...  a_nn ]
```
where a_ii = ∞ for i = 1,2,...,n

### Symmetric Matrix Construction
```
M(s) = [ M_∞        M(a)_d   ]  (2n × 2n)
       [ M(a)_d^T   M_∞      ]
```

### Tour Transformation
- Original tour in M(a): T_UPPERBOUND = (t_1, t_2, ..., t_n)
- Transformed tour in M(s): T = (t_1, t_{2+n}, t_2, t_{3+n}, t_3, ..., t_n, t_{1+n})
- Each 2-cycle (t_{i+n}, t_i) has value 0

### Acceptable Paths
An acceptable path in M(s) alternates between:
- Non-zero arcs (from M(a)_d or M(a)_d^T)
- Zero arcs (the 2-cycles connecting corresponding vertices)

---

## Claimed Algorithm

1. **Input:** n×n asymmetric cost matrix M(a)
2. **Normalize:** Add constant to make all entries positive
3. **Transform:** Construct 2n×2n symmetric matrix M(s)
4. **Upper Bound:** Find any tour T_UPPERBOUND in M(a)
5. **Transform Tour:** Convert to corresponding tour T in M(s)
6. **Apply Floyd-Warshall:** Use modified F-W algorithm on M(s)
7. **Extract Optimal:** Find minimal acceptable cycle or confirm T is optimal
8. **Output:** Optimal tour in M(a)

**Claimed Complexity:** O(n⁴) - polynomial time

---

## Claimed Implications

Since the Asymmetric Traveling Salesman Problem (ATSP) is NP-hard:
- If this algorithm correctly solves ATSP in polynomial time O(n⁴)
- Then all NP problems can be solved in polynomial time
- Therefore P = NP

---

## Author's Caveat

The paper explicitly states: "If the proof of theorem 1 in section II is correct, since the asymmetric traveling salesman problem is NP-hard, P would equal NP."

This conditional phrasing suggests the author was aware of potential issues with the proof.

---

## References

[1] Jonker, R. and Volgenannt, T., "Transforming asymmetric into symmetric traveling salesman problems," Operations Research Letters, 2, 161-163 (1983).

[2] Kleiman, H., "The symmetric traveling salesman problem," arXiv.org, math.CO/0509531.

---

## Related Papers by Kleiman

The author has made several attempts at solving TSP variants:
- 2001: "The Floyd-Warshall Algorithm, the AP and the TSP" (arXiv:math/0111309)
- 2005: "The Symmetric Traveling Salesman Problem" (arXiv:math/0508212)
- 2006: "The Asymmetric Traveling Salesman Problem" (this paper, arXiv:math.CO/0612114)
- 2011: "The General Traveling Salesman Problem" (arXiv:1110.4052)

---

## Note on Paper Status

The arXiv page indicates corrections were made post-submission, including errors in the original proof of Theorem 1 regarding cycle valuations and backtracking complexity estimates of O(n⁴).

This formalization attempts to capture the claimed approach and identify where the reasoning fails to establish P = NP.
