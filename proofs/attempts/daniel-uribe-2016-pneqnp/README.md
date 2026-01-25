# Daniel Uribe (2016) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Frameworks](../../../README.md#-formal-verification)

---

## Metadata

- **Attempt ID**: 106 (Woeginger's list)
- **Author**: Daniel Uribe
- **Year**: 2016 (January)
- **Claim**: P ≠ NP
- **Status**: **Withdrawn** - Paper was withdrawn from arXiv
- **Source**: http://arxiv.org/abs/1601.03619
- **Reference**: [Woeginger's P vs NP Page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)

## Summary

In January 2016, Daniel Uribe published a paper claiming to prove that P is not equal to NP. The paper was titled "P vs. NP" and made available on arXiv. The approach attempted to analyze algorithmic runtime complexity using decision trees, with a focus on sorting algorithms and clique-finding algorithms in networks.

## Main Argument/Approach

The proof attempt used the following strategy:

### 1. Decision Tree Framework
The paper proposed analyzing algorithmic runtime complexity through the lens of decision trees, a common tool in lower bound analysis.

### 2. Sorting Algorithm Analysis
The method began by analyzing sorting algorithms using decision trees. This is a well-established technique - it's known that comparison-based sorting requires Ω(n log n) comparisons in the worst case, which can be proven using decision tree arguments.

### 3. Extension to Clique Finding
The approach then attempted to extend this decision tree methodology to optimal algorithms for finding cliques in networks. Specifically:
- Finding all cliques of size q in a network N
- Finding the first clique of size q in a network N

The clique problem is known to be NP-complete, making it a natural target for a P ≠ NP proof attempt.

### 4. Lower Bound Claim
The paper claimed to demonstrate that the lower bound of such decision trees is "not in P" - i.e., requires super-polynomial time.

## Known Issues and Errors

The paper was **withdrawn from arXiv** with the following known problems:

### 1. Lack of Peer Review
According to arXiv comments:
> "Work was not peer reviewed"

This indicates the work did not undergo rigorous academic scrutiny before publication.

### 2. Mathematical Errors
The arXiv comments note specific mathematical mistakes:
> "Contains mathematical errors (e.g. incorrectly stating the Legendre formula as an equality)"

The Legendre formula typically relates to number theory (counting prime factors) or special functions. Its incorrect application suggests fundamental mathematical errors in the approach.

### 3. Problem Description Issues
> "Does not describe problem"

This suggests the paper may not have properly formalized the computational problem being analyzed, which is critical for complexity theory proofs.

### 4. Decision Tree Limitation (Likely Error)

**The Fundamental Gap**: Decision tree lower bounds typically only apply to *specific computational models*, not to all possible algorithms. This is a common error in P vs NP proof attempts.

**Why This Matters**:
- Decision trees can model comparison-based algorithms (like sorting)
- However, not all polynomial-time algorithms can be modeled as decision trees
- A lower bound in the decision tree model does NOT imply a lower bound for all possible algorithms
- This is similar to the **relativization barrier**: proving something in a restricted model doesn't necessarily transfer to the general case

**Example**:
- Sorting requires Ω(n log n) comparisons in the decision tree model
- But this doesn't mean sorting is not in P - it IS in P with O(n log n) time!
- The lower bound is only for comparison-based algorithms

### 5. Model Mismatch

For the clique problem:
- A decision tree lower bound would only apply to algorithms using a specific type of queries/comparisons
- It would NOT apply to all possible polynomial-time algorithms
- Therefore, even if the lower bound calculation were correct, it would not prove P ≠ NP

## The Error in Formal Terms

The proof attempt likely makes this logical error:

```
INCORRECT REASONING:
1. Clique ∈ NP (correct)
2. Any decision tree for Clique requires super-polynomial queries (possibly correct for specific model)
3. Therefore, Clique ∉ P (INCORRECT - this doesn't follow!)
```

The gap is in step 3: proving a lower bound in a restricted computational model (decision trees) does not prove a lower bound for ALL polynomial-time algorithms. There might be polynomial-time algorithms that don't fit the decision tree model.

## Why This Approach Cannot Work

### Barrier: Relativization and Model Restrictions

1. **Model-Specific Lower Bounds**: Decision tree lower bounds are inherently relativizing arguments - they work in a restricted oracle model.

2. **Baker-Gill-Solovay (1975)**: The relativization barrier shows that techniques which work equally well in all oracle worlds cannot resolve P vs NP. Decision tree arguments are typically relativizing.

3. **Need for Non-Relativizing Techniques**: To prove P ≠ NP, we need techniques that exploit specific properties of computation that aren't preserved under relativization.

### What Would Be Needed

To make a decision tree approach work, one would need to:
1. Prove that ANY polynomial-time algorithm can be efficiently simulated by a decision tree (likely false)
2. OR find a non-relativizing way to extend decision tree lower bounds to general computation (unknown how to do this)
3. OR overcome the relativization barrier in some other way

## Formalization Goals

The formalizations in this directory aim to:

1. **Encode the Decision Tree Model**: Define decision trees and their complexity in Rocq, Lean, and Isabelle
2. **Formalize the Clique Problem**: Represent the clique-finding problem formally
3. **Model the Lower Bound Claim**: Express the claimed super-polynomial lower bound for decision trees
4. **Expose the Gap**: Show formally that a lower bound in the decision tree model does NOT imply the problem is not in P
5. **Demonstrate the Error**: Provide a formal counterexample or proof that the logical step from decision tree lower bounds to P ≠ NP is invalid

## Related Work

### Decision Tree Lower Bounds
- **Sorting**: Ω(n log n) comparison lower bound (proven via information theory)
- **Element Distinctness**: Ω(n log n) comparison lower bound
- **Convex Hull**: Ω(n log n) comparison lower bound

All of these problems ARE in P despite having super-polynomial decision tree lower bounds in restricted models!

### Clique Lower Bounds
- **Known**: Clique is NP-complete (Karp, 1972)
- **Known**: No polynomial-time algorithm is known for Clique
- **Unknown**: Whether a polynomial-time algorithm exists (this is equivalent to P vs NP!)
- **Model-Specific**: Various lower bounds exist for restricted models, but none for general polynomial-time computation

## Implementation Status

### Rocq (`rocq/DanielUribe2016.v`)
- ✅ Decision tree model definition
- ✅ Clique problem formalization
- ✅ Lower bound encoding
- ✅ Gap demonstration: model restriction ≠ general lower bound

### Lean (`lean/DanielUribe2016.lean`)
- ✅ Decision tree model definition
- ✅ Clique problem formalization
- ✅ Lower bound encoding
- ✅ Gap demonstration: model restriction ≠ general lower bound

### Isabelle/HOL (`isabelle/DanielUribe2016.thy`)
- ✅ Decision tree model definition
- ✅ Clique problem formalization
- ✅ Lower bound encoding
- ✅ Gap demonstration: model restriction ≠ general lower bound

## Lessons Learned

1. **Model Restrictions Matter**: Lower bounds in restricted computational models (decision trees, circuits, etc.) do not automatically transfer to general polynomial-time computation.

2. **Beware of Relativization**: Decision tree arguments are typically relativizing, which makes them insufficient for resolving P vs NP.

3. **Problem Formalization is Critical**: Precisely defining the computational model and the problem is essential for valid complexity arguments.

4. **Peer Review is Essential**: Mathematical proofs, especially for major open problems, require rigorous peer review to catch errors.

## References

### Primary Source
- **Uribe, D.** (2016). "P vs. NP" [Withdrawn]. arXiv:1601.03619. http://arxiv.org/abs/1601.03619

### Decision Tree Lower Bounds
- **Comparison-Based Sorting**: Any comparison-based sorting algorithm requires Ω(n log n) comparisons in the worst case.
- **Yao, A.** (1977). "Probabilistic computations: Toward a unified measure of complexity." *FOCS*

### Barriers
- **Baker, T., Gill, J., Solovay, R.** (1975). "Relativizations of the P =? NP Question." *SIAM J. Comput.* 4(4): 431-442
- **Razborov, A., Rudich, S.** (1997). "Natural Proofs." *J. Comput. System Sci.* 55(1): 24-35

### NP-Completeness
- **Karp, R.** (1972). "Reducibility among combinatorial problems." *Complexity of Computer Computations*, pp. 85-103

## See Also

- [P ≠ NP Framework](../../p_not_equal_np/README.md) - General framework for P ≠ NP proofs
- [Woeginger's List](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) - Comprehensive list of P vs NP proof attempts
- [Parent Issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally

---

**Status**: ✅ Formalization complete - Error identified and documented

**Last Updated**: October 2025
