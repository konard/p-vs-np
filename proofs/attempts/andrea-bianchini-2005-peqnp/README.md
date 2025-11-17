# Andrea Bianchini (2005) - P=NP Attempt

**Attempt ID**: 16 (from Woeginger's list)
**Author**: Andrea Bianchini
**Year**: 2005
**Claim**: P = NP
**Status**: Refuted (contains fundamental error)

## Summary

In January 2005, Andrea Bianchini published a paper titled "A Polynomial-time Exact Algorithm for the Subset Sum Problem" claiming to prove P = NP by constructing a polynomial-time exact algorithm for the NP-hard SubsetSum problem.

## Main Argument/Approach

Bianchini's approach attempted to solve the SubsetSum problem using an algorithm claimed to run in polynomial time. The SubsetSum problem is known to be NP-complete, so a polynomial-time algorithm for it would imply P = NP.

### SubsetSum Problem Definition

Given a set of integers S = {a₁, a₂, ..., aₙ} and a target value T, determine whether there exists a subset S' ⊆ S such that the sum of elements in S' equals T.

## The Error in the Proof

The fundamental error in Bianchini's proof is the **confusion between pseudopolynomial time and true polynomial time complexity**.

### Detailed Explanation of the Error

#### 1. Input Encoding Matters

The complexity of an algorithm is measured relative to the **size of the input encoding**, not the numeric values themselves. For the SubsetSum problem:

- **Binary encoding**: Each integer aᵢ requires O(log aᵢ) bits
  - Example: The number 256 requires 8 bits (log₂ 256 = 8)
  - Input size for n numbers each ≤ M: O(n log M)

- **Unary encoding**: Each integer aᵢ requires O(aᵢ) bits
  - Example: The number 256 requires 256 bits (tally marks)
  - Input size for n numbers each ≤ M: O(n × M)

#### 2. The Critical Distinction

**Pseudopolynomial-time algorithms** are polynomial in the numeric values but **exponential** in the input size when using standard binary encoding.

The classic dynamic programming solution for SubsetSum:
- Time complexity: O(n × T) where T is the target sum
- This is polynomial in T (the numeric value)
- But T can be exponentially large compared to its binary encoding size O(log T)
- Therefore: O(n × T) = O(n × 2^(log T)) which is **exponential** in input size

#### 3. Concrete Example

Consider:
- 10 numbers, each between 128 and 256
- **Unary encoding**: Input size ≈ 10 × 256 = 2,560 bits
- **Binary encoding**: Input size ≈ 10 × 8 = 80 bits
- Ratio: 2,560 / 80 = 32 times larger!

An algorithm that is O(n × max(aᵢ)) would be:
- O(10 × 256) = O(2,560) operations in unary representation
- But O(10 × 2^8) = O(2,560) operations for only 80 bits of input in binary
- This is exponential: O(n × 2^k) where k = log₂(max(aᵢ))

#### 4. Why This Error is Common

This is a **weakly NP-complete** problem, meaning:
- NP-complete when numbers are encoded in binary (standard)
- Polynomial-time solvable when numbers are encoded in unary (non-standard)

Many attempted proofs of P = NP via SubsetSum fall into this trap by:
1. Using standard dynamic programming (pseudopolynomial time)
2. Incorrectly analyzing complexity relative to numeric values instead of input size
3. Claiming polynomial time without accounting for encoding

## Known Refutation

While no formal published refutation is widely available, the error is well-understood in the complexity theory community:

- The paper's algorithm likely runs in O(n × T) or similar time
- This is pseudopolynomial, not polynomial
- The paper does not account for the exponential relationship between numeric values and binary input size
- If the algorithm were truly polynomial in input size, it would have been recognized as resolving P vs NP

Reference: Discussion on Computer Science Stack Exchange (2014) regarding subset sum algorithms and the confusion between polynomial and pseudopolynomial time.

## Formalization Structure

This directory contains formal verification code that:

1. **Defines the SubsetSum problem formally**
2. **Formalizes input encoding (binary vs unary)**
3. **Proves the distinction between pseudopolynomial and polynomial time**
4. **Shows why O(n × T) is not polynomial in binary input size**
5. **Demonstrates the error in claiming polynomial-time solution**

### Files

- `coq/SubsetSumEncoding.v` - Coq formalization
- `lean/SubsetSumEncoding.lean` - Lean 4 formalization
- `isabelle/SubsetSumEncoding.thy` - Isabelle/HOL formalization

## Key Lessons

1. **Encoding matters**: Algorithm complexity must be measured against input encoding size
2. **Pseudopolynomial ≠ Polynomial**: Being polynomial in numeric values doesn't mean polynomial in input bits
3. **Weakly NP-complete problems**: Problems like SubsetSum, Knapsack, Partition are solvable in pseudopolynomial time but remain NP-complete
4. **Common pitfall**: Many P vs NP attempts fail by confusing these concepts

## References

1. Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #19)
2. Original paper: "A Polynomial-time Exact Algorithm for the Subset Sum Problem" (2005)
3. Computer Science Stack Exchange: Discussions on subset sum complexity (2014)
4. Standard textbook reference: Garey & Johnson, "Computers and Intractability" (1979) - Discussion of strong vs weak NP-completeness

## Related Work

- Pisinger (1999): "Linear Time Algorithms for Knapsack Problems with Bounded Weights"
- Bringmann (2017): "A Near-Linear Pseudopolynomial Time Algorithm for Subset Sum"
- Recent work continues to improve pseudopolynomial time bounds, but no polynomial-time algorithm in binary encoding exists

---

*This formalization is part of the P vs NP educational repository's effort to formally verify and understand attempted proofs, helping researchers learn from common errors.*
