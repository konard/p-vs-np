# Formalization: Daniel Uribe (2016) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../)

---

## Metadata

- **Attempt ID**: 106 (Woeginger's list)
- **Author**: Daniel Uribe
- **Year**: 2016
- **Claim**: P ≠ NP
- **Status**: Withdrawn (May 8, 2025)
- **Paper**: http://arxiv.org/abs/1601.03619 (no longer available)
- **Category**: Computational Complexity (cs.CC)

## Summary

In January 2016, Daniel Uribe submitted a paper claiming to prove that P is not equal to NP. The approach used decision tree analysis to study algorithmic runtime complexity. The method was first demonstrated on the sorting algorithm, then extended to analyze optimal algorithms for finding cliques in networks.

**Key Claim**: The lower bound of decision trees for the CLIQUE problem is not in P, implying P ≠ NP.

## Main Argument/Approach

Uribe's proof attempt followed this general structure:

### 1. Decision Tree Framework
- Used decision trees as a computational model for analyzing algorithm complexity
- Decision trees represent algorithms where each internal node asks a yes/no question
- Leaves represent outputs/solutions
- The depth of the tree represents the worst-case runtime

### 2. Sorting Algorithm Analysis
- Started with well-known decision tree lower bounds for comparison-based sorting
- Sorting n elements requires Ω(n log n) comparisons in the worst case
- This is a foundational result in computational complexity

### 3. Extension to CLIQUE Problem
- Applied decision tree analysis to the CLIQUE problem:
  - **Input**: A graph G = (V, E) and integer k
  - **Question**: Does G contain a clique of size k?
- Attempted to show that any decision tree solving CLIQUE requires exponential depth
- Claimed this exponential lower bound proves the problem is not in P

### 4. Conclusion
- If CLIQUE ∉ P and CLIQUE ∈ NP (which is well-known)
- Then P ≠ NP

## Known Refutation

A detailed critique was published by Henry B. Welles in May 2022:

**Paper**: "A Critique of Uribe's 'P vs. NP'" (arXiv:2205.01189)

### Identified Errors

The critique identifies two fundamental problems with Uribe's proof:

#### 1. **Failure to Generalize to All Algorithms**

Uribe's decision tree lower bound arguments do not apply to all possible algorithms for CLIQUE. Key issues:

- The proof only considers a specific class of algorithms (those representable as decision trees of a particular form)
- Does not account for algorithms using different computational approaches
- Misses the fact that lower bounds must apply to **all possible algorithms**, not just a restricted subset

**Why This Matters**: To prove CLIQUE ∉ P, one must show that **no polynomial-time algorithm exists**. Showing that a specific class of algorithms fails is insufficient.

#### 2. **Flawed Arguments Even for Applicable Algorithms**

Even for the algorithms to which Uribe's proofs might apply, the mathematical arguments contain technical flaws:

- Incorrect use of mathematical formulas (specifically noted: misuse of Legendre formula)
- Gaps in the reasoning about decision tree depth
- Insufficient justification for claimed exponential lower bounds
- Logic errors in the reduction arguments

### Methodological Concerns

The original arXiv submission also noted:

- Not guided by a research mentor
- Not associated with a research institution
- Inadequate problem description and formalization
- Lack of rigorous mathematical proof structure

## The Error in the Proof

The fundamental error can be understood at multiple levels:

### Conceptual Level

**Error**: Proving a lower bound for one computational model (decision trees) does not prove a lower bound for all possible algorithms.

**Correct Approach**: To prove P ≠ NP, one must show that **no algorithm whatsoever** (regardless of computational model) can solve an NP-complete problem in polynomial time.

### Technical Level

**Decision Tree Lower Bounds Are Model-Specific**:
- Decision tree lower bounds only apply to algorithms that follow the decision tree model
- Many polynomial-time algorithms cannot be efficiently represented as decision trees
- For example, algebraic and numerical algorithms may not fit the decision tree framework

**The CLIQUE Problem Example**:
- While decision trees for CLIQUE may require exponential depth
- This does not preclude the existence of a polynomial-time algorithm using a different approach
- The proof would need to account for **all possible computational approaches**

### Comparison with Valid Lower Bounds

**Valid Result**: Monotone circuit lower bounds for CLIQUE (Razborov, 1985)
- Proves exponential lower bound for **monotone circuits** specifically
- Does not claim to prove P ≠ NP
- Recognizes this is a restricted computational model

**Uribe's Mistake**:
- Claims decision tree lower bound implies P ≠ NP
- Does not account for non-decision-tree algorithms
- Overgeneralizes from restricted model to all computation

## Formal Verification Goals

This formalization aims to:

1. **Model the Decision Tree Framework**: Formalize decision trees and their depth as a complexity measure
2. **Formalize the CLIQUE Problem**: Define CLIQUE formally in terms of graphs and cliques
3. **Attempt to Prove the Lower Bound**: Try to formalize Uribe's claimed exponential lower bound for decision trees
4. **Identify the Gap**: Demonstrate where the proof fails to generalize from decision trees to all algorithms
5. **Document the Error**: Make explicit why decision tree lower bounds are insufficient for proving P ≠ NP

## Implementation Structure

### `/coq` - Coq Formalization
- `UribeAttempt.v`: Main formalization
- Defines decision trees, CLIQUE problem, and complexity measures
- Attempts to formalize the proof and identifies the gap

### `/lean` - Lean 4 Formalization
- `UribeAttempt.lean`: Main formalization
- Uses Lean's dependent type system
- Demonstrates where the proof reasoning breaks down

### `/isabelle` - Isabelle/HOL Formalization
- `UribeAttempt.thy`: Main formalization
- Higher-order logic approach
- Explicit modeling of the generalization failure

## Educational Value

This formalization demonstrates:

1. **The importance of computational models**: Different models have different power
2. **The challenge of universal quantification**: Proving something for all algorithms is much harder than for a specific class
3. **Common pitfalls in complexity theory**: Overgeneralizing from restricted models
4. **The rigor required for P vs NP**: Why the problem has resisted decades of attempts

## Related Work

### Decision Tree Complexity
- **Comparison-based sorting**: Ω(n log n) lower bound (tight)
- **Element distinctness**: Ω(n log n) lower bound in algebraic decision tree model
- **Various search problems**: Well-studied decision tree lower bounds

### CLIQUE Lower Bounds
- **Monotone circuits**: Exponential lower bound (Razborov, 1985)
- **Query complexity**: Various bounds in different query models
- **Approximation hardness**: Clique is hard to approximate (Håstad, 1999)

### Known Barriers to P ≠ NP
- **Relativization** (Baker-Gill-Solovay, 1975): Oracle-independent techniques cannot solve P vs NP
- **Natural Proofs** (Razborov-Rudich, 1997): "Natural" lower bound techniques face cryptographic barriers
- **Algebrization** (Aaronson-Wigderson, 2008): Extension of relativization barrier

**Note**: Decision tree arguments face the relativization barrier - they work equally in all relativized worlds and thus cannot resolve P vs NP.

## References

### Original Paper
- **Uribe, D.** (2016). "P vs. NP." arXiv:1601.03619 [cs.CC] (withdrawn)

### Critique
- **Welles, H. B.** (2022). "A Critique of Uribe's 'P vs. NP'." arXiv:2205.01189 [cs.CC]

### Related Papers
- **Razborov, A. A.** (1985). "Lower bounds on the monotone complexity of some Boolean functions." *Soviet Mathematics Doklady*, 31, 354-357.
- **Alon, N., & Boppana, R. B.** (1987). "The monotone circuit complexity of Boolean functions." *Combinatorica*, 7(1), 1-22.

### Background on Decision Trees
- **Ben-Or, M.** (1983). "Lower bounds for algebraic computation trees." *STOC '83*.
- **Yao, A. C.** (1994). "Decision tree complexity and Betti numbers." *STOC '94*.

### Textbooks
- **Arora, S., & Barak, B.** (2009). *Computational Complexity: A Modern Approach*. Cambridge University Press.
- **Jukna, S.** (2012). *Boolean Function Complexity: Advances and Frontiers*. Springer.

## Verification Status

- 🚧 Coq formalization: In development
- 🚧 Lean formalization: In development
- 🚧 Isabelle formalization: In development

## Notes

- The original paper PDF is no longer available on arXiv (withdrawn)
- Information reconstructed from abstract, Woeginger's list, and the 2022 critique
- This formalization is educational - demonstrates common errors in P vs NP proof attempts
- Highlights the gap between proving bounds for specific models vs. all possible algorithms

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Documentation](../../../P_VS_NP_TASK_DESCRIPTION.md)
