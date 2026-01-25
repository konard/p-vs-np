# Jerrald Meek (2008) - P≠NP Attempt

**Attempt ID**: 46
**Author**: Jerrald Meek
**Year**: 2008
**Claim**: P ≠ NP
**Paper**: "Analysis of the postulates produced by Karp's Theorem"
**Source**: [arXiv:0808.3222](https://arxiv.org/abs/0808.3222)
**Listed on**: [Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) (Entry #46)

## Summary

Jerrald Meek attempts to prove P ≠ NP by arguing that solving one NP-Complete problem in polynomial time does not necessarily provide a polynomial-time solution to all NP-Complete problems. This is the final article in a four-part series where Meek challenges what he calls the "second postulate" of Karp's Theorem.

### Main Claim

> "A deterministic polynomial time solution to any NP-Complete problem does not necessarily produce a deterministic polynomial time solution to all NP-Complete problems."

Meek argues that:
1. Some NP-Complete problems (like base conversion viewed as a special case of Knapsack) can be solved in polynomial time
2. These polynomial-time solutions rely on special relationships between inputs
3. Such solutions cannot be transferred to solve the underlying K-SAT problem
4. Therefore, finding a fast solution to one NP-Complete problem doesn't prove P = NP
5. This implies P ≠ NP

## The Argument

### Core Approach

Meek's strategy involves several key steps:

1. **Base Conversion as NP-Complete**:
   - Shows that converting a decimal number to binary can be formulated as a 0-1-Knapsack problem
   - Proves this is NP-Complete by reduction from K-SAT
   - Example: Finding binary representation of 6 using S = ⟨1, 2, 4⟩

2. **Special-Case Polynomial Solution**:
   - The base conversion problem has a polynomial-time solution
   - This works because of the special relationship between elements (powers of 2)
   - Can quickly identify which literal in the underlying K-SAT is true

3. **Non-Transferability Argument**:
   - Claims this polynomial solution relies on special input structure
   - Argues the solution cannot solve the general underlying K-SAT problem
   - Concludes such solutions don't prove P = NP

4. **Elimination of Solution Classes**:
   - Exhaustive search: Ruled out by "P = NP Optimization Theorem"
   - Partitioned search: Ruled out by "P = NP Partition Theorem"
   - Quality-based solutions: Ruled out by various "Knapsack Theorems"
   - "Magical solutions": Ruled out by arguing all possibilities are covered

### Key Components

**The "Two Postulates" Interpretation**:
- Postulate 1: K-SAT reduces to all NP-Complete problems (Meek accepts this)
- Postulate 2: Solving any NP-Complete problem provides a solution to K-SAT (Meek rejects this)

**The K-SAT Input Relation Theorem** (Theorem 4.1):
- A solution relying on special input relationships doesn't solve all K-SAT instances
- Therefore, doesn't prove P = NP

**The "No Magical Solutions" Argument** (Section 5):
- Claims to enumerate all possible algorithmic approaches
- Argues each approach either doesn't work or doesn't transfer to all NP-Complete problems

## The Error

### Critical Flaw: Fundamental Misunderstanding of NP-Completeness

Meek's attempt contains a **catastrophic conceptual error** about what NP-Completeness means and what would constitute a proof of P ≠ NP. The entire argument is based on a misunderstanding of Karp's Theorem.

### 1. **Confusion About What NP-Completeness Means**

**The Fatal Misunderstanding**:
- Meek treats "base conversion" (with specific structure like powers of 2) as an NP-Complete **problem**
- In reality, base conversion is a **specific instance** of the 0-1-Knapsack problem
- NP-Completeness applies to **problem classes**, not individual instances

**Why This Matters**:
- An NP-Complete problem is a **set of instances** with varying inputs
- The 0-1-Knapsack problem includes instances with arbitrary real numbers in S
- Having a polynomial algorithm for **some instances** (like base conversion) doesn't make those instances "NP-Complete problems"
- It just means those instances are **easy instances** of an NP-Complete problem

**The Analogy**:
- This is like claiming 2-SAT is "NP-Complete" because it's a special case of 3-SAT
- Or claiming "SAT with no clauses" is "NP-Complete"
- Special cases of NP-Complete problems are not themselves NP-Complete

### 2. **Misinterpretation of Karp's Theorem**

**What Karp's Theorem Actually Says**:
- If ANY NP-Complete problem L has a polynomial-time algorithm that works for **all instances** of L
- Then ALL NP-Complete problems have polynomial-time algorithms for all their instances
- This is because of polynomial-time reductions between complete problems

**What Meek Thinks It Says**:
- Meek invents a "second postulate" that doesn't exist
- He argues solving "one NP-Complete problem" should give you the solution to others
- But he's confusing **one instance** with **the entire problem class**

**The Real Situation**:
- If you have an algorithm that solves **all instances** of 0-1-Knapsack in polynomial time
- Then you can solve all instances of SAT in polynomial time (via reduction)
- An algorithm that only works for **special cases** (like base conversion) doesn't count

### 3. **The "Base Conversion is NP-Complete" Claim is Wrong**

**Meek's Claim** (Section 4.1):
- Base conversion is proven NP-Complete by showing K-SAT reduces to it
- Example: Finding binary digits of 6 is an NP-Complete problem

**Why This is Wrong**:
- Base conversion with powers of 2 is a **single instance type** with special structure
- To prove something NP-Complete, you need to show:
  - (a) It's in NP (Meek shows this)
  - (b) You can reduce **from it** to a known NP-Complete problem (Meek doesn't show this)
- Meek shows you can reduce **to it** (from K-SAT), but that's backwards!
- Many problems have reductions from SAT to them (including problems in P)

**The Fundamental Error**:
- Meek: "K-SAT reduces to base conversion, therefore base conversion is NP-Complete"
- Reality: "K-SAT reduces to many problems, including easy ones. You need to show **hardness** by reducing **from** your problem to SAT"

### 4. **Circular Reasoning in "Ruling Out" Solutions**

**The Structure of Meek's Argument**:
1. Assume P ≠ NP (via claimed "theorems" from previous papers)
2. Use this assumption to show polynomial algorithms "don't exist"
3. Conclude P ≠ NP

**The Circularity**:
- The "P = NP Optimization Theorem" (Section 2.1) essentially **assumes** that examining more than polynomial inputs is required
- This is restating P ≠ NP, not proving it
- Same with "P = NP Partition Theorem" - assumes you can't partition efficiently
- The argument uses what it's trying to prove as a premise

### 5. **The "No Magical Solutions" Argument is Incomplete**

**Meek's Claim** (Section 5):
- All possible algorithms fall into 4 categories
- All 4 categories are ruled out
- Therefore P ≠ NP

**Why This Fails**:
- The categorization is informal and not exhaustive
- Many sophisticated algorithmic techniques don't fit these categories:
  - Algebraic algorithms
  - Geometric algorithms
  - Randomized algorithms with derandomization
  - Quantum algorithms (for related problems)
  - Novel computational models
- The "proof by exhaustion" is incomplete without a formal model

### 6. **Confusion of Instance Complexity vs Problem Complexity**

**Throughout the Paper**:
- Meek conflates solving **easy instances** with solving the **general problem**
- Example (Section 5.1): Shows that determining values a, b, c from d + e + f = g requires "checking possibilities"
- But this only shows those **specific instances** are hard under certain restrictions
- Doesn't show the **general problem class** requires exponential time

**What's Missing**:
- A formal proof that **all possible instances** of an NP-Complete problem require super-polynomial time
- Meek only shows that some special-case algorithms don't generalize
- This doesn't rule out completely different algorithmic approaches

### 7. **Dependence on Unproven "Theorems" from Prior Papers**

Meek's argument relies on theorems from earlier papers (Articles 1 and 2):
- "P = NP Optimization Theorem"
- "P = NP Partition Theorem"
- "Knapsack Random Set Theorem"
- "Knapsack Composition Theorem"

**The Problem**:
- These "theorems" are not established results in complexity theory
- They appear to contain similar errors (circular reasoning, instance/problem confusion)
- Building a proof on unproven foundations doesn't work
- The complexity theory community hasn't validated these claims

### 8. **Misunderstanding of Karp Reductions**

**Meek's Section 4.3 Argument**:
- An optimized Knapsack algorithm uses elements of S with "quality Q"
- For other NP-Complete problems, S and M are not provided
- Therefore the algorithm gives "undefined" result

**Why This is Wrong**:
- Karp reductions **provide** the transformation
- If Knapsack is in P, the reduction from SAT to Knapsack would:
  1. Transform SAT instance to Knapsack instance (with appropriate S and M)
  2. Solve the Knapsack instance in polynomial time
  3. Transform solution back to SAT solution
- The reduction **constructs** S and M from the SAT instance
- The algorithm doesn't need S and M to be "provided in the problem definition"

## Formalization Approach

Our formalization demonstrates:

1. **The Instance/Problem Distinction**:
   - Formalize what it means for a problem to be NP-Complete
   - Show that special instances ≠ special problem classes
   - Demonstrate base conversion is not an NP-Complete problem

2. **What Karp's Theorem Actually Says**:
   - Formalize polynomial-time many-one reductions
   - Show what's actually required to prove P ≠ NP
   - Identify where Meek's interpretation diverges from reality

3. **The Gap in the Argument**:
   - Show that "some instances are easy" ≠ "problem is in P"
   - Demonstrate that ruling out special-case algorithms doesn't prove P ≠ NP
   - Identify the circular reasoning in the "theorem" dependencies

## Formalization Status

### Coq (`coq/MeekAttempt.v`)
- Defines NP-Completeness properly (problem classes, not instances)
- Formalizes what Karp reductions actually provide
- **Identifies the gap**: Confuses instance-specific algorithms with general problem complexity

### Lean (`lean/MeekAttempt.lean`)
- Models the distinction between problems and instances
- Shows why base conversion ≠ NP-Complete problem
- **Identifies the gap**: Misinterpretation of reduction direction and NP-Completeness definition

### Isabelle (`isabelle/MeekAttempt.thy`)
- Provides formal structure for problem complexity classes
- Demonstrates the instance/problem confusion
- **Identifies the gap**: Circular dependency on unproven "theorems"

## Conclusion

Meek's attempt is **not a valid proof** of P ≠ NP because:

1. ❌ Fundamentally misunderstands what NP-Completeness means (confuses instances with problem classes)
2. ❌ Misinterprets Karp's Theorem (invents a non-existent "second postulate")
3. ❌ Claims base conversion is "NP-Complete" when it's just an easy instance of an NP-Complete problem
4. ❌ Uses circular reasoning (assumes P ≠ NP to prove P ≠ NP)
5. ❌ Depends on unproven "theorems" from earlier papers
6. ❌ Doesn't understand how polynomial-time reductions work
7. ❌ The "exhaustive categorization" of algorithms is informal and incomplete
8. ❌ Confuses showing "some approaches don't work" with "no approach can work"

### What This Shows

This formalization demonstrates an important lesson: **understanding the formal definitions in complexity theory is essential**. The distinction between:
- **Problems** (sets of instances) vs **instances** (individual inputs)
- **Hardness** (reductions from your problem) vs **membership** (reductions to your problem)
- **Special-case algorithms** vs **general algorithms**
- **Assuming a statement** vs **proving a statement**

These distinctions are crucial. A valid proof of P ≠ NP must:
- Work within the formal framework of complexity theory
- Properly understand NP-Completeness and reductions
- Prove that **all possible algorithms** for an NP-Complete problem require super-polynomial time
- Not assume what it's trying to prove
- Address or circumvent known proof barriers

### Impact on the Field

This attempt received critical feedback (acknowledged in the paper):
- Timothy Chow pointed out the instance/problem confusion
- Lance Fortnow warned about the difficulty of the problem
- The paper was never published in a peer-reviewed venue
- It remains on arXiv as version 5 (September 2008)

The attempt illustrates why:
- Peer review is important in mathematics
- Complexity theory requires precise formal understanding
- Intuitive arguments must be backed by rigorous proofs
- The P vs NP problem resists informal approaches

## References

1. Meek, J. (2008). "Analysis of the postulates produced by Karp's Theorem", arXiv:0808.3222
2. Meek, J. (2008). "P is a proper subset of NP", arXiv:0804.1079 (Article 1)
3. Meek, J. (2008). "Analysis of the deterministic polynomial time solvability of the 0-1-Knapsack problem", arXiv:0805.0517 (Article 2)
4. Karp, R. M. (1972). "Reducibility Among Combinatorial Problems", Complexity of Computer Computations, pp. 85-103
5. Cook, S. A. (1971). "The complexity of theorem-proving procedures", STOC 1971
6. Woeginger, G. J. "The P-versus-NP page", https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
7. Garey, M. R., Johnson, D. S. (1979). "Computers and Intractability: A Guide to the Theory of NP-Completeness"

## Related Work

- [proofs/p_not_equal_np/](../../p_not_equal_np/README.md) - Framework for verifying P ≠ NP proof attempts
- [P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md](../../../P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md) - Catalog of valid approaches
- [TOOLS_AND_METHODOLOGIES.md](../../../TOOLS_AND_METHODOLOGIES.md) - Tools for formal verification
