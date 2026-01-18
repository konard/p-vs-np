# Jorma Jormakka (2008) - P≠NP Proof Attempt

**Attempt ID**: 47 (from Woeginger's list)
**Author**: Jorma Jormakka
**Year**: 2008
**Claim**: P ≠ NP
**Status**: **REFUTED** - Contains fundamental logical errors

## Overview

In September 2008, Jorma Jormakka published a paper titled "On the existence of polynomial-time algorithms to the subset sum problem" on arXiv (arXiv:0809.4935). The paper claims to prove that no polynomial-time algorithm exists for the subset sum problem, thereby establishing P ≠ NP.

## Main Argument

The proof attempts to establish P ≠ NP through a recursive lower bound argument:

1. **Define a complexity measure** f(n) representing the "worst in the median" computation time for any algorithm solving subset sum instances of size n
2. **Construct adversarial instances** K₁, K₂, K₃ that force any chosen algorithm to recursively solve n/2 subproblems of size n/2
3. **Derive the recurrence** f(n) ≥ (n/2)f(n/2)
4. **Conclude** that f(n) grows super-polynomially, therefore no polynomial-time algorithm exists
5. **Final conclusion**: Since subset sum is NP-complete, this implies P ≠ NP

## The Critical Errors

This proof contains **multiple fundamental flaws** that invalidate the entire argument:

### **Error 1: Circular Adversarial Construction**

**The Fatal Flaw**: The proof constructs hard instances AFTER selecting the algorithm, tailored specifically to that algorithm's behavior.

**Why This Is Wrong**:
- Definition 2 and Definition 3 construct instances K₁, K₂, K₃ based on the execution behavior of the chosen algorithm
- The construction explicitly selects j'ᵢ values that take "at least as long as the median computation time f(n₁)" (Definition 3)
- This is circular: you cannot prove an algorithm is slow by constructing inputs designed to be slow for that specific algorithm
- A valid lower bound must work for ALL algorithms simultaneously, not be tailored to each one individually

**The Logical Structure of the Error**:
```
1. Choose an arbitrary algorithm A
2. Analyze how A works (branches, execution paths)
3. Construct instances specifically designed to be hard for A
4. Show that A takes super-polynomial time on these instances
5. Conclude: "Therefore, A is not polynomial-time"
```

This proves nothing about the intrinsic hardness of subset sum - only that we can construct adversarial instances for any specific algorithm.

### **Error 2: Non-Uniform Lower Bound Technique**

**The Problem**: The proof technique is **non-uniform** - it constructs different hard instances for different algorithms.

**Why This Matters**:
- To prove P ≠ NP, you must show that a SINGLE problem (or set of instances) is hard for ALL polynomial-time algorithms
- Instead, this proof shows that for EACH algorithm, there EXISTS a hard instance for that algorithm
- These are completely different claims:
  - **What's needed**: ∃ problem P such that ∀ polynomial-time algorithms A, A cannot solve P
  - **What's proven**: ∀ algorithms A, ∃ instance Iₐ such that A is slow on Iₐ

**Formal Gap**: Different algorithms might have different hard instances, so there may be no universally hard instance.

### **Error 3: Assumption of Algorithm Structure**

**The Problem**: Lemma 5 and Remark 2 assume algorithms can be modeled as von Neumann machines with branching instructions.

**Why This Fails**:
- The proof assumes algorithms have a "branching tree" structure that partitions inputs into equivalence classes
- This assumption is used to argue that "we can find values j'ᵢ which are not executed by the same polynomial-time run"
- However, this analysis is specific to certain algorithmic models and may not apply to all possible algorithms
- Novel algorithmic techniques might not fit this model (e.g., quantum algorithms, non-deterministic shortcuts, implicit algorithms)

**Missing Justification**: The proof does not rigorously show that ALL possible algorithms must follow this branching structure.

### **Error 4: The Median Computation Time Measure**

**The Problem**: Definition 2's f(n) measure is problematic and not well-justified.

**Why This Is Questionable**:
- The proof uses "median computation time over instances with no solution" as its complexity measure
- This is an unusual measure - standard complexity theory uses worst-case or average-case over ALL instances
- The restriction to instances without solutions is artificial and creates logical issues
- Different instance distributions could yield different median times

**Consequence**: The recurrence f(n) ≥ (n/2)f(n/2) is only shown for this specific, non-standard measure, not for standard complexity measures.

### **Error 5: Gap in Lemma 5 (Non-Reusability Claim)**

**The Problem**: Lemma 5 claims that different values j'ᵢ cannot be solved in the same "polynomial time run" because of branching.

**Why This Is Incomplete**:
- The proof argues that branching instructions create partitions, and we can select j'ᵢ in different partitions
- However, a polynomial-time algorithm could potentially use memoization, dynamic programming, or other techniques to share computation
- The proof assumes a specific execution model where each instance requires a separate "run"
- This doesn't account for algorithms that solve multiple instances simultaneously or cache intermediate results

**Missing Rigor**: The proof doesn't formally define what constitutes a "run" or rigorously prove that sharing computation across instances is impossible.

### **Error 6: Ignoring Known Barriers**

The proof does not address the major barriers to proving P ≠ NP:

1. **Relativization Barrier** (Baker-Gill-Solovay, 1975): The proof technique appears to relativize (work in all oracle worlds). Since there exist oracles relative to which P = NP, any relativizing proof cannot resolve P vs NP.

2. **Natural Proofs Barrier** (Razborov-Rudich, 1997): The construction seems to be "natural" in the technical sense, which would make it subject to this barrier under cryptographic assumptions.

3. **Algebrization Barrier** (Aaronson-Wigderson, 2008): The technique doesn't appear to circumvent algebrization.

**Critical Point**: The proof's approach (analyzing algorithm behavior and constructing hard instances) appears to relativize, which means it cannot possibly resolve P vs NP.

## Classification of Errors

- **Primary Error Type**: Circular reasoning / non-uniform adversarial argument
- **Secondary Issues**: Unjustified algorithmic assumptions, non-standard complexity measure
- **Severity**: Fatal - invalidates the entire proof
- **Known Barrier Violations**: Likely violates relativization barrier

## What Would Be Required for a Valid Proof

To validly prove that subset sum requires super-polynomial time, one would need:

1. **Uniform Lower Bound**: A proof that works for ALL algorithms simultaneously, not tailored to each algorithm
2. **Algorithm-Independent Construction**: Hard instances must be defined independently of the algorithm, not constructed after observing the algorithm's behavior
3. **Barrier Circumvention**: The technique must overcome relativization, natural proofs, and algebrization barriers
4. **Rigorous Computational Model**: A precise formal model with rigorous proofs about ALL possible algorithms in that model
5. **Universal Argument**: Show that ANY algorithm solving subset sum must perform certain operations, establishing an unavoidable lower bound

## Detailed Analysis of the Proof Strategy

### The Construction Strategy (Section 3-4)

The proof proceeds in steps:

1. **Definition 2**: Define f(n) as the maximum median computation time over all n-tuples
2. **Definition 3**: Given an algorithm A, construct K₁,ⱼₙ with n/2 subproblems that each take time ≥ f(n/2)
3. **Lemma 5**: Argue these n/2 subproblems must be solved separately
4. **Definition 4-5**: Transform K₁ → K₃ → K₂ to handle varying upper/lower bits
5. **Lemma 15**: Show f(n) ≥ (n/2)f(n/2)
6. **Lemma 1-2**: Prove this recurrence implies super-polynomial growth

### Why This Strategy Fails

**The Core Issue**: Steps 2-3 are *adversarial* and *algorithm-dependent*. The construction of K₁,ⱼₙ DEPENDS on the algorithm A:

- Equation (3.2)-(3.3) selects aₖ values based on which j'ᵢ = jₙ,ₗ - aᵢ have "at least as long computation time as the median"
- This REQUIRES knowing how algorithm A performs on different inputs
- Different algorithms would yield different K₁,ⱼₙ constructions

**Why This Cannot Work**: To prove a lower bound, you must show that a SINGLE instance (or distribution) is hard for ALL algorithms. But this proof shows that for EACH algorithm, there EXISTS an instance hard for that algorithm. These are logically different claims.

**Analogy**: It's like trying to prove "no one can solve all puzzles quickly" by saying "for each person, I can find a puzzle they struggle with." That doesn't prove puzzles are inherently hard - it just proves you can tailor puzzles to individual weaknesses.

## Formal Verification

This repository contains formal proofs in three proof assistants demonstrating the logical errors:

- **[Coq](coq/JormakkaAttempt.v)**: Formalization showing the circular adversarial construction
- **[Lean](lean/JormakkaAttempt.lean)**: Formalization showing the non-uniform lower bound error
- **[Isabelle/HOL](isabelle/JormakkaAttempt.thy)**: Formalization showing the gap in the argument

Each formalization explicitly shows that the construction of hard instances depends on the chosen algorithm, revealing the non-uniform and circular nature of the proof.

## Educational Value

This attempt is valuable for understanding:

1. **The difficulty of lower bounds** - You cannot prove lower bounds by constructing adversarial instances tailored to each algorithm
2. **Uniform vs. non-uniform arguments** - The difference between "∀A∃I" and "∃I∀A"
3. **Why P vs NP is hard** - Simple recursive arguments fail because they don't account for all possible algorithms
4. **Common fallacies** - The danger of circular constructions and algorithm-dependent arguments
5. **The barrier theorems** - Why certain proof strategies are known to fail
6. **Complexity theory rigor** - The need for precise formal definitions and universal quantification

## Historical Context

This type of error - constructing algorithm-specific hard instances - appears in many failed P vs NP attempts. The confusion between:
- "For each algorithm, there exists a hard instance for that algorithm"
- "There exists an instance that is hard for all algorithms"

is extremely common and represents a fundamental misunderstanding of what lower bounds require.

## Technical Remarks

### On the Recurrence Relation

Even if the construction were valid, the recurrence f(n) ≥ (n/2)f(n/2) would only prove:
- f(n) ∈ Ω(n^(log n)) which is super-polynomial
- But this is for the specific measure f(n), not for worst-case complexity

### On Algorithm A0 in the Annex

Lemma A2 shows that if jₙ has an upper bound independent of n, then subset sum is in P. This is correct but not relevant to the main argument's validity.

## Current Status of Subset Sum Complexity

Currently known facts about subset sum:

- **Best known algorithm**: Pseudo-polynomial time O(nS) where S is the target sum (dynamic programming)
- **Hardness**: Subset sum is NP-complete (reduction from 3-SAT)
- **Approximation**: FPTAS exists for optimization version
- **Open question**: Whether a polynomial-time algorithm exists (equivalent to P = NP)

The claim "no polynomial-time algorithm exists" remains unproven and would require resolving P vs NP.

## References

- **Source**: Woeginger's P vs NP page, Entry #47: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
- **Original Paper**: "On the existence of polynomial-time algorithms to the subset sum problem", arXiv:0809.4935v4 [math.GM] (2008)
- **arXiv Link**: https://arxiv.org/abs/0809.4935
- **Related Work**:
  - Baker, T., Gill, J., & Solovay, R. (1975). "Relativizations of the P =? NP Question". SIAM Journal on Computing.
  - Razborov, A. & Rudich, S. (1997). "Natural Proofs". Journal of Computer Science and Systems.
  - Aaronson, S. & Wigderson, A. (2008). "Algebrization: A New Barrier in Complexity Theory". ACM Transactions on Computation Theory.

## Conclusion

The Jormakka 2008 proof attempt fails because it employs a **non-uniform, adversarial construction** that tailors hard instances to each specific algorithm. This is fundamentally different from proving that a problem is intrinsically hard for all algorithms.

The proof demonstrates: "For all algorithms A, there exists an instance IA hard for A"

What's needed to prove P ≠ NP: "There exists an instance I hard for all polynomial-time algorithms A"

These are logically distinct claims, and the former does not imply the latter. The proof's reliance on algorithm-specific constructions makes it a circular argument that assumes what it tries to prove.

---

**Key Lesson**: Lower bound proofs must be **uniform** - the hard instances must be defined independently of the algorithm, not constructed adversarially after observing the algorithm's behavior. Tailoring instances to algorithm weaknesses proves nothing about the intrinsic hardness of the problem.

**Status**: This formalization is part of issue #452, formalizing P vs NP proof attempts to identify errors.
**Parent Issue**: #44 - Test all P vs NP attempts formally
