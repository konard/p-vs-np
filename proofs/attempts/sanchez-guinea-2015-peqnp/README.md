# Sanchez Guinea (2015) - P=NP Claim

**Attempt ID**: 103
**Author**: Alejandro Sanchez Guinea
**Year**: 2015
**Claim**: P = NP
**Paper**: "Understanding SAT is in P"
**Source**: [arXiv:1504.00337v4](https://arxiv.org/abs/1504.00337)

## Summary

In April 2015, Alejandro Sanchez Guinea published a paper claiming to prove P=NP by designing an algorithm (Algorithm U) that solves 3-SAT in polynomial time. The approach introduces the concept of an "understanding" - a three-valued function mapping literals to {true, false, free} - and claims to construct satisfying assignments by analyzing the "contexts" (neighboring literals) of each literal in clauses.

## Main Argument

### Key Concepts

1. **Understanding**: A function ũ: L → {t, f, ε} mapping literals to true, false, or free
2. **Context**: For a literal l in clause {l₁, l₂, l₃}, the context is the other two literals
3. **Concept**: A context interpreted according to an understanding
4. **Concept Types**:
   - Type C⁺: Both literals false, or one false and one free, or both free
   - Type C*: Both literals true, or one true and one free, or one true and one false

### Algorithm Overview

**Algorithm U** (the main algorithm):
- **Input**: A 3-SAT instance Φ
- **Process**: Incrementally add clauses from Φ to a working set φ, maintaining an understanding ũ
- **For each clause**: Update ũ based on the "concepts" (contexts of literals interpreted under current understanding)
- **Output**: Either an understanding (claimed to be polynomial-time constructible) or "unsatisfiable"

**Supporting Algorithms**:
- **Algorithm G**: Verify if a literal can be made true
- **Algorithm D**: Recursively try to make a false literal free
- **⟨Compute ũ⟩**: Update understanding until no changes occur

### Claimed Complexity

The paper claims O(m²) time complexity, where m is the number of clauses, based on:
1. Processing each clause takes O(m) time for updating concepts
2. Algorithm D (recursive) is bounded by O(m) iterations
3. Total: O(m²) for m clauses

## The Error

### Critical Flaw: Exponential Recursion in Algorithm D

The fundamental error lies in the **time complexity analysis of Algorithm D** and its interaction with Algorithm U.

#### Problem 1: Unbounded Recursive Depth

**Algorithm D** (step D4) makes a **recursive call to itself** when trying to make a false literal free:
```
D4. If l is false under ũ', then set H' ← H + λ and ... define if possible
    an understanding ũ'' ... such that l is free under ũ''
    (this is done by Algorithm D).
```

The paper claims this recursion is bounded by the number of clauses (O(m)), but this analysis is **incorrect**. Here's why:

1. **Each recursive call** of Algorithm D may need to iterate through **multiple concepts** (D1-D2 loop)
2. **For each concept**, it may need to **recursively call Algorithm D again** (D4)
3. This creates a **tree of recursive calls** with:
   - Depth potentially proportional to the number of variables (n)
   - Branching factor potentially proportional to clause occurrences per literal

**Actual Complexity**: The recursion depth can be **O(n)** (number of variables), and at each level, the algorithm may branch **O(m)** times, leading to a **worst-case O(m^n)** or **O(2^n)** complexity - exponential, not polynomial!

#### Problem 2: The ⟨Compute ũ⟩ Operation

The **⟨Compute ũ⟩** operation used in G3, D5, and U4 states:
```
Compute ũ for each literal λ and its negation for which the type of C̃[λ]
has changed, until there is no change of type on any subset of concepts of C̃.
```

This is a **fixed-point computation** that iterates "until no change." The paper claims it takes O(m) time in the worst case, but:

1. **No proof** is given that this fixed-point computation terminates in polynomial steps
2. Changes to one literal can **cascade** to other literals through shared clauses
3. In the worst case, this could require **exponentially many iterations** to reach a fixed point

#### Problem 3: Hidden Dependency Graph

The algorithm implicitly builds a **dependency graph** between literals:
- Making literal l free may require making literals in C̃[¬l]⁻ true (Algorithm D)
- Making those literals true may require making other literals false or free
- This creates **cyclic dependencies** that the algorithm tries to break using set H

However:
- The paper provides **no bound** on the size or structure of this dependency graph
- The recursion through this graph (via repeated Algorithm D calls) can visit **exponentially many states**
- The set H prevents infinite loops but doesn't prevent **exponential exploration**

### Why This Error is Subtle

The error is subtle because:

1. **Local operations seem polynomial**: Each individual step (checking a concept, updating ũ) is indeed fast
2. **The recursion seems bounded**: The paper argues each recursive call processes "at most m clauses"
3. **The flaw is in composition**: The error emerges from the **interaction between recursive calls** across different literals and clauses

### Formal Statement of the Gap

**Claim** (Theorem 2 in paper): Algorithm U terminates in polynomial time, specifically O(m²).

**Reality**: The algorithm's worst-case time complexity is **exponential** in the number of variables n:
- Algorithm D has recursion depth O(n)
- At each level, it may try O(m) different concepts
- ⟨Compute ũ⟩ may require exponentially many iterations to converge

**Therefore**: The proof that 3-SAT ∈ P is **invalid**, and P=NP is **not established** by this paper.

### Additional Issues

1. **Lemma A**: The proof assumes that an understanding exists if and only if a satisfying assignment exists, but this equivalence is only shown for the case where the understanding is already defined - the proof is somewhat circular.

2. **Lemma D**: The conditions d1 and d2 for checking if a literal can be made free are **recursive** (d1 invokes Algorithm D recursively), making the termination analysis even more complex.

3. **Algorithm U step U3**: The ordering heuristic ("taking first literals that are not false") is not proven to avoid worst-case exponential behavior.

## Woeginger's Refutation

This attempt appears on Gerhard Woeginger's famous list of P=NP attempts (Entry #103). While Woeginger's site doesn't always provide detailed refutations, the consensus in the complexity theory community is that this paper contains the exponential recursion flaw described above.

## Formalization Strategy

Our formal verification in Coq, Lean, and Isabelle will:

1. **Formalize the 3-SAT problem** and the notion of polynomial-time algorithms
2. **Define the "understanding" concept** and related definitions (concepts, types C⁺/C*)
3. **Formalize Algorithms G, D, and U** as recursive functions
4. **Attempt to prove Theorem 2** (polynomial time complexity)
5. **Identify the gap**: Show that the recursion depth and iteration bounds are **not polynomially bounded**
6. **Conclude**: The proof attempt fails at the complexity analysis step

The formalization will make explicit what the paper leaves implicit: the **recursive structure** of Algorithm D and the **unbounded fixed-point iteration** of ⟨Compute ũ⟩.

## References

1. Sanchez Guinea, A. (2015). "Understanding SAT is in P." arXiv:1504.00337v4 [cs.CC]
2. Woeginger, G. J. "The P-versus-NP page." https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Cook, S. A. (1971). "The complexity of theorem-proving procedures." STOC 1971.

## Related Issues

- Parent issue: #44 (Test all P vs NP attempts formally)
- Source issue: #319 (This formalization task)
