# Jerrald Meek (2008) - P≠NP Attempt

**Attempt ID**: 43 (from [Woeginger's list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm))
**Author**: Jerrald Meek
**Year**: 2008 (April, final revision September)
**Claim**: P ≠ NP
**Paper**: "P is a proper subset of NP" - [arXiv:0804.1079](https://arxiv.org/abs/0804.1079)
**Status**: Never published (12 revisions, all rejected)

## Overview

Meek attempts to prove P≠NP through a **"computational rate" analysis**, arguing that:

1. For k-SAT with n clauses, there are 2^(kn) possible truth assignments
2. A polynomial-time algorithm performs only poly(n) operations
3. The ratio r(n) = 2^(kn)/poly(n) → ∞ as n → ∞
4. Therefore, algorithms must "examine ≤ polynomial input sets"
5. Finding such "search partitions" is FEXP-hard (exponential time)
6. This creates a circular dependency, proving P ≠ NP

## Critical Errors

### 1. **Confuses Search Space with Computational Requirements**

**Error**: Assumes solving SAT requires "processing" all 2^n truth assignments.

**Reality**: Algorithms (if they exist) might use algebraic techniques, structural properties, or transformations that never enumerate assignments.

**Counterexample**: 2-SAT is in P but doesn't work by enumerating assignments—it uses implication graphs.

### 2. **Circular Reasoning**

**Error**: Assumes there's no efficient way to find "search partitions" (i.e., assumes P≠NP) to prove P≠NP.

**Problem**: If P=NP, then by definition there would exist efficient methods; assuming none exist is circular.

### 3. **Invalid Inferences from Asymptotic Analysis**

**Error**: From "2^n / poly(n) → ∞" concludes "problem is hard".

**Counterexample**: Sorting has n! permutations (exponential), but can be done in O(n log n) time.

**Issue**: Search space size ≠ computational complexity.

### 4. **Undefined Concepts**

- **"Computational rate"**: No formal meaning in complexity theory
- **"Processing input sets"**: Algorithms don't work this way
- **"Representative polynomial search partition"**: Never rigorously defined

### 5. **Misunderstands How Algorithms Work**

**Assumes**: All algorithms work by finding partition → enumerating within partition.

**Reality**: Algorithms can use structure, algebraic methods, transformations, etc.

### 6. **Depends on Unproven Claims**

- Article 2: Claims about Knapsack (unpublished/rejected)
- Article 3: Claims about oracle relativization (unpublished/rejected)
- Article 4: **Claims "SAT does not have polynomial-time solution"** (this IS what needs proving!)

### 7. **Fails Known Barriers**

**Relativization** (Baker-Gill-Solovay, 1975): Meek's counting argument would work the same with oracle access, but we know relativizing proofs cannot resolve P vs NP.

## Folder Structure

```
jerrald-meek-2008-pneqnp/
├── README.md (this file)
├── ORIGINAL.pdf - Original arXiv paper
├── ORIGINAL.md - Markdown conversion of the paper
├── proof/
│   └── README.md - Why forward proof is unformalizable
├── refutation/
│   ├── README.md - Summary of errors
│   ├── lean/
│   │   └── MeekAttempt.lean - Demonstrates circular reasoning and invalid concepts
│   └── rocq/
│       └── MeekAttempt.v - Identifies invalid inferences
```

## Educational Value

This formalization demonstrates an important lesson:

> **Counting arguments about search space sizes do not directly translate to computational complexity separations.**

The size of the solution space (exponential) and the time complexity of the best algorithm (potentially polynomial) are **distinct concepts**. A valid proof of P≠NP must show that **every possible algorithm** requires superpolynomial time, not just that naive enumeration does.

## Historical Context

- Paper went through **12 revisions** between April-September 2008
- Author acknowledges feedback from **Stephen Cook**, who "identified an incorrect premise in a previous version"
- **Never accepted for publication**
- Part of a 4-paper series (Articles 2-4 also rejected/unpublished)

## The Core Misunderstanding

**Meek's implicit assumption**: Solving SAT = Searching through assignments

**Reality**: Solving SAT might involve:
- Algebraic transformations
- Structural decomposition
- Novel algorithmic techniques we haven't discovered
- Exploiting hidden structure in the problem

The entire argument rests on the assumption that any algorithm must essentially "touch" or "process" a large number of possible assignments, but this is **exactly the assumption that P≠NP makes**. Using it to prove P≠NP is circular.

## Key Formalization Results

All formalizations demonstrate:

1. **Gap in "Optimization Theorem"**: The claim that algorithms must "examine ≤ poly(n) input sets" is unformalizable—it assumes a specific (and unjustified) model of computation

2. **Circular "Partition Finding" Claim**: The assertion that finding search partitions is FEXP-hard assumes P≠NP (no efficient method exists), making the entire argument circular

3. **Valid Math, Invalid Conclusion**: While 2^n > poly(n) is mathematically correct, it doesn't imply computational hardness

## References

1. Meek, J. (2008). "P is a proper subset of NP", arXiv:0804.1079v12
2. Woeginger's P vs NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
3. Baker, Gill, Solovay (1975). "Relativizations of the P=?NP Question"
4. Razborov, Rudich (1997). "Natural Proofs"

---

**Status**: ✅ All formalizations complete with comprehensive error analysis
**Note**: Isabelle formalization moved to `archive/isabelle/` due to Isabelle support sunset (#530)
