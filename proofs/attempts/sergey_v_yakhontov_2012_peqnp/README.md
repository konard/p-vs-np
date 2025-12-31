# Sergey V. Yakhontov (2012) - P=NP Proof Attempt

**Author**: Sergey V. Yakhontov
**Year**: 2012
**Claim**: P = NP (constructive proof)
**Paper**: [arXiv:1208.0954v38](https://arxiv.org/abs/1208.0954)
**Status**: Flawed

## Overview

This is a formalization of Sergey V. Yakhontov's 2012 attempt to prove P=NP constructively. The paper claims to provide a polynomial-time deterministic multi-tape Turing machine M(∃AcceptingPath) that determines whether a polynomial-time non-deterministic single-tape Turing machine M(NP) has an accepting computation path.

## Main Argument

The proof attempts to establish P=NP through the following approach:

### 1. Novel Reduction Strategy

Instead of the traditional reduction path:
```
L ≤_P^m 3-CNF-SAT ≤_P^m ILP
```

The paper proposes:
```
L ≤_P^m TCPE ≤_P^m LP
```

Where:
- **TCPE** (Tape-Consistent Path Existence Problem): A new NP-complete problem introduced by the author
- **LP**: Linear Programming (polynomial-time solvable)

### 2. Core Concepts

**Computation Steps**: Each step is defined as a tuple:
```
(q, s, q', s', m, κ^(tape), κ^(step))
```
Where q, q' are states, s, s' are symbols, m is head movement, and κ^(tape), κ^(step) are commodities.

**Tape-Arbitrary Sequences**: Sequences of computation steps that:
- Start on input x (initial configuration)
- May or may not be tape-consistent
- Form a polynomial-size subset of all possible computation paths

**Tape-Consistent Sequences**: Tape-arbitrary sequences that additionally satisfy:
- Tape consistency conditions (read/write operations match)
- Can be verified by checking commodity flow equations

**Control Flow Graph**:
- Acyclic directed graph representing computation paths
- Size: O(|Δ| × t(n)^2) where Δ is the transition relation
- Constructed from the exponential computation tree through "reaching definitions" analysis

### 3. The Construction

1. **Step 1**: Convert non-deterministic single-tape TM to deterministic multi-tape TM
   - Claims time complexity: O(2^(C_σ × t(n)^272))
   - For Von Neumann architecture: O(2^(C_σ × t(n)^68))
   - Where C_σ depends on the transition relation Δ

2. **Step 2**: Define TCPE problem:
   - Input: Control flow graph, tape consistency constraints
   - Output: Does there exist a tape-consistent path to accepting state?
   - Claim: TCPE is NP-complete (proven in paper)

3. **Step 3**: Reduce TCPE to Linear Programming:
   - Formulate as network flow problem with commodities
   - Each commodity represents a tape cell's value flow
   - Connector graphs handle commodity intersections
   - Claims the LP has polynomial size

4. **Step 4**: Solve LP in polynomial time
   - Uses standard polynomial-time LP algorithms
   - Claims this gives polynomial-time solution to TCPE
   - Therefore claims polynomial-time solution to SAT and all NP problems

## The Error

The fundamental error in this proof lies in the **misrepresentation of complexity**:

### 1. Exponential Constants Hidden in "Polynomial Time"

The claimed time complexity is **O(2^(C_σ × t(n)^272))** where:
- t(n) is the time bound of the non-deterministic TM
- C_σ is a constant depending on the transition relation |Δ|
- For many NP problems, t(n) can be exponential in input size n

**Critical Issue**: While this is polynomial in t(n), it is **exponential in the input size n** for most NP-complete problems. This violates the definition of polynomial time complexity, which must be polynomial in the input size n, not in an intermediate parameter t(n).

### 2. Confusion Between Parameters

The paper conflates:
- **Polynomial in t(n)** (the NP machine's time bound)
- **Polynomial in n** (the actual input size)

For SAT with n variables:
- Input size: O(n)
- NP machine time bound t(n): O(2^n) for exhaustive search
- Claimed algorithm: O(2^(C_σ × (2^n)^272)) = O(2^(C_σ × 2^(272n)))

This is **doubly exponential** in the input size, not polynomial.

### 3. The TCPE Size Problem

While the paper claims the control flow graph is polynomial in t(n), it fails to account for:
- The number of distinct commodities scales with tape cells accessed
- For NP problems, this can be exponential in input size n
- The LP formulation therefore has exponentially many variables and constraints in n

### 4. Tape Cell Addressing

The construction requires:
- Tracking all possible tape cell positions (exponentially many)
- Creating commodities for each position (exponential)
- The "polynomial-size" control flow graph is only polynomial if you already know which O(t(n)) cells are accessed
- But determining which cells are accessed requires solving the original problem

## Formalization Strategy

Our formalization proceeds in the following stages:

### Stage 1: Basic Definitions (All Proof Assistants)
- Define Turing machines (deterministic and non-deterministic)
- Define computation steps and paths
- Define tape-arbitrary and tape-consistent sequences
- Define the P and NP complexity classes

### Stage 2: The Control Flow Graph Construction
- Formalize the construction of the control flow graph from a non-deterministic TM
- Prove its size is O(|Δ| × t(n)^2)
- **Identify the gap**: Show that t(n) can be exponential in n for NP problems

### Stage 3: The TCPE Problem
- Formalize the TCPE problem definition
- Prove TCPE is NP-complete (following the paper's proof)
- **Identify the contradiction**: If TCPE is NP-complete, it cannot have a polynomial-time solution unless P=NP (circular reasoning)

### Stage 4: The Linear Programming Reduction
- Formalize the LP formulation with commodities
- Count the number of variables and constraints
- **Prove the error**: Show that the LP size is exponential in input size n, not polynomial

### Stage 5: Complexity Analysis
- Formalize the claimed time complexity O(2^(C_σ × t(n)^272))
- **Prove the error**: For SAT instances, this is at least doubly exponential in n
- Show this violates the definition of polynomial time in input size

## Files in This Directory

- `README.md` - This file
- `yakhontov-2012.pdf` - The original paper (arXiv:1208.0954v38)
- `coq/YakhontovProof.v` - Coq formalization
- `lean/YakhontovProof.lean` - Lean 4 formalization
- `isabelle/YakhontovProof.thy` - Isabelle/HOL formalization

## Key Insights

1. **Polynomial in the wrong variable**: The construction is polynomial in t(n) but exponential in n
2. **Circular reasoning**: Assumes TCPE (NP-complete) can be solved in polynomial time to prove P=NP
3. **Hidden exponential blowup**: The "polynomial-size" structures require exponential resources when measured against input size
4. **Misunderstanding of complexity classes**: Confuses time bounds of non-deterministic machines with deterministic polynomial time

## References

- Yakhontov, S. V. (2012). "Polynomial-Time Algorithm for NP-Complete Problems." arXiv:1208.0954v38
- Woeginger's P-vs-NP page: Entry #90
- Related to mixed-DHORN-SAT and linear-CNF-SAT problems

## Verification Status

- Coq formalization: In progress
- Lean formalization: In progress
- Isabelle formalization: In progress

All formalizations aim to explicitly construct the error and prove the claimed polynomial-time algorithm actually has exponential time complexity in the input size.
