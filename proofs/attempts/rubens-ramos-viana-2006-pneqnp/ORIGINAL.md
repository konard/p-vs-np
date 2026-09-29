# Viana (2006) - Original Paper Summary

## Title
"Using Disentangled States and Algorithmic Information Theory to Construct a Not P Problem"

## Publication Details
- **Author**: Rubens Ramos Viana
- **Year**: 2006
- **arXiv ID**: quant-ph/0612001
- **URL**: https://arxiv.org/abs/quant-ph/0612001
- **Woeginger's List**: Entry #36

## Abstract Summary

Viana proposes using N-way disentangled quantum states combined with Chaitin's Omega (Ω) to construct a problem that provably cannot be solved in polynomial time, thus proving P ≠ NP.

## Main Claims

1. **Construction**: A problem based on N-way quantum disentangled states with coefficients derived from Chaitin's Ω
2. **Exponential Requirement**: The problem requires exponentially many bits of Ω (ST bits where S > 2^N for N > 4)
3. **Lower Bound**: Any algorithm solving this problem must have size ≥ ST and runtime ≥ Ω(ST)
4. **Conclusion**: Since ST grows exponentially, the problem is not in P

## Key Technical Elements

### Chaitin's Omega (Ω)
- Halting probability: probability that a random program halts
- Algorithmically random: incompressible
- First L bits require ≈ L bits to specify
- **Critical property used**: Incompressibility

### N-way Disentangled States
- Multi-party quantum states with specific entanglement structure
- For N > 4 qubits: decomposition requires > 2^N terms
- Each term has a coefficient
- **Critical property used**: Exponential growth in coefficients

### The Constructed Problem
- **Input**: Number N (number of qubits)
- **Output**: Quantum state Φ_Ω with coefficients from Ω
- **Method**: Extract ST bits from Ω, partition into S chunks, use as coefficients

## Author's Argument

1. Problem requires extracting ST ≈ 2^N · N bits from Ω
2. Ω is incompressible, so any program must store ST bits
3. Program size ≥ ST implies runtime ≥ ST
4. ST is exponential in N
5. Therefore problem requires exponential time
6. Conclusion: P ≠ NP

## Verification Claim

Viana argues that even with nondeterministic guessing:
- Verification requires checking against Ω
- This verification takes exponential time
- Therefore problem is "not NP"

## Paper Organization

1. **Introduction**: Motivation using quantum information theory
2. **Background**: Chaitin's Ω and its properties
3. **N-way Disentangled States**: Definition and coefficient growth
4. **Problem Construction**: How to build Φ_Ω from Ω
5. **Complexity Analysis**: Why it requires exponential time
6. **Conclusion**: P ≠ NP

## Original Text (Key Quote)

> "The proposed problem is not a NP problem because once the solution was guessed, it would take a non-polynomial time to check it."

This quote reveals the fundamental misunderstanding: NP is about decision problems with polynomial-time verifiable certificates, not about function problems.

## Why This is in Woeginger's List

Classified as a failed P ≠ NP proof due to:
- Category mistake (function vs decision problem)
- Confusion between uncomputability and complexity
- No valid connection to NP complexity class
- Missing logical steps from "hard problem" to "P ≠ NP"

---

*This summary is for educational purposes to understand the structure and errors in the original attempt.*
