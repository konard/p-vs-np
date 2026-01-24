# Rubens Ramos Viana (2006) - Original Proof Idea

## Overview

Rubens Ramos Viana's 2006 paper attempts to prove **P ≠ NP** using concepts from quantum information theory and algorithmic complexity theory.

## The Claim

Viana constructed a specific problem using N-way quantum disentangled states and Chaitin's Omega (Ω), claiming it:
1. Requires exponentially many bits of Ω
2. Cannot be solved in polynomial time
3. Therefore proves P ≠ NP

## Core Approach: Quantum States + Algorithmic Information

### Key Components

#### 1. Chaitin's Omega (Ω)
- An algorithmically random constant from algorithmic information theory
- Incompressible: shortest program outputting L bits has length ≈ L bits
- **Uncomputable**: no algorithm can compute it (halting problem-hard)

#### 2. N-way Disentangled Quantum States
- Multi-qubit quantum systems with specific entanglement structure
- For N qubits, the general decomposition requires exponentially many coefficients
- For N > 4, number of terms grows faster than 2^N

#### 3. The Constructed Problem

**Input**: A number N (number of qubits)

**Output**: Find an N-way disentangled state Φ_Ω whose coefficients are derived from Ω

**Construction Method**:
1. S = number of coefficients (grows exponentially with N)
2. T = ⌈log₂(S)⌉
3. Extract first ST bits of Ω
4. Partition into S chunks of T bits each
5. Convert each chunk to a coefficient

**Solution**: The sequence of coefficients {B₁, B₂, ..., B_S}

## Why Viana Believed This Proves P ≠ NP

1. **Exponential Growth**: S grows exponentially (> 2^N for N > 4)
2. **Exponential Bits**: ST = S · ⌈log₂(S)⌉ bits of Ω needed
3. **Incompressibility**: Smallest program to output ST bits has size ≈ ST
4. **Runtime Lower Bound**: Program of size ST requires ≥ Ω(ST) time
5. **Conclusion**: Since ST grows exponentially, problem requires exponential time

## The Error

### Fundamental Category Mistake

Viana's argument confuses **function problems** with **decision problems**:

- **P and NP** are classes of **decision problems** (YES/NO questions)
- **Viana's problem** is a **function problem** (compute a sequence of numbers)
- This is a type error that invalidates the entire proof

Even if Viana's function problem requires exponential time, this says nothing about P vs NP because:
- The problem isn't even in NP (wrong type)
- Function problems and decision problems are different categories
- Finding one hard function problem doesn't separate complexity classes

### Additional Errors

1. **Ω is uncomputable, not hard**: Chaitin's Ω cannot be computed by ANY algorithm (not even exponential-time ones). This is computability theory, not complexity theory.

2. **Decision version might be easy**: "Given N and coefficients, are these correct?" might be polynomial-time verifiable.

3. **No connection to NP**: Even if converted to decision form, no proof it's in NP or that it's hard.

4. **Missing logical step**: The argument jumps from "this specific problem is hard" to "P ≠ NP" without justification.

## Why This Approach Cannot Work

1. **Type Mismatch**: Using function problems to prove statements about decision problem classes
2. **Computability ≠ Complexity**: Uncomputable objects belong to a different theory
3. **Relativization Barrier**: Properties of specific numbers likely don't overcome known barriers
4. **Natural Proofs Barrier**: Incompressibility is too "natural" a property

## References

### Primary Source
- **Viana, R. R.** (2006). "Using Disentangled States and Algorithmic Information Theory to Construct a Not P Problem"
  - arXiv:quant-ph/0612001
  - https://arxiv.org/abs/quant-ph/0612001

### Background
- **Woeginger's P vs NP List**: Entry #36
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Chaitin's Omega
- Chaitin, G. (1974). "Information-theoretic computational complexity"
- Chaitin, G. (1987). Algorithmic Information Theory, Cambridge University Press
- Calude, C. (1994). Information and Randomness, Springer-Verlag

### Complexity Theory
- Arora, S. & Barak, B. (2009). Computational Complexity: A Modern Approach
