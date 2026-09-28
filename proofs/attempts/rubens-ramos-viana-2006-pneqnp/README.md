# Rubens Ramos Viana (2006) - P≠NP via Quantum States

**Attempt ID**: 36 (Woeginger's list)
**Author**: Rubens Ramos Viana
**Year**: 2006
**Claim**: P ≠ NP
**Status**: ❌ Refuted (Category mistake + computability/complexity confusion)

## Quick Summary

Viana attempted to prove P ≠ NP by constructing a problem using quantum disentangled states and Chaitin's Omega (Ω), claiming it requires exponential time. The attempt fails due to a **fundamental category mistake**: the constructed "problem" is a function problem (compute coefficients), not a decision problem (YES/NO question), yet P and NP are classes of decision problems. Additionally, Viana confuses uncomputability (Ω cannot be computed by ANY algorithm) with computational complexity (P vs NP).

## The Claimed Proof

### Core Idea
1. Use N-way quantum disentangled states (require > 2^N coefficients for N > 4 qubits)
2. Derive coefficients from Chaitin's Omega Ω (algorithmically random, incompressible)
3. Problem requires extracting ST ≈ 2^N · N bits from Ω
4. Claim: any program needs size ≥ ST and time ≥ ST
5. Conclude: problem requires exponential time → P ≠ NP

### Why Viana Believed It Works
- Ω is incompressible (shortest program to output L bits has length ≈ L)
- ST bits are needed, so program must be ST bits long
- Program of size ST requires ≥ ST time to run
- Therefore exponential time is required

## The Errors

### Error 1: Category Mistake (FATAL)
- **P and NP**: Classes of **decision problems** (input → YES/NO)
- **Viana's problem**: **Function problem** (input N → sequence of coefficients)
- **Type error**: Cannot use function problem hardness to prove P ≠ NP
- Even if the function problem is hard, it says nothing about decision problem classes

### Error 2: Uncomputability ≠ Complexity
- **Chaitin's Ω**: UNCOMPUTABLE (no algorithm can compute it, halting problem-hard)
- **Complexity theory**: Studies decidable problems and their runtime
- **Mixing these**: Invalid category error from different areas of CS theory
- Problems requiring uncomputable objects are undecidable, not "not in P"

### Error 3: Decision Version Might Be Easy
- Even if converted to decision form: "Given N and coefficients, are these correct?"
- **No proof verification is hard**: Checking patterns might be polynomial-time
- Incompressibility of Ω doesn't imply verification complexity

### Error 4: Missing Logical Step
```
Viana's argument:
1. Function problem F is hard ✓ (claimed)
2. ??? (no valid step)
3. Therefore P ≠ NP ✗

Required argument:
1. Decision problem D ∈ NP
2. D requires superpolynomial time for ALL algorithms
3. Therefore P ≠ NP
```

## Why This Approach Fails

1. **Type Mismatch**: No way to infer decision class properties from function problems
2. **Computability Barrier**: Uncomputable ≠ hard; different theory entirely
3. **Relativization Barrier**: Using specific number properties likely relativizes
4. **Natural Proofs Barrier**: Incompressibility is too "natural" a property

## Directory Structure

- `README.md`: This file - overview of the attempt and its errors
- `ORIGINAL.md`: Summary of the original paper content
- `ORIGINAL.pdf`: Original arXiv paper (quant-ph/0612001)

- **proof/**: Formalization of the claimed proof structure
  - `README.md`: Explanation of what the forward proof captures
  - `lean/VianaProof.lean`: What Viana claimed (structure only)
  - `rocq/VianaProof.v`: What Viana claimed (structure only)

- **refutation/**: Formalization of why the proof fails
  - `README.md`: Detailed explanation of all errors
  - `lean/VianaRefutation.lean`: Formal proof of the errors
  - `rocq/VianaRefutation.v`: Formal proof of the errors

## Key Lessons

1. **Problem Type Matters**: Always verify you're working with decision problems for P vs NP
2. **Types Catch Errors**: Formal verification immediately reveals category mistakes
3. **Computability ≠ Complexity**: These are different areas of theoretical CS
4. **Specific ≠ General**: One hard instance doesn't prove class separation
5. **Known Barriers**: Valid proofs must overcome relativization, algebrization, natural proofs

## References

- **Viana (2006)**: "Using Disentangled States and Algorithmic Information Theory to Construct a Not P Problem"
  - arXiv: quant-ph/0612001
  - https://arxiv.org/abs/quant-ph/0612001

- **Woeginger's List**: Entry #36
  - https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

- **Background**:
  - Chaitin, G. (1987). Algorithmic Information Theory
  - Arora & Barak (2009). Computational Complexity: A Modern Approach

---

*This formalization demonstrates how formal verification catches category errors that invalidate complexity theory arguments.*
