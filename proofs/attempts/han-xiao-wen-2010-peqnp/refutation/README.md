# Refutation: Han Xiao Wen 2010 P=NP Attempt

This directory contains the formal refutation of Han Xiao Wen's 2010 P=NP proof attempt.

## Contents

- `lean/HanXiaoWenRefutation.lean` - Lean 4 formalization demonstrating the errors
- `rocq/HanXiaoWenRefutation.v` - Rocq (Coq) formalization demonstrating the errors

## Summary of Refutation

Han Xiao Wen's 2010 papers claiming P=NP are refuted on multiple grounds:

### 1. Fundamental Contradiction

**The Core Error**: Han claims the "Knowledge Recognition Algorithm" (KRA) is simultaneously:
- **Deterministic**: Each computation step has a unique successor
- **Nondeterministic**: Each computation step has multiple possible successors

This is a category error. Deterministic and nondeterministic computation are mutually exclusive properties.

**Formalized As**: `deterministic_and_nondeterministic_contradiction`

### 2. Undefined Terminology

The papers introduce key concepts without formal definitions:

| Term | Status |
|------|--------|
| Mirrored Language Structure | Never formally defined |
| Perceptual-Conceptual Languages | Never formally defined |
| Member-Class Relations | Never formally defined |
| Chinese COVA | Mentioned without definition |

Without formal definitions, these concepts cannot be mathematically analyzed.

**Formalized As**: Axioms marking undefined concepts

### 3. No Algorithm Specification

The papers provide no concrete algorithm:
- No pseudocode
- No formal description
- No implementation

Without an algorithm, there is nothing to verify.

**Formalized As**: `han_papers_lack_essential_components`

### 4. No Complexity Analysis

The papers claim polynomial time but provide:
- No definition of the algorithm's steps
- No analysis of each step's time complexity
- No proof that total time is polynomial

**Formalized As**: `han_never_proves_polynomial_simulation`

### 5. Oracle Machine Confusion

Han conflates:
- **Oracle Machines**: Theoretical construct with magic oracles
- **Polynomial-Time Computation**: What P vs NP is about

Claiming to "simulate an oracle" without proving polynomial time is circular reasoning.

**Formalized As**: `oracle_simulation_requires_polynomial_time`

## What a Valid Proof Would Require

A valid P=NP proof via 3-SAT would need:

1. **Precise Algorithm**: Clear specification of every step
2. **Correctness Proof**: Rigorous proof that algorithm correctly decides 3-SAT
3. **Complexity Proof**: Rigorous proof of polynomial time bound
4. **Verification**: Either working implementation or formal proof
5. **Barrier Explanation**: How the proof avoids relativization, natural proofs, etc.

Han's papers provide NONE of these.

## The Missing Components

| Component | Required | Provided by Han |
|-----------|----------|-----------------|
| Formal definitions | Yes | No |
| Algorithm specification | Yes | No |
| Correctness proof | Yes | No |
| Complexity proof | Yes | No |
| Implementation | Recommended | No |
| Barrier discussion | Recommended | No |

## Known Barriers Not Addressed

Han's papers do not address known barriers to P vs NP proofs:

- **Relativization** (Baker-Gill-Solovay, 1975): The proof would need to be non-relativizing
- **Natural Proofs** (Razborov-Rudich, 1997): Barrier for certain proof techniques
- **Algebrization** (Aaronson-Wigderson, 2008): Another significant barrier

The vague nature of the papers makes it impossible to even classify which barriers would apply.

## Educational Value

This refutation demonstrates common patterns in failed P=NP attempts:

1. **Vague Terminology**: Introducing undefined concepts
2. **Category Errors**: Confusing mutually exclusive properties
3. **Missing Proofs**: Claiming without proving
4. **Model Confusion**: Conflating different computational models
5. **No Verification**: Providing nothing that can be tested

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Reconstructed content from original papers
- [`../proof/README.md`](../proof/README.md) - Forward formalization of claimed proof structure

## References

### The Original Papers
- arXiv:1006.2495 - "Mirrored Language Structure..."
- arXiv:1009.0884 - "Knowledge Recognition Algorithm enables P = NP"
- arXiv:1009.3687 - "3-SAT Polynomial Solution..."

### Background on P vs NP
- Cook, S. A. (1971). "The complexity of theorem proving procedures"
- Karp, R. M. (1972). "Reducibility among combinatorial problems"

### Known Barriers
- Baker, Gill, Solovay (1975). "Relativizations of the P =? NP Question"
- Razborov, Rudich (1997). "Natural Proofs"
- Aaronson, Wigderson (2008). "Algebrization"
