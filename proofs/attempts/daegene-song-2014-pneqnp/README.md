# Formalization: Daegene Song (2014) - P≠NP

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Core Documentation](../../../README.md#core-documentation)

---

## Overview

**Attempt ID**: 99 (from Woeginger's list)
**Author**: Daegene Song
**Year**: 2014 (February)
**Claim**: P ≠ NP
**Paper**: "The P versus NP Problem in Quantum Physics"
**Source**: http://arxiv.org/abs/1402.6970

## Summary

In February 2014, Daegene Song proposed a proof that P ≠ NP by examining the problem through the lens of quantum physics. The main approach is to consider P and NP not merely as abstract computational complexity classes, but as classes of actual physical processes:

- **P**: Class of deterministic polynomial-time physical processes
- **NP**: Class of nondeterministic polynomial-time physical processes

The paper argues that by examining how information is encoded and processed by physical systems in quantum theory, one can identify a "self-reference physical process" in quantum theory that belongs to NP but cannot be contained in P, thereby establishing P ≠ NP.

## Main Argument/Approach

The approach attempts to bridge computational complexity theory with quantum physics by:

1. **Physical Interpretation**: Reinterpreting complexity classes as classes of physical processes rather than abstract computational models
2. **Quantum Framework**: Utilizing quantum theory to analyze the fundamental nature of computation
3. **Self-Reference Process**: Identifying a specific quantum physical process that exhibits self-reference properties
4. **Separation Claim**: Arguing that this self-reference process is inherently nondeterministic and cannot be reduced to a deterministic polynomial-time process

### Key Claims

- Information processing can be understood through physical processes
- Quantum theory provides the framework for understanding computational limitations
- A self-reference quantum process exists that is verifiable in polynomial time (NP) but not solvable deterministically in polynomial time (P)
- This provides a physical basis for the separation between P and NP

## Known Issues and Critical Analysis

### Fundamental Problems

1. **Vague Physical-Computational Connection**: The paper does not provide a rigorous formal mapping between quantum physical processes and Turing machine computation. Standard complexity theory defines P and NP in terms of Turing machines or equivalent computational models, not physical processes.

2. **Missing Formal Definition**: The "self-reference physical process" is not precisely defined mathematically. Without a clear formal definition, it's impossible to verify whether it actually belongs to NP or whether it's outside P.

3. **Church-Turing Thesis Confusion**: The paper may conflate the physical Church-Turing thesis (all physical processes can be simulated by Turing machines) with the computational complexity question of P vs NP. Even if quantum processes have special properties, this doesn't immediately translate to complexity class separation.

4. **Quantum Computation vs Classical Complexity**: The relationship between quantum computation (BQP) and classical complexity classes (P, NP) is subtle. BQP is believed to be between P and NP, but this doesn't resolve P vs NP. The paper doesn't clearly address this distinction.

5. **Lack of Formal Proof Structure**: The paper lacks the rigorous mathematical proof structure expected for a Clay Millennium Prize Problem. It doesn't provide:
   - Formal definitions of all key terms
   - Lemmas building toward the main result
   - Rigorous proofs of intermediate steps
   - Clear statement of the main theorem

### The Core Error

The fundamental error is **category confusion**: mixing physical processes with formal computational models without establishing a rigorous correspondence. P and NP are defined via formal computational models (Turing machines), not via physical processes. While physical intuition can guide research, a valid proof requires:

1. Formal definition of the claimed hard problem
2. Proof that it's in NP (polynomial-time verifiable)
3. Proof that it's not in P (no polynomial-time algorithm exists)
4. All arguments must work within the standard complexity-theoretic framework

The paper attempts to bypass the standard framework by appealing to physical intuition, but this approach doesn't constitute a valid mathematical proof.

### Community Response

Limited formal refutation exists in published literature, but community discussion (e.g., on FQXi forums) notes:
- The paper doesn't meet the standard of proof required for P vs NP
- The connection between quantum physics and complexity class separation is not rigorously established
- Proving P=NP requires showing that nondeterministic computers can efficiently solve NP-complete problems, which the paper doesn't address at the required level of rigor

## Formalization Goal

This directory contains formalizations of the paper's approach in multiple proof assistants (Coq, Lean, Isabelle) to make explicit where the argument fails. The formalization attempts to:

1. **Model quantum physical processes** in a formal framework
2. **Define the "self-reference process"** precisely
3. **Attempt to prove** that this process is in NP
4. **Attempt to prove** that this process is not in P
5. **Identify the gap** where the proof breaks down

By formalizing the argument, we can pinpoint exactly where informal reasoning fails to translate into rigorous proof.

## Formalization Structure

```
proofs/attempts/daegene-song-2014-pneqnp/
├── README.md                 (this file)
├── coq/
│   └── DaegeneSong2014.v    (Coq formalization)
├── lean/
│   └── DaegeneSong2014.lean (Lean 4 formalization)
└── isabelle/
    └── DaegeneSong2014.thy  (Isabelle/HOL formalization)
```

## Expected Outcome

The formalization will likely reveal that:

1. **Undefined Terms**: The "self-reference physical process" cannot be given a precise formal definition that satisfies the required properties
2. **Unprovable Claims**: Either the claim "process is in NP" or "process is not in P" cannot be proven within the formal framework
3. **Circular Reasoning**: The proof may assume what it's trying to prove
4. **Type Errors**: When formalized, the physical and computational concepts may not type-check together

## References

### Primary Source
- **Song, D.** (2014). "The P versus NP Problem in Quantum Physics." *arXiv:1402.6970*
  http://arxiv.org/abs/1402.6970

### Relevant Background
- **Aaronson, S.** (2013). "Quantum Computing since Democritus." *Cambridge University Press*
- **Arora, S., Barak, B.** (2009). "Computational Complexity: A Modern Approach." Chapter on physical computation
- **Nielsen, M., Chuang, I.** (2010). "Quantum Computation and Quantum Information."
- **Woeginger, G.** P versus NP page: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #99)

### Related Issues
- [Issue #44](https://github.com/konard/p-vs-np/issues/44) - Test all P vs NP attempts formally
- [Issue #113](https://github.com/konard/p-vs-np/issues/113) - This formalization effort

## Status

- ✅ Coq formalization: Complete (with identified gaps)
- ✅ Lean formalization: Complete (with identified gaps)
- ✅ Isabelle formalization: Complete (with identified gaps)
- ✅ Error documentation: Complete (errors identified and documented in code and README)

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [P vs NP Attempts](../)
