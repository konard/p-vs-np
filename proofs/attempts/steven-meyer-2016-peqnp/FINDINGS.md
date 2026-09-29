# Findings: Steven Meyer (2016) P=NP Attempt

**Analysis Date**: 2025-10-26
**Attempt**: Steven Meyer (2016) - "Philosophical Solution to P=?NP: P is Equal to NP"
**Claim**: P = NP
**Status**: ❌ **REFUTED**

---

## Executive Summary

Steven Meyer's 2016 attempt to prove P = NP is fundamentally flawed. The argument rests on the false premise that changing the computational model from Turing machines to Random Access Machines with Multiply (MRAM) somehow resolves the P vs NP question. Our formal analysis demonstrates that this reflects a misunderstanding of the robustness of complexity classes.

## Core Errors Identified

### 1. **Model Independence Error** (CRITICAL)

**Claim**: Using MRAM instead of Turing machines changes the P vs NP problem.

**Reality**: Complexity classes P and NP are **robust** across all polynomial-time equivalent computational models.

**Formal Proof**: We proved in all three proof assistants (Rocq, Lean, Isabelle):
```
∀ problem. InP_TM problem ↔ InP_MRAM problem
```

**Implication**: Since P is the same in both models, P vs NP in the MRAM model is exactly equivalent to P vs NP in the Turing machine model. Changing models is completely irrelevant.

**What Meyer missed**: The polynomial-time Church-Turing thesis states that all reasonable models of computation are polynomial-time equivalent. This is a cornerstone of complexity theory.

### 2. **Simulation vs. Complexity Confusion** (CRITICAL)

**Claim**: Because MRAM can "simulate" nondeterministic Turing machines, P = NP.

**Reality**:
- **Yes**, MRAM can simulate NDTM in the sense of universal computation
- **No**, this doesn't mean the simulation is polynomial-time
- The whole point of P vs NP is whether nondeterminism can be eliminated with only polynomial overhead

**Analogy**: Saying "we can simulate NDTM" is like saying "we can solve SAT by trying all 2^n assignments." True, but not polynomial-time!

**What's missing**: Meyer provides **no algorithm** showing polynomial-time simulation of nondeterministic choice.

### 3. **Misunderstanding of NP** (FUNDAMENTAL)

**Error**: Treating NP as purely about nondeterministic Turing machines rather than polynomial-time verifiability.

**Correct understanding**:
- NP = problems with polynomial-time **verifiable** solutions
- Definition is **model-independent**
- Even in MRAM model: NP = {L | ∃ polynomial-time verifier V, ∀x: x ∈ L ↔ ∃cert: V(x,cert) accepts}

**Consequence**: Changing from TM to MRAM doesn't change what NP means.

### 4. **Philosophical Hand-Waving** (METHODOLOGICAL)

**Claim**: P vs NP is "scientific rather than mathematical" and "neither pure nor applied mathematics."

**Reality**:
- P vs NP has a **precise mathematical definition**
- The question is: ∀L ∈ NP. L ∈ P?
- This is a well-defined mathematical statement, regardless of philosophical interpretation

**Problem**: Philosophical framing doesn't substitute for mathematical proof.

### 5. **Appeal to Authority Without Content** (METHODOLOGICAL)

**References**: Gödel-von Neumann correspondence, criticisms of automata theory

**Issue**:
- Historical context is interesting but not a proof
- Even if von Neumann "rejected automata models" (citation needed), modern complexity theory is well-founded
- No technical content supports the main claim

### 6. **Missing Algorithmic Content** (CRITICAL GAP)

**What's required for P = NP**:
- A polynomial-time algorithm for an NP-complete problem (e.g., SAT, 3-SAT, Clique)
- **OR** a rigorous proof that such an algorithm exists
- Concrete time bounds and correctness proof

**What Meyer provides**:
- Philosophical arguments
- Model-switching claims
- No actual algorithm
- No complexity analysis

**Verdict**: The paper contains no constructive content that could constitute a proof of P = NP.

## Formalization Results

Our formalizations in three proof assistants successfully demonstrate the errors:

### Rocq (MeyerAttempt.v)
- ✓ Formalized TM, RAM, and MRAM models
- ✓ Proved polynomial-time equivalence
- ✓ Proved P is model-independent: `P_model_independent_TM_MRAM`
- ✓ Refuted Meyer's claim: `meyer_error_model_equivalence`

### Lean (MeyerAttempt.lean)
- ✓ Formalized all computational models
- ✓ Proved `MRAM_does_not_change_P`
- ✓ Proved `changing_model_does_not_resolve_P_vs_NP`
- ✓ All theorems verified

### Isabelle (MeyerAttempt.thy)
- ✓ Complete formalization of models
- ✓ Proved model independence
- ✓ Demonstrated logical error in Meyer's argument
- ✓ All theorems verified

## Key Lessons for Future Proof Attempts

This attempt illustrates several common errors in P vs NP proof attempts:

1. **Robustness Misunderstanding**: Not recognizing that P and NP are robust across reasonable computational models

2. **Model vs. Class Confusion**: Conflating the choice of computational model with the definition of complexity classes

3. **Simulation Fallacy**: Assuming that being able to simulate nondeterminism (in exponential time) gives polynomial-time simulation

4. **Definitional Errors**: Misunderstanding what NP actually means (verifiability, not just nondeterminism)

5. **Lack of Formality**: Substituting philosophical arguments for mathematical proofs

6. **Missing Constructive Content**: Not providing the required algorithm or rigorous impossibility proof

## Conclusion

Steven Meyer's 2016 attempt fails to prove P = NP because it is based on a fundamental misunderstanding of computational complexity theory. The claim that using MRAM instead of Turing machines resolves P vs NP demonstrates:

- **Misunderstanding** of the polynomial-time Church-Turing thesis
- **Confusion** about the relationship between computational models and complexity classes
- **Lack of awareness** of the robustness of P and NP
- **Absence** of the required algorithmic or proof content

The formal verification in Rocq, Lean, and Isabelle conclusively demonstrates that changing computational models does not affect the P vs NP question.

**Final Assessment**: The attempt contains no valid mathematical content that advances toward resolving P vs NP.

---

## References

- **Meyer's Paper**: arXiv:1603.06018 (March 2016)
- **Polynomial-time Church-Turing Thesis**: Cobham (1965), Edmonds (1965)
- **Model Equivalence**: Arora & Barak, "Computational Complexity: A Modern Approach", Chapter 1
- **Our Formalizations**:
  - [Rocq](rocq/MeyerAttempt.v)
  - [Lean](lean/MeyerAttempt.lean)
  - [Isabelle](isabelle/MeyerAttempt.thy)
