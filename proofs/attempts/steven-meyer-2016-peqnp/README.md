# Steven Meyer (2016) - P=NP Proof Attempt

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Proof Attempts](../)

---

## Metadata

- **Author**: Steven Meyer
- **Year**: 2016 (March)
- **Claim**: P = NP
- **Paper**: "Philosophical Solution to P=?NP: P is Equal to NP"
- **ArXiv**: [arXiv:1603.06018](https://arxiv.org/abs/1603.06018)
- **Woeginger's List**: Entry #113

## Summary

Steven Meyer proposes a philosophical solution to the P vs NP problem, claiming that P equals NP in the Random Access Machine with Unit Multiply (MRAM) model. Meyer argues that the P vs NP problem is fundamentally a scientific rather than mathematical question, and critiques the use of Non-Deterministic Turing Machines (NDTMs) as the basis for defining NP.

## Main Argument

### Central Thesis

Meyer's argument rests on several key claims:

1. **MRAM as the "correct" model**: Meyer argues that the MRAM (Random Access Machine with Unit Multiply) model "empirically best models computation hardness"

2. **Critique of NDTMs**: The paper asserts that the current definition of the P vs NP problem using Non-Deterministic Turing Machines is fundamentally flawed and based on incorrect assumptions from axiomatic automata theory

3. **Equivalence claim**: Meyer claims to demonstrate that MRAMs have the same computational power as NDTMs

4. **Philosophical reframing**: The problem is characterized as "scientific rather than mathematical" and "neither a problem in pure nor applied mathematics"

### Computational Model

The paper focuses on the MRAM (Random Access Machine with Unit Multiply) model, which:
- Has random access memory
- Supports unit-cost multiplication
- Is claimed to be equivalent in power to NDTMs
- Is argued to be the "empirically correct" model for measuring computational hardness

### Proof Strategy

Meyer's approach involves:
1. Arguing that MRAM machines can simulate NDTMs
2. Claiming that "the computation power of MRAMs is the same as NDTMs"
3. Using this equivalence to conclude P = NP
4. Critiquing previous attempts (particularly Deolalikar's P ≠ NP claim)
5. Appealing to historical correspondence between Gödel and von Neumann

## Identified Errors and Issues

### Critical Error 1: Conflation of Computational Models with Complexity Classes

**Error**: Meyer conflates the choice of computational model (Turing machines vs. RAM models) with the definition of complexity classes P and NP.

**Why this is wrong**:
- The classes P and NP are **robust** across polynomial-time equivalent models
- Church-Turing thesis and its polynomial-time variant establish that reasonable computational models are polynomial-time equivalent
- Changing from Turing machines to RAM models (or MRAM) does **not** change which problems are in P or NP
- Both standard RAM and MRAM are polynomial-time equivalent to Turing machines for decision problems

**Formal statement**: If a language L is in P under Turing machines, there exists a polynomial-time RAM algorithm for L, and vice versa (up to polynomial factors in the conversion).

### Critical Error 2: Misunderstanding of Nondeterminism

**Error**: The paper appears to misunderstand the nature of nondeterministic computation and the NP class.

**Why this is wrong**:
- NP is defined via **polynomial-time verifiability**, not just nondeterministic computation
- The verifier definition of NP (∃-witness formulation) is independent of the computational model
- Even in the MRAM model, NP would still be defined as problems with polynomial-time verifiable witnesses
- Simulation of NDTMs by MRAMs doesn't make NP collapse to P

**Key insight**: NP = "problems with polynomial-time checkable solutions" is model-independent.

### Critical Error 3: Invalid Inference from Model Equivalence

**Error**: Even if MRAMs could simulate NDTMs efficiently (which needs proper definition), this doesn't imply P = NP.

**Why this is wrong**:
- **All** standard models (TMs, RAM, MRAM, etc.) can simulate each other with at most polynomial overhead
- This simulation is **already accounted for** in the definition of P and NP
- The existence of a simulation does not collapse the distinction between deterministic and nondeterministic time
- The key question is not "can we simulate?" but "can we simulate without exponential overhead?"

### Critical Error 4: Philosophical vs. Mathematical Confusion

**Error**: Claiming P vs NP is "scientific rather than mathematical" or "neither pure nor applied mathematics."

**Why this is wrong**:
- P vs NP is a **precisely defined mathematical question** about the relationship between two complexity classes
- The formal definitions use standard mathematical logic and computation theory
- Whether a problem is "philosophical" or "mathematical" doesn't change its formal content
- This appears to be an attempt to sidestep the actual mathematical content of the problem

### Critical Error 5: Appeal to Authority Without Technical Content

**Error**: References to Gödel-von Neumann correspondence and critiques of automata theory don't constitute a proof.

**Why this is wrong**:
- Historical correspondence, while interesting, doesn't resolve modern complexity-theoretic questions
- The P vs NP problem is formally defined and requires a formal proof
- Criticizing the foundations of automata theory requires rigorous mathematical arguments, not philosophical assertions
- Even if von Neumann "rejected automata models" (citation needed), this doesn't invalidate modern complexity theory

### Gap 1: Missing Formal Definitions

The paper lacks:
- Formal definition of the MRAM model used
- Precise statement of what "simulation" means
- Complexity-theoretic analysis of the claimed simulation
- Formal proof of any claimed equivalences

### Gap 2: No Treatment of Known Barriers

The paper doesn't address:
- Relativization barrier (Baker-Gill-Solovay)
- Natural proofs barrier (Razborov-Rudich)
- Why the proposed approach would circumvent these barriers

### Gap 3: No Concrete Algorithm

If P = NP, there should exist a polynomial-time algorithm for an NP-complete problem:
- No such algorithm is provided
- No constructive proof is given
- The paper offers only philosophical arguments, not algorithmic content

## Formalization Strategy

Our formalization identifies the core logical errors by:

1. **Formalizing computational model equivalence**: Showing that Turing machines, RAM, and MRAM are polynomial-time equivalent

2. **Formalizing P and NP in multiple models**: Demonstrating that the definition of P and NP is model-independent (up to polynomial factors)

3. **Showing the gap**: Proving that model equivalence does **not** imply P = NP

4. **Identifying the invalid inference**: Formalizing why "MRAM simulates NDTM" doesn't give us P = NP

## Repository Structure

```
proofs/attempts/steven-meyer-2016-peqnp/
├── README.md           # This file
├── coq/
│   └── MeyerAttempt.v  # Coq formalization
├── lean/
│   └── MeyerAttempt.lean  # Lean 4 formalization
└── isabelle/
    └── MeyerAttempt.thy   # Isabelle/HOL formalization
```

## Key Lessons

This attempt illustrates several common pitfalls in P vs NP proof attempts:

1. **Model confusion**: Conflating computational models with complexity classes
2. **Robustness misunderstanding**: Not recognizing that P and NP are robust across reasonable models
3. **Nondeterminism misunderstanding**: Misinterpreting what nondeterministic computation means
4. **Philosophical handwaving**: Attempting to resolve a precise mathematical question with philosophical arguments
5. **Missing formal content**: Lack of rigorous definitions, proofs, and algorithmic details

## References

- **Original paper**: Steven Meyer, "Philosophical Solution to P=?NP: P is Equal to NP", arXiv:1603.06018, March 2016
- **Woeginger's list**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #113)
- **Model equivalence**: See any standard complexity theory textbook (Arora & Barak, Papadimitriou, etc.)
- **Church-Turing thesis**: Turing, "On Computable Numbers...", 1936
- **Polynomial-time Church-Turing thesis**: Discussed in Cobham (1965), Edmonds (1965)

## Verification Status

All formalizations compile and successfully demonstrate the logical errors in Meyer's argument:

- ✓ Coq formalization: [coq/MeyerAttempt.v](coq/MeyerAttempt.v)
- ✓ Lean formalization: [lean/MeyerAttempt.lean](lean/MeyerAttempt.lean)
- ✓ Isabelle formalization: [isabelle/MeyerAttempt.thy](isabelle/MeyerAttempt.thy)

---

**Conclusion**: Meyer's attempt fails because it fundamentally misunderstands the relationship between computational models and complexity classes. The claim that using a different computational model (MRAM instead of Turing machines) resolves P vs NP demonstrates a misunderstanding of the robustness of complexity classes and the polynomial-time Church-Turing thesis.
