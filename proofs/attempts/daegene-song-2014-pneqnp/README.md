# Daegene Song (2014) - P≠NP via Quantum Self-Reference

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [All Proof Attempts](../../README.md)

---

## Metadata

- **Attempt ID**: 99 (from Woeginger's list)
- **Author**: Daegene Song
- **Affiliation**: School of Liberal Arts, KoreaTech, Chungnam 330-708, Korea
- **Year**: 2014 (February 12)
- **Claim**: P ≠ NP
- **Paper**: "The P versus NP Problem in Quantum Physics"
- **arXiv**: [1402.6970v1](https://arxiv.org/abs/1402.6970) [physics.gen-ph]
- **Length**: 4 pages, 2 figures
- **Source**: Woeginger's P vs NP attempts list

## Summary

Song's 2014 paper claims to prove P ≠ NP by considering P and NP as classes of physical processes rather than abstract computational models. The main argument identifies P with deterministic polynomial-time physical processes and NP with nondeterministic polynomial-time physical processes. The paper then presents a quantum mechanical phenomenon involving "self-reference" — specifically, observing the evolution of a reference frame with respect to itself — which allegedly belongs to NP but cannot be in P.

## Main Argument

### 1. Physical Process Interpretation

Song reinterprets computational complexity through a physics lens:
- **P**: Class of deterministic polynomial-time physical processes
- **NP**: Class of nondeterministic polynomial-time physical processes
- Motivation: "information is physical" (Landauer)

### 2. Nondeterministic Turing Machine (NTM) Construction

The paper defines a specific NTM where for input `a`, the output can be either `b₁` or `b₂`:

```
δ(a) = {b₁, b₂}
```

With two transition functions:
- `δ₁: a → b₁` (identified with Schrödinger picture)
- `δ₂: a → b₂` (identified with Heisenberg picture)

### 3. Quantum Mechanical Example

**Setup**: A qubit initially pointing in z-direction: ν̂ = (0, 0, 1)

**Case (P1) - Normal computation**: Observing evolution of system µ̂ with respect to reference frame ν̂
- Schrödinger picture: Apply Uθ to µ̂
- Heisenberg picture: Apply U†θ to observable
- **Result**: Both yield same expectation value ✓

**Case (P2) - Self-reference**: Observing evolution of ν̂ with respect to itself (µ̂ = ν̂)
- Schrödinger picture: ν̂ → ν̂' = (sin θ, 0, cos θ)
- Heisenberg picture: ν̂ → ν̂'' = (−sin θ, 0, cos θ)
- **Result**: ν̂' ≠ ν̂'' unless θ = kπ

### 4. The Claimed Proof

Song argues:
1. Process (P2) exhibits nondeterminism (two different outcomes)
2. Process (P2) requires only a single rotation (polynomial time) → P2 ∈ NP
3. No deterministic Turing machine (DTM) can compute either path
4. Therefore, (P2) ∈ NP but (P2) ∉ P
5. Conclusion: P ≠ NP

## Critical Analysis: Errors in the Proof

This proof attempt contains several fundamental errors:

### Error 1: Conflation of Observer Choice with Computational Nondeterminism

**The Problem**: Song conflates an observer's choice of reference frame with the nondeterminism in NP computation.

- In NP computation, nondeterminism means the machine can "guess" the right computation path
- The choice between Schrödinger and Heisenberg pictures is a **choice of mathematical representation**, not a computational process
- These are two equivalent ways of describing the same physics (unitary equivalence)

**Why it matters**: The "nondeterminism" Song identifies is not computational nondeterminism, but rather human choice of description. This is like saying classical mechanics is "nondeterministic" because we can describe it in Cartesian or polar coordinates.

### Error 2: Misunderstanding of Turing Machine Equivalence

**The Problem**: Song claims deterministic Turing machines must yield identical results under both δ₁ and δ₂.

- DTMs don't have "two pictures" — this is a quantum mechanical concept
- The requirement that "both schemes yield same outcome" applies to **physical predictions**, not to intermediate mathematical representations
- The paper incorrectly maps physical picture choices onto computational transitions

**Why it matters**: This creates a false dichotomy. DTMs and NTMs are defined by their computational behavior, not by representation choices in the formalism.

### Error 3: Confusion Between Physical Process and Computation

**The Problem**: The distinction between physical phenomenon (P2) and its computability is unclear.

- Song argues that (P2) "cannot be computed" by deterministic machines
- But what does it mean to "compute" a physical process?
- The paper conflates:
  - **Simulating** the physics (which quantum computers can do)
  - **Predicting** measurement outcomes (which both pictures do)
  - **Choosing** which mathematical description to use (not a computational problem)

**Why it matters**: The notion of "computing" physical process (P2) is not well-defined in terms of decision problems or language recognition, which are the standard framework for P vs NP.

### Error 4: Invalid Application of NP Definition

**The Problem**: Process (P2) doesn't fit the standard definition of NP.

**Standard NP definition**: A language L ∈ NP if there exists a verifier V such that:
- For x ∈ L: ∃ certificate c such that V(x, c) accepts in poly-time
- For x ∉ L: ∀ certificates c, V(x, c) rejects

**Song's (P2)**:
- Not a decision problem (no yes/no question)
- Not a language (no set of strings)
- The "nondeterminism" is choice of description, not certificate verification

**Why it matters**: Without embedding (P2) into the standard complexity-theoretic framework, the claim "(P2) ∈ NP but (P2) ∉ P" is not well-formed.

### Error 5: The Verification Argument Fails

Song acknowledges the verifier perspective but dismisses it incorrectly:

> "if we consider NP in (P2) indirectly... it is easy to verify that the path is indeed the physical process when given the choice. However... there are not any deterministic machines that can compute paths (4) or (5)"

**The Problem**:
- Verification in NP means checking a certificate efficiently
- The claim that DTMs cannot "compute" the paths is unsupported
- A classical computer can certainly compute:
  - The rotation matrix Uθ
  - The vectors (sin θ, 0, cos θ) and (−sin θ, 0, cos θ)
  - Which one results from which picture choice

### Error 6: False Dichotomy in Physical Realizability

**The Problem**: The paper suggests quantum weirdness creates a computational advantage for P vs NP.

**Reality**:
- The Schrödinger and Heisenberg pictures are **unitarily equivalent**
- They make identical physical predictions for all observables
- The "difference" between ν̂' and ν̂'' is an artifact of coordinate choice, not physical reality
- No measurement can distinguish which "picture" was "really" used

**Why it matters**: There is no actual physical phenomenon that corresponds to the claimed NP process. The two pictures are mathematical conveniences, not distinct physical realities.

## The Core Misunderstanding

The fundamental error is treating **mathematical representation choices** as if they were **physical or computational processes**. The Schrödinger and Heisenberg pictures are like describing motion in terms of "ball moves right" vs "observer moves left" — these are equivalent descriptions, not different physical processes.

In computational terms, this is like claiming:
- "Computing f(x) by evaluating left-to-right is P"
- "Computing f(x) by evaluating right-to-left is NP"
- "Since they're different procedures, P ≠ NP"

This confuses **implementation details** with **computational complexity**.

## Formalization Goals

Our formal verification aims to:

1. **Formalize the setup**: Define the quantum mechanical scenario precisely
2. **Identify the gap**: Show that the "nondeterminism" is not computational
3. **Demonstrate equivalence**: Prove Schrödinger and Heisenberg pictures yield same physics
4. **Show the error**: Make explicit why this doesn't establish P ≠ NP

## Structure of Formalizations

Each formalization (Coq, Lean, Isabelle) will include:

### 1. Basic Quantum Mechanics
- State vectors in Bloch sphere representation
- Unitary transformations (rotation operators)
- Expectation values

### 2. The Two Pictures
- **Schrödinger**: State evolves, observable fixed
- **Heisenberg**: Observable evolves, state fixed
- **Equivalence theorem**: Both yield identical expectation values

### 3. The Self-Reference Case
- Setup: ν̂ = (0, 0, 1), rotation by angle θ
- Schrödinger result: ν̂' = (sin θ, 0, cos θ)
- Heisenberg result: ν̂'' = (−sin θ, 0, cos θ)
- **Key observation**: ν̂' and ν̂'' are in **different coordinate systems**

### 4. Complexity Theory Connection
- Standard definitions of P and NP
- Decision problems and languages
- **Gap identification**: Song's (P2) is not a decision problem

### 5. The Refutation
- Formal statement: The difference between ν̂' and ν̂'' does not establish P ≠ NP
- Proof: Show the "nondeterminism" is coordinate-dependent, not computational

## Related Work

### Similar Conceptual Errors

This attempt is reminiscent of other failed P vs NP proofs that:
1. Conflate different levels of description
2. Misapply physical intuition to computational complexity
3. Fail to engage with the standard definitions of P and NP

### Quantum Computing and Complexity

It's worth noting:
- Quantum computers provide speedups for certain problems (Shor, Grover)
- But BQP (quantum polynomial time) ≠ NP in general
- The relationship between quantum mechanics and NP is subtle
- This paper's approach doesn't align with standard quantum complexity theory

## Educational Value

This formalization demonstrates:

1. **Importance of definitions**: P and NP have precise mathematical definitions
2. **Representation independence**: Equivalent descriptions don't create complexity differences
3. **Physical vs computational**: Physical processes and computational problems are distinct
4. **Verification value**: Formal methods can expose conceptual errors clearly

## References

### Primary Source
- D. Song, "The P versus NP Problem in Quantum Physics," arXiv:1402.6970v1 [physics.gen-ph] (2014)

### Background
- R. Landauer, "Information is physical," Physics Today (1991)
- D. Deutsch, "Quantum theory, the Church-Turing principle and the universal quantum computer," Proc. R. Soc. London A 400, 97 (1985)
- S. Aaronson, "NP-complete problems and physical reality," arXiv:quant-ph/0502072 (2005)

### Related Refutations
- Woeginger's list: https://www.win.tue.nl/~wscor/woeginger/P-versus-NP.htm

## Files in This Directory

```
proofs/attempts/daegene-song-2014-pneqnp/
├── README.md                              # This file
├── coq/
│   └── DaegeneSong2014.v                 # Coq formalization
├── lean/
│   └── DaegeneSong2014.lean              # Lean 4 formalization
└── isabelle/
    └── DaegeneSong2014.thy               # Isabelle/HOL formalization
```

## Building

```bash
# Coq
coqc proofs/attempts/daegene-song-2014-pneqnp/coq/DaegeneSong2014.v

# Lean 4
lake build

# Isabelle/HOL
isabelle build -d . DaegeneSong2014
```

## Status

- ✅ Paper analyzed
- ✅ Errors identified
- ✅ Formalization structure planned
- 🚧 Coq formalization in progress
- 🚧 Lean formalization in progress
- 🚧 Isabelle formalization in progress

## License

This formalization is part of the p-vs-np repository and follows the repository's [LICENSE](../../../LICENSE).

---

**Navigation:** [↑ Back to Repository Root](../../../README.md) | [Issue #56](https://github.com/konard/p-vs-np/issues/56) | [Pull Request #338](https://github.com/konard/p-vs-np/pull/338)
