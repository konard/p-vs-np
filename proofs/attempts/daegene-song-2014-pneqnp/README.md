# Daegene Song (2014): P ≠ NP via Quantum Self-Reference

**Attempt ID**: 99 (Woeginger's List)
**Author**: Daegene Song
**Year**: 2014
**Claim**: P ≠ NP
**Paper**: [The P versus NP Problem in Quantum Physics](http://arxiv.org/abs/1402.6970)
**Status**: ❌ **Flawed** - Multiple fundamental errors identified

---

## Summary

In February 2014, Daegene Song claimed to establish P ≠ NP by examining computational complexity through the lens of physical processes. The main argument involves:

1. Interpreting P as a class of **deterministic** polynomial-time physical processes
2. Interpreting NP as a class of **nondeterministic** polynomial-time physical processes
3. Exhibiting a quantum mechanical self-reference phenomenon (called process **P2**) that supposedly belongs to NP but not P

The author argues that observing the evolution of a reference frame with respect to itself in quantum mechanics creates a nondeterministic process that cannot be computed deterministically.

---

## Main Argument

### Key Definitions

The paper defines two physical processes:

- **(P1)**: An observer observes the unitary evolution of a quantum state μ̂ with respect to a reference frame ν̂
- **(P2)**: An observer observes the unitary evolution of a reference frame ν̂ with respect to itself

### The Claimed Nondeterminism

For a qubit initially at ν̂ = (0, 0, 1), applying rotation Uθ about the y-axis by angle θ:

- **Schrödinger picture (δ₁)**: ν̂ → ν̂' = (sin θ, 0, cos θ)
- **Heisenberg picture (δ₂)**: ν̂ → ν̂'' = (-sin θ, 0, cos θ)

The author claims:
1. These two outcomes are different (unless θ = kπ)
2. This represents a nondeterministic computation in NP
3. No deterministic Turing machine can compute this because deterministic machines must yield the same result under both δ₁ and δ₂
4. Therefore, P2 ∈ NP \ P, which implies P ≠ NP

---

## Critical Errors in the Proof

### Error 1: Confusion Between Quantum Pictures

**The Flaw**: The Schrödinger and Heisenberg pictures are **mathematically equivalent representations** of the same physical process. They always yield identical observable predictions.

**Why This Matters**:
- In the Schrödinger picture: states evolve, observables are fixed
- In the Heisenberg picture: states are fixed, observables evolve
- **Physical predictions (expectation values, measurement probabilities) are always identical**

The paper's Eq. (4) and (5) show:
- δ₁: ν̂ → (sin θ, 0, cos θ)
- δ₂: ν̂ → (-sin θ, 0, cos θ)

But this is **meaningless** because:
- These are coordinate transformations in different representational schemes
- They don't represent different physical outcomes
- No measurement can distinguish between these "choices"

**Formal Refutation**: For any quantum state |ψ⟩ and observable Ô:
```
⟨ψ(0)|U†ÔU|ψ(0)⟩ = ⟨ψ(t)|Ô|ψ(t)⟩
```
where U is the time evolution operator. Both pictures yield identical expectation values for all observables.

### Error 2: Misunderstanding of Nondeterminism

**The Flaw**: The paper conflates **choice of mathematical representation** with **nondeterministic computation**.

**What NP Actually Means**: In complexity theory, nondeterministic polynomial time means:
- A problem can be **verified** in polynomial time given a certificate
- Or equivalently, a nondeterministic Turing machine can "guess" the right computation path

**Why the Paper Fails Here**:
- The "choice" between Schrödinger and Heisenberg pictures is not a computational choice
- It's a meta-level choice about how to mathematically describe the same physics
- This is like saying "French vs English descriptions of the same theorem represent nondeterministic computation"

### Error 3: No Actual Decision Problem

**The Flaw**: The paper never defines a proper **decision problem** (a mapping from inputs to YES/NO).

**What's Missing**:
- What is the input to the computation?
- What is the output (YES or NO)?
- What property is being decided?

**Why This Matters**: P and NP are classes of **decision problems**, not physical processes. To claim P ≠ NP, one must:
1. Define a specific decision problem
2. Prove it's in NP (polynomial-time verifiable)
3. Prove it's not in P (no polynomial-time algorithm exists)

The paper does none of this. Process P2 is not a decision problem at all.

### Error 4: Confusion About Physical Reality vs Computation

**The Flaw**: Even if the "self-reference" process were genuinely nondeterministic (which it isn't), this wouldn't prove P ≠ NP.

**Why**:
- Computational complexity is about **algorithms and Turing machines**
- Physical processes are implementations, not the fundamental objects of study
- Many physical processes have randomness (quantum measurement, thermal noise), but this doesn't resolve P vs NP
- The P vs NP question is about **deterministic computation time** vs **verification time**, not about physical determinism

### Error 5: The "Verification" Argument Fails

**The Flaw**: The paper claims (page 3) that the verification approach to NP "does not work" for process P2.

**Why This Is Wrong**:
- The author states: "there are not any deterministic machines that can compute paths (4) or (5)"
- But verification in NP doesn't require computing the solution, only **checking** a given certificate
- The argument is circular: the author assumes no deterministic machine can compute it, then uses this to argue it's in NP \ P

**Actual Situation**: If P2 could be formulated as a decision problem (which it can't), a deterministic machine could trivially "verify" any claimed outcome by computing the unitary evolution.

### Error 6: Misuse of Reference [26]

**The Flaw**: The paper relies heavily on reference [26] (Song, "Non-computability of consciousness", 2007), which itself contains similar conceptual errors.

**The Problem**:
- The 2007 paper confuses quantum mechanical descriptions with consciousness and computability
- Building the P vs NP argument on this foundation compounds the errors
- Neither paper provides rigorous definitions of the terms they use

---

## What This Attempt Gets Wrong About P vs NP

1. **P and NP are about algorithms, not physics**: While computation is implemented physically, the P vs NP question is about mathematical properties of algorithms and decision problems.

2. **Quantum mechanics doesn't change classical complexity classes**: BQP (bounded-error quantum polynomial time) is believed to be between P and NP, but quantum computers don't solve NP-complete problems efficiently.

3. **Different representations ≠ nondeterminism**: Mathematical equivalence of physical descriptions (Schrödinger vs Heisenberg) has nothing to do with nondeterministic computation.

4. **No decision problem is defined**: You can't prove something about complexity classes without defining what problem you're analyzing.

---

## Formalization Strategy

Our formalization in Coq, Lean, and Isabelle will:

1. **Define the necessary concepts**:
   - Nondeterministic Turing machines
   - The complexity classes P and NP
   - Decision problems
   - Quantum mechanical processes (simplified)

2. **Formalize the paper's claims**:
   - Process P1 and P2
   - The "nondeterminism" claim about Schrödinger vs Heisenberg pictures

3. **Prove the errors**:
   - Show that Schrödinger and Heisenberg pictures yield identical physical predictions
   - Show that no decision problem is defined
   - Show that the argument doesn't establish P ≠ NP

4. **Educational value**: Demonstrate common pitfalls in complexity theory proofs:
   - Confusing representation with reality
   - Mixing physical and computational concepts
   - Missing formal definitions

---

## Key Theorems to Formalize

### Theorem 1: Picture Equivalence
**Statement**: For any quantum state and observable, the Schrödinger and Heisenberg pictures yield identical expectation values.

**Formalization Goal**: Show that the "different outcomes" in Eq. (4) and (5) are merely coordinate artifacts, not physical differences.

### Theorem 2: No Decision Problem
**Statement**: Process P2 as described in the paper does not constitute a valid decision problem.

**Formalization Goal**: Show that P2 lacks the necessary structure (input, output, decidable property) to be a member of any complexity class.

### Theorem 3: Argument Invalidity
**Statement**: Even if P2 were nondeterministic (which it isn't), this doesn't establish P ≠ NP.

**Formalization Goal**: Show that the logical structure of the argument is invalid.

---

## References and Context

### The Paper
- **Song, D.** (2014). "The P versus NP Problem in Quantum Physics." arXiv:1402.6970 [physics.gen-ph]

### Related Work
- **Cook, S.** (1971). "The complexity of theorem-proving procedures." The foundational paper defining NP-completeness.
- **Aaronson, S.** (2005). "NP-complete problems and physical reality." arXiv:quant-ph/0502072. A rigorous examination of the relationship between physics and computational complexity.

### Why This Error Is Common
Many attempted P vs NP proofs make similar mistakes:
- Confusing computational models with physical implementation
- Misunderstanding what nondeterminism means in complexity theory
- Failing to define a proper decision problem
- Assuming quantum mechanics provides "free" nondeterminism

---

## Pedagogical Value

This formalization exercise demonstrates:

1. **Importance of precise definitions**: Without a clear decision problem, there's nothing to prove
2. **Distinction between representation and reality**: Mathematical descriptions must be distinguished from physical phenomena
3. **Complexity theory is mathematical, not physical**: While inspired by computation, P vs NP is a question about algorithms, not physics
4. **Common misconceptions about quantum mechanics**: Quantum "weirdness" doesn't automatically solve hard problems

---

## Status

- ✅ Paper analyzed
- ✅ Errors identified
- ✅ Formalization strategy planned
- 🚧 Coq formalization: In progress
- 🚧 Lean formalization: In progress
- 🚧 Isabelle formalization: In progress

---

## Navigation

- [Back to Repository Root](../../../README.md)
- [All Proof Attempts](../../attempts/)
- [P ≠ NP Framework](../../p_not_equal_np/README.md)

---

## License

This formalization and analysis are provided for educational and research purposes under the repository license.
