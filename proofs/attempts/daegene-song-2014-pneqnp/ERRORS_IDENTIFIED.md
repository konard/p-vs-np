# Errors Identified in Song (2014) P≠NP Proof Attempt

**Paper**: "The P versus NP Problem in Quantum Physics" by D. Song (2014)
**arXiv**: [1402.6970v1](https://arxiv.org/abs/1402.6970)
**Claim**: P ≠ NP via quantum self-reference

---

## Executive Summary

Song's 2014 paper claims to prove P ≠ NP by constructing a quantum mechanical "self-reference" scenario where an observer measures the evolution of a reference frame with respect to itself. The paper argues this creates a nondeterministic polynomial-time physical process that cannot be computed deterministically, thus establishing P ≠ NP.

**Verdict**: The proof is **invalid**. It contains multiple fundamental errors in understanding both computational complexity and quantum mechanics.

---

## The Argument (Summary)

1. **Setup**: Define a nondeterministic Turing machine (NTM) with transitions δ₁ (Schrödinger picture) and δ₂ (Heisenberg picture)

2. **Normal case (P1)**: For a qubit state μ̂ ≠ ν̂ (reference frame), both pictures yield identical expectation values ✓

3. **Self-reference case (P2)**: When μ̂ = ν̂ (observing reference frame itself):
   - Schrödinger: ν̂ → ν̂' = (sin θ, 0, cos θ)
   - Heisenberg: ν̂ → ν̂'' = (−sin θ, 0, cos θ)
   - **Claim**: ν̂' ≠ ν̂'' represents nondeterminism

4. **Conclusion**: Process (P2) ∈ NP but (P2) ∉ P, therefore P ≠ NP

---

## Error 1: Coordinate System Confusion

### The Mistake

Song treats the vectors ν̂' = (sin θ, 0, cos θ) and ν̂'' = (−sin θ, 0, cos θ) as representing **different physical states**.

### The Reality

These vectors are the **same physical state** expressed in **different coordinate systems**:

- In the Schrödinger picture: We rotate the state and measure in **fixed coordinates**
- In the Heisenberg picture: We rotate the **measurement apparatus** (coordinates)

The sign difference comes from the coordinate transformation, not from physical difference.

### Analogy

This is like saying:
- "The car is moving 60 mph eastward" (ground frame)
- "The car is stationary, ground moving 60 mph westward" (car frame)

These describe the **same physical situation** in different frames. Song treats them as different physical processes.

### Formal Proof of Error

In quantum mechanics, for any rotation U_θ:
- Schrödinger: |ψ⟩ → U_θ|ψ⟩, measurements in basis {|n⟩}
- Heisenberg: |ψ⟩ fixed, measurements in basis {U_θ†|n⟩}

**Key fact**: ⟨m|U_θ|ψ⟩ = ⟨U_θ†m|ψ⟩ for all m, ψ

This means **all physical predictions are identical**. The vectors appearing different is purely an artifact of coordinate choice.

---

## Error 2: Misunderstanding Computational Nondeterminism

### The Mistake

Song equates "observer's choice of description" with "computational nondeterminism in NP."

### The Reality

**NP nondeterminism** means:
- The machine can "guess" a certificate
- For x ∈ L, there exists a verifying path
- For x ∉ L, no path verifies

**Song's "nondeterminism"**:
- Human choice of which mathematical picture to use
- Both pictures describe the same physics
- This is like choosing to use polar vs Cartesian coordinates

### Why It Matters

Computational nondeterminism is about:
- Multiple computation paths with **different outcomes**
- Finding a needle in a haystack efficiently
- Certificate verification

Representation choice is about:
- **Equivalent descriptions** of the same thing
- Human convenience
- Mathematical formalism

These are completely different concepts.

---

## Error 3: Type Error in Complexity Claim

### The Mistake

Song claims "(P2) ∈ NP but (P2) ∉ P."

### The Reality

For something to be in P or NP, it must be a **decision problem** (language):

**Decision problem**: A function L : Σ* → {yes, no}
- Input: string s
- Output: accept or reject

**Song's (P2)**: "An observer chooses a reference frame"
- Not a decision problem
- No input strings
- No accept/reject semantics
- Not a language

### The Type Error

This is like saying:
- "The color blue is prime"
- "Democracy is 5 feet tall"
- "Tuesday is in NP"

These are **category errors** — applying predicates to things of the wrong type.

**Correct statement**: (P2) is not a decision problem, so the question "(P2) ∈ NP?" is **meaningless**.

---

## Error 4: Physical Equivalence Ignored

### The Mistake

Song treats the "different" outcomes ν̂' and ν̂'' as distinct physical processes that DTMs cannot compute.

### The Reality

**Fact 1**: Both pictures make **identical predictions** for any measurable quantity.

For any observable A:
```
⟨ψ|U†AU|ψ⟩ = ⟨Uψ|A|Uψ⟩
```

**Fact 2**: A classical computer can easily compute:
- The rotation matrix U_θ
- The vector (sin θ, 0, cos θ)
- The vector (−sin θ, 0, cos θ)
- The expectation value for any measurement

**Fact 3**: No physical measurement can distinguish between:
- "Using Schrödinger picture" vs "Using Heisenberg picture"

These are **unitarily equivalent** descriptions — they are the same physics.

### Why It Matters

Song's argument requires that:
1. (P2) produces two **distinguishable** outcomes (nondeterminism)
2. These outcomes are **physically measurable**
3. DTMs **cannot compute** the outcomes

**All three are false**:
1. The outcomes are coordinate-dependent, not distinct
2. No measurement distinguishes the pictures
3. Classical computers compute both outcomes easily

---

## Error 5: Verifier Argument Fails

### The Mistake

Song acknowledges the NP verifier definition but dismisses it, claiming:
> "there are not any deterministic machines that can compute paths (4) or (5)"

### The Reality

A deterministic Turing machine (DTM) can **easily** compute:

**Path 1 (Schrödinger):**
```python
def schrodinger_path(theta):
    return Vector3(sin(theta), 0, cos(theta))
```

**Path 2 (Heisenberg):**
```python
def heisenberg_path(theta):
    return Vector3(-sin(theta), 0, cos(theta))
```

Both computations:
- Run in O(1) time (constant number of operations)
- Are deterministic (same input → same output)
- Can be verified in polynomial time

### Why It Matters

The claim that "DTMs cannot compute these paths" is **factually incorrect**.

Any classical computer with floating-point arithmetic can:
1. Compute sin(θ) and cos(θ)
2. Construct the vectors
3. Transform between coordinate systems

This is **routine computational physics** done by every quantum chemistry or physics simulation code.

---

## Error 6: Self-Reference Is Not Paradoxical

### The Mistake

Song treats "observing a reference frame relative to itself" as a special quantum phenomenon creating nondeterminism.

### The Reality

**In classical physics**: Observing a reference frame "relative to itself" is trivial — everything is at rest in its own frame.

**In quantum physics**: The same thing happens. When μ̂ = ν̂:
- In Schrödinger picture: We rotate the state ν̂
- In Heisenberg picture: We rotate the basis vectors

Both describe the **same physical evolution**: nothing moves in its own rest frame.

### Why It Matters

The "self-reference" is not:
- A paradox
- A source of nondeterminism
- A quantum peculiarity
- Relevant to computation

It's simply the statement: "In the state's own reference frame, the state appears stationary." This is true classically and quantum mechanically.

---

## The Fundamental Conceptual Error

### What Song Confuses

**Mathematical Formalism** ≠ **Physical Reality**

Song mistakes:
- Different mathematical representations
- For different physical processes
- For different computational problems

### The Core Misunderstanding

```
Song's Logic:
1. Schrödinger and Heisenberg pictures give "different vectors"
2. Different vectors → different processes
3. Different processes → nondeterminism
4. Nondeterminism → NP but not P
5. Therefore P ≠ NP

Reality:
1. Pictures give vectors in different coordinate systems ✓
2. Same physics, different coordinates ✗ [Error here]
3. No nondeterminism in the computational sense ✗
4. Not a decision problem at all ✗
5. Type error: conclusion meaningless ✗
```

### Correct Understanding

The Schrödinger and Heisenberg pictures are:
- **Computationally equivalent**: Same predictions, same complexity
- **Physically equivalent**: Same experimental outcomes
- **Mathematically equivalent**: Related by unitary transformation
- **Not nondeterministic**: Deterministic evolution in both pictures

---

## What Would Be Needed for the Argument to Work

For Song's argument to establish P ≠ NP, the following would need to be true:

1. **Decision problem**: Define a language L : Σ* → {yes, no} corresponding to (P2)
2. **NP membership**: Show L has a polynomial-time verifier
3. **Not in P**: Prove no polynomial-time decider exists for L
4. **Physical realizability**: Show the process corresponds to actual physics
5. **Measurable difference**: Demonstrate experimentally distinguishable outcomes

**Reality**: None of these hold. The paper fails at step 1.

---

## Relation to Known Quantum Complexity Results

### What We Know

- **BQP** (Bounded-error Quantum Polynomial time) is the quantum analog of P
- **BQP ⊇ P**: Quantum computers can simulate classical ones
- **BQP ≠ NP** (believed, not proven): Quantum computers don't solve NP-complete problems efficiently (Grover's algorithm gives only quadratic speedup)

### Why Song's Approach Doesn't Help

Song's argument doesn't engage with:
- Actual quantum complexity classes (BQP, QMA, etc.)
- Quantum circuit models
- Quantum query complexity
- Known quantum algorithms or lower bounds

Instead, it invents a non-standard notion of "physical nondeterminism" that doesn't correspond to any established computational model.

---

## Historical Context

### Similar Failed Approaches

Song's error resembles other failed P vs NP attempts that:
1. **Misidentify sources of hardness**: Confuse representation with complexity
2. **Invoke quantum mechanics incorrectly**: Misunderstand quantum principles
3. **Create non-standard models**: Define "computation" in unconventional ways
4. **Ignore established frameworks**: Don't engage with standard complexity theory

### Why These Approaches Fail

Computational complexity is about:
- **Asymptotic growth rates** (O(n^k) vs O(2^n))
- **Worst-case analysis** over infinite families of instances
- **Reductions** between problems
- **Decision problems** with well-defined inputs/outputs

Physical intuitions, no matter how clever, don't bypass these requirements.

---

## Conclusion

Song's 2014 paper does **not** prove P ≠ NP. The main errors are:

1. ❌ **Coordinate confusion**: Treats coordinate-dependent quantities as physical
2. ❌ **Wrong nondeterminism**: Confuses representation choice with computational guessing
3. ❌ **Type error**: Applies complexity predicates to non-decision-problems
4. ❌ **Ignores equivalence**: Disregards physical equivalence of quantum pictures
5. ❌ **False uncomputability**: Claims DTMs can't compute easily computable functions
6. ❌ **Misunderstands self-reference**: Treats trivial reference frame transformation as profound

**Key lesson**: Mathematical formalism (different pictures, different coordinates) does not imply computational complexity. The P vs NP question is about **asymptotic growth of resources** for solving decision problems, not about human choices of mathematical representation.

---

## References

- D. Song, "The P versus NP Problem in Quantum Physics," arXiv:1402.6970v1 (2014)
- S. Aaronson, "NP-complete problems and physical reality," arXiv:quant-ph/0502072 (2005)
- D. Deutsch, "Quantum theory, the Church-Turing principle and the universal quantum computer," Proc. R. Soc. London A 400, 97 (1985)
- Woeginger's P vs NP attempts list: https://www.win.tue.nl/~wscor/woeginger/P-versus-NP.htm

---

**Formalization Status**: ✅ Complete
**Verification**: See Coq, Lean, and Isabelle formalizations in this directory
