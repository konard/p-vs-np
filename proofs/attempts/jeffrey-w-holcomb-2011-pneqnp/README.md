# Jeffrey W. Holcomb (2011) - P≠NP Proof Attempt

**Attempt ID**: 83
**Author**: Jeffrey W. Holcomb
**Year**: 2011
**Claim**: P ≠ NP
**Status**: ❌ Not accepted by the research community

## Overview

In fall 2011, Jeffrey W. Holcomb published a sequence of papers claiming to establish P ≠ NP.
The proof was hosted at http://www.holcombtechnologies.com (currently unavailable). According to
[Woeginger's P versus NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), the proof
"relies upon the existence of stochastic answers in the set difference between NP and P."

The key paper in the sequence was titled **"Just How Random Are Your Answers?"**

## Main Argument

The proof approach centers on:

1. **Stochastic Answers**: The claim that problems in NP \ P have fundamentally "stochastic"
   or probabilistic characteristics in their solution space
2. **Set Difference Analysis**: Analyzing the difference between NP and P to find properties
   that distinguish them
3. **Claimed Characterization**: Problems in NP \ P have stochastic answers; problems in P
   do not; therefore P ≠ NP

### Claimed Proof Strategy

The proof argues:
- Problems in P have deterministic, efficiently computable answers
- Problems in NP that are not in P must have some form of "stochastic" characteristic
- This stochastic nature provides a separation between the classes

## Error Explanation

The proof fails fundamentally because **"stochastic answer" is never formally defined**. This
is not a minor gap — the entire proof structure depends on this concept. Without a formal
definition, the proof cannot be verified or refuted, and the claimed properties cannot be
established.

### Primary Error: Undefined Key Concept

The central concept of "stochastic answer" is left informal throughout the proof. A valid
proof of P ≠ NP using any property would require:

1. A **mathematically precise definition** of the property that:
   - Applies to decision problems (which have YES/NO answers, not distributions)
   - Is well-defined for all instances
   - Is preserved under polynomial-time reductions
2. A **proof that all P problems lack this property**
3. A **proof that some NP-complete problem has this property**

None of these are provided.

### Error 1: Decision Problems Have Deterministic Answers

Decision problems (as used in complexity theory) have **deterministic** YES/NO answers.
Given an instance x:

- x ∈ L or x ∉ L — there is no middle ground
- The answer is not a probability or distribution
- The answer is the same regardless of how we compute it

Even NP-complete problems like SAT have definite answers: a formula is either satisfiable
or it is not. There is no "stochastic" character in the answer itself.

### Error 2: Confusing Non-Determinism with Randomness

The "non-determinism" in NP refers to **existential quantification** (∃), not randomness:

```
x ∈ L  ⟺  ∃w. |w| ≤ poly(|x|) ∧ V(x, w) = 1
```

This means "there exists a witness" — it is a statement about the existence of a certificate,
not about probabilistic computation or stochastic answers.

**Common Misconception**: "Non-deterministic" in "non-deterministic Turing machine" does NOT
mean "random." It means the machine can existentially choose the right path.

### Error 3: Randomness in Algorithms ≠ Randomness in Answers

Even if one could define a notion of "stochastic answer":

- **BPP** (Bounded-Error Probabilistic Polynomial time) captures problems solvable with
  randomized algorithms in polynomial time
- **P ⊆ BPP** (trivially, since randomized algorithms include deterministic ones)
- **BPP is believed to equal P** (derandomization conjecture)
- **NP** is orthogonal to BPP — there are problems believed in NP \ BPP

So even randomness in *algorithms* does not separate P from NP in the way claimed.

### Error 4: No Reduction Preservation

For a property to be useful in a P vs NP proof, it must be preserved under polynomial-time
reductions. If problem A reduces to problem B in polynomial time, and B has the claimed
property, does A also have it? This is essential because NP-completeness relies entirely on
such reductions. The Holcomb proof provides no such preservation argument.

### Error 5: Relativization Barrier

Any argument based on "properties of the problem's answer" is likely to relativize — that is,
it would work equally well in oracle worlds where P ≠ NP and in worlds where P = NP
(depending on the oracle). By the Baker-Gill-Solovay theorem (1975), any proof that
relativizes cannot resolve P vs NP.

## Critical Analysis

### Likely Errors and Gaps

#### 1. Confusion Between Different Complexity Classes
- **BPP**: Problems solvable in polynomial time with randomized algorithms
- **P**: Problems solvable in polynomial time deterministically
- **NP**: Problems verifiable in polynomial time (deterministically)
- **RP, ZPP, etc.**: Various probabilistic complexity classes

**Common Error**: Confusing randomness in *algorithms* with randomness in *problem structure*.
NP is defined using deterministic verification, not probabilistic methods.

#### 2. Misunderstanding of Non-Determinism
**NP Definition**: A language L is in NP if there exists a polynomial-time deterministic
verifier V such that:
```
x ∈ L  ⟺  ∃w. |w| ≤ poly(|x|) ∧ V(x, w) accepts
```
The "non-determinism" refers to *existential quantification* over certificates, not randomness.

#### 3. Lack of Formal Definition
**Critical Gap**: What exactly is a "stochastic answer"? Without a formal mathematical
definition that applies to decision problems and is invariant under polynomial-time reductions,
the concept cannot be used in a rigorous proof.

#### 4. Relativization Barrier
**Known Barrier**: Arguments that relativize cannot separate P from NP due to the
Baker-Gill-Solovay result (1975). Arguments based on "randomness" of answers likely relativize.

#### 5. Confusing Average-Case and Worst-Case Complexity
**P and NP Definition**: Both are worst-case complexity classes. Using properties of "typical"
or "random" instances rather than worst-case analysis is not valid.

## Formalization Approach

This directory contains formalizations in Lean and Rocq that:

1. **Formalize the proof structure**: Capture what the proof would look like if "stochastic
   answers" were defined
2. **Identify the gap**: Show where the proof requires formal definitions that are not provided
3. **Demonstrate the error**: Illustrate why informal notions of "randomness" don't suffice for
   a P vs NP separation

### What We Formalize

Since the original proof is not accessible and lacks formal rigor, we formalize:

1. **Basic Definitions**: P, NP, polynomial-time reductions
2. **Attempted Definition**: Several possible interpretations of "stochastic answer"
3. **The claimed theorem structure**: How the proof would work IF the key concept were defined
4. **Gap Analysis**: Show that none of the interpretations yield a valid separation proof
5. **Refutation**: Show that at least one interpretation (uniform random answers) cannot separate P from NP

## File Structure

```
proofs/attempts/jeffrey-w-holcomb-2011-pneqnp/
├── README.md          (this file)
├── ORIGINAL.md        (reconstructed description of the proof)
├── proof/
│   ├── README.md      (explanation of proof formalization)
│   ├── lean/
│   │   └── HolcombProof.lean
│   └── rocq/
│       └── HolcombProof.v
└── refutation/
    ├── README.md      (explanation of refutation)
    ├── lean/
    │   └── HolcombRefutation.lean
    └── rocq/
        └── HolcombRefutation.v
```

## Key Insights

### What Would Be Needed for a Valid Proof

To separate P from NP using any property (including "randomness"), one would need:

1. **Formal Definition**: A mathematically precise property that:
   - Can be defined for decision problems
   - Is well-defined for all instances
   - Is preserved under polynomial-time reductions

2. **Proof that P lacks the property**: Show all problems in P do not have this property

3. **Proof that some NP problem has the property**: Show at least one NP-complete problem
   has this property

4. **Avoiding barriers**: The proof must avoid:
   - Relativization (work in oracle worlds)
   - Natural proofs barrier (if using circuit lower bounds)
   - Algebrization barrier (algebraic oracle access)

### Common Pitfall Illustrated

```
❌ Informal reasoning: "NP problems seem harder/more random than P problems"
✓ What's needed: Formal mathematical property + rigorous proof
```

## References

1. **Woeginger's List**: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm (Entry #83)
2. **Baker-Gill-Solovay (1975)**: "Relativizations of the P =? NP Question"
3. **Razborov-Rudich (1997)**: "Natural Proofs" - on barriers to circuit lower bounds
4. **Arora-Barak**: "Computational Complexity: A Modern Approach"

## Source Attribution

- Listed on Woeginger's P versus NP page (maintained until 2016)
- Information provided by Peter Bro Miltersen
- Original papers were at http://www.holcombtechnologies.com (no longer accessible)

## Status

**Not Peer Reviewed**: This proof attempt does not appear in peer-reviewed literature.

**Educational Purpose**: This formalization serves to:
- Document a historical proof attempt
- Illustrate common errors in P vs NP proof attempts
- Teach proper formal methods in complexity theory
- Demonstrate the gap between informal arguments and rigorous proofs

---

**Part of**: Issue #484 - Complete formalization for attempt #83
**Parent Issue**: #44 - Test all P vs NP attempts formally
**Repository**: https://github.com/konard/p-vs-np
