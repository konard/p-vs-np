# P vs NP Proof Experiments

This directory contains **experimental proof attempts** for actually solving the P vs NP problem, not just proving that it's decidable.

## ⚠️ Important Disclaimer

**These are PROOF ATTEMPTS, not actual proofs.** They demonstrate:
- Various strategies that have been tried to solve P vs NP
- Why these approaches are challenging
- What would be required for a complete proof
- Known barriers and limitations

All proof files compile successfully but contain incomplete proofs (marked with `sorry` in Lean, `Admitted` in Coq, and `oops` in Isabelle) because **we don't actually have a proof of P = NP or P ≠ NP**.

## Relationship to Decidability

### What We Proved in `p_vs_np_decidable/`
In the main decidability proofs, we showed that:
- **P vs NP is decidable** in classical logic: `(P = NP) ∨ (P ≠ NP)`
- The question MUST have an answer (even though we don't know which)
- There is no "third option" beyond P = NP and P ≠ NP

### What These Experiments Attempt
These experiments try to determine **which answer is correct**:
- Attempt to prove P = NP by constructing polynomial-time algorithms
- Attempt to prove P ≠ NP by showing fundamental impossibility
- Document known proof strategies and their limitations

**Key Insight**: Knowing that a question is decidable doesn't tell us how to decide it! The decidability proof uses classical logic's law of excluded middle, which is non-constructive.

## Proof Strategies Explored

### 1. Direct Construction Approach
**Goal**: Construct a polynomial-time algorithm for an NP-complete problem (e.g., SAT)

**Status**: INCOMPLETE
- Requires explicit algorithm construction
- Must prove correctness and polynomial running time
- If successful, would prove P = NP

**Challenge**: Finding such an algorithm is the core difficulty of the problem!

### 2. Diagonalization Approach
**Goal**: Use time hierarchy theorems to separate P from NP

**Status**: INCOMPLETE
- Requires proving that some NP language cannot be decided in polynomial time
- Must show impossibility for ALL polynomial-time algorithms
- If successful, would prove P ≠ NP

**Challenge**: Proving such a strong impossibility result is extremely difficult

### 3. Oracle Separation (Relativization)
**Goal**: Use oracle-enhanced Turing machines to separate P from NP

**Status**: KNOWN TO FAIL
- Baker-Gill-Solovay (1975) proved this approach cannot work
- There exist oracles A and B where P^A = NP^A but P^B ≠ NP^B
- This means any proof of P vs NP must be "non-relativizing"

**Barrier**: Relativization barrier

### 4. Circuit Complexity Approach
**Goal**: Prove exponential circuit lower bounds for NP-complete problems

**Status**: INCOMPLETE
- Requires proving that some NP problem needs exponential-size circuits
- This is one of the hardest open problems in complexity theory
- If successful, would prove P ≠ NP (since P ⊆ P/poly)

**Challenge**: Best known circuit lower bounds are far from what's needed

### 5. Algebraic Approach (GCT)
**Goal**: Use Geometric Complexity Theory to separate complexity classes

**Status**: INCOMPLETE
- Requires deep algebraic geometry and representation theory
- Active area of research (Mulmuley, Sohoni, et al.)
- Extremely technical and not yet formalized

**Challenge**: Even the conjectures in GCT are unproven

### 6. Natural Proofs Barrier
**Goal**: Use "natural" proof techniques

**Status**: KNOWN TO FAIL (under cryptographic assumptions)
- Razborov-Rudich (1997) showed that "natural" proof techniques cannot prove P ≠ NP
- Natural proofs are constructive and work for large classes of functions
- If one-way functions exist, natural proofs cannot separate P from NP

**Barrier**: Natural proofs barrier

## Known Barriers

Three major barriers to proving P vs NP:

### 1. Relativization (Baker-Gill-Solovay, 1975)
- Oracle-based proofs don't work
- Any proof must use non-relativizing techniques

### 2. Natural Proofs (Razborov-Rudich, 1997)
- "Natural" circuit lower bound techniques are blocked
- Assumes existence of cryptographically strong one-way functions

### 3. Algebrization (Aaronson-Wigderson, 2008)
- Extension of relativization to algebraic computation
- Rules out even more proof techniques

**Implication**: Any successful proof of P vs NP must avoid ALL three barriers!

## File Structure

```
proofs/experiments/
├── README.md (this file)
├── lean/
│   └── PvsNPProofAttempt.lean
├── coq/
│   └── PvsNPProofAttempt.v
└── isabelle/
    └── PvsNPProofAttempt.thy
```

Each file contains:
- Formal definitions of complexity classes (P, NP, NP-complete)
- Formalization of different proof strategies
- Documentation of why each strategy is challenging
- Incomplete proofs (with `sorry`/`Admitted`/`oops`) showing proof obligations

## What Would a Complete Proof Require?

### For P = NP:
1. An explicit polynomial-time algorithm for an NP-complete problem
2. Proof of correctness: algorithm solves the problem
3. Proof of efficiency: algorithm runs in polynomial time
4. Verification that this implies all NP problems are in P

### For P ≠ NP:
1. A specific NP-complete problem
2. Proof that it's truly NP-complete
3. Proof that NO polynomial-time algorithm exists for it
4. This requires proving a universal negative statement (very hard!)

## Why This is So Hard

1. **Proving positive results (P = NP)**:
   - Requires finding a clever algorithm
   - Possibly discoverable by insight or machine search
   - But no one has found such an algorithm in 50+ years

2. **Proving negative results (P ≠ NP)**:
   - Requires proving a universal impossibility
   - Must rule out ALL possible polynomial-time algorithms
   - Known barriers eliminate many proof techniques
   - Considered significantly harder than positive results

3. **Fundamental difficulty**:
   - The problem asks about the limits of efficient computation
   - It's asking "are there fundamentally hard problems?"
   - This is both a mathematical and philosophical question

## Educational Value

These experiments demonstrate:

1. **Difference between decidability and solvability**
   - We know the question HAS an answer (decidability)
   - We don't know WHAT the answer is (solvability)

2. **Proof barriers in complexity theory**
   - Not all proof strategies can work
   - Understanding barriers guides future research

3. **Formalization challenges**
   - Even expressing what a proof would require is non-trivial
   - Formal verification requires making intuitions precise

4. **Limits of current knowledge**
   - Using `sorry`/`Admitted`/`oops` honestly shows what we don't know
   - Transparency about incomplete proofs is scientifically valuable

## Verification

All files in this directory are verified by CI to ensure they:
- ✅ Type-check and compile successfully
- ✅ Correctly formalize the definitions
- ✅ Honestly mark incomplete proofs
- ✅ Don't claim to prove what we don't know

However, they do NOT prove P = NP or P ≠ NP!

## Conclusion

These experiments show that:
- The P vs NP question is **decidable** (has a definite answer)
- We can **formalize** what a proof would look like
- Multiple **barriers** prevent many natural approaches
- The problem remains **unsolved** despite decades of effort

The gap between decidability and actual decision is the essence of the millennium problem!

## References

- Baker, T., Gill, J., & Solovay, R. (1975). Relativizations of the P =? NP Question.
- Razborov, A. A., & Rudich, S. (1997). Natural Proofs.
- Aaronson, S., & Wigderson, A. (2008). Algebrization: A New Barrier in Complexity Theory.
- Cook, S. (1971). The Complexity of Theorem-Proving Procedures.
- Mulmuley, K., & Sohoni, M. (2001). Geometric Complexity Theory I.
