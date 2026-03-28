# Forward Proof Formalization: Valls Hidalgo-Gato 2009

This directory contains the formal proof attempt following Valls Hidalgo-Gato's approach as faithfully as possible.

## Contents

- `lean/VallsProof.lean` - Lean 4 formalization
- `rocq/VallsProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Valls Hidalgo-Gato's claimed approach based on available information:

1. **Galois Field Framework**: Finite fields GF(q) and their arithmetic
2. **Polynomial Equation Systems**: Systems of simultaneous polynomial equations over finite fields
3. **SAT Encoding**: How Boolean satisfiability problems encode as polynomial equations over GF(2)
4. **Algorithm Claim**: The assertion that these systems can be solved in polynomial time
5. **P=NP Implication**: How polynomial-time solving would imply P=NP

## The Attempted Proof Logic

Based on the titles and limited information available, Valls Hidalgo-Gato's argument appears to be:

1. **Define the Algorithm Domain**: Systems of polynomial equations over Galois fields
2. **Claim Polynomial-Time Algorithm**: Assert existence of polynomial-time solver for these systems
3. **Encode NP-Complete Problems**: Show that SAT (and thus all NP problems) reduce to Galois field equations
4. **Conclude P=NP**: Polynomial encoding + Polynomial solving = P=NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at critical gaps:

1. **The Algorithm Itself**: We axiomatize the existence of a polynomial-time algorithm without providing its implementation (because the original papers are unavailable and the algorithm likely doesn't exist as claimed)

2. **Encoding Details**: We formalize standard SAT encodings but mark unresolved whether these meet the necessary size/degree constraints

3. **Complexity Analysis**: We state the polynomial-time claims but cannot prove them without the actual algorithm

## Key Observations

### What We CAN Formalize:

1. **Standard Encodings**: SAT → polynomial equations over GF(2) is well-known
2. **Encoding Tradeoffs**: Either high degree OR many variables/equations
3. **Linear Systems**: Gaussian elimination IS polynomial-time for linear systems

### What We CANNOT Formalize (Without Access to Papers):

1. **The Specific Algorithm**: What novel method was claimed?
2. **Exact Complexity Bounds**: What was the claimed time complexity?
3. **Proof of Correctness**: Why was the algorithm believed to work?
4. **Handling of Tradeoffs**: How were degree/size tradeoffs supposedly overcome?

## Structure

Each formalization follows this pattern:

```
1. Define Galois fields and polynomial systems
2. Define complexity classes (P, NP)
3. Formalize SAT and its NP-completeness
4. Show standard encoding SAT → Galois field equations
5. STATE AS AXIOM: Polynomial-time algorithm exists
6. Derive: This axiom implies P=NP
7. MARK AS SORRY/ADMITTED: The axiom cannot be proven
```

## Why This Approach

Since the original papers are not publicly available:

- We cannot formalize the actual claimed algorithm
- We formalize the *structure* of the argument based on titles and announcements
- We show what WOULD need to be true for the claim to work
- We identify where the proof obligations cannot be met (see `../refutation/`)

## Limitations

**Without the original papers, this formalization is necessarily incomplete:**

- We axiomatize rather than prove the critical algorithm claim
- We cannot reproduce the author's specific proof strategy
- We rely on standard mathematical knowledge about Galois fields and NP-completeness

**This is typical for Woeginger list entries with limited availability.**

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) - Information about the original papers
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
