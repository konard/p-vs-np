# Forward Proof Formalization: Peng Cui (2014)

This directory contains the formal proof attempt following Cui's approach as faithfully as possible.

## Contents

- `lean/CuiProof.lean` - Lean 4 formalization of Cui's claimed proof
- `rocq/CuiProof.v` - Rocq formalization of Cui's claimed proof

## What These Formalizations Capture

The formalizations attempt to capture Cui's claimed proof of P = NP:

1. **3-XOR Problem Definition**: The Max-3-Lin-2 constraint satisfaction problem
2. **Gap-3-XOR Problem**: The promise problem (YES: ≥ 1-ε fraction satisfiable; NO: ≤ 1/2+ε)
3. **NP-hardness of Gap-3-XOR**: Consequence of the PCP theorem and Hastad's inapproximability
4. **Charikar-Wirth SDP Algorithm**: Abstract formalization of the SDP approach
5. **Cui's Core Claim**: That running the SDP for 2 rounds solves Gap-3-XOR exactly
6. **The P=NP Conclusion**: The logical chain from solving an NP-hard problem in polynomial time

## The Attempted Proof Logic

Cui's argument proceeds:

1. **Construct disguised PCP verifier**: Use three truncated biased pairwise independent
   distributions to build a PCP verifier whose question distribution looks balanced
2. **Apply variance-style theorem**: Show optimal prover strategies must be dictator-like
3. **Run 2-round SDP**: Apply Charikar-Wirth SDP for 2 rounds to solve Gap-3-XOR exactly
4. **Conclude P=NP**: Since Gap-3-XOR is NP-hard but solvable in polynomial time, P = NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the
critical gaps where Cui's argument fails. These mark locations where:

1. **The core claim is unverifiable**: The claim that 2-round SDP solves Gap-3-XOR exactly
   is stated as an axiom — it cannot be proven because it is almost certainly false
2. **Composition of reductions**: Polynomial-time composability of reductions requires
   careful argument that is not provided in the paper
3. **Encoding details**: The precise encoding between binary strings and XOR instances
   is abstracted away via axioms

## The Core Error

The fundamental issue is in Step 3 of Cui's argument. The Charikar-Wirth SDP algorithm
provides an **approximation**, not an exact solution. Specifically:

- **What the SDP achieves:** Approximation ratio $\Omega(k/2^k \cdot \log k)$ for Max-k-CSP
- **What is claimed:** Exact solution (distinguishing YES from NO instances of Gap-3-XOR)
- **The gap:** No known polynomial-time algorithm can exactly solve Gap-3-XOR; doing so
  would contradict the PCP theorem (assuming P ≠ NP)

The paper's argument about "disguising" and "variance-style theorems" does not bridge this gap.
These are standard tools in hardness of approximation proofs, but they establish hardness
(NP-hardness of approximation), not algorithmic upper bounds.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Markdown reconstruction of the paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
