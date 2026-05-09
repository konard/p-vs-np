# Forward Proof Formalization: Kobayashi 2012

This directory contains the formal proof attempt following Kobayashi's approach as faithfully as possible.

## Contents

- `lean/KobayashiProof.lean` - Lean 4 formalization
- `rocq/KobayashiProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture the forward proof argument of Kobayashi (2012):

1. **Resolution Principle** (Theorems 3-6): Basic properties of binary resolution in propositional logic
2. **RCNF Definition** (Definition 9): Encoding resolution structure as a HornCNF formula
3. **RCNF P-Completeness** (Theorem 10): RCNF is equivalent to HornCNF in log-space
4. **TCNF Definition** (Definition 13): Triangular CNF structure T_PQR
5. **TCNF NP-Completeness** (Theorem 14): Polynomial reduction from 3CNF to TCNF
6. **TCNF Irreducibility** (Theorem 15): T_PQR cannot be factored as a product
7. **CCNF Definition** (Definition 16): Moore-graph-based combination of TCNFs
8. **Super-Polynomial RCNF** (Theorem 19): Some CNF formulas need super-polynomial RCNF
9. **Main Result** (Theorem 20): CNF ⊈_p RCNF, claimed to imply P ≠ NP

## The Attempted Proof Logic

Kobayashi's argument proceeds:

1. **Define RCNF** as the resolution-structure-encoding of a CNF formula (always a HornCNF)
2. **Show RCNF is P-complete** via log-space reduction from HornCNF
3. **Construct CCNF formulas** M_k using Moore graphs of diameter k
4. **Claim CCNF is irreducible** (cannot be compactly represented in RCNF)
5. **Conclude**: Since CNF cannot be reduced to RCNF polynomially, and RCNF is P-complete, P ≠ NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Kobayashi's argument fails or is insufficiently detailed:

1. **Theorem 15 (Irreducibility)**: The notion of "product irreducibility" is not precisely defined enough to formalize
2. **Theorem 17 (Chaotic MUC existence)**: The construction of M_k as a Chaotic MUC requires detailed combinatorial arguments not present in the paper
3. **Theorem 18 (Super-polynomial falsifying assignments)**: The claim that |[b[c]]| is super-polynomial is stated without proof
4. **Theorem 19 (Super-polynomial RCNF)**: This critical step — that CCNF requires super-polynomial RCNF — is asserted but not proven
5. **Theorem 20 (The gap)**: Even if Theorem 19 holds, concluding P ≠ NP requires an additional step that is never justified

## The Core Error

The fundamental issue (formalized in refutation/) is:

- **What Kobayashi shows**: CNF → RCNF representation requires super-polynomial size for some formulas
- **What P ≠ NP requires**: No polynomial-time algorithm exists to decide SAT

These are **different statements**. Representation size ≠ decision complexity.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Markdown conversion of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
