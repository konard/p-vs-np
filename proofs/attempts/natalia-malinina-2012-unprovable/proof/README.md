# Forward Proof Formalization: Malinina 2012

This directory contains the formal proof attempt following Malinina's claimed argument as faithfully as possible.

## Contents

- `lean/MalininaProof.lean` - Lean 4 formalization
- `rocq/MalininaProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Malinina's three-step argument:

1. **Self-Referential Algorithm Construction**: The hypothetical algorithm A that "inverts" any claimed P-algorithm for NP problems
2. **The Claimed Contradiction**: That A both must and cannot exist as a polynomial-time algorithm (given P ≠ NP provable)
3. **The Gödelian Transfer**: Encoding the contradiction as an arithmetic statement to invoke incompleteness

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at critical gaps:

1. **Algorithm A Is Not Constructive**: The construction of A assumes finding a "distinguishing instance" for any polynomial-time machine, which cannot be done in polynomial time itself (circular)
2. **The Symmetry Claim Fails**: The argument does not apply symmetrically to proofs of P = NP
3. **Missing Arithmetic Encoding**: The Gödelian transfer requires formalizing P vs NP as an arithmetic statement with self-referential structure — not provided
4. **No Model Construction**: Independence requires models of ZFC where P = NP and where P ≠ NP — neither is constructed

## The Core Error

Malinina conflates two distinct notions:
- **Computational undecidability**: No algorithm can solve the halting problem
- **Proof-theoretic independence**: Some arithmetic statements are unprovable from ZFC

The diagonalization argument from Gödel's theorem requires a precisely formatted self-referential statement. "P vs NP" is not obviously of the right form without extensive formalization work that the paper does not provide.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt and error analysis
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstructed original proof text
- [`../refutation/README.md`](../refutation/README.md) - Why the proof fails
