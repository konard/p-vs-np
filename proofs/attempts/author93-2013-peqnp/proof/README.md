# Forward Proof Formalization: Maknickas 2013

This directory contains the formal proof attempt following Maknickas's approach
as faithfully as possible.

## Contents

- `lean/MaknickasProof.lean` - Lean 4 formalization
- `rocq/MaknickasProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture Maknickas's claimed steps:

1. **Encoding Boolean variables as real variables** in [0, 1]
2. **Encoding each clause as an LP constraint**: for each clause (l_1 ∨ ... ∨ l_k),
   require sum of literal encodings ≥ 1
3. **Solving the LP** in polynomial time using standard LP algorithms
4. **Claiming the solution corresponds to a satisfying boolean assignment**

## The Attempted Proof Logic

Maknickas's argument proceeds:

1. **Encode SAT → LP**: Each boolean variable x_i becomes a real variable in [0, 1].
   Each clause becomes a linear inequality constraint.
2. **Solve in polynomial time**: Standard LP algorithms (interior point methods)
   run in polynomial time.
3. **Extract boolean solution**: The LP solution gives a valid SAT assignment.
4. **Conclusion**: SAT ∈ P, therefore P = NP.

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the
critical gap where Maknickas's argument fails:

- **The LP/ILP gap**: The claim that LP solutions over [0, 1] always yield valid
  boolean (0 or 1) solutions is unproven and false in general.
- **Fractional solutions**: LP relaxations of SAT often have fractional optimal
  solutions that do not correspond to valid boolean assignments.
- **Integer requirement**: Enforcing 0/1 solutions makes the problem ILP, which
  is NP-complete.

## See Also

- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstruction of the original paper
- [`../README.md`](../README.md) - Overview of the attempt
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
