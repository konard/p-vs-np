# Forward Proof Formalization: Plotnikov 2011 P≠NP

This directory contains a formalization of Plotnikov's claimed P≠NP proof, following his argument as faithfully as possible.

## Contents

- `lean/PlotnikovPNEQNP.lean` - Lean 4 formalization
- `rocq/PlotnikovPNEQNP.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **The Hypothesis**: Assume a polynomial-time algorithm A for 3-Colorability exists
2. **Enumeration of Algorithms**: Fix an enumeration of all polynomial-time algorithms
3. **Diagonal Graph Construction**: For each algorithm A_i, construct H_i such that H_i is 3-colorable iff A_i rejects H_i
4. **The Contradiction**: A_j(H_j) gives the wrong answer in both cases
5. **Conclusion**: No polynomial-time algorithm for 3-COL exists, hence P≠NP

## The Attempted Proof Logic

Plotnikov's argument:

1. **Assume** ∃ polynomial-time algorithm A deciding 3-COL
2. **Enumerate** all polynomial-time algorithms: A_0, A_1, A_2, ...
3. **Construct** diagonal graph G* = H_j (where j is A's index) such that:
   - G* is 3-colorable ↔ A(G*) = 0 (A rejects G*)
4. **Case analysis**:
   - If A(G*) = 1: A says 3-colorable → by construction G* is not 3-colorable → contradiction with A's correctness
   - If A(G*) = 0: A says not 3-colorable → by construction G* is 3-colorable → contradiction with A's correctness
5. **Conclude**: A cannot exist, so 3-COL ∉ P, hence P ≠ NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where Plotnikov's argument fails:

1. **Circular Construction**: H_i is 3-colorable iff A_i(H_i) = 0. But to BUILD H_i, you must already know whether H_i is 3-colorable — which requires running A_i on H_i — which requires H_i to already exist. This is circular.

2. **Fixed-Point Problem**: The construction requires a graph that "knows" its own colorability, equivalent to a fixed-point in the colorability predicate. The existence of such a fixed-point is not established.

3. **Relativization Barrier**: The Baker-Gill-Solovay theorem shows that diagonalization arguments (relativization) cannot separate P from NP, because there exist oracles relative to which P=NP and others relative to which P≠NP.

4. **Non-Uniform Algorithms**: Even if the argument worked for deterministic Turing machines, it does not account for all possible computational models and their relationship to complexity classes.

## The Core Error

The diagonal construction:
> "H_i is 3-colorable if and only if A_i rejects H_i"

requires simultaneously:
- **Knowing** the 3-colorability of H_i (to define H_i)
- **Defining** H_i (to know its 3-colorability)

This circularity means H_i is not well-defined. The Halting Problem diagonalization avoids this because:
- The diagonal machine D(i) runs machine M_i on input i and does the opposite
- The input i (machine description) is defined independently of D's output on i
- No circularity arises

In Plotnikov's case:
- H_i must encode "what A_i says about H_i"
- But H_i is the input to A_i — so H_i must be defined before running A_i on it

This is fundamentally different from Turing's diagonalization.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
