# Forward Proof Formalization: Mukherjee 2011

This directory contains the formal proof attempt following Mukherjee's claimed approach as faithfully as possible.

## Contents

- `lean/MukherjeeProof.lean` - Lean 4 formalization
- `rocq/MukherjeeProof.v` - Rocq (Coq) formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **3-SAT Problem Definition**: The formal statement of 3-SAT as an NP-complete decision problem
2. **Claimed Algorithm Structure**: The skeleton of a deterministic polynomial-time algorithm for 3-SAT
3. **Polynomial Time Claim**: The assertion that such an algorithm exists and runs in O(nᵏ) time
4. **Correctness Claim**: The assertion that the algorithm produces correct output on all inputs

## The Attempted Proof Logic

Mukherjee's argument (as understood from the abstract and Woeginger list entry) proceeds:

1. **3-SAT Formulation**: Express 3-SAT as a decision problem on CNF formulas with 3 literals per clause
2. **Algorithm Design**: Provide a deterministic algorithm that decides satisfiability
3. **Polynomial Bound**: Claim the algorithm's runtime is bounded by a polynomial in the input size
4. **Correctness Proof**: Claim the algorithm always returns the correct answer

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the critical gaps where the argument fails. These mark locations where:

1. **The Core Algorithm**: The paper was withdrawn, so the actual algorithm is unavailable. The formalization uses a placeholder that asserts polynomial solvability without proof.
2. **Correctness**: The claimed correctness of the algorithm cannot be established — if it were, P=NP would be proven.
3. **Complexity Analysis**: Even if an algorithm exists, proving it runs in polynomial time requires detailed analysis that was not made available.

## The Core Barrier

Any deterministic polynomial-time algorithm for 3-SAT must, on instances with n variables:
- Correctly decide satisfiability for all 2ⁿ possible truth assignments
- Do so without enumerating all assignments (which would be exponential)
- Exploit some structural property of 3-CNF formulas that enables polynomial-time decision

No such structural property is known to exist for general 3-SAT instances. The exponential lower bound (under P ≠ NP assumption) means:
- Any correct algorithm must implicitly search exponential space
- Polynomial-time algorithms exist only if P = NP (which is unproven and believed false)

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
