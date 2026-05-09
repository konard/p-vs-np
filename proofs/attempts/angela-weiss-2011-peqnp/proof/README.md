# Forward Proof Formalization: Weiss 2011

This directory contains the formal proof attempt following Weiss's approach as faithfully
as possible.

## Contents

- `lean/WeissProof.lean` - Lean 4 formalization
- `rocq/WeissProof.v` - Rocq (Coq) formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **3-SAT Definition**: The formal structure of 3-SAT instances (variables, clauses, literals)
2. **KE-Tableau System**: The tableau rules including α-rules, β-rules, and the KE cut rule
3. **Branch Concepts**: Open branches (satisfying assignments) and closed branches
   (contradictions)
4. **Macro Construction**: Weiss's claimed polynomial macro for encoding all closed branches
5. **Polynomial-Time Claim**: The asserted O(nᵏ) complexity of the algorithm

## The Attempted Proof Logic

Weiss's argument proceeds:

1. **3-SAT Setup**: Given φ = C₁ ∧ ... ∧ Cₘ with n variables and m clauses
2. **Tableau Construction**: Apply KE-tableau rules to ¬φ
3. **Macro Building**: Construct a polynomial-size "macro" encoding all closed branches
4. **Evaluation**: Evaluate macro to determine satisfiability in polynomial time
5. **Conclusion**: Since 3-SAT ∈ P and 3-SAT is NP-complete, P = NP

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at the
critical gaps where Weiss's argument fails. These mark locations where:

1. **Macro Size Claim**: The claim that the macro has polynomial size is stated as an axiom
   (it is unproven and almost certainly false for worst-case instances)
2. **Macro Construction Time**: The polynomial construction time is asserted but not
   demonstrated — the construction would require traversing exponentially many branches
3. **Correctness of Compression**: That the macro correctly captures all open/closed branch
   information is assumed but not established
4. **Polynomial Evaluation**: That evaluating the macro takes polynomial time is assumed

## The Core Error

The tableau for an n-variable 3-SAT formula can have up to 2ⁿ branches:
- Each variable can be assigned T or F
- In the worst case, all 2ⁿ assignments must be examined
- KE cuts allow splitting on any formula, but do not reduce the number of cases
  that must be considered for the full satisfiability decision

The "macro" claimed to compress this structure must either:
- Contain exponential information (contradicting polynomial size), or
- Fail to correctly decide satisfiability in all cases

No polynomial-size data structure can encode the satisfiability of arbitrary 3-SAT
formulas (unless P = NP), as this would itself be a polynomial-time algorithm.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
