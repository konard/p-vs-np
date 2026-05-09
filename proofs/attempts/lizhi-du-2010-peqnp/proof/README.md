# Forward Proof Formalization: Du (2010)

This directory contains the formal proof attempt following Du's approach as faithfully as possible.

## Contents

- `lean/DuProof.lean` - Lean 4 formalization
- `rocq/DuProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **The 3SAT Setting**: Formulas, clauses, literals, assignments, satisfiability
2. **Checking Trees**: Du's tree structure for representing formula dependencies
3. **Useful Units**: The set of forced literals under an assumption
4. **Contradiction Pairs**: Pairs of literals that cannot simultaneously be true
5. **Algorithm 1**: Du's claimed polynomial-time 3SAT decision algorithm
6. **Step 3 Intersection**: The critical (flawed) intersection operation on useful units
7. **The P=NP Claim**: How a correct Algorithm 1 would imply P = NP

## The Attempted Proof Logic

Du's argument proceeds:

1. **Build Checking Tree**: For the 3-CNF formula φ, build a checking tree T encoding the
   unit propagation structure of the formula.
2. **Compute Useful Units**: For each literal x in T, compute U(x) = the literals that
   are forced when x is assigned true.
3. **Apply Step 3**: For all non-contradiction pairs (x, y) in distinct 3-unit layers,
   replace U(x) and U(y) with U(x) ∩ U(y).
4. **Check Emptiness**: If any U(z) = ∅, return UNSAT; otherwise return SAT.
5. **Polynomial Time**: The algorithm runs in O(n³) time.
6. **Conclude P = NP**: Since 3SAT is NP-complete and Algorithm 1 solves it in polynomial
   time, P = NP.

## Where the Formalizations Stop

The formalizations use `sorry` (Lean) and `Admitted` (Rocq) placeholders at:

1. **Correctness of Step 3**: The claim that the intersection preserves all valid
   satisfying assignments is stated as an axiom (it cannot be proven — it is false).
2. **Counter-Example Construction**: The formalization includes the He et al.
   counter-example showing Algorithm 1 fails.
3. **Algorithm Building Blocks**: The checking tree construction and useful unit
   computation are axiomatized (their internal details are complex but not the source
   of the main error).

## The Core Error

The flaw is in Step 3's intersection operation:

**What Step 3 assumes:**
For non-contradiction pairs (x, y), valid solutions must use assignments
that are **common** to both U(x) and U(y).

**Why this is wrong:**
A satisfying assignment may make x true (using U(x)) or make y true (using U(y)) —
it does not need to be in both. The overall satisfiability of φ allows for
independent solution branches. Taking the intersection eliminates valid branches
that do not overlap.

**Formal statement of the error:**
```
∃ φ (satisfiable), ∃ x y (non-contradiction pair, in distinct 3-unit layers),
  U(x) ∩ U(y) = ∅  BUT  φ is satisfiable
```

## See Also

- [`../README.md`](../README.md) — Overview of the attempt
- [`../ORIGINAL.md`](../ORIGINAL.md) — Reconstruction of Du's original paper
- [`../refutation/README.md`](../refutation/README.md) — Why the proof fails
