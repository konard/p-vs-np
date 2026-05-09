# Forward Proof Formalization: Liao 2011

This directory contains formal proof attempt following Liao's approach as faithfully as possible.

## Contents

- `lean/LiaoProof.lean` - Lean 4 formalization
- `rocq/LiaoProof.v` - Rocq formalization

## What These Formalizations Capture

The formalizations attempt to capture:

1. **3SAT_N definition**: Normal 3-CNF expressions (no tautological clauses, no repeated clauses, full clauses)
2. **Classification Theorem**: Every 3SAT_N instance either satisfies (3,s)-SAT_N for s ≤ 3 (easy) or reduces to (3,4)-SAT_N (NP-complete)
3. **Aggressive truth assignments**: Extended truth assignments that also check if an instance falls in the easy class
4. **Metric space structure**: Distance between truth assignments forming (TA∞, d)
5. **Cauchy sequences and representations**: Construction of polynomial-time algorithm representations
6. **Compatibility and pseudo-algorithms**: Definition and properties
7. **Cantor diagonalization**: The attempted construction of uncountably many algorithms

## The Attempted Proof Logic

Liao's argument proceeds:

1. **Define 3SAT_N**: A normal variant of 3SAT, still NP-complete.
2. **Classify instances**: The Classification Theorem partitions 3SAT_N into easy cases (satisfiable by inspection) and the NP-complete core.
3. **Define aggressive truth assignments**: Polynomial-time "oracles" that decide the easy cases.
4. **Build metric space**: Endow compositions of aggressive truth assignments with a metric.
5. **Form Cauchy sequences**: Regular Cauchy sequences in <f>₂ converge to polynomial-time algorithm representations.
6. **Apply Cantor's diagonal argument**: If polynomially many algorithms exist, construct uncountably many distinct ones — contradiction, since algorithms are countable.

## Where the Formalizations Stop

The formalizations include `sorry` (Lean) and `Admitted` (Rocq) placeholders at critical gaps:

1. **The Diagonal Construction** (Section 10, Case 1): The sequence {f_n} constructed by diagonal argument is claimed to be outside all equivalence classes in the enumeration. This cannot be completed in the proof assistant because the claimed distinctness depends on an overly coarse equivalence relation (Proposition 2 says all elements of TA₁ are equivalent, defeating the diagonal).

2. **Uncountability of ECS**: The claim that the constructed sequence produces a new equivalence class requires that equivalence classes be fine enough to separate the diagonal from the enumerated classes. This is not established.

3. **Countably Many vs. Uncountably Many Algorithms**: The final contradiction requires that the representations of all ECS equivalence classes be distinct algorithms. But the equivalence relation defined can equate different algorithms.

## The Core Error (Summarized for Formalization)

Liao's proof has two incompatible facts:

- **Proposition 2** (Section 7): Any two elements of TA₁ are equivalent (under the appropriate relabeling map).
- **Diagonal Argument** (Section 10): Constructs a sequence outside all equivalence classes using differences in individual atomic truth assignments.

If all elements of TA₁ are equivalent, the constructed diagonal sequence uses aggressive truth assignments that are all equivalent to each other. Under the equivalence relation on sequences (Definition 7), the diagonal sequence will be equivalent to sequences already in the enumeration. The diagonalization fails.

## See Also

- [`../README.md`](../README.md) - Overview of the attempt
- [`../original/README.md`](../original/README.md) - Original paper materials and reconstruction summary
- [`../original/ORIGINAL.md`](../original/ORIGINAL.md) - Markdown reconstruction of the original paper
- [`../refutation/README.md`](../refutation/README.md) - Explanation of why the proof fails
