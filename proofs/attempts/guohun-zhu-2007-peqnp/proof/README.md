# Zhu (2007): forward proof sketch

The [Lean](lean/ZhuProof.lean) and [Rocq](rocq/ZhuProof.v) files follow the
projector-graph, perfect-matching, rank, and enumeration steps of the paper.
They contain simplified definitions and unproved premises. Compilation
checks only the consequences of those premises.

To establish Theorem 3, the sketch still needs a precise equivalence
relation on matchings, a proof that representatives preserve the rank
criterion, a complete and polynomial-time implementation of equations
(10–11), and a proof of correctness on every Γ digraph.

The [refutation audit](../refutation/README.md) gives a concrete Γ input
whose projector graph violates Theorem 1(c3)'s n/4 bound on C4 components.
It also has four code classes under the convention suggested by the paper's
examples, challenging Lemma 4's counting step. These results do not prove
that every possible matching-enumeration algorithm fails.
