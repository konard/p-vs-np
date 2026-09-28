# Issue 580 reproduction and verification

At the audited main commit, Zhu's Lean file declared
enumeration_gap and isomorphism_argument_invalid with conclusion True.
Groff's alleged SAT/UNSAT witness was an axiom about arbitrary Nat → Nat
functions and did not assert equal evaluation at a field point. Vega's
type-mismatch and subset theorems concluded True. The adjacent Rocq files
contained parallel tautologies, axioms, and admitted claims.

The regression suite was added first and failed against those files and
the unclassified COMMON_ERRORS.md index. Run it with:

    python3 -m unittest discover -s experiments/issue580 -p 'test_*.py' -v

The suite now guards against tautological claims and unproved assumptions
in the six named refutation files, checks that every catalog row has one
evidence label, and independently enumerates the six-vertex projector
witness. The Lean and Rocq compilers check the actual propositions.

The graph experiment can be rerun directly:

    python3 experiments/issue580/projector_witness.py

It prints all eight perfect matchings and their incidence ranks (4 or 5).
The graph has three C4 components, contradicting Zhu's Theorem 1(c3) bound
of n/4=1 for n=6. The four code weights challenge Lemma 4's n/2 bound under
the paper's code-permutation convention. This experiment does not simulate
equations (10–11). The Groff formula pair is in the Lean and Rocq files; it challenges
one raw polynomial evaluation, not the complete reconstruction algorithm.
