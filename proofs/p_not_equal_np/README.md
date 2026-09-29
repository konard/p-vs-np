# Conditional tests for P ≠ NP

The Lean, Rocq, and Agda files use the [shared finite-machine P and NP
model](../complexity/README.md). A P witness contains a finite machine and a
polynomial bound on its actual halting runs. An NP witness contains a verifier,
a polynomial step bound, and a polynomial certificate-length bound.

The main result says that `P ≠ NP` is equivalent, using classical logic for
the forward direction, to the existence of a language in NP and outside P.
The lower-bound test quantifies over every finite machine and every polynomial
bound and refers to their runs. It cannot be met by assigning an unrelated
`timeComplexity` field to an arbitrary function.

The SAT test takes SAT's NP membership as a premise. The NP-completeness test
takes a completeness predicate and a proof that every problem it marks belongs
to NP as premises. These files do **not** contain a polynomial-time reduction
semantics or a proof that SAT is NP-complete. In particular, they do not prove
`P ≠ NP` or supply a SAT lower bound. The earlier unconditional SAT and
NP-completeness axioms have been removed from these tests.

`ProofOfPNotEqualNP` holds a proof term. The proof assistant checks that term;
`verifyPNotEqualNPProof` returning `true` is not an independent verification
algorithm.

See [issue #571](https://github.com/konard/p-vs-np/issues/571) for the
runtime-free model that these definitions replaced.
