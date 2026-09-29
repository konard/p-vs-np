# A New and Elegant Argument that P is not NP

Craig Alan Feinstein, 2006.

## Reconstructed Argument Pattern

The article claims to give a short argument for `P != NP`. The proof can be
modeled as the following informal chain:

1. Choose an NP-complete problem with many possible witnesses or computation
   histories.
2. Observe that the number of possible witnesses grows exponentially with the
   input size.
3. Argue that a polynomial-time algorithm can examine only polynomially many
   of these possibilities.
4. Conclude that no polynomial-time algorithm can decide the NP-complete
   problem.
5. Infer `P != NP`.

## Critical Premise

The central implicit premise is:

> Every polynomial-time algorithm for the selected NP-complete problem must
> distinguish witnesses by direct or essentially exhaustive inspection.

This premise is stronger than the preceding counting facts. It is the point
where the argument would need a genuine lower-bound theorem for all
polynomial-time algorithms.

## Why the Reconstruction Is Sufficient

The formal files in this directory do not need a verbatim source transcript to
show the issue. They separate the valid counting observation from the invalid
transfer to arbitrary polynomial-time computation.

