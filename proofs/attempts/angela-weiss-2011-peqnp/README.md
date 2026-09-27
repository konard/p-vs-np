# Angela Weiss (2011): proposed polynomial 3-SAT algorithm using KE-tableaux

**Attempt ID:** 74 in Woeginger's list

**Author:** M. Angela Weiss

**Year:** 2011

**Claim:** P = NP via a polynomial-time 3-SAT algorithm
**Status in this repository:** The required correctness and complexity bounds are not established

## Proposed approach

Weiss proposes a KE-tableau procedure with a "macro" representing closed
branches. The claim is that the macro can be constructed and evaluated in
polynomial time while deciding whether an arbitrary 3-SAT formula is
satisfiable. A correct polynomial-time 3-SAT decision procedure would imply
P = NP.

The [original reconstruction](original/ORIGINAL.md) describes the proposed
procedure. The [proof sketch](proof/README.md) and [refutation analysis](refutation/README.md)
discuss the missing steps.

## Established counting fact

There are exactly `2^n` complete assignments to `n` Boolean variables. The
Lean theorem `numAssignments_exponential` proves this count exceeds every
polynomial `c * n^k` somewhere. A full binary tree of `n` unconditional
variable cuts likewise has `2^n` leaves. The proof uses a valid witness and
has no arithmetic admission. Issue [#586](https://github.com/konard/p-vs-np/issues/586)
identified the earlier false witness.

These counts do not show that the proposed KE procedure must construct the
full cut tree, visit every assignment, or store every branch. A lower bound
for the actual algorithm needs an explicit model of its operations and a
separate proof linking those operations to the count. A compact
representation can sometimes encode a large set without enumerating it.

## Open proof obligations

For the proposed method to prove P = NP, it needs:

1. A precise definition of the macro construction and evaluation procedure.
2. A proof that it decides 3-SAT correctly on all inputs.
3. Polynomial bounds on both construction and evaluation as functions of input size.

The formalization here does not discharge these obligations. It identifies a
gap in the argument; it does not prove an unconditional exponential lower
bound for KE-tableaux, for the macro, or for 3-SAT algorithms.

## Repository contents

- [`original/`](original/) contains source material and an English reconstruction.
- [`proof/`](proof/) contains a historical formalization of the proposed argument, including admitted steps.
- [`refutation/`](refutation/) contains counting facts and analysis of the complexity gap.

## References

- Weiss, M. A. (2011), *A Polynomial Algorithm for 3-sat*; source material is preserved in [`original/`](original/).
- [Woeginger's list of P versus NP attempts](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm), entry 74.
- D'Agostino, M. and Mondadori, M. (1994), *The Taming of the Cut: Classical Refutations with Analytic Cut*.
