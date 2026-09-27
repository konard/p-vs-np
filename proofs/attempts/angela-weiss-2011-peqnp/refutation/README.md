# Weiss 2011: counting facts and the KE complexity gap

This directory contains historical Lean and Rocq models of Weiss's proposed
KE-tableau macro. The Lean refutation proves a specific counting fact. It does
not prove a worst-case lower bound for Weiss's algorithm.

## Proven in Lean

For `n` variables, there are `2^n` complete Boolean assignments. The theorem
`numAssignments_exponential` proves that for every natural coefficient `c` and
degree `k`, some `n` satisfies `2^n > c * n^k`. Its witness is
`n = 2^(c + k + 8)`. The old witness `n = c + k + 2` was false: with `c = 1`
and `k = 10`, it gives `2^13 = 8192 < 13^10 = 137858491849`.

`full_ke_cut_tree_exponential` proves the same count for a **full binary tree**
that makes one unconditional cut for each variable. The regression check in
[`experiments/issue586`](../../../../experiments/issue586/) compiles these
claims, verifies the counterexample, and checks that the counting theorems do
not depend on Lean's `sorryAx`.

## What remains to be shown

A KE solver may prune branches or use a compressed representation. The number
of possible assignments alone does not imply that the solver visits every
assignment, takes exponential time, or produces an exponentially large macro.
The conditional theorem `enumerating_all_assignments_is_exponential` transfers
the count to a work function only when a lower bound of `2^n` on that function
has been proved. The formalization supplies no such lower bound for Weiss's
actual construction.

To validate the claimed polynomial 3-SAT procedure, one would need a precise
macro construction, a proof that it decides satisfiability correctly, and a
polynomial bound for its construction and evaluation. Without these, the
complexity claim is unproved. Showing that a particular construction exceeds
polynomial time would require an analysis of that construction, not assignment
counting alone.

The Rocq file is a historical sketch with admitted claims and should not be
read as a certified lower bound. See the [attempt overview](../README.md) for
background and source links.
