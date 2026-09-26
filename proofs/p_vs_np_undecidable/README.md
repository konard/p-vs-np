# Conditional independence schema

The Lean, Rocq, and Agda files import the [shared finite-machine P and NP
model](../complexity/README.md). They define an abstract `Theory` with a
predicate saying which statements that theory proves. For a supplied theory,
`PvsNPIsIndependent theory` means that the theory proves neither `P=NP` nor
its negation. No formal proof relation for ZFC is supplied, and no theorem
asserts that P versus NP is independent of ZFC.

The earlier files used the runtime-free P/NP records from
[issue #571](https://github.com/konard/p-vs-np/issues/571). Their purported
independence statements were also too weak or inconsistent: Rocq used `True`
as a placeholder, while Lean and Agda used proposition-level negation in
place of a separate provability relation. The current schema keeps those
concepts separate. It does not claim model existence from independence; that
would require additional metatheory and hypotheses.

The Isabelle files in [`../../archive/isabelle/`](../../archive/isabelle/) are
historical toy-model material and are not checked by the current CI.
