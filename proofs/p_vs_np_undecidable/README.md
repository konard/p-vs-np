# Conditional independence schema

The Lean, Rocq, and Agda files import the [shared finite-machine P and NP
model](../complexity/README.md). Each defines the same small `Statement`
syntax: an atom for `P=NP` and a `neg` constructor. `denotes` maps that
syntax to a semantic proposition. A supplied `Theory` has a proof predicate
over *statements*, and `Provable T φ` exposes that predicate. Thus
`PvsNPIsIndependent T` abbreviates
`¬Provable T pEqualsNP ∧ ¬Provable T (neg pEqualsNP)`. Negating a statement
constructs syntax; it does not assert that its denotation is false.

These files do not encode ZFC's language or axioms, define a derivation
system, or instantiate `Provable` with ZFC provability. The predicate can be
arbitrary: the empty proof relation makes the independence definition true,
while a relation proving every statement makes it false. The regression
examples in [`../../experiments/issue572/`](../../experiments/issue572/)
check the empty case and the denotation of syntactic negation in each prover.
The `independence_has_no_proof` theorem only projects the two conjuncts of
the definition; it supplies neither nonprovability result. Any ZFC
independence claim would require an actual encoding of proofs and separate
metatheoretic arguments for both nonprovability claims, with their required
consistency or model-existence assumptions stated explicitly.

The earlier files used the runtime-free P/NP records from
[issue #571](https://github.com/konard/p-vs-np/issues/571). Their purported
independence statements were also too weak or inconsistent: Rocq used `True`
as a placeholder, while Lean and Agda used proposition-level negation in
place of a separate provability relation. The current schema keeps those
concepts separate. It does not claim model existence from independence; that
would require additional metatheory and hypotheses. The excluded-middle
example is a semantic disjunction, not a decision procedure or an
independence theorem. Agda obtains it from an explicit classical postulate.

The Isabelle files in [`../../archive/isabelle/`](../../archive/isabelle/) are
historical toy-model material and are not checked by the current CI.
