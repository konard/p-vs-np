# Shared finite-machine complexity model

This directory defines the P and NP statements used by the current Lean, Rocq,
and Agda formalizations. The three implementations use the same mathematical
model; they are separate checked implementations, not a cross-assistant proof
of equivalence.

## Status

This model is the formal meaning of P and NP in the current proofs. The target
is `Complexity.PEqualsNP`; [FORMAL_STATEMENT.md](../../FORMAL_STATEMENT.md)
relates it to the Clay statement. As of November 2026, the following are
proved on top of the model and certified in
[the result manifest](../../scripts/proof_status.json):

- `Complexity.pSubsetNP`: P ⊆ NP, in this directory.
- `Issue532.SATVerifier.satInNP`: SAT ∈ NP, with an explicit 45-state
  verifier. The SAT language and the premises `SATHard` and `CookLevin` are
  defined in [`issue532/lean/Machines.lean`](../experiments/issue532/lean/Machines.lean).
- `Issue7.ClockedSAT.pNotEqualsNP_of_pi2`: the Π⁰₂ clocked-SAT sentence
  implies `P ≠ NP`, with no premise.
- `Issue568.Tableau.boundedAccept_iff_run`: bounded machine tableaux match
  `Run`, the first slice of a constructive Cook–Levin theorem.

NP-hardness of SAT (`SATHard`) is **not** proved; it is the main open premise.
Without it, `InP SAT` and `PEqualsNP` are different statements here.
`CircuitSATInNP` and `PSubsetPPoly` are premises on `main`; unmerged PRs
[#631](https://github.com/konard/p-vs-np/pull/631) and
[#632](https://github.com/konard/p-vs-np/pull/632) prove them (as of
2026-11-03). Every named premise is listed in
[proofs/HYPOTHESES.md](../HYPOTHESES.md).

## Machine and cost semantics

Inputs and certificates are finite lists of bits. A deterministic one-tape
machine has a finite list of instruction rows, indexed by a natural-number
state. Each row has at most four entries, one for each tape symbol: blank, zero,
one, and separator. A missing entry rejects. The initial state is zero and the
initial tape contains only the input. A transition can write one symbol and
move one cell left, right, or stay. A halt instruction returns one Boolean
answer. Each instruction, including the halt instruction, costs one step.
`Run machine input t answer` is derived from exactly `t` transitions.

A polynomial bound is explicit data `c (n + 1)^k`, for natural constants `c`
and `k`. `ClassP` requires a machine that halts within that bound on every
input, and every run's answer must match the language. `ClassNP` requires a
certificate bound of that form, a verifier that halts within a polynomial
bound on each bounded certificate, and an equivalence between language
acceptance and a bounded accepting run. The paired verifier reads
`input ++ [separator] ++ certificate`. A second verifier constructor ignores
its certificate and runs a P machine on the input; this gives the usual
P subset NP proof with an empty certificate.

`PolynomiallyBounded` is the shared predicate for standalone time, space, and
size functions in the Lean and Rocq attempt modules. It uses the same bound at
length zero. Both implementations prove zero, constants, `n + 1`, pointwise
domination, addition, multiplication, and composition. The regression examples
are in [`experiments/issue574`](../../experiments/issue574/).

The program is finite syntax. A language predicate cannot be placed in the
transition table or the initial configuration. Costs are attached to actual
runs, and certificates are bounded in length. These are the missing links
identified in [issue #571](https://github.com/konard/p-vs-np/issues/571).

## Scope

The formalized input model is binary words, not the earlier `String` model.
No theorem identifies this implementation with every conventional Turing
machine variant, nor proves a specific problem NP-complete. The P versus NP
question remains open. The classical disjunction `P = NP ∨ P ≠ NP` in this
repository is excluded middle, not an algorithm deciding its truth.

The [Clay problem statement](../../pvsnp.pdf) gives the external mathematical
reference. This directory's definitions are the precise internal meaning of
P and NP in the checked files.

## Verification

```sh
lake build
bash experiments/issue571/check.sh
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
# Then compile its Rocq consumers with the same -Q option.
# Agda is checked in CI using the pinned container image.
```

`experiments/issue571/AuditBefore.lean` records the original counterexample.
The regression check requires it to fail because a `ClassP` witness now needs
a machine, a bound, and a termination proof. The other experiment checks that
one halting instruction incurs one step.
