# P subset NP and the classical P versus NP disjunction

The Lean, Rocq, and Agda files here import the [shared finite-machine
model](../complexity/README.md). Their P and NP definitions require bounded
machine runs and bounded certificates. The `PSubsetNP` proof turns a P decider
into an NP verifier that ignores its certificate and accepts with the empty
certificate. Each proof is checked against the definitions in its own proof
assistant.

`PvsNPDecidable` also states `P = NP ∨ P ≠ NP`. In Lean and Rocq this follows
from classical excluded middle. In Agda, excluded middle is an explicit
postulate. This disjunction supplies neither an algorithm to determine the
answer nor a proof of either side. The term “decidable” in these file names is
historical and refers only to that classical disjunction.

The old records used `String → Bool` functions with a cost field unrelated to
execution; Agda also omitted correctness. Under those records, the Lean
counterexample in [issue #571](https://github.com/konard/p-vs-np/issues/571)
proved their `P=NP` statement. The current files use binary words and finite
machine programs instead. See [the regression experiment](../../experiments/issue571/)
for the old proof and the compiler check that now rejects it.

These files formalize P subset NP for the stated machine model. The repository
has not proved an equivalence between this model and every presentation of
Turing-machine complexity in the literature.

## Checks

```sh
lake build
bash experiments/issue571/check.sh
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/p_vs_np_decidable/rocq/PSubsetNP.v
rocq compile -Q . '' proofs/p_vs_np_decidable/rocq/PvsNPDecidable.v
```

Agda is checked by the `Agda Verification` CI job.
