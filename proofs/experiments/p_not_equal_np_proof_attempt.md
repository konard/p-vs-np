# Williams' algorithm-to-lower-bound method: an open experiment

This experiment revisits the proposed P ≠ NP argument from [PR #43](https://github.com/konard/p-vs-np/pull/43). Its formal development is [Idea 41](issue532/ideas/Idea41.md), with paired [Lean](issue532/lean/Idea41.lean) and [Rocq](issue532/rocq/Idea41.v) files. [WilliamsFramework.lean](WilliamsFramework.lean) and [WilliamsFramework.v](WilliamsFramework.v) retain the original entry point for regression checks. No theorem here settles P versus NP.

## The result and its target

Williams' [Theorem 1.1](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf) says that a sufficiently faster-than-exhaustive-search algorithm for Circuit-SAT on circuits with `n` inputs and `n^k` gates, for every fixed `k`, implies **NEXP ⊄ P/poly**. His [ACC⁰ lower bound](https://people.csail.mit.edu/rrw/acc-lbs-ccc.pdf) applies this algorithmic method to a restricted circuit class. Neither statement has conclusion `NP ⊄ P/poly`.

For the general-circuit version, Idea 41 uses NAND straight-line programs from `Issue532.Circuits`. `WF n C` checks that every gate refers only to earlier wires; `output x C` evaluates those gates. `encCircuit n C` gives the machine an actual binary input. `CircuitSAT` accepts exactly encodings of well-formed satisfiable circuits. The circuit family and its polynomial gate bound are defined by `InPPoly`, which quantifies one polynomial over all positive input lengths **for each language**, not one exponent shared by every circuit or every language.

`FastCircuitSAT` states the algorithmic obligation in the shared `Complexity.Machine` model. For every gate-bound exponent `k`, a machine `m` must work on all well-formed circuits of at most `(n+1)^k` gates. For every saving exponent `c`, after some `n₀`, its halting run on `encCircuit n C` must have a step count `t` satisfying `t (n+1)^c ≤ 2^n`, and its Boolean answer must equal satisfiability. The `t` is bound by `Run m ... t b`; it is not a free reported cost. The quantifier order permits `m` to depend on `k` and `n₀` on `c`, as in the formal statement. The saving is `2^n / n^{ω(1)}` in asymptotic notation. A bound `2^n - n^δ` would be a different and much weaker expression; `2^(n-n^δ)` is a stronger sufficient bound when available.

The exhaustive-search baseline evaluates `2^n` assignments and `2^n |C|` gates. Idea 41 proves `length_allAssignments`, `bruteCircuitSAT_correct`, and `bruteForceGateEvaluations_eq`. These are finite calculations, not a fast algorithm.

## How the conditional implication works

The checked theorem `williams_method` takes four explicit inputs:

1. `FastCircuitSAT`: the open algorithm for general circuits.
2. `NTimeHierarchy`: a language in `NTIME(2^n)` outside a smaller nondeterministic time class. The lazy diagonal contradiction is proved, but its simulation statement remains an assumption.
3. `EasyWitnessLemma`: under `NEXP ⊆ P/poly`, accepted exponential-time computations have succinct circuit witnesses.
4. `WilliamsSpeedup`: the witness circuit and fast Circuit-SAT machine together simulate each `NTIME(2^n)` language inside the smaller time class.

The last two inputs are **named propositions**, not proved literature-to-model transfers. The Lean and Rocq theorems prove that these premises contradict `NEXP ⊆ P/poly`; they do not prove the premises. Idea 41 also proves the bridge `P = NP → FastCircuitSAT` under the explicit `CircuitSATInNP` premise. Its contrapositive says that refuting `FastCircuitSAT` would prove `P ≠ NP`. Proving `FastCircuitSAT` instead gives `NEXP ⊄ P/poly` under the three other premises; it does not itself give `P ≠ NP`. A proposed `NP ⊄ P/poly` would be stronger for that purpose and is not supplied by this method.

The speedup argument uses **easy witnesses and succinct verification**. Under the assumed circuit upper bound, guess a small circuit describing an exponentially long satisfying assignment. Build a polynomial-size circuit whose inputs index clauses and whose output flags a violated clause, then apply the faster Circuit-SAT algorithm to check that none exists. A machine-level construction, including the succinct reduction, gate bound and exact `Run` budget, is what `WilliamsSpeedup` still asks for. Enumerating all polynomial-size circuits is exponential in their description length; a single output bit also cannot disagree with both constant circuits on the same input. That diagonalization sketch from PR #43 has therefore been removed.

Circuit-SAT being NP-complete creates no logical circularity here. An algorithm taking `2^n/n^{ω(1)}` time need not run in polynomial time. The unresolved work is constructing and proving such an algorithm, then transferring the known hierarchy and witness results into this exact machine model. No unsupported strict chain of ACC⁰, TC⁰, NC, or P/poly inclusions is used. In this repository, `InPPoly` means nonuniform polynomial-size NAND circuit families; ACC⁰ and TC⁰ would require their own gate bases, depth conditions, uniformity conventions, and paired proofs before they could be formal targets.

## Checked boundary and next obligation

| Claim | Current check |
| --- | --- |
| NAND gate semantics, well-formedness, circuit encoding and exhaustive search | Proved in paired Lean/Rocq modules. |
| Zero-step oracle and malformed-circuit rejection | Proved in the paired `WilliamsFramework` regression files. |
| `FastCircuitSAT → NEXP ⊄ P/poly` | Proved **conditionally** from `NTimeHierarchy`, `EasyWitnessLemma`, and `WilliamsSpeedup`. |
| `P = NP → FastCircuitSAT` | Proved **conditionally** from `CircuitSATInNP`. |
| General-circuit fast SAT, model-level hierarchy, easy witnesses, speedup, `CircuitSATInNP` | Not discharged here. |
| `NP ⊄ P/poly` or `P ≠ NP` | Not proved. |

A concrete next obligation is `CircuitSATInNP`: build a shared `Machine` that parses `encCircuit`, checks `WF`, reads a satisfying assignment as a certificate, evaluates the NAND gates, and prove its `Run` bound polynomial in the input encoding length. That would remove one named premise from the `P = NP → FastCircuitSAT` bridge. The longer research target is `WilliamsSpeedup`, including the succinct Cook–Levin construction and its `Run` accounting. The [Idea 41 dossier](issue532/ideas/Idea41.md) records the exact remaining statements.
