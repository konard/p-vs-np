# Issue #626: P is contained in P/poly

The paired Lean and Rocq theorem `Circuits.pSubsetPPoly : PSubsetPPoly`
proves the inclusion for the repository's finite-table machines and NAND
straight-line circuits. The compiler takes only a machine, a polynomial clock,
and an input length. Its first `n` wires are the actual input bits; it never
receives a language, truth table, answer, or termination witness.

This discharges a known simulation theorem. SAT and NP circuit lower bounds
remain open obligations; this does not prove P ≠ NP.

## Construction and proofs

The circuit model moved into `issue532/{lean,rocq}/CircuitModel` without
changing its definitions. `Circuits` re-exports it and the inclusion theorem,
so existing users retain the shared circuit semantics.

| Paired module | Role |
| --- | --- |
| `NandCompiler` | Compile Boolean expression trees and multiple outputs into backward-referencing NAND gates; prove wire semantics, well-formedness, and exact expression cost. |
| `Window` | Pad the two tape stacks with blanks. A transition consumes one cell of margin, so a shrinking window preserves every clocked run. Halting answers are absorbing. |
| `Simulation` | Encode done/answer bits, the scanned symbol, one-hot states, and both stacks. Compile the initial row from input wires and each successor row from its predecessor. Prove wire bounds and polynomial gate count. |
| `Correctness` | Prove the row encoding invariant, compose it through the NAND compiler, establish `simCircuit_correct`, and package every `ClassP` witness into `InPPoly`. |

Missing table rows, missing columns, and out-of-range successor states follow
`Complexity.instruction`'s default rejection. The two-bit encoding distinguishes
blank, zero, one, and separator. Both tape directions and stationary writes
follow `Complexity.moveHead`.

For `T = p(n)` and `M = m.program.length`, the initial window has
`n + T + 1` cells per stack. A row has `4 + M + 4·cells` bits. The proved bound is

```
|simCircuit m p n| ≤ (T·(64M + 19) + 3)·(4 + M + 4(n + T + 1)) + 2.
```

If `p(n) = c(n+1)^d`, `simulationPolynomial` has coefficient
`(c(64M+19)+3)(M+4c+8)+2` and degree `2d+1`.
`simCircuit_WF` holds at every positive length; `simCircuit_polynomial_size`
holds at every length. Correctness assumes a positive input length and an
actual `Run` whose charged instruction count is at most `p(n)`. Extra rows
preserve an early halting answer. The positive-length convention of `InPPoly`
is unchanged.

`simCircuit_correct_of_localTrace` uses the existing
`Issue568.Tableau.localTrace_iff_run` and `bounded_initial_span` to give the
same circuit answer and certify that all trace configurations fit the window.

The concrete Circuits, Idea 19, Idea 30, Idea 31, and issue #10 bridges use
`pSubsetPPoly` internally. Abstract schemas retain their simulation parameters.

## Reproduction and certification

Before this change, the shared Circuits module had the definition
`PSubsetPPoly`, but no theorem `pSubsetPPoly`; the regression's theorem-type
check failed. The paired regression files now check that theorem and execute
the actual NAND circuit on input-dependent one- and two-bit machines.
They also cover early halts, zero clocks, missing table data, blank tape,
and a separator written and read after moving right then left.

Negative proofs show that a constant-answer circuit cannot simulate both
one-bit inputs, that a two-instruction machine cannot terminate within a
one-instruction clock, and that an infinite loop cannot satisfy `ClassP`'s
termination field. Runtime inputs and clocks are finite (at most two bits
and three instructions); the check script bounds regression memory.

Run from the repository root:

```sh
bash experiments/issue626/check.sh
```

The inclusion, correctness, well-formedness, polynomial size bound, tableau
adapter, and updated bridges are listed in `scripts/proof_status.json` and
built in both certified CI jobs. The audit scans their local import closures
and queries transitive assumptions. Rocq reports no assumptions. Lean reports
only its standard foundational axioms `propext`, `Quot.sound`, and (for
correctness/inclusion) `Classical.choice`; there are no added axioms or
admissions in the certified closure. Executable examples supplement the
kernel-checked universal correctness theorem.
