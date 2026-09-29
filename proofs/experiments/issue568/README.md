# Issue 568: constructive SAT track

The target is one fixed `Complexity.Machine` and one fixed polynomial that
decide `Issue532.Machines.SAT` on **every encoded word**, with the bound
measured by `Complexity.Run`. The existing `Issue609.PEqualsNPAttempt.Candidate`
states that obligation. `Issue532.Machines.SATHard` is still an explicit
premise of the bridge to `Complexity.PEqualsNP`. This directory does not
claim an algorithm for P = NP.

## Checked first slice: local machine tableaux

`lean/Tableau.lean` and `rocq/Tableau.v` use the existing finite machine,
configuration, transition, and `Run` definitions. A trace lists the
configuration *before* each charged instruction. `LocalTrace`/`localTrace`
requires every adjacent pair to satisfy `step m c = inr d`, and requires the
last configuration to satisfy `step m c = inl b`. An empty trace is false.
`BoundedTableau`/`boundedTableau` also fixes the initial configuration and
limits the trace length to the clock.

The matching Lean and Rocq theorems `localTrace_iff_run` prove, for every
machine, start, answer, and time `t`:

```text
(exists trace, head trace = start AND length trace = t AND
               localTrace machine answer trace)
    iff Run machine start t answer
```

`boundedAccept_iff_run` then proves that a bounded accepting trace exists
exactly when `Run` accepts within the clock. This discharges the **local
transition soundness and completeness** obligation for this representation.
Before this PR there was no trace representation or theorem connected to the
shared `Run`. It does not yet discharge `SATHard`.

`trace_span_bound` proves that each represented configuration uses at most
`span start + length trace` tape cells. In particular,
`bounded_initial_span` gives the concrete bound `|x| + clock + 1` for a trace
starting at `initial x`. This counts tape cells, **not** the bits in a CNF or
the runtime of constructing it. State identifiers, clauses, and output
encoding still need bounds.

The paired examples check empty traces, zero clocks, wrong answers, premature
halts, missing final halts, and a valid two-step run. `wrong_successor_halts`
proves that a fabricated successor does accept by itself, while
`wrong_successor_rejected` proves that
the tableau rejects it because the preceding move cannot reach it. This
separates edge checking from final-answer checking.

The present constraints are local **between adjacent complete
configurations**. A later rectangular tableau must additionally prove that
bounded cell-neighborhood clauses implement those transitions, including tape
edges and state encoding. That per-cell CNF theorem is still open.

All listed results have **no explicit theorem hypotheses** beyond their
universally quantified machine, input, and clock data. The certified manifest
records Lean's standard `propext` allowance, plus `Quot.sound` for the width
bound and wrong-successor test; Rocq reports no global assumptions. There are
no new problem-specific axioms or admissions. Existing conditional bridges
still have explicit `SATHard` and solver premises; a clean assumption report
does not discharge them.

## Work plan and open obligations

1. **Cook–Levin bridge.** Convert these complete configurations into a finite
   rectangular tableau for both `VerifierProgram` constructors. Specify
   boundary blanks, initial input, certificate bound, transition, and an
   accepting row. Prove assignment-to-run and run-to-assignment directions,
   including malformed bit strings and clocks `0` and `1`. Then encode its
   local constraints into the repository's `CNF` and total `decodeCNF` model.
   Prove the *encoded bit length* bound, including variable identifiers and
   clause delimiters. Finally construct a reduction `Machine` and prove its
   `Computes` polynomial `Run` bound. Only then can `SATHard` be assembled.
2. **Executable baseline.** Reuse issue #8's verified DPLL semantics and the
   repaired Python backtracking experiment. Relate their representations,
   prove simplification, propagation, branching, backtracking, and termination
   for all formulas, and implement or verify a shared-machine execution with
   parsing, copying, lookup, and output costs. Keep the exponential worst-case
   upper bound visible. The issue #610 rollback case, empty clauses, sparse
   identifiers, and renamings remain regression inputs.
3. **Falsifiable improvement.** Define a computable canonical key for exact
   residual CNFs and prove that equal keys permit answer and witness reuse.
   Count generated states, edges, representation lengths, canonicalization,
   and lookup in the actual machine run. Test a specified infinite family or
   structural fragment, with decomposition construction and checking charged.
   Compare with [Idea 22](../issue532/ideas/Idea22.md) (decision to search),
   [Idea 25](../issue532/ideas/Idea25.md) (disjoint components),
   [Idea 26](../issue532/ideas/Idea26.md) (separator states),
   [Idea 35](../issue532/ideas/Idea35.md) (compilation), and
   [Idea 40](../issue532/ideas/Idea40.md) (cost recurrences). In particular,
   Idea 26's equality gadget distinguishes separator assignments, and Idea
   35 proves that a compact, fast all-input compilation is equivalent to a
   SAT decider. A new key must specify exactly what it can merge and what it
   costs; it cannot use SAT equivalence as a free test.

The first item is **known theorem newly mechanized / new-to-repository
engineering**, not a new mathematical result. Gäher and Kunze's
[Cook–Levin formalization](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20)
and [artifact](https://github.com/uds-psl/cook-levin) use a different
computational setup. A port must prove the simulation and encoding bounds in
this repository's model. The residual-sharing proposal is a **conjectural
experiment** until it yields a quantitative theorem or checked counterexample.

For the #567 exchange, each algorithm version should publish its exact
invariant and cost recurrence; each counterexample should identify the claim
and version it defeats. A failed implementation does not settle P vs NP.

## Common-errors audit

The local trace results address [families 4, 6, 11, and 12](../../attempts/COMMON_ERRORS.md):
both soundness and completeness are proved against the shared machine,
adjacent consistency alone cannot replace the final accepting instruction,
and no oracle or SAT answer is embedded in the local predicate. The malformed
successor case checks the distinction between a valid local edge and a valid
final state. Family 2 is guarded by the explicit `Run` clock and cell bound;
the later CNF and reduction stages must still charge all work. Families 5, 7,
8, 9, 15, and 17 remain relevant to later solver claims: no restricted or
measured instance can establish an all-input bound, no compact representation
is assumed to be cheap, and input size remains encoded bit length. This audit
does not claim to have passed those future obligations.

## Reproduce

Toolchains: Lean `v4.34.1` (`lean-toolchain`) and Rocq 9.0 (CI image).

```sh
lake build proofs.experiments.issue568.lean.Tableau
lake env lean experiments/issue568/TraceRegression.lean
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue568/rocq/Tableau.v
rocq compile -Q . '' experiments/issue568/TraceRegression.v
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The initial regression probes failed before the new modules existed. The
paired regression files and the certified-result audit now run in CI. No
experimental randomness is used in this slice.
