# Cook–Levin construction regressions

These paired regression files exercise the certified prerequisites in
[`proofs/experiments/issue624`](../../proofs/experiments/issue624/).
`CircuitCNFRegression` checks the shared NAND compiler against satisfiable
and unsatisfiable circuits, wrong gate outputs, and unary encoding bounds.
`MachineCNFRegression` checks actual finite-table instruction dispatch,
including default rejection for missing columns, nonzero variable offsets,
wrong instruction outputs, missing or multiple selected values, and an empty
program. Its size checks include the unary identifiers and explicit polynomial.
`SuccessorRegression` checks actual charged moves in all three directions,
state changes, row decoding, and rejection of incorrect writes, copied cells,
heads, and states. It also covers missing instructions, invalid destinations,
halts, empty domains, and both window edges. Its wrong-write, wrong-copy, and
wrong-state assignments satisfy the row clauses and fail the transition clauses.
`RunCNFRegression` checks the bounded accepting-trace compiler: immediate and
two-row acceptance, inactive suffixes, premature halts, exhausted clocks,
wrong successors, canonical decoding, empty domains, and unary encoded-size
and explicit polynomial bounds. These regressions do not certify full
tableau CNF or SAT hardness; initial input/certificate wiring and the
input-dependent reduction machine remain outstanding.

After building the imported modules, run:

```sh
lake env lean experiments/issue624/CertificateRegression.lean
lake env lean experiments/issue624/WindowRegression.lean
lake env lean experiments/issue624/CNFRegression.lean
lake env lean experiments/issue624/EmitterRegression.lean
lake env lean experiments/issue624/CircuitCNFRegression.lean
lake env lean experiments/issue624/MachineCNFRegression.lean
lake env lean experiments/issue624/SuccessorRegression.lean
lake env lean experiments/issue624/RunCNFRegression.lean
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
bash experiments/issue624/check.sh all
```

Each Lean regression is an explicit CI step; each Rocq regression is included
in `_CoqProject` and the whole-project build. All print assumption reports
for the main conclusions. The complete manifest audit output for these
modules is recorded in [ASSUMPTIONS.md](ASSUMPTIONS.md).

The small interactive inputs preserve the diagnostics used while developing
the Rocq proofs. They show intermediate goals, then complete their proofs.
They are `.in` files because they are diagnostic sessions rather than library
modules. All inputs are finite; neither probe performs a stress experiment.

```sh
rocq repl -quiet -Q proofs proofs < experiments/issue624/certificate_probe.in
rocq repl -quiet -Q proofs proofs < experiments/issue624/tableau_probe.in
rocq repl -quiet < experiments/issue624/local_cnf_size_probe.in
rocq repl -quiet < experiments/issue624/local_cnf_size_real_probe.in
lake env lean experiments/issue624/field_probe.lean
lake env lean experiments/issue624/successor_probe.lean
rocq repl -quiet -Q proofs proofs < experiments/issue624/successor_probe.in
rocq repl -quiet -Q proofs proofs < experiments/issue624/successor_decode_probe.in
rocq repl -quiet < experiments/issue624/successor_arithmetic_probe.in
rocq repl -quiet -Q . '' < experiments/issue624/run_probe.in
python3 experiments/issue624/run_assumptions.py
```

[PLAN.md](PLAN.md) tracks the completed prerequisites and the remaining
Cook–Levin construction. #624 must remain open.

`check.sh` reproduces the local Python, Lean, Rocq, and pinned-container Agda
workflow checks. Select an individual suite with `python`, `lean`, `rocq`, or
`agda`. Save large logs under `ci-logs/`. Passing these prerequisite checks
does not establish completion. `bash experiments/issue624/check.sh completion`
additionally requires all full-deliverable contracts in both kernels. It
currently fails on missing endpoints and the remaining bridge premises.

The completion checker and workflow regressions reproduce the previous gap:
the certified-result audit could accept the registered prerequisites while
`satHard` was absent. They also test deleted registrations, duplicate entries,
admissions in imported files, expanded assumption policies, type mismatches,
and failed/cancelled/skipped completion jobs. The real-kernel experiment
`check_completion_kernels.py --lean` / `--rocq` verifies that explicit,
implicit, and aliased premises, a restricted witness type, and an input-dependent
machine constructor cannot pass unconditional contract checks. Its temporary probes contain no
admissions or global axioms.

[The completion plan](COMPLETION_PLAN.md) tracks the full requirement and
the required CI result. [The checker documentation](../../scripts/README.md#check_issue624_completionpy)
describes the paired contract interface and required merge check.

[TABLEAU_DESIGN.md](TABLEAU_DESIGN.md) records the implemented trace layout,
the remaining initial-row and complete-size obligations, and the
input-dependent emitter's missing machine operations.
