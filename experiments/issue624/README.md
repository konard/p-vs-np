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
and explicit polynomial bounds. `TableauCNFRegression` checks the complete
formula, its unary size contract, and concrete models for both verifier
constructors with empty/short/full certificates. Wrong-state, wrong-head, and
wrong-tape assignments satisfy the earlier fragments but fail the initial row.
The input-independent reduction machine and SAT hardness remain outstanding.

`CounterRegression` executes a fixed nine-state counter on empty and mixed-bit
inputs, with arbitrary retained left tape and an existing counter. It checks
both tape sides, exact runtime, insufficient fuel, and rejection of missing
separators or non-unary counter symbols. Its 16-state `countedInput` checks
entry from `initial x`, including genuinely empty input, input retention, and
construction of the unary input length. The generic block contracts and
explicit polynomial envelopes are proved in both kernels.

`RegisterRegression` checks a shared generated insertion table on empty and
mixed-bit blocks, middle-register and final-output insertion, insufficient
fuel, and a missing home marker. The paired generic contracts quantify over
every input, register, and output block. Inserting one bit costs exactly
`2 * payload.length + 4`; appending `c` bits costs
`c * (2 * payload.length + c + 3)`. Fixed-count increments and constant
emission preserve the retained input and all other blocks. Regeneration and
bounded execution tests cover 2,058 small configurations from the same tables.
The straight-line `Prog` compiler sequences these operations with pure
`runProg` and `cost` semantics. Its generic execution theorem checks register
indices and preserves the number of registers. A complete program costs
`wordTime (growth p) payload.length`; the regressions execute a mixed
increment/emission sequence and reject one fewer unit of fuel.

The same generator also supplies unary decrement and clear tables. Clearing
the register between payloads of lengths `pre` and `post`, initially holding
`value` ticks, costs exactly
`value * (2 * pre + 4 * post + 2 * value + 7) + 2 * pre + 3`.
It preserves every surrounding symbol, returns to home, and permits only
trailing blanks in its final configuration. A polynomial envelope is proved
in both kernels. The regressions cover 196 finite clear executions, empty
registers, malformed unary contents, invalid slots, and insufficient fuel.
`clear_then_compile_reaches` consumes the clear contract before any
well-formed straight-line program. Its composition regression clears two
ticks, increments the scratch register, and appends a bit in exactly 83 steps.
`clear_then_cost_polynomial` combines both charged bounds using the shared
`polyAdd`, measured against the original payload and the program's growth.
These proofs reuse shared `Reaches` simulation and exit retargeting; they do
not yet construct the formula-emitting reduction machine.

The generator now supplies a unary loop controller and its charged backward
jump. `repeat_compile_reaches` executes any well-formed straight-line body
that leaves the loop register unchanged. Its table depends only on the body
and register index; the number of iterations comes from the tape. The pure
`repeatRun`/`repeatCost` semantics charge every pop, body instruction, backward
jump, and final empty-register test. `repeat_body_reaches` also embeds an
arbitrary home-preserving body, including its trailing blank padding.

`emitTicks` consumes this controller to append two true bits per unary unit.
For prefix/suffix tape lengths `pre`/`post` and counter `value`, its exact
cost is `value * (6 * pre + 8 * post + 12 * value + 12) + 2 * pre + 3`,
bounded by `20 * (pre + value + post + 1)^2`. `emitLiteral` consumes it with
the shared delimiter/polarity bits, appending the exact original `encodeLit`
and clearing only its scratch counter. Its cost adds
`wordTime 2 (pre + post + 2 * value + 1)` and is bounded by
`40 * (pre + value + post + 1)^2`. Both kernels check the generic contracts.

Regressions cover 588 finite tick executions and 30 literal executions with
every tested register position, both polarities, empty counters, retained
mixed-bit input/output, exact fuel boundaries, malformed unary counters,
and bodies that write their own loop counter. A paired regression checks
that the literal table is independent of the identifier on the tape.
`compose_home_reaches` combines arbitrary home-preserving blocks with blank
padding and is used in the literal proof.

`Program` composes straight-line code, clearing, dynamic literals, sequences,
and nested loops under one exact charged compiler contract. The regressions
execute a nested loop and a dynamic copy in both kernels, check insufficient
fuel, and reject bodies that increment, clear, emit, or recursively consume
their own loop counter. `addToProgram` restores the source, adds its value to
the destination, and clears scratch, with a cubic runtime bound measured
against the original payload. Its generic register contract covers all other
slots and prior output. The Python interpreter checks 36 nested executions,
648 copies across every permutation of three distinct register slots, and
324 copy/literal/clause-delimiter compositions, including exact fuel boundaries
and retained mixed-bit input/output. All use the original generated tables.
Input reads, dynamic arithmetic, schema compilation, setup/restoration, and
the complete reduction remain outstanding; these contracts alone do not
establish `red_computes`.

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
lake env lean experiments/issue624/TableauCNFRegression.lean
lake env lean experiments/issue624/CounterRegression.lean
lake env lean experiments/issue624/RegisterRegression.lean
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
rocq repl -quiet -Q . '' < experiments/issue624/initial_probe.in
rocq repl -quiet -Q . '' < experiments/issue624/register_probe.in
rocq repl -quiet -Q proofs proofs < experiments/issue624/delete_probe.in
python3 scripts/check_proof_status.py --lean --rocq
python3 experiments/issue624/check_tableau_contracts.py --lean
python3 experiments/issue624/check_tableau_contracts.py --rocq
python3 experiments/issue624/existing_bridge_probe.py --lean
python3 experiments/issue624/existing_bridge_probe.py --rocq
```

[COMPLETION_PLAN.md](COMPLETION_PLAN.md) is the paired Cook–Levin delivery checklist.

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

`check_tableau_contracts.py` checks the seven implemented tableau results
against the completion gate's original, unapplied types in each kernel. It
does not replace the full completion check or certify the missing reduction.

`existing_bridge_probe.py` checks the registered Idea 36 bridge at the
completion gate's exact type. Its separate `VCHard`, `CoverCheckInP`, and
`ExactRoundingObligation` premises remain part of that original contract.
