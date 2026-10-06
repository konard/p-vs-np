# Cook–Levin construction in the shared machine model

**Status: the full Cook–Levin theorem is not proved. The issue remains open.**
The single-tape reduction machine, `satHard`, and unconditional P = NP bridges
remain to be constructed. The complete `tableauCNF` and its explicit polynomial
encoded-size bound are checked in both provers. This directory certifies
variable-length certificates, fixed-width
verifier traces, local CNF combinators, a NAND-circuit CNF compiler, a
finite-row successor and bounded accepting-trace compilers, and a finite-table
output primitive and input-retaining unary counter blocks.

`MachineCNF` compiles instruction dispatch from the existing machine table.
`SuccessorCNF` compiles charged tape moves between two represented rows.
`RunCNF` assembles those moves and accepting termination into a bounded trace
formula. `InitialCNF` connects its first row to the input and decoded certificate;
`CookLevin` assembles the full formula and its language correspondence.

Classification: **known theorem mechanized**, for these prerequisites only.
Nothing here establishes an answer to P versus NP.

PR #630 now has an independent completion gate requiring all full-deliverable
contracts in both kernels, including the finite reduction's charged `Computes`
proof and unconditional public bridge signatures. Its missing-endpoint failure
propagates to the required `Verification Summary` merge check; green checks
for the prerequisites below cannot establish completion. See the
[completion checker](../../../scripts/README.md#check_issue624_completionpy).

## Certificate CNF

`CertificateCNF.lean` and `CertificateCNF.v` have matching public theorem names.
For bound `B`, each certificate cell has a presence variable and a value
variable. `certificateCNF start B` reserves these indices:

| Variable | Meaning |
| --- | --- |
| `2 * (start + i)`, for `i < B` | Certificate cell `i` is present. |
| `2 * (start + i) + 1`, for `i < B` | Its Boolean value. |
| `2 * (start + B)` | Forced absent sentinel. |

For each cell, the two clauses enforce `value → present` and
`present(next) → present`. The negative unit clause for the sentinel stops
certificates at the bound. Thus absent cells are canonical blanks and blanks
are suffix-closed. A present false bit is distinct from a blank. Bound zero
still produces the sentinel clause.

`certificateCNF_models` proves, for **each assignment**, that CNF satisfaction
is equivalent to representing its decoded certificate, including the blanks
and sentinel. `represents_length` proves every represented certificate fits
the bound; `represents_decode` makes the decoded certificate unique.
`encodeCertificate_models` and `decode_encodeCertificate` prove that every
bounded certificate, including the empty certificate, has a model and is
recovered exactly. `overlong_rejected` proves rejection for every attempted
overlong certificate. `overlong_not_representable` also excludes any other
assignment representing it.

The fragment has `2B + 1` clauses. `certificateCNF_variables` bounds all its
variable identifiers by `2 * (start + B) + 1`. Using the repository's actual
`encodeCNF`, `encode_certificateCNF_length` proves the **exact bit length**:

```text
8 * B * B + 14 * B + 4 + (16 * B + 4) * start
```

At `start = 0`, substituting `B = c * (n + 1)^d` gives the explicit polynomial
`⟨8c² + 14c + 4, 2d⟩`, proved by `certificateCNF_polynomial_size`. This counts
the unary variable identifiers, literal tokens, and clause delimiters; it is
only a bound for the certificate fragment.

## Semantic verifier interface

`VerifierTableau` combines the certificate CNF with #568's `LocalTrace`, its
starting configuration, and the trace-length clock. Both `.paired` and
`.ignoreCertificate` are covered. The paired initial configuration contains
the **decoded certificate**, with its actual length; unused capacity becomes
blank tape rather than extra certificate bits. The acceptance clock remains
`VerifierProgram.timeLimit np.timeBound x cert` at that actual length.

`verifierTableau_iff_language` proves, for every `ClassNP` witness and input,
that an assignment and such a trace exist exactly when `np.language x = true`.
The proof reuses `localTrace_iff_run`; there is no new trace semantics.

For future rectangular sizing, `maxClock` is
`timeBound.eval (n + certBound.eval n + 1)`. `verifierTimeLimit_le` proves it
is an envelope, and `maxClock_polynomial` supplies the explicit polynomial

```text
coefficient = timeBound.coefficient * (certBound.coefficient + 2)^timeBound.degree
degree      = (certBound.degree + 1) * timeBound.degree
```

`verifierTableau_span` bounds every represented configuration by
`n + certBound.eval n + maxClock n + 2` tape cells.
`acceptingRun_timeLimit` additionally proves that **every** accepting run on
a bounded certificate fits its actual clock: the verifier's termination
witness and determinism force the same step count. Consequently
`envelopeTableau_iff_exact` proves equality of the envelope and exact-clock
model predicates, for the original assignment and trace. This covers both
verifier constructors.

## Fixed tape windows

`FixedWindow` pads both sides of a configuration with blanks and proves a
step-by-step simulation of the shared two-way tape. Moving left from an empty
represented left tape remains valid; there is no assumed left boundary.
`run_fitWindow_iff` preserves the answer and exact charged run length.

With `T = maxClock np n` and `B = certBound.eval n`, `windowWidth` is
`n + B + 2T + 3`. `trace_window_of_run` proves that enough blank reserve on
both sides yields an actual #568 `LocalTrace` of constant width.
`windowVerifierTableau_iff_language` proves the complete semantic
correspondence for every `ClassNP` witness. `accepting_trace_state_lt` excludes
missing states, whose default instruction rejects. `windowWidth_polynomial`
uses the explicit polynomial

```text
coefficient = certBound.coefficient + 2 * clockPolynomial.coefficient + 4
degree      = certBound.degree + clockPolynomial.degree + 1
```

`RunCNF` compiles their state, head, tape, and accepting-trace constraints.
`InitialCNF` compiles the initial input/certificate constraints and joins them
to this formula in `CookLevin.tableauCNF`.

## Local CNF combinators

`LocalCNF.implies` compiles a conjunction of premise literals implying a
disjunction of conclusion literals into a single clause. An empty conclusion
forbids the premise; an empty premise forces the conclusion.
`implies_models` proves this contract for each assignment.

`oneHot base size` combines an at-least-one clause with pairwise exclusions.
`oneHot_models` proves selection of exactly one value in the bounded domain;
the empty domain is unsatisfiable. It enumerates value pairs rather than
whole configurations or certificates. `oneHot_encoded_size` bounds its
encoded bit length by

```text
2 * (size² + 1) * (1 + (size + 2) * (base + size + 1))
```

`cnf_encoded_size` also provides a general bound for formulas with bounded
variable identifiers and clause width. Both bounds use the actual unary
literal encoding, including delimiters.

## Shared circuit CNF compiler

`CircuitCNF` compiles the existing `Issue532.Circuits` NAND programs. Each
`gateCNF o i j` contributes three clauses asserting `o = NAND(i,j)`.
`gateCNF_models` includes repeated input wires. `circuitCNF_models` proves
assignment-by-assignment agreement with the existing `wires` evaluator for
well-formed circuits, given agreement on the input prefix.

`acceptingCNF` also asserts the last wire. When there are no wires, it emits
an empty clause, matching the existing constant-false output convention.
`acceptingCNF_iff` proves satisfiability exactly when an input of the specified
length makes the circuit output true. The formula uses the existing wire
indices, without enumerating input assignments. Its actual encoded bit length
is bounded by

```text
8 * (3 * gateCount + 1) * (inputCount + gateCount + 1)
```

If the total wire count is at most `p.eval inputLength`,
`acceptingCNF_polynomial_size` supplies `circuitPolynomial p`:

```text
coefficient = 8 * (3 * p.coefficient + 1) * (p.coefficient + 1)
degree      = 2 * p.degree
```

The shared `Circuits` modules now contain `wires_length`, `wire_wires_lt`,
and `toAssign_wire`. The shared `Machines` modules contain `ticks_length`
and `encodeLit_length`. Existing qualified Rocq helper names and
`Idea41.wires_length` delegate to these proofs. This removes repeated proof
logic without changing the established circuit or CNF definitions.

This compiler does not yet supply a verifier-to-circuit simulation or the
input-dependent finite reduction machine. Its correctness and size theorem
therefore do not establish `SATHard`.

## Shared machine instruction CNF

`MachineCNF` reuses `LocalCNF.oneHot` and `implies` to compile every bounded
state/scanned-symbol pair in the shared `Machine.instruction` table, including
ragged rows whose missing columns reject. The three disjoint variable groups
select a state, one of the four alphabet symbols, and an instruction code.
`instructionCode_injective` distinguishes both halting answers and every
move's next state, written symbol, and direction.

`dispatchCNF_models` proves the assignment-by-assignment correspondence.
`dispatchAssignment_models` constructs a model for every valid state and
every symbol at any variable offset. `dispatchCNF_wrong_instruction` proves
that changing the output to a different instruction fails even when all
three exactly-one constraints hold. An empty program has no dispatch model.
`dispatchCNF_instruction` recovers the actual instruction, and
`dispatchCNF_step` connects it to the original shared `step` and `moveHead` on
the complete configuration; neither introduces new machine semantics.

Let `Q = program.length` and `K = instructionBound`, one more than the largest
code in the finite dispatch table. The CNF has at most `Q² + 4Q + K² + 19`
clauses, its variable identifiers are below `base + Q + K + 4`, and its
clause width is at most `Q + K + 7`. Its actual unary encoded bit length is
bounded by

```text
2 * (Q² + 4Q + K² + 19) * (1 + (Q + K + 7) * (base + Q + K + 5))
```

`dispatchCNF_polynomial_size` provides the explicit polynomial when the
variable offset is polynomially bounded. `Q` and `K` are constants of the
fixed verifier, including any large next-state identifiers in its table.
The reusable bounded lookup compiler's contracts and size bounds are also
registered in the assumption manifest, with the same names in both provers.
`LocalCNF` exports its existing one-hot clause count and variable/width
contracts so this compiler uses those proofs directly.

This formula selects an instruction. `SuccessorCNF` supplies the head/tape
wiring and charged successor constraints below. `InitialCNF` supplies
initial/certificate constraints; `RunCNF` supplies row activity and final acceptance.
No input-dependent reduction machine or hardness theorem follows from these
local compilers alone.

## Finite-row successor CNF

`SuccessorCNF.lean` and `SuccessorCNF.v` use matching public names and the
existing `Config`, `moveHead`, `step`, and `encodeCNF`. For `Q` machine states,
window width `W`, and row offset `b`, the layout is:

| Variables | Meaning |
| --- | --- |
| `b + q`, `q < Q` | Selected state. |
| `b + Q + h`, `h < W` | Selected head position. |
| `b + Q + W + 4*i + s`, `i < W`, `s < 4` | Symbol at tape cell `i`. |

`flatten` reverses the stored left tape and appends the head and right tape.
`rowCNF` enforces one-hot selections. `decodeRow` searches these bounded
groups constructively; `rowCNF_models` extracts a represented configuration
from **every** satisfying row assignment, and `decodeRow_represents` proves
uniqueness. `rowAssignment_represents` constructs an assignment for every
configuration with span `W` and state below `Q`.

`transitionCNF` enumerates only states, head positions, symbols, and cells.
The selected instruction forces the next state and head, overwrites the old
head cell, and preserves every other cell. Halts, missing instructions,
out-of-range destination states, and moves outside the window forbid their
guard. `moveHead_flatten` and `moveHead_matches` connect these clauses to the
original two-way tape semantics. Crossing an edge grows that machine's span;
such a move cannot be a same-width successor.

`successorCNF` combines two rows with these transition clauses.
`successorCNF_step` proves equivalence to `step m c = inr d` for represented
rows. `successorCNF_models` extracts both rows directly from satisfaction;
`successorCNF_sound` consequently has no representation premise.
`successorCNF_decoded_wrong_successor` rejects an incorrect decoded move.
These conclusions concern one move, including a move into a configuration
that will halt; they do not encode the accepting halt itself.

The checked clause-count bound is

```text
C = 2*(Q*Q + W*W + 17*W + 2) + 4*Q*W*(4*W + 2).
```

For row offsets `b` and `next`, variables are below
`V = max b next + Q + 5*W`, and clauses have width at most `L = Q + W + 6`.
`successorCNF_encoded_size` proves encoded bit length at most
`2*C*(1 + L*(V + 1))`, counting unary identifiers and delimiters. `RunCNF`
combines this bound with the row-count and offset bounds below;
the initial/certificate clauses remain outside its polynomial.

## Bounded accepting-trace CNF

`RunCNF.lean` and `RunCNF.v` compile a nonempty accepting prefix of at most
`T` configurations with window width `W`. Each row reserves `Q + 5W + 1`
variables: the existing state/head/tape block and one stop bit. A true stop
bit requires the current instruction to halt accepting. A false stop bit
requires the existing `successorCNF` and the remaining trace formula.
Continuation clauses carry every preceding row's continuation guard, so
rows after an accepting halt require no selections. Clock zero emits an
empty clause; a move on the last possible row is also impossible.

`runCNF_sound` extracts a represented, accepting #568 `LocalTrace` from
every satisfying assignment. `runCNF_complete` proves the reverse direction
for each represented trace within the clock. `traceAssignment` supplies a
canonical model for every fixed-width accepting trace; `decodeTrace_represents`
recovers that exact trace. Consequently `runCNF_iff` characterizes
satisfiability by the existence of such a trace, without an assignment or
state-bound premise. `runCNF_wrong_successor_rejected` rejects a decoded
incorrect edge even if its final row accepts. `runCNF_rejecting_unsatisfiable`
proves unsatisfiability whenever the machine rejects every configuration.

Let `C = successorCount m W` and
`R = Q² + W² + 17W + 2 + 4QW + C`. The checked bounds are:

```text
clauses       <= T*R + 1
variable IDs  <  b + (T + 1)*(Q + 5W + 1)
clause width  <= Q + W + 6 + T
encoded bits  <= 2*(T*R + 1)*
                  (1 + (Q + W + 6 + T)*(b + (T + 1)*(Q + 5W + 1) + 1))
```

The variable bound includes an extra row mentioned syntactically by the
guarded successor clauses at the final clock position. `runPolynomial m b w t`
is an explicit `Polynomial` assembled from polynomial bounds for offset,
width, and clock. `runCNF_polynomial_size` checks that envelope against the
actual unary `encodeCNF` length. Shared `Complexity.polyAdd` and `polyMul`
compute coefficients and degrees; their checked evaluation lemmas also
serve the existing polynomial-closure proofs.

This fragment permits any first configuration. Its rejection theorem concerns
machines that reject
every configuration. Arbitrary rejecting verifiers may accept from other
configurations. `CookLevin.tableauCNF` includes the initial input/certificate
wiring, and its rejection theorem needs only rejection of the prescribed inputs.

## Initial row and complete tableau

`InitialCNF` builds one symbolic source per tape cell. A constant source forces
the selected tape symbol. A certificate source uses three implications to
select blank, zero, or one from its presence/value variables. Thus the formula
does not enumerate certificates. `windowSources_eval` equates those sources
with the flattened, blank-padded `verifierInitial` for both verifier constructors.
The initial row has state zero and head position `T`.

`initialCNF_models` proves the exact row-representation contract, including
the uniqueness of its state, head, and every tape cell. At offset `b`, the
fragment has at most `Q² + W² + 20W + 4` clauses, variables below `b + Q + 5W`,
and clause width at most `Q + W + 6`. `initialPolynomial` bounds its actual
unary encoded length using the shared polynomial arithmetic.

`CookLevin.tableauCNF np x` joins the certificate, initial-row, and accepting-run
fragments with row zero at `2B + 1`. `tableauCNF_sound` decodes a model to the
existing `WindowVerifierTableau`. `tableauCNF_complete` constructs a joint
model while preserving the decoded certificate and the exact trace. Certificate
variables are below the row offset, so this construction preserves both parts.
`tableauCNF_iff` proves satisfiability exactly when `np.language x = true`, for
every shared `ClassNP` witness. The three full-formula negative theorems reject
rejecting verifiers, attempted overlong certificates, and wrong decoded successors.

`sizePolynomial` is the shared polynomial sum of `certificatePolynomial`,
`initialPolynomial`, and `runPolynomial`, with the checked offset, width, and
clock bounds substituted. `tableauCNF_encoded_size` bounds the bit length of
the original unary `encodeCNF`, including identifiers and delimiters. This
output-size theorem does not supply the reduction machine's running-time proof.

## Charged output primitive

`ConstantEmitter.emitter w` is an explicit finite machine table over the
shared alphabet. It marks the origin, erases the input, returns to the marker,
writes the fixed word `w`, and restores the head to the leftmost cell. The
table has `4 + 2 * w.length` states. `emitter_computes` proves the existing
`Computes` contract, including the exit state, empty left tape, output bits,
and trailing blanks, within the polynomial `⟨4 + 2 * w.length, 1⟩`.
`write_block` and `return_block` expose reusable instruction-table contracts
with one charged step per written bit or head move.

The output is fixed when the table is constructed. This primitive supplies
neither the counters nor the input-dependent tableau emission required by
`Computes red (fun x => encodeCNF (tableauCNF np x)) r`.

## Charged input retention and unary counting

`UnaryCounter.counter` has nine states independent of the input and counter
value. Its tape contains a blank cursor, the remaining input, a separator,
and `k` unary ticks. Each iteration retains one input bit to the left of the
cursor, appends a tick, and returns to the cursor. `counter_reaches` proves
the complete tape contract for arbitrary input `x`, existing left tape, and
counter value, in exactly `|x| * (2 * (|x| + k) + 6) + 2` charged instructions.
`countTime_polynomial` bounds that time by `8 * (|x| + k + 1)^2`.

`prepare` constructs the cursor and delimiter from `initial x`, retaining
every bit, in exactly `2 * |x| + 4` steps, including empty input.
`countedInput` sequences the two tables into one fixed 16-state machine.
`countedInput_reaches` starts from the actual shared-model input and finishes
with the original bits on the reversed left tape, a blank cursor, separator,
and exactly `|x|` unary ticks. `inputTime_polynomial` proves the explicit bound
`12 * (|x| + 1)^2`. The exit state is 16, so further blocks can be sequenced.

These blocks reuse shared `Machines.scan_right`, `scan_left`, `Reaches.trans`
(`reaches_trans` in Rocq), and `reaches_append_right`. The scan lemmas preserve
arbitrary symbol lists and count one instruction per scanned cell; the shifted
composition lemma preserves the exact charged computation. The fixed emitter
also reuses the shared transitivity proof.

This is a tape-block interface. Formula emission, counter arithmetic for its
indices, final tape restoration, and the complete reduction's `Computes`
contract remain required.

## Verification and limits

The paired [regressions](../../../experiments/issue624/) cover zero bounds,
empty certificates, both bit values, short and full certificates, suffix holes,
noncanonical blanks, overlong certificates, nonzero offsets, and exact
encoding lengths. Concrete all-accepting and all-rejecting `ClassNP` witnesses
exercise both verifier constructors. Clock probes distinguish a decoded empty
certificate from a one-bit certificate at the same capacity. The bad-edge
case reuses `wrong_successor_rejected`, even though its final row accepts.
A concrete NP witness for the empty-input language has a valid two-row model
and rejects the same trace after replacing its successor with the bad row.
This exercises the predicate with a zero certificate bound and clock two.
Window regressions check two-way padding, exact span, state bounds, and an
invalid successor. CNF regressions reject zero, missing, and multiple selected
values and check forbidden or inactive constraints. Emitter regressions run
the concrete table on empty inputs/outputs and on inputs shorter and longer
than its output. Circuit-CNF regressions cover zero wires, a satisfiable
NAND circuit, an unsatisfiable contradiction circuit, incorrect gate outputs,
and the polynomial bound with unary wire identifiers. Run-CNF regressions
cover immediate and two-row acceptance, inactive suffixes with arbitrary
values, premature halts, missing accepting termination, zero/short clocks,
wrong successors, empty domains, and unary and polynomial size bounds.
Full-tableau regressions compare the same assignment across fragments: it
represents a bounded certificate and an accepting prefix from state one, but
fails the full initial row for a verifier that rejects from state zero. Wrong
head and certificate-bit assignments satisfy row one-hot constraints and fail
initial wiring. Concrete full models cover empty/short/full certificates,
zero bounds, both constructors, and exact certificate/trace decoding.

The certificate CNF alone is always satisfiable. The rejection-as-unsatisfiable-CNF
criterion in #624 is proved for the complete `CookLevin.tableauCNF`.

Assumption reports are attached in
[ASSUMPTIONS.md](../../../experiments/issue624/ASSUMPTIONS.md).
The source and enforced prover audits list the completed public conclusions
in `scripts/proof_status.json`. Lean uses only `propext`, `Classical.choice`, and `Quot.sound`;
Rocq uses no global assumptions. There are no admissions or new axioms.

```sh
lake build
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
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
bash experiments/issue624/check.sh all
```

Local toolchains: Lean 4.34.1 and Rocq 9.2. CI uses Rocq 9.0. The original
regression probes failed because these modules did not exist; logs are kept
locally under `ci-logs/`.

## Remaining construction

1. Build counters and copy/emission loops over the shared four-symbol alphabet
   and prove `Computes red (fun x => encodeCNF (tableauCNF np x)) r` for an
   explicit polynomial `r`, with the required final tape/head configuration.
2. Assemble `satHard` and `cookLevin`, then remove the existing hardness
   premises and update the Idea dossiers. Keep those premises until this step.

The shared model supplies sequencing (`compose_run`), charged scans and
input retention/counting, and the fixed-output primitive above. A general
counter-arithmetic/copy/tableau-emission compiler remains to be constructed. A finite CNF function
or its output-size bound cannot stand in for the `Computes` proof. Enumerating
all certificates or configurations would lose the required polynomial bound.
Importing [Gäher–Kunze's construction](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20)
requires a checked model simulation; this PR introduces no such import.

Refs #624, #568, #567, #532. The work plan is in
[PLAN.md](../../../experiments/issue624/PLAN.md); the current continuation is
tracked in [COMPLETION_PLAN.md](../../../experiments/issue624/COMPLETION_PLAN.md).
