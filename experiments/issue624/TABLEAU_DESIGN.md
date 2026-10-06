# Remaining tableau and reduction construction

This is a construction plan, not a certified formula or machine. The current
checked contracts are listed in [the proof README](../../proofs/experiments/issue624/README.md).

For input length `n`, use `B = certBound.eval n`, `T = maxClock np n`,
`W = windowWidth np n`, and `Q = verifierMachine.program.length`.
`FixedWindow.windowVerifierTableau_iff_language` provides a constant-width
semantic trace, with the initial head `T` cells from the left edge, and
`accepting_trace_state_lt` bounds every active state by `Q`.
`MachineCNF.dispatchCNF_models` now compiles the shared instruction table's
state/scanned-symbol lookup, with an injective instruction code and polynomial
unary encoding bound. Wire its scanned-symbol group to the tape cell chosen
by the row's head, guard it with row activity, and connect its instruction
output to the next row's state/head/tape constraints. The dispatch compiler
does not supply those connections. `SuccessorCNF` now supplies a separate
row-and-move compiler with the same instruction lookup; integrating activity
and accepting halts into the whole trace remains necessary.
`acceptingRun_timeLimit` recovers the actual certificate-dependent clock from
any accepting trace; the envelope cannot introduce a slower accepting run.

## Finite variable layout

Keep the existing certificate variables in `[0, 2B + 1)`. Allocate disjoint
blocks after them for:

- `T + 1` active-row bits, forced prefix-closed, with row zero active and
  sentinel row `T` inactive;
- `T` state groups of size `Q`;
- `T` head-position groups of size `W`;
- `T * W` symbol groups of size four.

Use `LocalCNF.oneHot` for state, head, and symbol groups. Variable uniqueness
and decoding need an arithmetic proof for these offsets. No group enumerates
configurations, traces, or certificates. `SuccessorCNF.rowCNF_models` and
`decodeRow_represents` now provide constructive extraction and uniqueness for
each block; `rowAssignment_represents` supplies its canonical model.
Disjointness and assembly across all row and certificate blocks remain to be
proved. Inactive rows can carry arbitrary
well-formed values. If `T = 0` or `Q = 0`, the corresponding formula should
be unsatisfiable, consistent with the impossibility of an accepting run.

## Initial row and transitions

Initialize row zero with state zero, head position `T`, and the padded tape.
For `.paired`, place input bits, the separator, then certificate cells, whose
presence/value literals distinguish zero from blank. For `.ignoreCertificate`,
place only input bits. Unused cells contain blank. Initial-row clauses must
relate each decoded certificate assignment to the exact padded configuration.

For each active row, state, head position, and scanned symbol, look up the
existing finite instruction table and guard clauses with those four literals.
`LocalCNF.implies` expresses each guarded consequent.

- An accepting halt forces the next row inactive.
- A rejecting halt forbids the guard.
- A move forces the next row active, the next state and head position, the
  written cell, and preservation of every other cell. Missing destination
  states and head moves outside the window forbid the guard.

The last possible active row must halt accepting; its successor is the
inactive sentinel. Missing table entries already mean rejecting halt in the
shared model. The decoded configuration must use reversed cells to the left
of the selected head and ordinary-order cells to its right. Proving that this
decoding commutes with each move, including the window boundary constraints,
is now proved by `SuccessorCNF.moveHead_matches` and `successorCNF_step`.
`successorCNF_sound` extracts a genuine charged move from any satisfying
two-row assignment. Both edge crossings are rejected rather than wrapped or
truncated. The active-prefix, initial-row, and accepting-halt integration is
still missing.

## Encoded size

The proposed variable count is `2B + 1 + (T + 1) + T*(Q + W + 4W)`.
Pairwise exactly-one constraints are quadratic in each group's domain size.
Copying the other tape cells costs at most a further factor of `W` per
transition guard. Thus the intended loops enumerate polynomially many
rows, cells, state/symbol values, and value pairs.

`SuccessorCNF` now has checked clause-count, variable-bound, clause-width,
and unary encoded-size bounds for one successor pair. These observations
are not a checked size theorem for the full tableau. The completed builder
needs explicit clause-count, maximum clause-width, and variable-bound lemmas.
`LocalCNF.cnf_encoded_size` then counts the unary identifier cost and clause
delimiters. Combine these bounds with `maxClock_polynomial`,
`windowWidth_polynomial`, and the certificate bound to produce an explicit
`Polynomial` for the whole encoded formula.

## Input-dependent machine emission

The reduction's table may depend on `np`, but must be fixed for all inputs
`x`. Constructing `emitter (encodeCNF (tableauCNF np x))` separately for each
`x` does not satisfy this quantifier order. `ConstantEmitter.emitter_computes`
only certifies a fixed output; its charged writing and return blocks are
primitives for a future emitter.

Still needed are bounded counters, input retention/copying, row/cell/value
loops, arithmetic for variable identifiers, unary literal-token emission,
and clause delimiters over the shared four-symbol tape alphabet. Each loop
requires a finite instruction table, tape invariant, charged `Reaches`
bound, and a final `Computes` proof. Neither classical choice of a formula
nor polynomial output length supplies these operations for free.

Only after formula correctness and this machine contract are proved can
`satHard` and `cookLevin` be assembled and the named hardness premises removed.
