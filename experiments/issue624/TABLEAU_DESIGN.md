# Remaining tableau and reduction construction

The accepting-trace formula is checked. Initial input/certificate wiring and
the reduction machine remain construction obligations. The checked contracts
are listed in [the proof README](../../proofs/experiments/issue624/README.md).

For input length `n`, use `B = certBound.eval n`, `T = maxClock np n`,
`W = windowWidth np n`, and `Q = verifierMachine.program.length`.
`FixedWindow.windowVerifierTableau_iff_language` provides a constant-width
semantic trace, with the initial head `T` cells from the left edge, and
`accepting_trace_state_lt` bounds every active state by `Q`.
`SuccessorCNF` compiles each row and charged move using the original instruction
lookup. `RunCNF` integrates these clauses with accepting halts and clock
exhaustion. Its two model directions use #568's original `LocalTrace`.
`acceptingRun_timeLimit` recovers the actual certificate-dependent clock from
any accepting trace; the envelope cannot introduce a slower accepting run.

## Finite variable layout

Keep the existing certificate variables in `[0, 2B + 1)`. The implemented
`RunCNF` layout puts row zero at an offset `b >= 2B + 1`. Successive offsets
are `b + i*(Q + 5W + 1)`. Each block contains state variables of size `Q`,
head variables of size `W`, `W` four-symbol tape groups, and a stop bit at
relative offset `Q + 5W`.

`SuccessorCNF.rowCNF_models` and `decodeRow_represents` provide constructive
extraction and uniqueness for each block. `RunCNF.traceAssignment_represents`
constructs the combined row/stop model, and `decodeTrace_represents` proves
exact extraction. Each row's continuation guards every clause in its suffix;
after a true stop bit, suffix variables are unconstrained. Regression models
use both all-false and all-true suffixes. Clock zero and empty state/head
domains are rejected. Certificate/row disjointness and joint initial-row model
construction remain to be proved. No group enumerates configurations,
traces, or certificates.

## Initial row and transitions

Initialize row zero with state zero, head position `T`, and the padded tape.
For `.paired`, place input bits, the separator, then certificate cells, whose
presence/value literals distinguish zero from blank. For `.ignoreCertificate`,
place only input bits. Unused cells contain blank. Initial-row clauses must
relate each decoded certificate assignment to the exact padded configuration.
These clauses remain unimplemented.

The checked recursion is:

```text
runCNF(0)     = [[]]
runCNF(k + 1) = rowCNF ++ (stop -> haltCNF) ++
                         (!stop -> (successorCNF ++ runCNF(k)))
```

`haltCNF_step` requires the selected instruction to halt accepting.
`successorCNF_step` requires a genuine move, including the written cell and
preservation of all others. Missing table entries reject in the shared model.
Every continuation ultimately requires an accepting halt before exhausting
the clock. `SuccessorCNF.moveHead_matches` proves that decoding commutes with
each move, including reversed cells to the left of the head and both edges.
`successorCNF_sound` extracts a genuine charged move from any satisfying
two-row assignment. Both edge crossings are rejected rather than wrapped or
truncated. `RunCNF.runCNF_sound` and `runCNF_complete` integrate accepting
prefixes. Only initial-row/certificate integration remains missing from this
part of the full formula.

## Encoded size

The checked trace variable bound is `b + (T + 1)*(Q + 5W + 1)`. It includes
an extra row referenced by the guarded successor clauses at the last clock
position, even though that continuation cannot be active in a model.
Pairwise exactly-one constraints are quadratic in each group's domain size.
Copying the other tape cells costs a further factor of `W` per transition
guard. These loops enumerate polynomially many rows, cells, state/symbol
values, and value pairs.

`RunCNF.runCNF_length`, `runCNF_bounds`, and `runCNF_encoded_size` extend
the successor bounds to the complete trace prefix. `runPolynomial` and
`runCNF_polynomial_size` give an explicit shared `Polynomial` envelope for
polynomially bounded offsets, windows, and clocks, counting unary identifiers
and delimiters. Nested guards make the maximum clause width grow linearly
with `T`; clause count remains linear in `T` times the per-row bound.
The full builder still needs to add the initial clauses and combine this
bound with the certificate fragment's bound. Substitute `maxClock_polynomial`
and `windowWidth_polynomial` for the trace parameters.

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
