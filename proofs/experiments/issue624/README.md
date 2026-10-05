# Cook–Levin certificate and verifier-tableau prerequisites

**Status: a preparatory part of #624's first slice. The issue remains open.**
The complete `tableauCNF`, its polynomial encoded-size bound, the single-tape
reduction machine, `satHard`, and unconditional P = NP bridges remain to be
constructed. This directory certifies the variable-length certificate fragment
and its connection to the existing bounded trace semantics.

Classification: **known theorem mechanized**, for these prerequisites only.
Nothing here establishes an answer to P versus NP.

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
`n + certBound.eval n + maxClock n + 2` tape cells. This envelope does not
replace the actual acceptance clock in the semantic predicate.

## Verification and limits

The paired [regressions](../../../experiments/issue624/) cover zero bounds,
empty certificates, both bit values, short and full certificates, suffix holes,
noncanonical blanks, overlong certificates, nonzero offsets, and exact
encoding lengths. Concrete all-accepting and all-rejecting `ClassNP` witnesses
exercise both verifier constructors. Clock probes distinguish a decoded empty
certificate from a one-bit certificate at the same capacity. The bad-edge
case reuses `wrong_successor_rejected`, even though its final row accepts.

The rejecting-verifier and wrong-successor results concern **the semantic
`VerifierTableau` predicate**. The certificate CNF alone is always satisfiable;
it does not express machine acceptance. The full rejection-as-unsatisfiable-CNF
criterion in #624 is therefore still outstanding.

Assumption reports are attached in
[ASSUMPTIONS.md](../../../experiments/issue624/ASSUMPTIONS.md).
The source and enforced prover audits list the completed public conclusions
in `scripts/proof_status.json`. Lean uses only `propext` and `Quot.sound`;
Rocq uses no global assumptions. There are no admissions or new axioms.

```sh
lake build
lake env lean experiments/issue624/CertificateRegression.lean
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
python3 scripts/check_proof_status.py
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

Local toolchains: Lean 4.34.1 and Rocq 9.2. CI uses Rocq 9.0. The original
regression probes failed because these modules did not exist; logs are kept
locally under `ci-logs/`.

## Remaining construction

1. Encode the configurations' finite state, tape contents, head position,
   represented lengths/boundaries, transitions, and the accepting final row
   into CNF. Relate each model to this semantic interface in both directions.
2. Combine that construction's bounds with the certificate fragment's bound,
   counting all variable identifiers under the unary encoding.
3. Build counters and copy/emission loops over the shared four-symbol alphabet
   and prove `Computes red (fun x => encodeCNF (tableauCNF np x)) r` for an
   explicit polynomial `r`, with the required final tape/head configuration.
4. Assemble `satHard` and `cookLevin`, then remove the existing hardness
   premises and update the Idea dossiers. Keep those premises until this step.

The shared model currently supplies sequencing (`compose_run`), but no
verified general counter/copy/tableau-emission compiler. A finite CNF function
or its output-size bound cannot stand in for the `Computes` proof. Enumerating
all certificates or configurations would lose the required polynomial bound.
Importing [Gäher–Kunze's construction](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2021.20)
requires a checked model simulation; this PR introduces no such import.

Refs #624, #568, #567, #532. The work plan is in
[PLAN.md](../../../experiments/issue624/PLAN.md).
