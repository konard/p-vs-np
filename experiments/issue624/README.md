# Cook–Levin construction regressions

These paired regression files exercise the certified prerequisites in
[`proofs/experiments/issue624`](../../proofs/experiments/issue624/).
`CircuitCNFRegression` checks the shared NAND compiler against satisfiable
and unsatisfiable circuits, wrong gate outputs, and unary encoding bounds.
These regressions do not certify full tableau CNF or SAT hardness. The semantic predicate
still carries an explicit trace whose constraints have not been encoded.

After building the imported modules, run:

```sh
lake env lean experiments/issue624/CertificateRegression.lean
lake env lean experiments/issue624/WindowRegression.lean
lake env lean experiments/issue624/CNFRegression.lean
lake env lean experiments/issue624/EmitterRegression.lean
lake env lean experiments/issue624/CircuitCNFRegression.lean
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
```

[PLAN.md](PLAN.md) tracks the completed prerequisites and the remaining
Cook–Levin construction. #624 must remain open.

`check.sh` reproduces the local Python, Lean, Rocq, and pinned-container Agda
workflow checks. Select an individual suite with `python`, `lean`, `rocq`, or
`agda`. Save large logs under `ci-logs/`.

[TABLEAU_DESIGN.md](TABLEAU_DESIGN.md) records the proposed variable layout,
transition guards, size obligations, and the input-dependent emitter's
missing machine operations. It is a plan rather than an implemented formula.
