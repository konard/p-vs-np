# Certificate and verifier-tableau regressions

These paired regression files exercise the certified prerequisites in
[`proofs/experiments/issue624`](../../proofs/experiments/issue624/).
They do not certify full tableau CNF or SAT hardness. The semantic predicate
still carries an explicit trace whose constraints have not been encoded.

After building the imported modules, run:

```sh
lake env lean experiments/issue624/CertificateRegression.lean
rocq compile -Q proofs proofs -Q experiments experiments experiments/issue624/CertificateRegression.v
```

The Lean regression is an explicit CI step; the Rocq regression is included
in `_CoqProject` and the whole-project build. Both print assumption reports
for the main conclusions. The complete manifest audit output for these
modules is recorded in [ASSUMPTIONS.md](ASSUMPTIONS.md).

Two small interactive inputs preserve the diagnostics used while developing
the Rocq proofs. They show intermediate goals, then complete their proofs.
They are `.in` files because they are diagnostic sessions rather than library
modules. All inputs are finite; neither probe performs a stress experiment.

```sh
rocq repl -quiet -Q proofs proofs < experiments/issue624/certificate_probe.in
rocq repl -quiet -Q proofs proofs < experiments/issue624/tableau_probe.in
```

[PLAN.md](PLAN.md) tracks the completed prerequisites and the remaining
Cook–Levin construction. #624 must remain open.
