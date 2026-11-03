# Assumption audit probe

Status at 2026-11-03: a historical probe for issue #576 (closed). CI does not
run it; CI runs `scripts/check_proof_status.py` instead.

`assumption_probe.lean` records the initial Lean `#print axioms` queries used
to identify the shared model's logical dependencies. Run it after building the
two imported modules with `lake env lean experiments/issue576/assumption_probe.lean`.
The production audit and approved theorem list are in
`scripts/check_proof_status.py` and `scripts/proof_status.json` (78 rows per
prover; recount with
`python3 -I -c "import json; d=json.load(open('scripts/proof_status.json')); print(len(d['lean']), len(d['rocq']))"`).
