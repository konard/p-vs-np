# Assumption audit probe

`assumption_probe.lean` records the initial Lean `#print axioms` queries used
to identify the shared model's logical dependencies. Run it after building the
two imported modules with `lake env lean experiments/issue576/assumption_probe.lean`.
The production audit and approved theorem list are in
`scripts/check_proof_status.py` and `scripts/proof_status.json`.
