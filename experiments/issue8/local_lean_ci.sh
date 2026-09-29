#!/usr/bin/env bash
# Local replay of the Lean historical CI job (see .github/workflows/verification.yml).
set -e
bash experiments/issue575/check.sh
lake build
python3 -m unittest experiments.issue614.test_framework -v
bash experiments/issue586/check.sh
python3 experiments/issue585/check_guidance.py
lake env lean experiments/issue574/PolynomialRegression.lean
lean experiments/issue7_shoenfield_absoluteness.lean
lean experiments/issue7_undecidability_formalization.lean
lake env lean experiments/issue572/Independent.lean
python3 experiments/issue532_vacuity/check.py
bash experiments/issue571/check.sh
python3 experiments/issue570/check_contradiction.py --lean
bash experiments/issue573/check.sh --lean
bash experiments/issue587/check.sh --lean
echo "LOCAL LEAN CI OK"
