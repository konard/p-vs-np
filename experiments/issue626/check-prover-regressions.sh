#!/usr/bin/env bash
# Existing prover regressions from verification.yml, after a full build.
set -euo pipefail
cd "$(dirname "$0")/../.."
bash experiments/issue575/check.sh
python3 -m unittest experiments.issue614.test_framework -v
bash experiments/issue586/check.sh
python3 experiments/issue585/check_guidance.py
lake env lean experiments/issue574/PolynomialRegression.lean
lake env lean experiments/issue567/DecoderRegression.lean
lean experiments/issue7_shoenfield_absoluteness.lean
lean experiments/issue7_undecidability_formalization.lean
lake env lean experiments/issue572/Independent.lean
lake env lean experiments/issue568/TraceRegression.lean
python3 experiments/issue532_vacuity/check.py
bash experiments/issue571/check.sh
if lake_test_output=$(lake test 2>&1); then
  printf '%s\n' "$lake_test_output"
elif [[ "$lake_test_output" =~ ^error:\ .+:\ no\ test\ driver\ configured$ ]]; then
  echo "No Lake test driver configured"
else
  printf '%s\n' "$lake_test_output" >&2
  exit 1
fi
python3 experiments/issue570/check_contradiction.py --lean
bash experiments/issue573/check.sh --lean
bash experiments/issue587/check.sh --lean
python3 experiments/issue570/check_contradiction.py --rocq
bash experiments/issue573/check.sh --rocq
bash experiments/issue587/check.sh --rocq
