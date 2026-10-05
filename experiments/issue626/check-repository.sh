#!/usr/bin/env bash
# Repository-wide non-prover CI checks; logs can be redirected by the caller.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 scripts/check_gubin_audit.py
python3 -m unittest scripts.test_check_attempt_structure scripts.test_check_proof_status scripts.test_list_issues -v
python3 scripts/check_proof_status.py
python3 experiments/issue578/check_paper_lp.py
for issue in 577 580 584 532 587 588; do
  python3 -m unittest discover -s "experiments/issue${issue}" -p 'test_*.py' -v
done
python3 experiments/issue579/check_claims.py
bash experiments/issue7/check_claims_mutations.sh
python3 experiments/issue532/check_dossiers.py
python3 -m unittest discover -s experiments/sat_solvers -p 'test_*.py' -v
python3 experiments/issue588/admission_inventory.py
python3 -m unittest experiments.issue611.test_rocq_project -v
