#!/usr/bin/env bash
# Local counterparts of the repository's Python and prover regression checks.
# Run after lake build and make -f Makefile.coq. The unresolved membership
# diagnostic is separate and deliberately excluded from this passing suite.
set -euo pipefail
cd "$(dirname "$0")/../.."
python3 scripts/check_gubin_audit.py
python3 -m unittest scripts.test_check_attempt_structure -v
python3 -m unittest scripts.test_check_proof_status -v
python3 -m unittest scripts.test_list_issues -v
python3 scripts/check_proof_status.py
python3 experiments/issue578/check_paper_lp.py
python3 -m unittest discover -s experiments/issue577 -p 'test_*.py' -v
python3 -m unittest discover -s experiments/issue580 -p 'test_*.py' -v
python3 experiments/issue579/check_claims.py
bash experiments/issue7/check_claims_mutations.sh
python3 -m unittest discover -s experiments/issue584 -p 'test_*.py' -v
python3 -m unittest discover -s experiments/issue532 -p 'test_*.py' -v
python3 experiments/issue532/check_dossiers.py
python3 -m unittest discover -s experiments/issue587 -p 'test_*.py' -v
python3 -m unittest discover -s experiments/sat_solvers -p 'test_*.py' -v
python3 -m unittest discover -s experiments/issue588 -p 'test_*.py' -v
python3 experiments/issue588/admission_inventory.py
bash experiments/issue575/check.sh
python3 -m unittest experiments.issue614.test_framework -v
bash experiments/issue586/check.sh
python3 experiments/issue585/check_guidance.py
lake env lean experiments/issue574/PolynomialRegression.lean
lake env lean experiments/issue567/DecoderRegression.lean
python3 experiments/issue567/check_machines.py --lean --rocq
lean experiments/issue7_shoenfield_absoluteness.lean
lean experiments/issue7_undecidability_formalization.lean
lake env lean experiments/issue572/Independent.lean
lake env lean experiments/issue568/TraceRegression.lean
python3 experiments/issue532_vacuity/check.py
bash experiments/issue571/check.sh
python3 experiments/issue570/check_contradiction.py --lean --rocq
bash experiments/issue573/check.sh --lean
bash experiments/issue573/check.sh --rocq
bash experiments/issue587/check.sh --lean
bash experiments/issue587/check.sh --rocq
python3 -m unittest experiments.issue611.test_rocq_project -v
