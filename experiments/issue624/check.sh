#!/usr/bin/env bash
# Reproduce the repository verification jobs locally, including issue 624.
set -euo pipefail
cd "$(dirname "$0")/../.."

check_python() {
  python3 scripts/check_gubin_audit.py
  python3 -m unittest scripts.test_check_attempt_structure scripts.test_check_proof_status scripts.test_list_issues -v
  python3 -m unittest experiments.issue624.test_completion experiments.issue624.test_completion_workflow -v
  python3 scripts/check_proof_status.py
  python3 experiments/issue578/check_paper_lp.py
  for issue in issue577 issue580 issue584 issue532 issue587 sat_solvers issue588; do
    python3 -m unittest discover -s "experiments/$issue" -p 'test_*.py' -v
  done
  python3 experiments/issue579/check_claims.py
  bash experiments/issue7/check_claims_mutations.sh
  python3 experiments/issue532/check_dossiers.py
  python3 experiments/issue588/admission_inventory.py
}

check_lean() {
  bash experiments/issue575/check.sh
  lake build
  python3 -m unittest experiments.issue614.test_framework -v
  bash experiments/issue586/check.sh
  python3 experiments/issue585/check_guidance.py
  for file in experiments/issue574/PolynomialRegression.lean experiments/issue567/DecoderRegression.lean \
    experiments/issue7_shoenfield_absoluteness.lean experiments/issue7_undecidability_formalization.lean \
    experiments/issue572/Independent.lean experiments/issue568/TraceRegression.lean \
    experiments/issue624/CertificateRegression.lean experiments/issue624/WindowRegression.lean \
    experiments/issue624/CNFRegression.lean experiments/issue624/EmitterRegression.lean \
    experiments/issue624/CircuitCNFRegression.lean; do
    lake env lean "$file"
  done
  python3 experiments/issue532_vacuity/check.py
  bash experiments/issue571/check.sh
  if lake_test_output=$(lake test 2>&1); then
    printf '%s\n' "$lake_test_output"
  elif [[ "$lake_test_output" =~ ^error:\ .+:\ no\ test\ driver\ configured$ ]]; then
    printf '%s\n' 'No Lake test driver configured'
  else
    printf '%s\n' "$lake_test_output" >&2
    return 1
  fi
  python3 experiments/issue570/check_contradiction.py --lean
  bash experiments/issue573/check.sh --lean
  bash experiments/issue587/check.sh --lean
  python3 scripts/check_proof_status.py --lean
  python3 experiments/issue624/check_completion_kernels.py --lean
  python3 experiments/issue624/check_completion_types.py --lean
}

check_rocq() {
  python3 -m unittest experiments.issue611.test_rocq_project -v
  rocq makefile -f _CoqProject -o Makefile.coq
  make -f Makefile.coq
  python3 experiments/issue570/check_contradiction.py --rocq
  bash experiments/issue573/check.sh --rocq
  bash experiments/issue587/check.sh --rocq
  python3 scripts/check_proof_status.py --rocq
  python3 experiments/issue624/check_completion_kernels.py --rocq
  python3 experiments/issue624/check_completion_types.py --rocq
}

check_agda() {
  docker run --rm --user "$(id -u):$(id -g)" -v "$PWD:/work" -w /work \
    ghcr.io/codewars/agda@sha256:d56bf738f23befbd02352bd207483bbefe513de612683747ebc35675549e9d0e \
    sh -c 'set -e
      agda -i . proofs/complexity/agda/Complexity.agda
      agda -i . proofs/p_vs_np_decidable/agda/PSubsetNP.agda
      agda -i . proofs/p_vs_np_decidable/agda/PvsNPDecidable.agda
      agda -i . proofs/p_not_equal_np/agda/PNotEqualNP.agda
      agda -i . proofs/p_vs_np_undecidable/agda/PvsNPUndecidable.agda
      agda -i . experiments/issue572/Independent.agda'
}

case "${1:-all}" in
  python) check_python ;;
  lean) check_lean ;;
  rocq) check_rocq ;;
  agda) check_agda ;;
  completion)
    python3 scripts/check_issue624_completion.py
    check_lean
    check_rocq
    python3 scripts/check_issue624_completion.py --lean
    python3 scripts/check_issue624_completion.py --rocq
    ;;
  all) check_python; check_lean; check_rocq; check_agda ;;
  *) printf 'Usage: %s [python|lean|rocq|agda|all|completion]\n' "$0" >&2; exit 2 ;;
esac
