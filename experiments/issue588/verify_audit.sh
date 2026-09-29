#!/usr/bin/env bash
# Re-run every regression check added for the defects linked from issue #588.
#
# Usage: bash experiments/issue588/verify_audit.sh [python] [lean] [rocq] [agda]
# With no arguments all four groups run. A requested group whose tool is not
# installed fails instead of being skipped (see issue #584). Without a local
# agda binary, the Agda group uses the Docker image pinned by CI.
set -euo pipefail

cd "$(dirname "$0")/../.."

groups=("$@")
if [ ${#groups[@]} -eq 0 ]; then
  groups=(python lean rocq agda)
fi

step() {
  printf '\n=== %s\n' "$*"
  "$@"
}

require() {
  if ! command -v "$1" > /dev/null; then
    echo "error: $1 is required for the $2 checks" >&2
    exit 2
  fi
}

run_python() {
  require python3 python
  step python3 scripts/check_gubin_audit.py                                   # 578
  step python3 -m unittest scripts.test_check_attempt_structure -v            # 581 582 583
  step python3 -m unittest scripts.test_check_proof_status -v                 # 576
  step python3 scripts/check_proof_status.py                                  # 576
  step python3 experiments/issue578/check_paper_lp.py                         # 578
  step python3 -m unittest discover -s experiments/issue577 -p 'test_*.py' -v # 577
  step python3 -m unittest discover -s experiments/issue580 -p 'test_*.py' -v # 580
  step python3 experiments/issue579/check_claims.py                           # 579
  step python3 -m unittest discover -s experiments/issue584 -p 'test_*.py' -v # 584
  step python3 -m unittest discover -s experiments/issue587 -p 'test_*.py' -v # 587
  step python3 scripts/check_attempt_structure.py --offline --quiet           # 581 582
  step python3 -m unittest discover -s experiments/issue588 -p 'test_*.py' -v
  step python3 -m unittest experiments.issue611.test_rocq_project -v          # 611
  step python3 experiments/issue588/admission_inventory.py
}

run_lean() {
  require lake lean
  step python3 experiments/issue585/check_guidance.py                         # 585
  step bash experiments/issue575/check.sh                                     # 575
  step lake build
  step bash experiments/issue586/check.sh                                     # 586
  step lake env lean experiments/issue574/PolynomialRegression.lean           # 574
  step lean experiments/issue7_shoenfield_absoluteness.lean                   # 579
  step lean experiments/issue7_undecidability_formalization.lean              # 579
  step lake env lean experiments/issue572/Independent.lean                    # 572
  step bash experiments/issue571/check.sh                                     # 571
  step python3 experiments/issue570/check_contradiction.py --lean             # 570
  step bash experiments/issue573/check.sh --lean                              # 573
  step bash experiments/issue587/check.sh --lean                              # 587
  step python3 scripts/check_proof_status.py --lean                           # 576
}

run_rocq() {
  require rocq rocq
  require make rocq
  step python3 -m unittest experiments.issue611.test_rocq_project -v
  step rocq makefile -f _CoqProject -o Makefile.coq
  step make -f Makefile.coq
  step python3 experiments/issue570/check_contradiction.py --rocq             # 570
  step bash experiments/issue573/check.sh --rocq                              # 573
  step bash experiments/issue587/check.sh --rocq                              # 587
  step python3 scripts/check_proof_status.py --rocq                           # 576
}

run_agda() {
  local files=(proofs/complexity/agda/Complexity.agda
    proofs/p_vs_np_decidable/agda/PSubsetNP.agda
    proofs/p_vs_np_decidable/agda/PvsNPDecidable.agda
    proofs/p_not_equal_np/agda/PNotEqualNP.agda
    proofs/p_vs_np_undecidable/agda/PvsNPUndecidable.agda
    experiments/issue572/Independent.agda)                                    # 571 572
  if command -v agda > /dev/null; then
    for file in "${files[@]}"; do
      step agda -i . "$file"
    done
  else
    # Fall back to the image pinned in .github/workflows/verification.yml.
    require docker agda
    step docker run --rm --user "$(id -u):$(id -g)" -v "$PWD:/work" -w /work \
      ghcr.io/codewars/agda@sha256:d56bf738f23befbd02352bd207483bbefe513de612683747ebc35675549e9d0e \
      sh -c 'set -e; for file in "$@"; do echo "agda $file"; agda -i . "$file"; done' agda "${files[@]}"
  fi
}

for group in "${groups[@]}"; do
  case "$group" in
    python|lean|rocq|agda) "run_$group" ;;
    *) echo "error: unknown group '$group' (expected python, lean, rocq, agda)" >&2; exit 2 ;;
  esac
done

printf '\nAll requested issue #588 regression groups passed: %s\n' "${groups[*]}"
