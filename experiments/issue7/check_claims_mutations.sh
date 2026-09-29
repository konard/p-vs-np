#!/usr/bin/env bash
# Mutation test for the issue #7 clocked-SAT claim regressions in
# experiments/issue579/check_claims.py. Each mutation breaks one corrected
# claim in a scratch copy of the repository; the check must reject all of them.
# Run from the repository root: bash experiments/issue7/check_claims_mutations.sh
set -euo pipefail
root=$(pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
d=proofs/experiments/issue7

mutate() {
  local name=$1 file=$2 script=$3
  rm -rf "$work/repo" && mkdir -p "$work/repo"
  (cd "$root" && git ls-files -co --exclude-standard -z | xargs -0 cp --parents -t "$work/repo")
  sed -i "$script" "$work/repo/$file"
  if (cd "$work/repo" && python3 experiments/issue579/check_claims.py) >/dev/null 2>&1; then
    echo "NOT CAUGHT: $name"; exit 1
  fi
  echo "caught: $name"
}

mutate "Σ⁰₂ form with swapped quantifiers" $d/README.md 's/∃ m p, ∀ x, clockCheck m p x = true /∀ m p, ∃ x, clockCheck m p x = true /'
mutate "independence claimed" $d/README.md '$a Thus P vs NP is independent of ZFC.'
mutate "SATHard called proved" $d/README.md 's/and is still unproved in the/and holds in the/'
mutate "Rocq admission" $d/rocq/ClockedSAT.v 's/^Proof. intros m x. reflexivity. Qed./Proof. Admitted./'
mutate "Lean SATHard premise dropped" $d/lean/ClockedSAT.lean 's/pEqualsNP_of_clockedSAT (hard : SATHard)/pEqualsNP_of_clockedSAT/'
mutate "Lean axiom" $d/lean/ClockedSAT.lean '$a axiom bad : False'
(cd "$root" && python3 experiments/issue579/check_claims.py)
