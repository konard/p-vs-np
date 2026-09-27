#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

lake build 'proofs.attempts.«angela-weiss-2011-peqnp».refutation.lean.WeissRefutation'
output=$(lake env lean experiments/issue586/WeissGrowthRegression.lean)
printf '%s\n' "$output"
if grep -q 'sorryAx' <<< "$output"; then
  echo 'Weiss growth theorems still depend on sorryAx' >&2
  exit 1
fi
