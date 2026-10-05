#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
# Build the full manifest's dependencies before querying all certified results.
lake build
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
lake env lean -j 1 -M 2048 experiments/issue626/SimulationRegression.lean
(
  ulimit -v 2097152
  rocq compile -Q . '' experiments/issue626/CompilerRegression.v
  rocq compile -Q . '' experiments/issue626/SimulationRegression.v
)
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
