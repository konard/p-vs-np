#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

# Compile the entire refutation, including contradictory_is_unsat. This failed
# at line 108 in the Lean 4.34.1 run reported by issue #575.
lean "${1:-proofs/attempts/antano-maknickas-2011-peqnp/refutation/lean/MaknickasRefutation.lean}"
