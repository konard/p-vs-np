#!/usr/bin/env bash
# Check that the 2-SAT counterexamples in the Kardash refutation are proved
# without the file's informal axioms (issue #587).
set -euo pipefail

cd "$(dirname "$0")/../.."
audit_dir=$(mktemp -d)
audit_log="$audit_dir/audit.log"
trap 'rm -rf "$audit_dir"' EXIT

refutation=proofs/attempts/sergey-kardash-2011-peqnp/refutation

case "${1:-}" in
  --lean)
    lake build 'proofs.attempts.«sergey-kardash-2011-peqnp».refutation.lean.KardashRefutation' \
      > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    lake env lean experiments/issue587/Audit.lean > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    expected=$(grep -c '^#print axioms ' experiments/issue587/Audit.lean)
    checked=$(grep -Ec "depends on axioms: \[|does not depend on any axioms" "$audit_log" || true)
    unexpected=$(grep -o 'depends on axioms: \[.*\]' "$audit_log" |
      sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | sed 's/^ *//' |
      grep -Ev '^(propext|Quot\.sound|Classical\.choice)$' || true)
    if [ "$checked" -ne "$expected" ] || [ -n "$unexpected" ]; then
      cat "$audit_log" >&2
      echo "Lean: audited $checked of $expected results; unexpected axioms: ${unexpected:-none}" >&2
      exit 1
    fi
    echo "Lean: $checked 2-SAT results use only standard axioms"
    ;;
  --rocq)
    # Audit.v.in is appended to a copy so the normal Rocq build ignores it.
    cat "$refutation/rocq/KardashRefutation.v" experiments/issue587/Audit.v.in \
      > "$audit_dir/KardashAudit.v"
    rocq compile -Q . '' "$audit_dir/KardashAudit.v" > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    expected=$(grep -c '^Print Assumptions ' experiments/issue587/Audit.v.in)
    closed=$(grep -c '^Closed under the global context$' "$audit_log" || true)
    if [ "$closed" -ne "$expected" ]; then
      cat "$audit_log" >&2
      echo "Rocq: expected $expected closed results, got $closed" >&2
      exit 1
    fi
    echo "Rocq: $closed 2-SAT results are closed under the global context"
    ;;
  *)
    echo "Usage: $0 --lean|--rocq" >&2
    exit 2
    ;;
esac
