#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."
audit_dir=$(mktemp -d)
audit_log="$audit_dir/audit.log"
trap 'rm -rf "$audit_dir"' EXIT

case "${1:-}" in
  --lean)
    lake build proofs.p_eq_np.lean.PvsNP > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    if lake env lean experiments/issue573/AuditBefore.lean > "$audit_log" 2>&1; then
      echo 'Issue #573 regression: an arbitrary Boolean map is still a reduction in Lean' >&2
      exit 1
    fi
    if ! grep -Fq 'expected to have type' "$audit_log" ||
       ! grep -Fq 'PEqNP.PolyTimeComputable' "$audit_log"; then
      cat "$audit_log" >&2
      echo 'Lean rejected the audit for an unexpected reason' >&2
      exit 1
    fi
    echo 'Lean: arbitrary Boolean map rejected without a computation certificate'
    ;;
  --rocq)
    # The intentionally failing source uses .v.in so the full Rocq CI build
    # does not pick it up as a normal proof file.
    rocq compile -Q . '' proofs/complexity/rocq/Complexity.v > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    rocq compile -Q . '' proofs/p_eq_np/rocq/PvsNP.v > "$audit_log" 2>&1 || {
      cat "$audit_log" >&2
      exit 1
    }
    cp experiments/issue573/AuditBefore.v.in "$audit_dir/AuditBefore.v"
    if rocq compile -Q . '' "$audit_dir/AuditBefore.v" > "$audit_log" 2>&1; then
      echo 'Issue #573 regression: an arbitrary Boolean map is still a reduction in Rocq' >&2
      exit 1
    fi
    if ! grep -Fq 'AuditBefore.v' "$audit_log" ||
       ! grep -Eq 'Not the right number of missing arguments|expected.*poly_time_computable' "$audit_log"; then
      cat "$audit_log" >&2
      echo 'Rocq rejected the audit for an unexpected reason' >&2
      exit 1
    fi
    echo 'Rocq: arbitrary Boolean map rejected without a computation certificate'
    ;;
  *)
    echo "Usage: $0 --lean|--rocq" >&2
    exit 2
    ;;
esac
