#!/usr/bin/env bash
set -euo pipefail

lake env lean experiments/issue571/Runtime.lean

audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
if lake env lean experiments/issue571/AuditBefore.lean > "$audit_log" 2>&1; then
  echo 'Issue #571 regression: the arbitrary-language proof still compiles' >&2
  exit 1
fi

# Check the relevant failure, not merely a changed import or input type.
if ! grep -q 'Fields missing: `machine`, `bound`, `terminates`' "$audit_log"; then
  cat "$audit_log" >&2
  echo 'Issue #571 regression failed for an unexpected reason' >&2
  exit 1
fi
