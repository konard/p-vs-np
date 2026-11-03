#!/usr/bin/env bash
# Issue #638: check the output of `lake env lean <file with #print axioms>`.
#
# Usage: check_axioms_log.sh <log> <expected count> <theorem>...
#
# Fails unless
#   * the log is non-empty,
#   * it holds exactly <expected count> axiom reports, i.e. lines
#       'Name' depends on axioms: [...]   or   'Name' does not depend on any axioms
#     (one per `#print axioms` command),
#   * every <theorem> named on the command line has a report,
#   * no report names an axiom other than propext, Classical.choice and
#     Quot.sound (sorryAx included).
# The whole log is joined into one line before the axiom lists are read, so a
# list that Lean wraps over several lines is still checked.
set -euo pipefail

[ "$#" -ge 2 ] || { echo "usage: $0 <log> <expected count> <theorem>..." >&2; exit 2; }
log="$1"; expected="$2"; shift 2
fail() { echo "::error::$*"; exit 1; }

[ -s "$log" ] || fail "axioms log $log is empty or missing"

report_re="'[^']+' (depends on axioms: \[|does not depend on any axioms)"
reported="$(grep -cE "$report_re" "$log" || true)"
[ "$reported" -eq "$expected" ] \
  || fail "expected $expected axiom reports in $log, found $reported"

for t in "$@"; do
  grep -qE "'$(sed 's/[.[\*^$]/\\&/g' <<<"$t")' (depends on axioms|does not depend on any axioms)" "$log" \
    || fail "no axiom report for $t in $log"
done

if grep -q sorryAx "$log"; then
  fail "sorryAx in $log"
fi
leftover="$(tr '\n' ' ' < "$log" | grep -oE 'depends on axioms: \[[^]]*\]' \
  | sed -E 's/^depends on axioms: \[//; s/\]$//' | tr ',' '\n' | tr -d ' \r' \
  | grep -vxE 'propext|Quot\.sound|Classical\.choice|' || true)"
[ -z "$leftover" ] || fail "non-standard axioms in $log: $(echo $leftover)"

echo "axioms log $log: $reported reports, all named theorems present, standard axioms only"
