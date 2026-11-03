#!/usr/bin/env bash
# Issue #638: regression tests for check_axioms_log.sh (no Lean needed).
# Usage: bash experiments/issue638/test_check_axioms_log.sh
set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
check="$here/check_axioms_log.sh"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
failures=0

expect() {  # <expected exit: 0|1> <name> <log text> <count> <theorem>...
  local want="$1" name="$2" text="$3"; shift 3
  printf '%b' "$text" > "$tmp/$name.log"
  bash "$check" "$tmp/$name.log" "$@" > "$tmp/$name.out" 2>&1
  local got=$?
  if [ "$got" -eq "$want" ]; then
    echo "ok   $name (exit $got)"
  else
    echo "FAIL $name: exit $got, expected $want"; cat "$tmp/$name.out"
    failures=$((failures + 1))
  fi
}

std="[propext, Classical.choice, Quot.sound]"
# Lines as printed by the anthropic-eth job of run 41619710887.
eth="'MainResults.ethIsFalse' depends on axioms: $std\n'MainResults.mainTheorem' depends on axioms: $std\n"

expect 0 eth-ok "$eth" 2 MainResults.ethIsFalse MainResults.mainTheorem
expect 1 empty-log "" 2 MainResults.ethIsFalse
expect 1 wrong-count "$eth" 3 MainResults.ethIsFalse
expect 1 missing-theorem "$eth" 2 MainResults.other
expect 1 dot-is-literal "'MainResultsXethIsFalse' depends on axioms: $std\n" 1 MainResults.ethIsFalse
expect 1 sorry "'A.b' depends on axioms: [propext, sorryAx]\n" 1 A.b
expect 1 wrapped-extra-axiom "'A.b' depends on axioms: [propext,\n  myAxiom,\n  Quot.sound]\n" 1 A.b
expect 0 wrapped-standard "'A.b' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]\n" 1 A.b
expect 0 no-axioms "'A.b' does not depend on any axioms\n" 1 A.b
expect 1 error-only "error: unknown constant 'A.b'\n" 1 A.b

[ "$failures" -eq 0 ] && echo "all tests passed" || { echo "$failures test(s) failed"; exit 1; }
