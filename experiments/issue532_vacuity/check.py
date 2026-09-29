#!/usr/bin/env python3
"""Regression for the PR #569 vacuity review (issue #532).

`ReviewProofs.lean` is the reviewer's file, copied verbatim from the review.
The `IdeaNNVacuity.lean` files are the audit's trivialising proofs (see
`REPORT.md`). All of them compiled against commit 76ebd01, where the "open
obligations" had free cost functions or free classes.

Some of those files now fail only because a definition was renamed (the free
schemas became `...For`). A rename would make them fail too, so
`ReviewProofsRetargeted.lean` restates the reviewer's moves against the
current names. Files named `*Retargeted.lean` must fail without any
unknown-name error: every error must be a type or proof error.

After the move to the shared machine model, none of them may compile. Every
`theorem` in every file, except the auxiliary lemmas listed in `HELPERS`, must
produce its own error, and no error may come from the import header: a missing
module would make the whole file fail for a reason that says nothing about the
definitions.

Run after `lake build`, from the repository root:

    python3 experiments/issue532_vacuity/check.py
"""
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ERROR = re.compile(r"^(?P<file>[^\s:]+\.lean):(?P<line>\d+):\d+: error")
DECL = re.compile(r"^(?:private\s+)?theorem\s+(?P<name>\S+)")
IMPORT_FAILURE = ("unknown module prefix", "object file", "file not found")
NAME_ERROR = re.compile(r"error.*\b(unknown (identifier|constant|namespace))", re.IGNORECASE)

# Auxiliary lemmas of the audit files. They state nothing about an obligation
# (a correctness fact about a classical oracle, a lemma about CNFs, the bare
# inequality `0 ≤ p n`), so they may keep compiling.
HELPERS = {
    "Idea09Vacuity.lean": {"idea09_oracleRuns_monotone"},
    "Idea14Vacuity.lean": {"oneSided_trivial"},
    "Idea18Vacuity.lean": {"idea18_dcost_free"},
    "Idea25Vacuity.lean": {"unsat_emptyClause", "oracleSplit_spec"},
    "Idea26Vacuity.lean": {"unsat_emptyClause"},
    "Idea32Vacuity.lean": {"classicalSat_correct"},
    "Idea36Vacuity.lean": {"exists_min"},
    "Idea40Vacuity.lean": {"vars_posUnits", "posUnits_sat", "emptyClause_unsat"},
}


def theorem_ranges(lines):
    """Return (name, first_line, last_line) for each top-level theorem."""
    starts = []
    for number, line in enumerate(lines, 1):
        match = DECL.match(line)
        if match:
            starts.append((match["name"], number))
    ranges = []
    for index, (name, start) in enumerate(starts):
        end = starts[index + 1][1] - 1 if index + 1 < len(starts) else len(lines)
        ranges.append((name, start, end))
    return ranges


def check(path):
    source = path.read_text().splitlines()
    header_end = max(
        (n for n, l in enumerate(source, 1) if l.startswith("import ")), default=0
    )
    result = subprocess.run(
        ["lake", "env", "lean", str(path.relative_to(ROOT))],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    problems = []
    if result.returncode == 0:
        problems.append("compiles; the trivialising proofs still go through")
    if any(marker in output for marker in IMPORT_FAILURE):
        problems.append("an imported module is missing or not built")
    error_lines = [
        int(m["line"])
        for m in map(ERROR.match, output.splitlines())
        if m and m["file"].endswith(path.name)
    ]
    if any(line <= header_end for line in error_lines):
        problems.append("fails in the import header")
    if path.name.endswith("Retargeted.lean"):
        for line in output.splitlines():
            if NAME_ERROR.search(line):
                problems.append(f"fails on a name, not on the definition: {line}")
    helpers = HELPERS.get(path.name, set())
    ranges = [r for r in theorem_ranges(source) if r[0] not in helpers]
    if not ranges:
        problems.append("declares no trivialising theorem")
    for name, start, end in ranges:
        if not any(start <= line <= end for line in error_lines):
            problems.append(f"theorem `{name}` still compiles")
    return problems, output


def main():
    files = sorted(HERE.glob("*.lean"))
    if not files:
        print("no vacuity files found", file=sys.stderr)
        return 1
    failed = False
    for path in files:
        problems, output = check(path)
        if problems:
            failed = True
            print(f"FAIL {path.name}:", file=sys.stderr)
            for problem in problems:
                print(f"  {problem}", file=sys.stderr)
            print(output, file=sys.stderr)
        else:
            print(f"ok   {path.name}: every trivialising proof is rejected")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
