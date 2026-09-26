#!/usr/bin/env python3
"""Reject unproved assumptions in the Gubin 2010 proof files.

Both proof assistants already compile these files in CI. This extra check
catches the exact regression from issue #578: turning an unsupported historical
claim or an impossible geometric property into an axiom or admission.
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
ATTEMPT = ROOT / "proofs/attempts/sergey-gubin-2010-peqnp"
FILES = [
    ATTEMPT / section / language / filename
    for section, language, filename in (
        ("proof", "lean", "GubinProof.lean"),
        ("proof", "rocq", "GubinProof.v"),
        ("refutation", "lean", "GubinRefutation.lean"),
        ("refutation", "rocq", "GubinRefutation.v"),
        ("refutation", "lean", "GubinPaperCounterexample.lean"),
        ("refutation", "rocq", "GubinPaperCounterexample.v"),
    )
]
UNPROVED = re.compile(
    r"\b(?:axiom|Axiom|sorry|admit|Admitted|constant|opaque|Parameter|Conjecture|native_decide)\b"
)


def main() -> int:
    failures = []
    for path in FILES:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if UNPROVED.search(line):
                failures.append(f"{path.relative_to(ROOT)}:{number}: {line.strip()}")
    if failures:
        print("Unproved Gubin audit declarations found:", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("Gubin audit files contain no axioms or admissions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
