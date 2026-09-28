#!/usr/bin/env python3
"""Count admissions under proofs/, ignoring comments and string literals.

Issue #588 reported 393 Lean ``sorry`` occurrences in 115 files and 480 Rocq
admissions in 119 files at c4a7803. This script recomputes those numbers for a
checkout so the closure report can compare the audit with the current tree.
The counts describe unfinished historical material; certified conclusions are
audited separately by scripts/check_proof_status.py.

Usage: python3 experiments/issue588/admission_inventory.py [--root DIR] [--json]
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from check_proof_status import strip_comments_and_strings  # noqa: E402


PATTERNS = {
    "lean": (".lean", re.compile(r"(?<![\w.'])sorry(?![\w'])")),
    "rocq": (".v", re.compile(r"(?<![\w.'])(?:Admitted|admit)(?![\w'])")),
}


def inventory(root: Path) -> dict:
    report = {}
    for language, (suffix, pattern) in PATTERNS.items():
        files = sorted((root / "proofs").rglob(f"*{suffix}"))
        counts = {}
        for path in files:
            text = strip_comments_and_strings(path.read_text(encoding="utf-8"), language)
            hits = len(pattern.findall(text))
            if hits:
                counts[path.relative_to(root).as_posix()] = hits
        refutations = [f for f in files if "/refutation/" in f.as_posix()]
        report[language] = {
            "files": len(files),
            "admissions": sum(counts.values()),
            "files_with_admissions": len(counts),
            "refutation_files": len(refutations),
            "refutation_files_with_admissions": sum(
                1 for f in refutations if f.relative_to(root).as_posix() in counts
            ),
        }
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--json", action="store_true", help="print machine-readable output")
    args = parser.parse_args()
    report = inventory(args.root.resolve())
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    for language, data in report.items():
        print(
            f"{language}: {data['admissions']} admissions in "
            f"{data['files_with_admissions']}/{data['files']} files; "
            f"refutation/: {data['refutation_files_with_admissions']}/"
            f"{data['refutation_files']} files contain admissions"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
