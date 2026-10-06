#!/usr/bin/env python3
"""Preserve kernel assumption reports for the charged unary-counter blocks."""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.check_proof_status import query_assumptions


def entries(language):
    suffix = "lean" if language == "lean" else "v"
    source = f"proofs/experiments/issue624/{language}/UnaryCounter.{suffix}"
    keyword = "theorem" if language == "lean" else "Theorem"
    names = re.findall(rf"(?m)^{keyword} (\w+)", (ROOT / source).read_text())
    prefix = "Issue624.UnaryCounter" if language == "lean" else "UnaryCounter"
    result = [{"source": source, "theorem": f"{prefix}.{name}"} for name in names]
    shared = (
        "Reaches.trans" if language == "lean" else "reaches_trans",
        "scan_right",
        "scan_left",
        "reaches_append_right",
    )
    shared_prefix = "Issue532.Machines" if language == "lean" else "Machines"
    result.extend(
        {
            "source": f"proofs/experiments/issue532/{language}/Machines.{suffix}",
            "theorem": f"{shared_prefix}.{name}",
        }
        for name in shared
    )
    return result


if __name__ == "__main__":
    reports = {}
    for language in ("lean", "rocq"):
        reports[language] = entries(language)
        for entry in reports[language]:
            entry["allowed_axioms"] = sorted(query_assumptions(ROOT, language, entry))
    print(json.dumps(reports, indent=2))
