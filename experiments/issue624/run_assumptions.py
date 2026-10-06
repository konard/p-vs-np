#!/usr/bin/env python3
"""Query paired trace, initial-row, full-tableau and polynomial lemmas."""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.check_proof_status import query_assumptions


def entries(language):
    extension = "lean" if language == "lean" else "v"
    keyword = "theorem" if language == "lean" else "Theorem"
    results = []
    for module in ("RunCNF", "InitialCNF", "CookLevin"):
        source = f"proofs/experiments/issue624/{language}/{module}.{extension}"
        names = re.findall(rf"(?m)^(?:@\[[^\n]*\]\s*)?{keyword} (\w+)", (ROOT / source).read_text())
        prefix = f"Issue624.{module}" if language == "lean" else module
        results.extend({"source": source, "theorem": f"{prefix}.{name}"} for name in names)
    results.extend({
        "source": f"proofs/complexity/{language}/Complexity.{extension}",
        "theorem": f"Complexity.{name}",
    } for name in ("polyAdd_eval", "polyMul_eval"))
    return results


if __name__ == "__main__":
    lean, rocq = entries("lean"), entries("rocq")
    assert [e["theorem"].split(".")[-1] for e in lean] == [e["theorem"].split(".")[-1] for e in rocq]
    reports = {}
    for language, items in (("lean", lean), ("rocq", rocq)):
        for item in items:
            item["allowed_axioms"] = sorted(query_assumptions(ROOT, language, item))
        reports[language] = items
    print(json.dumps(reports, indent=2))
