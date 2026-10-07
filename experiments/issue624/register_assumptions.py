#!/usr/bin/env python3
"""Capture kernel assumptions for the charged register insertion contracts."""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.check_proof_status import query_assumptions


def entries(language):
    suffix = "lean" if language == "lean" else "v"
    source = f"proofs/experiments/issue624/{language}/RegisterMachine.{suffix}"
    keyword = "theorem" if language == "lean" else "Theorem"
    names = re.findall(rf"\b{keyword} (\w+)", (ROOT / source).read_text())
    prefix = "Issue624.RegisterMachine" if language == "lean" else "RegisterMachine"
    return [{"source": source, "theorem": f"{prefix}.{name}"} for name in names]


if __name__ == "__main__":
    reports = {}
    for language in ("lean", "rocq"):
        reports[language] = entries(language)
        for entry in reports[language]:
            entry["allowed_axioms"] = sorted(query_assumptions(ROOT, language, entry))
    print(json.dumps(reports, indent=2))
