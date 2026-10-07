#!/usr/bin/env python3
"""Capture both kernels' assumptions for the dynamic register continuation."""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from experiments.issue624.register_assumptions import entries
from scripts.check_proof_status import query_assumptions


SHARED = {
    "lean": ["reaches_of_similar", "BlankPad.trans", "Similar.trans",
             "retarget_instruction", "retarget_moveHead", "retarget_reaches"],
    "rocq": ["reaches_of_similar", "blankPad_trans", "similar_trans",
             "retarget_instruction", "retarget_moveHead", "retarget_reaches"],
}
REGISTER = {
    "pop_states", "clear_states", "delete_shift", "delete_positive", "delete_empty",
    "pop_positive", "pop_empty", "clearTime_succ", "clearTarget_inside",
    "clearTarget_positive", "clearTarget_empty", "clear_reaches", "clearTime_polynomial",
    "clear_then_compile_reaches", "clear_then_cost_polynomial",
}


def reports():
    result = {}
    for language in ("lean", "rocq"):
        suffix = "lean" if language == "lean" else "v"
        prefix = "Issue532.Machines" if language == "lean" else "Machines"
        candidates = [entry for entry in entries(language)
                      if entry["theorem"].rsplit(".", 1)[1] in REGISTER] + [
            {"source": f"proofs/experiments/issue532/{language}/Machines.{suffix}",
             "theorem": f"{prefix}.{name}"} for name in SHARED[language]
        ]
        result[language] = candidates
        for entry in result[language]:
            entry["allowed_axioms"] = sorted(query_assumptions(ROOT, language, entry))
    return result


if __name__ == "__main__":
    print(json.dumps(reports(), indent=2))
