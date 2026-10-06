#!/usr/bin/env python3
"""Check the implemented tableau endpoints against the unchanged completion types.

This does not claim full issue completion: the reduction machine and hardness
endpoints remain subject to scripts/check_issue624_completion.py.
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.check_issue624_completion import ALLOWED, REQUIREMENTS
from scripts.check_proof_status import MANIFEST, ROOT, query_assumptions


def check(language):
    entries = {entry["theorem"]: entry for entry in json.loads(MANIFEST.read_text())[language]}
    count = 0
    for requirement in REQUIREMENTS:
        if not requirement.lean_name.startswith("Issue624.CookLevin.tableauCNF_"):
            continue
        entry = entries[requirement.name(language)]
        preamble = ("open Complexity Issue532.Machines\n" if language == "lean" else
                    "From Stdlib Require Import List.\n"
                    "From proofs.experiments.issue532.rocq Require Import Machines.\n"
                    "Import ListNotations Complexity.Complexity.\n")
        assumptions = query_assumptions(ROOT, language, entry,
                                        expected_type=requirement.type(language), preamble=preamble)
        if assumptions != set(entry["allowed_axioms"]) or not assumptions <= ALLOWED[language]:
            raise ValueError(f"{entry['theorem']}: unexpected assumptions: {sorted(assumptions)}")
        print(f"{language} {entry['theorem']}: completion type checked; assumptions: "
              f"{', '.join(sorted(assumptions)) or '(none)'}")
        count += 1
    assert count == 7, f"expected seven tableau endpoints, checked {count}"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--lean", action="store_true")
    group.add_argument("--rocq", action="store_true")
    arguments = parser.parse_args()
    check("lean" if arguments.lean else "rocq")
