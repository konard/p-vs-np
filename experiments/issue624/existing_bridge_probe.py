#!/usr/bin/env python3
"""Check the existing Idea 36 bridge without discharging its non-SAT premises."""

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.check_issue624_completion import ALLOWED, REQUIREMENTS
from scripts.check_proof_status import MANIFEST, ROOT, query_assumptions


def check(language):
    requirement = next(item for item in REQUIREMENTS
                       if item.lean_name == "Issue532.Idea36.exactRounding_gives_pEqualsNP")
    entries = {entry["theorem"]: entry for entry in json.loads(MANIFEST.read_text())[language]}
    entry = entries[requirement.name(language)]
    assumptions = query_assumptions(ROOT, language, entry, expected_type=requirement.type(language))
    if assumptions != set(entry["allowed_axioms"]) or not assumptions <= ALLOWED[language]:
        raise ValueError(f"{entry['theorem']}: unexpected assumptions: {sorted(assumptions)}")
    print(f"{language} {entry['theorem']}: completion type checked; assumptions: "
          f"{', '.join(sorted(assumptions)) or '(none)'}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--lean", action="store_true")
    group.add_argument("--rocq", action="store_true")
    arguments = parser.parse_args()
    check("lean" if arguments.lean else "rocq")
