#!/usr/bin/env python3
"""Require the complete, certified deliverable of issue 625 in CI.

Compilation must establish unconditional CircuitSAT membership and all six
bridges without a membership premise. Fixed assumption limits and mandatory
manifest entries prevent a conditional helper or an admission from passing.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from scripts import check_proof_status as proof_status


IDEA41_TARGETS = (
    "circuitSATInNP",
    "pNotEqualsNP_of_not_fastCircuitSAT",
    "fastCircuitSAT_of_pEqualsNP",
    "pNotEqualsNP_of_nexpSubsetPPoly",
    "not_nexpSubsetPPoly_of_pEqualsNP",
)
ISSUE10_TARGETS = (
    "npNotSubsetP_of_not_fastCircuitSAT",
    "nexp_lower_bound_of_pEqualsNP",
)
ALLOWED_AXIOMS = {"lean": {"propext", "Classical.choice", "Quot.sound"}, "rocq": set()}


def required_entries(language: str) -> list[dict]:
    suffix = "lean" if language == "lean" else "v"
    entries = []
    for issue, module, targets in (
        ("issue532", "Idea41", IDEA41_TARGETS),
        ("issue10", "NPNotSubsetP", ISSUE10_TARGETS),
    ):
        namespace = f"Issue{issue[5:]}.{module}" if language == "lean" else module
        for name in targets:
            entries.append({
                "source": f"proofs/experiments/{issue}/{language}/{module}.{suffix}",
                "theorem": f"{namespace}.{name}",
                "allowed_axioms": sorted(ALLOWED_AXIOMS[language]),
            })
    return entries


def check_registration(manifest: dict, language: str) -> list[str]:
    failures = []
    for required in required_entries(language):
        name = required["theorem"]
        matching = [entry for entry in manifest[language] if entry["theorem"] == name]
        if len(matching) != 1:
            failures.append(f"{language}: {name} must have exactly one entry in scripts/proof_status.json")
        elif matching[0]["source"] != required["source"]:
            failures.append(f"{language}: {name} must be certified from {required['source']}")
        elif set(matching[0]["allowed_axioms"]) - ALLOWED_AXIOMS[language]:
            failures.append(f"{language}: {name} permits assumptions outside the completion gate's limits")
    return failures


def check(language: str, root: Path = ROOT, here: Path = HERE) -> list[str]:
    logs = here / "logs"
    logs.mkdir(exist_ok=True)
    (logs / f"{language}-assumptions.log").write_text(
        "Assumptions are queried only after both contracts compile without admissions.\n", encoding="utf-8",
    )
    entries = required_entries(language)
    manifest = json.loads((root / "scripts/proof_status.json").read_text(encoding="utf-8"))
    failures = check_registration(manifest, language)
    (logs / f"{language}-registration.log").write_text(
        "\n".join(failures) + "\n", encoding="utf-8",
    )
    # Scan the required modules and their imports even if their entries were
    # removed from the editable manifest. Compilation alone allows admissions.
    source_failures = proof_status.check_sources(root, proof_status.source_closure(root, entries))
    failures.extend(source_failures)
    (logs / f"{language}-sources.log").write_text(
        "\n".join(source_failures) + "\n", encoding="utf-8",
    )
    contracts_passed = True
    suffix = ".lean" if language == "lean" else ".v"
    command = ["lake", "env", "lean"] if language == "lean" else ["rocq", "compile", "-Q", ".", ""]
    with tempfile.TemporaryDirectory(prefix="membership_", dir=here) as directory:
        for name, label in (("MembershipTarget", "membership"), ("ConsequencesTarget", "consequences")):
            source = (here / f"{name}{suffix}.in").read_text(encoding="utf-8")
            path = Path(directory) / f"{name}{suffix}"
            path.write_text(source, encoding="utf-8")
            # Keep a stable copy because the temporary probe is deleted.
            # The source inventory includes every *.v, even in ignored logs.
            (logs / f"{language}-{label}{suffix}.in").write_text(source, encoding="utf-8")
            result = subprocess.run([*command, str(path)], cwd=root, capture_output=True, text=True)
            log = logs / f"{language}-{label}.log"
            log.write_text(result.stdout + result.stderr, encoding="utf-8")
            if result.returncode:
                contracts_passed = False
                failures.append(
                    f"{language}: {name} failed; see {log.relative_to(root)}\n"
                    + (result.stdout + result.stderr).rstrip()
                )

    if contracts_passed and not source_failures:
        reports = []
        registered = {entry["theorem"]: entry for entry in manifest[language]}
        # Query with fixed limits rather than trusting the manifest's allowlist.
        for entry in entries:
            try:
                assumptions = proof_status.query_assumptions(root, language, entry)
            except ValueError as error:
                reports.append(str(error))
                failures.append(str(error))
                continue
            report = f"{language} {entry['theorem']}: {', '.join(sorted(assumptions)) or '(none)'}"
            reports.append(report)
            if assumptions - ALLOWED_AXIOMS[language]:
                failures.append(f"{report}: unapproved assumptions")
            elif entry["theorem"] in registered and assumptions - set(
                registered[entry["theorem"]]["allowed_axioms"]
            ):
                failures.append(f"{report}: assumptions exceed scripts/proof_status.json registration")
        (logs / f"{language}-assumptions.log").write_text("\n".join(reports) + "\n", encoding="utf-8")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--rocq", action="store_true")
    args = parser.parse_args()
    selected = [language for language in ("lean", "rocq") if getattr(args, language)]
    failures = []
    for language in selected or ["lean", "rocq"]:
        try:
            failures.extend(check(language))
        except (OSError, ValueError, KeyError, TypeError) as error:
            failures.append(f"{language}: completion check failed: {error}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        print("Issue 625 is incomplete; circuit syntax recognition is insufficient.", file=sys.stderr)
        return 1
    print("Issue 625 completion checks passed for: " + ", ".join(selected or ["lean", "rocq"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
