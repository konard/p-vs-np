#!/usr/bin/env python3
"""Check finite counterexamples to reusing existing tables for circuit evaluation.

The separate certified evaluator and completion gate establish CircuitSAT membership.
Each prover proves the negation of the proposed evaluator run contract.
"""

import argparse
from pathlib import Path
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from experiments.issue567.check_machines import compile_probe


def check(language: str) -> None:
    logs = HERE / "logs"
    logs.mkdir(exist_ok=True)
    suffix = ".lean" if language == "lean" else ".v"
    source = (HERE / f"VerifierReuse{suffix}.in").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="verifier_reuse_", dir=HERE) as directory:
        path = Path(directory) / f"VerifierReuse{suffix}"
        path.write_text(source, encoding="utf-8")
        log = logs / f"{language}-verifier-reuse.log"
        result = compile_probe(language, path, log)
        if result.returncode:
            raise RuntimeError(f"{language}: reuse counterexample failed; see {log}\n"
                               + (result.stdout + result.stderr).rstrip())
    print(f"{language}: syntax and SAT tables cannot implement verifyCircuit directly")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--rocq", action="store_true")
    args = parser.parse_args()
    selected = [language for language in ("lean", "rocq") if getattr(args, language)]
    for language in selected or ["lean", "rocq"]:
        check(language)


if __name__ == "__main__":
    main()
