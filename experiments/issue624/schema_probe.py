#!/usr/bin/env python3
"""Show Rocq's remaining goals at the end of one schema proof.

Example: python3 experiments/issue624/schema_probe.py initialSchema_eq
The temporary probe uses the current module, so schema data is never copied
into an experiment. Successful proofs report that no goals remain.
"""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("theorem")
    parser.add_argument("--log", type=Path, default=ROOT / "ci-logs/schema-probe.log")
    args = parser.parse_args()
    source = (ROOT / "proofs/experiments/issue624/rocq/Schema.v").read_text()
    declaration = re.search(
        r"(?m)^Theorem " + re.escape(args.theorem) + r"\s*:", source
    )
    if declaration is None:
        parser.error(f"unknown schema theorem: {args.theorem}")
    end = source.index("\nQed.", declaration.end())
    probe = source[:end] + "\nShow.\nAbort.\nEnd Schema.\n"
    args.log.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="issue624_schema_") as directory:
        path = Path(directory) / "SchemaProbe.v"
        path.write_text(probe)
        with args.log.open("w") as log:
            result = subprocess.run(
                ["rocq", "compile", "-Q", ".", "", str(path)],
                cwd=ROOT,
                stdout=log,
                stderr=subprocess.STDOUT,
            )
    print(f"Rocq exited {result.returncode}; goals saved to {args.log}")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
