#!/usr/bin/env python3
"""Check the exact acceptance target of issue 625 (currently unresolved).

This diagnostic exits nonzero until the unconditional paired membership
theorems exist. It is separate from the passing syntax-slice regression suite.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--rocq", action="store_true")
    args = parser.parse_args()
    selected = [language for language in ("lean", "rocq") if getattr(args, language)]
    logs = HERE / "logs"
    logs.mkdir(exist_ok=True)
    failed = False
    with tempfile.TemporaryDirectory(prefix="membership_", dir=HERE) as directory:
        for language in selected or ["lean", "rocq"]:
            suffix = ".lean" if language == "lean" else ".v"
            path = Path(directory) / f"MembershipTarget{suffix}"
            path.write_text((HERE / f"MembershipTarget{suffix}.in").read_text(), encoding="utf-8")
            command = ["lake", "env", "lean"] if language == "lean" else ["rocq", "compile", "-Q", ".", ""]
            result = subprocess.run([*command, str(path)], cwd=ROOT, capture_output=True, text=True)
            log = logs / f"{language}-membership.log"
            log.write_text(result.stdout + result.stderr, encoding="utf-8")
            failed |= bool(result.returncode)
            print(f"{language}: {'FAILED' if result.returncode else 'passed'}; {log.relative_to(ROOT)}")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
