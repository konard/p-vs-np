#!/usr/bin/env python3
"""Compile the contributor guide's core Lean example without Mathlib."""

import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
guide = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
section = guide.split("#### Core Lean example\n", 1)
if len(section) != 2:
    raise SystemExit("CONTRIBUTING.md: missing the Core Lean example")
match = re.search(
    r"^```lean\n(.*?)^```",
    section[1].split("\n### ", 1)[0],
    re.MULTILINE | re.DOTALL,
)
if match is None:
    raise SystemExit("CONTRIBUTING.md: missing the Core Lean example")

example = match.group(1)
for tactic in ("omega", "simp", "decide"):
    if not re.search(rf"\b{tactic}\b", example):
        raise SystemExit(f"CONTRIBUTING.md: example does not demonstrate {tactic}")
if '#print "supported"' not in example:
    raise SystemExit('CONTRIBUTING.md: example does not demonstrate #print "supported"')
if re.search(r"\bsorry\b", example):
    raise SystemExit("CONTRIBUTING.md: example must not use sorry")

with tempfile.TemporaryDirectory() as directory:
    source = Path(directory) / "CoreTactics.lean"
    source.write_text(example, encoding="utf-8")
    subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT, check=True)

print("Contributor guide core Lean example compiles without Mathlib")
