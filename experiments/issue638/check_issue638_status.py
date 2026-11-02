#!/usr/bin/env python3
"""Run the certified-result audit on the issue #638 entries only.

Lightweight local check. CI runs the full `scripts/check_proof_status.py`.
Usage (after building `proofs.experiments.issue638.lean.ETH` and compiling
`proofs/experiments/issue638/rocq/ETH.v`):
    python3 experiments/issue638/check_issue638_status.py
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("check_proof_status", ROOT / "scripts/check_proof_status.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

manifest = json.loads((ROOT / "scripts/proof_status.json").read_text(encoding="utf-8"))
subset = {lang: [e for e in manifest[lang] if "/issue638/" in e["source"]] for lang in ("lean", "rocq")}
failures = module.audit(ROOT, subset, ["lean", "rocq"], True)
if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
print(f"issue #638 audit passed: {len(subset['lean'])} Lean and {len(subset['rocq'])} Rocq theorems")
