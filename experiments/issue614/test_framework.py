"""Regression checks for the Williams framework on the pinned toolchains."""

import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class WilliamsFrameworkTests(unittest.TestCase):
    def test_lean_framework_compiles(self):
        result = subprocess.run(
            ["lake", "env", "lean", "proofs/experiments/WilliamsFramework.lean"],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
