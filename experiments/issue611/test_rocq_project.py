"""Keep the dependency-aware Rocq project in sync with its source files."""

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "_CoqProject"


class RocqProjectTest(unittest.TestCase):
    def test_project_lists_every_rocq_source(self):
        lines = [
            line.strip()
            for line in PROJECT.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        ]
        self.assertEqual(lines[0], '-Q . ""')
        sources = lines[1:]
        self.assertEqual(len(sources), len(set(sources)))
        self.assertEqual(
            set(sources),
            {path.relative_to(ROOT).as_posix() for path in ROOT.rglob("*.v")},
        )


if __name__ == "__main__":
    unittest.main()
