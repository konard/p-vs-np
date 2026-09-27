"""Tests for the issue #588 admission inventory."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from admission_inventory import inventory  # noqa: E402


class AdmissionInventoryTests(unittest.TestCase):
    def build(self, files: dict[str, str]) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name, text in files.items():
                path = root / "proofs" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            return inventory(root)

    def test_ignores_comments_strings_and_identifiers(self):
        report = self.build({
            "a/proof/lean/A.lean": (
                "-- sorry\n/- sorry /- nested sorry -/ -/\n"
                "def s := \"sorry\"\ndef sorry_free := 1\n"
                "theorem t : True := by sorry\n"
            ),
            "a/proof/rocq/A.v": (
                "(* Admitted. (* nested admit *) *)\n"
                "Definition s := \"Admitted\".\nDefinition admitted_free := 1.\n"
                "Lemma l : True. Proof. admit. Admitted.\n"
            ),
        })
        self.assertEqual(report["lean"]["admissions"], 1)
        self.assertEqual(report["rocq"]["admissions"], 2)

    def test_counts_refutation_files_separately(self):
        report = self.build({
            "a/refutation/lean/R.lean": "theorem r : True := sorry\n",
            "a/refutation/lean/S.lean": "theorem s : True := trivial\n",
            "a/proof/lean/P.lean": "theorem p : True := sorry\n",
        })
        self.assertEqual(report["lean"], {
            "files": 3,
            "admissions": 2,
            "files_with_admissions": 2,
            "refutation_files": 2,
            "refutation_files_with_admissions": 1,
        })


if __name__ == "__main__":
    unittest.main()
