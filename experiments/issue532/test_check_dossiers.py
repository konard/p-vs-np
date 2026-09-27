"""Regression tests for the issue #532 dossier checker."""

import tempfile
import unittest
from pathlib import Path

import check_dossiers


class CheckerUnitTests(unittest.TestCase):
    def check_source(self, language: str, source: str) -> list[str]:
        suffix = ".lean" if language == "lean" else ".v"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / f"Idea01{suffix}"
            path.write_text(source)
            return check_dossiers.check_prover_file(language, path, 1)

    def test_lean_admission_is_rejected_but_comment_is_not(self):
        body = "namespace Issue532.Idea01\ntheorem a : 1 = 1 := rfl\ntheorem b : 2 = 2 := rfl\n"
        self.assertEqual(self.check_source("lean", body + "-- no sorry here\n"), [])
        errors = self.check_source("lean", body + "theorem c : 3 = 4 := sorry\n")
        self.assertTrue(any("sorry" in error for error in errors))

    def test_trivial_conclusions_are_rejected(self):
        lean = "namespace Issue532.Idea01\ntheorem a : True := trivial\ntheorem b : 1 = 1 := rfl\n"
        self.assertTrue(any("True" in e for e in self.check_source("lean", lean)))
        rocq = "Theorem a : True.\nProof. exact I. Qed.\nTheorem b : 1 = 1.\nProof. reflexivity. Qed.\n"
        self.assertTrue(any("True" in e for e in self.check_source("rocq", rocq)))

    def test_rocq_axiom_and_missing_theorems_are_rejected(self):
        errors = self.check_source("rocq", "Axiom p : False.\n")
        self.assertTrue(any("Axiom" in error for error in errors))
        self.assertTrue(any("fewer than two" in error for error in errors))

    def test_table_names_reads_first_column_only(self):
        markdown = "\n".join([
            check_dossiers.SECTIONS[2],
            "| Theorem | Statement | Lean | Rocq |",
            "| --- | --- | --- | --- |",
            "| `alpha`, `beta` | uses `gamma` | [Lean](x) | [Rocq](y) |",
            check_dossiers.SECTIONS[3],
            "| `delta` | outside | a | b |",
        ])
        self.assertEqual(check_dossiers.table_names(markdown), ["alpha", "beta"])


class RepositoryTests(unittest.TestCase):
    def test_every_idea_passes(self):
        errors = check_dossiers.check_log()
        for number in check_dossiers.IDEAS:
            errors.extend(check_dossiers.check_idea(number))
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
