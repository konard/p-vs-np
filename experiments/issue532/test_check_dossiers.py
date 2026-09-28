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

    def test_open_obligation_must_use_the_machine_model(self):
        head = "namespace Issue532.Idea01\ntheorem a : 1 = 1 := rfl\ntheorem b : 2 = 2 := rfl\n"
        # The reviewer's pattern: a free time function with no link to `Run`.
        free = head + (
            "/-- **Open obligation.** -/\n"
            "def PolyDec (L : Nat → Bool) : Prop :=\n"
            "  ∃ (D : Nat → Bool) (t : Nat → Nat) (c : Nat), (∀ x, D x = L x) ∧ ∀ x, t x ≤ c\n"
        )
        errors = self.check_source("lean", free)
        self.assertTrue(any("without importing" in e for e in errors))
        self.assertTrue(any("does not mention the machine model" in e for e in errors))
        self.assertTrue(any("free cost function" in e for e in errors))
        tied = "import proofs.experiments.issue532.lean.Machines\n" + head + (
            "/-- A helper tied to the model. -/\n"
            "def Fast (L : Complexity.Language) : Prop :=\n"
            "  ∃ m p, Issue532.Machines.DecidesWithin m p L\n"
            "/-- **Open obligation.** -/\n"
            "def Goal : Prop := Fast Issue532.Machines.SAT\n"
        )
        self.assertEqual(self.check_source("lean", tied), [])
        # `SATVerifier` imports `Machines`, so it is part of the shared layer.
        via_verifier = tied.replace(".lean.Machines\n", ".lean.SATVerifier\n")
        self.assertIn(".lean.SATVerifier\n", via_verifier)
        self.assertEqual(self.check_source("lean", via_verifier), [])
        # A free predicate parameter makes the obligation depend on its choice.
        free_predicate = tied + (
            "/-- **Open obligation.** -/\n"
            "def Isolation (PolyTime : (Nat → Nat) → Prop) : Prop :=\n"
            "  ∃ g, PolyTime g ∧ Issue532.Machines.SAT = Issue532.Machines.SAT\n"
        )
        self.assertTrue(
            any("free predicate `PolyTime`" in e for e in self.check_source("lean", free_predicate))
        )
        # A plain schema that is not called an open obligation is not checked.
        schema = head + "/-- An abstract schema. -/\ndef Schema (P : Prop) : Prop := P\n"
        self.assertEqual(self.check_source("lean", schema), [])

    def test_rocq_open_obligation_must_use_the_machine_model(self):
        body = "Theorem a : 1 = 1.\nProof. reflexivity. Qed.\nTheorem b : 2 = 2.\nProof. reflexivity. Qed.\n"
        free = body + (
            "(** Open obligation. *)\n"
            "Definition PolyDec (L : nat -> bool) : Prop :=\n"
            "  exists (t : nat -> nat) (c : nat), forall x, t x <= c.\n"
        )
        errors = self.check_source("rocq", free)
        self.assertTrue(any("without importing" in e for e in errors))
        self.assertTrue(any("free cost function" in e for e in errors))
        tied = "From proofs.experiments.issue532.rocq Require Import Machines.\n" + body + (
            "(** Open obligation. *)\n"
            "Definition Goal : Prop := InP SAT.\n"
        )
        self.assertEqual(self.check_source("rocq", tied), [])
        via_verifier = tied.replace("Require Import Machines.", "Require SATVerifier.")
        self.assertEqual(self.check_source("rocq", via_verifier), [])

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
        errors = check_dossiers.check_issue532_sources()
        errors.extend(check_dossiers.check_log())
        for number in check_dossiers.IDEAS:
            errors.extend(check_dossiers.check_idea(number))
        self.assertEqual(errors, [])


class ImportClosureTests(unittest.TestCase):
    def test_shared_and_transitive_mutations_are_rejected_in_both_provers(self):
        for language, suffix, mutations in (
            ("lean", ".lean", (
                ("admission", "theorem hole : True := by sorry\n", "sorry"),
                ("false axiom", "axiom falseClaim : False\n", "axiom"),
            )),
            ("rocq", ".v", (
                ("admission", "Theorem hole : True. Admitted.\n", "Admitted"),
                ("false axiom", "Axiom falseClaim : False.\n", "Axiom"),
            )),
        ):
            for location in ("shared", "helper"):
                for kind, mutation, token in mutations:
                    with self.subTest(language=language, location=location, kind=kind), tempfile.TemporaryDirectory() as tmp:
                        root = Path(tmp)
                        base = root / "proofs/experiments/issue532"
                        proof_dir = base / language
                        proof_dir.mkdir(parents=True)
                        helper = root / "experiments/helpers" / f"Helper{suffix}"
                        deep = root / "experiments/helpers" / f"Deep{suffix}"
                        helper.parent.mkdir(parents=True)
                        deep.write_text(mutation if location == "helper" else "")
                        if language == "lean":
                            helper.write_text("import experiments.helpers.Deep\n")
                            (proof_dir / "Machines.lean").write_text("import experiments.helpers.Helper\n")
                            (proof_dir / "SATVerifier.lean").write_text(
                                "import proofs.experiments.issue532.lean.Machines\n"
                                + (mutation if location == "shared" else "")
                            )
                            (proof_dir / "Idea01.lean").write_text(
                                "import proofs.experiments.issue532.lean.SATVerifier\n"
                            )
                        else:
                            helper.write_text("From experiments.helpers Require Deep.\n")
                            (proof_dir / "Machines.v").write_text(
                                "From experiments.helpers Require Helper.\n"
                            )
                            (proof_dir / "SATVerifier.v").write_text(
                                "From proofs.experiments.issue532.rocq Require Import Machines.\n"
                                + (mutation if location == "shared" else "")
                            )
                            (proof_dir / "Idea01.v").write_text(
                                "From proofs.experiments.issue532.rocq Require SATVerifier.\n"
                            )
                        errors = check_dossiers.check_issue532_sources(root, base)
                        self.assertTrue(any(token in error for error in errors), errors)
                        expected = "SATVerifier" if location == "shared" else "Deep"
                        self.assertTrue(any(expected in error for error in errors), errors)

    def test_historical_admissions_outside_issue532_closure_are_allowed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            base = root / "proofs/experiments/issue532"
            proof_dir = base / "lean"
            proof_dir.mkdir(parents=True)
            (proof_dir / "Idea01.lean").write_text("theorem one : 1 = 1 := rfl\n")
            historical = root / "proofs/attempts/old/Sketch.lean"
            historical.parent.mkdir(parents=True)
            historical.write_text("theorem old : True := by sorry\n")
            self.assertEqual(check_dossiers.check_issue532_sources(root, base), [])


if __name__ == "__main__":
    unittest.main()
