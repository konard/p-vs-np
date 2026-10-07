"""The completion gate must reject prerequisite-only Cook-Levin work."""

from contextlib import redirect_stdout
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.check_issue624_completion import REQUIREMENTS, audit_completion
from scripts.check_proof_status import audit


class CompletionTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(redirect_stdout(io.StringIO()))

    def test_contracts_reference_the_shared_hardness_definitions(self):
        for name in ("satHard", "cookLevin"):
            requirement = next(r for r in REQUIREMENTS if r.lean_name.endswith(f".{name}"))
            predicate = "SATHard" if name == "satHard" else "CookLevin"
            self.assertEqual(requirement.lean_type, f"_root_.Issue532.Machines.{predicate}")
            self.assertEqual(requirement.rocq_type, f"proofs.experiments.issue532.rocq.Machines.{predicate}")

    def test_construction_contracts_quantify_over_the_entire_shared_np_class(self):
        for requirement in REQUIREMENTS[:10]:
            if requirement.lean_name.endswith((".satHard", ".cookLevin")):
                continue
            with self.subTest(theorem=requirement.lean_name):
                self.assertTrue(requirement.lean_type.startswith(
                    "∀ (np : _root_.Complexity.ClassNP)"))
                self.assertTrue(requirement.rocq_type.startswith(
                    "forall (np : proofs.complexity.rocq.Complexity.Complexity.ClassNP)"))

    def test_overlong_contract_rejects_the_full_formula_with_arbitrary_auxiliary_values(self):
        requirement = next(r for r in REQUIREMENTS if r.lean_name.endswith(".tableauCNF_overlong_rejected"))
        for language in ("lean", "rocq"):
            expected = requirement.type(language)
            self.assertIn("encodeCertificate cert v", expected)
            self.assertIn("evalCNF a", expected)
            self.assertTrue(expected.endswith("tableauCNF np x) = false"))

    def fixture(self, root):
        manifest = {language: [] for language in ("lean", "rocq")}
        for language, suffix in (("lean", "lean"), ("rocq", "v")):
            source = root / f"proofs/Result.{suffix}"
            source.parent.mkdir(exist_ok=True)
            declarations = []
            for requirement in REQUIREMENTS:
                name = requirement.name(language)
                short = name.split(".")[-1]
                expected = requirement.type(language)
                declarations.append(
                    f"theorem {short} : {expected} := by trivial\n" if language == "lean"
                    else f"Theorem {short} : {expected}. Proof. exact I. Qed.\n"
                )
                manifest[language].append({
                    "source": f"proofs/Result.{suffix}", "theorem": name,
                    "allowed_axioms": [],
                })
            source.write_text("".join(declarations))
        return manifest

    def test_prerequisite_certification_does_not_establish_completion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "Conditional.lean"
            source.write_text("theorem pEqualsNP_of_inP_sat (hard : SATHard) : InP SAT → PEqualsNP := bridge hard\n")
            manifest = {"lean": [{"source": "Conditional.lean", "theorem": "Issue532.Machines.pEqualsNP_of_inP_sat",
                                  "allowed_axioms": []}]}
            self.assertEqual(audit(root, manifest, ["lean"], False), [])
            failures = audit_completion(root, manifest, ["lean"], query=False)
            self.assertTrue(any("satHard" in message for message in failures))
            self.assertTrue(any("red_computes" in message for message in failures))
            self.assertTrue(any("hardness premise" in message for message in failures))

    def test_empty_manifest_does_not_vacuously_pass(self):
        failures = audit_completion(Path("."), {"lean": [], "rocq": []}, ["lean", "rocq"], False)
        self.assertEqual(len(failures), 2 * len(REQUIREMENTS))

    def test_paired_registered_results_are_queried_at_required_types(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            with patch("scripts.check_issue624_completion.query_assumptions", return_value=set()) as query:
                self.assertEqual(audit_completion(root, manifest, ["lean", "rocq"], True), [])
            self.assertEqual(query.call_count, 2 * len(REQUIREMENTS))
            for call in query.call_args_list:
                self.assertTrue(call.kwargs["expected_type"])

    def test_omitting_any_required_result_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            for language in manifest:
                for index, entry in enumerate(list(manifest[language])):
                    with self.subTest(language=language, theorem=entry["theorem"]):
                        altered = {**manifest, language: manifest[language][:index] + manifest[language][index + 1:]}
                        failures = audit_completion(root, altered, [language], False)
                        self.assertTrue(any(entry["theorem"] in message for message in failures))

    def test_conditional_hardness_and_bridges_fail_preflight(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            for language, suffix in (("lean", "lean"), ("rocq", "v")):
                path = root / f"proofs/Result.{suffix}"
                original = path.read_text()
                for premise in ("SATHard", "CookLevin"):
                    for name in ("satHard", "pEqualsNP_of_inP_sat"):
                        with self.subTest(language=language, premise=premise, name=name):
                            keyword = "theorem" if language == "lean" else "Theorem"
                            path.write_text(original.replace(f"{keyword} {name} :", f"{keyword} {name} (h : {premise}) :"))
                            failures = audit_completion(root, manifest, [language], False)
                            self.assertTrue(any("hardness premise" in message for message in failures))
                path.write_text(original)

    def test_duplicate_registration_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            manifest["lean"].append(dict(manifest["lean"][0]))
            failures = audit_completion(root, manifest, ["lean"], False)
            self.assertTrue(any("duplicate" in message for message in failures))

    def test_assumption_allowlist_cannot_be_expanded_to_admissions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            for language, bad in (("lean", "sorryAx"), ("rocq", "custom.hardness")):
                manifest[language][0]["allowed_axioms"] = [bad]
                failures = audit_completion(root, manifest, [language], False)
                self.assertTrue(any(bad in message for message in failures))

    def test_imported_admission_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            dependency = root / "proofs/Hole.lean"
            dependency.write_text("theorem hole : False := by sorry\n")
            source = root / "proofs/Result.lean"
            source.write_text("import proofs.Hole\n" + source.read_text())
            failures = audit_completion(root, manifest, ["lean"], False)
            self.assertTrue(any("proofs/Hole.lean:1" in message for message in failures))

    def test_kernel_type_failure_is_not_treated_as_completion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            with patch("scripts.check_issue624_completion.query_assumptions", side_effect=ValueError("type mismatch")):
                failures = audit_completion(root, manifest, ["lean"], True)
            self.assertTrue(any("type mismatch" in message for message in failures))

    def test_unapproved_transitive_axiom_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = self.fixture(root)
            with patch("scripts.check_issue624_completion.query_assumptions", return_value={"custom.bad"}):
                failures = audit_completion(root, manifest, ["rocq"], True)
            self.assertTrue(any("custom.bad" in message for message in failures))


if __name__ == "__main__":
    unittest.main()
