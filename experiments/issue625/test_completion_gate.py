"""Regressions for the issue 625 completion gate, independent of the open proof."""

import copy
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from experiments.issue584.test_verification_workflow import step_script
from experiments.issue625 import check_membership as gate


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github/workflows/verification.yml"


class CompletionWorkflowTests(unittest.TestCase):
    def job(self, name):
        text = WORKFLOW.read_text(encoding="utf-8")
        match = re.search(rf"(?ms)^  {name}:\n(.*?)(?=^  [a-z][\w-]*:|\Z)", text)
        self.assertIsNotNone(match, f"missing mandatory completion job: {name}")
        return match.group(1)

    def test_both_completion_jobs_run_without_changed_file_filters(self):
        for language in ("lean", "rocq"):
            with self.subTest(language=language):
                job = self.job(f"circuit-sat-{language}")
                self.assertNotRegex(job, r"(?m)^    (?:if|needs):")
                self.assertIn(f"check_membership.py --{language}", job)
                self.assertIn(f"check_machines.py --{language}", job)
                self.assertLess(job.index(f"check_evaluator_candidate.py --{language}"),
                                job.index(f"check_membership.py --{language}"))
                self.assertNotIn("continue-on-error", job)
                self.assertIn("timeout-minutes:", job)

    def test_completion_jobs_build_before_checking_targets_and_save_logs(self):
        for language in ("lean", "rocq"):
            with self.subTest(language=language):
                job = self.job(f"circuit-sat-{language}")
                build = "lake build" if language == "lean" else "make -f Makefile.coq"
                self.assertLess(job.index(build), job.index("check_membership.py"))
                self.assertIn("NPNotSubsetP", job)
                self.assertRegex(job, r"if: always\(\)\n\s+uses: actions/upload-artifact@")
                self.assertIn("experiments/issue625/logs/", job)

    def test_summary_requires_both_completion_jobs(self):
        job = self.job("summary")
        for language in ("lean", "rocq"):
            self.assertIn(f"circuit-sat-{language}", job.split("steps:", 1)[0])

    def test_incomplete_cancelled_or_skipped_target_fails_summary(self):
        for language in ("lean", "rocq"):
            for status in ("failure", "cancelled", "skipped"):
                with self.subTest(language=language, status=status):
                    failed_job = f"circuit-sat-{language}"
                    script = step_script("Check results")
                    self.assertIn(f"needs.{failed_job}.result", script)
                    script = re.sub(
                        r"\$\{\{ needs\.([\w-]+)\.result \}\}",
                        lambda match: status if match.group(1) == failed_job else "success",
                        script,
                    )
                    result = subprocess.run(
                        ["bash", "-e", "-o", "pipefail", "-c", script],
                        capture_output=True, text=True,
                    )
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn("CircuitSAT", result.stdout)

    def test_successful_targets_allow_unchanged_historical_jobs_to_skip(self):
        script = step_script("Check results")
        script = re.sub(
            r"\$\{\{ needs\.([\w-]+)\.result \}\}",
            lambda match: "success" if match.group(1) in
            ("detect-changes", "circuit-sat-lean", "circuit-sat-rocq") else "skipped",
            script,
        )
        result = subprocess.run(
            ["bash", "-e", "-o", "pipefail", "-c", script], capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_lean_step_propagates_the_real_gate_exit_status(self):
        with tempfile.TemporaryDirectory() as directory:
            bin_dir = Path(directory)
            (bin_dir / "lake").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            (bin_dir / "python3").write_text(
                '#!/bin/sh\ncase "$1" in\n'
                '  *check_membership.py) exit "$GATE_EXIT" ;;\n'
                '  *) exit 0 ;;\nesac\n', encoding="utf-8",
            )
            for program in bin_dir.iterdir():
                program.chmod(0o755)
            for exit_code in (0, 1):
                with self.subTest(exit_code=exit_code):
                    result = subprocess.run(
                        ["bash", "-e", "-o", "pipefail", "-c",
                         step_script("Require complete CircuitSAT membership in Lean")],
                        cwd=ROOT, capture_output=True, text=True,
                        env={**os.environ, "PATH": f"{bin_dir}:{os.environ['PATH']}",
                             "GATE_EXIT": str(exit_code)},
                    )
                    self.assertEqual(result.returncode, exit_code, result.stdout + result.stderr)


class CompletionAuditTests(unittest.TestCase):
    def manifest(self):
        return {language: gate.required_entries(language) for language in ("lean", "rocq")}

    def test_complete_registration_is_accepted(self):
        for language in ("lean", "rocq"):
            self.assertEqual(gate.check_registration(self.manifest(), language), [])

    def test_syntax_slice_is_not_completion(self):
        manifest = {language: [{
            "source": "proofs/experiments/issue567/" + language + "/CircuitSyntax." +
            ("lean" if language == "lean" else "v"),
            "theorem": "circuitSyntaxMachine_run",
            "allowed_axioms": [],
        }] for language in ("lean", "rocq")}
        for language in ("lean", "rocq"):
            failures = gate.check_registration(manifest, language)
            self.assertTrue(any("circuitSATInNP" in error for error in failures), failures)

    def test_conditional_helper_cannot_replace_membership_target(self):
        manifest = self.manifest()
        for language in ("lean", "rocq"):
            for entry in manifest[language]:
                if entry["theorem"].endswith(".circuitSATInNP"):
                    entry["theorem"] += "_of_verifier_run"
            self.assertTrue(gate.check_registration(manifest, language))

    def test_missing_bridge_wrong_source_or_duplicate_registration_is_rejected(self):
        for language in ("lean", "rocq"):
            for mutation in ("missing", "source", "duplicate"):
                with self.subTest(language=language, mutation=mutation):
                    manifest = self.manifest()
                    entry = manifest[language][-1]
                    if mutation == "missing":
                        manifest[language].pop()
                    elif mutation == "source":
                        entry["source"] = "proofs/unrelated.lean"
                    else:
                        manifest[language].append(copy.deepcopy(entry))
                    self.assertTrue(gate.check_registration(manifest, language))

    def test_allowlist_cannot_be_expanded_to_assume_the_missing_theorem(self):
        for language in ("lean", "rocq"):
            manifest = self.manifest()
            manifest[language][0]["allowed_axioms"].append("assumedCircuitSATInNP")
            self.assertTrue(gate.check_registration(manifest, language))

    def fixture(self, directory):
        root = Path(directory)
        here = root / "experiments/issue625"
        here.mkdir(parents=True)
        (root / "scripts").mkdir()
        (root / "scripts/proof_status.json").write_text(json.dumps(self.manifest()), encoding="utf-8")
        for language in ("lean", "rocq"):
            for entry in gate.required_entries(language):
                path = root / entry["source"]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("", encoding="utf-8")
            suffix = ".lean" if language == "lean" else ".v"
            for name in ("MembershipTarget", "ConsequencesTarget"):
                template = ROOT / "experiments/issue625" / f"{name}{suffix}.in"
                (here / template.name).write_text(template.read_text(encoding="utf-8"), encoding="utf-8")
        return root, here

    def test_prover_failure_fails_gate_and_preserves_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            root, here = self.fixture(directory)
            result = subprocess.CompletedProcess([], 1, "unknown circuitSATInNP\n", "")
            with patch.object(gate.subprocess, "run", return_value=result), \
                    patch.object(gate.proof_status, "query_assumptions") as query:
                self.assertTrue(gate.check("lean", root, here))
                query.assert_not_called()
            self.assertIn("unknown circuitSATInNP", (here / "logs/lean-membership.log").read_text())

    def test_saved_probes_do_not_pollute_the_prover_source_inventory(self):
        for language, suffix in (("lean", ".lean"), ("rocq", ".v")):
            with self.subTest(language=language), tempfile.TemporaryDirectory() as directory:
                root, here = self.fixture(directory)
                result = subprocess.CompletedProcess([], 1, "missing theorem\n", "")
                with patch.object(gate.subprocess, "run", return_value=result):
                    gate.check(language, root, here)
                self.assertFalse(list((here / "logs").glob(f"*{suffix}")))
                self.assertTrue((here / "logs" / f"{language}-membership{suffix}.in").is_file())

    def test_transitive_admission_fails_even_when_prover_compilation_succeeds(self):
        for language, forbidden in (("lean", "sorry"), ("rocq", "Admitted")):
            with self.subTest(language=language), tempfile.TemporaryDirectory() as directory:
                root, here = self.fixture(directory)
                entry = gate.required_entries(language)[0]
                source = root / entry["source"]
                sibling = source.with_name("Gap" + source.suffix)
                sibling.write_text(forbidden, encoding="utf-8")
                module = sibling.relative_to(root).with_suffix("").as_posix().replace("/", ".")
                statement = f"import {module}" if language == "lean" else f"Require Import {module}."
                source.write_text(statement, encoding="utf-8")
                success = subprocess.CompletedProcess([], 0, "", "")
                with patch.object(gate.subprocess, "run", return_value=success), \
                        patch.object(gate.proof_status, "query_assumptions", return_value=set()):
                    self.assertTrue(any(forbidden in error for error in gate.check(language, root, here)))

    def test_closed_types_and_standard_assumptions_pass_but_global_axiom_fails(self):
        for language in ("lean", "rocq"):
            for assumptions, passes in ((set(), True),
                                        (gate.ALLOWED_AXIOMS[language], True),
                                        ({"assumedCircuitSATInNP"}, False)):
                with self.subTest(language=language, assumptions=assumptions), \
                        tempfile.TemporaryDirectory() as directory:
                    root, here = self.fixture(directory)
                    success = subprocess.CompletedProcess([], 0, "", "")
                    with patch.object(gate.subprocess, "run", return_value=success), \
                            patch.object(gate.proof_status, "query_assumptions", return_value=assumptions):
                        failures = gate.check(language, root, here)
                    self.assertEqual(not failures, passes, failures)

    def test_manifest_stricter_assumption_limits_are_enforced(self):
        with tempfile.TemporaryDirectory() as directory:
            root, here = self.fixture(directory)
            manifest = self.manifest()
            manifest["lean"][0]["allowed_axioms"] = []
            (root / "scripts/proof_status.json").write_text(json.dumps(manifest), encoding="utf-8")
            success = subprocess.CompletedProcess([], 0, "", "")
            with patch.object(gate.subprocess, "run", return_value=success), \
                    patch.object(gate.proof_status, "query_assumptions", return_value={"propext"}):
                self.assertTrue(any("registration" in error for error in gate.check("lean", root, here)))


if __name__ == "__main__":
    unittest.main()
