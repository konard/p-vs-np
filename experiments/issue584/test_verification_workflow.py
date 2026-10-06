"""Regression tests for the Formal Verification Suite's event and result handling."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github/workflows/verification.yml"


def step_script(name):
    text = WORKFLOW.read_text()
    match = re.search(
        rf"(?m)^    - name: {re.escape(name)}\n(?:      [^\n]*\n)*?      run: \|\n",
        text,
    )
    if not match:
        raise AssertionError(f"Cannot find run script for {name}")
    lines = []
    for line in text[match.end():].splitlines():
        if line and not line.startswith("        "):
            break
        lines.append(line[8:] if line else "")
    return "\n".join(lines)


class VerificationWorkflowTests(unittest.TestCase):
    def run_detector(self, event, files="", base="main", git_failure=False):
        with tempfile.TemporaryDirectory() as temp:
            temp = Path(temp)
            output = temp / "outputs"
            bin_dir = temp / "bin"
            bin_dir.mkdir()
            fake_git = bin_dir / "git"
            fake_git.write_text(
                "#!/bin/sh\n"
                "if [ \"$TEST_GIT_FAIL\" = 1 ]; then\n"
                "  echo 'fatal: diff failed' >&2\n"
                "  exit 128\n"
                "fi\n"
                "printf '%s' \"$TEST_CHANGED_FILES\"\n"
            )
            fake_git.chmod(0o755)
            script = step_script("Detect changed files")
            script = script.replace("${{ github.event_name }}", event)
            script = script.replace("${{ github.base_ref }}", base)
            env = dict(os.environ)
            env.update(
                GITHUB_OUTPUT=str(output),
                GITHUB_EVENT_NAME=event,
                GITHUB_BASE_REF=base,
                TEST_CHANGED_FILES=files,
                TEST_GIT_FAIL="1" if git_failure else "0",
                PATH=f"{bin_dir}:{env['PATH']}",
            )
            result = subprocess.run(
                ["bash", "-e", "-o", "pipefail", "-c", script],
                cwd=ROOT,
                env=env,
                capture_output=True,
                text=True,
            )
            values = dict(
                line.split("=", 1)
                for line in output.read_text().splitlines()
            ) if output.exists() else {}
            return result, values

    def test_push_runs_all_provers(self):
        result, values = self.run_detector("push")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values, {"lean": "true", "rocq": "true", "agda": "true"})

    def test_manual_dispatch_runs_all_provers_with_no_base_ref(self):
        result, values = self.run_detector("workflow_dispatch", base="", git_failure=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values, {"lean": "true", "rocq": "true", "agda": "true"})

    def test_pr_only_runs_changed_prover(self):
        for filename, selected in (
            ("proofs/example.lean", "lean"),
            ("proofs/example.v", "rocq"),
            ("proofs/example.agda", "agda"),
        ):
            with self.subTest(filename=filename):
                result, values = self.run_detector("pull_request", f"{filename}\n")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(
                    values,
                    {name: "true" if name == selected else "false" for name in ("lean", "rocq", "agda")},
                )

    def test_pr_with_no_matching_changes_skips_provers(self):
        for files in ("", "README.md\n"):
            with self.subTest(files=files):
                result, values = self.run_detector("pull_request", files)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(values, {"lean": "false", "rocq": "false", "agda": "false"})

    def test_pr_without_base_ref_fails_detection(self):
        result, values = self.run_detector("pull_request", base="")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(values, {})

    def test_workflow_change_runs_all_provers(self):
        result, values = self.run_detector("pull_request", ".github/workflows/verification.yml\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values, {"lean": "true", "rocq": "true", "agda": "true"})

    def test_manifest_change_runs_lean(self):
        result, values = self.run_detector("pull_request", "lake-manifest.json\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values["lean"], "true")

    def test_contributor_guide_change_runs_lean(self):
        result, values = self.run_detector("pull_request", "CONTRIBUTING.md\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(values, {"lean": "true", "rocq": "false", "agda": "false"})

    def test_certified_checker_change_runs_both_provers(self):
        for filename in ("scripts/check_proof_status.py", "scripts/proof_status.json"):
            with self.subTest(filename=filename):
                result, values = self.run_detector("pull_request", f"{filename}\n")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(values, {"lean": "true", "rocq": "true", "agda": "false"})

    def test_failed_certified_audit_fails_summary(self):
        script = step_script("Check results")
        for job in ("detect-changes", "lean-verification", "rocq-verification", "agda-verification", "certified-lean", "circuit-sat-lean", "circuit-sat-rocq"):
            script = script.replace(f"${{{{ needs.{job}.result }}}}", "success")
        script = script.replace("${{ needs.certified-rocq.result }}", "failure")
        result = subprocess.run(
            ["bash", "-e", "-o", "pipefail", "-c", script], capture_output=True, text=True
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Certified Rocq audit failed", result.stdout)

    def test_failed_diff_fails_detection(self):
        result, values = self.run_detector("pull_request", git_failure=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(values, {})

    def test_failed_detector_fails_summary(self):
        script = step_script("Check results")
        for job in ("circuit-sat-lean", "circuit-sat-rocq"):
            script = script.replace(f"${{{{ needs.{job}.result }}}}", "success")
        for job in ("lean-verification", "rocq-verification", "certified-lean", "certified-rocq", "agda-verification"):
            script = script.replace(f"${{{{ needs.{job}.result }}}}", "skipped")
        script = script.replace("${{ needs.detect-changes.result }}", "failure")
        result = subprocess.run(
            ["bash", "-e", "-o", "pipefail", "-c", script],
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)

    def run_lean_step(self, test_output, test_exit):
        with tempfile.TemporaryDirectory() as temp:
            bin_dir = Path(temp)
            (bin_dir / "lean").write_text("#!/bin/sh\nexit 0\n")
            (bin_dir / "lake").write_text(
                "#!/bin/sh\n"
                "if [ \"$1\" = test ]; then\n"
                "  printf '%s\\n' \"$TEST_LAKE_OUTPUT\"\n"
                "  exit \"$TEST_LAKE_EXIT\"\n"
                "fi\n"
                "exit 0\n"
            )
            (bin_dir / "bash").write_text("#!/bin/sh\nexit 0\n")
            (bin_dir / "python3").write_text("#!/bin/sh\nexit 0\n")
            (bin_dir / "rm").write_text("#!/bin/sh\nexit 0\n")
            for program in bin_dir.iterdir():
                program.chmod(0o755)
            env = dict(os.environ)
            env.update(
                PATH=f"{bin_dir}:{env['PATH']}",
                TEST_LAKE_OUTPUT=test_output,
                TEST_LAKE_EXIT=str(test_exit),
            )
            return subprocess.run(
                ["/bin/bash", "-e", "-o", "pipefail", "-c", step_script("Build and test Lean")],
                cwd=ROOT,
                env=env,
                capture_output=True,
                text=True,
            )

    def test_lake_test_failure_fails_job(self):
        result = self.run_lean_step("test assertion failed", 1)
        self.assertNotEqual(result.returncode, 0)

    def test_missing_lake_test_driver_is_allowed(self):
        result = self.run_lean_step("error: p-vs-np: no test driver configured", 1)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
