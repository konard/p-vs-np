"""Check that incomplete endpoints cannot produce a green PR summary."""

import json
import os
from pathlib import Path
import re
import subprocess
import unittest

from experiments.issue584.test_verification_workflow import step_script
from scripts.check_proof_status import source_closure


ROOT = Path(__file__).resolve().parents[2]


class CompletionWorkflowTests(unittest.TestCase):
    def test_certification_builds_all_registered_source_dependencies(self):
        workflow = (ROOT / ".github/workflows/verification.yml").read_text()
        manifest = json.loads((ROOT / "scripts/proof_status.json").read_text())
        for language in ("lean", "rocq"):
            with self.subTest(language=language):
                job = re.search(
                    rf"(?ms)^  certified-{language}:\n(.*?)(?=^  [\w-]+:|\Z)",
                    workflow,
                )[1]
                if language == "lean":
                    command = re.search(r"(?ms)^\s+lake build(.*?)^\s+python3 ", job)[1]
                    modules = re.findall(r"\bproofs(?:\.\w+)+\b", command)
                    targets = [{"source": module.replace(".", "/") + ".lean"}
                               for module in modules]
                    built = source_closure(ROOT, targets)
                else:
                    # Rocq compile does not build imported source files itself.
                    targets = re.findall(r"rocq compile[^\n]*? (\S+\.v)", job)
                    built = {ROOT / target for target in targets}
                self.assertTrue(targets, f"no {language} certification build targets")
                required = source_closure(ROOT, manifest[language])
                missing = sorted(str(path.relative_to(ROOT)) for path in required - built)
                self.assertEqual(missing, [],
                                 f"{language} certification lacks build targets: {missing}")

    def run_summary(self, completion, required=True):
        script = step_script("Check results")
        script = re.sub(r"\$\{\{ needs\.([\w-]+)\.result \}\}",
                        lambda m: completion if m[1] == "issue624-completion" else "success", script)
        return subprocess.run(["bash", "-e", "-o", "pipefail", "-c", script],
                              capture_output=True, text=True,
                              env={**os.environ, "ISSUE624_REQUIRED": str(required).lower()})

    def test_incomplete_cancelled_or_skipped_completion_fails_summary(self):
        for status in ("failure", "cancelled", "skipped", ""):
            with self.subTest(status=status):
                result = self.run_summary(status)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Issue 624 completion", result.stdout)

    def test_completed_deliverable_passes_summary(self):
        result = self.run_summary("success")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_unrelated_pr_may_skip_completion(self):
        result = self.run_summary("skipped", required=False)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_completion_runs_independently_of_change_detection(self):
        workflow = (ROOT / ".github/workflows/verification.yml").read_text()
        match = re.search(r"(?ms)^  issue624-completion:\n(.*?)(?=^  [\w-]+:|\Z)", workflow)
        self.assertIsNotNone(match, "missing independent completion job")
        job = match[1]
        self.assertNotRegex(job, r"(?m)^    needs:")
        self.assertIn("github.event.pull_request.number == 630", job)
        self.assertIn("github.head_ref == 'issue-624-0b9b9b6c5d75'", job)
        self.assertIn("python3 scripts/check_issue624_completion.py --lean", job)
        self.assertIn("python3 scripts/check_issue624_completion.py --rocq", job)
        self.assertNotIn("continue-on-error", job)
        self.assertIn("issue624-completion", re.search(r"(?m)^    needs: \[.*\]$", workflow[workflow.index("  summary:"):])[0])

    def test_job_selection_and_required_summary_use_the_same_condition(self):
        workflow = (ROOT / ".github/workflows/verification.yml").read_text()
        job = workflow[workflow.index("  issue624-completion:"):workflow.index("  summary:")]
        selected = re.search(r"(?s)    if: >-\n(.*?)\n    timeout-minutes:", job)[1]
        required = re.search(r"(?s)      ISSUE624_REQUIRED: >-\n\s*\$\{\{(.*?)\}\}", workflow)[1]
        compact = lambda text: re.sub(r"\s+", "", text)
        self.assertEqual(compact(selected), compact(required))


if __name__ == "__main__":
    unittest.main()
