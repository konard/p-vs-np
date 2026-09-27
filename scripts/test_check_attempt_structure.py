#!/usr/bin/env python3
"""Tests for the P vs NP attempt structure checker."""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from urllib.error import URLError


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_attempt_structure import (  # noqa: E402
    AttemptMetadata,
    StructureValidation,
    WoegingerAttempt,
    compare_with_woeginger,
    extract_author,
    main,
    parse_metadata_from_readme,
    parse_woeginger_html,
)


class CheckAttemptStructureTests(unittest.TestCase):
    def run_checker(self, *args):
        stdout, stderr = io.StringIO(), io.StringIO()
        argv = ["check_attempt_structure.py", "--base-dir", str(self.base_dir), *args]
        with patch.object(sys, "argv", argv), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            try:
                main()
                status = 0
            except SystemExit as exc:
                status = exc.code
        return status, stdout.getvalue(), stderr.getvalue()

    def setUp(self):
        temp_dir = tempfile.TemporaryDirectory()
        self.addCleanup(temp_dir.cleanup)
        self.base_dir = Path(temp_dir.name)
        attempt_dir = self.base_dir / "proofs" / "attempts" / "alice-smith-2001-peqnp"
        attempt_dir.mkdir(parents=True)
        (attempt_dir / "README.md").write_text(
            "# Alice Smith (2001) - P=NP Attempt\n\n"
            "- **Authors**: Alice Smith\n- **Year**: 2001\n- **Claim**: P = NP\n",
            encoding="utf-8",
        )

    def write_source(self, html):
        source = self.base_dir / "woeginger.html"
        source.write_text(html, encoding="utf-8")
        return source.as_uri()

    def test_strict_coverage_fails_when_source_file_is_missing_even_when_quiet(self):
        missing_url = (self.base_dir / "missing.html").as_uri()
        status, output, errors = self.run_checker(
            "--fail-on-missing-woeginger", "--woeginger-url", missing_url, "--quiet"
        )
        self.assertEqual(status, 2)
        self.assertEqual(output, "")
        self.assertIn("could not compare against Woeginger", errors)

    def test_strict_coverage_fails_on_network_error(self):
        with patch("check_attempt_structure.urlopen", side_effect=URLError("network unavailable")):
            status, _, errors = self.run_checker("--fail-on-missing-woeginger", "--quiet")
        self.assertEqual(status, 2)
        self.assertIn("network unavailable", errors)

    def test_strict_coverage_fails_on_malformed_source(self):
        source_url = self.write_source("<html><body>Not a milestone list</body></html>")
        status, _, errors = self.run_checker(
            "--fail-on-missing-woeginger", "--woeginger-url", source_url, "--quiet"
        )
        self.assertEqual(status, 2)
        self.assertIn("No Woeginger milestone entries parsed", errors)

    def test_strict_coverage_rejects_modes_that_skip_the_source(self):
        for args in (
            ("--offline", "--fail-on-missing-woeginger"),
            ("--path", str(self.base_dir / "proofs" / "attempts" / "alice-smith-2001-peqnp"),
             "--fail-on-missing-woeginger"),
            ("--offline", "--require-woeginger"),
        ):
            with self.subTest(args=args):
                status, _, errors = self.run_checker(*args)
                self.assertEqual(status, 2)
                self.assertIn("incompatible", errors)

    def test_strict_coverage_distinguishes_missing_entries_from_unavailable_source(self):
        source_url = self.write_source(
            "<h2>Milestones</h2><ol><li>[Equal]: In 2002 Bob Jones proved P=NP.</ol>"
        )
        status, output, errors = self.run_checker(
            "--fail-on-missing-woeginger", "--woeginger-url", source_url, "--quiet"
        )
        self.assertEqual(status, 1)
        self.assertIn("1 Woeginger entries are missing", output)
        self.assertEqual(errors, "")

    def test_strict_coverage_succeeds_when_all_source_entries_match(self):
        source_url = self.write_source(
            "<h2>Milestones</h2><ol>"
            "<li>[Equal]: In 2001 Alice Smith proved P=NP with a SAT algorithm.</ol>"
        )
        status, _, errors = self.run_checker(
            "--fail-on-missing-woeginger", "--woeginger-url", source_url, "--quiet"
        )
        self.assertEqual(status, 0)
        self.assertEqual(errors, "")

    def test_parse_woeginger_html_handles_implicit_li_end_tags(self):
        html = """
        <html><body>
        <h2>Milestones</h2>
        <ol>
          <li><b>[Equal]:</b> In 2001 Alice Smith proved P=NP with a SAT algorithm.
          <li><b>[Not equal]:</b> In 2002 Bob Jones proved P is not equal to NP.
        </ol>
        </body></html>
        """

        attempts = parse_woeginger_html(html, "https://example.test/P-versus-NP.htm")

        self.assertEqual(len(attempts), 2)
        self.assertEqual(attempts[0].entry_id, 1)
        self.assertEqual(attempts[0].claim, "P = NP")
        self.assertEqual(attempts[0].year, "2001")
        self.assertEqual(attempts[0].author, "Alice Smith")
        self.assertEqual(attempts[1].entry_id, 2)
        self.assertEqual(attempts[1].claim, "P != NP")
        self.assertEqual(attempts[1].year, "2002")
        self.assertEqual(attempts[1].author, "Bob Jones")

    def test_parse_metadata_from_readme_keeps_full_h1_title(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            attempt_path = Path(tmpdir) / "alice-smith-2001-peqnp"
            attempt_path.mkdir()
            readme_path = attempt_path / "README.md"
            readme_path.write_text(
                "# Alice Smith (2001) - P=NP Attempt\n\n"
                "- **Authors**: Alice Smith and Bob Jones\n"
                "- **Year**: 2001\n"
                "- **Claim**: P = NP\n",
                encoding="utf-8",
            )

            metadata = parse_metadata_from_readme(readme_path)

        self.assertIsNotNone(metadata)
        self.assertEqual(metadata.title, "Alice Smith (2001) - P=NP Attempt")
        self.assertEqual(metadata.author, "Alice Smith and Bob Jones")
        self.assertEqual(metadata.year, "2001")
        self.assertEqual(metadata.claim, "P = NP")

    def test_extract_author_handles_initials_and_lowercase_particles(self):
        text = (
            'Applied Mathematics and Computation contains the article '
            '"Consequences of an exotic definition for P=NP" by N.C.A. da Costa '
            'and F.A. Doria.'
        )

        self.assertEqual(extract_author(text), "N.C.A. da Costa and F.A. Doria")

    def test_compare_with_woeginger_matches_author_year_claim_and_title(self):
        validation = StructureValidation(
            path=Path("proofs/attempts/alice-smith-2001-peqnp"),
            has_readme=True,
            metadata=AttemptMetadata(
                author="Alice Smith",
                year="2001",
                claim="P = NP",
                title="Polynomial SAT Algorithm",
            ),
        )
        attempt = WoegingerAttempt(
            entry_id=1,
            claim="P = NP",
            year="2001",
            author="Alice Smith",
            title="Polynomial SAT Algorithm",
            summary="In 2001 Alice Smith proved P=NP with a polynomial SAT algorithm.",
            source_url="https://example.test/P-versus-NP.htm",
        )

        matches, unmatched = compare_with_woeginger([validation], [attempt])

        self.assertEqual(len(matches), 1)
        self.assertIs(matches[0].validation, validation)
        self.assertGreaterEqual(matches[0].score, 9)
        self.assertEqual(unmatched, [])

    def test_compare_with_woeginger_keeps_feinstein_entries_distinct(self):
        validations = [
            StructureValidation(
                path=Path("proofs/attempts/craig-feinstein-2003-pneqnp"),
                has_readme=True,
                metadata=AttemptMetadata(
                    author="Craig Alan Feinstein",
                    year="2003",
                    claim="P ≠ NP",
                    title="Craig Alan Feinstein (2003-04) - P≠NP Attempt",
                ),
            ),
            StructureValidation(
                path=Path("proofs/attempts/craig-feinstein-2006-pneqnp"),
                has_readme=True,
                metadata=AttemptMetadata(
                    author="Craig Alan Feinstein",
                    year="2006",
                    claim="P ≠ NP",
                    title="A New and Elegant Argument that P is not NP",
                ),
            ),
        ]
        attempts = [
            WoegingerAttempt(
                entry_id=11,
                claim="P != NP",
                year="2003",
                author="Craig Alan Feinstein",
                title="P vs NP attempts",
                summary="In 2003 Craig Alan Feinstein claimed P is not equal to NP.",
                source_url="https://example.test/P-versus-NP.htm",
            ),
            WoegingerAttempt(
                entry_id=31,
                claim="P != NP",
                year="2006",
                author="Craig Alan Feinstein",
                title="A New and Elegant Argument that P is not NP",
                summary=(
                    "In 2006 Craig Alan Feinstein wrote "
                    "\"A New and Elegant Argument that P is not NP\"."
                ),
                source_url="https://example.test/P-versus-NP.htm",
            ),
        ]

        matches, unmatched = compare_with_woeginger(validations, attempts)

        self.assertEqual(matches[0].validation.path.name, "craig-feinstein-2003-pneqnp")
        self.assertEqual(matches[1].validation.path.name, "craig-feinstein-2006-pneqnp")
        self.assertEqual(unmatched, [])


if __name__ == "__main__":
    unittest.main()
