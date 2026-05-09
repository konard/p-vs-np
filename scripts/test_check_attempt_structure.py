#!/usr/bin/env python3
"""Tests for the P vs NP attempt structure checker."""

import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from check_attempt_structure import (  # noqa: E402
    AttemptMetadata,
    StructureValidation,
    WoegingerAttempt,
    compare_with_woeginger,
    extract_author,
    parse_metadata_from_readme,
    parse_woeginger_html,
)


class CheckAttemptStructureTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
