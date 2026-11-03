#!/usr/bin/env python3
"""Tests for the literature registry checker. Offline; uses temporary files."""

import contextlib
import copy
import io
import json
import sys
import tempfile
from collections import Counter
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

import check_literature_registry as reg  # noqa: E402


def entry(entry_id, date="2026-10-26", url=None, **extra):
    record = {
        "id": entry_id,
        "title": "Title of " + entry_id,
        "authors": ["A. Author"],
        "year": int(date[:4]),
        "date": date,
        "venue": "arXiv",
        "urls": [url or "https://arxiv.org/abs/" + entry_id],
        "artifact_class": "paper",
        "result_type": "preprint-theorem",
        "claim": "A bound for k-SAT.",
        "status": "unreviewed-preprint",
        "claim_status_local": "discovered",
        "relevance": "Touches ETH.",
        "caveats": "None noted.",
        "tags": ["eth"],
        "verified": "yes",
        "added": "2026-11-03",
    }
    record.update(extra)
    return record


def registry(*entries):
    return {"schema_version": "1", "updated": "2026-11-03", "entries": list(entries)}


def formal(**extra):
    record = {"prover": "Lean 4", "model": "Mathlib Turing.FinTM2", "declaration": "Ns.main",
              "file": "Main.lean", "revision": "0123456789abcdef0123456789abcdef01234567",
              "kernel_checks": ["lean"], "axioms": "unknown"}
    record.update(extra)
    return record


TAG_TABLE = "<!-- tags:start -->\n" + "\n".join("| `{}` | x |".format(t) for t in sorted(reg.TAGS)) \
    + "\n<!-- tags:end -->\n"


def guide(unverified_ids, extra=""):
    listed = ", ".join("`{}`".format(i) for i in unverified_ids)
    return (TAG_TABLE + "\n## Known gaps\n\n- Entries with `verified: no`: " + listed
            + " (reasons).\n- Other rows are `partial`.\n" + extra + "\n## Next\n")


class ValidationTests(unittest.TestCase):
    def assertError(self, data, fragment):
        errors = reg.validate(data)
        self.assertTrue(any(fragment in e for e in errors), "expected {!r} in {}".format(fragment, errors))

    def test_minimal_registry_is_valid(self):
        self.assertEqual(reg.validate(registry(entry("a-2026"), entry("b-2025", date="2025-03"))), [])

    def test_duplicate_id(self):
        self.assertError(registry(entry("a-2026"), entry("a-2026", url="https://example.org/other")),
                         "duplicate id 'a-2026'")

    def test_bad_enum_values(self):
        self.assertError(registry(entry("a-2026", status="accepted")), "status 'accepted' is not one of")
        self.assertError(registry(entry("a-2026", claim_status_local="certified")), "claim_status_local 'certified'")
        self.assertError(registry(entry("a-2026", artifact_class="weights")), "artifact_class 'weights'")

    def test_duplicate_canonical_url_after_normalization(self):
        self.assertError(registry(entry("a-2026", url="https://arxiv.org/abs/1"),
                                  entry("b-2026", url="http://www.arxiv.org/abs/1/")),
                         "duplicates entry a-2026")

    def test_secondary_urls_may_repeat_across_entries(self):
        first = entry("a-2026", url="https://github.com/org/one")
        second = entry("b-2026", url="https://github.com/org/two")
        second["urls"].append("https://github.com/org/one")
        self.assertEqual(reg.validate(registry(first, second)), [])

    def test_arxiv_and_doi_urls_normalize_to_paper_keys(self):
        for url in ("https://arxiv.org/abs/2104.14316", "http://arxiv.org/abs/2104.14316v3",
                    "https://www.arxiv.org/pdf/2104.14316v2.pdf", "https://export.arxiv.org/abs/2104.14316/"):
            self.assertEqual(reg.paper_key(url), "arxiv:2104.14316", url)
        self.assertEqual(reg.paper_key("https://arxiv.org/abs/cs/0305035v27"), "arxiv:cs/0305035")
        self.assertEqual(reg.paper_key("https://dx.doi.org/10.1145/ABC.1"), "doi:10.1145/abc.1")
        self.assertIsNone(reg.paper_key("https://github.com/openai/math"))
        self.assertError(registry(entry("a-2026", url="https://arxiv.org/abs/1708.03486",
                                        urls=["https://arxiv.org/abs/1708.03486v2", "https://arxiv.org/abs/1708.03486"])),
                         "URL listed twice")
        self.assertError(registry(entry("a-2026", url="https://arxiv.org/abs/2104.14316"),
                                  entry("b-2026", url="https://arxiv.org/pdf/2104.14316v3.pdf")),
                         "duplicates entry a-2026")
        self.assertEqual(reg.validate(registry(entry("a-2026", url="https://arxiv.org/abs/2104.14316"),
                                               entry("b-2026", url="https://arxiv.org/abs/2104.14317"))), [])

    def test_paper_listed_by_two_entries_needs_a_parent_link(self):
        first = entry("a-2026", url="https://arxiv.org/abs/2610.06783")
        second = entry("b-2026", url="https://github.com/org/b")
        second["urls"].append("https://arxiv.org/pdf/2610.06783v1")
        self.assertError(registry(first, second), "paper arxiv:2610.06783 is also listed by entry a-2026")
        second["parent"] = "a-2026"
        self.assertEqual(reg.validate(registry(first, second)), [])

    def test_formal_gate_needs_pinned_declaration_file_revision_and_model(self):
        for label in ("upstream-checked", "locally-replayed", "conditional-bridge"):
            self.assertEqual(reg.validate(registry(entry("a-2026", claim_status_local=label, formal=formal()))), [])
            for key, value in (("declaration", "not recorded"), ("file", "unknown"),
                               ("revision", "unknown (master)"), ("model", "unknown (see note)"),
                               ("declaration", "")):
                self.assertError(registry(entry("a-2026", claim_status_local=label, formal=formal(**{key: value}))),
                                 "needs formal.{} to be recorded".format(key))
            broken = formal()
            del broken["revision"]
            self.assertError(registry(entry("a-2026", claim_status_local=label, formal=broken)),
                             "needs formal.revision")

    def test_locally_certified_needs_a_theorem_in_proof_status(self):
        data = registry(entry("a-2026", claim_status_local="locally-certified", formal=formal(),
                              local_certificate="Issue532.SATVerifier.satInNP"))
        self.assertEqual(reg.validate(data, certified={"Issue532.SATVerifier.satInNP"}), [])
        errors = reg.validate(data, certified={"Other.theorem"})
        self.assertTrue(any("is not a theorem in scripts/proof_status.json" in e for e in errors), errors)
        with tempfile.TemporaryDirectory() as tmp:
            status = Path(tmp) / "proof_status.json"
            status.write_text(json.dumps({"lean": [{"source": "x.lean", "theorem": "A.b", "allowed_axioms": []}],
                                          "rocq": [{"source": "x.v", "theorem": "C.d", "allowed_axioms": []}]}),
                              encoding="utf-8")
            self.assertEqual(reg.load_certified(status), {"A.b", "C.d"})

    def test_peer_reviewed_needs_a_publication_venue(self):
        ok = entry("a-2026", status="peer-reviewed", venue="STOC 2026, DOI 10.1/x; arXiv:2601.00001")
        self.assertEqual(reg.validate(registry(ok)), [])
        for venue in ("arXiv:2601.00001 (v3)", "Zenodo; GitHub", "Author's web page"):
            self.assertError(registry(entry("a-2026", status="peer-reviewed", venue=venue)),
                             "needs a publication venue")
        self.assertError(registry(entry("a-2026", result_type="peer-reviewed-theorem")),
                         "needs status 'peer-reviewed'")

    def test_sourced_statuses_need_responses_or_cited_notes(self):
        for status in ("withdrawn", "refuted", "formally-checked", "under-expert-review"):
            extra = {"formal": formal()} if status == "formally-checked" else {}
            self.assertError(registry(entry("a-2026", status=status, **extra)), "needs documented_responses or notes")
            self.assertError(registry(entry("a-2026", status=status, notes="Said so somewhere.", **extra)),
                             "needs documented_responses or notes")
            for notes in ("Read on https://arxiv.org/abs/2104.14316v3.", "See arXiv:2104.14316.",
                          "Commit e24a92a.", "Per the repository README."):
                self.assertEqual(reg.validate(registry(entry("a-2026", status=status, notes=notes, **extra))), [])
            responses = [{"url": "https://example.org/reply", "note": "Author's withdrawal."}]
            self.assertEqual(reg.validate(registry(entry("a-2026", status=status, documented_responses=responses,
                                                         **extra))), [])

    def test_claim_direction_must_agree_with_tags(self):
        def claim(direction, tags):
            return entry("a-2026", result_type="claimed-p-vs-np-proof", tags=["claimed-proof"] + tags,
                         attempt_slug="a-2026", claim_direction=direction, common_errors_family=1)
        for direction, tags in (("peqnp", ["peqnp"]), ("pneqnp", ["pneqnp"]), ("both", ["peqnp", "pneqnp"]),
                                ("other", []), ("undecidable", ["independence"])):
            self.assertEqual(reg.validate(registry(claim(direction, tags))), [], direction)
        self.assertError(registry(claim("undecidable", ["pneqnp"])), "disagrees with the peqnp/pneqnp tags")
        self.assertError(registry(claim("peqnp", ["pneqnp"])), "disagrees with the peqnp/pneqnp tags")
        self.assertError(registry(claim("pneqnp", ["peqnp", "pneqnp"])), "expected both")
        self.assertError(registry(claim("both", [])), "needs the tag(s) peqnp, pneqnp")
        self.assertError(registry(claim("peqnp", [])), "needs the tag(s) peqnp")

    def test_date_year_added_and_updated_are_ordered(self):
        self.assertEqual(reg.validate(registry(entry("a-2026", date="2026-11"), entry("b-2026", date="2026-11-03"))), [])
        self.assertError(registry(entry("a-2026", date="2026-11", year=2025)), "does not match year")
        self.assertError(registry(entry("a-2026", date="2026-11-04")), "is later than added")
        self.assertError(registry(entry("a-2026", date="2026-12")), "is later than added")
        self.assertError(registry(entry("a-2026", added="2026-11-04")), "later than the registry's updated")

    def test_attempt_slug_and_source_row_are_unique(self):
        first = entry("a-2026", attempt_slug="a-2026", source_row=1)
        second = entry("b-2026", attempt_slug="a-2026", source_row=2)
        self.assertError(registry(first, second), "attempt_slug 'a-2026' is also used by entry a-2026")
        second.update(attempt_slug="b-2026", source_row=1)
        self.assertError(registry(first, second), "source_row 1 is also used by entry a-2026")
        second["source_row"] = 2
        self.assertEqual(reg.validate(registry(first, second)), [])

    def test_ai_lab_lean_checked_needs_formal(self):
        self.assertError(registry(entry("a-2026", result_type="ai-lab-lean-checked")),
                         "'ai-lab-lean-checked' needs a formal object")
        self.assertEqual(reg.validate(registry(entry("a-2026", result_type="ai-lab-lean-checked",
                                                     claim_status_local="statement-only", formal=formal()))), [])

    def test_missing_field_bad_id_bad_date_unknown_tag_and_field(self):
        broken = entry("a-2026")
        del broken["caveats"]
        self.assertError(registry(broken), "missing required field 'caveats'")
        self.assertError(registry(entry("A_2026")), "kebab-case")
        self.assertError(registry(entry("a-2026", date="2026-13")), "must be YYYY, YYYY-MM or YYYY-MM-DD")
        self.assertError(registry(entry("a-2026", date="2025-01", year=2026)), "does not match year")
        self.assertError(registry(entry("a-2026", tags=["eth", "hype"])), "unknown tag 'hype'")
        self.assertError(registry(entry("a-2026", colour="red")), "unknown field 'colour'")

    def test_trust_gates(self):
        self.assertError(registry(entry("a-2026", claim_status_local="locally-certified")), "local_certificate")
        self.assertError(registry(entry("a-2026", claim_status_local="upstream-checked")), "needs a formal object")
        self.assertError(registry(entry("a-2026", status="formally-checked")), "needs a formal object")
        claim = entry("a-2026", result_type="claimed-p-vs-np-proof", tags=["claimed-proof"])
        self.assertError(registry(claim), "claimed proofs need 'attempt_slug'")
        claim.update(attempt_slug="a-2026", claim_direction="peqnp", common_errors_family=21)
        self.assertError(registry(claim), "between 1 and 20")

    def test_parent_must_exist(self):
        self.assertError(registry(entry("a-2026", parent="missing-release")), "does not name an entry")
        self.assertEqual(reg.validate(registry(entry("r-2026"), entry("a-2026", parent="r-2026"))), [])


class QueryAndRenderTests(unittest.TestCase):
    def setUp(self):
        self.entries = [
            entry("b-2026", date="2026-10-26", tags=["eth", "lean"]),
            entry("a-2026", date="2026-10-26", tags=["eth"]),
            entry("c-2026", date="2026-10", tags=["eth"]),
            entry("d-2024", date="2024", tags=["proof-complexity"], claim="Resolution lower bound."),
            entry("e-2026", date="2026-11-02", tags=["eth"], result_type="claimed-p-vs-np-proof",
                  attempt_slug="e-2026", claim_direction="pneqnp", common_errors_family=1),
        ]
        self.entries[4]["tags"] = ["claimed-proof", "pneqnp"]

    def test_query_ordering_is_date_desc_then_id(self):
        ids = [e["id"] for e in reg.query(self.entries, tag="eth")]
        self.assertEqual(ids, ["a-2026", "b-2026", "c-2026"])
        ids = [e["id"] for e in reg.query(list(reversed(self.entries)))]
        self.assertEqual(ids, ["e-2026", "a-2026", "b-2026", "c-2026", "d-2024"])

    def test_query_filters(self):
        self.assertEqual([e["id"] for e in reg.query(self.entries, since=2025, tag="lean")], ["b-2026"])
        self.assertEqual([e["id"] for e in reg.query(self.entries, text="RESOLUTION")], ["d-2024"])
        self.assertEqual([e["id"] for e in reg.query(self.entries, kind="claimed-p-vs-np-proof")], ["e-2026"])
        self.assertEqual(len(reg.query(self.entries, status="unreviewed-preprint")), 5)

    def test_render_is_idempotent_and_byte_identical(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "registry.json"
            path.write_text(json.dumps(registry(*self.entries)), encoding="utf-8")
            out = Path(tmp) / "REGISTRY.md"
            args = ["--registry", str(path), "--readme", "none", "--render"]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(reg.main(args), 0)
                first = out.read_bytes()
                self.assertEqual(reg.main(args), 0)
                self.assertEqual(reg.main(["--registry", str(path), "--readme", "none", "--check-render"]), 0)
            self.assertEqual(first, out.read_bytes())
            text = first.decode("utf-8")
            self.assertIn("must not be edited by hand", text)
            self.assertIn("## Claimed P vs NP proofs 2017-2026", text)
            self.assertLess(text.index("`a-2026`"), text.index("`b-2026`"))

    def test_check_render_detects_stale_file_and_main_rejects_invalid(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "registry.json"
            path.write_text(json.dumps(registry(*self.entries)), encoding="utf-8")
            (Path(tmp) / "REGISTRY.md").write_text("hand edit\n", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(reg.main(["--registry", str(path), "--readme", "none", "--check-render"]), 1)
            bad = copy.deepcopy(self.entries)
            bad[1]["id"] = "b-2026"
            path.write_text(json.dumps(registry(*bad)), encoding="utf-8")
            stderr = io.StringIO()
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(stderr):
                self.assertEqual(reg.main(["--registry", str(path), "--readme", "none"]), 1)
            self.assertIn("duplicate id 'b-2026'", stderr.getvalue())

    def test_readme_tag_table_must_match_vocabulary(self):
        with tempfile.TemporaryDirectory() as tmp:
            readme = Path(tmp) / "README.md"
            rows = "\n".join("| `{}` | x |".format(tag) for tag in sorted(reg.TAGS))
            readme.write_text("<!-- tags:start -->\n" + rows + "\n<!-- tags:end -->\n", encoding="utf-8")
            self.assertEqual(reg.validate_readme(readme), [])
            readme.write_text("<!-- tags:start -->\n| `eth` | x |\n| `hype` | y |\n<!-- tags:end -->\n", encoding="utf-8")
            errors = reg.validate_readme(readme)
            self.assertTrue(any("lacks" in e for e in errors) and any("hype" in e for e in errors), errors)


class DocumentationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.readme = self.root / "README.md"
        self.claimed = self.root / "CLAIMED.md"
        self.attempts = self.root / "attempts"
        (self.attempts / "old-author-2004-peqnp").mkdir(parents=True)
        self.data = registry(entry("a-2026", verified="no"), entry("b-2025", date="2025-01"),
                             entry("c-2026", attempt_slug="c-author-2026-peqnp"))
        self.claimed.write_text("Rows `a-2026`, `c-author-2026-peqnp`, `old-author-2004-peqnp`, `verified: no`, "
                                "`PEqualsNP`, `lean/docs/105.md`.\n", encoding="utf-8")

    def tearDown(self):
        self.tmp.cleanup()

    def check(self):
        return reg.validate_docs(self.data, self.readme, self.claimed, self.attempts)

    def test_consistent_documents_pass(self):
        self.readme.write_text(guide(["a-2026"], "- See `b-2025`.\n"), encoding="utf-8")
        self.assertEqual(self.check(), [])

    def test_known_gaps_must_match_verified_no(self):
        self.readme.write_text(guide([]), encoding="utf-8")
        self.assertTrue(any("omits verified: no entries a-2026" in e for e in self.check()))
        self.readme.write_text(guide(["a-2026", "b-2025"]), encoding="utf-8")
        self.assertTrue(any("lists b-2025 as verified: no" in e for e in self.check()))
        self.readme.write_text(TAG_TABLE + "\n## Known gaps\n\n- Nothing.\n", encoding="utf-8")
        self.assertTrue(any("missing the 'Entries with `verified: no`' bullet" in e for e in self.check()))

    def test_backticked_ids_must_exist(self):
        self.readme.write_text(guide(["a-2026"], "- See `ghost-2026-entry`.\n"), encoding="utf-8")
        self.assertTrue(any("`ghost-2026-entry` is not a registry id" in e for e in self.check()))
        self.readme.write_text(guide(["a-2026"]), encoding="utf-8")
        self.claimed.write_text("Row `missing-author-2019-pneqnp`.\n", encoding="utf-8")
        self.assertTrue(any("`missing-author-2019-pneqnp`" in e and "CLAIMED.md" in e for e in self.check()))

    def test_missing_guide_fails_and_cli_check_readme(self):
        self.assertTrue(any("guide not found" in e for e in self.check()))
        path = self.root / "registry.json"
        path.write_text(json.dumps(self.data), encoding="utf-8")
        args = ["--registry", str(path), "--readme", str(self.readme), "--claimed", str(self.claimed),
                "--check-readme"]
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(reg.main(args), 1)
        self.readme.write_text(guide(["a-2026"]), encoding="utf-8")
        with mock_attempts(self.attempts), contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(reg.main(args), 0)
        self.assertIn("documentation matches the registry", out.getvalue())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(reg.main(["--registry", str(path), "--readme", "none", "--check-readme"]), 1)


@contextlib.contextmanager
def mock_attempts(path):
    saved = reg.ATTEMPTS
    reg.ATTEMPTS = path
    try:
        yield
    finally:
        reg.ATTEMPTS = saved


class RepositoryRegistryTests(unittest.TestCase):
    @unittest.skipUnless(reg.REGISTRY.exists(), "repository registry not present")
    def test_repository_registry_and_guide_are_valid(self):
        data = reg.load(reg.REGISTRY)
        self.assertEqual(reg.validate(data), [])
        self.assertEqual(reg.validate_docs(data, reg.README, reg.CLAIMED_PROOFS, reg.ATTEMPTS), [])
        local = Counter(e["claim_status_local"] for e in data["entries"])
        self.assertEqual(local.get("locally-certified", 0), 0)



if __name__ == "__main__":
    unittest.main()
