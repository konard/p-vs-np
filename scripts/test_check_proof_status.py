"""Regression tests for the certified-result boundary."""

import tempfile
import unittest
import re
import json
from types import SimpleNamespace
from pathlib import Path
from unittest.mock import patch

from scripts.check_proof_status import (
    audit,
    check_sources,
    parse_lean_axioms,
    parse_rocq_assumptions,
    strip_comments_and_strings,
    query_assumptions,
)


class ProofStatusTests(unittest.TestCase):
    def test_typed_queries_audit_the_checked_term_in_both_provers(self):
        for language in ("lean", "rocq"):
            with self.subTest(language=language):
                suffix = "lean" if language == "lean" else "v"
                entry = {"source": f"proofs/Result.{suffix}", "theorem": "Result.endpoint"}
                probes = []

                def compile_probe(command, **_):
                    probes.append(Path(command[-1]).read_text())
                    output = ("'completion_contract' does not depend on any axioms\n" if language == "lean"
                              else "Closed under the global context\n")
                    return SimpleNamespace(returncode=0, stdout=output, stderr="")

                with patch("scripts.check_proof_status.subprocess.run", side_effect=compile_probe):
                    assumptions = query_assumptions(Path("."), language, entry, expected_type="True")
                self.assertEqual(assumptions, set())
                self.assertIn("@Result.endpoint", probes[0])
                self.assertIn("completion_contract : True :=", probes[0])
                self.assertIn("axioms completion_contract" if language == "lean" else "Assumptions completion_contract", probes[0])

    def test_issue532_public_results_have_assumption_policies(self):
        manifest = json.loads((Path(__file__).with_name('proof_status.json')).read_text())
        for language in ('lean', 'rocq'):
            names = {entry['theorem'].split('.')[-1] for entry in manifest[language]
                     if '/issue532/' in entry['source']}
            self.assertTrue({
                'satInNP', 'cookLevin_iff', 'pEqualsNP_of_inP_sat',
                'inP_sat_of_pEqualsNP', 'inP_sat_iff', 'inP_sat_on_encodings',
                "inP_sat_of_pEqualsNP'", 'cookLevin_iff_satHard',
                'inP_sat_iff_of_hard', 'polySATDecider_iff_of_hard',
            } <= names)
            # SATHard and PEqualsNP are explicit theorem premises, not
            # global axioms that the audit is allowed to overlook.
            for entry in manifest[language]:
                if '/issue532/' in entry['source']:
                    self.assertNotIn('SATHard', entry['allowed_axioms'])
                    self.assertNotIn('PEqualsNP', entry['allowed_axioms'])

    def test_false_historical_premises_are_explicit_parameters(self):
        root = Path(__file__).resolve().parents[1]
        for suffix, language in [('lean', 'lean'), ('v', 'rocq')]:
            for relative in (
                f'proofs/attempts/singh-anand-2006-pneqnp/refutation/{language}/SinghAnandRefutation.{suffix}',
                f'proofs/attempts/minseong-kim-2012-pneqnp/{language}/KimAttempt.{suffix}',
            ):
                with self.subTest(relative=relative):
                    source = strip_comments_and_strings((root / relative).read_text(), language)
                    self.assertIsNone(re.search(
                        r'\b(?:axiom|Axiom)\s+(?:singh_anand_inference|ZFC_inconsistent)\b', source
                    ))

    def test_imported_admission_blocks_certification(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dependency = root / 'proofs/base/Dependency.lean'
            dependency.parent.mkdir(parents=True)
            dependency.write_text('theorem hole : True := by sorry\n')
            source = root / 'proofs/result/Result.lean'
            source.parent.mkdir(parents=True)
            source.write_text('import proofs.base.Dependency\ntheorem result : True := by trivial\n')
            manifest = {'lean': [{'source': 'proofs/result/Result.lean',
                                  'theorem': 'result', 'allowed_axioms': []}]}
            failures = audit(root, manifest, ['lean'], False)
            self.assertEqual(len(failures), 1)
            self.assertIn('proofs/base/Dependency.lean:1', failures[0])

    def test_direct_rocq_imported_admission_blocks_certification(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dependency = root / 'proofs/base/Dependency.v'
            dependency.parent.mkdir(parents=True)
            dependency.write_text('Theorem hole : True. Admitted.\n')
            source = root / 'proofs/result/Result.v'
            source.parent.mkdir(parents=True)
            source.write_text('Require Import proofs.base.Dependency.\nTheorem result : True. Proof. exact I. Qed.\n')
            manifest = {'rocq': [{'source': 'proofs/result/Result.v',
                                  'theorem': 'result', 'allowed_axioms': []}]}
            failures = audit(root, manifest, ['rocq'], False)
            self.assertEqual(len(failures), 1)
            self.assertIn('proofs/base/Dependency.v:1', failures[0])

    def test_unapproved_prover_assumption_blocks_certification(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'proofs/result/Result.lean'
            source.parent.mkdir(parents=True)
            source.write_text('theorem result : True := by trivial\n')
            manifest = {'lean': [{'source': 'proofs/result/Result.lean',
                                  'theorem': 'result', 'allowed_axioms': []}]}
            with patch('scripts.check_proof_status.query_assumptions', return_value={'custom.bad'}):
                failures = audit(root, manifest, ['lean'], True)
            self.assertEqual(len(failures), 1)
            self.assertIn('custom.bad', failures[0])

    def test_comments_and_strings_do_not_count_as_admissions(self):
        lean = 'theorem t : True := by trivial\n/- sorry /- axiom -/ -/\n-- admit\n#check "sorry"\n'
        rocq = 'Theorem t : True. Proof. exact I. Qed.\n(* Admitted. (* Axiom x *) *)\n'
        self.assertNotIn('sorry', strip_comments_and_strings(lean, 'lean'))
        self.assertNotIn('Admitted', strip_comments_and_strings(rocq, 'rocq'))

    def test_certified_source_rejects_admissions_and_axioms(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean = root / 'Certified.lean'
            rocq = root / 'Certified.v'
            lean.write_text('theorem fake : False := by sorry\naxiom trap : False\n')
            rocq.write_text('Theorem fake : False. Admitted.\nAxiom trap : False.\n')
            failures = check_sources(root, [lean, rocq])
            self.assertEqual(len(failures), 4)

    def test_lean_axioms_are_parsed_and_checked_by_name(self):
        self.assertEqual(parse_lean_axioms("'A' depends on axioms: [propext, Classical.choice]\n"),
                         {'propext', 'Classical.choice'})
        self.assertEqual(parse_lean_axioms("'A' does not depend on any axioms\n"), set())
        with self.assertRaises(ValueError):
            parse_lean_axioms('some unrelated compiler output')

    def test_rocq_assumptions_are_parsed_and_checked_by_name(self):
        self.assertEqual(parse_rocq_assumptions('Closed under the global context\n'), set())
        self.assertEqual(parse_rocq_assumptions('Axioms:\nclassical : forall P : Prop, P \\/ ~ P\n'),
                         {'classical'})
        with self.assertRaises(ValueError):
            parse_rocq_assumptions('some unrelated compiler output')


if __name__ == '__main__':
    unittest.main()
