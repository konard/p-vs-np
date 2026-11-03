"""Tests for scripts/check_formal_statement.py.

Each test builds a small repository in a temporary directory. No network.
Run with ``python3 -m unittest scripts.test_check_formal_statement -v``.
"""

import contextlib
import importlib.util
import io
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

_SCRIPT = Path(__file__).resolve().with_name('check_formal_statement.py')
_SPEC = importlib.util.spec_from_file_location('check_formal_statement', _SCRIPT)
checker = importlib.util.module_from_spec(_SPEC)
sys.modules.setdefault('check_formal_statement', checker)
_SPEC.loader.exec_module(checker)

LEAN = textwrap.dedent('''\
    namespace Demo

    def PEqualsNP : Prop := True

    /-- **Known theorem, not mechanised here.** A bridge. -/
    def Bridge : Prop := True

    theorem target_of_bridge (h : Bridge) : PEqualsNP := trivial

    def PNotEqualsNP : Prop := ¬PEqualsNP

    end Demo
''')

ROCQ = textwrap.dedent('''\
    Definition PEqualsNP : Prop := True.

    (** Known theorem, not mechanised here. A bridge. *)
    Definition Bridge : Prop := True.
''')

AGDA = textwrap.dedent('''\
    module Demo where

    PEqualsNP : Set
    PEqualsNP = Empty
''')

HYPOTHESES = textwrap.dedent('''\
    # Named hypotheses

    <!-- path-base: proofs/demo/ -->

    | name | class | lean (file:line) | rocq (file:line) | statement (one line) | reference | dependents | status |
    | --- | --- | --- | --- | --- | --- | --- | --- |
    | `Bridge` | bridge | `lean/Demo.lean:6` | `rocq/Demo.v:4` | `True` | none | `target_of_bridge` | open |
''')

STATEMENT = textwrap.dedent('''\
    # Statement

    <!-- verbatim-from: proofs/demo/lean/Demo.lean -->
    ```lean
    -- proofs/demo/lean/Demo.lean:3-6
    def PEqualsNP : Prop := True
    def Bridge : Prop := True
    -- :10
    def PNotEqualsNP : Prop := ¬PEqualsNP
    ```

    The target is `PEqualsNP` (`proofs/demo/lean/Demo.lean:3`), and the bridge
    is `target_of_bridge`
    (`proofs/demo/lean/Demo.lean:8`).

    | edge (from → to) | theorem | file:line | premise | certified | status |
    | --- | --- | --- | --- | --- | --- |
    | `True` → `PEqualsNP` | `target_of_bridge` | `proofs/demo/lean/Demo.lean:8` | `Bridge` | yes | open |

    ```claims
    # comment lines are ignored
    proofs/demo/lean/Demo.lean::PEqualsNP
    proofs/demo/lean/Demo.lean::target_of_bridge
    proofs/demo/rocq/Demo.v::Bridge
    proofs/demo/agda/Demo.agda::PEqualsNP
    ```
''')


PROOF_STATUS = textwrap.dedent('''\
    {"lean": [{"source": "proofs/demo/lean/Demo.lean", "theorem": "Demo.target_of_bridge",
               "allowed_axioms": []}],
     "rocq": []}
''')

DISCHARGED_DEFECT = textwrap.dedent('''\

    ## Known defects

    - **Discharged but still a parameter.** `Bridge` is proved, yet
      `target_of_bridge` still takes it.
''')


class CheckFormalStatementTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.write('proofs/demo/lean/Demo.lean', LEAN)
        self.write('proofs/demo/rocq/Demo.v', ROCQ)
        self.write('proofs/demo/agda/Demo.agda', AGDA)
        self.write('proofs/HYPOTHESES.md', HYPOTHESES)
        self.write('FORMAL_STATEMENT.md', STATEMENT)
        self.write('scripts/proof_status.json', PROOF_STATUS)

    def tearDown(self):
        self._tmp.cleanup()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding='utf-8')

    def read(self, relative):
        return (self.root / relative).read_text(encoding='utf-8')

    def edit(self, relative, old, new):
        text = self.read(relative)
        self.assertIn(old, text)
        self.write(relative, text.replace(old, new, 1))

    def run_checker(self, *extra):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = checker.main(['--root', str(self.root), *extra])
        return code, out.getvalue(), err.getvalue()

    def test_consistent_tree_passes(self):
        code, out, err = self.run_checker()
        self.assertEqual(code, 0, err)
        self.assertIn('4 claims', out)
        self.assertIn('1 result-graph rows checked', out)
        self.assertIn('1 rows (bridge 1,', out)
        self.assertIn('0 unregistered', out)
        self.assertNotIn('WARN', out)

    def test_unregistered_hypothesis_fails(self):
        # Mutation test: a new marked hypothesis without a table row.
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- Known theorem, not mechanised here. -/\n'
                  'def NewBridge : Prop := True\n\nend Demo')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: NewBridge', err)

    def test_unregistered_rocq_hypothesis_with_multiline_signature_fails(self):
        self.write('proofs/demo/rocq/Demo.v', ROCQ +
                   '\n(** Not mechanized: a second bridge. *)\n'
                   'Definition Other (n : nat)\n  : Prop := True.\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: Other', err)
        self.assertEqual(err.count('FAIL'), 2, err)

    def test_marker_inside_previous_definition_is_ignored(self):
        # The marker is a comment inside an earlier body, not the comment of
        # the next definition, so the next definition is not a hypothesis.
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  'def Earlier : Prop :=\n  True  -- Known theorem - assumed\n\n'
                  '/-- Plain. -/\ndef Later : Prop := True\n\nend Demo')
        code, _, err = self.run_checker()
        self.assertEqual(code, 0, err)

    def test_missing_claim_fails(self):
        self.edit('FORMAL_STATEMENT.md', '::target_of_bridge', '::no_such_theorem')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('does not declare no_such_theorem', err)

    def test_missing_file_in_claims_fails(self):
        self.edit('FORMAL_STATEMENT.md', 'proofs/demo/rocq/Demo.v::Bridge',
                  'proofs/demo/rocq/Missing.v::Bridge')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('Missing.v does not exist', err)

    def test_small_drift_warns_and_large_drift_fails(self):
        self.edit('proofs/HYPOTHESES.md', '`lean/Demo.lean:6`', '`lean/Demo.lean:4`')
        code, out, err = self.run_checker()
        self.assertEqual(code, 0, err)
        self.assertIn('WARN', out)
        self.assertIn('declared at proofs/demo/lean/Demo.lean:6', out)
        self.edit('proofs/HYPOTHESES.md', '`lean/Demo.lean:4`', '`lean/Demo.lean:1`')
        self.edit('proofs/demo/lean/Demo.lean', 'namespace Demo\n',
                  'namespace Demo\n' + '\n' * 10)
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`Bridge` is declared at proofs/demo/lean/Demo.lean:16, not at line 1', err)
        self.assertIn('comment says lines 3-6, but the segment is at '
                      'proofs/demo/lean/Demo.lean:13-16', err)

    def test_wrong_line_in_statement_table_and_prose_fails(self):
        self.edit('FORMAL_STATEMENT.md', '| `proofs/demo/lean/Demo.lean:8` |',
                  '| `proofs/demo/lean/Demo.lean:20` |')
        self.edit('FORMAL_STATEMENT.md', '(`proofs/demo/lean/Demo.lean:3`)',
                  '(`proofs/demo/lean/Demo.lean:30`)')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`target_of_bridge` is declared at proofs/demo/lean/Demo.lean:8, '
                      'not at line 20', err)
        self.assertIn('`PEqualsNP` is declared at proofs/demo/lean/Demo.lean:3, '
                      'not at line 30', err)

    def test_write_lines_repairs_moved_declarations(self):
        self.edit('proofs/demo/lean/Demo.lean', 'namespace Demo\n',
                  'namespace Demo\n' + '\n' * 10)
        self.assertEqual(self.run_checker()[0], 1)
        code, out, err = self.run_checker('--write-lines')
        self.assertEqual(code, 0, err)
        self.assertIn('--write-lines: updated', out)
        self.assertNotIn('WARN', out)
        self.assertIn('`lean/Demo.lean:16`', self.read('proofs/HYPOTHESES.md'))
        statement = self.read('FORMAL_STATEMENT.md')
        self.assertIn('(`proofs/demo/lean/Demo.lean:13`)', statement)
        self.assertIn('| `proofs/demo/lean/Demo.lean:18` |', statement)
        self.assertIn('-- proofs/demo/lean/Demo.lean:13-16\n', statement)
        self.assertIn('-- :20\n', statement)
        self.assertEqual(self.run_checker()[0], 0)

    def test_bad_class_and_status_fail(self):
        self.edit('proofs/HYPOTHESES.md', '| bridge |', '| folklore |')
        self.edit('proofs/HYPOTHESES.md', '| open |', '| in progress #12 |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn("class 'folklore'", err)
        self.assertIn("status 'in progress #12'", err)

    def test_allowed_status_values_pass(self):
        for status in ('in progress (PR #630, unmerged)',
                       'discharged in PR #631 (unmerged)'):
            self.write('proofs/HYPOTHESES.md', HYPOTHESES.replace('| open |', f'| {status} |'))
            code, _, err = self.run_checker()
            self.assertEqual(code, 0, f'{status}: {err}')

    def test_wrong_columns_fail(self):
        self.edit('proofs/HYPOTHESES.md', '| reference | dependents |',
                  '| source | dependents |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('columns are', err)

    def test_summary_box_must_be_verbatim(self):
        self.edit('FORMAL_STATEMENT.md', 'def PNotEqualsNP : Prop := ¬PEqualsNP\n```',
                  'def PNotEqualsNP : Prop := PEqualsNP\n```')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('does not occur in proofs/demo/lean/Demo.lean', err)

    # ---- mutations M1-M8 of the 2026-11-03 review (each must be rejected)

    def test_m1_premise_deleted_from_result_graph_fails(self):
        self.edit('FORMAL_STATEMENT.md', '| `Bridge` | yes |', '| none | yes |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('takes the hypothesis `Bridge`, which the premise cell does not list', err)

    def test_m1_premise_added_to_result_graph_fails(self):
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- Open obligation. -/\ndef Other : Prop := True\n\nend Demo')
        self.edit('proofs/HYPOTHESES.md', '| open |\n',
                  '| open |\n| `Other` | obligation | `lean/Demo.lean:12` | '
                  '`rocq/Demo.v:4` | `True` | none | none | open |\n')
        self.edit('proofs/demo/rocq/Demo.v', 'Definition Bridge',
                  '(** Open obligation. *)\nDefinition Other : Prop := True.\n\nDefinition Bridge')
        self.edit('proofs/HYPOTHESES.md', '`rocq/Demo.v:4` | `True` | none | `target',
                  '`rocq/Demo.v:7` | `True` | none | `target')
        self.edit('FORMAL_STATEMENT.md', '| `Bridge` | yes |', '| `Bridge`, `Other` | yes |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1, err)
        self.assertIn('premise `Other` is listed for `target_of_bridge`, but its signature', err)

    def test_m2_summary_box_order_and_line_comments_are_checked(self):
        swapped = ('-- :10\ndef PNotEqualsNP : Prop := ¬PEqualsNP\n'
                   '-- proofs/demo/lean/Demo.lean:3-6\ndef PEqualsNP : Prop := True\n'
                   'def Bridge : Prop := True\n')
        original = ('-- proofs/demo/lean/Demo.lean:3-6\ndef PEqualsNP : Prop := True\n'
                    'def Bridge : Prop := True\n-- :10\ndef PNotEqualsNP : Prop := ¬PEqualsNP\n')
        self.edit('FORMAL_STATEMENT.md', original, swapped)
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('comes before the previous segment', err)
        # Lines swapped inside one segment.
        self.edit('FORMAL_STATEMENT.md', swapped, original.replace(
            'def PEqualsNP : Prop := True\ndef Bridge : Prop := True\n',
            'def Bridge : Prop := True\ndef PEqualsNP : Prop := True\n'))
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        # A wrong line number in a comment.
        self.write('FORMAL_STATEMENT.md', STATEMENT.replace('-- :10\n', '-- :11\n'))
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('comment says lines 11, but the segment is at '
                      'proofs/demo/lean/Demo.lean:10', err)

    def test_m3_removed_dependent_fails(self):
        self.edit('proofs/HYPOTHESES.md', '| `target_of_bridge` |', '| none |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('dependents of `Bridge` say none, but 1 Lean theorem(s) take it', err)

    def test_m3_wrong_dependent_and_wrong_total_fail(self):
        self.edit('proofs/HYPOTHESES.md', '| `target_of_bridge` |',
                  '| `target_of_bridge`, `no_such_theorem` |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`no_such_theorem` is listed as a dependent of `Bridge`', err)
        self.write('proofs/HYPOTHESES.md', HYPOTHESES.replace(
            '| `target_of_bridge` |', '| `target_of_bridge`, … (2 total) |'))
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('say 2 total, but 1 Lean theorems take it', err)

    def test_m3_class_against_marker_and_statement_fail(self):
        self.edit('proofs/HYPOTHESES.md', '| bridge |', '| obligation |')
        self.edit('proofs/HYPOTHESES.md', '| `True` |', '| `False` |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('is marked as a known theorem', err)
        self.assertIn('the statement mentions `False`', err)

    def test_m4_open_obligation_marker_is_a_marker(self):
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- **Open obligation.** A new route. -/\n'
                  'def NewRoute : Prop := True\n\nend Demo')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: NewRoute', err)

    def test_m5_marked_agda_hypothesis_fails(self):
        self.write('proofs/demo/agda/Demo.agda', AGDA +
                   '\n-- Known theorem, not mechanised here.\n'
                   'AgdaBridge : Set\nAgdaBridge = Empty\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: AgdaBridge', err)
        # An Agda twin of a registered name is accepted.
        self.write('proofs/demo/agda/Demo.agda', AGDA +
                   '\n-- Known theorem, not mechanised here.\nBridge : Set\nBridge = Empty\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 0, err)

    def test_m6_abbrev_structure_and_inductive_forms_fail(self):
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- Known theorem, not mechanised here. -/\n'
                  'abbrev ShortBridge : Prop := True\n\n'
                  '/-- Known theorem, not mechanised here. -/\n'
                  'structure BoxBridge : Prop where\n  holds : True\n\nend Demo')
        self.write('proofs/demo/rocq/Demo.v', ROCQ +
                   '\n(** Not mechanized. *)\nInductive IndBridge : Prop := mk.\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: BoxBridge, IndBridge, ShortBridge', err)

    def test_m7_marker_far_above_the_definition_still_counts(self):
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- **Known theorem, not mechanised here.**\n\n  A long\n  docstring\n'
                  '  of many lines. -/\n\n\n\n\ndef FarBridge : Prop := True\n\nend Demo')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('unregistered hypotheses: FarBridge', err)

    def test_m8_deleted_row_of_unmarked_hypothesis_fails(self):
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  'def Unmarked : Prop := True\n\n'
                  'theorem uses_unmarked (h : Unmarked) : PEqualsNP := trivial\n\nend Demo')
        self.edit('proofs/demo/rocq/Demo.v', 'Definition PEqualsNP : Prop := True.\n',
                  'Definition PEqualsNP : Prop := True.\nDefinition Unmarked : Prop := True.\n')
        self.edit('proofs/HYPOTHESES.md', '`rocq/Demo.v:4` | `True` | none | `target',
                  '`rocq/Demo.v:5` | `True` | none | `target')
        row = ('| `Unmarked` | bridge | `lean/Demo.lean:12` | `rocq/Demo.v:2` | `True` | '
               'none | `uses_unmarked` | open |\n')
        defects = ('\n## Known defects\n\n- **Missing markers.** `Unmarked` has no marker.\n')
        self.edit('proofs/HYPOTHESES.md', '| open |\n', '| open |\n' + row)
        self.write('proofs/HYPOTHESES.md', self.read('proofs/HYPOTHESES.md') + defects)
        code, _, err = self.run_checker()
        self.assertEqual(code, 0, err)
        self.edit('proofs/HYPOTHESES.md', row, '')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`Unmarked` is listed under Missing markers but has no row', err)

    def test_unmarked_row_must_be_listed_under_missing_markers(self):
        self.edit('proofs/demo/lean/Demo.lean', '/-- **Known theorem, not mechanised here.** '
                  'A bridge. -/\n', '/-- A bridge. -/\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('the Lean definition of `Bridge` has no marker comment', err)

    # ---- further checks

    def test_row_that_is_no_longer_a_prop_definition_fails(self):
        self.edit('proofs/demo/lean/Demo.lean', 'def Bridge : Prop := True',
                  'def Bridge : Nat := 0')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`Bridge` is no longer a Prop definition', err)

    def test_not_defined_row(self):
        row = ('| `Future` | simulation | not defined | not defined | a known theorem | '
               'folklore | none | open |\n')
        self.edit('proofs/HYPOTHESES.md', '| open |\n', '| open |\n' + row)
        code, _, err = self.run_checker()
        self.assertEqual(code, 0, err)
        self.edit('proofs/demo/lean/Demo.lean', 'end Demo',
                  '/-- Known theorem, not mechanised here. -/\n'
                  'def Future : Prop := True\n\nend Demo')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn("`Future` is marked 'not defined', but it is defined", err)

    def test_certified_column_must_match_proof_status(self):
        self.edit('FORMAL_STATEMENT.md', '| `Bridge` | yes |', '| `Bridge` | no |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn("certified is 'no', but scripts/proof_status.json lists", err)
        self.write('FORMAL_STATEMENT.md', STATEMENT)
        self.write('scripts/proof_status.json', '{"lean": [], "rocq": []}')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn("certified is 'yes', but scripts/proof_status.json does not list", err)

    def test_certified_and_proved_wording_needs_proof_status(self):
        self.write('scripts/proof_status.json', '{"lean": [], "rocq": []}')
        self.edit('FORMAL_STATEMENT.md', '| `Bridge` | yes |', '| `Bridge` | no |')
        self.edit('FORMAL_STATEMENT.md', 'and the bridge\n', 'and the certified bridge\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`target_of_bridge` is called certified', err)
        self.edit('FORMAL_STATEMENT.md', 'and the certified bridge\n', 'and the proved bridge\n')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`target_of_bridge` is called proved', err)
        self.edit('FORMAL_STATEMENT.md', '(`proofs/demo/lean/Demo.lean:8`).',
                  '(`proofs/demo/lean/Demo.lean:8`; not certified).')
        code, _, err = self.run_checker()
        self.assertEqual(code, 0, err)

    def test_discharged_hypothesis_still_a_premise(self):
        self.edit('proofs/HYPOTHESES.md', '| open |', '| discharged on main |')
        code, _, err = self.run_checker()
        self.assertEqual(code, 1)
        self.assertIn('`Bridge` is discharged on main but still a premise', err)
        self.write('proofs/HYPOTHESES.md',
                   self.read('proofs/HYPOTHESES.md') + DISCHARGED_DEFECT)
        code, out, err = self.run_checker()
        self.assertEqual(code, 0, err)
        self.assertIn('WARN', out)
        code, _, err = self.run_checker('--strict')
        self.assertEqual(code, 1)
        self.assertIn('(strict)', err)

    def test_repository_documents_pass(self):
        root = Path(__file__).resolve().parents[1]
        if not (root / 'FORMAL_STATEMENT.md').is_file():
            self.skipTest('FORMAL_STATEMENT.md is not present')
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = checker.main(['--root', str(root)])
        self.assertEqual(code, 0, err.getvalue())


if __name__ == '__main__':
    unittest.main()
