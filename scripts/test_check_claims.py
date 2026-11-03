"""Tests for scripts/check_claims.py.

Each test builds a small repository in a temporary directory. No network,
no Lean or Rocq build. Run with ``python3 -I scripts/test_check_claims.py``.
"""

import contextlib
import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

_SCRIPT = Path(__file__).resolve().with_name('check_claims.py')
_SPEC = importlib.util.spec_from_file_location('check_claims', _SCRIPT)
checker = importlib.util.module_from_spec(_SPEC)
sys.modules.setdefault('check_claims', checker)
_SPEC.loader.exec_module(checker)

LEAN_PATH = 'proofs/demo/lean/Demo.lean'
ROCQ_PATH = 'proofs/demo/rocq/Demo.v'

LEAN = textwrap.dedent('''\
    namespace Demo
    def Prem : Prop := True
    def Other : Prop := True
    theorem good : True := trivial
    theorem cond (h : Prem) : True := trivial
    theorem uses_prem (h : Prem) : True := trivial
    theorem pending : True := trivial
    end Demo
''')

ROCQ = textwrap.dedent('''\
    Definition Prem : Prop := True.
    Definition Other : Prop := True.
    Theorem good : True.
    Proof. exact I. Qed.
    Theorem cond : Prem -> True.
    Proof. intros _. exact I. Qed.
    Theorem uses_prem : Prem -> True.
    Proof. intros _. exact I. Qed.
    Theorem pending : True.
    Proof. exact I. Qed.
''')

HYPOTHESES = textwrap.dedent('''\
    | name | class | lean (file:line) | rocq (file:line) | statement (one line) | reference | dependents | status |
    | --- | --- | --- | --- | --- | --- | --- | --- |
    | `Prem` | bridge | `lean/Demo.lean:2` | `rocq/Demo.v:1` | `True` | none | `cond` | open |
''')

STATUS = {
    'lean': [
        {'source': LEAN_PATH, 'theorem': 'Demo.good', 'allowed_axioms': []},
        {'source': LEAN_PATH, 'theorem': 'Demo.cond', 'allowed_axioms': []},
        {'source': LEAN_PATH, 'theorem': 'Demo.uses_prem',
         'allowed_axioms': []},
    ],
    'rocq': [
        {'source': ROCQ_PATH, 'theorem': 'good', 'allowed_axioms': []},
        {'source': ROCQ_PATH, 'theorem': 'cond', 'allowed_axioms': []},
        {'source': ROCQ_PATH, 'theorem': 'uses_prem', 'allowed_axioms': []},
    ],
}

REGISTRY = {'entries': [
    {'id': 'textbook', 'status': 'peer-reviewed'},
    {'id': 'preprint', 'status': 'unreviewed-preprint',
     'formal': {'declaration': 'Upstream.mainTheorem'}},
]}

HEADER = ('| id | claim | stated in (file) | check | reference | status |\n'
          '| --- | --- | --- | --- | --- | --- |\n')


def pair(name):
    return f'`{LEAN_PATH}::{name}`; `{ROCQ_PATH}::{name}`'


ROWS = {
    'good': ('Good holds.', 'README.md', 'formal', pair('good'), 'checked'),
    'cond': ('Cond holds under Prem.', 'README.md', 'formal-conditional',
             pair('cond') + '; premises: Prem', 'checked-conditional'),
    'ext': ('Upstream claims a theorem.', 'README.md', 'external-formal',
            'registry: preprint; upstream: `mainTheorem`', 'external'),
    'cite': ('A textbook theorem.', 'README.md', 'source',
             'registry: textbook', 'cited'),
    'count': ('The demo count is 7.', 'README.md', 'script',
              '`python3 -I scripts/count.py` expect=7', 'checked'),
    'counted': ('The match count is 7.', 'README.md', 'script',
                r'`python3 -I scripts/count.py --verbose` expect=7 '
                r'match=count:\s(\d+)', 'checked'),
    'todo': ('Pending holds.', 'README.md', 'unverified', pair('pending'),
             'to-formalize'),
    'loose': ('Nobody checked this.', 'README.md', 'unverified', '',
              'unverified'),
}

QUEUE = textwrap.dedent('''\

    ## Formalization queue

    ### 1. `todo`

    - Statement: `pending : True`.
    - Definitions: none.
    - Hypotheses: none.
    - Size: small.
    - Result class: known theorem mechanized.
    - Provenance: known theorem newly mechanized.

    ## Claims that cannot be formalized

    - `loose`: a fact about the world.
''')

COUNT_SCRIPT = textwrap.dedent('''\
    import sys
    value = int(open('count.txt').read())
    if '--verbose' in sys.argv:
        print(f'count: {value}')
    else:
        print(value)
''')


def ledger(rows):
    lines = [f'| `{ident}` | ' + ' | '.join(cells) + ' |'
             for ident, cells in rows.items()]
    return '# Claims\n\n' + HEADER + '\n'.join(lines) + '\n' + QUEUE


class CheckClaimsTest(unittest.TestCase):

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.rows = {k: list(v) for k, v in ROWS.items()}
        self.status = json.loads(json.dumps(STATUS))
        self.registry = json.loads(json.dumps(REGISTRY))
        self.write(LEAN_PATH, LEAN)
        self.write(ROCQ_PATH, ROCQ)
        self.write('_CoqProject', f'-Q . ""\n{ROCQ_PATH}\n')
        self.write('proofs/HYPOTHESES.md', HYPOTHESES)
        self.write('README.md', '# Demo\n')
        self.write('scripts/count.py', COUNT_SCRIPT)
        self.write('count.txt', '7\n')

    def tearDown(self):
        self._tmp.cleanup()

    def write(self, path, text):
        full = self.root / path
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text(text, encoding='utf-8')

    def run_check(self, run_scripts=False, queue=True):
        self.write('scripts/proof_status.json', json.dumps(self.status))
        self.write('literature/registry.json', json.dumps(self.registry))
        text = ledger({k: tuple(v) for k, v in self.rows.items()})
        if not queue:
            text = text.split('\n## Formalization queue')[0]
        self.write('CLAIMS.md', text)
        report, *_ = checker.check(self.root, run_scripts=run_scripts,
                                   timeout=60)
        return report.errors

    def assertFails(self, errors, fragment):
        self.assertTrue(any(fragment in e for e in errors),
                        f'no error containing {fragment!r} in {errors}')

    # -- baseline

    def test_baseline_passes_with_scripts(self):
        self.assertEqual(self.run_check(run_scripts=True), [])

    # -- required mutations

    def test_formal_claim_not_in_manifest_fails(self):
        self.status['lean'] = [e for e in self.status['lean']
                               if e['theorem'] != 'Demo.good']
        self.assertFails(self.run_check(), 'is not in scripts/proof_status.json')

    def test_unregistered_premise_fails(self):
        self.rows['cond'][3] = pair('cond') + '; premises: Prem, Other'
        errors = self.run_check()
        self.assertFails(errors, 'premise `Other` is not a row of')

    def test_unknown_registry_id_fails(self):
        self.rows['cite'][3] = 'registry: no-such-entry'
        self.assertFails(self.run_check(), "registry id 'no-such-entry'")

    def test_count_mismatch_with_run_scripts_fails(self):
        self.write('count.txt', '8\n')
        self.assertEqual(self.run_check(run_scripts=False), [])
        errors = self.run_check(run_scripts=True)
        self.assertFails(errors, 'gives 8, the ledger expects 7')
        self.assertEqual(sum('gives 8' in e for e in errors), 2)

    # -- further mutations

    def test_duplicate_and_bad_ids_fail(self):
        text = ledger({k: tuple(v) for k, v in self.rows.items()})
        row = text.splitlines()[4]
        bad = row.replace('`good`', '`Bad_Id`')
        self.write('scripts/proof_status.json', json.dumps(self.status))
        self.write('literature/registry.json', json.dumps(self.registry))
        self.write('CLAIMS.md', text.replace(row, row + '\n' + row + '\n' + bad))
        errors = checker.check(self.root)[0].errors
        self.assertFails(errors, 'duplicate id good')
        self.assertFails(errors, 'id is not kebab-case')

    def test_status_must_match_check_type(self):
        self.rows['loose'][4] = 'checked'
        self.assertFails(self.run_check(), "status 'checked' is not allowed")
        self.rows['loose'][4] = 'proved'
        self.assertFails(self.run_check(), "unknown status 'proved'")

    def test_formal_row_with_registered_premise_fails(self):
        self.rows['good'][3] = pair('uses_prem')
        self.assertFails(self.run_check(), 'takes the registered hypothesis')

    def test_conditional_claim_must_name_premises(self):
        self.rows['cond'][0] = 'Cond holds.'
        self.assertFails(self.run_check(), 'does not name premise `Prem`')

    def test_premise_missing_from_signature_fails(self):
        self.rows['cond'][3] = pair('good') + '; premises: Prem'
        self.assertFails(self.run_check(), 'does not occur in the signature')

    def test_undeclared_name_and_missing_files_fail(self):
        self.rows['good'][3] = pair('missing')
        self.rows['loose'][1] = 'NO_SUCH_FILE.md'
        errors = self.run_check()
        self.assertFails(errors, '`missing` is not declared')
        self.assertFails(errors, 'stated-in file NO_SUCH_FILE.md does not exist')

    def test_upstream_name_must_be_in_registry(self):
        self.rows['ext'][3] = 'registry: preprint; upstream: `otherTheorem`'
        self.assertFails(self.run_check(), "upstream name 'otherTheorem'")

    def test_cited_needs_reviewed_source(self):
        self.rows['cite'][3] = 'registry: preprint'
        self.assertFails(self.run_check(), 'status cited needs')
        self.rows['cite'][4] = 'unverified'
        self.assertEqual(self.run_check(), [])

    def test_to_formalize_needs_queue_and_uncertified_theorem(self):
        self.assertFails(self.run_check(queue=False),
                         'no "## Formalization queue" section')
        self.status['lean'].append({'source': LEAN_PATH,
                                    'theorem': 'Demo.pending',
                                    'allowed_axioms': []})
        self.assertFails(self.run_check(), 'promote the row to formal')

    def test_script_claim_must_contain_expected_value(self):
        self.rows['count'][0] = 'The demo count is seven.'
        self.assertFails(self.run_check(), 'does not contain the expected')
        self.rows['count'][0] = 'The demo count is 7.'
        self.rows['count'][3] = '`python3 -I other/count.py` expect=7'
        self.assertFails(self.run_check(), 'must run a file under')

    def test_command_line_exit_codes(self):
        self.assertEqual(self.run_check(), [])
        ok = subprocess.run([sys.executable, '-I', str(_SCRIPT), '--root',
                             str(self.root), '--stats'],
                            capture_output=True, text=True)
        self.assertEqual(ok.returncode, 0, ok.stderr)
        self.assertIn('check_claims: OK', ok.stdout)
        self.assertIn('formalization queue (1): todo', ok.stdout)
        count = subprocess.run([sys.executable, '-I', str(_SCRIPT), '--root',
                                str(self.root), '--count', 'certified-lean'],
                               capture_output=True, text=True)
        self.assertEqual(count.stdout.strip(), '3')
        self.rows['cite'][3] = 'registry: no-such-entry'
        self.run_check()
        bad = subprocess.run([sys.executable, '-I', str(_SCRIPT), '--root',
                              str(self.root)], capture_output=True, text=True)
        self.assertEqual(bad.returncode, 1)
        self.assertIn('FAIL', bad.stderr)

    def test_signature_binder_detection(self):
        self.assertTrue(checker.binds('theorem t (hard : SATHard) : X',
                                      'SATHard'))
        self.assertTrue(checker.binds('Theorem t : SATHard -> X.', 'SATHard'))
        self.assertTrue(checker.binds('theorem t (h : M.SATHard) : X',
                                      'SATHard'))
        self.assertFalse(checker.binds('theorem t : SATInNP', 'SATInNP'))
        self.assertFalse(checker.binds('theorem t : CookLevin ↔ SATHard',
                                       'SATHard'))

    def test_sat_verifier_state_counter(self):
        lean = textwrap.dedent("""\
            def triples : List (Bool × Bool × Bool) :=
              [(false, false, false), (true, true, true)]

            def allStates : List St :=
              [.a, .b, .c] ++
              triples.map (fun t => St.x t.1 t.2.1 t.2.2)

            """)
        rocq = textwrap.dedent("""\
            Definition triples : list (bool * (bool * bool)) :=
              [(false, (false, false)); (true, (true, true))].

            Definition allStates : list St :=
              [a; b; c] ++ map (fun t => x (fst t)) triples.

            """)
        self.write('proofs/experiments/issue532/lean/SATVerifier.lean', lean)
        self.write('proofs/experiments/issue532/rocq/SATVerifier.v', rocq)
        repo = checker.Repo(self.root)
        self.assertEqual(checker.counter(repo, 'sat-verifier-states'), 5)
        self.write('proofs/experiments/issue532/rocq/SATVerifier.v',
                   rocq.replace('[a; b; c]', '[a; b]'))
        repo = checker.Repo(self.root)
        self.assertEqual(checker.counter(repo, 'sat-verifier-states'), -1)

    # -- the real ledger

    def test_repository_ledger_passes_static_checks(self):
        report, rows, *_ = checker.check(checker.ROOT)
        self.assertEqual(report.errors, [])
        self.assertGreaterEqual(len(rows), 60)


if __name__ == '__main__':
    unittest.main(verbosity=2)
