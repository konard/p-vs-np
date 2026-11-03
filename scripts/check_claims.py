#!/usr/bin/env python3
"""Check the claims ledger in CLAIMS.md against the repository.

The ledger is one Markdown table with the columns
``id | claim | stated in (file) | check | reference | status``.

Checks:

1. Ids are unique kebab-case. Check types and statuses are known values,
   and the status is allowed for the check type.
2. Every file in "stated in" exists.
3. Every ``path::Name`` in a reference names a file that declares ``Name``.
4. ``formal``: at least one Lean and one Rocq ``path::Name``. Each is listed
   in scripts/proof_status.json, and its signature takes no hypothesis
   registered in proofs/HYPOTHESES.md as an argument.
5. ``formal-conditional``: ``path::Name`` items and ``premises: A, B``. Each
   premise is a row of proofs/HYPOTHESES.md and occurs in every signature.
   The Lean file is under proofs/ (built by ``lake build``) and the Rocq file
   is listed in _CoqProject. The claim text names every premise, so that a
   conditional row never reads as unconditional.
6. ``external-formal``: ``registry: ids; upstream: `X```. The ids exist in
   literature/registry.json and ``X`` occurs in the ``formal.declaration`` of
   one of them.
7. ``source``: ``registry: ids`` that exist. Status ``cited`` needs at least
   one entry with status ``peer-reviewed`` or ``formally-checked``.
8. ``script``: a backticked command, ``expect=N`` and optional
   ``match=REGEX``. The first file argument is under scripts/ or
   experiments/, and the claim text contains ``N``. With ``--run-scripts``
   the command runs from the repository root. Its output (or the first
   group of ``REGEX`` in it) must equal ``N``.
9. ``unverified`` and ``to-formalize`` rows need no reference. A
   ``to-formalize`` row may not name a theorem that is already certified.
10. Every ``to-formalize`` row has exactly one entry in the formalization
    queue, and each queue entry has the required fields. Every id in the
    list of claims that cannot be formalized is a ledger row with a
    ``source``, ``unverified`` or ``external-formal`` check.

``--count NAME`` prints one integer computed from repository files. Script
rows use it. ``--stats`` prints a summary. Standard library only.
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = 'CLAIMS.md'
PROOF_STATUS = 'scripts/proof_status.json'
HYPOTHESES = 'proofs/HYPOTHESES.md'
REGISTRY = 'literature/registry.json'
COQ_PROJECT = '_CoqProject'

COLUMNS = ['id', 'claim', 'stated in (file)', 'check', 'reference', 'status']
STATUSES = ('checked', 'checked-conditional', 'external', 'cited',
            'unverified', 'to-formalize')
ALLOWED = {
    'formal': ('checked',),
    'formal-conditional': ('checked-conditional',),
    'external-formal': ('external',),
    'script': ('checked',),
    'source': ('cited', 'to-formalize', 'unverified'),
    'unverified': ('unverified', 'to-formalize'),
}
CITABLE = ('peer-reviewed', 'formally-checked')
SIZES = ('small', 'medium', 'large')
RESULT_CLASSES = (
    'known theorem mechanized', 'algorithm-specific refutation',
    'restricted-model lower bound', 'conditional general result',
    'unconditional general result',
)
QUEUE_FIELDS = ('Statement', 'Definitions', 'Hypotheses', 'Size',
                'Result class', 'Provenance')
SCRIPT_DIRS = ('scripts/', 'experiments/')
INTERPRETERS = ('python3', 'python', 'bash', 'sh')
KEYWORDS = (
    'theorem|def|lemma|abbrev|structure|inductive|'
    'Theorem|Definition|Lemma|Inductive|Record|Fixpoint|Corollary'
)

ID = re.compile(r'^[a-z0-9]+(?:-[a-z0-9]+)*$')
DECL = re.compile(r"(?P<path>[\w./-]+\.(?:lean|v|agda))::(?P<name>[A-Za-z_][\w'.]*)")
FIELD = re.compile(r'\b(premises|registry|upstream):\s*([^;]*)')
COMMAND = re.compile(r'`([^`]+)`')
EXPECT = re.compile(r'\bexpect=(\d+)\b')
MATCH = re.compile(r'\bmatch=(\S+)')
HYP_ROW = re.compile(r"^\|\s*`([A-Za-z_][\w'.]*)`")
QUEUE_HEAD = re.compile(r'^###\s+\d+\.\s+`([^`]+)`')
CANNOT_ITEM = re.compile(r'^-\s+`([^`]+)`')
CELL_SPLIT = re.compile(r'(?<!\\)\|')


@dataclass
class Report:
    errors: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    def fail(self, message: str) -> None:
        self.errors.append(message)


@dataclass
class Row:
    line: int
    id: str
    claim: str
    stated: str
    check: str
    reference: str
    status: str


@dataclass
class Decl:
    path: str
    name: str
    line: int
    signature: str


# --------------------------------------------------------------------------
# Repository data


class Repo:
    """Cached repository files under one root."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._lines: dict[str, list[str] | None] = {}
        self._status: dict | None = None
        self._hyps: set[str] | None = None
        self._registry: dict[str, dict] | None = None
        self._coq: set[str] | None = None

    def lines(self, path: str) -> list[str] | None:
        if path not in self._lines:
            full = self.root / path
            self._lines[path] = (full.read_text(encoding='utf-8').splitlines()
                                 if full.is_file() else None)
        return self._lines[path]

    def proof_status(self) -> dict:
        if self._status is None:
            path = self.root / PROOF_STATUS
            self._status = (json.loads(path.read_text(encoding='utf-8'))
                            if path.is_file() else {'lean': [], 'rocq': []})
        return self._status

    def hypotheses(self) -> set[str]:
        if self._hyps is None:
            names = set()
            for text in self.lines(HYPOTHESES) or []:
                match = HYP_ROW.match(text)
                if match and match[1] != 'name':
                    names.add(match[1])
            self._hyps = names
        return self._hyps

    def registry(self) -> dict[str, dict]:
        if self._registry is None:
            path = self.root / REGISTRY
            data = (json.loads(path.read_text(encoding='utf-8'))
                    if path.is_file() else {'entries': []})
            self._registry = {e.get('id'): e for e in data.get('entries', [])}
        return self._registry

    def coq_project(self) -> set[str]:
        if self._coq is None:
            self._coq = {t.strip() for t in self.lines(COQ_PROJECT) or []
                         if t.strip() and not t.strip().startswith('-')}
        return self._coq

    def find(self, path: str, name: str) -> Decl | None:
        """The first declaration of ``name`` (or its last dotted part)."""
        lines = self.lines(path)
        if lines is None:
            return None
        candidates = [name]
        if '.' in name:
            candidates.append(name.rsplit('.', 1)[1])
        for candidate in candidates:
            pattern = re.compile(
                rf"\b(?:{KEYWORDS})\s+{re.escape(candidate)}(?![\w'.])")
            for index, text in enumerate(lines):
                if pattern.search(text):
                    return Decl(path, name, index + 1,
                                signature(lines, index, path))
        return None

    def certified(self, path: str, name: str) -> bool:
        prover = 'lean' if path.endswith('.lean') else 'rocq'
        short = name.rsplit('.', 1)[-1]
        for entry in self.proof_status().get(prover, []):
            if (entry.get('source') == path
                    and entry.get('theorem', '').rsplit('.', 1)[-1] == short):
                return True
        return False


def signature(lines: list[str], index: int, path: str) -> str:
    """Declaration text up to ``:=`` (Lean) or the closing period (Rocq)."""
    parts = []
    for text in lines[index:index + 25]:
        cut = re.split(r':=|\bProof\b', text, maxsplit=1)
        parts.append(cut[0])
        if len(cut) > 1:
            break
        if path.endswith('.v') and text.rstrip().endswith('.'):
            break
    return ' '.join(' '.join(parts).split())


def binds(sig: str, name: str) -> bool:
    """``sig`` takes ``name`` as an argument: ``(h : name``, ``name ->``."""
    qualified = rf"(?:[\w']+\.)*{re.escape(name)}(?![\w'])"
    return bool(re.search(rf"[({{\[]\s*[\w' ]*:\s*{qualified}", sig)
                or re.search(rf"\[\s*{qualified}", sig)
                or re.search(rf"{qualified}\s*(?:→|->)", sig))


# --------------------------------------------------------------------------
# Ledger parsing


def cells(text: str) -> list[str] | None:
    stripped = text.strip()
    if not (stripped.startswith('|') and stripped.endswith('|')):
        return None
    parts = CELL_SPLIT.split(stripped)[1:-1]
    return [p.strip().replace('\\|', '|') for p in parts]


def section(lines: list[str], title: str) -> list[tuple[int, str]]:
    """Numbered lines of the ``## title`` section, up to the next ``## ``."""
    out, inside = [], False
    for number, text in enumerate(lines, 1):
        if text.startswith('## '):
            inside = text[3:].strip().lower().startswith(title.lower())
            continue
        if inside:
            out.append((number, text))
    return out


def parse_ledger(lines: list[str], report: Report) -> list[Row]:
    rows: list[Row] = []
    header = None
    for number, text in enumerate(lines, 1):
        row = cells(text)
        if row is not None and [c.lower() for c in row] == COLUMNS:
            header = number
            break
    if header is None:
        report.fail(f'{LEDGER}: no table with columns {" | ".join(COLUMNS)}')
        return rows
    for number in range(header + 2, len(lines) + 1):
        row = cells(lines[number - 1])
        if row is None:
            break
        if len(row) != len(COLUMNS):
            report.fail(f'{LEDGER}:{number}: {len(row)} cells, expected '
                        f'{len(COLUMNS)}')
            continue
        ident = row[0].strip('`')
        rows.append(Row(number, ident, row[1], row[2], row[3].strip('`'),
                        row[4], row[5].strip('`')))
    return rows


def fields(reference: str) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for key, value in FIELD.findall(reference):
        items = [v.strip().strip('`').strip() for v in value.split(',')]
        out.setdefault(key, []).extend(i for i in items if i)
    return out


def stated_files(cell: str) -> list[str]:
    return [p.strip().strip('`') for p in cell.split(',') if p.strip()]


# --------------------------------------------------------------------------
# Row checks


def check_row(row: Row, repo: Repo, report: Report,
              decls: dict[str, list[Decl]]) -> None:
    where = f'{LEDGER}:{row.line}: {row.id}'
    if not ID.match(row.id):
        report.fail(f'{where}: id is not kebab-case')
    if row.check not in ALLOWED:
        report.fail(f'{where}: unknown check type {row.check!r}')
        return
    if row.status not in STATUSES:
        report.fail(f'{where}: unknown status {row.status!r}')
        return
    if row.status not in ALLOWED[row.check]:
        report.fail(f'{where}: status {row.status!r} is not allowed for check '
                    f'{row.check!r} (allowed: {", ".join(ALLOWED[row.check])})')
    if not row.claim:
        report.fail(f'{where}: empty claim')
    stated = stated_files(row.stated)
    if not stated:
        report.fail(f'{where}: no "stated in" file')
    for path in stated:
        if not (repo.root / path).is_file():
            report.fail(f'{where}: stated-in file {path} does not exist')

    found: list[Decl] = []
    for match in DECL.finditer(row.reference):
        path, name = match['path'], match['name']
        if repo.lines(path) is None:
            report.fail(f'{where}: file {path} does not exist')
            continue
        decl = repo.find(path, name)
        if decl is None:
            report.fail(f'{where}: `{name}` is not declared in {path}')
            continue
        found.append(decl)
    decls[row.id] = found
    ref = fields(row.reference)

    if row.check == 'formal':
        check_formal(where, found, repo, report)
    elif row.check == 'formal-conditional':
        check_conditional(where, found, ref.get('premises', []), repo, report)
        for premise in ref.get('premises', []):
            if not re.search(rf"(?<![\w']){re.escape(premise)}(?![\w'])",
                             row.claim):
                report.fail(f'{where}: claim text does not name premise '
                            f'`{premise}`; write "Under `{premise}`: ..."')
    elif row.check == 'external-formal':
        check_external(where, ref, repo, report)
    elif row.check == 'source':
        check_source(where, row, ref, repo, report)
    elif row.check == 'script':
        check_script_static(where, row, repo, report)
    if row.status == 'to-formalize':
        for decl in found:
            if repo.certified(decl.path, decl.name):
                report.fail(f'{where}: `{decl.name}` is already certified in '
                            f'{PROOF_STATUS}; promote the row to formal')


def provers(where: str, found: list[Decl], report: Report) -> None:
    if not any(d.path.endswith('.lean') for d in found):
        report.fail(f'{where}: no Lean `path::Name` in the reference')
    if not any(d.path.endswith('.v') for d in found):
        report.fail(f'{where}: no Rocq `path::Name` in the reference')


def check_formal(where: str, found: list[Decl], repo: Repo,
                 report: Report) -> None:
    provers(where, found, report)
    for decl in found:
        if not repo.certified(decl.path, decl.name):
            report.fail(f'{where}: `{decl.name}` ({decl.path}) is not in '
                        f'{PROOF_STATUS}; use status to-formalize or check '
                        f'formal-conditional')
        for hyp in sorted(repo.hypotheses()):
            if binds(decl.signature, hyp):
                report.fail(f'{where}: `{decl.name}` takes the registered '
                            f'hypothesis `{hyp}` as an argument; use check '
                            f'formal-conditional')


def check_conditional(where: str, found: list[Decl], premises: list[str],
                      repo: Repo, report: Report) -> None:
    provers(where, found, report)
    if not premises:
        report.fail(f'{where}: formal-conditional row has no `premises:`')
    for premise in premises:
        if premise not in repo.hypotheses():
            report.fail(f'{where}: premise `{premise}` is not a row of '
                        f'{HYPOTHESES}')
        for decl in found:
            if not re.search(rf"(?<![\w']){re.escape(premise)}(?![\w'])",
                             decl.signature):
                report.fail(f'{where}: premise `{premise}` does not occur in '
                            f'the signature of `{decl.name}` ({decl.path})')
    for decl in found:
        if decl.path.endswith('.lean') and not decl.path.startswith('proofs/'):
            report.fail(f'{where}: {decl.path} is outside proofs/ and is not '
                        f'built by lake build')
        if decl.path.endswith('.v') and decl.path not in repo.coq_project():
            report.fail(f'{where}: {decl.path} is not listed in {COQ_PROJECT}')


def check_external(where: str, ref: dict[str, list[str]], repo: Repo,
                   report: Report) -> None:
    ids = ref.get('registry', [])
    upstream = ref.get('upstream', [])
    if not ids:
        report.fail(f'{where}: external-formal row has no `registry:` id')
    if not upstream:
        report.fail(f'{where}: external-formal row has no `upstream:` name')
    entries = []
    for ident in ids:
        entry = repo.registry().get(ident)
        if entry is None:
            report.fail(f'{where}: registry id {ident!r} is not in {REGISTRY}')
        else:
            entries.append(entry)
    for name in upstream:
        declared = [str((e.get('formal') or {}).get('declaration', ''))
                    for e in entries]
        if entries and not any(name in d for d in declared):
            report.fail(f'{where}: upstream name {name!r} is not in the '
                        f'formal.declaration of {", ".join(ids)}')


def check_source(where: str, row: Row, ref: dict[str, list[str]], repo: Repo,
                 report: Report) -> None:
    ids = ref.get('registry', [])
    if not ids:
        report.fail(f'{where}: source row has no `registry:` id')
    statuses = []
    for ident in ids:
        entry = repo.registry().get(ident)
        if entry is None:
            report.fail(f'{where}: registry id {ident!r} is not in {REGISTRY}')
        else:
            statuses.append(entry.get('status'))
    if row.status == 'cited' and statuses and not any(
            s in CITABLE for s in statuses):
        report.fail(f'{where}: status cited needs a registry entry with status '
                    f'{" or ".join(CITABLE)}; found {", ".join(map(str, statuses))}')


@dataclass
class Script:
    command: str
    expect: int
    pattern: str | None


def parse_script(row: Row) -> Script | None:
    command = COMMAND.search(row.reference)
    expect = EXPECT.search(row.reference)
    if not command or not expect:
        return None
    rest = row.reference[command.end():]
    pattern = MATCH.search(rest)
    return Script(command[1], int(expect[1]), pattern[1] if pattern else None)


def script_file(command: str) -> str | None:
    tokens = shlex.split(command)
    for token in tokens:
        if token in INTERPRETERS or token.startswith('-'):
            continue
        return token
    return None


def check_script_static(where: str, row: Row, repo: Repo,
                        report: Report) -> None:
    script = parse_script(row)
    if script is None:
        report.fail(f'{where}: script row needs a backticked command and '
                    f'expect=N')
        return
    target = script_file(script.command)
    if target is None or not target.startswith(SCRIPT_DIRS):
        report.fail(f'{where}: the command must run a file under '
                    f'{" or ".join(SCRIPT_DIRS)}; found {target!r}')
    elif not (repo.root / target).is_file():
        report.fail(f'{where}: script {target} does not exist')
    if not re.search(rf'(?<![\d.]){script.expect}(?![\d])', row.claim):
        report.fail(f'{where}: the claim text does not contain the expected '
                    f'value {script.expect}')
    if script.pattern is not None:
        try:
            if re.compile(script.pattern).groups < 1:
                report.fail(f'{where}: match= needs one capturing group')
        except re.error as error:
            report.fail(f'{where}: bad match= regex: {error}')


def run_script(where: str, row: Row, root: Path, report: Report,
               cache: dict[str, tuple[int, str]], timeout: int) -> None:
    script = parse_script(row)
    if script is None:
        return
    if script.command not in cache:
        argv = [sys.executable if t in ('python3', 'python') else t
                for t in shlex.split(script.command)]
        try:
            done = subprocess.run(argv, cwd=root, capture_output=True,
                                  text=True, timeout=timeout)
            cache[script.command] = (done.returncode,
                                     done.stdout + done.stderr)
        except (OSError, subprocess.TimeoutExpired) as error:
            cache[script.command] = (-1, str(error))
    code, output = cache[script.command]
    if code != 0:
        tail = output.strip().splitlines()[-1:] or ['']
        report.fail(f'{where}: `{script.command}` exited with {code}: {tail[0]}')
        return
    if script.pattern is not None:
        match = re.search(script.pattern, output)
        if not match:
            report.fail(f'{where}: output of `{script.command}` does not match '
                        f'{script.pattern}')
            return
        value = match[1]
    else:
        value = output.strip()
    if not value.isdigit():
        report.fail(f'{where}: output of `{script.command}` is not an integer: '
                    f'{value[:60]!r}')
    elif int(value) != script.expect:
        report.fail(f'{where}: `{script.command}` gives {value}, the ledger '
                    f'expects {script.expect}')


# --------------------------------------------------------------------------
# Sections


def check_queue(lines: list[str], rows: list[Row], report: Report) -> list[str]:
    body = section(lines, 'Formalization queue')
    if not body:
        report.fail(f'{LEDGER}: no "## Formalization queue" section')
        return []
    entries: list[tuple[int, str, list[str]]] = []
    for number, text in body:
        head = QUEUE_HEAD.match(text)
        if head:
            entries.append((number, head[1], []))
        elif entries:
            entries[-1][2].append(text)
    wanted = {r.id for r in rows if r.status == 'to-formalize'}
    seen: dict[str, int] = {}
    for number, ident, text in entries:
        where = f'{LEDGER}:{number}: queue entry {ident}'
        if ident in seen:
            report.fail(f'{where}: duplicate (first at line {seen[ident]})')
        seen.setdefault(ident, number)
        if ident not in wanted:
            report.fail(f'{where}: not a to-formalize row of the ledger')
        joined = '\n'.join(text)
        for name in QUEUE_FIELDS:
            value = re.search(rf'^-\s+{name}:\s*(.+)$', joined, re.MULTILINE)
            if not value:
                report.fail(f'{where}: missing "- {name}:"')
            elif name == 'Size' and value[1].split()[0].strip('.,;') not in SIZES:
                report.fail(f'{where}: size must start with one of '
                            f'{", ".join(SIZES)}')
            elif name == 'Result class' and not value[1].strip().rstrip(
                    '.').startswith(RESULT_CLASSES):
                report.fail(f'{where}: unknown result class {value[1]!r}')
    for ident in sorted(wanted - set(seen)):
        report.fail(f'{LEDGER}: to-formalize row {ident} has no queue entry')
    return [ident for _, ident, _ in entries]


def check_cannot(lines: list[str], rows: list[Row], report: Report) -> list[str]:
    body = section(lines, 'Claims that cannot be formalized')
    if not body:
        report.fail(f'{LEDGER}: no "## Claims that cannot be formalized" '
                    f'section')
        return []
    by_id = {r.id: r for r in rows}
    out = []
    for number, text in body:
        item = CANNOT_ITEM.match(text)
        if not item:
            continue
        ident = item[1]
        out.append(ident)
        row = by_id.get(ident)
        if row is None:
            report.fail(f'{LEDGER}:{number}: {ident} is not a ledger row')
        elif row.check not in ('source', 'unverified', 'external-formal'):
            report.fail(f'{LEDGER}:{number}: {ident} has check {row.check}; '
                        f'only source, unverified or external-formal rows '
                        f'belong in this list')
    return out


# --------------------------------------------------------------------------
# Counters for script rows


def count_lines(repo: Repo, path: str, pattern: str,
                after: str | None = None) -> int:
    lines = repo.lines(path) or []
    if after is not None:
        starts = [i for i, t in enumerate(lines) if t.startswith(after)]
        lines = lines[starts[0] + 1:] if starts else []
    regex = re.compile(pattern)
    return sum(1 for t in lines if regex.search(t))


def coverage(repo: Repo, level: str) -> int:
    lines = repo.lines('proofs/attempts/COMMON_ERRORS.md') or []
    starts = [i for i, t in enumerate(lines)
              if t.startswith('## Attempt Coverage Index')]
    total = 0
    for text in lines[starts[0] + 1:] if starts else []:
        if text.startswith('## '):
            break
        row = cells(text)
        if row and row[0].startswith('[') and row[-1] == level:
            total += 1
    return total


def verdicts(repo: Repo, prefix: str) -> int:
    folder = repo.root / 'proofs/experiments/issue532/ideas'
    total = 0
    for path in sorted(folder.glob('Idea[0-9][0-9].md')):
        for text in path.read_text(encoding='utf-8').splitlines():
            if text.startswith(f'**Verdict:** {prefix}'):
                total += 1
    return total


def manifest_signatures(repo: Repo) -> list[str]:
    out = []
    for prover in ('lean', 'rocq'):
        for entry in repo.proof_status().get(prover, []):
            decl = repo.find(entry.get('source', ''), entry.get('theorem', ''))
            if decl is not None:
                out.append(decl.signature)
    return out


SAT_VERIFIER = 'proofs/experiments/issue532/{0}/SATVerifier.{1}'


def definition_text(repo: Repo, path: str, keyword: str, name: str) -> str:
    lines = repo.lines(path) or []
    out: list[str] = []
    for text in lines:
        if out:
            if not text.strip():
                break
            out.append(text)
        elif re.match(rf'^{keyword}\s+{name}\b', text):
            out.append(text)
    return '\n'.join(out)


def list_literal_length(text: str, sep: str) -> int | None:
    """Count the top-level elements of the first list literal in text."""
    start = text.find('[')
    if start < 0:
        return None
    depth, count = 0, 1
    for ch in text[start + 1:]:
        if ch in '([':
            depth += 1
        elif ch in ')]':
            if depth == 0:
                return count
            depth -= 1
        elif ch == sep and depth == 0:
            count += 1
    return None


def sat_verifier_states(repo: Repo) -> int:
    """Length of `allStates` in SATVerifier, in Lean and in Rocq.

    The definition is an explicit list followed by maps over the lists
    `triples` and `pairs2`. Returns -1 if a file cannot be parsed or the two
    provers disagree.
    """
    counts = []
    for prover, ext, keyword, sep in (('lean', 'lean', 'def', ','),
                                       ('rocq', 'v', 'Definition', ';')):
        path = SAT_VERIFIER.format(prover, ext)
        body = definition_text(repo, path, keyword, 'allStates')
        head = list_literal_length(body, sep)
        if head is None:
            return -1
        total = head
        for helper in ('triples', 'pairs2'):
            size = list_literal_length(
                definition_text(repo, path, keyword, helper), sep)
            uses = len(re.findall(rf'\b{helper}\b', body))
            if uses and size is None:
                return -1
            total += uses * (size or 0)
        counts.append(total)
    return counts[0] if len(set(counts)) == 1 else -1


TARGET = re.compile(
    r"^(?:theorem|lemma|Theorem|Lemma|Corollary)\s+[\w'.]+\s*:\s*"
    r"(?:Complexity\.)?P(?:Not)?EqualsNP\s*\.?\s*$")


def counter(repo: Repo, name: str) -> int | None:
    status = repo.proof_status()
    simple = {
        'certified-lean': lambda: len(status.get('lean', [])),
        'certified-rocq': lambda: len(status.get('rocq', [])),
        'hypotheses-rows': lambda: sum(
            1 for t in repo.lines(HYPOTHESES) or []
            if HYP_ROW.match(t) and not t.startswith('| `name`')),
        'attempt-folders': lambda: sum(
            1 for p in (repo.root / 'proofs/attempts').iterdir() if p.is_dir()),
        'attempts-p-eq-np': lambda: count_lines(
            repo, 'proofs/attempts/ATTEMPTS.md', r'^\| ✓ \|'),
        'attempts-p-neq-np': lambda: count_lines(
            repo, 'proofs/attempts/ATTEMPTS.md', r'^\| ✗ \|'),
        'attempts-other': lambda: count_lines(
            repo, 'proofs/attempts/ATTEMPTS.md', r'^\| \? \|'),
        'strategies': lambda: count_lines(
            repo, 'SOLUTION_STRATEGIES.md', r'^### Strategy \d+\.\d+:'),
        'error-families': lambda: count_lines(
            repo, 'proofs/attempts/COMMON_ERRORS.md', r'^### \d+\. ',
            after='## '),
        'coverage-concrete-refutation': lambda: coverage(
            repo, 'Concrete refutation'),
        'coverage-conditional-result': lambda: coverage(
            repo, 'Conditional result'),
        'coverage-identified-gap': lambda: coverage(repo, 'Identified gap'),
        'coverage-informal': lambda: coverage(
            repo, 'Informal/unverified analysis'),
        'verdict-refuted-route': lambda: verdicts(repo, 'Refuted as a route'),
        'verdict-refuted-full': lambda: verdicts(
            repo, 'Refuted in full strength'),
        'verdict-open-obligation': lambda: verdicts(
            repo, 'Developed to an open obligation'),
        'verdict-insufficient': lambda: verdicts(
            repo, 'Correct tool, insufficient alone'),
        'unconditional-target-theorems': lambda: sum(
            1 for s in manifest_signatures(repo) if TARGET.match(s)),
        'sat-verifier-states': lambda: sat_verifier_states(repo),
        'manifest-eth-premises': lambda: sum(
            1 for s in manifest_signatures(repo)
            if re.search(r"(?<![\w'])S?ETH(?![\w'])", s)),
    }
    if name in simple:
        return simple[name]()
    if name.startswith('registry-status:'):
        wanted = name.split(':', 1)[1]
        return sum(1 for e in repo.registry().values()
                   if e.get('status') == wanted)
    return None


COUNTERS = (
    'certified-lean', 'certified-rocq', 'hypotheses-rows', 'attempt-folders', 'attempts-p-eq-np',
    'attempts-p-neq-np', 'attempts-other', 'strategies', 'error-families',
    'coverage-concrete-refutation', 'coverage-conditional-result',
    'coverage-identified-gap', 'coverage-informal', 'verdict-refuted-route',
    'verdict-refuted-full', 'verdict-open-obligation', 'verdict-insufficient',
    'unconditional-target-theorems', 'manifest-eth-premises',
    'sat-verifier-states', 'registry-status:<status>',
)


# --------------------------------------------------------------------------
# Main


def check(root: Path, run_scripts: bool = False, timeout: int = 600
          ) -> tuple[Report, list[Row], dict[str, list[Decl]], list[str],
                     list[str]]:
    report = Report()
    repo = Repo(root)
    lines = repo.lines(LEDGER)
    if lines is None:
        report.fail(f'{LEDGER} does not exist under {root}')
        return report, [], {}, [], []
    rows = parse_ledger(lines, report)
    seen: dict[str, int] = {}
    decls: dict[str, list[Decl]] = {}
    for row in rows:
        if row.id in seen:
            report.fail(f'{LEDGER}:{row.line}: duplicate id {row.id} (first at '
                        f'line {seen[row.id]})')
        seen.setdefault(row.id, row.line)
        check_row(row, repo, report, decls)
    queue = check_queue(lines, rows, report)
    cannot = check_cannot(lines, rows, report)
    if run_scripts:
        cache: dict[str, tuple[int, str]] = {}
        for row in rows:
            if row.check == 'script':
                run_script(f'{LEDGER}:{row.line}: {row.id}', row, root, report,
                           cache, timeout)
    scripts = sum(1 for r in rows if r.check == 'script')
    report.notes.append(
        f'{LEDGER}: {len(rows)} claims, {len(queue)} queue entries, '
        f'{len(cannot)} not formalizable; '
        + (f'{scripts} script rows run' if run_scripts
           else f'{scripts} script rows not run (use --run-scripts)'))
    return report, rows, decls, queue, cannot


def stats(rows: list[Row], decls: dict[str, list[Decl]], queue: list[str],
          cannot: list[str], root: Path) -> list[str]:
    repo = Repo(root)
    out = [f'claims: {len(rows)}']
    out.append('by status: ' + ', '.join(
        f'{s} {sum(1 for r in rows if r.status == s)}' for s in STATUSES))
    out.append('by check: ' + ', '.join(
        f'{c} {sum(1 for r in rows if r.check == c)}' for c in ALLOWED))
    certified, compiled = [], []
    for row in rows:
        if row.check != 'formal-conditional':
            continue
        found = decls.get(row.id, [])
        if found and all(repo.certified(d.path, d.name) for d in found):
            certified.append(row.id)
        else:
            compiled.append(row.id)
    out.append(f'formal-conditional, certified ({len(certified)}): '
               + ', '.join(certified))
    out.append(f'formal-conditional, compiled only ({len(compiled)}): '
               + ', '.join(compiled))
    out.append(f'formalization queue ({len(queue)}): ' + ', '.join(queue))
    out.append(f'cannot be formalized ({len(cannot)}): ' + ', '.join(cannot))
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--run-scripts', action='store_true',
                        help='run the commands of script rows')
    parser.add_argument('--stats', action='store_true',
                        help='print counts by status and check type')
    parser.add_argument('--count', metavar='NAME',
                        help='print one count: ' + ', '.join(COUNTERS))
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args(argv)
    root = args.root.resolve()

    if args.count:
        value = counter(Repo(root), args.count)
        if value is None:
            print(f'unknown counter {args.count!r}; known: '
                  + ', '.join(COUNTERS), file=sys.stderr)
            return 1
        print(value)
        return 0

    report, rows, decls, queue, cannot = check(root, args.run_scripts,
                                               args.timeout)
    for note in report.notes:
        print(note)
    if args.stats:
        for line in stats(rows, decls, queue, cannot, root):
            print(line)
    for error in report.errors:
        print(f'FAIL {error}', file=sys.stderr)
    if report.errors:
        print(f'check_claims: FAILED ({len(report.errors)} error(s))',
              file=sys.stderr)
        return 1
    print('check_claims: OK')
    return 0


if __name__ == '__main__':
    sys.exit(main())
