#!/usr/bin/env python3
"""Check FORMAL_STATEMENT.md and proofs/HYPOTHESES.md against the sources.

The checks read source text only. Nothing is built, so a binder is found by
its text in a signature, not by elaboration.

1. Claims. Every ``path::Name`` line of the ``claims`` block in
   FORMAL_STATEMENT.md names a file that exists and declares ``Name``.
2. Locations. Every location written as `Name` (`path:line`), or as a table
   cell `Name` followed by a cell `path:line`, declares ``Name`` on that
   line. A declaration up to three lines away is a warning; anything else
   fails.
3. Summary box. In a fenced block preceded by ``<!-- verbatim-from: path -->``
   the code lines occur in that file in the same order (they need not be
   contiguous). A comment line ``-- [path]:N`` or ``-- [path]:N-M`` starts a
   segment: the first code line of the segment is line N and the last is
   line M (N if no M). Segments with line numbers must come in increasing
   line order.
4. Hypotheses table (proofs/HYPOTHESES.md):
   a. fixed columns, classes and status values;
   b. the lean and rocq cells point at a declaration of the name (or both
      say "not defined", for a known theorem that has no definition yet;
      then no Prop definition of that name may exist under proofs/), and that
      declaration is a Prop definition (``def … : Prop``, ``abbrev``,
      ``structure``, ``class``, ``inductive``; ``Definition``, ``Record``,
      ``Class``, ``Inductive`` … ``: Prop`` in Rocq);
   c. if the statement cell starts with a code span, every identifier of that
      span occurs in the Lean definition (the name itself is allowed);
   d. the class agrees with the marker comment of the Lean definition: a
      definition marked "Open obligation" has class ``obligation``, one
      marked only "Known theorem"/"not mechanised" does not;
   e. dependents: every listed theorem is a Lean theorem under proofs/
      (outside proofs/attempts/) whose signature takes the hypothesis as a
      premise; a list without "…" is complete; a list with "…" ends in
      "(N total)" and N is the number of such theorems; a cell that starts
      with "none" means there are none;
   f. a row with status "discharged on main" whose name is still a premise
      of some Lean or Rocq theorem is a warning if its dependents cell lists
      them and a bullet of the Known defects section that says
      "discharged" names it, and a failure otherwise.
5. Markers. Every Prop definition under proofs/ (``.lean``, ``.v``,
   ``.agda``) whose own comment (the comment just above it, with only blank
   lines and attributes between) says "Known theorem", "not mechanised" /
   "not mechanized" or "Open obligation" has a row (an Agda definition needs
   a row of the same name). The names in the "Missing markers" bullet of the
   Known defects section are exactly the rows whose Lean definition has no
   marker, and each has a row.
6. Result graph. The table of FORMAL_STATEMENT.md with columns
   ``edge (from → to) | theorem | file:line | premise | certified | status``:
   the hypotheses (rows of HYPOTHESES.md) that occur as premises of the
   theorem's signature are exactly the names of the premise cell, apart
   from names that occur in the edge cell; ``certified`` is ``yes`` exactly
   when scripts/proof_status.json lists the theorem for that source file.
7. Certified wording. In the prose of both documents, a sentence that
   locates a theorem (`name` (`path:line`), with a theorem or lemma
   declared there) and calls it "certified", or "proved"/"proves" without
   saying "not certified", fails unless scripts/proof_status.json lists it.

``--write-lines`` rewrites the line numbers of checks 2, 3 and 4b to the
nearest current declaration before checking. ``--strict`` turns every warning
into a failure. Standard library only.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATEMENT = 'FORMAL_STATEMENT.md'
HYPOTHESES = 'proofs/HYPOTHESES.md'
PROOF_STATUS = 'scripts/proof_status.json'
EXCLUDED = ('proofs/attempts/',)

COLUMNS = [
    'name', 'class', 'lean (file:line)', 'rocq (file:line)',
    'statement (one line)', 'reference', 'dependents', 'status',
]
GRAPH_COLUMNS = ['edge (from → to)', 'theorem', 'file:line', 'premise',
                 'certified', 'status']
NOT_DEFINED = 'not defined'
CLASSES = ('bridge', 'P-membership', 'simulation', 'deep', 'obligation')
STATUS = re.compile(
    r'^(open|in progress \(PR #\d+, unmerged\)'
    r'|discharged in PR #\d+ \(unmerged\)|discharged on main)$'
)
KEYWORDS = (
    'theorem|def|lemma|abbrev|structure|inductive|class|opaque|'
    'Theorem|Definition|Lemma|Inductive|CoInductive|Record|Structure|Class|'
    'Variant|Fixpoint|CoFixpoint|Corollary|Proposition|Fact|Remark'
)
AGDA_KEYWORDS = 'data|record|postulate'
THEOREM_KEYWORDS = ('theorem', 'lemma', 'Theorem', 'Lemma', 'Corollary',
                    'Proposition', 'Fact', 'Remark')
KNOWN_MARKER = re.compile(r'Known theorem|[Nn]ot mechani[sz]ed')
OBLIGATION_MARKER = re.compile(r'Open obligation')
SOURCE_SUFFIXES = ('.lean', '.v', '.agda')

NAME = r"[A-Za-z_][\w'.]*"
LOCATION = r"[\w./-]+\.(?:lean|v|agda)"
INLINE_REF = re.compile(rf'`(?P<name>{NAME})`\s+\(`(?P<path>{LOCATION}):(?P<line>\d+)`[);,]')
NAME_CELL = re.compile(rf'^`({NAME})`$')
LOCATION_CELL = re.compile(rf'^`({LOCATION}):(\d+)`$')
CLAIM = re.compile(rf'^(?P<path>{LOCATION})::(?P<name>{NAME})$')
PATH_BASE = re.compile(r'<!--\s*path-base:\s*(\S+)\s*-->')
VERBATIM = re.compile(r'<!--\s*verbatim-from:\s*(\S+)\s*-->')
RANGE_COMMENT = re.compile(r'^--\s*(?:\S*?)?:(\d+)(?:-(\d+))?\b')
IDENT = re.compile(r"[A-Za-z_][\w']*")
CODE_SPAN = re.compile(r'`([^`]+)`')

LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?P<kw>def|abbrev|structure|class|inductive|opaque)\s+(?:inductive\s+)?"
    r"(?P<name>[A-Za-z_][\w'.]*)")
ROCQ_DECL = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Polymorphic|Program)\s+)*"
    r"(?P<kw>Definition|Record|Structure|Class|Inductive|CoInductive|Variant)\s+"
    r"(?P<name>[A-Za-z_][\w'.]*)")
AGDA_DECL = re.compile(
    r"^\s*(?:(?P<kw>data|record)\s+)?(?P<name>[^\s:;(){}@\"\-][^\s:;(){}@\"]*)"
    r"\s*:(?![=:])(?P<rest>.*)$")
LEAN_THEOREM = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+(?P<name>[^\s(:{\[⦃]+)")
ROCQ_THEOREM = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global)\s+)*"
    r"(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark)\s+(?P<name>[^\s(:{]+)")


@dataclass
class Report:
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    def fail(self, message: str) -> None:
        self.errors.append(message)

    def warn(self, message: str) -> None:
        self.warnings.append(message)


def mask_comments(text: str, suffix: str) -> str:
    """Replace comment text by spaces, keeping newlines and nesting."""
    if suffix == '.v':
        opener, closer, line_comment = '(*', '*)', None
    elif suffix == '.agda':
        opener, closer, line_comment = '{-', '-}', '--'
    else:
        opener, closer, line_comment = '/-', '-/', '--'
    out = []
    depth = 0
    k = 0
    while k < len(text):
        if text.startswith(opener, k):
            depth += 1
            out.append('  ')
            k += 2
            continue
        if depth and text.startswith(closer, k):
            depth -= 1
            out.append('  ')
            k += 2
            continue
        if not depth and line_comment and text.startswith(line_comment, k):
            end = text.find('\n', k)
            end = len(text) if end < 0 else end
            out.append(' ' * (end - k))
            k = end
            continue
        char = text[k]
        out.append(char if (not depth or char == '\n') else ' ')
        k += 1
    return ''.join(out)


class Sources:
    """Cached source files under one root."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._lines: dict[Path, list[str] | None] = {}
        self._all: list[Path] | None = None
        self._code: dict[Path, list[str] | None] = {}

    def lines(self, path: Path) -> list[str] | None:
        if path not in self._lines:
            full = self.root / path
            self._lines[path] = (full.read_text(encoding='utf-8').splitlines()
                                 if full.is_file() else None)
        return self._lines[path]

    def code(self, path: Path) -> list[str] | None:
        """The lines of ``path`` with comments blanked out (line count kept)."""
        if path not in self._code:
            lines = self.lines(path)
            self._code[path] = (None if lines is None else
                                mask_comments('\n'.join(lines), path.suffix).split('\n'))
        return self._code[path]

    def all_sources(self) -> list[Path]:
        """Source files under proofs/, outside the excluded directories."""
        if self._all is None:
            proofs = self.root / 'proofs'
            found = []
            if proofs.is_dir():
                for path in sorted(proofs.rglob('*')):
                    if path.suffix not in SOURCE_SUFFIXES or not path.is_file():
                        continue
                    relative = path.relative_to(self.root)
                    if relative.as_posix().startswith(EXCLUDED):
                        continue
                    found.append(relative)
            self._all = found
        return self._all


# ---------------------------------------------------------------- declarations

def declaration_pattern(name: str, path: Path) -> re.Pattern[str]:
    """A declaration of ``name``; Agda files also use the ``name :`` form."""
    escaped = re.escape(name)
    lean_rocq = rf"\b(?:{KEYWORDS})\s+{escaped}(?![\w'.])"
    if path.suffix == '.agda':
        return re.compile(rf"(?:{lean_rocq})|\b(?:{AGDA_KEYWORDS})\s+{escaped}(?![\w'.])"
                          rf"|^\s*{escaped}\s*:(?![=:])")
    return re.compile(lean_rocq)


def declaration_lines(lines: list[str], name: str, path: Path) -> list[int]:
    """1-based lines declaring ``name`` or, for a dotted name, its last part."""
    candidates = [name]
    if '.' in name:
        candidates.append(name.rsplit('.', 1)[1])
    for candidate in candidates:
        pattern = declaration_pattern(candidate, path)
        found = [i + 1 for i, text in enumerate(lines) if pattern.search(text)]
        if found:
            return found
    return []


def declaration_keyword(line: str) -> str | None:
    match = re.search(rf"\b({KEYWORDS}|{AGDA_KEYWORDS})\s", line)
    return match[1] if match else None


def prop_declaration(lines: list[str], i: int, path: Path) -> str | None:
    """The name declared on line ``i`` (0-based) if it is a Prop definition."""
    line = lines[i]
    if path.suffix == '.lean':
        match = LEAN_DECL.match(line)
    elif path.suffix == '.v':
        match = ROCQ_DECL.match(line)
    else:
        match = AGDA_DECL.match(line)
        if not match or match['name'] in ('module', 'open', 'import', 'where'):
            return None
        rest = re.sub(r'\bwhere\s*$', '', match['rest']).strip()
        return match['name'] if re.search(r'(?:Set|Prop|Set₀)$', rest) else None
    if not match:
        return None
    signature = line
    j = i
    while (':=' not in signature and not re.search(r'\bwhere\b', signature)
           and j + 1 < len(lines) and j < i + 8):
        nxt = lines[j + 1]
        if nxt.lstrip().startswith('|'):
            break
        j += 1
        signature += ' ' + nxt
    head = re.split(r':=|\bwhere\b', signature, maxsplit=1)[0].strip().rstrip('.').strip()
    return match['name'] if head.endswith('Prop') else None


def prop_lines(lines: list[str], name: str, path: Path) -> list[int]:
    """1-based lines that declare ``name`` (or its last part) as a Prop."""
    short = name.rsplit('.', 1)[-1]
    out = []
    for i in range(len(lines)):
        declared = prop_declaration(lines, i, path)
        if declared is not None and declared.rsplit('.', 1)[-1] == short:
            out.append(i + 1)
    return out


COMMENT_PAIRS = {'.lean': (('/-', '-/'),), '.v': (('(*', '*)'),), '.agda': (('{-', '-}'),)}


def preceding_comment(lines: list[str], i: int, suffix: str = '.lean') -> str | None:
    """The comment just above line ``i``.

    Blank lines and attributes may separate the comment from the
    declaration, however many there are. Any other line ends the search, so
    a comment inside an earlier definition is not used.
    """
    k = i - 1
    while k >= 0:
        text = lines[k].strip()
        if (not text or text.startswith(('@[', '#[', 'attribute [', '{-#'))):
            k -= 1
            continue
        if suffix in ('.lean', '.agda') and text.startswith('--'):
            start = k
            while start - 1 >= 0 and lines[start - 1].strip().startswith('--'):
                start -= 1
            return ' '.join(lines[start:k + 1])
        for opener, closer in COMMENT_PAIRS.get(suffix, ()):
            if text.endswith(closer):
                start = k
                while start >= 0 and opener not in lines[start]:
                    start -= 1
                if start < 0:
                    return None
                return ' '.join(lines[start:k + 1])
        return None
    return None


def marker_kinds(comment: str | None) -> set[str]:
    kinds = set()
    if comment:
        if KNOWN_MARKER.search(comment):
            kinds.add('known')
        if OBLIGATION_MARKER.search(comment):
            kinds.add('obligation')
    return kinds


@dataclass
class Marked:
    path: Path
    line: int
    name: str
    kinds: set[str]


def marked_hypotheses(sources: Sources) -> list[Marked]:
    """Prop definitions under proofs/ whose own comment carries a marker."""
    out = []
    for path in sources.all_sources():
        lines = sources.lines(path) or []
        code = sources.code(path) or []
        for i in range(len(code)):
            name = prop_declaration(code, i, path)
            if name is None:
                continue
            kinds = marker_kinds(preceding_comment(lines, i, path.suffix))
            if kinds:
                out.append(Marked(path, i + 1, name, kinds))
    return out


# ------------------------------------------------------------------ signatures

def strip_comments(text: str, suffix: str) -> str:
    if suffix == '.v':
        return re.sub(r'\(\*.*?\*\)', ' ', text, flags=re.DOTALL)
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.DOTALL)
    return re.sub(r'--[^\n]*', ' ', text)


OPEN = '([{⦃'
CLOSE = ')]}⦄'


STOPS = re.compile(r'∃|\bexists\b|\bfun\b|λ')


def split_top(text: str, separators: tuple[str, ...],
              stops: re.Pattern[str] | None = None) -> list[str]:
    """Split ``text`` at separators that are outside every bracket.

    Splitting ends at a top-level match of ``stops`` (a binder such as
    ``∃`` whose body extends to the end).
    """
    parts, depth, start, k = [], 0, 0, 0
    while k < len(text):
        char = text[k]
        if depth == 0 and stops is not None and stops.match(text, k):
            break
        if char in OPEN:
            depth += 1
        elif char in CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0:
            for separator in separators:
                if text.startswith(separator, k):
                    parts.append(text[start:k])
                    k += len(separator)
                    start = k
                    break
            else:
                k += 1
                continue
            continue
        k += 1
    parts.append(text[start:])
    return parts


def premise_text(signature: str) -> str:
    """The binders and the premises of the type of a theorem signature.

    ``signature`` starts after the theorem name and ends before ``:=`` (Lean)
    or the final period (Rocq). Bracketed binders before the top-level colon,
    ``∀``/``forall`` binders and every arrow premise of the type are
    premises; the final conclusion is not.
    """
    premises = []
    k = 0
    text = signature
    while k < len(text):
        char = text[k]
        if char.isspace():
            k += 1
            continue
        if char in OPEN:
            depth, j = 0, k
            while j < len(text):
                if text[j] in OPEN:
                    depth += 1
                elif text[j] in CLOSE:
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            premises.append(text[k:j + 1])
            k = j + 1
            continue
        break
    rest = text[k:]
    colon = split_top(rest, (':',))
    kind = ':'.join(colon[1:]) if len(colon) > 1 else rest
    while True:
        kind = kind.strip()
        quantifier = re.match(r'^(?:∀|forall)\s*', kind)
        if quantifier:
            parts = split_top(kind[quantifier.end():], (',',))
            if len(parts) > 1:
                premises.append(parts[0])
                kind = ','.join(parts[1:])
                continue
        if len(split_top(kind, ('↔', '<->'), STOPS)) > 1:
            return ' '.join(premises)
        parts = split_top(kind, ('→', '->'), STOPS)
        if len(parts) > 1:
            premises.extend(parts[:-1])
            kind = parts[-1]
            continue
        return ' '.join(premises)


@dataclass
class Theorem:
    path: Path
    line: int
    name: str
    premises: str


def theorem_signature(lines: list[str], i: int, path: Path) -> tuple[str, str] | None:
    """(name, text after the name up to ``:=`` or the final period)."""
    pattern = LEAN_THEOREM if path.suffix == '.lean' else ROCQ_THEOREM
    match = pattern.match(lines[i])
    if not match:
        return None
    text = lines[i][match.end():]
    j = i
    while j + 1 < len(lines) and j < i + 40:
        cleaned = strip_comments(text, path.suffix)
        if path.suffix == '.lean' and ':=' in cleaned:
            break
        if path.suffix == '.v' and re.search(r'\.(?=\s|$)', cleaned):
            break
        nxt = lines[j + 1]
        if path.suffix == '.lean' and nxt.lstrip().startswith(('|', 'where')):
            break
        j += 1
        text += '\n' + nxt
    text = strip_comments(text, path.suffix)
    if path.suffix == '.lean':
        text = text.split(':=', 1)[0]
    else:
        text = re.split(r'\.(?=\s|$)', text, maxsplit=1)[0]
    return match['name'], text


def theorems(sources: Sources, suffixes: tuple[str, ...]) -> list[Theorem]:
    out = []
    for path in sources.all_sources():
        if path.suffix not in suffixes:
            continue
        lines = sources.code(path) or []
        for i in range(len(lines)):
            found = theorem_signature(lines, i, path)
            if found:
                out.append(Theorem(path, i + 1, found[0], premise_text(found[1])))
    return out


def occurrences(name: str, text: str) -> list[str]:
    """Qualifiers of every occurrence of identifier ``name`` in ``text``."""
    pattern = re.compile(rf"(?<![\w'.])((?:[A-Za-z_][\w']*\.)*){re.escape(name)}"
                         rf"(?![\w']|\.[A-Za-z_])")
    return [m[1] for m in pattern.finditer(text)]


# ------------------------------------------------------------------- documents

@dataclass
class Ref:
    """A `name` at `path:line` written in a document."""
    doc: str
    doc_line: int
    name: str
    written: str
    resolved: Path
    line: int


def resolve(written: str, base: str | None) -> Path:
    if base is None or written.startswith('proofs/'):
        return Path(written)
    return Path(base) / written


def split_row(text: str) -> list[str] | None:
    stripped = text.strip()
    if not (stripped.startswith('|') and stripped.endswith('|')):
        return None
    return text.split('|')


def nearest_line(found: list[int], line: int) -> int:
    return min(found, key=lambda n: (abs(n - line), n))


def check_ref(ref: Ref, sources: Sources, report: Report) -> int | None:
    """Check one reference. Return the nearest declaration line, if any."""
    lines = sources.lines(ref.resolved)
    where = f'{ref.doc}:{ref.doc_line}'
    if lines is None:
        report.fail(f'{where}: `{ref.name}`: file {ref.resolved} does not exist')
        return None
    found = declaration_lines(lines, ref.name, ref.resolved)
    if not found:
        report.fail(f'{where}: `{ref.name}` is not declared in {ref.resolved}')
        return None
    nearest = nearest_line(found, ref.line)
    if nearest == ref.line:
        return nearest
    message = (f'{where}: `{ref.name}` is declared at {ref.resolved}:{nearest}, '
               f'not at line {ref.line}')
    if abs(nearest - ref.line) <= 3:
        report.warn(message + ' (drift of at most 3 lines)')
    else:
        report.fail(message)
    return nearest


def inline_refs(doc: str, text: str, base: str | None) -> list[tuple[re.Match[str], Ref]]:
    """`Name` (`path:line`), possibly with a line break before the parenthesis."""
    out = []
    for match in INLINE_REF.finditer(text):
        number = text.count('\n', 0, match.start('line')) + 1
        written = match['path']
        out.append((match, Ref(doc, number, match['name'], written,
                               resolve(written, base), int(match['line']))))
    return out


def table_cell_refs(doc: str, text: str, base: str | None) -> list[tuple[int, int, Ref]]:
    """Adjacent table cells `Name` | `path:line`. Returns (line, cell index, ref)."""
    out = []
    for number, line in enumerate(text.splitlines(), 1):
        cells = split_row(line)
        if cells is None:
            continue
        for index in range(len(cells) - 1):
            name = NAME_CELL.match(cells[index].strip())
            location = LOCATION_CELL.match(cells[index + 1].strip())
            if name and location:
                out.append((number, index + 1, Ref(
                    doc, number, name[1], location[1],
                    resolve(location[1], base), int(location[2]))))
    return out


@dataclass
class Row:
    line: int
    cells: list[str]
    name: str
    hclass: str
    statement: str
    dependents: str
    status: str
    refs: list[tuple[int, Ref]]

    def lean_ref(self) -> Ref | None:
        for column, ref in self.refs:
            if column == 3:
                return ref
        return None


def table_after(lines: list[str], header_at: int) -> list[tuple[int, list[str]]]:
    out = []
    for number in range(header_at + 2, len(lines) + 1):
        cells = split_row(lines[number - 1])
        if cells is None:
            break
        out.append((number, [c.strip() for c in cells[1:-1]]))
    return out


def hypotheses_table(text: str, base: str | None, report: Report) -> list[Row]:
    rows: list[Row] = []
    lines = text.splitlines()
    header_at = None
    for number, line in enumerate(lines, 1):
        cells = split_row(line)
        if cells and [c.strip() for c in cells[1:-1]][:2] == ['name', 'class']:
            header_at = number
            header = [c.strip() for c in cells[1:-1]]
            if header != COLUMNS:
                report.fail(f'{HYPOTHESES}:{number}: columns are {header}, expected {COLUMNS}')
            break
    if header_at is None:
        report.fail(f'{HYPOTHESES}: no table with columns {COLUMNS}')
        return rows
    for number, inner in table_after(lines, header_at):
        where = f'{HYPOTHESES}:{number}'
        if len(inner) != len(COLUMNS):
            report.fail(f'{where}: {len(inner)} cells, expected {len(COLUMNS)}')
            continue
        name = re.match(rf'^`({NAME})`', inner[0])
        if not name:
            report.fail(f'{where}: name cell must start with a backticked identifier')
            continue
        if inner[1] not in CLASSES:
            report.fail(f'{where}: class {inner[1]!r} is not one of {", ".join(CLASSES)}')
        if not STATUS.match(inner[7]):
            report.fail(f'{where}: status {inner[7]!r} is not one of: open, '
                        'in progress (PR #N, unmerged), discharged in PR #N (unmerged), '
                        'discharged on main')
        refs = []
        undefined = [inner[c] == NOT_DEFINED for c in (2, 3)]
        if any(undefined) and not all(undefined):
            report.fail(f'{where}: write {NOT_DEFINED!r} in both the lean and rocq cells, '
                        'or give both locations')
        for column in (2, 3):
            if all(undefined):
                break
            location = LOCATION_CELL.match(inner[column])
            if not location:
                report.fail(f'{where}: column {COLUMNS[column]!r} must be `file:line`, '
                            f'found {inner[column]!r}')
                continue
            refs.append((column + 1, Ref(HYPOTHESES, number, name[1], location[1],
                                         resolve(location[1], base), int(location[2]))))
        rows.append(Row(number, inner, name[1], inner[1], inner[4], inner[6], inner[7], refs))
    return rows


def known_defects(text: str) -> list[str]:
    """The bullets of the ``## Known defects`` section, each joined to one line."""
    section = re.search(r'^## Known defects\s*\n(.*?)(?=^## |\Z)', text, re.MULTILINE | re.DOTALL)
    if not section:
        return []
    bullets: list[str] = []
    for line in section[1].splitlines():
        if line.startswith('- '):
            bullets.append(line[2:].strip())
        elif line.startswith('  ') and bullets:
            bullets[-1] += ' ' + line.strip()
    return bullets


# --------------------------------------------------------------- proof status

class ProofStatus:
    def __init__(self, root: Path, report: Report) -> None:
        self.entries: list[tuple[str, str]] = []
        path = root / PROOF_STATUS
        self.present = path.is_file()
        if not self.present:
            return
        try:
            data = json.loads(path.read_text(encoding='utf-8'))
        except json.JSONDecodeError as error:
            report.fail(f'{PROOF_STATUS}: not valid JSON ({error})')
            return
        for language in ('lean', 'rocq'):
            for entry in data.get(language, []):
                if isinstance(entry, dict) and 'theorem' in entry:
                    self.entries.append((str(entry.get('source', '')), str(entry['theorem'])))

    def certified(self, source: Path, name: str) -> bool:
        short = name.rsplit('.', 1)[-1]
        for entry_source, theorem in self.entries:
            if entry_source and entry_source != source.as_posix():
                continue
            if theorem == name or theorem.rsplit('.', 1)[-1] == short:
                return True
        return False


# ---------------------------------------------------------------------- checks

def check_claims(text: str, sources: Sources, report: Report) -> int:
    block = re.search(r'^```claims\s*\n(.*?)^```', text, re.MULTILINE | re.DOTALL)
    if not block:
        report.fail(f'{STATEMENT}: no ```claims block')
        return 0
    first = text.count('\n', 0, block.start(1)) + 1
    count = 0
    for offset, raw in enumerate(block[1].splitlines()):
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        where = f'{STATEMENT}:{first + offset}'
        claim = CLAIM.match(line)
        if not claim:
            report.fail(f'{where}: claim {line!r} is not `path::Name`')
            continue
        count += 1
        path = Path(claim['path'])
        lines = sources.lines(path)
        if lines is None:
            report.fail(f'{where}: file {path} does not exist')
        elif not declaration_lines(lines, claim['name'], path):
            report.fail(f'{where}: {path} does not declare {claim["name"]}')
    if count == 0:
        report.fail(f'{STATEMENT}: the claims block is empty')
    return count


@dataclass
class Segment:
    comment_line: int | None       # 0-based document line of the range comment
    start: int | None              # stated first source line
    end: int | None                # stated last source line
    body: list[tuple[int, str]]    # (0-based document line, stripped text)


def verbatim_blocks(lines: list[str]) -> list[tuple[int, Path, list[Segment]]]:
    out = []
    for number, line in enumerate(lines):
        marker = VERBATIM.search(line)
        if not marker:
            continue
        k = number + 1
        while k < len(lines) and not lines[k].startswith('```'):
            k += 1
        k += 1
        segments = [Segment(None, None, None, [])]
        while k < len(lines) and not lines[k].startswith('```'):
            body = lines[k].strip()
            if body.startswith('--'):
                stated = RANGE_COMMENT.match(body)
                if stated:
                    start = int(stated[1])
                    end = int(stated[2]) if stated[2] else start
                    segments.append(Segment(k, start, end, []))
            elif body:
                segments[-1].body.append((k, body))
            k += 1
        out.append((number, Path(marker[1]), [s for s in segments if s.body]))
    return out


def match_segment(source: list[str], body: list[tuple[int, str]], lo: int, hi: int) -> list[int] | None:
    """0-based source lines that match ``body`` in order within [lo, hi)."""
    found, k = [], lo
    for _, text in body:
        while k < hi and source[k].strip() != text:
            k += 1
        if k >= hi:
            return None
        found.append(k)
        k += 1
    return found


def check_verbatim(doc: str, lines: list[str], sources: Sources, report: Report,
                   rewrite: dict[int, str] | None = None) -> None:
    for number, path, segments in verbatim_blocks(lines):
        source = sources.lines(path)
        if source is None:
            report.fail(f'{doc}:{number + 1}: verbatim source {path} does not exist')
            continue
        position = 0
        for segment in segments:
            within = None
            if segment.start is not None:
                within = match_segment(source, segment.body, segment.start - 1,
                                       min(segment.end, len(source)))
            anywhere = within or match_segment(source, segment.body, position, len(source))
            if anywhere is None:
                for doc_line, text in segment.body:
                    if text not in {s.strip() for s in source}:
                        report.fail(f'{doc}:{doc_line + 1}: line {text!r} does not occur in {path}')
                        break
                else:
                    report.fail(f'{doc}:{segment.body[0][0] + 1}: the lines of this segment '
                                f'do not occur in this order in {path} after line {position}')
                continue
            first, last = anywhere[0] + 1, anywhere[-1] + 1
            if anywhere[0] < position:
                report.fail(f'{doc}:{segment.body[0][0] + 1}: segment at {path}:{first} comes '
                            f'before the previous segment (the box must follow source order)')
            if segment.start is not None and (first, last) != (segment.start, segment.end):
                stated = (f'{segment.start}' if segment.start == segment.end
                          else f'{segment.start}-{segment.end}')
                actual = f'{first}' if first == last else f'{first}-{last}'
                if rewrite is not None:
                    old = lines[segment.comment_line]
                    rewrite[segment.comment_line] = re.sub(
                        rf':{re.escape(stated)}\b', f':{actual}', old, count=1)
                else:
                    report.fail(f'{doc}:{segment.comment_line + 1}: comment says lines {stated}, '
                                f'but the segment is at {path}:{actual}')
            position = max(position, anywhere[-1] + 1)


def prose_sentences(text: str) -> list[tuple[int, str]]:
    """(first line, sentence) for the prose of a Markdown text.

    Fenced blocks, tables, headings and HTML comments are skipped. List items
    and blank lines end a sentence.
    """
    blocks: list[tuple[int, list[str]]] = []
    fenced = False
    current: list[str] = []
    start = 0
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith('```'):
            fenced = not fenced
            if current:
                blocks.append((start, current))
                current = []
            continue
        breaks = (fenced or not stripped or stripped.startswith(('|', '#', '<!--'))
                  or re.match(r'^(?:[-*]|\d+\.)\s', stripped))
        if breaks and current:
            blocks.append((start, current))
            current = []
        if fenced or not stripped or stripped.startswith(('|', '#', '<!--')):
            continue
        if not current:
            start = number
        current.append(stripped)
    if current:
        blocks.append((start, current))
    out = []
    for first, block in blocks:
        joined = ' '.join(block)
        for sentence in re.split(r'(?<=[.!?])\s+(?=[A-Z`*\[(])', joined):
            out.append((first, sentence))
    return out


def check_certified_wording(doc: str, text: str, base: str | None, sources: Sources,
                            status: ProofStatus, report: Report) -> None:
    for first, sentence in prose_sentences(text):
        for match in INLINE_REF.finditer(sentence):
            path = resolve(match['path'], base)
            lines = sources.lines(path)
            if lines is None:
                continue
            line = int(match['line'])
            if not 1 <= line <= len(lines):
                continue
            if declaration_keyword(lines[line - 1]) not in THEOREM_KEYWORDS:
                continue
            name = match['name']
            if status.certified(path, name):
                continue
            uncertified = re.search(r'not certified|uncertified|not in `?scripts/proof_status',
                                    sentence)
            if re.search(r'\bcertified\b', sentence) and not uncertified:
                report.fail(f'{doc}:{first}: `{name}` is called certified, but '
                            f'{PROOF_STATUS} does not list it for {path}')
            elif re.search(r'\bprov(?:ed|es|en)\b', sentence) and not uncertified:
                report.fail(f'{doc}:{first}: `{name}` is called proved but {PROOF_STATUS} '
                            f'does not list it; say "not certified" in the same sentence')


def code_names(cell: str) -> set[str]:
    names: set[str] = set()
    for code in CODE_SPAN.findall(cell):
        names.update(IDENT.findall(code))
    return names


def check_result_graph(text: str, sources: Sources, rows: list[Row], status: ProofStatus,
                       report: Report) -> int:
    lines = text.splitlines()
    header_at = None
    for number, line in enumerate(lines, 1):
        cells = split_row(line)
        if cells and [c.strip() for c in cells[1:-1]][:1] == [GRAPH_COLUMNS[0]]:
            header_at = number
            header = [c.strip() for c in cells[1:-1]]
            if header != GRAPH_COLUMNS:
                report.fail(f'{STATEMENT}:{number}: result graph columns are {header}, '
                            f'expected {GRAPH_COLUMNS}')
                return 0
            break
    if header_at is None:
        report.fail(f'{STATEMENT}: no result graph table with columns {GRAPH_COLUMNS}')
        return 0
    hypotheses = {row.name for row in rows}
    count = 0
    for number, inner in table_after(lines, header_at):
        where = f'{STATEMENT}:{number}'
        if len(inner) != len(GRAPH_COLUMNS):
            report.fail(f'{where}: {len(inner)} cells, expected {len(GRAPH_COLUMNS)}')
            continue
        name = NAME_CELL.match(inner[1])
        location = LOCATION_CELL.match(inner[2])
        if not name or not location:
            report.fail(f'{where}: theorem and file:line cells must be `name` and `path:line`')
            continue
        count += 1
        theorem, path = name[1], Path(location[1])
        source = sources.lines(path)
        if source is None:
            continue  # reported by the location check
        found = declaration_lines(source, theorem, path)
        if not found:
            continue  # reported by the location check
        at = nearest_line(found, int(location[2])) - 1
        signature = theorem_signature(sources.code(path) or source, at, path)
        if signature is None:
            report.fail(f'{where}: {path}:{at + 1} does not declare `{theorem}` as a theorem')
            continue
        premises = premise_text(signature[1])
        used = {h for h in hypotheses if occurrences(h, premises)}
        edge = code_names(inner[0])
        listed = set() if inner[3].lower().startswith('none') else code_names(inner[3])
        for missing in sorted(listed - used):
            report.fail(f'{where}: premise `{missing}` is listed for `{theorem}`, but its '
                        f'signature ({path}:{at + 1}) does not take it')
        for extra in sorted(used - listed - edge):
            report.fail(f'{where}: `{theorem}` ({path}:{at + 1}) takes the hypothesis '
                        f'`{extra}`, which the premise cell does not list')
        certified = inner[4].split()[0].lower() if inner[4] else ''
        if certified not in ('yes', 'no'):
            report.fail(f'{where}: certified cell must start with yes or no, found {inner[4]!r}')
        elif (certified == 'yes') != status.certified(path, theorem):
            actual = 'lists' if status.certified(path, theorem) else 'does not list'
            report.fail(f'{where}: certified is {certified!r}, but {PROOF_STATUS} {actual} '
                        f'`{theorem}` for {path}')
    return count


def users_by_row(rows: list[Row], sources: Sources,
                 all_theorems: list[Theorem]) -> dict[int, list[Theorem]]:
    """For each row (by line), the theorems whose premises name it."""
    by_name: dict[str, list[Row]] = {}
    for row in rows:
        by_name.setdefault(row.name, []).append(row)
    opens: dict[Path, set[str]] = {}
    out: dict[int, list[Theorem]] = {row.line: [] for row in rows}
    for theorem in all_theorems:
        for name, candidates in by_name.items():
            qualifiers = occurrences(name, theorem.premises)
            if not qualifiers:
                continue
            if len(candidates) == 1:
                out[candidates[0].line].append(theorem)
                continue
            chosen: set[int] = set()
            for qualifier in qualifiers:
                for row in candidates:
                    lean = row.lean_ref()
                    if lean is None:
                        continue
                    stem = lean.resolved.stem
                    if qualifier:
                        if qualifier.rstrip('.').rsplit('.', 1)[-1] == stem:
                            chosen.add(row.line)
                    elif theorem.path.stem == stem:
                        chosen.add(row.line)
            if not chosen and '' in qualifiers:
                if theorem.path not in opens:
                    text = '\n'.join(sources.lines(theorem.path) or [])
                    opens[theorem.path] = {
                        part.rsplit('.', 1)[-1]
                        for line in re.findall(r'^\s*open\s+([^\n]*)', text, re.MULTILINE)
                        for part in line.split()}
                for row in candidates:
                    lean = row.lean_ref()
                    if lean is not None and lean.resolved.stem in opens[theorem.path]:
                        chosen.add(row.line)
            if not chosen:
                chosen = {row.line for row in candidates}
            for line in chosen:
                out[line].append(theorem)
    return out


def check_rows(rows: list[Row], sources: Sources, report: Report, text: str,
               marked: list[Marked]) -> None:
    marks = {(m.name.rsplit('.', 1)[-1], m.path): m for m in marked}
    lean_theorems = theorems(sources, ('.lean',))
    all_theorems = lean_theorems + theorems(sources, ('.v',))
    lean_users = users_by_row(rows, sources, lean_theorems)
    any_users = users_by_row(rows, sources, all_theorems)
    defects = known_defects(text)
    missing_bullet = next((b for b in defects if b.startswith('**Missing markers.**')), None)
    missing_listed = ({c for c in CODE_SPAN.findall(missing_bullet)
                       if NAME_CELL.match(f'`{c}`') and c not in CLASSES}
                      if missing_bullet else set())
    unmarked: set[str] = set()

    for row in rows:
        where = f'{HYPOTHESES}:{row.line}'
        lean_body = ''
        if not row.refs and row.cells[2] == NOT_DEFINED:
            defined = [f'{path}:{line}' for path in sources.all_sources()
                       for line in prop_lines(sources.code(path) or [], row.name, path)]
            if defined:
                report.fail(f'{where}: `{row.name}` is marked {NOT_DEFINED!r}, but it is '
                            f'defined at {defined[0]}; give its locations')
            if row.status.startswith('discharged'):
                report.fail(f'{where}: `{row.name}` is not defined, so it cannot be discharged')
        for _, ref in row.refs:
            lines = sources.lines(ref.resolved)
            if lines is None:
                continue
            props = prop_lines(sources.code(ref.resolved) or lines, ref.name, ref.resolved)
            found = declaration_lines(lines, ref.name, ref.resolved)
            nearest = nearest_line(found, ref.line) if found else None
            if not props:
                report.fail(f'{where}: `{row.name}` is no longer a Prop definition '
                            f'(`def … : Prop` / `Definition … : Prop`) in {ref.resolved}')
                continue
            if nearest is not None and nearest not in props:
                report.fail(f'{where}: {ref.resolved}:{nearest} declares `{row.name}`, '
                            'but not as a Prop definition')
                continue
            at = nearest_line(props, ref.line)
            if ref.resolved.suffix == '.lean':
                body = []
                for j in range(at - 1, min(at + 14, len(lines))):
                    if j > at - 1 and (not lines[j].strip() or re.match(
                            rf'\s*(?:{KEYWORDS}|/-|--|@\[)', lines[j])):
                        break
                    body.append(lines[j])
                lean_body = ' '.join(body)
                kinds = marks.get((row.name, ref.resolved))
                if kinds is None:
                    unmarked.add(row.name)
                elif 'obligation' in kinds.kinds and row.hclass != 'obligation':
                    report.fail(f'{where}: `{row.name}` is marked "Open obligation" in '
                                f'{ref.resolved}:{at}, but its class is {row.hclass!r}')
                elif 'obligation' not in kinds.kinds and row.hclass == 'obligation':
                    report.fail(f'{where}: `{row.name}` is marked as a known theorem in '
                                f'{ref.resolved}:{at}, but its class is obligation')

        # c. the leading code span of the statement
        leading = re.match(r'^`([^`]+)`', row.statement)
        if leading and lean_body:
            for ident in IDENT.findall(leading[1]):
                if ident != row.name and not occurrences(ident, lean_body) \
                        and not re.search(rf"(?<![\w']){re.escape(ident)}(?![\w'])", lean_body):
                    report.fail(f'{where}: the statement mentions `{ident}`, which does not '
                                f'occur in the Lean definition of `{row.name}`')

        # e. dependents
        users = sorted({t.name.rsplit('.', 1)[-1] for t in lean_users[row.line]})
        cell = row.dependents
        if cell.lower().startswith('none'):
            if users:
                report.fail(f'{where}: dependents of `{row.name}` say none, but '
                            f'{len(users)} Lean theorem(s) take it: {", ".join(users[:5])}')
        else:
            listed = [n for n in CODE_SPAN.findall(cell)]
            for name in listed:
                if name not in users:
                    report.fail(f'{where}: `{name}` is listed as a dependent of `{row.name}`, '
                                'but no Lean theorem of that name takes it as a premise')
            total = re.search(r'\((\d+) total\)', cell)
            if '…' in cell:
                if not total:
                    report.fail(f'{where}: the dependents of `{row.name}` end in "…" '
                                f'without "(N total)"; there are {len(users)}')
                elif int(total[1]) != len(users):
                    report.fail(f'{where}: dependents of `{row.name}` say {total[1]} total, '
                                f'but {len(users)} Lean theorems take it')
            else:
                absent = [u for u in users if u not in listed]
                if absent:
                    report.fail(f'{where}: dependents of `{row.name}` omit '
                                f'{", ".join(absent)}')

        # f. discharged on main but still a premise
        if row.status == 'discharged on main':
            still = sorted({f'{t.path}:{t.line}' for t in any_users[row.line]})
            if still:
                documented = (not cell.lower().startswith('none') and any(
                    'discharged' in b.lower() and f'`{row.name}`' in b for b in defects))
                message = (f'{where}: `{row.name}` is discharged on main but still a premise '
                           f'of {len(still)} Lean and Rocq theorem(s), e.g. {still[0]}')
                if documented:
                    report.warn(message + ' (listed in Known defects)')
                else:
                    report.fail(message + '; list it in the dependents cell and in a '
                                '"discharged" bullet of Known defects, or remove the premise')

    # 5. the "Missing markers" bullet
    names = {row.name for row in rows}
    for name in sorted(missing_listed - names):
        report.fail(f'{HYPOTHESES}: `{name}` is listed under Missing markers but has no row')
    for name in sorted(missing_listed & names - unmarked):
        report.fail(f'{HYPOTHESES}: `{name}` is listed under Missing markers, but its Lean '
                    'definition carries a marker now; remove it from the list')
    for name in sorted(unmarked - missing_listed):
        report.fail(f'{HYPOTHESES}: the Lean definition of `{name}` has no marker comment; '
                    'add a marker in the source or list it under Missing markers')


def rewrite_lines(root: Path, sources: Sources, report: Report) -> None:
    """Move every checked location to the nearest current declaration."""
    for doc in (STATEMENT, HYPOTHESES):
        path = root / doc
        if not path.is_file():
            continue
        text = path.read_text(encoding='utf-8')
        base = path_base(text)
        changed = 0

        def nearest(ref: Ref) -> int | None:
            found = declaration_lines(sources.lines(ref.resolved) or [], ref.name, ref.resolved)
            return nearest_line(found, ref.line) if found else None

        for match, ref in reversed(inline_refs(doc, text, base)):
            new = nearest(ref)
            if new is not None and new != ref.line:
                start, end = match.span('line')
                text = text[:start] + str(new) + text[end:]
                changed += 1
        lines = text.splitlines(keepends=True)
        cell_refs = table_cell_refs(doc, text, base)
        if doc == HYPOTHESES:
            for row in hypotheses_table(text, base, Report()):
                cell_refs.extend((row.line, index, ref) for index, ref in row.refs)
        for number, index, ref in cell_refs:
            new = nearest(ref)
            if new is None or new == ref.line:
                continue
            cells = lines[number - 1].split('|')
            cells[index] = cells[index].replace(f'{ref.written}:{ref.line}`',
                                                f'{ref.written}:{new}`', 1)
            lines[number - 1] = '|'.join(cells)
            changed += 1
        rewrite: dict[int, str] = {}
        check_verbatim(doc, [l.rstrip('\n') for l in lines], sources, Report(), rewrite)
        for index, new_line in rewrite.items():
            if lines[index].rstrip('\n') != new_line:
                lines[index] = new_line + '\n'
                changed += 1
        if changed:
            path.write_text(''.join(lines), encoding='utf-8')
            report.notes.append(f'--write-lines: updated {changed} line number(s) in {doc}')


def path_base(text: str) -> str | None:
    match = PATH_BASE.search(text)
    return match[1] if match else None


def run(root: Path, write_lines: bool = False, strict: bool = False) -> Report:
    report = Report()
    sources = Sources(root)
    if write_lines:
        rewrite_lines(root, sources, report)
        sources = Sources(root)

    statement_path = root / STATEMENT
    hypotheses_path = root / HYPOTHESES
    for path in (statement_path, hypotheses_path):
        if not path.is_file():
            report.fail(f'{path.relative_to(root)} does not exist')
    if report.errors:
        return report
    status = ProofStatus(root, report)
    if not status.present:
        report.fail(f'{PROOF_STATUS} does not exist')

    statement = statement_path.read_text(encoding='utf-8')
    claims = check_claims(statement, sources, report)
    check_verbatim(STATEMENT, statement.splitlines(), sources, report)
    refs = [ref for _, ref in inline_refs(STATEMENT, statement, None)]
    refs += [ref for _, _, ref in table_cell_refs(STATEMENT, statement, None)]

    hypotheses = hypotheses_path.read_text(encoding='utf-8')
    base = path_base(hypotheses)
    rows = hypotheses_table(hypotheses, base, report)
    refs += [ref for _, ref in inline_refs(HYPOTHESES, hypotheses, base)]
    for row in rows:
        refs.extend(ref for _, ref in row.refs)
    for ref in refs:
        check_ref(ref, sources, report)

    edges = check_result_graph(statement, sources, rows, status, report)
    check_certified_wording(STATEMENT, statement, None, sources, status, report)
    check_certified_wording(HYPOTHESES, hypotheses, base, sources, status, report)

    seen: dict[tuple[str, str], int] = {}
    registered: set[tuple[str, Path]] = set()
    for row in rows:
        for _, ref in row.refs:
            registered.add((ref.name, ref.resolved))
        key = (row.name, row.refs[0][1].written if row.refs else '')
        if key in seen:
            report.fail(f'{HYPOTHESES}:{row.line}: duplicate row for `{row.name}` '
                        f'(first at line {seen[key]})')
        seen[key] = row.line

    marked = marked_hypotheses(sources)
    check_rows(rows, sources, report, hypotheses, marked)
    row_names = {row.name for row in rows}
    missing = []
    for item in marked:
        short = item.name.rsplit('.', 1)[-1]
        if item.path.suffix == '.agda':
            if short not in row_names:
                missing.append(item)
        elif (short, item.path) not in registered:
            missing.append(item)
    for item in missing:
        report.fail(f'{item.path}:{item.line}: hypothesis `{item.name}` is marked '
                    f'"Known theorem", "not mechanised" or "Open obligation" but has no '
                    f'row in {HYPOTHESES}')
    if missing:
        names = ', '.join(sorted({item.name for item in missing}))
        report.fail(f'unregistered hypotheses: {names}')

    counts = {c: sum(1 for row in rows if row.hclass == c) for c in CLASSES}
    report.notes.append(f'{STATEMENT}: {claims} claims, {len(refs)} located references, '
                        f'{edges} result-graph rows checked')
    report.notes.append(f'{HYPOTHESES}: {len(rows)} rows (' +
                        ', '.join(f'{c} {n}' for c, n in counts.items()) + ')')
    report.notes.append(f'{len(marked)} marked definitions under proofs/, '
                        f'{len(missing)} unregistered')
    if strict and report.warnings:
        report.errors.extend(f'(strict) {w}' for w in report.warnings)
        report.warnings = []
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--write-lines', action='store_true',
                        help='rewrite line numbers to the current declarations, then check')
    parser.add_argument('--strict', action='store_true',
                        help='treat every warning as a failure')
    parser.add_argument('--root', type=Path, default=ROOT,
                        help='repository root (default: the parent of scripts/)')
    args = parser.parse_args(argv)
    report = run(args.root.resolve(), args.write_lines, args.strict)
    for note in report.notes:
        print(note)
    for warning in report.warnings:
        print(f'WARN {warning}')
    for error in report.errors:
        print(f'FAIL {error}', file=sys.stderr)
    if report.errors:
        print(f'check_formal_statement: {len(report.errors)} failure(s), '
              f'{len(report.warnings)} warning(s)', file=sys.stderr)
        return 1
    print(f'check_formal_statement: OK ({len(report.warnings)} warning(s))')
    return 0


if __name__ == '__main__':
    sys.exit(main())
