#!/usr/bin/env python3
"""Check the forty-one issue #532 idea dossiers and their paired proof files.

For every idea NN the checker requires:

* ``proofs/experiments/issue532/ideas/IdeaNN.md`` with the fixed section
  headings, one allowed verdict, and a section-3 table whose theorem names
  are declared in both the Lean and the Rocq file;
* ``lean/IdeaNN.lean`` in namespace ``Issue532.IdeaNN`` and ``rocq/IdeaNN.v``,
  both free of admissions, axioms, and trivial ``True`` conclusions;
* every definition whose doc comment calls it an "open obligation" lives in a
  file that imports the shared machine model, mentions that model (directly or
  through other definitions of the same file), and quantifies over no free cost
  function such as ``∃ (time : α → Nat)``: its cost must be a ``Run`` step count;
* a link to the dossier from ``RESEARCH_LOG.md``.

Compilation itself is done by ``lake build`` and ``rocq compile`` in CI.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

from check_proof_status import strip_comments_and_strings  # noqa: E402

BASE = ROOT / "proofs" / "experiments" / "issue532"
IDEAS = range(1, 42)
# Shared machine layer; a section-3 row may name a theorem declared there.
SHARED = {
    "lean": [BASE / "lean" / "Machines.lean", BASE / "lean" / "Circuits.lean"],
    "rocq": [BASE / "rocq" / "Machines.v", BASE / "rocq" / "Circuits.v"],
}

SECTIONS = [
    "## 1. The idea at full strength",
    "## 2. Precise mathematical formulation",
    "## 3. What is machine-checked",
    "## 4. Complete argument",
    "## 5. Known results and literature",
    "## 6. How far the idea can be pushed toward P vs NP",
    "## 7. Failure modes this idea catches",
    "## 8. Reproduction",
]

VERDICTS = [
    "Refuted as a route (general theorem)",
    "Refuted in full strength (published theorem) + formal core",
    "Developed to an open obligation (conditional theorem proved)",
    "Correct tool, insufficient alone (general theorem proved)",
]

FORBIDDEN = {
    "lean": re.compile(
        r"\b(?:sorry|admit|axiom|constant|opaque|native_decide|unsafe|implemented_by)\b"
    ),
    "rocq": re.compile(r"\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Hypothesis)\b"),
}

TRIVIAL = {
    "lean": re.compile(r"(?s)\btheorem\s+\w+[^:=]*:\s*True\s*:="),
    "rocq": re.compile(r"\b(?:Theorem|Lemma)\s+\w+[^.]*:\s*True\s*\."),
}

DECLARATION = {
    "lean": r"\b(?:theorem|lemma|def|abbrev|structure|inductive)\s+(?:[\w']+\.)*{name}(?![\w'])",
    "rocq": r"\b(?:Theorem|Lemma|Corollary|Proposition|Definition|Fixpoint|Inductive|Record)\s+{name}(?![\w'])",
}


# Names of the shared machine model (``proofs/complexity`` and the issue #532
# ``Machines`` layer) whose meaning is tied to ``Complexity.Run`` step counts.
MACHINE_NAMES = {
    "Run", "Reaches", "DecidesWithin", "DecidesOn", "PolyDec", "Computes",
    "PolyReduces", "InP", "InNP", "InCoNP", "PEqualsNP", "PNotEqualsNP",
    "NPEqualsCoNP", "NPHard", "NPComplete", "ClassP", "ClassNP", "InRP",
    "SAT", "SATInNP", "SATHard", "CookLevin", "InPPoly", "PSubsetPPoly", "CircuitDecides",
}

SHARED_IMPORT = {
    "lean": re.compile(
        r"^import\s+proofs\.(?:complexity\.lean\.Complexity|experiments\.issue532\.lean\.(?:Machines|Circuits))\s*$",
        re.MULTILINE,
    ),
    "rocq": re.compile(r"^From\s+proofs\.\S+\s+Require\s+Import\s+.*\b(?:Complexity|Machines|Circuits)\b", re.MULTILINE),
}

DOCUMENTED = {
    "lean": re.compile(
        r"/--(?P<doc>(?:(?!-/).)*)-/\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*"
        r"(?:def|abbrev|structure|inductive)\s+(?P<name>[\w'.]+)",
        re.DOTALL,
    ),
    "rocq": re.compile(
        r"\(\*\*(?P<doc>(?:(?!\*\)).)*)\*\)\s*(?:Definition|Fixpoint|Inductive|Record)\s+(?P<name>[\w']+)",
        re.DOTALL,
    ),
}

DEFINITION = {
    "lean": re.compile(
        r"^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|structure|inductive)\s+(?P<name>[\w'.]+)",
        re.MULTILINE,
    ),
    "rocq": re.compile(r"^(?:Definition|Fixpoint|Inductive|Record)\s+(?P<name>[\w']+)", re.MULTILINE),
}

FREE_COST = {
    "lean": re.compile(r"(?:∃|\()\s*(?P<names>[\w' ]+?)\s*:\s*[^,()]*?→\s*Nat\b"),
    "rocq": re.compile(r"(?:\bexists|\()\s*(?P<names>[\w' ]+?)\s*:\s*[^,()]*?->\s*nat\b"),
}

# A binder for a free predicate, such as ``(PolyTime : (α → β) → Prop)``: the
# obligation would then hold or fail depending on how the predicate is chosen.
FREE_PREDICATE = {
    "lean": re.compile(r"[({]\s*(?P<names>[\w' ]+?)\s*:\s*(?:[^(){}]|\([^()]*\))*?→\s*Prop\s*[)}]"),
    "rocq": re.compile(r"[({]\s*(?P<names>[\w' ]+?)\s*:\s*(?:[^(){}]|\([^()]*\))*?->\s*Prop\s*[)}]"),
}

COST_NAME = re.compile(r"^(?:t|T|time\w*|cost\w*|steps?|runtime\w*)$")

OBLIGATION = re.compile(r"open\s+obligation", re.IGNORECASE)


def definition_body(language: str, stripped: str, start: int) -> str:
    """Text of the declaration starting at ``start`` in the stripped source."""
    if language == "lean":
        # A Lean declaration ends before the next line that starts in column 0.
        match = re.compile(r"\n(?=\S)").search(stripped, start + 1)
    else:
        match = re.compile(r"\.(?=\s)").search(stripped, start)
    return stripped[start:match.start() if match else len(stripped)]


def machine_tied_definitions(language: str, stripped: str) -> set[str]:
    """Definitions of the file that mention the machine model, transitively."""
    bodies = {
        match.group("name").split(".")[-1]: definition_body(language, stripped, match.start())
        for match in DEFINITION[language].finditer(stripped)
    }
    tied = set(MACHINE_NAMES)
    changed = True
    while changed:
        changed = False
        for name, body in bodies.items():
            if name in tied:
                continue
            words = set(re.findall(r"[A-Za-z_][\w']*", body)) - {name}
            if words & tied:
                tied.add(name)
                changed = True
    return tied


def check_obligations(language: str, source: str, stripped: str, name: str) -> list[str]:
    """Open obligations must be statements about the shared machine model."""
    errors = []
    tied = None
    for match in DOCUMENTED[language].finditer(source):
        if not OBLIGATION.search(match.group("doc")):
            continue
        definition = match.group("name").split(".")[-1]
        if not SHARED_IMPORT[language].search(stripped):
            errors.append(f"{name}: open obligation `{definition}` without importing the shared machine model")
        if tied is None:
            tied = machine_tied_definitions(language, stripped)
        body = definition_body(language, stripped, match.start("name"))
        words = set(re.findall(r"[A-Za-z_][\w']*", body)) - {definition}
        if not words & tied:
            errors.append(f"{name}: open obligation `{definition}` does not mention the machine model")
        for cost in FREE_COST[language].finditer(body):
            names = cost.group("names").split()
            if any(COST_NAME.match(candidate) for candidate in names):
                errors.append(
                    f"{name}: open obligation `{definition}` quantifies over a free cost function; "
                    "use a `Run` step count"
                )
        for predicate in FREE_PREDICATE[language].finditer(body):
            errors.append(
                f"{name}: open obligation `{definition}` binds a free predicate "
                f"`{predicate.group('names').strip()}`; use the machine model's classes"
            )
    return errors


def paths(number: int) -> dict[str, Path]:
    stem = f"Idea{number:02d}"
    return {
        "md": BASE / "ideas" / f"{stem}.md",
        "lean": BASE / "lean" / f"{stem}.lean",
        "rocq": BASE / "rocq" / f"{stem}.v",
    }


def table_rows(markdown: str) -> list[list[str]]:
    """Backticked names in the first column of each section-3 table row."""
    start = markdown.find(SECTIONS[2])
    end = markdown.find(SECTIONS[3])
    rows = []
    for line in markdown[start:end].splitlines():
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 4 or set(cells[0]) <= {"-", ":", " "}:
            continue
        names = re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)`", cells[0])
        if names:
            rows.append(names)
    return rows


def table_names(markdown: str) -> list[str]:
    return [name for row in table_rows(markdown) for name in row]


def declared(language: str, stripped: str, name: str) -> bool:
    short = re.escape(name.split(".")[-1])
    return re.search(DECLARATION[language].format(name=short), stripped) is not None


def check_prover_file(language: str, path: Path, number: int) -> list[str]:
    source = path.read_text()
    stripped = strip_comments_and_strings(source, language)
    errors = []
    match = FORBIDDEN[language].search(stripped)
    if match:
        errors.append(f"{path.name}: forbidden token `{match.group(0)}`")
    if TRIVIAL[language].search(stripped):
        errors.append(f"{path.name}: theorem with trivial `True` conclusion")
    keyword = r"\btheorem\b" if language == "lean" else r"\b(?:Theorem|Lemma)\b"
    if len(re.findall(keyword, stripped)) < 2:
        errors.append(f"{path.name}: fewer than two theorems")
    if language == "lean" and f"namespace Issue532.Idea{number:02d}" not in stripped:
        errors.append(f"{path.name}: missing namespace Issue532.Idea{number:02d}")
    errors.extend(check_obligations(language, source, stripped, path.name))
    return errors


def check_idea(number: int) -> list[str]:
    files = paths(number)
    missing = [str(path.relative_to(ROOT)) for path in files.values() if not path.is_file()]
    if missing:
        return [f"Idea{number:02d}: missing {', '.join(missing)}"]

    errors = []
    markdown = files["md"].read_text()
    if not markdown.startswith(f"# Idea {number:02d} — "):
        errors.append(f"Idea{number:02d}.md: title must start with '# Idea {number:02d} — '")
    positions = [markdown.find(section) for section in SECTIONS]
    for section, position in zip(SECTIONS, positions):
        if position < 0:
            errors.append(f"Idea{number:02d}.md: missing section '{section}'")
    if all(position >= 0 for position in positions) and positions != sorted(positions):
        errors.append(f"Idea{number:02d}.md: sections out of order")
    verdict = re.search(r"^\*\*Verdict:\*\*\s*(.+)$", markdown, re.MULTILINE)
    if not verdict or not any(verdict.group(1).startswith(v) for v in VERDICTS):
        errors.append(f"Idea{number:02d}.md: missing or unknown verdict")
    for target in (f"../lean/Idea{number:02d}.lean", f"../rocq/Idea{number:02d}.v"):
        if target not in markdown:
            errors.append(f"Idea{number:02d}.md: no link to {target}")

    for language in ("lean", "rocq"):
        errors.extend(check_prover_file(language, files[language], number))
        # An idea that claims an open obligation must state it in the file,
        # where `check_obligations` ties it to the machine model.
        if verdict and verdict.group(1).startswith(VERDICTS[2]) and not any(
            OBLIGATION.search(match.group("doc"))
            for match in DOCUMENTED[language].finditer(files[language].read_text())
        ):
            errors.append(
                f"Idea{number:02d}: verdict claims an open obligation but {files[language].name} "
                "labels no definition as one"
            )

    if not any(section in markdown for section in SECTIONS[2:4]):
        return errors
    rows = table_rows(markdown)
    if not rows:
        errors.append(f"Idea{number:02d}.md: section 3 table lists no theorem names")
    sources = {
        language: "\n".join(
            strip_comments_and_strings(path.read_text(), language)
            for path in [files[language], *SHARED[language]]
            if path.is_file()
        )
        for language in ("lean", "rocq")
    }
    for row in rows:
        # A row may give different Lean and Rocq names for one theorem.
        for name in row:
            if not any(declared(language, sources[language], name) for language in sources):
                errors.append(f"Idea{number:02d}.md: `{name}` is declared in neither file")
        for language, source in sources.items():
            if not any(declared(language, source, name) for name in row):
                errors.append(
                    f"Idea{number:02d}.md: row {', '.join(row)} has no declaration in "
                    f"{files[language].name}"
                )
    return errors


def check_log() -> list[str]:
    log = (BASE / "RESEARCH_LOG.md").read_text()
    return [
        f"RESEARCH_LOG.md: no link to ideas/Idea{number:02d}.md"
        for number in IDEAS
        if f"ideas/Idea{number:02d}.md" not in log
    ]


def main() -> int:
    errors = check_log()
    for number in IDEAS:
        errors.extend(check_idea(number))
    for error in errors:
        print(f"error: {error}")
    if errors:
        return 1
    print(f"Checked {len(IDEAS)} idea dossiers with paired Lean and Rocq files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
