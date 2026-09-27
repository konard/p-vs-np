#!/usr/bin/env python3
"""Audit the small, explicit set of certified results.

Everything outside proof_status.json remains historical compilation only. The
source scan rejects admissions anywhere in a certified module's local import
closure; prover queries catch transitive assumptions in each public theorem.
"""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path(__file__).with_name("proof_status.json")
FORBIDDEN = {
    "lean": re.compile(r"\b(?:sorry|admit|axiom|constant|opaque|native_decide)\b"),
    "rocq": re.compile(r"\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b"),
}


def strip_comments_and_strings(source: str, language: str) -> str:
    """Replace comments and strings with spaces, retaining line numbers."""
    opening, closing = ("/-", "-/") if language == "lean" else ("(*", "*)")
    output = []
    depth = 0
    quoted = False
    index = 0
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == opening:
                depth += 1
                output.extend("  ")
                index += 2
            elif pair == closing:
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif quoted:
            if source[index] == "\\" and index + 1 < len(source):
                output.extend("  ")
                index += 2
            elif source[index] == '"':
                quoted = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif pair == opening:
            depth = 1
            output.extend("  ")
            index += 2
        elif language == "lean" and pair == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            output.extend(" " * (end - index))
            index = end
        elif source[index] == '"':
            quoted = True
            output.append(" ")
            index += 1
        else:
            output.append(source[index])
            index += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string")
    return "".join(output)


def local_imports(root: Path, path: Path) -> set[Path]:
    language = "lean" if path.suffix == ".lean" else "rocq"
    source = strip_comments_and_strings(path.read_text(encoding="utf-8"), language)
    modules = []
    if language == "lean":
        for match in re.finditer(r"(?m)^\s*import\s+([^\n]+)", source):
            modules.extend(match.group(1).split())
    else:
        for match in re.finditer(
            r"\bFrom\s+(proofs(?:\.[\w]+)*)\s+Require\s+(?:Import|Export)\s+([^.]*)\.", source
        ):
            modules.extend(f"{match.group(1)}.{name}" for name in match.group(2).split())
        for match in re.finditer(r"(?m)^\s*Require\s+(?:Import|Export)\s+(.+?)\.\s*$", source):
            modules.extend(name for name in match.group(1).split() if name.startswith("proofs."))
    result = set()
    for module in modules:
        if module.startswith("proofs."):
            dependency = root / (module.replace(".", "/") + path.suffix)
            if not dependency.is_file():
                raise ValueError(f"{path}: missing local import {module}")
            result.add(dependency)
    return result


def source_closure(root: Path, entries: list[dict]) -> set[Path]:
    pending = [root / item["source"] for item in entries]
    visited = set()
    while pending:
        path = pending.pop()
        if path in visited:
            continue
        if not path.is_file():
            raise ValueError(f"missing certified source: {path}")
        visited.add(path)
        pending.extend(local_imports(root, path) - visited)
    return visited


def check_sources(root: Path, paths: set[Path] | list[Path]) -> list[str]:
    failures = []
    for path in sorted(paths):
        language = "lean" if path.suffix == ".lean" else "rocq"
        source = strip_comments_and_strings(path.read_text(encoding="utf-8"), language)
        for match in FORBIDDEN[language].finditer(source):
            line = source.count("\n", 0, match.start()) + 1
            failures.append(f"{path.relative_to(root)}:{line}: certified source uses {match.group()}")
    return failures


def parse_lean_axioms(output: str) -> set[str]:
    match = re.search(r"depends on axioms:\s*\[([^]]*)\]", output)
    if match:
        return {item.strip() for item in match.group(1).split(",") if item.strip()}
    if "does not depend on any axioms" in output:
        return set()
    raise ValueError(f"Lean did not report axioms: {output.strip()}")


def parse_rocq_assumptions(output: str) -> set[str]:
    if "Closed under the global context" in output:
        return set()
    if "Axioms:" not in output:
        raise ValueError(f"Rocq did not report assumptions: {output.strip()}")
    names = set(re.findall(r"(?m)^([A-Za-z_][\w.']*)\s*:", output.split("Axioms:", 1)[1]))
    if not names:
        raise ValueError(f"Could not parse Rocq assumptions: {output.strip()}")
    return names


def query_assumptions(root: Path, language: str, entry: dict) -> set[str]:
    module = entry["source"].removesuffix(".lean").removesuffix(".v").replace("/", ".")
    if language == "lean":
        source = f"import {module}\n#print axioms {entry['theorem']}\n"
        command = ["lake", "env", "lean"]
        suffix = ".lean"
    else:
        parent, name = module.rsplit(".", 1)
        source = f"From {parent} Require Import {name}.\nPrint Assumptions {entry['theorem']}.\n"
        command = ["rocq", "compile", "-Q", ".", ""]
        suffix = ".v"
    with tempfile.TemporaryDirectory(prefix="proof_status_") as directory:
        probe = Path(directory) / f"Audit{suffix}"
        probe.write_text(source, encoding="utf-8")
        result = subprocess.run([*command, str(probe)], cwd=root, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if result.returncode:
        raise ValueError(f"{language} query for {entry['theorem']} failed:\n{output}")
    return parse_lean_axioms(output) if language == "lean" else parse_rocq_assumptions(output)


def audit(root: Path, manifest: dict, languages: list[str], query: bool) -> list[str]:
    failures = []
    for language in languages:
        entries = manifest[language]
        paths = source_closure(root, entries)
        failures.extend(check_sources(root, paths))
        if query and not failures:
            for entry in entries:
                assumptions = query_assumptions(root, language, entry)
                allowed = set(entry["allowed_axioms"])
                print(f"{language} {entry['theorem']}: {', '.join(sorted(assumptions)) or '(none)'}")
                if assumptions - allowed:
                    failures.append(
                        f"{language} {entry['theorem']}: unapproved assumptions: "
                        + ", ".join(sorted(assumptions - allowed))
                    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="query certified Lean theorems")
    parser.add_argument("--rocq", action="store_true", help="query certified Rocq theorems")
    arguments = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    languages = [name for name in ("lean", "rocq") if getattr(arguments, name)]
    try:
        failures = audit(ROOT, manifest, languages or ["lean", "rocq"], bool(languages))
    except ValueError as error:
        failures = [str(error)]
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print("Certified source and assumption audit passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
