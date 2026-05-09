#!/usr/bin/env python3
"""
Script to verify P vs NP attempt structure and generate markdown lists.

This script checks that each attempt follows the required directory structure:
- README.md        (required - overview of the attempt)
- original/        (preferred location for the original paper materials)
  - README.md      (recommended - description of the original proof idea)
  - ORIGINAL.md    (recommended - markdown reconstruction of paper)
  - ORIGINAL.pdf   (recommended - original paper file)
- ORIGINAL.md      (legacy location, still accepted for compatibility)
- ORIGINAL.pdf     (legacy location, still accepted for compatibility)
- proof/           (forward proof formalization)
  - README.md      (recommended - explanation of proofs)
  - lean/          (optional - Lean 4 formalizations)
  - rocq/          (optional - Rocq formalizations)
- refutation/      (refutation formalization)
  - README.md      (recommended - explanation of failures)
  - lean/          (optional - Lean 4 formalizations)
  - rocq/          (optional - Rocq formalizations)

Usage:
    python3 scripts/check_attempt_structure.py
    python3 scripts/check_attempt_structure.py --offline
    python3 scripts/check_attempt_structure.py --json attempts_report.json
    python3 scripts/check_attempt_structure.py --path proofs/attempts/specific-attempt
    python3 scripts/check_attempt_structure.py --generate-list
    python3 scripts/check_attempt_structure.py --generate-list --output proofs/attempts/ATTEMPTS.md
"""

import json
import sys
import re
from html.parser import HTMLParser
from pathlib import Path
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin
from urllib.request import urlopen


WOEGINGER_URL = "https://wscor.win.tue.nl/woeginger/P-versus-NP.htm"
STOPWORDS = {
    "abs", "and", "are", "arxiv", "article", "attempt", "available", "based",
    "class", "contains", "equal", "from", "http", "https", "into", "model",
    "not", "org", "paper", "papers", "problem", "proof", "proves", "showed",
    "shows", "solution", "that", "the", "this", "time", "versus", "with",
}


@dataclass(frozen=True)
class WoegingerAttempt:
    """A live entry parsed from Woeginger's P-versus-NP page."""
    entry_id: int
    claim: str
    year: str
    author: str
    title: str
    summary: str
    source_url: str
    links: Tuple[str, ...] = ()


@dataclass
class WoegingerMatch:
    """Best repository match for a live Woeginger entry."""
    attempt: WoegingerAttempt
    validation: Optional["StructureValidation"]
    score: int
    reasons: List[str] = field(default_factory=list)


@dataclass
class AttemptMetadata:
    """Parsed metadata from an attempt's README.md."""
    author: str = ""
    year: str = ""
    claim: str = ""  # P=NP, P!=NP, or unprovable
    title: str = ""
    source: str = ""
    attempt_id: str = ""


@dataclass
class StructureValidation:
    """Results of validating an attempt's structure."""
    path: Path
    has_readme: bool = False
    has_original_dir: bool = False
    has_original_readme: bool = False
    has_original_md: bool = False
    has_original_file: bool = False  # PDF, HTML, or other original format
    original_file_ext: str = ""
    has_proof: bool = False
    has_proof_readme: bool = False
    has_proof_lean: bool = False
    has_proof_rocq: bool = False
    proof_lean_files: List[str] = field(default_factory=list)
    proof_rocq_files: List[str] = field(default_factory=list)
    has_refutation: bool = False
    has_refutation_readme: bool = False
    has_refutation_lean: bool = False
    has_refutation_rocq: bool = False
    refutation_lean_files: List[str] = field(default_factory=list)
    refutation_rocq_files: List[str] = field(default_factory=list)
    metadata: Optional[AttemptMetadata] = None
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)

    def is_valid(self) -> bool:
        """Check if the attempt has minimum required components."""
        return self.has_readme

    def is_complete(self) -> bool:
        """Check if the attempt has all recommended components."""
        return (
            self.has_readme and
            self.has_original_md and
            self.has_original_file and
            self.has_proof and
            self.has_refutation
        )

    def has_lean(self) -> bool:
        """Check if the attempt has any Lean formalization."""
        return self.has_proof_lean or self.has_refutation_lean

    def has_rocq(self) -> bool:
        """Check if the attempt has any Rocq formalization."""
        return self.has_proof_rocq or self.has_refutation_rocq

    def get_missing(self) -> List[str]:
        """List missing components."""
        missing = []
        if not self.has_readme:
            missing.append("README.md (required)")
        if not self.has_original_md:
            missing.append("ORIGINAL.md (recommended, root or original/)")
        if not self.has_original_file:
            missing.append("ORIGINAL.pdf or ORIGINAL.html (recommended, root or original/)")
        if not self.has_proof:
            missing.append("proof/ directory (recommended)")
        elif not self.has_proof_readme:
            missing.append("proof/README.md (recommended)")
        if not self.has_refutation:
            missing.append("refutation/ directory (recommended)")
        elif not self.has_refutation_readme:
            missing.append("refutation/README.md (recommended)")
        return missing

    def get_claim_emoji(self) -> str:
        """Get emoji for the claim type."""
        if self.metadata:
            claim = self.metadata.claim.lower()
            if "p=np" in claim or "peqnp" in claim:
                return "✓"  # P=NP claim
            elif "p≠np" in claim or "pneqnp" in claim or "p!=np" in claim or "p ≠ np" in claim:
                return "✗"  # P≠NP claim
            elif "unprovable" in claim:
                return "?"  # Unprovable claim
        # Try to infer from folder name
        folder_name = self.path.name.lower()
        if "peqnp" in folder_name:
            return "✓"
        elif "pneqnp" in folder_name:
            return "✗"
        elif "unprovable" in folder_name:
            return "?"
        return "-"


class WoegingerHTMLParser(HTMLParser):
    """Extract top-level milestone entries from Woeginger's HTML page.

    The source HTML omits closing </li> tags, so each new <li> finalizes the
    previous entry.
    """

    def __init__(self, source_url: str):
        super().__init__(convert_charrefs=True)
        self.source_url = source_url
        self._in_h2 = False
        self._seen_milestones = False
        self._in_milestones = False
        self._current_text: Optional[List[str]] = None
        self._current_links: Optional[List[str]] = None
        self.items: List[Tuple[str, Tuple[str, ...]]] = []

    def handle_starttag(self, tag: str, attrs: List[Tuple[str, Optional[str]]]):
        attrs_dict = dict(attrs)
        if tag == "h2":
            self._in_h2 = True
            return

        if tag == "ol" and self._seen_milestones and not self._in_milestones:
            self._in_milestones = True
            return

        if tag == "li" and self._in_milestones:
            self._finish_item()
            self._current_text = []
            self._current_links = []
            return

        if tag == "a" and self._current_links is not None:
            href = attrs_dict.get("href")
            if href:
                self._current_links.append(urljoin(self.source_url, href))

    def handle_endtag(self, tag: str):
        if tag == "h2":
            self._in_h2 = False
        elif tag == "ol" and self._in_milestones:
            self._finish_item()
            self._in_milestones = False

    def handle_data(self, data: str):
        if self._in_h2 and "milestones" in data.lower():
            self._seen_milestones = True
        if self._current_text is not None:
            self._current_text.append(data)

    def _finish_item(self):
        if self._current_text is None:
            return
        text = normalize_whitespace("".join(self._current_text))
        if text:
            self.items.append((text, tuple(self._current_links or [])))
        self._current_text = None
        self._current_links = None


def normalize_whitespace(text: str) -> str:
    """Collapse whitespace in parsed prose."""
    return re.sub(r"\s+", " ", text).strip()


def normalize_token_text(text: str) -> str:
    """Normalize text for fuzzy matching."""
    text = text.lower().replace("≠", " not equal ").replace("=/=", " not equal ")
    text = text.replace("!=", " not equal ").replace("=", " equal ")
    return re.sub(r"[^a-z0-9]+", " ", text)


def significant_tokens(text: str) -> Set[str]:
    """Tokenize text and remove common low-information words."""
    return {
        token
        for token in normalize_token_text(text).split()
        if len(token) > 2 and token not in STOPWORDS
    }


def first_year(text: str) -> str:
    """Return the first four-digit year in text, or an empty string."""
    match = re.search(r"\b(19|20)\d{2}\b", text)
    return match.group(0) if match else ""


def normalize_claim(claim: str) -> str:
    """Normalize claim labels used in folder names, READMEs, and Woeginger."""
    lowered = normalize_token_text(claim)
    if "unprovable" in lowered:
        return "unprovable"
    if "undecidable" in lowered:
        return "undecidable"
    if "not equal" in lowered or "pneqnp" in lowered or "pne np" in lowered:
        return "pneqnp"
    if "p np" in lowered or "peqnp" in lowered or "equal np" in lowered:
        return "peqnp"
    if "both" in lowered:
        return "both"
    return ""


def infer_claim_from_folder(folder_name: str) -> str:
    """Infer normalized claim from an attempt directory name."""
    lowered = folder_name.lower()
    if "unprovable" in lowered:
        return "unprovable"
    if "undecidable" in lowered:
        return "undecidable"
    if "pneqnp" in lowered:
        return "pneqnp"
    if "peqnp" in lowered or "peqnppspace" in lowered:
        return "peqnp"
    if "both" in lowered:
        return "both"
    return ""


def extract_claim(text: str) -> Tuple[str, str]:
    """Extract Woeginger's leading bracketed claim label."""
    match = re.match(r"\[(Equal|Not equal|Undecidable|Unprovable)\]:\s*(.*)", text, re.IGNORECASE)
    if match:
        label = match.group(1).lower()
        body = match.group(2)
        claims = {
            "equal": "P = NP",
            "not equal": "P != NP",
            "undecidable": "Undecidable",
            "unprovable": "Unprovable",
        }
        return claims[label], body

    lowered = text.lower()
    if "p-not-equal-to-np" in lowered or "p is not equal to np" in lowered:
        return "P != NP", text
    if "p=np" in lowered or "p = np" in lowered:
        return "P = NP", text
    return "Unclassified", text


def extract_title(text: str) -> str:
    """Extract a likely paper title from a Woeginger entry."""
    for pattern in (
        r'"([^"]{3,180})"',
        r"“([^”]{3,180})”",
        r"paper\s+([^.;]{3,180}?)\s+by\s+[A-Z]",
        r"called\s+([^.,;]{3,180})",
        r"title\s+([^.,;]{3,180})",
    ):
        match = re.search(pattern, text)
        if match:
            title = normalize_whitespace(match.group(1))
            if title.lower() not in {"p versus np", "p=np", "p = np", "p not equal np"}:
                return title
            return title

    first_sentence = re.split(r"(?<=[.!?])\s+", text, maxsplit=1)[0]
    return first_sentence[:120].rstrip(" ,;")


def extract_author(text: str) -> str:
    """Heuristically extract the author names from a Woeginger entry."""
    name = r"(?:[A-Z][A-Za-zÀ-ÖØ-öø-ÿ.\-']+|[a-z]{1,3})"
    patterns = [
        rf"(?:In|Around|On|Since)\s+(?:[A-Za-z]+\s+)?(?:\d{{4}}(?:/\d{{2}})?|summer\s+\d{{4}}|spring\s+\d{{4}})[:,]?\s+({name}(?:\s+(?:{name}|and|&|,)){{0,12}}?)\s+(?:proved|constructed|designed|showed|established|introduced|wrote|provided|published|made|put|started|claimed)",
        r"Here is\s+([A-Z][A-Za-zÀ-ÖØ-öø-ÿ.\-'\s]+?)'s",
        rf"\bThe authors are\s+({name}(?:\s+(?:{name}|and|&|,)){{0,12}})",
        rf"\bpaper\s+[^.]+?\s+by\s+({name}(?:\s+{name}){{0,5}})",
        rf"^({name}(?:\s+(?:{name}|and|&|,)){{0,12}}?)\s+(?:proved|constructed|designed|showed|established|introduced|wrote|provided|published|made|put|has|started)",
        rf"\bby\s+({name}(?:\s+(?:{name}|and|&|,)){{0,12}})",
    ]
    for pattern in patterns:
        match = re.search(pattern, text)
        if not match:
            continue
        author = normalize_whitespace(match.group(1))
        author = re.split(r"(?<!\b[A-Z])\.\s+", author, maxsplit=1)[0]
        author = re.sub(r"\s+(?:that|with|from|in|on|at)$", "", author, flags=re.IGNORECASE)
        author = author.strip(" ,.;")
        if not re.search(r"[A-Z]", author):
            continue
        if 2 < len(author) <= 120:
            return author
    return ""


def parse_woeginger_html(html: str, source_url: str = WOEGINGER_URL) -> List[WoegingerAttempt]:
    """Parse live Woeginger HTML into milestone entries."""
    parser = WoegingerHTMLParser(source_url)
    parser.feed(html)

    attempts = []
    for index, (raw_text, links) in enumerate(parser.items, start=1):
        claim, body = extract_claim(raw_text)
        attempts.append(
            WoegingerAttempt(
                entry_id=index,
                claim=claim,
                year=first_year(body),
                author=extract_author(body),
                title=extract_title(body),
                summary=body,
                source_url=source_url,
                links=links,
            )
        )
    return attempts


def fetch_woeginger_attempts(url: str = WOEGINGER_URL) -> List[WoegingerAttempt]:
    """Fetch and parse Woeginger's live P-versus-NP page."""
    with urlopen(url) as response:
        charset = response.headers.get_content_charset() or "latin-1"
        html = response.read().decode(charset, errors="replace")
    attempts = parse_woeginger_html(html, url)
    if not attempts:
        raise ValueError(f"No Woeginger milestone entries parsed from {url}")
    return attempts


def validation_match_text(validation: StructureValidation) -> str:
    """Collect searchable text from one repository attempt."""
    metadata = validation.metadata or AttemptMetadata()
    pieces = [
        validation.path.name,
        metadata.author,
        metadata.year,
        metadata.claim,
        metadata.title,
        metadata.source,
        format_folder_name(validation.path.name),
    ]
    return " ".join(piece for piece in pieces if piece)


def score_woeginger_match(attempt: WoegingerAttempt, validation: StructureValidation) -> Tuple[int, List[str]]:
    """Score how well a repository attempt matches one Woeginger entry."""
    metadata = validation.metadata or AttemptMetadata()
    repo_text = validation_match_text(validation)
    repo_tokens = significant_tokens(repo_text)
    attempt_tokens = significant_tokens(
        f"{attempt.author} {attempt.year} {attempt.title} {attempt.summary[:240]}"
    )
    reasons: List[str] = []
    score = 0

    overlap = attempt_tokens & repo_tokens
    if overlap:
        score += min(len(overlap), 8)
        reasons.append(f"token overlap: {', '.join(sorted(overlap)[:5])}")

    if attempt.year and attempt.year in repo_text:
        score += 5
        reasons.append(f"year {attempt.year}")
    elif attempt.year and (metadata.year or re.search(r"\b(19|20)\d{2}\b", validation.path.name)):
        score -= 5
        reasons.append(f"year mismatch for {attempt.year}")

    author_tokens = significant_tokens(attempt.author)
    repo_author_tokens = significant_tokens(metadata.author)
    if author_tokens:
        author_overlap = author_tokens & (repo_author_tokens or repo_tokens)
        if author_overlap:
            score += 4 + len(author_overlap)
            reasons.append(f"author: {', '.join(sorted(author_overlap))}")
        elif repo_author_tokens:
            score -= 6
            reasons.append("author mismatch")

    title_tokens = significant_tokens(attempt.title)
    title_overlap = title_tokens & repo_tokens
    if len(title_overlap) >= 2:
        score += 3
        reasons.append("title")

    attempt_claim = normalize_claim(attempt.claim)
    repo_claim = normalize_claim((validation.metadata.claim if validation.metadata else "")) or infer_claim_from_folder(validation.path.name)
    if attempt_claim and repo_claim and (attempt_claim == repo_claim or "both" in {attempt_claim, repo_claim}):
        score += 2
        reasons.append(f"claim {attempt.claim}")

    return score, reasons


def compare_with_woeginger(
    validations: List[StructureValidation],
    attempts: List[WoegingerAttempt],
    minimum_score: int = 9,
) -> Tuple[List[WoegingerMatch], List[StructureValidation]]:
    """Match live Woeginger entries to repository attempt directories."""
    available = set(range(len(validations)))
    matches: List[WoegingerMatch] = []

    for attempt in attempts:
        best_index: Optional[int] = None
        best_score = -1
        best_reasons: List[str] = []

        for index in available:
            score, reasons = score_woeginger_match(attempt, validations[index])
            if score > best_score:
                best_index = index
                best_score = score
                best_reasons = reasons

        if best_index is not None and best_score >= minimum_score:
            matches.append(WoegingerMatch(attempt, validations[best_index], best_score, best_reasons))
            available.remove(best_index)
        else:
            matches.append(WoegingerMatch(attempt, None, max(best_score, 0), best_reasons))

    unmatched_repo = [validations[index] for index in sorted(available)]
    return matches, unmatched_repo


def print_woeginger_report(matches: List[WoegingerMatch], unmatched_repo: List[StructureValidation], source_url: str):
    """Print comparison against Woeginger's live milestone list."""
    missing = [match for match in matches if match.validation is None]
    matched = [match for match in matches if match.validation is not None]

    print("=" * 80)
    print("WOEGINGER LIVE LIST COMPARISON")
    print("=" * 80)
    print(f"Source: {source_url}")
    print()
    print("SUMMARY")
    print("-" * 80)
    print(f"Woeginger entries parsed:      {len(matches)}")
    print(f"Matched repository attempts:   {len(matched)}")
    print(f"Missing repository attempts:   {len(missing)}")
    print(f"Unmatched repository attempts: {len(unmatched_repo)}")
    print()

    if missing:
        print("MISSING WOEGINGER ENTRIES")
        print("-" * 80)
        for match in missing:
            attempt = match.attempt
            label = f"#{attempt.entry_id} {attempt.claim}"
            author = attempt.author or "Unknown author"
            year = attempt.year or "Unknown year"
            print(f"  {label}: {author} ({year})")
            print(f"      {attempt.title}")
            print(f"      Suggested issue title: Formalize Woeginger entry #{attempt.entry_id}: {author}")
        print()

    if unmatched_repo:
        print("REPOSITORY ATTEMPTS NOT MATCHED TO WOEGINGER")
        print("-" * 80)
        for validation in unmatched_repo:
            print(f"  {validation.path.name}")
        print()

    print("=" * 80)


def serialize_validation(validation: StructureValidation) -> Dict:
    """Convert a structure validation to JSON-friendly data."""
    metadata = validation.metadata or AttemptMetadata()
    return {
        "path": str(validation.path),
        "name": validation.path.name,
        "metadata": {
            "author": metadata.author,
            "year": metadata.year,
            "claim": metadata.claim,
            "title": metadata.title,
            "source": metadata.source,
            "attempt_id": metadata.attempt_id,
        },
        "is_valid": validation.is_valid(),
        "is_complete": validation.is_complete(),
        "missing": validation.get_missing(),
        "warnings": validation.warnings,
        "has_lean": validation.has_lean(),
        "has_rocq": validation.has_rocq(),
    }


def serialize_woeginger_match(match: WoegingerMatch) -> Dict:
    """Convert a Woeginger comparison match to JSON-friendly data."""
    return {
        "entry": {
            "entry_id": match.attempt.entry_id,
            "claim": match.attempt.claim,
            "year": match.attempt.year,
            "author": match.attempt.author,
            "title": match.attempt.title,
            "summary": match.attempt.summary,
            "source_url": match.attempt.source_url,
            "links": list(match.attempt.links),
        },
        "matched_directory": match.validation.path.name if match.validation else None,
        "score": match.score,
        "reasons": match.reasons,
    }


def save_json_report(
    output_path: Path,
    validations: List[StructureValidation],
    woeginger_matches: Optional[List[WoegingerMatch]] = None,
    unmatched_repo: Optional[List[StructureValidation]] = None,
    woeginger_source_url: str = WOEGINGER_URL,
):
    """Save a machine-readable structure and Woeginger comparison report."""
    report = {
        "summary": {
            "attempts_scanned": len(validations),
            "valid": sum(1 for validation in validations if validation.is_valid()),
            "complete": sum(1 for validation in validations if validation.is_complete()),
            "invalid": sum(1 for validation in validations if not validation.is_valid()),
            "with_warnings": sum(1 for validation in validations if validation.warnings),
        },
        "attempts": [serialize_validation(validation) for validation in validations],
    }
    if woeginger_matches is not None:
        missing = [match for match in woeginger_matches if match.validation is None]
        report["woeginger"] = {
            "source": woeginger_source_url,
            "entries": len(woeginger_matches),
            "matched": len(woeginger_matches) - len(missing),
            "missing": len(missing),
            "unmatched_repository_attempts": len(unmatched_repo or []),
            "matches": [serialize_woeginger_match(match) for match in woeginger_matches],
            "unmatched_repository": [
                serialize_validation(validation)
                for validation in (unmatched_repo or [])
            ],
        }

    output_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"JSON report saved: {output_path}")


def parse_metadata_from_readme(readme_path: Path) -> Optional[AttemptMetadata]:
    """Extract metadata from README.md file."""
    if not readme_path.exists():
        return None

    try:
        content = readme_path.read_text(encoding='utf-8')
    except Exception:
        return None

    metadata = AttemptMetadata()

    # Extract title from the first H1. Keep the full heading; earlier versions used
    # a non-greedy regex that reduced many generated titles to a single letter.
    title_match = re.search(r'^#\s+(.+?)\s*$', content, re.MULTILINE)
    if title_match:
        metadata.title = title_match.group(1).strip()

    # Extract metadata fields
    patterns = {
        'author': r'\*\*Authors?\*\*[:\s]*(.+?)(?:\n|$)',
        'year': r'\*\*Year\*\*[:\s]*(\d{4})',
        'claim': r'\*\*Claim\*\*[:\s]*(.+?)(?:\n|$)',
        'source': r'\*\*Source\*\*[:\s]*\[?([^\]\n]+)',
        'attempt_id': r'\*\*Attempt ID\*\*[:\s]*(\d+)',
    }

    for fld, pattern in patterns.items():
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            setattr(metadata, fld, match.group(1).strip())

    # Try to extract claim from folder name if not found
    if not metadata.claim:
        folder_name = readme_path.parent.name.lower()
        if "peqnp" in folder_name:
            metadata.claim = "P = NP"
        elif "pneqnp" in folder_name:
            metadata.claim = "P ≠ NP"
        elif "unprovable" in folder_name:
            metadata.claim = "Unprovable"

    # Try to extract year from folder name if not found
    if not metadata.year:
        year_match = re.search(r'-(\d{4})-', readme_path.parent.name)
        if year_match:
            metadata.year = year_match.group(1)

    return metadata


def validate_attempt_structure(attempt_path: Path) -> StructureValidation:
    """Validate the structure of a single attempt directory."""
    result = StructureValidation(path=attempt_path)

    # Check main README
    readme_path = attempt_path / "README.md"
    result.has_readme = readme_path.exists()
    if result.has_readme:
        result.metadata = parse_metadata_from_readme(readme_path)

    # Check original paper reconstruction in either the preferred or legacy location.
    original_path = attempt_path / "original"
    result.has_original_dir = original_path.exists() and original_path.is_dir()
    result.has_original_readme = (original_path / "README.md").exists()
    result.has_original_md = (
        (attempt_path / "ORIGINAL.md").exists() or
        (original_path / "ORIGINAL.md").exists()
    )

    # Check for original paper file (PDF, HTML, etc.)
    original_extensions = ['.pdf', '.html', '.htm', '.txt', '.tex']
    for base_path in (attempt_path, original_path):
        if not base_path.exists() or not base_path.is_dir():
            continue
        for ext in original_extensions:
            original_file = base_path / f"ORIGINAL{ext}"
            if original_file.exists():
                result.has_original_file = True
                result.original_file_ext = ext
                break
        if result.has_original_file:
            break

    # Check proof/ directory
    proof_path = attempt_path / "proof"
    if proof_path.exists() and proof_path.is_dir():
        result.has_proof = True
        result.has_proof_readme = (proof_path / "README.md").exists()

        lean_path = proof_path / "lean"
        if lean_path.exists() and lean_path.is_dir():
            lean_files = list(lean_path.glob("*.lean"))
            if lean_files:
                result.has_proof_lean = True
                result.proof_lean_files = [f.name for f in lean_files]

        rocq_path = proof_path / "rocq"
        if rocq_path.exists() and rocq_path.is_dir():
            rocq_files = list(rocq_path.glob("*.v"))
            if rocq_files:
                result.has_proof_rocq = True
                result.proof_rocq_files = [f.name for f in rocq_files]

    # Check refutation/ directory
    refutation_path = attempt_path / "refutation"
    if refutation_path.exists() and refutation_path.is_dir():
        result.has_refutation = True
        result.has_refutation_readme = (refutation_path / "README.md").exists()

        lean_path = refutation_path / "lean"
        if lean_path.exists() and lean_path.is_dir():
            lean_files = list(lean_path.glob("*.lean"))
            if lean_files:
                result.has_refutation_lean = True
                result.refutation_lean_files = [f.name for f in lean_files]

        rocq_path = refutation_path / "rocq"
        if rocq_path.exists() and rocq_path.is_dir():
            rocq_files = list(rocq_path.glob("*.v"))
            if rocq_files:
                result.has_refutation_rocq = True
                result.refutation_rocq_files = [f.name for f in rocq_files]

    # Check for legacy structures (old formats) - These are WARNINGS, not errors
    # Legacy: lean/ or rocq/ at root level (should be in proof/ and refutation/)
    if (attempt_path / "lean").exists() and not result.has_proof:
        result.warnings.append("Legacy: lean/ at root level. Consider moving to proof/lean/ and refutation/lean/")
    if (attempt_path / "rocq").exists() and not result.has_proof:
        result.warnings.append("Legacy: rocq/ at root level. Consider moving to proof/rocq/ and refutation/rocq/")
    if (attempt_path / "coq").exists():
        result.warnings.append("Legacy: coq/ should be renamed to rocq/")
    if (attempt_path / "isabelle").exists():
        result.warnings.append("Deprecated: isabelle/ - Isabelle support has been sunset")

    return result


def find_attempts(base_path: Path) -> List[Path]:
    """Find all attempt directories."""
    attempts_path = base_path / "proofs" / "attempts"
    if not attempts_path.exists():
        return []

    attempts = []
    for item in attempts_path.iterdir():
        if item.is_dir() and not item.name.startswith('.'):
            # Skip known non-attempt items
            if item.name not in ["README.md", "__pycache__", "ATTEMPTS.md"]:
                attempts.append(item)

    return sorted(attempts)


def print_report(validations: List[StructureValidation]):
    """Print a human-readable report."""
    print("=" * 80)
    print("P vs NP ATTEMPTS - STRUCTURE VALIDATION REPORT")
    print("=" * 80)
    print()

    valid = [v for v in validations if v.is_valid()]
    complete = [v for v in validations if v.is_complete()]
    incomplete = [v for v in validations if not v.is_valid()]
    with_warnings = [v for v in validations if v.warnings]

    print("SUMMARY")
    print("-" * 80)
    print(f"Total attempts scanned:     {len(validations)}")
    print(f"Valid (has README.md):      {len(valid)}")
    print(f"Complete (all recommended): {len(complete)}")
    print(f"Invalid (missing README):   {len(incomplete)}")
    print(f"With warnings:              {len(with_warnings)}")
    print()

    if complete:
        print("COMPLETE ATTEMPTS (has README.md, original materials, proof/, refutation/)")
        print("-" * 80)
        for v in complete:
            status = []
            if v.has_lean():
                lean_count = len(v.proof_lean_files) + len(v.refutation_lean_files)
                status.append(f"Lean ({lean_count})")
            if v.has_rocq():
                rocq_count = len(v.proof_rocq_files) + len(v.refutation_rocq_files)
                status.append(f"Rocq ({rocq_count})")
            status_str = f" [{', '.join(status)}]" if status else ""
            print(f"  ✓ {v.path.name}{status_str}")
        print()

    partial = [v for v in valid if not v.is_complete()]
    if partial:
        print("PARTIAL ATTEMPTS (valid but missing some recommended files)")
        print("-" * 80)
        for v in partial:
            status = []
            if v.has_lean():
                status.append("Lean")
            if v.has_rocq():
                status.append("Rocq")
            status_str = f" [{', '.join(status)}]" if status else ""
            print(f"  ~ {v.path.name}{status_str}")
            for missing in v.get_missing():
                if "required" not in missing:
                    print(f"      Missing: {missing}")
        print()

    if incomplete:
        print("INVALID ATTEMPTS (missing required files)")
        print("-" * 80)
        for v in incomplete:
            print(f"  ✗ {v.path.name}")
            for missing in v.get_missing():
                if "required" in missing:
                    print(f"      Missing: {missing}")
        print()

    if with_warnings:
        print("WARNINGS")
        print("-" * 80)
        for v in with_warnings:
            print(f"  ⚠ {v.path.name}")
            for warning in v.warnings:
                print(f"      {warning}")
        print()

    print("=" * 80)
    print()
    print("Expected structure for each attempt:")
    print("""
attempt-name/
├── README.md              # Overview of the attempt (REQUIRED)
├── original/              # Original proof idea and paper reconstruction
│   ├── README.md          # Description of the original approach
│   ├── ORIGINAL.md        # Markdown reconstruction of paper
│   └── ORIGINAL.pdf       # Original paper PDF (or .html/.tex)
├── proof/                 # Forward proof formalization (recommended)
│   ├── README.md          # Explanation of proofs
│   ├── lean/              # Lean 4 formalizations
│   │   └── ProofAttempt.lean
│   └── rocq/              # Rocq formalizations
│       └── ProofAttempt.v
└── refutation/            # Refutation formalization (recommended)
    ├── README.md          # Explanation of failures
    ├── lean/              # Lean 4 formalizations
    │   └── Refutation.lean
    └── rocq/              # Rocq formalizations
        └── Refutation.v
""")
    print("Legacy attempts may also keep root-level ORIGINAL.* files; the checker accepts either layout.")


def generate_markdown_list(validations: List[StructureValidation], output_path: Optional[Path] = None) -> str:
    """Generate a markdown list of all attempts."""
    lines = []
    lines.append("# P vs NP Proof Attempts")
    lines.append("")
    lines.append("This document provides a comparison of all documented P vs NP proof attempts in this repository.")
    lines.append("")
    lines.append("**Legend:**")
    lines.append("- ✓ = Claims P = NP")
    lines.append("- ✗ = Claims P ≠ NP")
    lines.append("- ? = Claims unprovable")
    lines.append("- 📄 = Has ORIGINAL.md (root or original/)")
    lines.append("- 📎 = Has original paper file (PDF/HTML/TXT/TEX, root or original/)")
    lines.append("- 🔷 = Has Lean formalization")
    lines.append("- 🔶 = Has Rocq formalization")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Sort alphabetically by folder name to reduce probability of merge conflicts
    sorted_validations = sorted(
        validations,
        key=lambda v: v.path.name.lower()
    )

    lines.append("| Claim | Author | Year | Title | Docs | Formal |")
    lines.append("|:-----:|--------|------|-------|:----:|:------:|")

    for v in sorted_validations:
        claim_emoji = v.get_claim_emoji()
        author = v.metadata.author if v.metadata and v.metadata.author else extract_author_from_folder(v.path.name)
        year = v.metadata.year if v.metadata and v.metadata.year else extract_year_from_folder(v.path.name)
        title = v.metadata.title if v.metadata and v.metadata.title else format_folder_name(v.path.name)

        # Docs column
        docs = []
        if v.has_original_md:
            docs.append("📄")
        if v.has_original_file:
            docs.append("📎")
        docs_str = " ".join(docs) if docs else "-"

        # Formal column
        formal = []
        if v.has_lean():
            formal.append("🔷")
        if v.has_rocq():
            formal.append("🔶")
        formal_str = " ".join(formal) if formal else "-"

        # Create link to attempt folder
        folder_link = f"[{title}]({v.path.name}/)"

        lines.append(f"| {claim_emoji} | {author} | {year} | {folder_link} | {docs_str} | {formal_str} |")

    lines.append("")

    lines.append("---")
    lines.append("")
    lines.append("*This file is auto-generated by `scripts/check_attempt_structure.py --generate-list`*")

    content = "\n".join(lines) + "\n"

    if output_path:
        output_path.write_text(content, encoding='utf-8')
        print(f"Generated markdown list: {output_path}")

    return content


def extract_author_from_folder(folder_name: str) -> str:
    """Extract author name from folder name like 'john-doe-2006-peqnp'."""
    parts = folder_name.split('-')
    # Remove year and claim type
    author_parts = []
    for part in parts:
        if part.isdigit() and len(part) == 4:
            break
        if part.lower() in ['peqnp', 'pneqnp', 'unprovable']:
            continue
        author_parts.append(part.capitalize())
    return " ".join(author_parts)


def extract_year_from_folder(folder_name: str) -> str:
    """Extract year from folder name."""
    match = re.search(r'-(\d{4})-', folder_name)
    return match.group(1) if match else "Unknown"


def format_folder_name(folder_name: str) -> str:
    """Format folder name as a readable title."""
    # Remove claim suffix
    name = re.sub(r'-(peqnp|pneqnp|unprovable)$', '', folder_name, flags=re.IGNORECASE)
    # Replace hyphens with spaces and title case
    parts = name.split('-')
    return " ".join(p.capitalize() for p in parts)


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Check P vs NP attempt directory structure and generate reports'
    )
    parser.add_argument(
        '--path',
        type=Path,
        help='Path to a specific attempt to validate (default: scan all attempts)'
    )
    parser.add_argument(
        '--base-dir',
        type=Path,
        default=Path.cwd(),
        help='Base directory of the repository (default: current directory)'
    )
    parser.add_argument(
        '--generate-list',
        action='store_true',
        help='Generate a markdown list of all attempts'
    )
    parser.add_argument(
        '--output',
        type=Path,
        help='Output file for the markdown list (default: stdout)'
    )
    parser.add_argument(
        '--json',
        type=Path,
        help='Write a machine-readable validation report to this path'
    )
    parser.add_argument(
        '--offline',
        action='store_true',
        help="Skip fetching Woeginger's live milestone list"
    )
    parser.add_argument(
        '--woeginger-url',
        default=WOEGINGER_URL,
        help=f"Woeginger milestone URL (default: {WOEGINGER_URL})"
    )
    parser.add_argument(
        '--minimum-match-score',
        type=int,
        default=9,
        help='Minimum fuzzy score required to match a Woeginger entry (default: 9)'
    )
    parser.add_argument(
        '--require-woeginger',
        action='store_true',
        help='Exit with an error if the live Woeginger list cannot be fetched or parsed'
    )
    parser.add_argument(
        '--fail-on-missing-woeginger',
        action='store_true',
        help='Exit with an error if any live Woeginger entry is not matched to a repository attempt'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Only output errors and the generated list'
    )

    args = parser.parse_args()

    if args.path:
        # Validate a single attempt
        if not args.path.exists():
            print(f"Error: Path does not exist: {args.path}")
            sys.exit(1)
        validations = [validate_attempt_structure(args.path)]
    else:
        # Scan all attempts
        attempts = find_attempts(args.base_dir)
        if not attempts:
            print("No attempts found in proofs/attempts/")
            sys.exit(1)
        validations = [validate_attempt_structure(attempt) for attempt in attempts]

    woeginger_matches: Optional[List[WoegingerMatch]] = None
    unmatched_repo: Optional[List[StructureValidation]] = None
    if not args.path and not args.offline:
        try:
            woeginger_attempts = fetch_woeginger_attempts(args.woeginger_url)
            woeginger_matches, unmatched_repo = compare_with_woeginger(
                validations,
                woeginger_attempts,
                minimum_score=args.minimum_match_score,
            )
        except (HTTPError, URLError, TimeoutError, OSError, ValueError) as exc:
            message = f"Warning: could not compare against Woeginger live list: {exc}"
            if args.require_woeginger:
                print(message, file=sys.stderr)
                sys.exit(1)
            if not args.quiet:
                print(message, file=sys.stderr)

    if args.generate_list:
        content = generate_markdown_list(validations, args.output)
        if not args.output:
            print(content)
    else:
        if not args.quiet:
            print_report(validations)
            if woeginger_matches is not None:
                print_woeginger_report(woeginger_matches, unmatched_repo or [], args.woeginger_url)

    if args.json:
        save_json_report(
            args.json,
            validations,
            woeginger_matches,
            unmatched_repo,
            woeginger_source_url=args.woeginger_url,
        )

    # Exit with error if any attempts are invalid (missing README)
    invalid = [v for v in validations if not v.is_valid()]
    if invalid:
        print(f"\n{len(invalid)} attempt(s) are invalid (missing README.md).")
        sys.exit(1)

    if args.fail_on_missing_woeginger and woeginger_matches is not None:
        missing = [match for match in woeginger_matches if match.validation is None]
        if missing:
            print(f"\n{len(missing)} Woeginger entries are missing repository attempts.")
            sys.exit(1)


if __name__ == '__main__':
    main()
