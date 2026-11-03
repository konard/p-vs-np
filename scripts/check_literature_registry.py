#!/usr/bin/env python3
"""Validate, query and render the literature registry.

The registry is literature/registry.json. It records external sources: papers,
AI-lab releases, formal proof artifacts, surveys, critiques and claimed P vs NP
proofs. A registry entry never changes a proof status in this repository; see
literature/README.md.

Uses the Python 3 standard library only and makes no network calls.

    python3 -I scripts/check_literature_registry.py              # validate
    python3 -I scripts/check_literature_registry.py --stats
    python3 -I scripts/check_literature_registry.py --tag eth --since 2026
    python3 -I scripts/check_literature_registry.py --render     # write REGISTRY.md
    python3 -I scripts/check_literature_registry.py --check-render
    python3 -I scripts/check_literature_registry.py --check-readme

Validation always includes the documentation checks of --check-readme unless
--readme none is given. Exit status 0 means the registry is valid (and, for
--check-render, that REGISTRY.md is current). Exit status 1 means validation errors or a stale
rendering; each problem is printed on stderr. Exit status 2 means bad arguments.
"""

import argparse
import datetime
import json
import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "literature" / "registry.json"
RENDERED = ROOT / "literature" / "REGISTRY.md"
README = ROOT / "literature" / "README.md"
CLAIMED_PROOFS = ROOT / "literature" / "CLAIMED_PROOFS_2017_2026.md"
PROOF_STATUS = ROOT / "scripts" / "proof_status.json"
ATTEMPTS = ROOT / "proofs" / "attempts"

SCHEMA_VERSION = "1"

ARTIFACT_CLASSES = (
    "paper", "machine-checked-proof", "statement-only-benchmark", "generated-candidate", "code",
    "dataset", "model", "survey", "blog", "critique", "formalization-library", "tool",
)
RESULT_TYPES = (
    "peer-reviewed-theorem", "preprint-theorem", "ai-lab-lean-checked", "ai-lab-manuscript-only",
    "barrier-result", "formalization-artifact", "survey", "critique", "claimed-p-vs-np-proof",
)
STATUSES = (
    "peer-reviewed", "under-expert-review", "unreviewed-preprint", "withdrawn", "refuted",
    "formally-checked", "unknown",
)
# Claim-status labels from issue #635, weakest first.
CLAIM_STATUS_LOCAL = (
    "discovered", "statement-only", "candidate", "upstream-checked", "locally-replayed",
    "conditional-bridge", "locally-certified",
)
VERIFIED = ("yes", "partial", "no")
CLAIM_DIRECTIONS = ("peqnp", "pneqnp", "unprovable", "undecidable", "other", "both", "unknown")

# The tag vocabulary. literature/README.md must list exactly these tags.
TAGS = {
    "eth": "Exponential Time Hypothesis, its variants and refutation claims",
    "seth": "Strong Exponential Time Hypothesis",
    "sat-algorithms": "algorithms and exact bounds for SAT and k-SAT",
    "fine-grained": "fine-grained complexity (3SUM, APSP, exponential-time bounds)",
    "counting": "counting problems (#SAT, permanent)",
    "circuit-lower-bounds": "Boolean or quantum circuit lower bounds",
    "algebraic-complexity": "algebraic circuits, VP vs VNP, permanent vs determinant",
    "matrix-multiplication": "the matrix multiplication exponent",
    "gct": "geometric complexity theory",
    "proof-complexity": "proof systems and their lower bounds",
    "meta-complexity": "MCSP, learning and Kolmogorov-style meta-complexity",
    "kolmogorov": "time-bounded Kolmogorov complexity",
    "range-avoidance": "range avoidance and explicit constructions",
    "williams": "the Williams algorithms-to-lower-bounds route (Idea 41)",
    "derandomization": "derandomization of time or space",
    "space-time": "time-space simulations and space classes",
    "catalytic": "catalytic computation",
    "pcp": "PCPs, label cover and unique games",
    "hardness-of-approximation": "NP-hardness of approximation",
    "extended-formulations": "LP and SDP extended formulations",
    "reductions": "reductions and completeness results",
    "quantum": "quantum models",
    "barriers": "relativization, natural proofs, algebrization and other barriers",
    "independence": "claims about unprovability or undecidability",
    "formalization": "machine-checked artifacts and formal libraries",
    "lean": "Lean artifacts",
    "rocq": "Rocq (Coq) artifacts",
    "isabelle": "Isabelle artifacts",
    "cook-levin": "Cook-Levin theorem and SAT hardness (SATHard, #624)",
    "model-fidelity": "machine-model, encoding or cost-model mismatch risk",
    "tool": "verification or registry tooling",
    "ai-lab": "results or releases from AI labs",
    "expert-commentary": "blogs, statements and expert commentary",
    "survey": "surveys, textbooks and canonical references",
    "critique": "published critiques of claimed proofs",
    "claimed-proof": "claimed resolutions of P vs NP and related separations",
    "peqnp": "the claim is P = NP",
    "pneqnp": "the claim is P != NP",
}

REQUIRED = {
    "id": str, "title": str, "authors": list, "year": int, "date": str, "venue": str, "urls": list,
    "artifact_class": str, "result_type": str, "claim": str, "status": str, "claim_status_local": str,
    "relevance": str, "caveats": str, "tags": list, "verified": str, "added": str,
}
OPTIONAL = {
    "formal": dict, "license": str, "size_note": str, "local_obligation": str,
    "common_errors_family": int, "common_errors_secondary": list, "documented_responses": list,
    "notes": str, "parent": str, "attempt_slug": str, "claim_direction": str, "existing_attempt": str,
    "source_row": int, "local_certificate": str,
}
FORMAL_KEYS = ("prover", "model", "declaration", "file", "revision", "kernel_checks", "axioms")
# Labels that claim a kernel check of a named declaration, and the formal keys they must pin.
FORMAL_GATED = ("upstream-checked", "locally-replayed", "conditional-bridge", "locally-certified")
PINNED_FORMAL_KEYS = ("model", "declaration", "file", "revision")
# Statuses that assert something about the source and so must cite where it was read.
SOURCED_STATUSES = ("withdrawn", "refuted", "formally-checked", "under-expert-review")
# Venue parts that are not peer-reviewed publication venues (lowercase prefixes).
PREPRINT_MARKERS = (
    "arxiv", "eccc", "zenodo", "hal ", "hal-", "preprints.org", "engrxiv", "github", "ssrn", "vixra",
    "researchgate", "author's web page", "openai/math", "anthropics/",
)

ID_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
DATE_RE = re.compile(r"^(\d{4})(?:-(\d{2})(?:-(\d{2}))?)?$")
URL_RE = re.compile(r"^https?://[^\s]+$")
ARXIV_URL_RE = re.compile(
    r"^https?://(?:www\.|export\.)?arxiv\.org/(?:abs|pdf)/"
    r"([a-z][a-z.-]*/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?(?:\.pdf)?/?$", re.I)
DOI_URL_RE = re.compile(r"^https?://(?:dx\.)?doi\.org/(10\.\S+?)/?$", re.I)
# A source citation in notes: a URL, an arXiv id, a DOI, a commit hash or a README.
SOURCE_RE = re.compile(
    r"https?://|\barXiv:\s*\S|\bdoi[: ]\s*10\.|\b(?=[0-9a-f]*[a-f])(?=[0-9a-f]*[0-9])[0-9a-f]{7,40}\b|README",
    re.I)
BACKTICK_RE = re.compile(r"`([^`\n]+)`")
YEAR_SEGMENT_RE = re.compile(r"^(?:19|20)\d\d$")

GROUP_ORDER = (
    ("ai-lab-lean-checked", "AI-lab results with Lean artifacts"),
    ("ai-lab-manuscript-only", "AI-lab manuscripts without a checked formal statement"),
    ("peer-reviewed-theorem", "Peer-reviewed theorems"),
    ("preprint-theorem", "Preprint theorems"),
    ("barrier-result", "Barrier results"),
    ("formalization-artifact", "Formalization artifacts and tools"),
    ("survey", "Surveys, references and commentary"),
    ("critique", "Critiques of claimed proofs"),
)
CLAIMED = "claimed-p-vs-np-proof"


# --------------------------------------------------------------------------- validation

def valid_date(text):
    """Return True for YYYY, YYYY-MM or YYYY-MM-DD with a real month and day."""
    match = DATE_RE.match(text) if isinstance(text, str) else None
    if not match:
        return False
    year, month, day = match.groups()
    try:
        datetime.date(int(year), int(month or 1), int(day or 1))
    except ValueError:
        return False
    return True


def paper_key(url):
    """Return 'arxiv:<id>' or 'doi:<doi>' for arXiv and doi.org URLs, else None.

    arXiv abs and pdf pages, version suffixes, '.pdf', http or https and the
    www. or export. hosts all map to the same key. DOIs are case-insensitive.
    """
    if not isinstance(url, str):
        return None
    url = url.split("#", 1)[0].split("?", 1)[0]
    match = ARXIV_URL_RE.match(url)
    if match:
        return "arxiv:" + match.group(1).lower()
    match = DOI_URL_RE.match(url)
    if match:
        return "doi:" + match.group(1).lower()
    return None


def normalize_url(url):
    """Normalize a URL for duplicate detection.

    arXiv and DOI URLs reduce to their paper key. Other URLs lose the scheme,
    the case of the host, a leading www., a trailing slash and the fragment.
    """
    key = paper_key(url)
    if key:
        return key
    url = url.split("#", 1)[0]
    match = re.match(r"^https?://([^/]+)(.*)$", url)
    if not match:
        return url
    host, rest = match.groups()
    host = host.lower()
    if host.startswith("www."):
        host = host[4:]
    return host + rest.rstrip("/")


def load_certified(path=None):
    """Return the set of theorem names in scripts/proof_status.json."""
    with open(path or PROOF_STATUS, encoding="utf-8") as handle:
        status = json.load(handle)
    names = set()
    for rows in status.values():
        if isinstance(rows, list):
            names.update(row["theorem"] for row in rows if isinstance(row, dict) and isinstance(row.get("theorem"), str))
    return names


def validate(data, certified=None):
    """Return a list of error strings. An empty list means the registry is valid.

    certified is the set of certified theorem names; when None it is read from
    scripts/proof_status.json, and only if some entry is locally-certified.
    """
    errors = []
    if not isinstance(data, dict):
        return ["top level: expected a JSON object"]
    if data.get("schema_version") != SCHEMA_VERSION:
        errors.append("top level: schema_version must be {!r}".format(SCHEMA_VERSION))
    if not (isinstance(data.get("updated"), str) and len(data["updated"]) == 10 and valid_date(data["updated"])):
        errors.append("top level: updated must be a YYYY-MM-DD date")
    entries = data.get("entries")
    if not isinstance(entries, list):
        errors.append("top level: entries must be a list")
        return errors
    extra = set(data) - {"schema_version", "updated", "entries"}
    if extra:
        errors.append("top level: unknown keys {}".format(sorted(extra)))

    ids = Counter(e.get("id") for e in entries if isinstance(e, dict))
    if certified is None and any(isinstance(e, dict) and e.get("claim_status_local") == "locally-certified"
                                 for e in entries):
        try:
            certified = load_certified()
        except (OSError, ValueError, KeyError) as exc:
            errors.append("cannot read {}: {}".format(PROOF_STATUS, exc))
            certified = set()
    updated = data.get("updated") if isinstance(data.get("updated"), str) else None
    canonical = {}
    for index, entry in enumerate(entries):
        errors.extend(validate_entry(index, entry, ids, certified or set(), updated))
        if isinstance(entry, dict) and isinstance(entry.get("urls"), list) and entry["urls"] \
                and isinstance(entry["urls"][0], str):
            key = normalize_url(entry["urls"][0])
            if key in canonical:
                errors.append("{}: canonical URL {} duplicates entry {}".format(
                    label(index, entry), entry["urls"][0], canonical[key]))
            else:
                canonical[key] = entry.get("id")
    for entry_id, count in sorted((k, v) for k, v in ids.items() if isinstance(k, str)):
        if count > 1:
            errors.append("duplicate id {!r} ({} entries)".format(entry_id, count))
    errors.extend(cross_entry_errors([e for e in entries if isinstance(e, dict)]))
    return errors


def cross_entry_errors(entries):
    """Paper keys, attempt slugs and source rows that two entries share."""
    errors = []
    parents = {e.get("id"): e.get("parent") for e in entries}

    def related(a, b):
        return parents.get(a) == b or parents.get(b) == a

    papers = {}
    for entry in entries:
        urls = entry.get("urls") if isinstance(entry.get("urls"), list) else []
        for key in sorted({paper_key(u) for u in urls} - {None}):
            other = papers.get(key)
            if other is None:
                papers[key] = entry.get("id")
            elif other != entry.get("id") and not related(other, entry.get("id")):
                errors.append("entry {}: paper {} is also listed by entry {} (link them with parent or merge)".format(
                    entry.get("id"), key, other))
    for field in ("attempt_slug", "source_row"):
        seen = {}
        for entry in entries:
            if field in entry:
                value = entry[field]
                if value in seen:
                    errors.append("entry {}: {} {!r} is also used by entry {}".format(
                        entry.get("id"), field, value, seen[value]))
                else:
                    seen[value] = entry.get("id")
    return errors


def is_placeholder(value):
    """True for values that record nothing: empty, n/a, none, unknown..., not applicable..., not recorded."""
    if not isinstance(value, str):
        return True
    text = value.strip().lower()
    return (not text or text in ("n/a", "none", "-", "?", "tbd")
            or text.startswith("unknown") or text.startswith("not applicable") or "not recorded" in text)


def has_publication_venue(venue):
    """True if some ';'-separated part of venue is not a preprint server or repository."""
    return any(part.strip() and not part.strip().lower().startswith(PREPRINT_MARKERS) for part in venue.split(";"))


def label(index, entry):
    entry_id = entry.get("id") if isinstance(entry, dict) else None
    return "entry {} ({})".format(index, entry_id if isinstance(entry_id, str) else "no id")


def validate_entry(index, entry, ids, certified=frozenset(), updated=None):
    where = label(index, entry)
    if not isinstance(entry, dict):
        return ["{}: expected an object".format(where)]
    errors = []

    def err(message):
        errors.append("{}: {}".format(where, message))

    for field, kind in REQUIRED.items():
        if field not in entry:
            err("missing required field {!r}".format(field))
        elif not isinstance(entry[field], kind) or (kind is int and isinstance(entry[field], bool)):
            err("field {!r} must be {}".format(field, kind.__name__))
        elif kind is str and not entry[field].strip():
            err("field {!r} must not be empty".format(field))
    for field, value in entry.items():
        if field in REQUIRED:
            continue
        if field not in OPTIONAL:
            err("unknown field {!r}".format(field))
        elif not isinstance(value, OPTIONAL[field]) or (OPTIONAL[field] is int and isinstance(value, bool)):
            err("field {!r} must be {}".format(field, OPTIONAL[field].__name__))
    if errors:
        return errors

    if not ID_RE.match(entry["id"]):
        err("id must be kebab-case (lowercase letters, digits, single hyphens)")
    if not entry["authors"] or not all(isinstance(a, str) and a.strip() for a in entry["authors"]):
        err("authors must be a non-empty list of names")
    if not valid_date(entry["date"]):
        err("date {!r} must be YYYY, YYYY-MM or YYYY-MM-DD".format(entry["date"]))
    elif not entry["date"].startswith(str(entry["year"])):
        err("date {!r} does not match year {}".format(entry["date"], entry["year"]))
    if not (len(entry["added"]) == 10 and valid_date(entry["added"])):
        err("added must be a YYYY-MM-DD date")
    else:
        if valid_date(entry["date"]) and entry["added"][:len(entry["date"])] < entry["date"]:
            err("date {!r} is later than added {!r}".format(entry["date"], entry["added"]))
        if updated and entry["added"] > updated:
            err("added {!r} is later than the registry's updated {!r}".format(entry["added"], updated))
    if not entry["urls"]:
        err("urls must contain at least the canonical primary URL")
    seen = set()
    for url in entry["urls"]:
        if not isinstance(url, str) or not URL_RE.match(url):
            err("bad URL {!r}".format(url))
        elif normalize_url(url) in seen:
            err("URL listed twice: {}".format(url))
        else:
            seen.add(normalize_url(url))

    for field, allowed in (("artifact_class", ARTIFACT_CLASSES), ("result_type", RESULT_TYPES),
                           ("status", STATUSES), ("claim_status_local", CLAIM_STATUS_LOCAL),
                           ("verified", VERIFIED)):
        if entry[field] not in allowed:
            err("{} {!r} is not one of {}".format(field, entry[field], ", ".join(allowed)))
    if "claim_direction" in entry and entry["claim_direction"] not in CLAIM_DIRECTIONS:
        err("claim_direction {!r} is not one of {}".format(entry["claim_direction"], ", ".join(CLAIM_DIRECTIONS)))
    direction = entry.get("claim_direction")
    has_peq, has_pneq = "peqnp" in entry["tags"], "pneqnp" in entry["tags"]
    expected = {(True, True): ("both",), (True, False): ("peqnp", "both"), (False, True): ("pneqnp", "both")}
    if (has_peq or has_pneq) and direction not in expected[(has_peq, has_pneq)]:
        err("claim_direction {!r} disagrees with the peqnp/pneqnp tags (expected {})".format(
            direction, " or ".join(expected[(has_peq, has_pneq)])))
    needed = {"peqnp": {"peqnp"}, "pneqnp": {"pneqnp"}, "both": {"peqnp", "pneqnp"}}.get(direction, set())
    if needed - set(entry["tags"]):
        err("claim_direction {!r} needs the tag(s) {}".format(direction, ", ".join(sorted(needed - set(entry["tags"])))))

    if not entry["tags"]:
        err("tags must not be empty")
    if len(set(map(str, entry["tags"]))) != len(entry["tags"]):
        err("tags contain duplicates")
    for tag in entry["tags"]:
        if tag not in TAGS:
            err("unknown tag {!r} (vocabulary in scripts/check_literature_registry.py and literature/README.md)".format(tag))

    for field in ("common_errors_family",):
        if field in entry and not 1 <= entry[field] <= 20:
            err("common_errors_family must be between 1 and 20")
    for family in entry.get("common_errors_secondary", []):
        if not isinstance(family, int) or isinstance(family, bool) or not 1 <= family <= 20:
            err("common_errors_secondary must list families between 1 and 20")
    for response in entry.get("documented_responses", []):
        if not (isinstance(response, dict) and set(response) == {"url", "note"}
                and isinstance(response["url"], str) and URL_RE.match(response["url"])
                and isinstance(response["note"], str) and response["note"].strip()):
            err("documented_responses items must be objects with a URL and a non-empty note")
    if "attempt_slug" in entry and not ID_RE.match(entry["attempt_slug"]):
        err("attempt_slug must be kebab-case")
    if "parent" in entry:
        if entry["parent"] == entry["id"]:
            err("parent must not be the entry itself")
        elif ids.get(entry["parent"], 0) == 0:
            err("parent {!r} does not name an entry".format(entry["parent"]))

    formal = entry.get("formal")
    if formal is not None:
        unknown = set(formal) - set(FORMAL_KEYS)
        if unknown:
            err("formal has unknown keys {}".format(sorted(unknown)))
        for key in ("prover", "model", "declaration", "file", "revision"):
            if key in formal and not isinstance(formal[key], str):
                err("formal.{} must be a string".format(key))
        if "prover" not in formal or "model" not in formal:
            err("formal must name at least prover and model ('unknown' is allowed)")
        if "kernel_checks" in formal and not (isinstance(formal["kernel_checks"], list)
                                               and all(isinstance(k, str) for k in formal["kernel_checks"])):
            err("formal.kernel_checks must be a list of strings")
        if "axioms" in formal and not (isinstance(formal["axioms"], str) or (
                isinstance(formal["axioms"], list) and all(isinstance(a, str) for a in formal["axioms"]))):
            err("formal.axioms must be a string or a list of strings")

    # Trust gates. A registry entry can never certify anything by itself.
    local = entry["claim_status_local"]
    if local == "locally-certified":
        if "local_certificate" not in entry:
            err("locally-certified needs a local_certificate naming the certified result in scripts/proof_status.json")
        elif entry["local_certificate"] not in certified:
            err("local_certificate {!r} is not a theorem in scripts/proof_status.json".format(entry["local_certificate"]))
    if local in FORMAL_GATED:
        if formal is None:
            err("claim_status_local {!r} needs a formal object".format(local))
        else:
            for key in PINNED_FORMAL_KEYS:
                if is_placeholder(formal.get(key)):
                    err("claim_status_local {!r} needs formal.{} to be recorded (got {!r})".format(
                        local, key, formal.get(key)))
    if entry["status"] == "formally-checked" and formal is None:
        err("status 'formally-checked' needs a formal object")
    if entry["result_type"] == "ai-lab-lean-checked" and formal is None:
        err("result_type 'ai-lab-lean-checked' needs a formal object")
    if entry["status"] == "peer-reviewed" and not has_publication_venue(entry["venue"]):
        err("status 'peer-reviewed' needs a publication venue, not only a preprint server or repository")
    if entry["result_type"] == "peer-reviewed-theorem" and entry["status"] != "peer-reviewed":
        err("result_type 'peer-reviewed-theorem' needs status 'peer-reviewed'")
    if entry["status"] in SOURCED_STATUSES and not entry.get("documented_responses") \
            and not SOURCE_RE.search(entry.get("notes", "")):
        err("status {!r} needs documented_responses or notes that cite the source (URL, arXiv id, DOI, "
            "commit or README)".format(entry["status"]))
    if entry["result_type"] == CLAIMED:
        if "claimed-proof" not in entry["tags"]:
            err("claimed proofs must carry the 'claimed-proof' tag")
        for field in ("attempt_slug", "claim_direction", "common_errors_family"):
            if field not in entry:
                err("claimed proofs need {!r}".format(field))
        if entry["claim_status_local"] not in ("discovered", "statement-only", "candidate"):
            err("claimed proofs stay at discovered, statement-only or candidate in this registry")
    return errors


def readme_tags(text):
    """Return the tags listed between the tag markers of literature/README.md."""
    match = re.search(r"<!-- tags:start -->(.*?)<!-- tags:end -->", text, re.S)
    if not match:
        return None
    return re.findall(r"^\|\s*`([a-z0-9-]+)`\s*\|", match.group(1), re.M)


def validate_readme(path):
    if not path.exists():
        return ["{}: guide not found (pass --readme none to skip the documentation checks)".format(path)]
    tags = readme_tags(path.read_text(encoding="utf-8"))
    if tags is None:
        return ["{}: missing <!-- tags:start --> ... <!-- tags:end --> section".format(path)]
    errors = []
    if len(tags) != len(set(tags)):
        errors.append("{}: tag table lists a tag twice".format(path))
    missing = sorted(set(TAGS) - set(tags))
    extra = sorted(set(tags) - set(TAGS))
    if missing:
        errors.append("{}: tag table lacks {}".format(path, ", ".join(missing)))
    if extra:
        errors.append("{}: tag table has tags the checker does not know: {}".format(path, ", ".join(extra)))
    return errors


def known_gaps_unverified(text):
    """Return the backticked ids of the 'Entries with `verified: no`' bullet under '## Known gaps', or None."""
    match = re.search(r"^## Known gaps\s*$(.*?)(?=^## |\Z)", text, re.M | re.S)
    if not match:
        return None
    bullet = re.search(r"^- Entries with `verified: no`(.*?)(?=^- |^\s*$|\Z)", match.group(1), re.M | re.S)
    if not bullet:
        return None
    return {token for token in BACKTICK_RE.findall(bullet.group(1)) if ID_RE.match(token)}


def entry_like_tokens(text):
    """Backticked kebab-case tokens with a year segment: the tokens that look like registry ids."""
    tokens = set()
    for token in BACKTICK_RE.findall(text):
        parts = token.split("-")
        if ID_RE.match(token) and len(parts) > 1 and re.search(r"[a-z]", token) \
                and any(YEAR_SEGMENT_RE.match(part) for part in parts):
            tokens.add(token)
    return tokens


def validate_docs(data, readme, claimed=None, attempts=None):
    """Check literature/README.md and the claimed-proof backlog against the registry.

    The tag table must match TAGS; the 'Known gaps' list of `verified: no` entries
    must equal the registry's; every backticked id-like token (kebab-case with a
    year segment) must be a registry id, an attempt_slug or a proofs/attempts folder.
    """
    errors = validate_readme(readme)
    if not readme.exists():
        return errors
    entries = [e for e in data.get("entries", []) if isinstance(e, dict)]
    ids = {e.get("id") for e in entries}
    known = ids | {e.get("attempt_slug") for e in entries}
    if attempts is not None and attempts.is_dir():
        known |= {p.name for p in attempts.iterdir() if p.is_dir()}
    text = readme.read_text(encoding="utf-8")
    listed = known_gaps_unverified(text)
    if listed is None:
        errors.append("{}: missing the 'Entries with `verified: no`' bullet under '## Known gaps'".format(readme))
    else:
        unverified = {e.get("id") for e in entries if e.get("verified") == "no"}
        if listed - unverified:
            errors.append("{}: Known gaps lists {} as verified: no, but the registry does not".format(
                readme, ", ".join(sorted(listed - unverified))))
        if unverified - listed:
            errors.append("{}: Known gaps omits verified: no entries {}".format(
                readme, ", ".join(sorted(unverified - listed))))
    documents = [readme] + ([claimed] if claimed is not None else [])
    for path in documents:
        if not path.exists():
            errors.append("{}: not found".format(path))
            continue
        for token in sorted(entry_like_tokens(path.read_text(encoding="utf-8")) - known):
            errors.append("{}: `{}` is not a registry id, attempt_slug or proofs/attempts folder".format(path, token))
    return errors


def load(path):
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)


# --------------------------------------------------------------------------- query

def date_key(entry):
    """Sortable form of a date of any supported precision; missing parts sort first."""
    parts = entry["date"].split("-")
    while len(parts) < 3:
        parts.append("00")
    return "-".join(parts)


def ordered(entries):
    """Date descending, then id ascending. Deterministic for equal dates."""
    by_id = sorted(entries, key=lambda e: e["id"])
    return sorted(by_id, key=date_key, reverse=True)


def query(entries, tag=None, kind=None, status=None, text=None, since=None):
    result = []
    for entry in entries:
        if tag and tag not in entry["tags"]:
            continue
        if kind and kind not in (entry["result_type"], entry["artifact_class"]):
            continue
        if status and status not in (entry["status"], entry["claim_status_local"]):
            continue
        if text and text.lower() not in (entry["title"] + "\n" + entry["claim"]).lower():
            continue
        if since is not None and entry["year"] < since:
            continue
        result.append(entry)
    return ordered(result)


def format_row(entry):
    return "{:<10}  {:<52}  {:<19}  {}".format(entry["date"], entry["id"], entry["status"], entry["title"])


# --------------------------------------------------------------------------- render

def cell(text):
    return " ".join(str(text).split()).replace("|", "\\|")


def link(entry):
    return "[{}]({})".format(cell(entry["title"]).replace("[", "\\[").replace("]", "\\]"), entry["urls"][0])


def render(data):
    entries = data["entries"]
    certified = sum(e["claim_status_local"] == "locally-certified" for e in entries)
    lines = [
        "<!-- Generated by scripts/check_literature_registry.py --render from literature/registry.json. -->",
        "<!-- Do not edit by hand: edit registry.json and run the renderer. -->",
        "",
        "# Literature registry (generated)",
        "",
        "This file is generated from [registry.json](registry.json) and must not be edited by hand.",
        "The schema, tag vocabulary and intake rules are in [README.md](README.md).",
        "Registry data updated {}. {} entries.".format(data["updated"], len(entries)),
        "",
        "Listing a source here changes no proof status in this repository. "
        "`status` is the source's own publication or review status; "
        "`claim_status_local` is the issue #635 label{}.".format(
            ", and no entry is locally certified" if not certified
            else "; {} entries are locally certified".format(certified)),
        "",
        "## Contents",
        "",
    ]
    groups = [(key, title) for key, title in GROUP_ORDER if any(e["result_type"] == key for e in entries)]
    claimed = [e for e in entries if e["result_type"] == CLAIMED]
    for key, title in groups:
        lines.append("- [{}](#{}) ({})".format(title, anchor(title), sum(e["result_type"] == key for e in entries)))
    if claimed:
        lines.append("- [Claimed P vs NP proofs 2017-2026](#claimed-p-vs-np-proofs-2017-2026) ({})".format(
            sum(2017 <= e["year"] <= 2026 for e in claimed)))
    lines.append("")
    for key, title in groups:
        lines += ["## " + title, "", "| id | year | title | status | relevance |", "| --- | --- | --- | --- | --- |"]
        for entry in ordered([e for e in entries if e["result_type"] == key]):
            lines.append("| `{}` | {} | {} | {} | {} |".format(
                entry["id"], entry["year"], link(entry), entry["status"], cell(entry["relevance"])))
        lines.append("")
    if claimed:
        inside = [e for e in claimed if 2017 <= e["year"] <= 2026]
        outside = [e for e in claimed if not 2017 <= e["year"] <= 2026]
        lines += [
            "## Claimed P vs NP proofs 2017-2026",
            "",
            "Claims are reported as stated by their authors. The error family is a hypothesis "
            "using the numbering of [COMMON_ERRORS.md](../proofs/attempts/COMMON_ERRORS.md), not an audit. "
            "The human-readable backlog is [CLAIMED_PROOFS_2017_2026.md](CLAIMED_PROOFS_2017_2026.md).",
            "",
        ]
        lines += claimed_table(inside)
        if outside:
            lines += ["### Claimed proofs outside 2017-2026", ""] + claimed_table(outside)
    lines += ["## Counts", ""] + ["- " + line for line in stats_lines(data)] + [""]
    return "\n".join(lines)


def claimed_table(entries):
    lines = ["| id | year | claim | title | status | family (H) | responses |",
             "| --- | --- | --- | --- | --- | --- | --- |"]
    for entry in ordered(entries):
        family = str(entry.get("common_errors_family", ""))
        if entry.get("common_errors_secondary"):
            family += " (also " + ", ".join(map(str, entry["common_errors_secondary"])) + ")"
        lines.append("| `{}` | {} | {} | {} | {} | {} | {} |".format(
            entry["id"], entry["year"], entry.get("claim_direction", ""), link(entry), entry["status"],
            family, len(entry.get("documented_responses", []))))
    lines.append("")
    return lines


def anchor(title):
    text = re.sub(r"[^a-z0-9 -]", "", title.lower())
    return text.replace(" ", "-")


def stats_lines(data):
    entries = data["entries"]
    lines = ["entries: {}".format(len(entries))]
    for field in ("result_type", "artifact_class", "status", "claim_status_local", "verified"):
        counts = Counter(e[field] for e in entries)
        lines.append("{}: {}".format(field, ", ".join(
            "{} {}".format(k, counts[k]) for k in sorted(counts, key=lambda k: (-counts[k], k)))))
    years = Counter(e["year"] for e in entries)
    lines.append("year: {}".format(", ".join("{} {}".format(y, years[y]) for y in sorted(years, reverse=True))))
    return lines


# --------------------------------------------------------------------------- command line

def parse_args(argv):
    parser = argparse.ArgumentParser(description="Validate, query and render literature/registry.json.")
    parser.add_argument("--registry", type=Path, default=REGISTRY, help="registry JSON (default: %(default)s)")
    parser.add_argument("--readme", default=str(README),
                        help="guide checked against the registry (tags, Known gaps, ids), or 'none' to skip "
                             "all documentation checks")
    parser.add_argument("--claimed", default=str(CLAIMED_PROOFS),
                        help="claimed-proof backlog whose backticked ids must exist, or 'none' to skip")
    parser.add_argument("--output", type=Path, default=None, help="rendered Markdown path (default: next to the registry)")
    parser.add_argument("--tag", choices=sorted(TAGS), help="query: entries with this tag")
    parser.add_argument("--type", dest="kind", help="query: result_type or artifact_class")
    parser.add_argument("--status", help="query: status or claim_status_local")
    parser.add_argument("--text", help="query: case-insensitive substring of title or claim")
    parser.add_argument("--since", type=int, metavar="YEAR", help="query: year >= YEAR")
    parser.add_argument("--json", action="store_true", help="query: print matching entries as JSON")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--render", action="store_true", help="write REGISTRY.md from the registry")
    action.add_argument("--check-render", action="store_true", help="fail if REGISTRY.md is not current")
    action.add_argument("--stats", action="store_true", help="print counts by type, status and year")
    action.add_argument("--check-readme", action="store_true",
                        help="validate, including the documentation checks, and report them explicitly")
    return parser.parse_args(argv)


def main(argv=None):
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        data = load(args.registry)
    except (OSError, ValueError) as exc:
        print("error: cannot read {}: {}".format(args.registry, exc), file=sys.stderr)
        return 1
    errors = validate(data)
    if args.readme.lower() != "none":
        claimed = None if args.claimed.lower() == "none" else Path(args.claimed)
        errors += validate_docs(data, Path(args.readme), claimed, ATTEMPTS)
    elif args.check_readme:
        errors.append("--check-readme needs a guide; do not pass --readme none")
    if errors:
        for message in errors:
            print("error: " + message, file=sys.stderr)
        print("{} problem(s) in {}".format(len(errors), args.registry), file=sys.stderr)
        return 1

    output = args.output or args.registry.with_name("REGISTRY.md")
    if args.render:
        text = render(data)
        output.write_text(text, encoding="utf-8")
        print("wrote {} ({} entries)".format(output, len(data["entries"])))
        return 0
    if args.check_render:
        current = output.read_text(encoding="utf-8") if output.exists() else None
        if current != render(data):
            print("error: {} is stale; run with --render".format(output), file=sys.stderr)
            return 1
        print("{} is current".format(output))
        return 0
    if args.check_readme:
        print("{}: documentation matches the registry".format(args.readme))
        return 0
    if args.stats:
        for line in stats_lines(data):
            print(line)
        return 0
    if any(v is not None for v in (args.tag, args.kind, args.status, args.text, args.since)):
        matches = query(data["entries"], tag=args.tag, kind=args.kind, status=args.status,
                        text=args.text, since=args.since)
        if args.json:
            print(json.dumps(matches, ensure_ascii=False, indent=2))
        else:
            for entry in matches:
                print(format_row(entry))
            print("{} match(es)".format(len(matches)))
        return 0
    print("{}: {} entries valid".format(args.registry, len(data["entries"])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
