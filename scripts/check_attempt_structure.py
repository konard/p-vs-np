#!/usr/bin/env python3
"""
Script to verify P vs NP attempt structure and generate markdown lists.

This script checks that each attempt follows the required directory structure:
- README.md        (required - overview of the attempt)
- ORIGINAL.md      (recommended - markdown reconstruction of paper)
- ORIGINAL.pdf     (recommended - original paper file)
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
    python3 scripts/check_attempt_structure.py --path proofs/attempts/specific-attempt
    python3 scripts/check_attempt_structure.py --generate-list
    python3 scripts/check_attempt_structure.py --generate-list --output proofs/attempts/ATTEMPTS.md
"""

import os
import sys
import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Tuple, Optional


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
            missing.append("ORIGINAL.md (recommended)")
        if not self.has_original_file:
            missing.append("ORIGINAL.pdf or ORIGINAL.html (recommended)")
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


def parse_metadata_from_readme(readme_path: Path) -> Optional[AttemptMetadata]:
    """Extract metadata from README.md file."""
    if not readme_path.exists():
        return None

    try:
        content = readme_path.read_text(encoding='utf-8')
    except Exception:
        return None

    metadata = AttemptMetadata()

    # Extract title from first H1
    title_match = re.search(r'^#\s+(.+?)(?:\s+-\s+|\s+\()?(P[≠=!]?N?P)?', content, re.MULTILINE)
    if title_match:
        metadata.title = title_match.group(1).strip()

    # Extract metadata fields
    patterns = {
        'author': r'\*\*Author\*\*[:\s]*(.+?)(?:\n|$)',
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

    # Check ORIGINAL.md
    result.has_original_md = (attempt_path / "ORIGINAL.md").exists()

    # Check for original paper file (PDF, HTML, etc.)
    original_extensions = ['.pdf', '.html', '.htm', '.txt', '.tex']
    for ext in original_extensions:
        original_file = attempt_path / f"ORIGINAL{ext}"
        if original_file.exists():
            result.has_original_file = True
            result.original_file_ext = ext
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
    if (attempt_path / "original").exists():
        result.warnings.append("Legacy: original/ folder. ORIGINAL.md and ORIGINAL.pdf should be at root level")

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
        print("COMPLETE ATTEMPTS (has README.md, ORIGINAL.md, ORIGINAL.pdf, proof/, refutation/)")
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
├── ORIGINAL.md            # Markdown reconstruction of paper (recommended)
├── ORIGINAL.pdf           # Original paper PDF (recommended, can be .html/.tex)
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
    lines.append("- 📄 = Has ORIGINAL.md")
    lines.append("- 📎 = Has ORIGINAL.pdf")
    lines.append("- 🔷 = Has Lean formalization")
    lines.append("- 🔶 = Has Rocq formalization")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Sort by year, then by author
    sorted_validations = sorted(
        validations,
        key=lambda v: (
            v.metadata.year if v.metadata and v.metadata.year else "9999",
            v.metadata.author if v.metadata and v.metadata.author else v.path.name
        )
    )

    # Group by decade
    decades = {}
    for v in sorted_validations:
        year = v.metadata.year if v.metadata and v.metadata.year else "Unknown"
        try:
            decade = f"{int(year)//10*10}s"
        except ValueError:
            decade = "Unknown"
        if decade not in decades:
            decades[decade] = []
        decades[decade].append(v)

    for decade in sorted(decades.keys()):
        lines.append(f"## {decade}")
        lines.append("")
        lines.append("| Claim | Author | Year | Title | Docs | Formal |")
        lines.append("|:-----:|--------|------|-------|:----:|:------:|")

        for v in decades[decade]:
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

    # Statistics
    lines.append("---")
    lines.append("")
    lines.append("## Statistics")
    lines.append("")

    total = len(validations)
    with_original_md = sum(1 for v in validations if v.has_original_md)
    with_original_file = sum(1 for v in validations if v.has_original_file)
    with_lean = sum(1 for v in validations if v.has_lean())
    with_rocq = sum(1 for v in validations if v.has_rocq())
    with_proof = sum(1 for v in validations if v.has_proof)
    with_refutation = sum(1 for v in validations if v.has_refutation)

    p_eq_np = sum(1 for v in validations if v.get_claim_emoji() == "✓")
    p_neq_np = sum(1 for v in validations if v.get_claim_emoji() == "✗")
    unprovable = sum(1 for v in validations if v.get_claim_emoji() == "?")

    lines.append(f"- **Total attempts:** {total}")
    lines.append(f"- **Claims P = NP:** {p_eq_np}")
    lines.append(f"- **Claims P ≠ NP:** {p_neq_np}")
    lines.append(f"- **Claims unprovable:** {unprovable}")
    lines.append(f"- **With ORIGINAL.md:** {with_original_md}")
    lines.append(f"- **With original paper:** {with_original_file}")
    lines.append(f"- **With proof/ directory:** {with_proof}")
    lines.append(f"- **With refutation/ directory:** {with_refutation}")
    lines.append(f"- **With Lean formalization:** {with_lean}")
    lines.append(f"- **With Rocq formalization:** {with_rocq}")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("*This file is auto-generated by `scripts/check_attempt_structure.py --generate-list`*")

    content = "\n".join(lines)

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

    if args.generate_list:
        content = generate_markdown_list(validations, args.output)
        if not args.output:
            print(content)
    else:
        if not args.quiet:
            print_report(validations)

    # Exit with error if any attempts are invalid (missing README)
    invalid = [v for v in validations if not v.is_valid()]
    if invalid:
        print(f"\n{len(invalid)} attempt(s) are invalid (missing README.md).")
        sys.exit(1)


if __name__ == '__main__':
    main()
