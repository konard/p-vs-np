#!/usr/bin/env python3
"""
Script to verify P vs NP attempt structure.

This script checks that each attempt follows the required directory structure:
- original/     (description of proof idea)
- proof/        (the forward proof attempt)
- refutation/   (the proof against the original idea)

Each proof/ and refutation/ should contain:
- lean/         (Lean 4 formalizations)
- rocq/         (Rocq formalizations)

Usage:
    python3 scripts/check_attempt_structure.py
    python3 scripts/check_attempt_structure.py --path proofs/attempts/specific-attempt
"""

import os
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Tuple


@dataclass
class StructureValidation:
    """Results of validating an attempt's structure."""
    path: Path
    has_readme: bool = False
    has_original: bool = False
    has_original_readme: bool = False
    has_proof: bool = False
    has_proof_lean: bool = False
    has_proof_rocq: bool = False
    has_refutation: bool = False
    has_refutation_readme: bool = False
    has_refutation_lean: bool = False
    has_refutation_rocq: bool = False
    errors: List[str] = None
    warnings: List[str] = None

    def __post_init__(self):
        if self.errors is None:
            self.errors = []
        if self.warnings is None:
            self.warnings = []

    def is_complete(self) -> bool:
        """Check if the attempt has all required components."""
        return (
            self.has_readme and
            self.has_original and
            self.has_original_readme and
            self.has_proof and
            (self.has_proof_lean or self.has_proof_rocq) and
            self.has_refutation and
            self.has_refutation_readme and
            (self.has_refutation_lean or self.has_refutation_rocq)
        )

    def get_missing(self) -> List[str]:
        """List missing required components."""
        missing = []
        if not self.has_readme:
            missing.append("README.md")
        if not self.has_original:
            missing.append("original/")
        elif not self.has_original_readme:
            missing.append("original/README.md")
        if not self.has_proof:
            missing.append("proof/")
        elif not (self.has_proof_lean or self.has_proof_rocq):
            missing.append("proof/lean/ or proof/rocq/ (at least one required)")
        if not self.has_refutation:
            missing.append("refutation/")
        elif not self.has_refutation_readme:
            missing.append("refutation/README.md")
        elif not (self.has_refutation_lean or self.has_refutation_rocq):
            missing.append("refutation/lean/ or refutation/rocq/ (at least one required)")
        return missing


def validate_attempt_structure(attempt_path: Path) -> StructureValidation:
    """Validate the structure of a single attempt directory."""
    result = StructureValidation(path=attempt_path)

    # Check main README
    readme_path = attempt_path / "README.md"
    result.has_readme = readme_path.exists()

    # Check original/ directory
    original_path = attempt_path / "original"
    result.has_original = original_path.exists() and original_path.is_dir()
    if result.has_original:
        result.has_original_readme = (original_path / "README.md").exists()

    # Check proof/ directory
    proof_path = attempt_path / "proof"
    result.has_proof = proof_path.exists() and proof_path.is_dir()
    if result.has_proof:
        lean_path = proof_path / "lean"
        rocq_path = proof_path / "rocq"
        result.has_proof_lean = lean_path.exists() and any(lean_path.glob("*.lean"))
        result.has_proof_rocq = rocq_path.exists() and any(rocq_path.glob("*.v"))

    # Check refutation/ directory
    refutation_path = attempt_path / "refutation"
    result.has_refutation = refutation_path.exists() and refutation_path.is_dir()
    if result.has_refutation:
        result.has_refutation_readme = (refutation_path / "README.md").exists()
        lean_path = refutation_path / "lean"
        rocq_path = refutation_path / "rocq"
        result.has_refutation_lean = lean_path.exists() and any(lean_path.glob("*.lean"))
        result.has_refutation_rocq = rocq_path.exists() and any(rocq_path.glob("*.v"))

    # Check for legacy structure (old coq/, lean/, isabelle/ at root)
    if (attempt_path / "coq").exists():
        result.warnings.append("Legacy structure detected: coq/ directory at root level. Should be moved to proof/rocq/ and refutation/rocq/")
    if (attempt_path / "lean").exists() and not result.has_proof:
        result.warnings.append("Legacy structure detected: lean/ directory at root level. Should be moved to proof/lean/ and refutation/lean/")
    if (attempt_path / "isabelle").exists():
        result.warnings.append("Deprecated: isabelle/ directory found. Isabelle support has been sunset.")

    return result


def find_attempts(base_path: Path) -> List[Path]:
    """Find all attempt directories."""
    attempts_path = base_path / "proofs" / "attempts"
    if not attempts_path.exists():
        return []

    attempts = []
    for item in attempts_path.iterdir():
        if item.is_dir() and not item.name.startswith('.'):
            # Skip files and known non-attempt directories
            if item.name not in ["README.md"]:
                attempts.append(item)

    return sorted(attempts)


def print_report(validations: List[StructureValidation]):
    """Print a human-readable report."""
    print("=" * 80)
    print("P vs NP ATTEMPTS - STRUCTURE VALIDATION REPORT")
    print("=" * 80)
    print()

    complete = [v for v in validations if v.is_complete()]
    incomplete = [v for v in validations if not v.is_complete()]
    with_warnings = [v for v in validations if v.warnings]

    print("SUMMARY")
    print("-" * 80)
    print(f"Total attempts scanned:     {len(validations)}")
    print(f"Complete (new structure):   {len(complete)}")
    print(f"Incomplete/legacy:          {len(incomplete)}")
    print(f"With warnings:              {len(with_warnings)}")
    print()

    if complete:
        print("COMPLETE ATTEMPTS (new structure)")
        print("-" * 80)
        for v in complete:
            status = []
            if v.has_proof_lean:
                status.append("Lean")
            if v.has_proof_rocq:
                status.append("Rocq")
            print(f"  ✓ {v.path.name} [{', '.join(status)}]")
        print()

    if incomplete:
        print("INCOMPLETE/LEGACY ATTEMPTS")
        print("-" * 80)
        for v in incomplete:
            print(f"  ✗ {v.path.name}")
            for missing in v.get_missing():
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
├── README.md              # Overview of the attempt
├── original/              # Description of the proof idea
│   └── README.md         # Detailed description
├── proof/                 # The forward proof formalization
│   ├── lean/             # Lean 4 files (*.lean)
│   └── rocq/             # Rocq files (*.v)
└── refutation/           # The refutation formalization
    ├── README.md         # Explanation of why the proof fails
    ├── lean/             # Lean 4 refutation (*.lean)
    └── rocq/             # Rocq refutation (*.v)
""")


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Check P vs NP attempt directory structure'
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

    print_report(validations)

    # Exit with error if any attempts are incomplete
    incomplete = [v for v in validations if not v.is_complete()]
    if incomplete:
        print(f"\n{len(incomplete)} attempt(s) have incomplete structure.")
        # Don't fail for now since this is a new structure requirement
        # sys.exit(1)


if __name__ == '__main__':
    main()
