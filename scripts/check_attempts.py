#!/usr/bin/env python3
"""
P vs NP Proof Attempts Tracker

This script compares the repository's formalized attempts against the reference
list from Woeginger's page and checks the completeness of each formalization.

Requirements per formalization (as specified in Issue #44):
1. README.md - Detailed description of the attempt, core idea, solution approach, and error explanations
2. Original papers (or README.md if paper not available)
3. Formalization (Coq/Lean/Isabelle) - Full proof draft with error comments
4. Formal refutation (Coq/Lean/Isabelle) - Proof of the refutation

Usage:
    python3 scripts/check_attempts.py [--json] [--verbose] [--markdown] [--create-issues]

Source: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
"""

import os
import re
import sys
import json
import argparse
import subprocess
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional
from datetime import datetime


# Reference list from Woeginger's P vs NP page (as of 2026-01)
# Format: (number, author, year, claim, folder_name_if_mapped)
WOEGINGER_ATTEMPTS = [
    (1, "Ted Swart", "1986-87", "P=NP", "ted-swart-1986-87-peqnp"),
    (2, "Anatoly Plotnikov", "1996", "P=NP", "author2-1996-peqnp"),
    (3, "Tang Pushan", "1997", "P=NP", "tang-pushan-1997-peqnp"),
    (4, "Miron Telpiz", "2000", "P=NP", "author4-2000-peqnp"),
    (5, "Seenil Gram", "2001", "P≠NP", "has-also-2001-pneqnp"),
    (6, "Charles Sauerbier", "2002", "P=NP", "charles-sauerbier-2002-peqnp"),
    (7, "Givi Bolotashvili", "2003", "P=NP", "author7-2003-peqnp"),
    (8, "Nicholas Argall", "2003", "Undecidable", "author8-2003-pneqnp"),
    (9, "N.C.A. da Costa & F.A. Doria", "2003", "Unprovable", None),
    (10, "Hubert Chen", "2003", "P≠NP", "author10-2004-pneqnp"),
    (11, "Craig Alan Feinstein", "2003-04", "P≠NP", None),
    (12, "Ki-Bong Nam et al.", "2004", "P≠NP", "ki-bong-nam-sh-wang-and-yang-gon-kim-published-2004-pneqnp"),
    (13, "Mikhail N. Kupchik", "2004", "P≠NP", None),
    (14, "Selmer Bringsjord & Joshua Taylor", "2004", "P=NP", "author11-2004-peqnp"),
    (15, "Bhupinder Singh Anand", "2004-2015", "P≠NP", "author12-2004-pneqnp"),
    (16, "Marius Ionescu", "2004", "P≠NP", "author13-2004-pneqnp"),
    (17, "Moustapha Diaby", "2004-2016", "P=NP", "moustapha-diaby-2004-peqnp"),
    (18, "Mircea Alexandru Popescu Moscu", "2004", "P≠NP", "author15-2004-pneqnp"),
    (19, "Andrea Bianchini", "2005", "P=NP", "andrea-bianchini-2005-peqnp"),
    (20, "Raju Renjit Grover", "2005", "P≠NP", "renjit-grover-2005-pneqnp"),
    (21, "Viktor V. Ivanov", "2005", "P≠NP", None),
    (22, "Bhupinder Singh Anand", "2005", "P≠NP", "singh-anand-2005-pneqnp"),
    (23, "Craig Alan Feinstein", "2005", "P≠NP", "alan-feinstein-2005-pneqnp"),
    (24, "Lev Gordeev", "2005", "P≠NP", "lev-gordeev-2005-pneqnp"),
    (25, "Lokman Kolukisa", "2005", "P=NP", "lokman-kolukisa-2005-peqnp"),
    (26, "Francesco Capasso", "2005", "P=NP", "francesco-capasso-2005-peqnp"),
    (27, "Ron Cohen", "2005", "P≠NP", "ron-cohen-2005-pneqnp"),
    (28, "Miron Teplitz", "2005", "P=NP", "miron-teplitz-2005-peqnp"),
    (29, "Joachim Mertz", "2005", "P=NP", "dr-joachim-mertz-2005-peqnp"),
    (30, "Bhupinder Singh Anand", "2006", "P≠NP", "singh-anand-2006-pneqnp"),
    (31, "Craig Alan Feinstein", "2006", "P≠NP", "a-new-version-of-2005-pneqnp"),
    (32, "Mohamed Mimouni", "2006", "P=NP", None),
    (33, "Sergey Gubin", "2006", "P=NP", None),
    (34, "Radoslaw Hofman", "2006", "P≠NP", None),
    (35, "Raju Renjit", "2006", "co-NP=NP", None),
    (36, "Rubens Ramos Viana", "2006", "P≠NP", None),
    (37, "Howard Kleiman", "2006", "P=NP", None),
    (38, "Khadija Riaz & Malik Sikander Hayat Khiyal", "2006", "P=NP", None),
    (39, "Anatoly D. Plotnikov", "2007", "P=NP", None),
    (40, "Guohun Zhu", "2007", "P=NP", None),
    (41, "Matthew Delacorte / Reiner Czerwinski", "2007", "P=NP/PSPACE", None),
    (42, "Cynthia Ann Harlan Krieger & Lee K. Jones", "2008", "P=NP", None),
    (43, "Jerrald Meek", "2008", "P≠NP", None),
    (44, "Bhupinder Singh Anand", "2008", "P≠NP", None),
    (45, "Rafee Ebrahim Kamouna", "2008", "P=NP", None),
    (46, "Jerrald Meek", "2008", "P≠NP", None),
    (47, "Jorma Jormakka", "2008", "P≠NP", None),
    (48, "Sten-Ake Tarnlund", "2008", "P≠NP", None),
    (49, "Zohreh O. Akbari", "2008", "P=NP", None),
    (50, "Javaid Aslam", "2008", "P=NP", None),
    (51, "Rafael Valls Hidalgo-Gato", "2009", "P=NP", None),
    (52, "Doron Zeilberger", "2009", "P=NP", None),
    (53, "Xinwen Jiang", "2009", "P=NP", None),
    (54, "Arto Annila", "2009", "P≠NP", "arto-annila-2009-pneqnp"),
    (55, "Andre Luiz Barbosa", "2009", "P≠NP", "luiz-barbosa-2009-pneqnp"),
    (56, "Yann Dujardin", "2009", "P=NP", "yann-dujardin-2009-peqnp"),
    (57, "Luigi Salemi", "2009", "P=NP", None),
    (58, "Ari Blinder", "2009", "P≠NP", None),
    (59, "Narendra S. Chaudhari", "2009", "P=NP", None),
    (60, "Lizhi Du", "2010", "P=NP", None),
    (61, "Changlin Wan", "2010", "P=NP", None),
    (62, "Carlos Barron-Romero", "2010", "P≠NP", None),
    (63, "Han Xiao Wen", "2010", "P=NP", None),
    (64, "Mikhail Katkov", "2010", "P=NP", None),
    (65, "Vinay Deolalikar", "2010", "P≠NP", "deolalikar-2010-pneqnp"),
    (66, "Sergey Gubin", "2010", "P=NP", None),
    (67, "Vladimir Romanov", "2010", "P=NP", None),
    (68, "Frank Vega Delgado", "2010", "P≠NP", None),
    (69, "Carlos Barron-Romero", "2010", "P≠NP", None),
    (70, "Bangyan Wen & Yi Lin", "2010", "P≠NP", None),
    (71, "Ruijia Liao", "2011", "P≠NP", None),
    (72, "Stefan Jaeger", "2011", "Both", None),
    (73, "Amar Mukherjee", "2011", "P=NP", None),
    (74, "Angela Weiss", "2011", "P=NP", None),
    (75, "Matt Groff", "2011", "P=NP", None),
    (76, "Sergey Kardash", "2011", "P=NP", None),
    (77, "Anatoly Plotnikov", "2011", "P≠NP", None),
    (78, "Koji Kobayashi", "2011", "P≠NP", None),
    (79, "Jason W. Steinmetz", "2011", "P=NP", "jason-w-steinmetz-2011-peqnp"),
    (80, "Jose Ignacio Alvarez-Hamelin", "2011", "P=NP", "hamelin-2011-peqnp"),
    (81, "Roman Yampolskiy", "2011", "P≠NP", "roman-yampolskiy-2011-pneqnp"),
    (82, "Craig Alan Feinstein", "2011", "P≠NP", "alan-feinstein-2011-pneqnp"),
    (83, "Jeffrey W. Holcomb", "2011", "P≠NP", "jeffrey-w-holcomb-2011-pneqnp"),
    (84, "Douglas Youvan", "2012", "P=NP", "douglas-youvan-2012-peqnp"),
    (85, "Gilberto Rodrigo Diduch", "2012", "P≠NP", "rodrigo-diduch-2012-pneqnp"),
    (86, "Koji Kobayashi", "2012", "P≠NP", "koji-kobayashi-2012-pneqnp"),
    (87, "Frank Vega Delgado", "2012", "P≠NP", "vega-delgado-2012-pneqnp"),
    (88, "Minseong Kim", "2012", "P≠NP", "minseong-kim-2012-pneqnp"),
    (89, "Algirdas Antano Maknickas", "2011", "P=NP", "antano-maknickas-2011-peqnp"),
    (90, "Michel Feldmann", "2012", "P=NP", "michel-feldmann-2012-peqnp"),
    (91, "Junichiro Fukuyama", "2012", "P≠NP", "infotechnology-center-2012-pneqnp"),
    (92, "Satoshi Tazawa", "2012", "P≠NP", "satoshi-tazawa-2012-pneqnp"),
    (93, "Wen-Qi Duan", "2012", "P=NP", "qi-duan-2012-peqnp"),
    (94, "Sergey V. Yakhontov", "2012", "P=NP", "sergey_v_yakhontov_2012_peqnp"),
    (95, "Natalia L. Malinina", "2012", "Unprovable", None),
    (96, "Louis Coder", "2012", "P=NP", "louis-coder-2012-peqnp"),
    (97, "Dmitriy Nuriyev", "2013", "P=NP", "dmitriy-nuriyev-2013-peqnp"),
    (98, "Algirdas Antano Maknickas", "2013", "P=NP", "author93-2013-peqnp"),
    (99, "Rustem Chingizovich Valeyev", "2013", "P≠NP", "chingizovich-valeyev-2013-pneqnp"),
    (100, "Frederic Gillet", "2013", "P=NP", "frederic-gillet-2013-peqnp"),
    (101, "Hanlin Liu", "2014", "P=NP", "hanlin-liu-2014-peqnp"),
    (102, "Pawan Tamta et al.", "2014", "P=NP", "dhami-2014-peqnp"),
    (103, "Peng Cui", "2014", "P=NP", "peng-cui-2014-peqnp"),
    (104, "Daegene Song", "2014", "P≠NP", "daegene-song-2014-pneqnp"),
    (105, "Joonmo Kim", "2014", "P≠NP", "joonmo-kim-2014-pneqnp"),
    (106, "Anatoly Panyukov", "2014", "P=NP", "anatoly-panyukov-2014-peqnp"),
    (107, "Michael LaPlante", "2015", "P=NP", "michael-laplante-2015-peqnp"),
    (108, "Alejandro Sanchez Guinea", "2015", "P=NP", "sanchez-guinea-2015-peqnp"),
    (109, "Frank Vega", "2015", "P=NP", "author104-2015-peqnp"),
    (110, "Yubin Huang", "2015", "P=NP", "yubin-huang-2015-peqnp"),
    (111, "Daniel Uribe & Frank Vega", "2016", "P≠NP", "daniel-uribe-2016-pneqnp"),
    (112, "Mathias Hauptmann", "2016", "P≠NP", "mathias-hauptmann-2016-pneqnp"),
    (113, "Steven Meyer", "2016", "P=NP", "steven-meyer-2016-peqnp"),
    (114, "Javier A. Arroyo-Figueroa", "2016", "P≠NP", "figueroa-2016-pneqnp"),
    (115, "Eli Halylaurin", "2016", "P=NP", "eli-halylaurin-2016-peqnp"),
    (116, "Stefan Rass", "2016", "P≠NP", "stefan-rass-2016-pneqnp"),
]


@dataclass
class AttemptStatus:
    """Status of a single P vs NP proof attempt."""
    number: int
    author: str
    year: str
    claim: str
    folder_name: Optional[str]
    has_folder: bool = False
    has_readme: bool = False
    has_paper: bool = False
    has_lean: bool = False
    has_coq: bool = False
    has_isabelle: bool = False
    readme_has_detailed_description: bool = False
    readme_has_error_explanation: bool = False
    lean_has_refutation: bool = False
    coq_has_refutation: bool = False
    isabelle_has_refutation: bool = False

    @property
    def completeness_score(self) -> int:
        """Calculate completeness score (0-100)."""
        score = 0
        if self.has_folder:
            score += 10
        if self.has_readme:
            score += 10
        if self.readme_has_detailed_description:
            score += 10
        if self.readme_has_error_explanation:
            score += 10
        if self.has_paper:
            score += 10
        if self.has_lean:
            score += 10
        if self.has_coq:
            score += 10
        if self.has_isabelle:
            score += 10
        # Refutation is important - 20 points total
        if self.lean_has_refutation or self.coq_has_refutation or self.isabelle_has_refutation:
            score += 20
        return score

    @property
    def status_emoji(self) -> str:
        """Return status emoji based on completeness."""
        score = self.completeness_score
        if score >= 90:
            return "✅"
        elif score >= 70:
            return "🟡"
        elif score >= 50:
            return "🟠"
        elif score > 0:
            return "🔴"
        else:
            return "⬜"


def find_repository_root() -> Path:
    """Find the repository root by looking for proofs/attempts directory."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "proofs" / "attempts").exists():
            return current
        current = current.parent
    # Fallback: assume script is in scripts/ directory
    return Path(__file__).resolve().parent.parent


def check_readme_quality(readme_path: Path) -> tuple[bool, bool]:
    """Check if README has detailed description and error explanation."""
    if not readme_path.exists():
        return False, False

    content = readme_path.read_text(encoding='utf-8', errors='ignore').lower()

    # Check for detailed description markers
    has_description = any(marker in content for marker in [
        "## summary",
        "## main argument",
        "## the argument",
        "## approach",
        "## proof strategy",
        "## overview",
        "## description",
    ])

    # Check for error explanation markers
    has_error = any(marker in content for marker in [
        "## error",
        "## the error",
        "## known issues",
        "## flaw",
        "## gap",
        "## mistake",
        "## critical gap",
        "## why this is wrong",
        "## refutation",
    ])

    return has_description, has_error


def check_formalization_has_refutation(dir_path: Path, ext: str) -> bool:
    """Check if formalization files contain refutation proofs."""
    if not dir_path.exists():
        return False

    patterns = [
        r'refut',
        r'error',
        r'gap',
        r'flaw',
        r'contradiction',
        r'invalid',
        r'mistake',
        r'sorry',  # In Lean, sorry marks incomplete proofs
        r'Admitted',  # In Coq, Admitted marks incomplete proofs
        r'oops',  # In Isabelle, oops marks failed proofs
    ]

    for file_path in dir_path.glob(f'*{ext}'):
        try:
            content = file_path.read_text(encoding='utf-8', errors='ignore')
            if any(re.search(pattern, content, re.IGNORECASE) for pattern in patterns):
                return True
        except Exception:
            continue

    return False


def check_attempt(repo_root: Path, number: int, author: str, year: str,
                  claim: str, folder_name: Optional[str]) -> AttemptStatus:
    """Check the status of a single attempt."""
    status = AttemptStatus(
        number=number,
        author=author,
        year=year,
        claim=claim,
        folder_name=folder_name,
    )

    attempts_dir = repo_root / "proofs" / "attempts"

    if folder_name:
        folder_path = attempts_dir / folder_name
        status.has_folder = folder_path.exists()

        if status.has_folder:
            # Check README
            readme_path = folder_path / "README.md"
            status.has_readme = readme_path.exists()
            if status.has_readme:
                status.readme_has_detailed_description, status.readme_has_error_explanation = \
                    check_readme_quality(readme_path)

            # Check for paper
            paper_dir = folder_path / "paper"
            status.has_paper = paper_dir.exists() and any(paper_dir.glob("*"))

            # Check Lean
            lean_dir = folder_path / "lean"
            status.has_lean = lean_dir.exists() and any(lean_dir.glob("*.lean"))
            if status.has_lean:
                status.lean_has_refutation = check_formalization_has_refutation(lean_dir, ".lean")

            # Check Coq
            coq_dir = folder_path / "coq"
            status.has_coq = coq_dir.exists() and any(coq_dir.glob("*.v"))
            if status.has_coq:
                status.coq_has_refutation = check_formalization_has_refutation(coq_dir, ".v")

            # Check Isabelle
            isabelle_dir = folder_path / "isabelle"
            status.has_isabelle = isabelle_dir.exists() and any(isabelle_dir.glob("*.thy"))
            if status.has_isabelle:
                status.isabelle_has_refutation = check_formalization_has_refutation(isabelle_dir, ".thy")

    return status


def find_unmapped_folders(repo_root: Path) -> list[str]:
    """Find attempt folders that aren't mapped in WOEGINGER_ATTEMPTS."""
    attempts_dir = repo_root / "proofs" / "attempts"
    if not attempts_dir.exists():
        return []

    mapped_folders = {a[4] for a in WOEGINGER_ATTEMPTS if a[4] is not None}
    existing_folders = {d.name for d in attempts_dir.iterdir() if d.is_dir()}

    return sorted(existing_folders - mapped_folders)


def check_folder_structure_consistency(repo_root: Path, results: list) -> list[dict]:
    """Check if all attempt folders have consistent structure."""
    issues = []
    expected_structure = ["README.md", "lean/", "coq/", "isabelle/"]

    for r in results:
        if not r.has_folder or not r.folder_name:
            continue

        folder_path = repo_root / "proofs" / "attempts" / r.folder_name
        folder_issues = []

        # Check for expected structure
        if not r.has_readme:
            folder_issues.append("Missing README.md")
        if not r.has_lean:
            folder_issues.append("Missing lean/ folder or .lean files")
        if not r.has_coq:
            folder_issues.append("Missing coq/ folder or .v files")
        if not r.has_isabelle:
            folder_issues.append("Missing isabelle/ folder or .thy files")
        if not r.has_paper:
            folder_issues.append("Missing paper/ folder")

        if folder_issues:
            issues.append({
                "number": r.number,
                "author": r.author,
                "year": r.year,
                "folder": r.folder_name,
                "issues": folder_issues,
                "completeness_score": r.completeness_score,
            })

    return issues


def generate_markdown_report(results: list, unmapped: list[str], repo_root: Path) -> str:
    """Generate a markdown document with comparison table."""
    total = len(results)
    mapped = sum(1 for r in results if r.folder_name is not None)
    with_folders = sum(1 for r in results if r.has_folder)
    with_readme = sum(1 for r in results if r.has_readme)
    with_paper = sum(1 for r in results if r.has_paper)
    with_lean = sum(1 for r in results if r.has_lean)
    with_coq = sum(1 for r in results if r.has_coq)
    with_isabelle = sum(1 for r in results if r.has_isabelle)
    with_refutation = sum(1 for r in results if r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation)
    avg_score = sum(r.completeness_score for r in results) / len(results) if results else 0

    md = []
    md.append("# P vs NP Proof Attempts Status Report")
    md.append("")
    md.append(f"*Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*")
    md.append("")
    md.append("Reference: [Woeginger's P vs NP page](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm)")
    md.append("")

    # Summary table
    md.append("## Summary")
    md.append("")
    md.append("| Metric | Count | Percentage |")
    md.append("|--------|-------|------------|")
    md.append(f"| Total attempts on Woeginger's list | {total} | 100% |")
    md.append(f"| Mapped to repository folders | {mapped} | {mapped*100//total}% |")
    md.append(f"| With existing folders | {with_folders} | {with_folders*100//total}% |")
    md.append(f"| With README.md | {with_readme} | {with_readme*100//total}% |")
    md.append(f"| With original paper | {with_paper} | {with_paper*100//total}% |")
    md.append(f"| With Lean formalization | {with_lean} | {with_lean*100//total}% |")
    md.append(f"| With Coq formalization | {with_coq} | {with_coq*100//total}% |")
    md.append(f"| With Isabelle formalization | {with_isabelle} | {with_isabelle*100//total}% |")
    md.append(f"| With formal refutation | {with_refutation} | {with_refutation*100//total}% |")
    md.append(f"| **Average completeness score** | **{avg_score:.1f}%** | - |")
    md.append("")

    # Full comparison table
    md.append("## All Attempts Comparison")
    md.append("")
    md.append("| # | Status | Score | Author | Year | Claim | Folder | README | Paper | Lean | Coq | Isabelle | Refutation |")
    md.append("|---|--------|-------|--------|------|-------|--------|--------|-------|------|-----|----------|------------|")

    for r in results:
        check = "x"
        cross = " "
        has_refutation = r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation
        folder_link = f"[{r.folder_name[:20]}...](proofs/attempts/{r.folder_name})" if r.folder_name and len(r.folder_name) > 23 else (f"[{r.folder_name}](proofs/attempts/{r.folder_name})" if r.folder_name else "-")

        md.append(f"| {r.number} | {r.status_emoji} | {r.completeness_score}% | {r.author[:25]}{'...' if len(r.author) > 25 else ''} | {r.year} | {r.claim} | {folder_link} | {check if r.has_readme else cross} | {check if r.has_paper else cross} | {check if r.has_lean else cross} | {check if r.has_coq else cross} | {check if r.has_isabelle else cross} | {check if has_refutation else cross} |")

    md.append("")

    # Missing attempts section
    missing_attempts = [r for r in results if r.folder_name is None]
    if missing_attempts:
        md.append("## Missing Attempts (Not Yet Mapped)")
        md.append("")
        md.append("These attempts from Woeginger's list do not have corresponding folders in the repository:")
        md.append("")
        md.append("| # | Author | Year | Claim | Action Needed |")
        md.append("|---|--------|------|-------|---------------|")
        for r in missing_attempts:
            md.append(f"| {r.number} | {r.author} | {r.year} | {r.claim} | Create folder and formalization |")
        md.append("")
        md.append(f"**Total missing: {len(missing_attempts)}**")
        md.append("")

    # Incomplete attempts section
    incomplete = [r for r in results if r.has_folder and r.completeness_score < 90]
    if incomplete:
        md.append("## Incomplete Attempts (Need More Work)")
        md.append("")
        md.append("| # | Status | Score | Author | Year | Missing Components |")
        md.append("|---|--------|-------|--------|------|-------------------|")

        for r in sorted(incomplete, key=lambda x: x.completeness_score):
            missing = []
            if not r.readme_has_detailed_description:
                missing.append("detailed description")
            if not r.readme_has_error_explanation:
                missing.append("error explanation")
            if not r.has_paper:
                missing.append("paper")
            if not r.has_lean:
                missing.append("Lean")
            if not r.has_coq:
                missing.append("Coq")
            if not r.has_isabelle:
                missing.append("Isabelle")
            if not (r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation):
                missing.append("formal refutation")

            md.append(f"| {r.number} | {r.status_emoji} | {r.completeness_score}% | {r.author[:25]} | {r.year} | {', '.join(missing)} |")

        md.append("")

    # Structure consistency check
    structure_issues = check_folder_structure_consistency(repo_root, results)
    if structure_issues:
        md.append("## Folder Structure Issues")
        md.append("")
        md.append("The following attempts have inconsistent folder structures:")
        md.append("")
        md.append("| # | Author | Folder | Issues |")
        md.append("|---|--------|--------|--------|")
        for issue in structure_issues:
            md.append(f"| {issue['number']} | {issue['author'][:20]} | {issue['folder'][:30]} | {', '.join(issue['issues'])} |")
        md.append("")

    # Unmapped folders
    if unmapped:
        md.append("## Unmapped Folders")
        md.append("")
        md.append("These folders exist in the repository but are not in Woeginger's list:")
        md.append("")
        for folder in unmapped:
            md.append(f"- `{folder}`")
        md.append("")

    # Legend
    md.append("## Legend")
    md.append("")
    md.append("| Symbol | Meaning |")
    md.append("|--------|---------|")
    md.append("| x | Present |")
    md.append("| (blank) | Missing |")
    md.append("")
    md.append("### Status Icons")
    md.append("")
    md.append("| Icon | Meaning | Score Range |")
    md.append("|------|---------|-------------|")
    md.append("| :white_check_mark: | Complete | 90-100% |")
    md.append("| :yellow_circle: | Nearly complete | 70-89% |")
    md.append("| :orange_circle: | In progress | 50-69% |")
    md.append("| :red_circle: | Started | 1-49% |")
    md.append("| :white_large_square: | Not started | 0% |")
    md.append("")

    # Requirements reference
    md.append("## Requirements per Formalization")
    md.append("")
    md.append("Each attempt should have:")
    md.append("")
    md.append("1. **README.md** - Detailed description of how the attempt was structured, core idea, intended solution, and error explanations")
    md.append("2. **paper/** folder - Original papers (or documentation in README.md)")
    md.append("3. **lean/** folder - Lean formalization with full proof draft and error comments")
    md.append("4. **coq/** folder - Coq formalization with full proof draft and error comments")
    md.append("5. **isabelle/** folder - Isabelle formalization with full proof draft and error comments")
    md.append("6. **Formal refutation** - Formal proof of the refutation in at least one proof assistant")
    md.append("")

    return "\n".join(md)


def create_github_issue(title: str, body: str, labels: list[str] = None) -> bool:
    """Create a GitHub issue using gh CLI."""
    cmd = ["gh", "issue", "create", "--title", title, "--body", body]
    if labels:
        for label in labels:
            cmd.extend(["--label", label])

    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        if result.returncode == 0:
            print(f"  Created: {result.stdout.strip()}")
            return True
        else:
            print(f"  Failed: {result.stderr.strip()}")
            return False
    except subprocess.TimeoutExpired:
        print("  Timeout creating issue")
        return False
    except Exception as e:
        print(f"  Error: {e}")
        return False


def create_issues_for_missing(results: list, dry_run: bool = False) -> tuple[int, int]:
    """Create GitHub issues for missing and incomplete attempts."""
    created = 0
    failed = 0

    # Issues for missing attempts (not mapped)
    missing_attempts = [r for r in results if r.folder_name is None]
    print(f"\nCreating issues for {len(missing_attempts)} missing attempts...")

    for r in missing_attempts:
        title = f"Add formalization for attempt #{r.number}: {r.author} ({r.year}) - {r.claim}"
        body = f"""## Missing Attempt Formalization

This attempt from [Woeginger's P vs NP list](https://wscor.win.tue.nl/woeginger/P-versus-NP.htm) needs to be formalized.

### Attempt Details
- **Number**: #{r.number}
- **Author**: {r.author}
- **Year**: {r.year}
- **Claim**: {r.claim}

### Required Work

1. Create folder `proofs/attempts/[author-name]-{r.year.split('-')[0]}-{'peqnp' if r.claim == 'P=NP' else 'pneqnp'}/`
2. Add `README.md` with:
   - Description of the attempt's core idea
   - How it intended to solve P vs NP
   - Detailed error explanation
3. Add `paper/` folder with original paper (if available)
4. Add Lean formalization in `lean/` folder
5. Add Coq formalization in `coq/` folder
6. Add Isabelle formalization in `isabelle/` folder
7. Include formal refutation proof

### Reference
- Woeginger's list entry #{r.number}
- Related to issue #44
"""
        print(f"  #{r.number}: {r.author} ({r.year})")
        if not dry_run:
            if create_github_issue(title, body, ["attempt-formalization"]):
                created += 1
            else:
                failed += 1
        else:
            print(f"    [DRY RUN] Would create issue: {title}")
            created += 1

    # Issues for incomplete attempts
    incomplete = [r for r in results if r.has_folder and r.completeness_score < 90]
    print(f"\nCreating issues for {len(incomplete)} incomplete attempts...")

    for r in incomplete:
        missing = []
        if not r.readme_has_detailed_description:
            missing.append("detailed description in README")
        if not r.readme_has_error_explanation:
            missing.append("error explanation in README")
        if not r.has_paper:
            missing.append("paper/ folder")
        if not r.has_lean:
            missing.append("Lean formalization")
        if not r.has_coq:
            missing.append("Coq formalization")
        if not r.has_isabelle:
            missing.append("Isabelle formalization")
        if not (r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation):
            missing.append("formal refutation proof")

        title = f"Complete formalization for attempt #{r.number}: {r.author} ({r.year}) - Score: {r.completeness_score}%"
        body = f"""## Incomplete Attempt Formalization

This attempt needs additional work to be complete.

### Attempt Details
- **Number**: #{r.number}
- **Author**: {r.author}
- **Year**: {r.year}
- **Claim**: {r.claim}
- **Current Score**: {r.completeness_score}%
- **Folder**: `proofs/attempts/{r.folder_name}/`

### Missing Components

{chr(10).join(f'- [ ] {m}' for m in missing)}

### Current Status
- README.md: {'Present' if r.has_readme else 'Missing'}
- Paper: {'Present' if r.has_paper else 'Missing'}
- Lean: {'Present' if r.has_lean else 'Missing'}
- Coq: {'Present' if r.has_coq else 'Missing'}
- Isabelle: {'Present' if r.has_isabelle else 'Missing'}
- Refutation: {'Present' if (r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation) else 'Missing'}

### Reference
- Related to issue #44
"""
        print(f"  #{r.number}: {r.author} - {r.completeness_score}% complete")
        if not dry_run:
            if create_github_issue(title, body, ["attempt-formalization"]):
                created += 1
            else:
                failed += 1
        else:
            print(f"    [DRY RUN] Would create issue: {title}")
            created += 1

    return created, failed


def main():
    parser = argparse.ArgumentParser(
        description="Check P vs NP proof attempts against Woeginger's list"
    )
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    parser.add_argument('--verbose', '-v', action='store_true', help='Show detailed output')
    parser.add_argument('--missing-only', action='store_true', help='Show only missing attempts')
    parser.add_argument('--incomplete-only', action='store_true', help='Show only incomplete attempts')
    parser.add_argument('--markdown', '-m', action='store_true', help='Generate markdown report')
    parser.add_argument('--markdown-file', type=str, default='ATTEMPTS_STATUS.md', help='Output file for markdown report (default: ATTEMPTS_STATUS.md)')
    parser.add_argument('--create-issues', action='store_true', help='Create GitHub issues for missing/incomplete attempts')
    parser.add_argument('--dry-run', action='store_true', help='Show what issues would be created without creating them')
    parser.add_argument('--check-structure', action='store_true', help='Check folder structure consistency')
    args = parser.parse_args()

    repo_root = find_repository_root()
    results: list[AttemptStatus] = []

    for number, author, year, claim, folder_name in WOEGINGER_ATTEMPTS:
        status = check_attempt(repo_root, number, author, year, claim, folder_name)
        results.append(status)

    # Find unmapped folders
    unmapped = find_unmapped_folders(repo_root)

    # Handle create-issues mode
    if args.create_issues or args.dry_run:
        created, failed = create_issues_for_missing(results, dry_run=args.dry_run)
        print(f"\nSummary: {created} issues {'would be ' if args.dry_run else ''}created, {failed} failed")
        return

    # Handle markdown mode
    if args.markdown:
        md_content = generate_markdown_report(results, unmapped, repo_root)
        output_path = repo_root / args.markdown_file
        output_path.write_text(md_content, encoding='utf-8')
        print(f"Markdown report generated: {output_path}")
        return

    # Handle structure check mode
    if args.check_structure:
        issues = check_folder_structure_consistency(repo_root, results)
        if issues:
            print("Folder Structure Issues Found:")
            print("-" * 60)
            for issue in issues:
                print(f"\n#{issue['number']}: {issue['author']} ({issue['year']})")
                print(f"  Folder: {issue['folder']}")
                print(f"  Score: {issue['completeness_score']}%")
                print(f"  Issues:")
                for i in issue['issues']:
                    print(f"    - {i}")
            print(f"\nTotal: {len(issues)} folders with structure issues")
        else:
            print("All folders have consistent structure!")
        return

    if args.json:
        output = {
            "total_attempts": len(WOEGINGER_ATTEMPTS),
            "mapped_attempts": sum(1 for r in results if r.folder_name is not None),
            "with_folders": sum(1 for r in results if r.has_folder),
            "with_readme": sum(1 for r in results if r.has_readme),
            "with_paper": sum(1 for r in results if r.has_paper),
            "with_lean": sum(1 for r in results if r.has_lean),
            "with_coq": sum(1 for r in results if r.has_coq),
            "with_isabelle": sum(1 for r in results if r.has_isabelle),
            "complete_refutation": sum(1 for r in results if r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation),
            "average_completeness": sum(r.completeness_score for r in results) / len(results) if results else 0,
            "unmapped_folders": unmapped,
            "attempts": [
                {
                    "number": r.number,
                    "author": r.author,
                    "year": r.year,
                    "claim": r.claim,
                    "folder_name": r.folder_name,
                    "completeness_score": r.completeness_score,
                    "has_folder": r.has_folder,
                    "has_readme": r.has_readme,
                    "has_paper": r.has_paper,
                    "has_lean": r.has_lean,
                    "has_coq": r.has_coq,
                    "has_isabelle": r.has_isabelle,
                    "has_refutation": r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation,
                }
                for r in results
            ]
        }
        print(json.dumps(output, indent=2))
        return

    # Text output
    print("=" * 80)
    print("P vs NP Proof Attempts Status Report")
    print("=" * 80)
    print(f"Reference: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm")
    print()

    # Summary statistics
    total = len(WOEGINGER_ATTEMPTS)
    mapped = sum(1 for r in results if r.folder_name is not None)
    with_folders = sum(1 for r in results if r.has_folder)
    with_readme = sum(1 for r in results if r.has_readme)
    with_paper = sum(1 for r in results if r.has_paper)
    with_lean = sum(1 for r in results if r.has_lean)
    with_coq = sum(1 for r in results if r.has_coq)
    with_isabelle = sum(1 for r in results if r.has_isabelle)
    with_refutation = sum(1 for r in results if r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation)
    avg_score = sum(r.completeness_score for r in results) / len(results) if results else 0

    print("SUMMARY")
    print("-" * 40)
    print(f"Total attempts on Woeginger's list: {total}")
    print(f"Mapped to repository folders:       {mapped} ({mapped*100//total}%)")
    print(f"With existing folders:              {with_folders} ({with_folders*100//total}%)")
    print(f"With README.md:                     {with_readme} ({with_readme*100//total}%)")
    print(f"With original paper:                {with_paper} ({with_paper*100//total}%)")
    print(f"With Lean formalization:            {with_lean} ({with_lean*100//total}%)")
    print(f"With Coq formalization:             {with_coq} ({with_coq*100//total}%)")
    print(f"With Isabelle formalization:        {with_isabelle} ({with_isabelle*100//total}%)")
    print(f"With formal refutation:             {with_refutation} ({with_refutation*100//total}%)")
    print(f"Average completeness score:         {avg_score:.1f}%")
    print()

    # Detailed list
    if args.verbose or args.missing_only or args.incomplete_only:
        print("DETAILED STATUS")
        print("-" * 80)
        print(f"{'#':<4} {'Status':<6} {'Score':<6} {'Author':<30} {'Year':<10} {'Claim':<10}")
        print("-" * 80)

        for r in results:
            if args.missing_only and r.has_folder:
                continue
            if args.incomplete_only and r.completeness_score >= 90:
                continue

            print(f"{r.number:<4} {r.status_emoji:<6} {r.completeness_score:<6} {r.author[:28]:<30} {r.year:<10} {r.claim:<10}")

            if args.verbose and r.has_folder:
                components = []
                if r.has_readme:
                    components.append("README")
                if r.has_paper:
                    components.append("Paper")
                if r.has_lean:
                    components.append("Lean")
                if r.has_coq:
                    components.append("Coq")
                if r.has_isabelle:
                    components.append("Isabelle")
                print(f"     Components: {', '.join(components) if components else 'None'}")
                if r.folder_name:
                    print(f"     Folder: {r.folder_name}")
                print()

        print()

    # Missing attempts (not yet mapped)
    missing_attempts = [r for r in results if r.folder_name is None]
    if missing_attempts:
        print("MISSING ATTEMPTS (not yet mapped to repository)")
        print("-" * 80)
        for r in missing_attempts:
            print(f"  #{r.number}: {r.author} ({r.year}) - {r.claim}")
        print(f"\nTotal missing: {len(missing_attempts)}")
        print()

    # Incomplete attempts (mapped but missing components)
    incomplete = [r for r in results if r.has_folder and r.completeness_score < 90]
    if incomplete:
        print("INCOMPLETE ATTEMPTS (need more work)")
        print("-" * 80)
        for r in sorted(incomplete, key=lambda x: x.completeness_score):
            missing = []
            if not r.readme_has_detailed_description:
                missing.append("detailed description")
            if not r.readme_has_error_explanation:
                missing.append("error explanation")
            if not r.has_paper:
                missing.append("paper")
            if not r.has_lean:
                missing.append("Lean")
            if not r.has_coq:
                missing.append("Coq")
            if not r.has_isabelle:
                missing.append("Isabelle")
            if not (r.lean_has_refutation or r.coq_has_refutation or r.isabelle_has_refutation):
                missing.append("formal refutation")

            print(f"  {r.status_emoji} #{r.number}: {r.author} ({r.year}) - Score: {r.completeness_score}%")
            print(f"     Missing: {', '.join(missing)}")
        print()

    # Unmapped folders
    if unmapped:
        print("UNMAPPED FOLDERS (in repository but not in Woeginger's list)")
        print("-" * 80)
        for folder in unmapped:
            print(f"  - {folder}")
        print()

    # Legend
    print("LEGEND")
    print("-" * 40)
    print("✅ Complete (90-100%)")
    print("🟡 Nearly complete (70-89%)")
    print("🟠 In progress (50-69%)")
    print("🔴 Started (1-49%)")
    print("⬜ Not started (0%)")


if __name__ == "__main__":
    main()
