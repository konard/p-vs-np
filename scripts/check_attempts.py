#!/usr/bin/env python3
"""
Script to verify P vs NP attempts against Woeginger's list.

This script:
1. Parses the list of attempts from Woeginger's page
2. Checks existing attempts in proofs/attempts/
3. Verifies each attempt has the required structure:
   - README.md with detailed description
   - Original papers (or at least README.md documentation)
   - Formalization attempts (Coq/Lean/Isabelle)
   - Formal refutation (where applicable)
4. Reports missing attempts and incomplete formalizations
"""

import os
import json
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple
from dataclasses import dataclass, asdict
from enum import Enum


class Claim(Enum):
    P_EQ_NP = "P=NP"
    P_NEQ_NP = "P≠NP"
    UNDECIDABLE = "Undecidable"
    UNPROVABLE = "Unprovable"
    MODEL_DEPENDENT = "Model-dependent"
    UNKNOWN = "Unknown"


@dataclass(frozen=True)
class Attempt:
    """Represents a P vs NP attempt from Woeginger's list."""
    author: str
    year: str
    claim: Claim
    description: str
    woeginger_id: int = None

    def get_normalized_name(self) -> str:
        """Generate a normalized directory name for the attempt."""
        # Normalize author name
        author_norm = self.author.lower()
        # Remove special characters
        author_norm = re.sub(r'[^a-z0-9\s-]', '', author_norm)
        # Replace spaces with hyphens
        author_norm = re.sub(r'\s+', '-', author_norm.strip())

        # Determine claim suffix
        claim_suffix = "peqnp" if self.claim == Claim.P_EQ_NP else "pneqnp"

        return f"{author_norm}-{self.year}-{claim_suffix}"


@dataclass
class AttemptStructure:
    """Represents the file structure requirements for an attempt."""
    has_readme: bool = False
    has_lean: bool = False
    has_coq: bool = False
    has_isabelle: bool = False
    has_refutation: bool = False
    has_papers: bool = False
    readme_path: str = None
    lean_files: List[str] = None
    coq_files: List[str] = None
    isabelle_files: List[str] = None

    def __post_init__(self):
        if self.lean_files is None:
            self.lean_files = []
        if self.coq_files is None:
            self.coq_files = []
        if self.isabelle_files is None:
            self.isabelle_files = []

    def is_complete(self) -> bool:
        """Check if the attempt has all required components."""
        return (self.has_readme and
                (self.has_lean or self.has_coq or self.has_isabelle))

    def get_missing_components(self) -> List[str]:
        """List missing components."""
        missing = []
        if not self.has_readme:
            missing.append("README.md")
        if not self.has_lean and not self.has_coq and not self.has_isabelle:
            missing.append("At least one formalization (Lean/Coq/Isabelle)")
        return missing


# Woeginger's list - parsed from https://wscor.win.tue.nl/woeginger/P-versus-NP.htm
WOEGINGER_ATTEMPTS = [
    # P=NP attempts
    Attempt("Ted Swart", "1986", Claim.P_EQ_NP, "Linear programming formulations for Hamiltonian cycle", 1),
    Attempt("Anatoly Plotnikov", "1996", Claim.P_EQ_NP, "Polynomial-time graph partition into cliques", 2),
    Attempt("Tang Pushan", "1997", Claim.P_EQ_NP, "Polynomial algorithm for clique problem", 3),
    Attempt("Miron Telpiz", "2000", Claim.P_EQ_NP, "Proof that NP-complete class coincides with P", 4),
    Attempt("Charles Sauerbier", "2002", Claim.P_EQ_NP, "Polynomial SAT algorithm", 5),
    Attempt("Givi Bolotashvili", "2003", Claim.P_EQ_NP, "Solution of Linear Ordering Problem", 6),
    Attempt("Moustapha Diaby", "2004", Claim.P_EQ_NP, "LP formulation of TSP", 7),
    Attempt("Lokman Kolukisa", "2005", Claim.P_EQ_NP, "Polynomial algorithm for tautology recognition", 8),
    Attempt("Francesco Capasso", "2005", Claim.P_EQ_NP, "Polynomial-time Circuit-SAT algorithm", 9),
    Attempt("Miron Teplitz", "2005", Claim.P_EQ_NP, "Sigma-notation equivalence proof", 10),
    Attempt("Joachim Mertz", "2005", Claim.P_EQ_NP, "LP formulation of TSP with O(n^5) variables", 11),
    Attempt("Mohamed Mimouni", "2006", Claim.P_EQ_NP, "Polynomial clique algorithm", 12),
    Attempt("Sergey Gubin", "2006", Claim.P_EQ_NP, "Polynomial Hamiltonian cycle algorithm", 13),
    Attempt("Howard Kleiman", "2006", Claim.P_EQ_NP, "Asymmetric TSP modification approach", 14),
    Attempt("Khadija Riaz and Malik Hayat", "2006", Claim.P_EQ_NP, "Hamiltonian cycle polynomial time", 15),
    Attempt("Anatoly D. Plotnikov", "2007", Claim.P_EQ_NP, "Experimental algorithm, O(n^8) independent set", 16),
    Attempt("Guohun Zhu", "2007", Claim.P_EQ_NP, "Hamiltonian Cycle in bipartite cubic graphs", 17),
    Attempt("Matthew Delacorte", "2007", Claim.P_EQ_NP, "Graph isomorphism PSPACE-complete", 18),
    Attempt("Reiner Czerwinski", "2007", Claim.P_EQ_NP, "Polynomial graph isomorphism algorithm", 19),
    Attempt("Cynthia Ann Harlan Krieger", "2008", Claim.P_EQ_NP, "Patent for Hamiltonian circuit polynomial solution", 20),
    Attempt("Rafee Ebrahim Kamouna", "2008", Claim.P_EQ_NP, "SAT not NP-complete, therefore P=NP", 21),
    Attempt("Doron Zeilberger", "2009", Claim.P_EQ_NP, "Subset Sum polynomial algorithm (April Fool's joke)", 22),
    Attempt("Xinwen Jiang", "2009", Claim.P_EQ_NP, "Hamilton circuit polynomial algorithm", 23),
    Attempt("Yann Dujardin", "2009", Claim.P_EQ_NP, "Partition problem arithmetic approach", 24),
    Attempt("Luigi Salemi", "2009", Claim.P_EQ_NP, "3SAT O(n^11) algorithm", 25),
    Attempt("Narendra S. Chaudhari", "2009", Claim.P_EQ_NP, "3-SAT O(n^13) constructive procedure", 26),
    Attempt("Lizhi Du", "2010", Claim.P_EQ_NP, "Hamilton Cycle polynomial algorithm", 27),
    Attempt("Changlin Wan", "2010", Claim.P_EQ_NP, "Recursive Turing machine definition approach", 28),
    Attempt("Han Xiao Wen", "2010", Claim.P_EQ_NP, "Relation learning algorithm", 29),
    Attempt("Mikhail Katkov", "2010", Claim.P_EQ_NP, "Semi-definite program for Max-Cut", 30),
    Attempt("Vladimir Romanov", "2010", Claim.P_EQ_NP, "Compact triplets structures representation", 31),
    Attempt("Sergey Gubin", "2010", Claim.P_EQ_NP, "ATSP polynomial-size LP formulation", 32),
    Attempt("Stefan Jaeger", "2011", Claim.P_EQ_NP, "P=NP under first Peano axiom", 33),
    Attempt("Amar Mukherjee", "2011", Claim.P_EQ_NP, "Deterministic polynomial 3-satisfiability", 34),
    Attempt("Angela Weiss", "2011", Claim.P_EQ_NP, "Polynomial 3-sat using KE-tableaux", 35),
    Attempt("Matt Groff", "2011", Claim.P_EQ_NP, "O(n^7) satisfiability using linear algebra", 36),
    Attempt("Sergey Kardash", "2011", Claim.P_EQ_NP, "O(n^12) 3-SAT algorithm", 37),
    Attempt("Jason W. Steinmetz", "2011", Claim.P_EQ_NP, "Polynomial 3-SAT solution", 38),
    Attempt("Jose Ignacio Alvarez-Hamelin", "2011", Claim.P_EQ_NP, "Maximum clique efficient algorithm", 39),
    Attempt("Douglas Youvan", "2012", Claim.P_EQ_NP, "P=NP at light speed with zero-mass particles", 40),
    Attempt("Algirdas Antano Maknickas", "2011", Claim.P_EQ_NP, "Multi-nary logic k-SAT; LP formulation", 41),
    Attempt("Michel Feldmann", "2012", Claim.P_EQ_NP, "3-SAT reduction to linear programming", 42),
    Attempt("Wen-Qi Duan", "2012", Claim.P_EQ_NP, "TSP cost 0/1 approach to Hamiltonian cycle", 43),
    Attempt("Sergey V. Yakhontov", "2012", Claim.P_EQ_NP, "Deterministic algorithm for NTM acceptance", 44),
    Attempt("Louis Coder", "2012", Claim.P_EQ_NP, "Exact-3-SAT polynomial solver", 45),
    Attempt("Dmitriy Nuriyev", "2013", Claim.P_EQ_NP, "DP approach, O(n^8) Hamiltonian Path", 46),
    Attempt("Frederic Gillet", "2013", Claim.P_EQ_NP, "Conservative logic gates on flow networks", 47),
    Attempt("Hanlin Liu", "2014", Claim.P_EQ_NP, "O(|V|^9) Hamiltonian circuit algorithm", 48),
    Attempt("Pawan Tamta, B.P. Pande, H.S. Dhami", "2014", Claim.P_EQ_NP, "Clique problem maximum flow reduction", 49),
    Attempt("Peng Cui", "2014", Claim.P_EQ_NP, "CSP gap problem SDP algorithm approach", 50),
    Attempt("Anatoly Panyukov", "2014", Claim.P_EQ_NP, "Polynomial Hamiltonian circuit algorithm", 51),
    Attempt("Michael LaPlante", "2015", Claim.P_EQ_NP, "Polynomial maximum clique algorithm", 52),
    Attempt("Alejandro Sanchez Guinea", "2015", Claim.P_EQ_NP, "CNF satisfiability in polynomial time", 53),
    Attempt("Frank Vega", "2015", Claim.P_EQ_NP, "Equivalent-P class equivalence proof", 54),
    Attempt("Yubin Huang", "2015", Claim.P_EQ_NP, "Restricted NTM hierarchy approach", 55),
    Attempt("Steven Meyer", "2016", Claim.P_EQ_NP, "Philosophical solution via MRAM model", 56),
    Attempt("Eli Halylaurin", "2016", Claim.P_EQ_NP, "PSPACE included in P demonstration", 57),
    Attempt("Rafael Valls Hidalgo-Gato", "2009", Claim.P_EQ_NP, "Technical report; originally 1985", 58),

    # P≠NP attempts
    Attempt("Seenil Gram", "2001", Claim.P_NEQ_NP, "Indistinguishability Lemma", 100),
    Attempt("Hubert Chen", "2003", Claim.P_NEQ_NP, "Proof by contradiction", 101),
    Attempt("Craig Alan Feinstein", "2003", Claim.P_NEQ_NP, "Evidence in restricted computation model", 102),
    Attempt("Ki-Bong Nam, S.H. Wang, Yang Gon Kim", "2004", Claim.P_NEQ_NP, "Linear algebra/Lie algebra counterexample", 103),
    Attempt("Mikhail N. Kupchik", "2004", Claim.P_NEQ_NP, "Series of papers on P vs NP", 104),
    Attempt("Mircea Alexandru Popescu Moscu", "2004", Claim.P_NEQ_NP, "Complexity hierarchy invariance principle", 105),
    Attempt("Raju Renjit Grover", "2005", Claim.P_NEQ_NP, "All clique algorithms exponential worst-case", 106),
    Attempt("Viktor V. Ivanov", "2005", Claim.P_NEQ_NP, "Lower bound estimates", 107),
    Attempt("Bhupinder Singh Anand", "2005", Claim.P_NEQ_NP, "Provability approach", 108),
    Attempt("Craig Alan Feinstein", "2005", Claim.P_NEQ_NP, "Mabel-Mildred-Feinstein model", 109),
    Attempt("Lev Gordeev", "2005", Claim.P_NEQ_NP, "Proof-sketch via traditional combinatorics", 110),
    Attempt("Ron Cohen", "2005", Claim.P_NEQ_NP, "P ≠ intersection of NP and co-NP", 111),
    Attempt("Craig Alan Feinstein", "2006", Claim.P_NEQ_NP, "Elegant argument", 112),
    Attempt("Radoslaw Hofman", "2006", Claim.P_NEQ_NP, "Under deterministic calculation assumption", 113),
    Attempt("Raju Renjit", "2006", Claim.P_NEQ_NP, "co-NP equals NP", 114),
    Attempt("Rubens Ramos Viana", "2006", Claim.P_NEQ_NP, "Disentangled states and Chaitin Omega", 115),
    Attempt("Jerrald Meek", "2008", Claim.P_NEQ_NP, "Clause limit approach", 116),
    Attempt("Jerrald Meek", "2008", Claim.P_NEQ_NP, "Karp's theorem postulates analysis", 117),
    Attempt("Jorma Jormakka", "2008", Claim.P_NEQ_NP, "Subset sum cannot be polynomial", 118),
    Attempt("Sten-Ake Tarnlund", "2008", Claim.P_NEQ_NP, "First-order theory approach", 119),
    Attempt("Zohreh O. Akbari", "2008", Claim.P_NEQ_NP, "Deterministic clique algorithm", 120),
    Attempt("Javaid Aslam", "2008", Claim.P_NEQ_NP, "Hamiltonian circuit counting", 121),
    Attempt("Arto Annila", "2009", Claim.P_NEQ_NP, "Physical state space evolution argument", 122),
    Attempt("Andre Luiz Barbosa", "2009", Claim.P_NEQ_NP, "Artificial XG-SAT problem", 123),
    Attempt("Ari Blinder", "2009", Claim.P_NEQ_NP, "Language in NP not in co-NP", 124),
    Attempt("Carlos Barron-Romero", "2010", Claim.P_NEQ_NP, "NP-class complexity novel formulation", 125),
    Attempt("Frank Vega Delgado", "2010", Claim.P_NEQ_NP, "CERTIFYING problem approach", 126),
    Attempt("Carlos Barron-Romero", "2010", Claim.P_NEQ_NP, "Euclidean TSP vs assignment problem", 127),
    Attempt("Bangyan Wen and Yi Lin", "2010", Claim.P_NEQ_NP, "Formal logic reasoning", 128),
    Attempt("Ruijia Liao", "2011", Claim.P_NEQ_NP, "3SAT_N algorithms and pseudo-algorithms", 129),
    Attempt("Koji Kobayashi", "2011", Claim.P_NEQ_NP, "CHAOS language in NP\\AL", 130),
    Attempt("Roman Yampolskiy", "2011", Claim.P_NEQ_NP, "Hashed-Path TSP exponential lower bound", 131),
    Attempt("Craig Alan Feinstein", "2011", Claim.P_NEQ_NP, "TSP cannot solve in polynomial time", 132),
    Attempt("Jeffrey W. Holcomb", "2011", Claim.P_NEQ_NP, "Stochastic answers in NP-P difference", 133),
    Attempt("Gilberto Rodrigo Diduch", "2012", Claim.P_NEQ_NP, "Categorical rejection of P=NP", 134),
    Attempt("Koji Kobayashi", "2012", Claim.P_NEQ_NP, "Topological approach", 135),
    Attempt("Frank Vega Delgado", "2012", Claim.P_NEQ_NP, "P=UP leads to EXP=P contradiction", 136),
    Attempt("Minseong Kim", "2012", Claim.P_NEQ_NP, "ZFC inconsistency argument", 137),
    Attempt("Junichiro Fukuyama", "2012", Claim.P_NEQ_NP, "Clique computation intractability via topology", 138),
    Attempt("Satoshi Tazawa", "2012", Claim.P_NEQ_NP, "Integer factorization neither P nor NP-complete", 139),
    Attempt("Natalia L. Malinina", "2012", Claim.P_NEQ_NP, "Principal impossibility to prove P=NP", 140),
    Attempt("Rustem Chingizovich Valeyev", "2013", Claim.P_NEQ_NP, "TSP exhaustive search most effective", 141),
    Attempt("Daegene Song", "2014", Claim.P_NEQ_NP, "Quantum physics process in NP not P", 142),
    Attempt("Joonmo Kim", "2014", Claim.P_NEQ_NP, "Modus tollens artificial TM approach", 143),
    Attempt("Daniel Uribe", "2016", Claim.P_NEQ_NP, "Decision tree lower bound analysis", 144),
    Attempt("Frank Vega", "2016", Claim.P_NEQ_NP, "P=NP implies P=EXP contradiction", 145),
    Attempt("Mathias Hauptmann", "2016", Claim.P_NEQ_NP, "Sigma-2-p Union Theorem variant contradiction", 146),
    Attempt("Javier A. Arroyo-Figueroa", "2016", Claim.P_NEQ_NP, "One-way functions class existence", 147),
    Attempt("Stefan Rass", "2016", Claim.P_NEQ_NP, "Weak one-way functions existence", 148),

    # Other classifications
    Attempt("Nicholas Argall", "2003", Claim.UNDECIDABLE, "P=NP undecidable via Gödel's theorem", 200),
    Attempt("N.C.A. da Costa and F.A. Doria", "2003", Claim.UNPROVABLE, "P≠NP unprovable in ZFC", 201),
    Attempt("Stefan Jaeger", "2011", Claim.MODEL_DEPENDENT, "Both P=NP and P≠NP depending on axioms", 202),
]


def scan_attempt_directory(attempt_dir: Path) -> AttemptStructure:
    """Scan an attempt directory and check for required files."""
    structure = AttemptStructure()

    # Check for README.md
    readme_path = attempt_dir / "README.md"
    if readme_path.exists():
        structure.has_readme = True
        structure.readme_path = str(readme_path)

    # Check for Lean files
    lean_dir = attempt_dir / "lean"
    if lean_dir.exists():
        lean_files = list(lean_dir.glob("*.lean"))
        if lean_files:
            structure.has_lean = True
            structure.lean_files = [str(f) for f in lean_files]

    # Check for Coq files
    coq_dir = attempt_dir / "coq"
    if coq_dir.exists():
        coq_files = list(coq_dir.glob("*.v"))
        if coq_files:
            structure.has_coq = True
            structure.coq_files = [str(f) for f in coq_files]

    # Check for Isabelle files
    isabelle_dir = attempt_dir / "isabelle"
    if isabelle_dir.exists():
        isabelle_files = list(isabelle_dir.glob("*.thy"))
        if isabelle_files:
            structure.has_isabelle = True
            structure.isabelle_files = [str(f) for f in isabelle_files]

    # Check for papers directory
    papers_dir = attempt_dir / "papers"
    if papers_dir.exists() and any(papers_dir.iterdir()):
        structure.has_papers = True

    # Check for refutation (look for files with "refutation" or "counter" in name)
    for subdir in [lean_dir, coq_dir, isabelle_dir]:
        if subdir and subdir.exists():
            for file in subdir.iterdir():
                if any(keyword in file.name.lower() for keyword in ['refut', 'counter', 'error']):
                    structure.has_refutation = True
                    break

    return structure


def get_existing_attempts(base_dir: Path) -> Dict[str, AttemptStructure]:
    """Get all existing attempts from the proofs/attempts directory."""
    attempts_dir = base_dir / "proofs" / "attempts"
    existing = {}

    if not attempts_dir.exists():
        return existing

    for item in attempts_dir.iterdir():
        if item.is_dir():
            structure = scan_attempt_directory(item)
            existing[item.name] = structure

    return existing


def match_woeginger_to_existing(woeginger: List[Attempt],
                                 existing: Dict[str, AttemptStructure]) -> Tuple[Dict, Dict, List]:
    """
    Match Woeginger attempts to existing directories.

    Returns:
        matched: Dict mapping Woeginger attempt to existing directory
        unmatched_woeginger: List of Woeginger attempts with no match
        unmatched_existing: List of existing directories with no clear Woeginger match
    """
    matched = {}
    unmatched_woeginger = []
    unmatched_existing = set(existing.keys())

    for attempt in woeginger:
        normalized = attempt.get_normalized_name()
        found = False

        # Try exact match
        if normalized in existing:
            matched[attempt] = normalized
            unmatched_existing.discard(normalized)
            found = True
        else:
            # Try fuzzy matching
            for dir_name in existing.keys():
                # Check if author and year are in the directory name
                author_parts = attempt.author.lower().split()
                year_in_name = attempt.year in dir_name
                author_in_name = any(part in dir_name for part in author_parts if len(part) > 3)

                if year_in_name and author_in_name:
                    matched[attempt] = dir_name
                    unmatched_existing.discard(dir_name)
                    found = True
                    break

        if not found:
            unmatched_woeginger.append(attempt)

    return matched, unmatched_woeginger, list(unmatched_existing)


def generate_report(base_dir: Path) -> Dict:
    """Generate a comprehensive report on attempt coverage and completeness."""
    existing = get_existing_attempts(base_dir)
    matched, unmatched_woeginger, unmatched_existing = match_woeginger_to_existing(
        WOEGINGER_ATTEMPTS, existing
    )

    # Check completeness of matched attempts
    incomplete_attempts = []
    complete_attempts = []

    for attempt, dir_name in matched.items():
        structure = existing[dir_name]
        if not structure.is_complete():
            incomplete_attempts.append({
                'attempt': attempt,
                'directory': dir_name,
                'structure': structure,
                'missing': structure.get_missing_components()
            })
        else:
            complete_attempts.append({
                'attempt': attempt,
                'directory': dir_name,
                'structure': structure
            })

    report = {
        'summary': {
            'total_woeginger': len(WOEGINGER_ATTEMPTS),
            'total_existing': len(existing),
            'matched': len(matched),
            'complete': len(complete_attempts),
            'incomplete': len(incomplete_attempts),
            'missing_from_repo': len(unmatched_woeginger),
            'unmatched_in_repo': len(unmatched_existing)
        },
        'complete_attempts': complete_attempts,
        'incomplete_attempts': incomplete_attempts,
        'missing_attempts': unmatched_woeginger,
        'unmatched_directories': unmatched_existing
    }

    return report


def print_report(report: Dict):
    """Print a human-readable report."""
    summary = report['summary']

    print("=" * 80)
    print("P vs NP ATTEMPTS - COMPLETENESS REPORT")
    print("=" * 80)
    print()

    print("SUMMARY")
    print("-" * 80)
    print(f"Total attempts in Woeginger's list: {summary['total_woeginger']}")
    print(f"Total attempts in repository:      {summary['total_existing']}")
    print(f"Matched attempts:                   {summary['matched']}")
    print(f"Complete formalizations:            {summary['complete']}")
    print(f"Incomplete formalizations:          {summary['incomplete']}")
    print(f"Missing from repository:            {summary['missing_from_repo']}")
    print(f"Unmatched directories:              {summary['unmatched_in_repo']}")
    print()

    # Print missing attempts
    if report['missing_attempts']:
        print("MISSING ATTEMPTS (Not in repository)")
        print("-" * 80)
        for attempt in report['missing_attempts']:
            print(f"  [{attempt.woeginger_id}] {attempt.author} ({attempt.year}) - {attempt.claim.value}")
            print(f"      {attempt.description}")
            print(f"      Expected directory: {attempt.get_normalized_name()}")
            print()

    # Print incomplete attempts
    if report['incomplete_attempts']:
        print("INCOMPLETE ATTEMPTS (Missing required files)")
        print("-" * 80)
        for item in report['incomplete_attempts']:
            attempt = item['attempt']
            print(f"  [{attempt.woeginger_id}] {attempt.author} ({attempt.year})")
            print(f"      Directory: {item['directory']}")
            print(f"      Missing: {', '.join(item['missing'])}")
            print()

    # Print unmatched directories
    if report['unmatched_directories']:
        print("UNMATCHED DIRECTORIES (In repo but not matched to Woeginger's list)")
        print("-" * 80)
        for dir_name in report['unmatched_directories']:
            print(f"  {dir_name}")
        print()

    # Print statistics by claim type
    print("STATISTICS BY CLAIM TYPE")
    print("-" * 80)
    claims_stats = {}
    for attempt in WOEGINGER_ATTEMPTS:
        claim = attempt.claim.value
        if claim not in claims_stats:
            claims_stats[claim] = {'total': 0, 'matched': 0, 'complete': 0}
        claims_stats[claim]['total'] += 1

    for item in report['complete_attempts']:
        claim = item['attempt'].claim.value
        claims_stats[claim]['matched'] += 1
        claims_stats[claim]['complete'] += 1

    for item in report['incomplete_attempts']:
        claim = item['attempt'].claim.value
        claims_stats[claim]['matched'] += 1

    for claim, stats in sorted(claims_stats.items()):
        print(f"  {claim}:")
        print(f"    Total in Woeginger: {stats['total']}")
        print(f"    Matched:            {stats['matched']}")
        print(f"    Complete:           {stats['complete']}")
        print()

    print("=" * 80)


def save_json_report(report: Dict, output_path: Path):
    """Save report as JSON file."""
    # Convert Attempt objects to dicts for JSON serialization
    json_report = {
        'summary': report['summary'],
        'complete_attempts': [
            {
                'attempt': asdict(item['attempt']),
                'directory': item['directory'],
                'has_lean': item['structure'].has_lean,
                'has_coq': item['structure'].has_coq,
                'has_isabelle': item['structure'].has_isabelle,
            }
            for item in report['complete_attempts']
        ],
        'incomplete_attempts': [
            {
                'attempt': asdict(item['attempt']),
                'directory': item['directory'],
                'missing': item['missing'],
                'has_lean': item['structure'].has_lean,
                'has_coq': item['structure'].has_coq,
                'has_isabelle': item['structure'].has_isabelle,
            }
            for item in report['incomplete_attempts']
        ],
        'missing_attempts': [
            {
                **asdict(attempt),
                'suggested_directory': attempt.get_normalized_name()
            }
            for attempt in report['missing_attempts']
        ],
        'unmatched_directories': report['unmatched_directories']
    }

    # Custom JSON encoder for Enum
    class EnumEncoder(json.JSONEncoder):
        def default(self, obj):
            if isinstance(obj, Enum):
                return obj.value
            return super().default(obj)

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(json_report, f, indent=2, cls=EnumEncoder)


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Check P vs NP attempts against Woeginger\'s list'
    )
    parser.add_argument(
        '--base-dir',
        type=Path,
        default=Path.cwd(),
        help='Base directory of the repository (default: current directory)'
    )
    parser.add_argument(
        '--json',
        type=Path,
        help='Save JSON report to specified file'
    )

    args = parser.parse_args()

    # Generate report
    report = generate_report(args.base_dir)

    # Print report
    print_report(report)

    # Save JSON if requested
    if args.json:
        save_json_report(report, args.json)
        print(f"\nJSON report saved to: {args.json}")


if __name__ == '__main__':
    main()
