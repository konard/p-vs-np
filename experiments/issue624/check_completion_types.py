#!/usr/bin/env python3
"""Type-check the gate's expected propositions, without asserting their proofs.

Dummy data functions live in a probe-only namespace, never in CookLevin or the
certified manifest. This catches misspelled model names and ill-formed contract
types even while the actual Cook-Levin declarations are absent.
"""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.check_issue624_completion import REQUIREMENTS
from scripts.check_proof_status import ROOT


MODULES = [
    ("issue532", name) for name in ("Machines", "SATVerifier", "Idea01", "Idea14", "Idea32", "Idea36", "Idea37", "Idea41")
] + [("issue609", "PEqualsNPAttempt"), ("issue7", "ClockedSAT"), ("issue8", "NPSubsetP"), ("issue624", "FixedWindow")]

LEAN_DATA = """open Complexity Issue532.Machines
namespace CompletionTypeProbe
def tableauCNF (_ : ClassNP) (_ : Word) : _root_.Issue532.Machines.CNF := []
def decodeTrace (_ : ClassNP) (_ : Word) (_ : _root_.Issue532.Machines.Assignment) : List Config := []
def sizePolynomial (_ : ClassNP) : Polynomial := ⟨0, 0⟩
def red (_ : ClassNP) : Machine := ⟨[]⟩
def timePolynomial (_ : ClassNP) : Polynomial := ⟨0, 0⟩
end CompletionTypeProbe
"""

ROCQ_DATA = """From Stdlib Require Import List.
Import ListNotations Complexity.Complexity.
Module SharedComplexity := proofs.complexity.rocq.Complexity.Complexity.
Module SharedSAT := proofs.experiments.issue532.rocq.Machines.
Module CompletionTypeProbe.
Definition tableauCNF (_ : SharedComplexity.ClassNP) (_ : SharedComplexity.Word) : SharedSAT.CNF := nil.
Definition decodeTrace (_ : SharedComplexity.ClassNP) (_ : SharedComplexity.Word)
  (_ : SharedSAT.Assignment) : list SharedComplexity.Config := nil.
Definition sizePolynomial (_ : SharedComplexity.ClassNP) : SharedComplexity.Polynomial :=
  {| SharedComplexity.coefficient := 0; SharedComplexity.degree := 0 |}.
Definition red (_ : SharedComplexity.ClassNP) : SharedComplexity.Machine := {| SharedComplexity.program := nil |}.
Definition timePolynomial (_ : SharedComplexity.ClassNP) : SharedComplexity.Polynomial :=
  {| SharedComplexity.coefficient := 0; SharedComplexity.degree := 0 |}.
End CompletionTypeProbe.
"""


def check(language):
    if language == "lean":
        source = "".join(f"import proofs.experiments.{issue}.lean.{name}\n" for issue, name in MODULES)
        source += LEAN_DATA
        for requirement in REQUIREMENTS:
            expected = requirement.lean_type.replace("Issue624.CookLevin.", "CompletionTypeProbe.")
            source += f"#check ({expected} : Prop)\n"
        command, suffix = ["lake", "env", "lean"], ".lean"
    else:
        source = "".join(f"From proofs.experiments.{issue}.rocq Require Import {name}.\n" for issue, name in MODULES)
        source += ROCQ_DATA
        for index, requirement in enumerate(REQUIREMENTS):
            expected = requirement.rocq_type.replace("CookLevin.", "CompletionTypeProbe.")
            source += f"Definition contract_type_{index} : Prop := {expected}.\n"
        command, suffix = ["rocq", "compile", "-Q", ".", ""], ".v"
    with tempfile.TemporaryDirectory(prefix="completion_types_") as directory:
        probe = Path(directory) / f"ContractTypes{suffix}"
        probe.write_text(source)
        result = subprocess.run([*command, str(probe)], cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise ValueError(result.stdout + result.stderr)
    print(f"{language}: all {len(REQUIREMENTS)} expected propositions type-check (no proofs asserted)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--lean", action="store_true")
    group.add_argument("--rocq", action="store_true")
    arguments = parser.parse_args()
    check("lean" if arguments.lean else "rocq")


if __name__ == "__main__":
    main()
