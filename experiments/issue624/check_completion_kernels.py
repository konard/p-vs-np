#!/usr/bin/env python3
"""Exercise completion type checks with real kernels, including hidden premises.

The declarations are injected into temporary probes by the shared assumption
checker. They use only the shared complexity model and no admissions/axioms.
"""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.check_proof_status import ROOT, query_assumptions


LEAN = """open Complexity
namespace CompletionProbe
def Requirement := True
def Alias := Requirement
theorem complete : Requirement := True.intro
theorem explicit (h : Requirement) : Requirement := h
theorem implicit {h : Requirement} : Requirement := h
theorem aliased {h : Alias} : Requirement := h
theorem restricted (_ : Unit) : Requirement := True.intro
def perInput (_ : Word) : Machine := ⟨[]⟩
end CompletionProbe
"""

ROCQ = """Import Complexity.Complexity.
Module CompletionProbe.
Definition Requirement := True.
Definition Alias := Requirement.
Theorem complete : Requirement. Proof. exact I. Qed.
Theorem explicit (h : Requirement) : Requirement. Proof. exact h. Qed.
Theorem implicit {h : Requirement} : Requirement. Proof. exact h. Qed.
Theorem aliased {h : Alias} : Requirement. Proof. exact h. Qed.
Theorem restricted (_ : unit) : Requirement. Proof. exact I. Qed.
Definition perInput (_ : Word) : Machine := {| program := nil |}.
End CompletionProbe.
"""


def check(language):
    suffix = "lean" if language == "lean" else "v"
    preamble = LEAN if language == "lean" else ROCQ
    source = f"proofs/complexity/{language}/Complexity.{suffix}"
    for name in ("complete", "explicit", "implicit", "aliased", "restricted", "perInput"):
        entry = {"source": source, "theorem": f"CompletionProbe.{name}"}
        # First prove this is a valid, admission-free declaration. A broken
        # import or probe must not count as successful rejection of its type.
        assumptions = query_assumptions(ROOT, language, entry, preamble=preamble)
        if assumptions:
            raise ValueError(f"{language} fixture {name} has assumptions: {assumptions}")
        expected = "Machine" if name == "perInput" else "CompletionProbe.Requirement"
        if name == "restricted":
            expected = ("∀ (_ : ClassNP), CompletionProbe.Requirement" if language == "lean"
                        else "forall (_ : ClassNP), CompletionProbe.Requirement")
        try:
            query_assumptions(ROOT, language, entry, expected_type=expected, preamble=preamble)
        except ValueError:
            if name == "complete":
                raise
            print(f"{language}: kernel rejected {name} at the unconditional type")
        else:
            if name != "complete":
                raise ValueError(f"{language}: kernel accepted unwanted premise/input for {name}")
            print(f"{language}: kernel accepted the complete contract")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    language = parser.add_mutually_exclusive_group(required=True)
    language.add_argument("--lean", action="store_true")
    language.add_argument("--rocq", action="store_true")
    arguments = parser.parse_args()
    check("lean" if arguments.lean else "rocq")


if __name__ == "__main__":
    main()
