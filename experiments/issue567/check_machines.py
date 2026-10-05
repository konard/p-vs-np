#!/usr/bin/env python3
"""Compile paired regressions and require four invalid proof mutations to fail.

These checks cover syntax-machine runs and finite verifier semantics. They do
not substitute for the still-missing circuit evaluator or membership theorem.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

LEAN_HEADER = """import proofs.experiments.issue567.lean.CircuitSyntax
open Complexity Issue532.Idea41 Issue567.CircuitSyntax
"""
ROCQ_HEADER = """From Stdlib Require Import List Bool Arith.
Import ListNotations.
From proofs.experiments.issue567.rocq Require Import CircuitSyntax.
From proofs.experiments.issue532.rocq Require Import Idea41.
Import Complexity Machines Circuits CircuitSyntax.
"""

# Each semantic mutation removes one check from the actual verifier definition.
# The zero-step mutation attempts to use a halting instruction without its cost.
MUTATIONS = {
    "zero_step": (
        "example : Run circuitSyntaxMachine (pairedInput [] []) 0 false := by\n"
        "  apply Run.halt\n  rfl\n",
        "Example mutation : Run circuitSyntaxMachine (pairedInput [] []) 0 false.\n"
        "Proof. apply run_halt. reflexivity. Qed.\n",
    ),
    "ignore_certificate": (
        "def mutated (x _cert : Word) := verifyCircuit x [false]\n"
        "example : mutated (encCircuit 1 []) [true] = true := by decide\n",
        "Definition mutated (x _cert : Word) := verifyCircuit x [false].\n"
        "Example mutation : mutated (encCircuit 1 []) [true] = true.\n"
        "Proof. reflexivity. Qed.\n",
    ),
    "wrong_length": (
        "def mutated (x cert : Word) := match decCircuit x with\n"
        "  | none => false\n  | some (n, C) => wfFromb n C && Issue532.Circuits.output cert C\n"
        "example : mutated (encCircuit 1 [(0, 0)]) [] = false := by decide\n",
        "Definition mutated (x cert : Word) := match decCircuit x with\n"
        "  | None => false | Some (n, C) => wfFromb n C && output cert C end.\n"
        "Example mutation : mutated (encCircuit 1 [(0, 0)]) [] = false.\n"
        "Proof. reflexivity. Qed.\n",
    ),
    "forward_wire": (
        "def mutated (x cert : Word) := match decCircuit x with\n"
        "  | none => false\n  | some (n, C) => decide (cert.length = n) && Issue532.Circuits.output cert C\n"
        "example : mutated (encCircuit 1 [(0, 1)]) [false] = false := by decide\n",
        "Definition mutated (x cert : Word) := match decCircuit x with\n"
        "  | None => false | Some (n, C) => Nat.eqb (length cert) n && output cert C end.\n"
        "Example mutation : mutated (encCircuit 1 [(0, 1)]) [false] = false.\n"
        "Proof. reflexivity. Qed.\n",
    ),
}


def compile_probe(language: str, path: Path, log: Path) -> subprocess.CompletedProcess:
    command = ["lake", "env", "lean"] if language == "lean" else ["rocq", "compile", "-Q", ".", ""]
    result = subprocess.run([*command, str(path)], cwd=ROOT, capture_output=True, text=True)
    log.write_text(result.stdout + result.stderr, encoding="utf-8")
    return result


def check(language: str) -> None:
    logs = HERE / "logs"
    logs.mkdir(exist_ok=True)
    suffix = ".lean" if language == "lean" else ".v"
    baseline = compile_probe(language, HERE / f"MachineRegression{suffix}", logs / f"{language}-regression.log")
    if baseline.returncode:
        raise RuntimeError(f"{language} regression failed; see {logs}")
    header, index = (LEAN_HEADER, 0) if language == "lean" else (ROCQ_HEADER, 1)
    with tempfile.TemporaryDirectory(prefix="machine_mutations_", dir=HERE) as directory:
        for name, bodies in MUTATIONS.items():
            probe = Path(directory) / f"Mutation_{name}{suffix}"
            probe.write_text(header + bodies[index], encoding="utf-8")
            result = compile_probe(language, probe, logs / f"{language}-{name}.log")
            if not result.returncode:
                raise RuntimeError(f"{language} accepted mutation {name}")
            # Missing imports/names would give a spurious passing mutation test.
            output = result.stdout + result.stderr
            if language == "lean":
                expected = (
                    ("could not unify the conclusion of `@Run.halt`",)
                    if name == "zero_step"
                    else ("Tactic `decide` proved that the proposition", "is false")
                )
            else:
                expected = ("Unable to unify",)
            if not all(reason in output for reason in expected):
                raise RuntimeError(f"{language} mutation {name} failed for an unexpected reason; see {logs}")
            print(f"{language}: rejected {name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--rocq", action="store_true")
    args = parser.parse_args()
    selected = [language for language in ("lean", "rocq") if getattr(args, language)]
    for language in selected or ["lean", "rocq"]:
        check(language)


if __name__ == "__main__":
    main()
