#!/usr/bin/env python3
"""Fail until the complete paired Cook-Levin deliverable of issue #624 exists.

The ordinary certified-result audit permits explicit theorem premises. This
gate additionally requires the endpoint entries and asks the kernels to check
their unapplied types. Prerequisite certification cannot satisfy these types.
"""

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.check_proof_status import (
    MANIFEST, ROOT, check_sources, query_assumptions, source_closure,
    strip_comments_and_strings,
)


ALLOWED = {
    "lean": {"propext", "Classical.choice", "Quot.sound"},
    "rocq": {"Classical_Prop.classic"},
}


@dataclass(frozen=True)
class Requirement:
    lean_name: str
    rocq_name: str
    lean_type: str
    rocq_type: str

    def name(self, language):
        return getattr(self, f"{language}_name")

    def type(self, language):
        return getattr(self, f"{language}_type")


def contract(namespace, name, lean_type, rocq_type):
    """Pair public names and anchor the contracts to the shared model."""
    complexity = {"ClassNP", "Word", "Machine", "Polynomial", "step", "InP", "PEqualsNP", "PNotEqualsNP"}
    machines = {"evalCNF", "Satisfiable", "encodeCNF", "Computes", "SATHard", "CookLevin", "SAT", "DecidesWithin"}
    rocq_fields = {"np_language", "np_certBound", "np_verifier", "evalPoly"}

    def qualify(expected, language):
        if language == "rocq":
            modules = {name: f"proofs.experiments.issue532.rocq.{name}"
                       for name in ("Idea01", "Idea14", "Idea32", "Idea36", "Idea37", "Idea41")}
            modules.update({
                "PEqualsNPAttempt": "proofs.experiments.issue609.rocq.PEqualsNPAttempt",
                "ClockedSAT": "proofs.experiments.issue7.rocq.ClockedSAT",
                "NPSubsetP": "proofs.experiments.issue8.rocq.NPSubsetP",
                **{name: f"proofs.experiments.issue624.rocq.{name}.{name}"
                   for name in ("FixedWindow", "CertificateCNF", "VerifierTableau")},
            })
            expected = re.sub(r"(?<![\w.])(" + "|".join(modules) + r")\.",
                              lambda match: modules[match[1]] + ".", expected)
        names = complexity | machines | (rocq_fields if language == "rocq" else set())
        pattern = r"(?<![\w.])(?:" + "|".join(sorted(names)) + r")(?![\w.])"

        def shared(match):
            word = match[0]
            if language == "lean":
                prefix = "_root_.Complexity" if word in complexity else "_root_.Issue532.Machines"
            else:
                prefix = ("proofs.complexity.rocq.Complexity.Complexity" if word in complexity | rocq_fields
                          else "proofs.experiments.issue532.rocq.Machines")
            return f"{prefix}.{word}"

        return re.sub(pattern, shared, expected)

    return Requirement(f"{namespace}.{name}", f"{namespace.split('.')[-1]}.{name}",
                       qualify(lean_type, "lean"), qualify(rocq_type, "rocq"))


# The construction may live in separate modules. CookLevin exports this stable
# interface; each manifest entry selects its actual defining source. All model
# predicates in these types are the existing shared definitions.
CL = "Issue624.CookLevin"
REQUIREMENTS = (
    contract(CL, "tableauCNF_sound",
             "∀ (np : ClassNP) (x : Word) a, evalCNF a (Issue624.CookLevin.tableauCNF np x) = true → "
             "Issue624.FixedWindow.WindowVerifierTableau np x a (Issue624.CookLevin.decodeTrace np x a)",
             "forall (np : ClassNP) (x : Word) a, evalCNF a (CookLevin.tableauCNF np x) = true -> "
             "FixedWindow.WindowVerifierTableau np x a (CookLevin.decodeTrace np x a)"),
    contract(CL, "tableauCNF_complete",
             "∀ (np : ClassNP) (x : Word) a trace, Issue624.FixedWindow.WindowVerifierTableau np x a trace → "
             "∃ b, evalCNF b (Issue624.CookLevin.tableauCNF np x) = true ∧ "
             "Issue624.CertificateCNF.decodeCertificate b 0 (np.certBound.eval x.length) = "
             "Issue624.CertificateCNF.decodeCertificate a 0 (np.certBound.eval x.length) ∧ "
             "Issue624.CookLevin.decodeTrace np x b = trace",
             "forall (np : ClassNP) (x : Word) a trace, FixedWindow.WindowVerifierTableau np x a trace -> "
             "exists b, evalCNF b (CookLevin.tableauCNF np x) = true /\\ "
             "CertificateCNF.decodeCertificate b 0 (evalPoly (np_certBound np) (length x)) = "
             "CertificateCNF.decodeCertificate a 0 (evalPoly (np_certBound np) (length x)) /\\ "
             "CookLevin.decodeTrace np x b = trace"),
    contract(CL, "tableauCNF_iff",
             "∀ (np : ClassNP) (x : Word), Satisfiable (Issue624.CookLevin.tableauCNF np x) ↔ np.language x = true",
             "forall (np : ClassNP) (x : Word), Satisfiable (CookLevin.tableauCNF np x) <-> np_language np x = true"),
    contract(CL, "tableauCNF_encoded_size",
             "∀ (np : ClassNP) (x : Word), (encodeCNF (Issue624.CookLevin.tableauCNF np x)).length ≤ "
             "(Issue624.CookLevin.sizePolynomial np).eval x.length",
             "forall (np : ClassNP) (x : Word), length (encodeCNF (CookLevin.tableauCNF np x)) <= "
             "evalPoly (CookLevin.sizePolynomial np) (length x)"),
    contract(CL, "red_computes",
             "∀ (np : ClassNP), Computes (Issue624.CookLevin.red np) "
             "(fun x => encodeCNF (Issue624.CookLevin.tableauCNF np x)) (Issue624.CookLevin.timePolynomial np)",
             "forall (np : ClassNP), Computes (CookLevin.red np) "
             "(fun x => encodeCNF (CookLevin.tableauCNF np x)) (CookLevin.timePolynomial np)"),
    contract(CL, "satHard", "SATHard", "SATHard"),
    contract(CL, "cookLevin", "CookLevin", "CookLevin"),
    contract(CL, "tableauCNF_rejecting_unsatisfiable",
             "∀ (np : ClassNP) (x : Word), (∀ w, np.language w = false) → ¬ Satisfiable (Issue624.CookLevin.tableauCNF np x)",
             "forall (np : ClassNP) (x : Word), (forall w, np_language np w = false) -> ~ Satisfiable (CookLevin.tableauCNF np x)"),
    contract(CL, "tableauCNF_overlong_rejected",
             "∀ (np : ClassNP) (x cert : Word) a, np.certBound.eval x.length < cert.length → "
             "(∀ v, v ≤ 2 * np.certBound.eval x.length → "
             "a v = Issue624.CertificateCNF.encodeCertificate cert v) → "
             "evalCNF a (Issue624.CookLevin.tableauCNF np x) = false",
             "forall (np : ClassNP) (x cert : Word) a, evalPoly (np_certBound np) (length x) < length cert -> "
             "(forall v, v <= 2 * evalPoly (np_certBound np) (length x) -> "
             "a v = CertificateCNF.encodeCertificate cert v) -> "
             "evalCNF a (CookLevin.tableauCNF np x) = false"),
    contract(CL, "tableauCNF_wrong_successor_rejected",
             "∀ (np : ClassNP) (x : Word) a c d rest, step (Issue624.VerifierTableau.verifierMachine np.verifier) c ≠ Sum.inr d → "
             "Issue624.CookLevin.decodeTrace np x a = c :: d :: rest → "
             "evalCNF a (Issue624.CookLevin.tableauCNF np x) = false",
             "forall (np : ClassNP) (x : Word) a c d rest, step (VerifierTableau.verifierMachine (np_verifier np)) c <> inr d -> "
             "CookLevin.decodeTrace np x a = c :: d :: rest -> evalCNF a (CookLevin.tableauCNF np x) = false"),
    contract("Issue532.Machines", "pEqualsNP_of_inP_sat", "InP SAT → PEqualsNP", "InP SAT -> PEqualsNP"),
    contract("Issue532.Machines", "inP_sat_iff", "InP SAT ↔ PEqualsNP", "InP SAT <-> PEqualsNP"),
    contract("Issue532.SATVerifier", "inP_sat_iff_of_hard", "InP SAT ↔ PEqualsNP", "InP SAT <-> PEqualsNP"),
    contract("Issue532.Idea01", "pEqualsNP_of_polySATDecider",
             "Issue532.Idea01.PolySATDecider → PEqualsNP", "Idea01.PolySATDecider -> PEqualsNP"),
    contract("Issue532.Idea01", "polySATDecider_iff",
             "Issue532.Idea01.PolySATDecider ↔ PEqualsNP", "Idea01.PolySATDecider <-> PEqualsNP"),
    contract("Issue532.Idea01", "polySATDecider_iff_of_hard",
             "Issue532.Idea01.PolySATDecider ↔ PEqualsNP", "Idea01.PolySATDecider <-> PEqualsNP"),
    contract("Issue609.PEqualsNPAttempt", "pEqualsNP_of_candidate",
             "Issue609.PEqualsNPAttempt.Candidate → PEqualsNP", "PEqualsNPAttempt.Candidate -> PEqualsNP"),
    contract("Issue609.PEqualsNPAttempt", "candidate_iff_pEqualsNP",
             "Nonempty Issue609.PEqualsNPAttempt.Candidate ↔ PEqualsNP",
             "(exists c : PEqualsNPAttempt.Candidate, True) <-> PEqualsNP"),
    contract("Issue7.ClockedSAT", "pEqualsNP_of_clockedSAT",
             "Issue7.ClockedSAT.ClockedSAT → PEqualsNP", "ClockedSAT.ClockedSAT -> PEqualsNP"),
    contract("Issue7.ClockedSAT", "clockedSAT_iff_pEqualsNP",
             "Issue7.ClockedSAT.ClockedSAT ↔ PEqualsNP", "ClockedSAT.ClockedSAT <-> PEqualsNP"),
    contract("Issue7.ClockedSAT", "pi2_of_pNotEqualsNP",
             "PNotEqualsNP → ∀ (m : Machine) (p : Polynomial), ∃ x, Issue7.ClockedSAT.clockCheck m p x = false",
             "PNotEqualsNP -> forall (m : Machine) (p : Polynomial), exists x, ClockedSAT.clockCheck m p x = false"),
    contract("Issue8.NPSubsetP", "npSubsetP_iff_inP_sat",
             "Issue8.NPSubsetP.NPSubsetP ↔ InP SAT", "NPSubsetP.NPSubsetP <-> InP SAT"),
    contract("Issue8.NPSubsetP", "npSubsetP_iff_candidate",
             "Issue8.NPSubsetP.NPSubsetP ↔ Nonempty Issue609.PEqualsNPAttempt.Candidate",
             "NPSubsetP.NPSubsetP <-> (exists c : PEqualsNPAttempt.Candidate, True)"),
    contract("Issue8.NPSubsetP", "npSubsetP_of_dpll_machine",
             "∀ (m : Machine) (p : Polynomial), DecidesWithin m p Issue8.NPSubsetP.dpllSAT → Issue8.NPSubsetP.NPSubsetP",
             "forall (m : Machine) (p : Polynomial), DecidesWithin m p NPSubsetP.dpllSAT -> NPSubsetP.NPSubsetP"),
    contract("Issue532.Idea41", "fastCircuitSAT_of_inP_sat",
             "Issue532.Idea41.CircuitSATInNP → InP SAT → Issue532.Idea41.FastCircuitSAT",
             "Idea41.CircuitSATInNP -> InP SAT -> Idea41.FastCircuitSAT"),
    contract("Issue532.Idea14", "rp_route_gives_pEqualsNP",
             "Issue532.Idea14.NPinRP → Issue532.Idea14.SeedCompression SAT → Issue532.Idea14.SeedEnumeration → PEqualsNP",
             "Idea14.NPinRP -> Idea14.SeedCompression SAT -> Idea14.SeedEnumeration -> PEqualsNP"),
    contract("Issue532.Idea32", "isolation_route_gives_pEqualsNP",
             "Issue532.Idea32.IsolationObligation → Issue532.Idea32.PromiseSolver → PEqualsNP",
             "Idea32.IsolationObligation -> Idea32.PromiseSolver -> PEqualsNP"),
    # Idea 36 has a separate VCHard obligation, not a SATHard/CookLevin
    # parameter. This gate preserves its existing non-SAT premises.
    contract("Issue532.Idea36", "exactRounding_gives_pEqualsNP",
             "Issue532.Idea36.VCHard → Issue532.Idea36.CoverCheckInP → Issue532.Idea36.ExactRoundingObligation → PEqualsNP",
             "Idea36.VCHard -> Idea36.CoverCheckInP -> Idea36.ExactRoundingObligation -> PEqualsNP"),
    contract("Issue532.Idea37", "logParam_route_gives_pEqualsNP",
             "Issue532.Idea37.LogParamFPTObligation → PEqualsNP", "Idea37.LogParamFPTObligation -> PEqualsNP"),
)


def declaration_header(source, language, name):
    source = strip_comments_and_strings(source, language)
    short = re.escape(name.split(".")[-1])
    keywords = ("theorem|lemma|def|abbrev" if language == "lean"
                else "Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition")
    end = r":=" if language == "lean" else r":=|\.(?=\s|$)"
    match = re.search(rf"\b(?:{keywords})\s+{short}(?![\w'.])(.*?)(?:{end})", source, re.S)
    if match is None:
        raise ValueError(f"missing declaration {name}")
    return match.group(1), source.count("\n", 0, match.start()) + 1


def audit_completion(root, manifest, languages, query):
    failures = []
    selected = []
    for language in languages:
        entries = manifest.get(language, [])
        sources = []
        for requirement in REQUIREMENTS:
            name = requirement.name(language)
            matches = [entry for entry in entries if entry.get("theorem") == name]
            if len(matches) != 1:
                reason = "missing certified result" if not matches else "duplicate certified result"
                failures.append(f"{language}: {reason}: {name}")
                continue
            entry = matches[0]
            unexpected = set(entry["allowed_axioms"]) - ALLOWED[language]
            if unexpected:
                failures.append(f"{language} {name}: disallowed assumption policy: {', '.join(sorted(unexpected))}")
            path = root / entry["source"]
            suffix = ".lean" if language == "lean" else ".v"
            if path.suffix != suffix or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
                failures.append(f"{language} {name}: missing or invalid source: {entry['source']}")
                continue
            try:
                header, line = declaration_header(path.read_text(), language, name)
                # The endpoint's conclusion may itself be SATHard/CookLevin;
                # occurrences in its parameters still cause failure.
                leaf = name.split(".")[-1]
                if leaf in ("satHard", "cookLevin"):
                    conclusion = "SATHard" if leaf == "satHard" else "CookLevin"
                    header = re.sub(rf":\s*(?:\w+\.)*{conclusion}\s*$", "", header)
                if re.search(r"\b(?:SATHard|CookLevin)(?![\w.])", header):
                    failures.append(f"{entry['source']}:{line}: {name}: explicit hardness premise remains")
            except ValueError as error:
                failures.append(f"{entry['source']}: {error}")
            sources.append(entry)
            selected.append((language, requirement, entry))
        try:
            failures.extend(check_sources(root, source_closure(root, sources)))
        except (ValueError, OSError) as error:
            failures.append(f"{language}: {error}")
    if query and not failures:
        for language, requirement, entry in selected:
            preamble = ("open Complexity Issue532.Machines\n" if language == "lean"
                        else "From Stdlib Require Import List.\n"
                        "From proofs.experiments.issue532.rocq Require Import Machines.\n"
                        "Import ListNotations Complexity.Complexity.\n")
            try:
                assumptions = query_assumptions(root, language, entry,
                                               expected_type=requirement.type(language), preamble=preamble)
                print(f"{language} {entry['theorem']}: type checked; assumptions: "
                      f"{', '.join(sorted(assumptions)) or '(none)'}")
                unexpected = assumptions - set(entry["allowed_axioms"])
                if unexpected:
                    failures.append(f"{language} {entry['theorem']}: unapproved assumptions: {', '.join(sorted(unexpected))}")
            except (ValueError, OSError) as error:
                failures.append(str(error))
    return failures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="kernel-check Lean types and assumptions")
    parser.add_argument("--rocq", action="store_true", help="kernel-check Rocq types and assumptions")
    arguments = parser.parse_args()
    languages = [name for name in ("lean", "rocq") if getattr(arguments, name)]
    try:
        manifest = json.loads(MANIFEST.read_text())
        failures = audit_completion(ROOT, manifest, languages or ["lean", "rocq"], bool(languages))
    except (ValueError, KeyError, TypeError, OSError) as error:
        failures = [str(error)]
    if failures:
        print("Issue #624 is incomplete:", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    if not languages:
        print("Issue #624 source preflight passed; both kernel checks are still required")
    else:
        print(f"Issue #624 completion contracts passed: {', '.join(languages)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
