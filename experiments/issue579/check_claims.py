"""Regression check for unsupported independence claims in issues #579 and #613.

Run from any directory with ``python3 experiments/issue579/check_claims.py``.
The Lean examples are compiled separately by the Lean verification job.
"""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
EXPERIMENT = ROOT / "experiments/issue7_undecidability_attempt.md"
INDEPENDENCE = ROOT / "P_VS_NP_INDEPENDENCE_STRATEGIES.md"
DECIDABILITY = ROOT / "SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md"
ROADMAP = ROOT / "PROVING_P_VS_NP_UNDECIDABILITY.md"
CLOCKED_README = ROOT / "proofs/experiments/issue7/README.md"
CLOCKED_LEAN = ROOT / "proofs/experiments/issue7/lean/ClockedSAT.lean"
CLOCKED_ROCQ = ROOT / "proofs/experiments/issue7/rocq/ClockedSAT.v"
LEAN_FILES = [
    ROOT / "experiments/issue7_shoenfield_absoluteness.lean",
    ROOT / "experiments/issue7_undecidability_formalization.lean",
]


def require(text: str, pattern: str, path: Path) -> None:
    if not re.search(pattern, text, re.IGNORECASE):
        raise AssertionError(f"{path.name}: missing {pattern!r}")


def forbid(text: str, pattern: str, path: Path) -> None:
    if re.search(pattern, text, re.IGNORECASE):
        raise AssertionError(f"{path.name}: unsupported claim matches {pattern!r}")


def main() -> None:
    experiment = EXPERIMENT.read_text()
    independence = INDEPENDENCE.read_text()
    decidability = DECIDABILITY.read_text()
    roadmap = ROADMAP.read_text()

    for path, content in [(EXPERIMENT, experiment), (INDEPENDENCE, independence), (DECIDABILITY, decidability), (ROADMAP, roadmap)]:
        require(content, r"Σ[⁰0]₂", path)
        require(content, r"forcing.{0,100}(preserv|invar|cannot change)", path)
        require(content, r"(independen|provab).{0,100}(open|does not follow|does not establish|unresolved)", path)
        forbid(content, r"(?:P\s*=\s*NP|P vs NP)\s+(?:is|as)\s+(?:a )?Π[⁰0]₂", path)
        forbid(content, r"(?:CH|Continuum Hypothesis) is Π[¹1]₂", path)
        forbid(content, r"(?:proof|answer).{0,35}provable in ZFC", path)

    require(experiment, r"∃.{0,90}∀.{0,90}(SAT|input)", EXPERIMENT)
    forbid(experiment, r"(cannot be independent|independence from ZFC is impossible|almost certainly impossible)", EXPERIMENT)
    forbid(independence, r"enumerate all polynomial-time TMs and check", INDEPENDENCE)
    forbid(independence, r"PA should be able to resolve", INDEPENDENCE)
    forbid(decidability, r"forcing cannot change truth value, this supports decidability", DECIDABILITY)

    # The incoming issue #7 roadmap previously repeated the precise claims
    # corrected in #579. Keep these checks on the actual merge candidate.
    require(roadmap, r"∃.{0,90}∀.{0,90}(SAT|input|x)", ROADMAP)
    require(roadmap, r"∀.{0,90}∃.{0,90}(input|x)", ROADMAP)
    require(roadmap, r"Π[⁰0]₂", ROADMAP)
    require(roadmap, r"(object theory|object system).{0,100}ZFC", ROADMAP)
    require(roadmap, r"metatheory", ROADMAP)
    require(roadmap, r"Pr_T|Proof_T", ROADMAP)
    require(roadmap, r"S₂¹.{0,120}Σᵇ₁.{0,50}(PIND|polynomial|length induction)", ROADMAP)
    require(roadmap, r"T₂¹.{0,120}Σᵇ₁.{0,50}(IND|ordinary induction)", ROADMAP)
    require(roadmap, r"issue532/(lean|rocq)/Machines", ROADMAP)
    require(roadmap, r"SATHard.{0,120}(open|unfinished|unproved|not (yet )?formalized)", ROADMAP)
    forbid(roadmap, r"∀ polynomial-time .{0,80}∃ NP language", ROADMAP)
    forbid(roadmap, r"(?:all forcing attempts (?:fail|must fail)|forcing invariance).{0,120}(?:cannot be independent|not independent|provable|decidable in ZFC)", ROADMAP)
    forbid(roadmap, r"(?:Shoenfield.{0,100}independence is unlikely|independence is impossible \(due to Shoenfield\))", ROADMAP)
    forbid(roadmap, r"(?:all forcing attempts must fail|this is decidable in principle|100% certainty)", ROADMAP)
    forbid(roadmap, r"(?:automated|automation).{0,100}(?:cannot (?:find|discover|generate)|guarantee(?:s)? correctness)", ROADMAP)
    forbid(roadmap, r"(?:success probability|probability:|automation contribution:|certainty:)\s*(?:<?\d+%)", ROADMAP)
    forbid(roadmap, r"def SAT\s*:[\s\S]{0,200}?\bsorry\b", ROADMAP)

    # The issue #7 clocked-SAT files must keep the corrected quantifiers,
    # an explicit SATHard premise and the open status of independence.
    clocked = CLOCKED_README.read_text()
    require(clocked, r"∃ m p, ∀ x, clockCheck m p x = true.{0,40}Σ[⁰0]₂", CLOCKED_README)
    require(clocked, r"∀ m p, ∃ x, clockCheck m p x = false.{0,40}Π[⁰0]₂", CLOCKED_README)
    require(clocked, r"SATHard.{0,120}(open|unfinished|unproved|not (yet )?formalized)", CLOCKED_README)
    require(clocked, r"(independen|provab).{0,100}(open|does not follow|does not establish|unresolved)", CLOCKED_README)
    require(clocked, r"per_machine_form_holds", CLOCKED_README)
    forbid(clocked, r"(?:100% certainty|(?:success probability|probability:)\s*<?\d+%)", CLOCKED_README)
    require(clocked, r"Nothing here proves P = NP, P ≠ NP, or anything about ZFC", CLOCKED_README)
    forbid(clocked, r"(?<!prove )(?:P vs NP|P\s*=\s*NP|P\s*≠\s*NP) is (?:independent|undecidable)|independence (?:is|has been) (?:proved|established)", CLOCKED_README)
    for path, pattern in [(CLOCKED_LEAN, r"\b(?:axiom|sorry|admit|native_decide)\b"), (CLOCKED_ROCQ, r"\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Hypothesis)\b")]:
        content = re.sub(r"\(\*[\s\S]*?\*\)|/-[\s\S]*?-/|--.*", "", path.read_text())
        forbid(content, pattern, path)
        require(content, r"pEqualsNP_of_clockedSAT\s*(?:\(hard : SATHard\)|: SATHard ->)", path)
        require(content, r"pi2_of_pNotEqualsNP\s*(?:\(hard : SATHard\)|: SATHard ->)", path)
        require(content, r"per_machine_form_holds", path)

    for path in LEAN_FILES:
        content = path.read_text()
        forbid(content, r"\b(?:axiom|sorry)\b", path)
        forbid(content, r"not_independent_of_zfc|pvsnp_not_independent", path)
        require(content, r"Classical\.em", path)

    print("Issue #579 claim regression checks passed")


if __name__ == "__main__":
    main()
