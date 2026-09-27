"""Regression check for the unsupported independence conclusions in issue #579.

Run from any directory with ``python3 experiments/issue579/check_claims.py``.
The Lean examples are compiled separately by the Lean verification job.
"""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
EXPERIMENT = ROOT / "experiments/issue7_undecidability_attempt.md"
INDEPENDENCE = ROOT / "P_VS_NP_INDEPENDENCE_STRATEGIES.md"
DECIDABILITY = ROOT / "SOLUTION_STRATEGIES_FOR_P_VS_NP_DECIDABILITY.md"
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

    for path, content in [(EXPERIMENT, experiment), (INDEPENDENCE, independence), (DECIDABILITY, decidability)]:
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

    for path in LEAN_FILES:
        content = path.read_text()
        forbid(content, r"\b(?:axiom|sorry)\b", path)
        forbid(content, r"not_independent_of_zfc|pvsnp_not_independent", path)
        require(content, r"Classical\.em", path)

    print("Issue #579 claim regression checks passed")


if __name__ == "__main__":
    main()
