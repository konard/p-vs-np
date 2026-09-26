"""Compile the issue's derivation of False against both core frameworks.

The check fails if either proof assistant accepts the derivation. Run from the
repository root with ``python3 experiments/issue570/check_contradiction.py``.
"""

from pathlib import Path
import argparse
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "proofs/p_eq_np/lean/PvsNP.lean"
ROCQ = ROOT / "proofs/p_eq_np/rocq/PvsNP.v"

LEAN_CONTRADICTION = """
theorem audit_core_false : False := by
  obtain ⟨_, _, _, _, h⟩ := PEqNP.empty_in_P
  exact (h []).mpr True.intro
"""

ROCQ_CONTRADICTION = """
Theorem audit_core_false : False.
Proof.
  destruct empty_in_P as [M [time [_ [_ H]]]].
  specialize (H []).
  unfold empty_language in H.
  exact (proj2 H I).
Qed.
Print Assumptions audit_core_false.
"""


def rejected(source: Path, extra: str, command: list[str]) -> None:
    with tempfile.TemporaryDirectory(prefix="issue570-") as tmp:
        path = Path(tmp) / ("Audit.lean" if source.suffix == ".lean" else "Audit.v")
        original = source.read_text()
        path.write_text(original)
        baseline = subprocess.run(command + [str(path)], capture_output=True, text=True)
        if baseline.returncode != 0:
            raise AssertionError(f"{source.name} does not compile:\n{baseline.stdout}{baseline.stderr}")
        path.write_text(original + "\n" + extra)
        result = subprocess.run(command + [str(path)], capture_output=True, text=True)
        if result.returncode == 0:
            raise AssertionError(f"{source.name} still proves False:\n{result.stdout}")
        if "expected to have type" not in result.stdout + result.stderr:
            raise AssertionError(f"{source.name} failed for an unrelated reason:\n{result.stdout}{result.stderr}")
        print(f"{source.name}: contradiction rejected")
        print("\n".join((result.stdout + result.stderr).splitlines()[-8:]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="check only Lean")
    parser.add_argument("--rocq", action="store_true", help="check only Rocq")
    args = parser.parse_args()
    if args.lean or not args.rocq:
        rejected(LEAN, LEAN_CONTRADICTION, ["lean"])
    if args.rocq or not args.lean:
        rejected(ROCQ, ROCQ_CONTRADICTION, ["rocq", "compile"])
