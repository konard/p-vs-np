"""Generate paired, standalone finite tests for issue #532.

Run from the repository root: python3 experiments/issue532/generate.py
The output is deterministic. The research log explains what each test does and
does not establish about the open P versus NP problem.
"""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "proofs" / "experiments" / "issue532"

# (slug, Lean definitions and theorem, Rocq definitions and theorem).
# Keep each file independent: CI compiles Rocq files
# one at a time, without an _CoqProject or shared load path.
CASES = [
    (
        "01_bounded_sat",
        "def sat (x y : Bool) : Bool := x && !y\n"
        "def search : Bool := sat false false || sat false true || sat true false || sat true true\n"
        "theorem tested : search = true := by decide",
        "Definition sat (x y : bool) : bool := andb x (negb y).\n"
        "Definition search : bool := orb (sat false false) (orb (sat false true) (orb (sat true false) (sat true true))).\n"
        "Theorem tested : search = true. Proof. reflexivity. Qed.",
    ),
    (
        "02_failed_certificate",
        "def sat (x y : Bool) : Bool := x && !y\n"
        "def search : Bool := sat false false || sat false true || sat true false || sat true true\n"
        "theorem tested : sat true true = false ∧ search = true := by decide",
        "Definition sat (x y : bool) : bool := andb x (negb y).\n"
        "Definition search : bool := orb (sat false false) (orb (sat false true) (orb (sat true false) (sat true true))).\n"
        "Theorem tested : sat true true = false /\\ search = true. Proof. split; reflexivity. Qed.",
    ),
    (
        "03_verifier_soundness",
        "def verify (x y : Bool) : Bool := x && y\n"
        "theorem tested : ∀ x y : Bool, verify x y = true → x = true ∧ y = true := by decide",
        "Definition verify (x y : bool) : bool := andb x y.\n"
        "Theorem tested : forall x y : bool, verify x y = true -> x = true /\\ y = true.\n"
        "Proof. destruct x, y; simpl; intros H; try discriminate; split; reflexivity. Qed.",
    ),
    (
        "04_pairwise_consistency",
        "def allConstraints (x y z : Bool) : Bool := (x != y) && (y != z) && (x != z)\n"
        "theorem tested : ∀ x y z : Bool, allConstraints x y z = false := by decide",
        "Definition allConstraints (x y z : bool) : bool := andb (andb (xorb x y) (xorb y z)) (xorb x z).\n"
        "Theorem tested : forall x y z : bool, allConstraints x y z = false.\n"
        "Proof. destruct x, y, z; reflexivity. Qed.",
    ),
    (
        "05_greedy_choice",
        "def greedyCost : Nat := 1 + 10\n"
        "def alternativeCost : Nat := 2 + 1\n"
        "theorem tested : alternativeCost < greedyCost := by decide",
        "Definition greedyCost : nat := 1 + 10.\n"
        "Definition alternativeCost : nat := 2 + 1.\n"
        "Theorem tested : alternativeCost < greedyCost. Proof. compute; lia. Qed.",
    ),
    (
        "06_local_minimum",
        "def cost : Nat → Nat\n  | 0 => 1\n  | 1 => 2\n  | _ => 0\n"
        "theorem tested : cost 0 < cost 1 ∧ cost 2 < cost 0 := by decide",
        "Definition cost (n : nat) : nat := match n with 0 => 1 | 1 => 2 | _ => 0 end.\n"
        "Theorem tested : cost 0 < cost 1 /\\ cost 2 < cost 0. Proof. compute; lia. Qed.",
    ),
    (
        "07_lossy_compression",
        "def encode (p : Bool × Bool) : Bool := p.1\n"
        "theorem tested : encode (false, false) = encode (false, true) ∧ (false, false) ≠ (false, true) := by decide",
        "Definition encode (p : bool * bool) : bool := fst p.\n"
        "Theorem tested : encode (false, false) = encode (false, true) /\\ (false, false) <> (false, true).\n"
        "Proof. split; [reflexivity | discriminate]. Qed.",
    ),
    (
        "08_finite_samples",
        "def f (x : Bool) : Bool := x\n"
        "def g (_ : Bool) : Bool := false\n"
        "theorem tested : f false = g false ∧ f true ≠ g true := by decide",
        "Definition f (x : bool) : bool := x.\n"
        "Definition g (_ : bool) : bool := false.\n"
        "Theorem tested : f false = g false /\\ f true <> g true.\n"
        "Proof. split; [reflexivity | discriminate]. Qed.",
    ),
    (
        "09_length_vs_runtime",
        "inductive Program where | short | long\n"
        "def length : Program → Nat | .short => 1 | .long => 2\n"
        "def steps : Program → Nat | .short => 10 | .long => 1\n"
        "theorem tested : length .short < length .long ∧ steps .long < steps .short := by decide",
        "Inductive program := short | long.\n"
        "Definition codeLength (p : program) : nat := match p with short => 1 | long => 2 end.\n"
        "Definition steps (p : program) : nat := match p with short => 10 | long => 1 end.\n"
        "Theorem tested : codeLength short < codeLength long /\\ steps long < steps short.\n"
        "Proof. compute; lia. Qed.",
    ),
    (
        "10_monotone_boundary",
        "def negation (x : Bool) : Bool := !x\n"
        "theorem tested : negation false = true ∧ negation true = false := by decide",
        "Definition negation (x : bool) : bool := negb x.\n"
        "Theorem tested : negation false = true /\\ negation true = false.\n"
        "Proof. split; reflexivity. Qed.",
    ),
    (
        "11_relaxation_gap",
        "def cost (n : Nat) : Nat := if n == 1 then 0 else 1\n"
        "theorem tested : cost 1 < cost 0 ∧ cost 1 < cost 2 := by decide",
        "Definition cost (n : nat) : nat := if Nat.eqb n 1 then 0 else 1.\n"
        "Theorem tested : cost 1 < cost 0 /\\ cost 1 < cost 2.\n"
        "Proof. compute; lia. Qed.",
    ),
    (
        "12_reduction_soundness",
        "def source (x : Bool) : Bool := x\n"
        "def target (x : Bool) : Bool := x\n"
        "def badMap (_ : Bool) : Bool := true\n"
        "theorem tested : source false ≠ target (badMap false) := by decide",
        "Definition source (x : bool) : bool := x.\n"
        "Definition target (x : bool) : bool := x.\n"
        "Definition badMap (_ : bool) : bool := true.\n"
        "Theorem tested : source false <> target (badMap false). Proof. discriminate. Qed.",
    ),
    (
        "13_approximation_gap",
        "def optimum : Nat := 3\n"
        "def approximate : Nat := 4\n"
        "theorem tested : approximate ≤ 2 * optimum ∧ approximate ≠ optimum := by decide",
        "Definition optimum : nat := 3.\n"
        "Definition approximate : nat := 4.\n"
        "Theorem tested : approximate <= 2 * optimum /\\ approximate <> optimum.\n"
        "Proof. compute; lia. Qed.",
    ),
    (
        "14_random_seed",
        "def randomizedAnswer (seed : Bool) : Bool := seed\n"
        "theorem tested : randomizedAnswer true = true ∧ randomizedAnswer false = false := by decide",
        "Definition randomizedAnswer (seed : bool) : bool := seed.\n"
        "Theorem tested : randomizedAnswer true = true /\\ randomizedAnswer false = false.\n"
        "Proof. split; reflexivity. Qed.",
    ),
    (
        "15_size_vs_depth",
        "inductive Shape where | chain | balanced\n"
        "def size : Shape → Nat | .chain => 3 | .balanced => 3\n"
        "def depth : Shape → Nat | .chain => 3 | .balanced => 2\n"
        "theorem tested : size .chain = size .balanced ∧ depth .chain ≠ depth .balanced := by decide",
        "Inductive shape := chain | balanced.\n"
        "Definition size (s : shape) : nat := match s with chain => 3 | balanced => 3 end.\n"
        "Definition depth (s : shape) : nat := match s with chain => 3 | balanced => 2 end.\n"
        "Theorem tested : size chain = size balanced /\\ depth chain <> depth balanced.\n"
        "Proof. split; [reflexivity | discriminate]. Qed.",
    ),
    (
        "16_finite_diagonal",
        "def first (_ : Bool) : Bool := false\n"
        "def second (_ : Bool) : Bool := true\n"
        "def diagonal (x : Bool) : Bool := !x\n"
        "theorem tested : diagonal false ≠ first false ∧ diagonal true ≠ second true := by decide",
        "Definition first (_ : bool) : bool := false.\n"
        "Definition second (_ : bool) : bool := true.\n"
        "Definition diagonal (x : bool) : bool := negb x.\n"
        "Theorem tested : diagonal false <> first false /\\ diagonal true <> second true.\n"
        "Proof. split; discriminate. Qed.",
    ),
    (
        "17_enumeration_cost",
        "def assignments : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]\n"
        "theorem tested : assignments.length = 4 := by decide",
        "Definition assignments : list (bool * bool) := (false, false) :: (false, true) :: (true, false) :: (true, true) :: nil.\n"
        "Theorem tested : length assignments = 4. Proof. reflexivity. Qed.",
    ),
    (
        "18_restricted_instance",
        "def easy (x : Bool) : Bool := x || true\n"
        "def general (x y : Bool) : Bool := x || y\n"
        "theorem tested : (∀ x : Bool, easy x = true) ∧ general false false = false := by decide",
        "Definition easy (x : bool) : bool := orb x true.\n"
        "Definition general (x y : bool) : bool := orb x y.\n"
        "Theorem tested : (forall x : bool, easy x = true) /\\ general false false = false.\n"
        "Proof. split; [destruct x; reflexivity | reflexivity]. Qed.",
    ),
    (
        "19_answer_as_advice",
        "def advice (x : Bool) : Bool := x\n"
        "def solver (_x hint : Bool) : Bool := hint\n"
        "theorem tested : ∀ x : Bool, solver x (advice x) = x := by decide",
        "Definition advice (x : bool) : bool := x.\n"
        "Definition solver (_x hint : bool) : bool := hint.\n"
        "Theorem tested : forall x : bool, solver x (advice x) = x.\n"
        "Proof. destruct x; reflexivity. Qed.",
    ),
    (
        "20_parallel_depth",
        "def serial : Nat := 3 + 5\n"
        "def independent : Nat := max 3 5\n"
        "def dependent : Nat := 3 + 5\n"
        "theorem tested : independent < serial ∧ dependent = serial := by decide",
        "Definition serial : nat := 3 + 5.\n"
        "Definition independent : nat := Nat.max 3 5.\n"
        "Definition dependent : nat := 3 + 5.\n"
        "Theorem tested : independent < serial /\\ dependent = serial.\n"
        "Proof. compute; lia. Qed.",
    ),
]


def main():
    for slug, lean, rocq in CASES:
        for language in ("lean", "rocq"):
            (OUT / language).mkdir(parents=True, exist_ok=True)
        namespace = "Idea" + slug[:2]
        (OUT / "lean" / f"{namespace}.lean").write_text(
            f"/- Issue #532: {slug}. Finite model only; see RESEARCH_LOG.md. -/\n"
            f"namespace Issue532.{namespace}\n{lean}\nend Issue532.{namespace}\n"
        )
        (OUT / "rocq" / f"{namespace}.v").write_text(
            f"(* Issue #532: {slug}. Finite model only; see RESEARCH_LOG.md. *)\n"
            "From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.\n"
            f"{rocq}\n"
        )


if __name__ == "__main__":
    main()
