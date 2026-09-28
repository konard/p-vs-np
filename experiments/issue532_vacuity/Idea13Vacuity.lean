import proofs.experiments.issue532.lean.Idea13
open Issue532.Idea13

/-- (a) `PolyApprox` holds for every problem and every ratio `num/den ≥ 1`:
`Algo.time` is a free field, so `run := opt`, `time := 0` works. -/
theorem idea13_polyApprox_trivial {α : Type} (sz opt : α → Nat) (num den : Nat)
    (h : den ≤ num) : PolyApprox sz opt num den :=
  ⟨⟨opt, fun _ => 0⟩, 0, 0, fun _ => ⟨Nat.le_refl _, Nat.mul_le_mul_left _ h⟩,
    fun _ => Nat.zero_le _⟩

/-- Even exact (ratio 1/1) approximation is "polynomial". -/
theorem idea13_exact_polyApprox {α : Type} (sz opt : α → Nat) : PolyApprox sz opt 1 1 :=
  idea13_polyApprox_trivial sz opt 1 1 (Nat.le_refl _)
