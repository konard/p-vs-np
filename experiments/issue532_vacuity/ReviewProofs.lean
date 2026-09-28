import proofs.experiments.issue532.lean.Idea13
import proofs.experiments.issue532.lean.Idea14
import proofs.experiments.issue532.lean.Idea32
import proofs.experiments.issue532.lean.Idea37

open Issue532

/-- Idea 14: `PolyDec sz L` holds for every language `L`, including SAT. -/
theorem idea14_polyDec_holds_for_every_language {α : Type} (sz : α → Nat) (L : α → Bool) :
    Idea14.PolyDec sz L :=
  ⟨L, fun _ => 0, 0, 0, fun _ => rfl, fun _ => Nat.zero_le _⟩

/-- Idea 13: `PolyApprox` holds for every problem and every ratio `num/den ≥ 1`. -/
theorem idea13_polyApprox_holds_for_every_problem {α : Type} (sz opt : α → Nat) (num den : Nat)
    (h : den ≤ num) : Idea13.PolyApprox sz opt num den :=
  ⟨⟨opt, fun _ => 0⟩, 0, 0, fun x => ⟨Nat.le_refl _, Nat.mul_le_mul_left _ h⟩, fun _ => Nat.zero_le _⟩

/-- Idea 37: the cost model is a parameter, so the zero cost function meets the obligation. -/
theorem idea37_obligation_holds_with_zero_cost {Inst Alg : Type} (Correct : Alg → Prop)
    (size : Inst → Nat) (A : Alg) (hA : Correct A) :
    Idea37.LogParamFPTObligation Correct (fun _ _ => 0) size :=
  ⟨A, fun _ => 0, 0, 0, hA, fun _ => Nat.zero_le _, fun I => by simp⟩

/-- Idea 32: `PolyTime` is a parameter, so `decider_meets_isolation` plus the classical
SAT decider meets the obligation. -/
theorem idea32_obligation_holds_with_trivial_polytime :
    Idea32.IsolationObligation (fun _ => True) := by
  classical
  have hsat : ∀ φ, (decide (Idea32.Satisfiable φ)) = true ↔ Idea32.Satisfiable φ :=
    fun φ => decide_eq_true_iff
  obtain ⟨hinto, hpres⟩ :=
    Idea32.decider_meets_isolation (fun φ => decide (Idea32.Satisfiable φ)) hsat
  exact ⟨_, trivial, hinto, hpres⟩
