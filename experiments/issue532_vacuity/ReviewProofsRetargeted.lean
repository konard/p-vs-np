import proofs.experiments.issue532.lean.Idea13
import proofs.experiments.issue532.lean.Idea14
import proofs.experiments.issue532.lean.Idea32
import proofs.experiments.issue532.lean.Idea37

/-!
The reviewer's four proofs (`ReviewProofs.lean`), aimed at the *current* names.

`ReviewProofs.lean` now fails partly because the free-cost definitions were
renamed (`PolyDec sz L` is gone, the schemas are `…For`). A rename alone would
also make it fail, so this file restates each move against the definitions
that replaced them: the answer function in the decider slot, the zero cost
function, or a machine that is claimed to halt in zero steps. Every theorem
must fail with a type or proof error, never with an unknown name; `check.py`
enforces both.
-/

open Complexity Issue532

/-- Idea 14 move 1: the language itself as the decider. `PolyDec` now asks for a
`Complexity.Machine`, so `L` does not fit. -/
theorem polyDec_holds_for_every_language (L : Language) : Machines.PolyDec L :=
  ⟨L, ⟨0, 0⟩, fun x => ⟨0, L x, Nat.zero_le _, rfl, rfl⟩⟩

/-- Idea 14 move 2: an honest machine, with the time set to zero. `Run` has no
zero-step constructor, so the run cannot be produced. -/
theorem polyDec_with_zero_steps (L : Language) : Machines.PolyDec L :=
  ⟨⟨[]⟩, ⟨0, 0⟩, fun x => ⟨0, L x, Nat.zero_le _, by constructor, rfl⟩⟩

/-- Idea 14 move 3: the same move against `NPinRP`. -/
theorem npInRP_with_zero_steps : Idea14.NPinRP :=
  ⟨⟨[]⟩, ⟨0, 0⟩, ⟨0, 0⟩, fun x _ => ⟨0, Machines.SAT x, Nat.zero_le _, by constructor⟩,
    fun _ => by simp⟩

/-- Idea 13: `run := opt`, `time := 0`. The approximation algorithm is now a
machine that computes `f` within `p` steps. -/
theorem polyApprox_holds_for_every_problem (opt : Word → Nat) (num den : Nat) (h : den ≤ num) :
    Idea13.PolyApprox opt num den :=
  ⟨⟨opt, fun _ => 0⟩, 0, 0, fun _ => ⟨Nat.le_refl _, Nat.mul_le_mul_left _ h⟩,
    fun _ => Nat.zero_le _⟩

/-- Idea 37: the zero cost function. The obligation has no cost parameter any
more; the steps are those of `Run`. -/
theorem logParamFPT_with_zero_cost : Idea37.LogParamFPTObligation :=
  ⟨⟨[]⟩, fun _ => 0, 0, 0, fun _ => by simp,
    fun x => ⟨0, Machines.SAT x, by simp, by constructor, rfl⟩⟩

/-- Idea 32: `decider_meets_isolation` with the classical SAT decider. The
obligation now asks for a machine that computes the isolating map on words
within a polynomial number of steps; the classical decider is not a machine. -/
theorem isolation_with_classical_decider : Idea32.IsolationObligation := by
  classical
  have hsat : ∀ φ, (decide (Idea32.Satisfiable φ)) = true ↔ Idea32.Satisfiable φ :=
    fun φ => decide_eq_true_iff
  obtain ⟨hinto, hpres⟩ :=
    Idea32.decider_meets_isolation (fun φ => decide (Idea32.Satisfiable φ)) hsat
  exact ⟨_, _, _, trivial, hinto, hpres⟩
