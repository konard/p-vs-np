import proofs.experiments.issue532.lean.Idea39
open Issue532.Idea39

variable {F : Type}

/-- (a) The class `C` is free: for the empty class the obligation is vacuous. -/
theorem idea39_superpolyAll_empty (taut : F → Prop) (fsize : F → Nat) :
    SuperpolyAllSystems (fun _ => False) taut fsize :=
  fun _ h => h.elim

/-- (a) For the singleton class `{weakSys}` (exponential size by fiat) it holds
whenever tautologies have unbounded size. -/
theorem idea39_superpolyAll_weak (taut : F → Prop) (fsize : F → Nat)
    (hunb : ∀ m, ∃ φ, taut φ ∧ m ≤ fsize φ) :
    SuperpolyAllSystems (fun S => S = weakSys taut fsize) taut fsize := by
  rintro S rfl
  exact (weak_lb_strong_short taut fsize hunb).1

/-- (b) For the singleton class `{strongSys}` (proof size = formula size) it is
refutable, by the file's `bounded_member_refutes`. -/
theorem idea39_not_superpolyAll_strong (taut : F → Prop) (fsize : F → Nat)
    (hunb : ∀ m, ∃ φ, taut φ ∧ m ≤ fsize φ) :
    ¬ SuperpolyAllSystems (fun S => S = strongSys taut fsize) taut fsize :=
  bounded_member_refutes _ taut fsize _ rfl ⟨1, 1⟩ (weak_lb_strong_short taut fsize hunb).2.1
