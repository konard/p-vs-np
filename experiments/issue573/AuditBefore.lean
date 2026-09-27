import proofs.p_eq_np.lean.PvsNP

-- The old relation accepts any Boolean computation as a one-bit reduction.
-- No finite program or runtime witness for `g` is required.
theorem audit_arbitrary_boolean_reduction (g : PEqNP.BinaryString → Bool) :
    PEqNP.PolyTimeReduction (fun x => g x = true) (fun y => y = [true]) := by
  refine ⟨fun x => [g x], fun _ => 1, PEqNP.constant_is_poly 1, ?_, ?_⟩
  · intro x
    exact Nat.le_refl 1
  · intro x
    change g x = true ↔ [g x] = [true]
    simp [List.cons.injEq]
