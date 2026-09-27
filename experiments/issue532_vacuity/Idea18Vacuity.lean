import proofs.experiments.issue532.lean.Idea18
open Issue532.Idea18

/-- (a) `PolySizeReductionInto R` holds for *every* class `R` containing one
satisfiable and one unsatisfiable formula (the file proves only the unit-CNF
case): send each φ to the fixed yes/no member; size is constant.  No
computability requirement is recorded, so the definition has no P-vs-NP content. -/
theorem idea18_polySizeReduction_trivial (R : CNF → Prop) (y n : CNF)
    (hy : R y) (hn : R n) (hsy : Satisfiable y) (hsn : ¬ Satisfiable n) :
    PolySizeReductionInto R := by
  classical
  refine ⟨fun φ => if Satisfiable φ then y else n, size y + size n, 0, ?_, ?_, ?_⟩
  · intro φ; by_cases h : Satisfiable φ <;> simp [h, hy, hn]
  · intro φ; by_cases h : Satisfiable φ <;> simp [h, hsy, hsn]
  · intro φ; by_cases h : Satisfiable φ <;> simp [h, polyEval] <;> omega

/-- Moreover the decider cost in `restriction_transfer` is a free parameter:
`dcost := 0` always satisfies `hcost`. -/
theorem idea18_dcost_free (c' k' : Nat) : ∀ ψ : CNF, (fun _ => 0) ψ ≤ polyEval c' k' (size ψ) :=
  fun _ => Nat.zero_le _
