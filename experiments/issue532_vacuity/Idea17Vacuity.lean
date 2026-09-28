import proofs.experiments.issue532.lean.Idea17
open Issue532.Idea17

/-- (a) The model `M` is a free parameter: any model with no correct algorithm
satisfies the "lower bound" vacuously. -/
def noCorrectModel : AlgorithmModel where
  Alg := Unit
  correct := fun _ => False
  cost := fun _ _ => 0

theorem idea17_allSuperpoly_trivial : AllAlgorithmsSuperpolynomial noCorrectModel :=
  fun _ h => h.elim

/-- (a) Also for an arbitrary model after restricting `correct` to `False`. -/
theorem idea17_allSuperpoly_of_no_correct (M : AlgorithmModel) (h : ∀ A, ¬ M.correct A) :
    AllAlgorithmsSuperpolynomial M :=
  fun A hA => (h A hA).elim

/-- (b) And its negation is one line for any model with a correct constant-cost
algorithm (the file itself proves this for `twoAlgModel`). -/
theorem idea17_not_allSuperpoly (M : AlgorithmModel) (A : M.Alg) (hA : M.correct A)
    (hc : ∀ n, M.cost A n ≤ 1) : ¬ AllAlgorithmsSuperpolynomial M := by
  intro h
  obtain ⟨n, _, hn⟩ := h A hA 1 0 0
  have := hc n
  simp [polyEval] at hn
  omega
