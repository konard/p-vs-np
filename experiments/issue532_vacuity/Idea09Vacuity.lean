import proofs.experiments.issue532.lean.Idea09
open Issue532.Idea09
attribute [local instance] Classical.propDecidable

/-- (a) `PolyTimeWitnessProgramExists` holds for every `sz`, `V` once the free
parameter `runs` is chosen as an oracle that returns a witness at time 0.
It is also monotone, so `levin_poly_of_obligation`'s hypotheses are all met. -/
noncomputable def oracleRuns {X W : Type} (V : X → W → Bool) : Nat → X → Nat → Option W :=
  fun _ x _ => if h : ∃ w, V x w = true then some (Classical.choose h) else none

theorem idea09_obligation_trivial {X W : Type} (sz : X → Nat) (V : X → W → Bool) :
    PolyTimeWitnessProgramExists sz (oracleRuns V) V := by
  refine ⟨0, 0, 0, fun x hx => ⟨0, Classical.choose hx, ?_, ?_, Classical.choose_spec hx⟩⟩
  · exact Nat.zero_le _
  · simp [oracleRuns, hx]

theorem idea09_oracleRuns_monotone {X W : Type} (V : X → W → Bool) (x : X) :
    MonotoneRuns (oracleRuns V · x) := by
  intro i t t' w _ h; simpa [oracleRuns] using h

/-- Existential form: for every `sz`, `V` some `runs` satisfies the obligation. -/
theorem idea09_exists_runs {X W : Type} (sz : X → Nat) (V : X → W → Bool) :
    ∃ runs : Nat → X → Nat → Option W,
      (∀ x, MonotoneRuns (runs · x)) ∧ PolyTimeWitnessProgramExists sz runs V :=
  ⟨oracleRuns V, idea09_oracleRuns_monotone V, idea09_obligation_trivial sz V⟩
