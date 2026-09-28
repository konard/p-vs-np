import proofs.experiments.issue532.lean.Idea35
open Issue532.Idea35

/-- (a) `CompactTractableCompilation` has no cost component at all: for any `sat`
(e.g. the real SAT predicate as a classical `Bool` function) the one-bit
compilation `compile := sat`, `query := id` meets it with `q := fun _ => 1`.
The file already records this as `decider_gives_compilation`. -/
theorem idea35_compilation_trivial {Formula : Type} (size : Formula → Nat)
    (sat : Formula → Bool) :
    ∃ (compile : Formula → Bool) (query : Bool → Bool),
      CompactTractableCompilation size (fun _ => 1) sat (fun _ => 1) compile query :=
  ⟨sat, fun b => b, decider_gives_compilation size sat⟩

/-- Even with `q := fun _ => 0` and a zero-size representation. -/
theorem idea35_compilation_zero {Formula : Type} (size : Formula → Nat)
    (sat : Formula → Bool) :
    CompactTractableCompilation size (fun _ : Bool => 0) sat (fun _ => 0) sat (fun b => b) :=
  ⟨fun _ => Nat.le_refl _, fun _ => rfl⟩
