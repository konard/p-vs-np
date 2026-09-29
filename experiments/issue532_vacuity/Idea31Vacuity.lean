import proofs.experiments.issue532.lean.Idea31
open Issue532.Idea31

/-- (a) `decode` is unrestricted, so the empty generator plus `decode := fun _ x => L x`
meets `UniformPolyAdvice` for every `L` (e.g. SAT) and every `Uniform` class that
contains the constant-`[]` generator (true for any honest uniform class). -/
theorem idea31_uniformPolyAdvice_of (Uniform : (Nat → List Bool) → Prop)
    (hU : Uniform (fun _ => [])) (L : List Bool → Bool) : UniformPolyAdvice Uniform L :=
  ⟨fun _ => [], fun _ x => L x, ⟨0, 0⟩, hU, fun _ => Nat.zero_le _, fun _ => rfl⟩

theorem idea31_uniformPolyAdvice_trivial (L : List Bool → Bool) :
    UniformPolyAdvice (fun _ => True) L :=
  idea31_uniformPolyAdvice_of _ trivial L
