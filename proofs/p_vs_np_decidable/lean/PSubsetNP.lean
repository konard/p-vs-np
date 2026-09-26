import proofs.complexity.lean.Complexity

/-! P ⊆ NP for finite machine programs and polynomially bounded runs. -/

namespace PSubsetNP

abbrev ClassP := Complexity.ClassP
abbrev ClassNP := Complexity.ClassNP

theorem pSubsetNP (L : ClassP) :
    ∃ L' : ClassNP, ∀ x, L.language x = L'.language x := by
  exact ⟨L.toNP, fun _ => rfl⟩

#print axioms pSubsetNP

end PSubsetNP
