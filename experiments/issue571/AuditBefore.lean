import proofs.p_vs_np_decidable.lean.PvsNPDecidable

-- Reproduction from issue #571 against the old permissive records.
theorem audit_all_languages_in_P (L : String → Bool) :
    ∃ p : PvsNPDecidable.ClassP, p.language = L := by
  refine ⟨{
    language := L
    decider := fun s => if L s then 1 else 0
    timeComplexity := fun _ => 0
    isPoly := ⟨0, 0, by intro n; simp⟩
    correct := by intro s; cases h : L s <;> simp [h]
  }, rfl⟩

theorem audit_PEqualsNP : PvsNPDecidable.PEqualsNP := by
  intro L
  obtain ⟨p, hp⟩ := audit_all_languages_in_P L.language
  exact ⟨p, fun s => congrFun hp.symm s⟩

#print axioms audit_PEqualsNP
