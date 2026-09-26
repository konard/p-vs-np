import proofs.complexity.lean.Complexity

/-!
The classical dichotomy for P versus NP, using the finite machine definitions
from `Complexity`. Excluded middle supplies no decision procedure or answer.
-/

namespace PvsNPDecidable

abbrev Language := Complexity.Language
abbrev ClassP := Complexity.ClassP
abbrev ClassNP := Complexity.ClassNP

def PEqualsNP : Prop := Complexity.PEqualsNP
def PNotEqualsNP : Prop := ¬PEqualsNP
def is_decidable (P : Prop) : Prop := P ∨ ¬P

theorem P_vs_NP_is_decidable : PEqualsNP ∨ PNotEqualsNP :=
  Classical.em PEqualsNP

theorem P_vs_NP_decidable : is_decidable PEqualsNP :=
  Classical.em PEqualsNP

theorem P_vs_NP_has_answer : PEqualsNP ∨ ¬PEqualsNP :=
  Classical.em PEqualsNP

theorem pSubsetNP (L : ClassP) :
    ∃ L' : ClassNP, ∀ x, L.language x = L'.language x := by
  exact ⟨L.toNP, fun _ => rfl⟩

def pvsnpIsWellFormed : Prop := PEqualsNP ∨ PNotEqualsNP

theorem decidability_reflexive (P : Prop) :
    is_decidable P ↔ (P ∨ ¬P) := Iff.rfl

theorem classicalLogicConsistency (P : Prop) : P ∨ ¬P :=
  Classical.em P

theorem decidability_implies_answer :
    is_decidable PEqualsNP → (PEqualsNP ∨ PNotEqualsNP) :=
  id

theorem double_negation :
    ¬¬(PEqualsNP ∨ PNotEqualsNP) → (PEqualsNP ∨ PNotEqualsNP) :=
  Classical.not_not.mp

#print axioms pSubsetNP

end PvsNPDecidable
