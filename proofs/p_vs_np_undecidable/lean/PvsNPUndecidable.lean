import proofs.complexity.lean.Complexity

/-!
A conditional schema for syntactic independence. `Theory.proves` must be
instantiated with a formal proof relation before the schema says anything
about ZFC. In particular, no independence result is asserted here.
-/
namespace PvsNPUndecidable

abbrev PEqualsNP := Complexity.PEqualsNP
abbrev PNotEqualsNP := Complexity.PNotEqualsNP

structure Theory where
  proves : Prop → Prop

def Independent (theory : Theory) (statement : Prop) : Prop :=
  ¬theory.proves statement ∧ ¬theory.proves (¬statement)

def PvsNPIsIndependent (theory : Theory) : Prop :=
  Independent theory PEqualsNP

theorem independence_has_no_proof (theory : Theory)
    (h : PvsNPIsIndependent theory) :
    ¬theory.proves PEqualsNP ∧ ¬theory.proves PNotEqualsNP := h

theorem pSubsetNP (L : Complexity.ClassP) :
    ∃ L' : Complexity.ClassNP, ∀ x, L.language x = L'.language x :=
  ⟨L.toNP, fun _ => rfl⟩

theorem pvsnpExcludedMiddle : PEqualsNP ∨ PNotEqualsNP :=
  Classical.em PEqualsNP

#print axioms pSubsetNP

end PvsNPUndecidable
