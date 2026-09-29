import proofs.complexity.lean.Complexity

/-!
A conditional schema for syntactic independence. `Statement` is syntax,
separate from the propositions it denotes. `Provable` must be instantiated
with a formal proof relation before the schema says anything about ZFC.
No independence result is asserted here.
-/
namespace PvsNPUndecidable

abbrev PEqualsNP := Complexity.PEqualsNP
abbrev PNotEqualsNP := Complexity.PNotEqualsNP

inductive Statement where
  | pEqualsNP
  | neg (statement : Statement)

def Statement.denotes : Statement → Prop
  | .pEqualsNP => PEqualsNP
  | .neg statement => ¬statement.denotes

structure Theory where
  proves : Statement → Prop

def Provable (theory : Theory) (statement : Statement) : Prop :=
  theory.proves statement

def Independent (theory : Theory) (statement : Statement) : Prop :=
  ¬Provable theory statement ∧ ¬Provable theory (.neg statement)

def PvsNPIsIndependent (theory : Theory) : Prop :=
  Independent theory .pEqualsNP

theorem independence_has_no_proof (theory : Theory)
    (h : PvsNPIsIndependent theory) :
    ¬Provable theory .pEqualsNP ∧ ¬Provable theory (.neg .pEqualsNP) := h

theorem pSubsetNP (L : Complexity.ClassP) :
    ∃ L' : Complexity.ClassNP, ∀ x, L.language x = L'.language x :=
  ⟨L.toNP, fun _ => rfl⟩

theorem pvsnpExcludedMiddle : PEqualsNP ∨ PNotEqualsNP :=
  Classical.em PEqualsNP

#print axioms pSubsetNP

end PvsNPUndecidable
