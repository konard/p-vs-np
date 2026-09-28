import proofs.experiments.issue532.lean.Machines

/-!
# Relativization: a sound abstract schema

This file does not construct oracle machines or prove the historical
Baker--Gill--Solovay theorem. `P` and `NP` below are *parameters* denoting
classes in each oracle world. A claimed uniform proof of equality must be
valid in every world where its technique applies. An explicit separating
world then rules out that uniform proof when the technique applies there.

Natural proofs and algebrization require circuit and algebraic oracle models;
the incoming PR #41 placeholders for them are not asserted here as theorems.
-/

namespace Issue609.KnownBarriers

open Complexity

universe u

def EqualAt {Oracle : Type u} (P NP : Oracle → Language → Prop) (A : Oracle) : Prop :=
  ∀ L, P A L ↔ NP A L

def SeparationAt {Oracle : Type u} (P NP : Oracle → Language → Prop) (A : Oracle) : Prop :=
  ∃ L, NP A L ∧ ¬ P A L

/-- `T A` says that the technique's hypothesis holds in world `A`. This
schema describes the claimed conclusion of a relativizing equality proof. -/
def UniformEqualityProof {Oracle : Type u} (P NP : Oracle → Language → Prop)
    (T : Oracle → Prop) : Prop :=
  ∀ A, T A → EqualAt P NP A

def UniformSeparationProof {Oracle : Type u} (P NP : Oracle → Language → Prop)
    (T : Oracle → Prop) : Prop :=
  ∀ A, T A → SeparationAt P NP A

/-- A separating world refutes a uniform proof if the technique applies in
that world. Both the separation and applicability are explicit hypotheses. -/
theorem separation_refutes_uniform {Oracle : Type u} {P NP : Oracle → Language → Prop}
    {T : Oracle → Prop} {B : Oracle} (sep : SeparationAt P NP B) (hT : T B) :
    ¬ UniformEqualityProof P NP T := by
  intro uniform
  obtain ⟨L, hNP, hNotP⟩ := sep
  exact hNotP ((uniform B hT L).mpr hNP)

/-- An equality world dually refutes a uniform separation proof. -/
theorem equality_refutes_uniform {Oracle : Type u} {P NP : Oracle → Language → Prop}
    {T : Oracle → Prop} {A : Oracle} (eq : EqualAt P NP A) (hT : T A) :
    ¬ UniformSeparationProof P NP T := by
  intro uniform
  obtain ⟨L, hNP, hNotP⟩ := uniform A hT
  exact hNotP ((eq L).mpr hNP)

/-! A tiny countermodel checks that the definition carries semantic content.
It is illustrative only: these are not actual oracle machine classes. -/

def modelP (A : Bool) (_ : Language) : Prop := A = true
def modelNP (_ : Bool) (_ : Language) : Prop := True

theorem model_equal : EqualAt modelP modelNP true := by
  intro L
  simp [modelP, modelNP]

theorem model_separates : SeparationAt modelP modelNP false := by
  exact ⟨Issue532.Machines.SAT, trivial, by simp [modelP]⟩

/-- The constant-true predicate is not a valid proof of equality in both
worlds. This is the regression case hidden by PR #41's `∀ A, True`. -/
theorem constant_true_not_uniform :
    ¬ UniformEqualityProof modelP modelNP (fun _ => True) :=
  separation_refutes_uniform model_separates trivial

theorem constant_true_not_uniform_separation :
    ¬ UniformSeparationProof modelP modelNP (fun _ => True) :=
  equality_refutes_uniform model_equal trivial

/-- PR #41's universal barrier claim fails at `technique := False`:
`False → PEqualsNP` is valid without any complexity assumption. -/
theorem false_technique_counterexample : ¬ (¬ (False → PEqualsNP)) := by
  intro h
  exact h (fun impossible => False.elim impossible)

end Issue609.KnownBarriers
