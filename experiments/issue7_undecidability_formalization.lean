/-!
  Issue #7: schematic forcing invariance, conditional on arithmetic absoluteness.

  This file does not formalize ZFC, forcing, Shoenfield's theorem, or P = NP.
  `sameArithmetic` and `arithmeticAbsolute` are explicit hypotheses. The result
  says that a forcing extension satisfying those hypotheses cannot change the
  truth value of an arithmetic statement. It says nothing about whether either
  statement is provable in ZFC.
-/

namespace PvsNPIndependenceAttempt

variable {Model : Type}
variable (PEqualsNP : Model → Prop)
variable (sameArithmetic : Model → Model → Prop)

/-- A schematic instance of forcing invariance. A real application must prove
    the hypotheses for its actual models and its encoding of P = NP. -/
theorem forcing_preserves_pvsnp
    (arithmeticAbsolute :
      ∀ ground extension : Model,
        sameArithmetic ground extension →
          (PEqualsNP ground ↔ PEqualsNP extension))
    (ground extension : Model)
    (hSame : sameArithmetic ground extension) :
    PEqualsNP ground ↔ PEqualsNP extension :=
  arithmeticAbsolute ground extension hSame

theorem no_forcing_truth_flip
    (arithmeticAbsolute :
      ∀ ground extension : Model,
        sameArithmetic ground extension →
          (PEqualsNP ground ↔ PEqualsNP extension))
    (ground extension : Model)
    (hSame : sameArithmetic ground extension) :
    ¬(PEqualsNP ground ∧ ¬PEqualsNP extension) := by
  intro ⟨hGround, hExtension⟩
  exact hExtension
    ((forcing_preserves_pvsnp PEqualsNP sameArithmetic arithmeticAbsolute
      ground extension hSame).mp hGround)

/-- This is excluded middle for a model's proposition, not a proof of either
    branch in any formal theory. -/
theorem classical_answer (M : Model) :
    PEqualsNP M ∨ ¬PEqualsNP M :=
  Classical.em _

#check forcing_preserves_pvsnp
#check no_forcing_truth_flip
#check classical_answer

end PvsNPIndependenceAttempt
