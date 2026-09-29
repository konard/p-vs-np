/-!
  Issue #7: what excluded middle actually proves.

  `HasClockedSATDecider` illustrates the Σ⁰₂ form of P = NP: the outer
  existential choices are a machine and a polynomial clock, and the remaining
  condition checks every input. The Bool predicate is a placeholder for the
  finite simulation and SAT correctness test; this file does not construct that
  encoding or prove its equivalence to a full formalization of P = NP.

  The theorems below prove excluded middle only. Neither branch is established,
  and no result about provability or independence from ZFC follows.
-/

namespace ShoenfieldAbsoluteness

variable (correctClockedSAT : Nat → Nat → Nat → Bool)

def HasClockedSATDecider : Prop :=
  ∃ machine clock : Nat,
    ∀ input : Nat, correctClockedSAT machine clock input = true

theorem clockedSAT_excluded_middle :
    HasClockedSATDecider correctClockedSAT ∨
      ¬HasClockedSATDecider correctClockedSAT :=
  Classical.em _

/-- Provability is a separate predicate. Excluded middle does not supply either
    a proof of the proposition or a proof of its negation in a given theory. -/
def Independent (Provable : Prop → Prop) (φ : Prop) : Prop :=
  ¬Provable φ ∧ ¬Provable (¬φ)

theorem excluded_middle_compatible_with_independence
    (Provable : Prop → Prop) (φ : Prop) (h : Independent Provable φ) :
    (φ ∨ ¬φ) ∧ Independent Provable φ :=
  ⟨Classical.em φ, h⟩

#check clockedSAT_excluded_middle
#check excluded_middle_compatible_with_independence

end ShoenfieldAbsoluteness
