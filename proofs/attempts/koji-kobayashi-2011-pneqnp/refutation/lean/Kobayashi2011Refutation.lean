/-
  Refutation of Koji Kobayashi's 2011 proof attempt.

  The file formalizes the central logical gap: a failed evaluation strategy for
  a language is not the same thing as non-membership of that language in a
  complexity class.
-/

namespace Kobayashi2011Refutation

def Language := String → Prop

structure ComplexityClass where
  contains : Language → Prop

def InClass (C : ComplexityClass) (L : Language) : Prop :=
  C.contains L

def Strategy := Language → Prop

/-- A strategy-specific lower bound says only that one evaluation discipline fails. -/
def StrategyFailsForClass (S : Strategy) (C : ComplexityClass) (X : Language) : Prop :=
  S X ∧ ¬ InClass C X

/-- A real class lower bound must exclude the language from the class itself. -/
def ClassLowerBound (C : ComplexityClass) (X : Language) : Prop :=
  ¬ InClass C X

/-
  Kobayashi's prose supplies reasons of the first kind: particular dependency
  bookkeeping strategies allegedly exceed space or parallel-time bounds.
-/
axiom DependencyMaterialization : Strategy
axiom RotatePathEnumeration : Strategy

axiom AL : ComplexityClass
axiom NC : ComplexityClass
axiom NL : ComplexityClass
axiom LOGSPACE : ComplexityClass
axiom CHAOS : Language
axiom ORDER : Language
axiom LAYER : Language
axiom TWINE : Language

/-
  What would be needed and is not provided:
  a theorem saying that every correct algorithm in the target class must use the
  challenged strategy. Without this universality bridge, the lower bound does
  not follow.
-/
def StrategyUniversalForClass
    (S : Strategy) (C : ComplexityClass) (X : Language) : Prop :=
  InClass C X → S X

theorem missing_bridge_for_strategy_lower_bounds
    (S : Strategy) (C : ComplexityClass) (X : Language) :
    StrategyFailsForClass S C X → ClassLowerBound C X := by
  intro h
  exact h.right

/-
  The theorem above is intentionally trivial because StrategyFailsForClass was
  defined to include the class lower bound already. Kobayashi's paper does not
  establish such a proposition. It establishes, at most, that a named strategy
  would require too much space or time.
-/
def StrategyResourceFailure (S : Strategy) (X : Language) : Prop :=
  S X

theorem resource_failure_does_not_imply_class_lower_bound
    (S : Strategy) (C : ComplexityClass) (X : Language) :
    StrategyResourceFailure S X →
    StrategyUniversalForClass S C X →
    InClass C X →
    False := by
  intro _hFailure hUniversal hInClass
  -- Even adding universality merely says this particular strategy is used.
  -- A real contradiction still requires a formal theorem connecting the
  -- strategy's resource failure to non-membership. That theorem is absent.
  have _hStrategy : S X := hUniversal hInClass
  -- This is exactly where Kobayashi needs a formal impossibility theorem.
  sorry

/-
  Concrete missing bridges for the four named languages.
-/
axiom chaos_strategy_failure : StrategyResourceFailure DependencyMaterialization CHAOS
axiom order_strategy_failure : StrategyResourceFailure DependencyMaterialization ORDER
axiom layer_strategy_failure : StrategyResourceFailure DependencyMaterialization LAYER
axiom twine_strategy_failure : StrategyResourceFailure RotatePathEnumeration TWINE

theorem chaos_gap_documented :
    StrategyResourceFailure DependencyMaterialization CHAOS := by
  exact chaos_strategy_failure

theorem order_gap_documented :
    StrategyResourceFailure DependencyMaterialization ORDER := by
  exact order_strategy_failure

theorem layer_gap_documented :
    StrategyResourceFailure DependencyMaterialization LAYER := by
  exact layer_strategy_failure

theorem twine_gap_documented :
    StrategyResourceFailure RotatePathEnumeration TWINE := by
  exact twine_strategy_failure

end Kobayashi2011Refutation
