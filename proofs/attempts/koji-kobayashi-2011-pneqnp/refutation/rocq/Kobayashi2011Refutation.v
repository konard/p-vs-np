(*
  Refutation of Koji Kobayashi's 2011 proof attempt.

  The formal point is that a failed dependency-evaluation strategy does not
  establish language non-membership in a complexity class.
*)

Require Import Coq.Strings.String.

Module Kobayashi2011RefutationAttempt.

Definition Language := string -> Prop.

Record ComplexityClass := {
  contains : Language -> Prop
}.

Definition InClass (C : ComplexityClass) (X : Language) : Prop :=
  contains C X.

Definition Strategy := Language -> Prop.

Definition StrategyResourceFailure (S : Strategy) (X : Language) : Prop :=
  S X.

Definition ClassLowerBound (C : ComplexityClass) (X : Language) : Prop :=
  ~ InClass C X.

Definition StrategyUniversalForClass
    (S : Strategy) (C : ComplexityClass) (X : Language) : Prop :=
  InClass C X -> S X.

Parameter DependencyMaterialization RotatePathEnumeration : Strategy.
Parameter AL NC NL L : ComplexityClass.
Parameter CHAOS ORDER LAYER TWINE : Language.

Parameter chaos_strategy_failure :
  StrategyResourceFailure DependencyMaterialization CHAOS.
Parameter order_strategy_failure :
  StrategyResourceFailure DependencyMaterialization ORDER.
Parameter layer_strategy_failure :
  StrategyResourceFailure DependencyMaterialization LAYER.
Parameter twine_strategy_failure :
  StrategyResourceFailure RotatePathEnumeration TWINE.

Theorem chaos_gap_documented :
  StrategyResourceFailure DependencyMaterialization CHAOS.
Proof. exact chaos_strategy_failure. Qed.

Theorem order_gap_documented :
  StrategyResourceFailure DependencyMaterialization ORDER.
Proof. exact order_strategy_failure. Qed.

Theorem layer_gap_documented :
  StrategyResourceFailure DependencyMaterialization LAYER.
Proof. exact layer_strategy_failure. Qed.

Theorem twine_gap_documented :
  StrategyResourceFailure RotatePathEnumeration TWINE.
Proof. exact twine_strategy_failure. Qed.

Theorem strategy_failure_needs_extra_lower_bound :
  forall (S : Strategy) (C : ComplexityClass) (X : Language),
    StrategyResourceFailure S X ->
    StrategyUniversalForClass S C X ->
    InClass C X ->
    False.
Proof.
  intros S C X _failure universal in_class.
  pose proof (universal in_class) as _strategy_used.
  (*
    This is the missing step in Kobayashi's proof. One would still need a
    theorem saying that this strategy's resource failure rules out every
    machine in C. The paper does not provide such a theorem.
  *)
Admitted.

End Kobayashi2011RefutationAttempt.
