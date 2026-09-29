/-
  FeinsteinProof.lean - Formalization of Craig Alan Feinstein's 2003-04 P≠NP proof attempt

  This file formalizes the structure of Feinstein's argument, showing how he attempted
  to prove P ≠ NP using a restricted computational model approach.

  NOTE: This formalization represents the CLAIMED proof structure. The errors and
  refutation are in the refutation/ directory.

  Author: Formalization for p-vs-np repository
  Date: 2026-01-18
  Related: Issue #434, Woeginger's list entry #11
-/

/-! # Part 1: Basic Computational Definitions -/

/-- A problem instance (abstract representation) -/
def ProblemInstance := Nat

/-- A solution to a problem instance -/
def Solution := Nat

/-- An algorithm maps problem instances to solutions -/
structure Algorithm where
  solve : ProblemInstance → Solution
  runningTime : ProblemInstance → Nat

/-- NP-complete problem (abstract) -/
structure NPCompleteProblem where
  verify : ProblemInstance → Solution → Bool

/-! # Part 2: Restricted Computational Models -/

/-- Abstract computational model with specific restrictions -/
structure ComputationalModel where
  allowedOperations : List String
  operationCosts : String → Nat → Nat

/-- The unrestricted/general Turing machine model -/
def turingMachineModel : ComputationalModel := {
  allowedOperations := ["read", "write", "move", "branch"],
  operationCosts := fun _ n => n
}

/-- Example: A restricted model that only allows certain types of operations
    This represents the kind of model Feinstein would have defined -/
def feinsteinRestrictedModel : ComputationalModel := {
  allowedOperations := ["compare", "add"],
  operationCosts := fun op n =>
    match op with
    | "compare" => n * n
    | "add" => n
    | _ => n
}

/-- Running time of an algorithm in a specific model -/
def runningTimeInModel (alg : Algorithm) (_model : ComputationalModel) : ProblemInstance → Nat :=
  fun inst => alg.runningTime inst

/-! # Part 3: Lower Bounds -/

/-- An algorithm has a lower bound in a model -/
def hasLowerBound (alg : Algorithm) (model : ComputationalModel) (bound : Nat → Nat) : Prop :=
  ∀ inst, runningTimeInModel alg model inst ≥ bound inst

/-- A problem requires at least some time in a model -/
def problemLowerBound (problem : NPCompleteProblem) (model : ComputationalModel)
    (bound : Nat → Nat) : Prop :=
  ∀ alg : Algorithm,
    (∀ inst sol, alg.solve inst = sol → problem.verify inst sol = true) →
    hasLowerBound alg model bound

/-- Exponential lower bound -/
def exponentialBound (n : Nat) : Nat := 2^(n/2)

/-! # Part 4: Feinstein's Claimed Proof Structure -/

/-
  Feinstein's proof had three main steps:

  1. CLAIM: Proved lower bound in restricted model
     - Within his restricted computational model, NP-complete problems require
       exponential time

  2. CLAIM: Transfer principle
     - Lower bounds in the restricted model imply lower bounds in general
       Turing machine computation

  3. CONCLUSION: P ≠ NP
     - Combining (1) and (2), NP-complete problems require exponential time
       in general, so P ≠ NP
-/

/-- Step 1: Feinstein's claimed lower bound in restricted model
    This axiom represents what Feinstein claimed to have proven -/
axiom feinsteinRestrictedLowerBound :
  ∀ (problem : NPCompleteProblem),
    problemLowerBound problem feinsteinRestrictedModel exponentialBound

/-- Step 2: Feinstein's transfer principle (THE ERROR)
    This axiom represents Feinstein's claimed transfer principle.
    This is where the proof fails - see refutation/ for why. -/
axiom feinsteinTransferPrinciple :
  ∀ (problem : NPCompleteProblem) (bound : Nat → Nat),
    problemLowerBound problem feinsteinRestrictedModel bound →
    problemLowerBound problem turingMachineModel bound

/-- Step 3: Feinstein's conclusion
    Combining the restricted model lower bound with the transfer principle -/
theorem feinsteinConclusion :
  ∀ (problem : NPCompleteProblem),
    problemLowerBound problem turingMachineModel exponentialBound := by
  intro problem
  -- Apply the transfer principle to the restricted model lower bound
  apply feinsteinTransferPrinciple
  -- Use the claimed restricted model lower bound
  exact feinsteinRestrictedLowerBound problem

/-!
# Summary

This file formalizes the STRUCTURE of Feinstein's 2003-04 proof attempt.
The proof relies on:

1. `feinsteinRestrictedLowerBound` - A lower bound proven within a restricted model
2. `feinsteinTransferPrinciple` - A claim that restricted model bounds transfer to general computation
3. `feinsteinConclusion` - The logical consequence of (1) and (2)

The proof structure is valid IF the axioms are true. However, `feinsteinTransferPrinciple`
is FALSE - this is demonstrated in the refutation/ directory.

The counterexample that invalidated Feinstein's proof showed that an algorithm
unavailable in his restricted model could solve the problem efficiently in general
computation, thereby violating the transfer principle.
-/
