import proofs.experiments.issue532.lean.Idea41

/-!
# Williams' method: regression checks

The formal framework is `Issue532.Idea41`, over the shared `Complexity.Machine`
and NAND circuit model. This file keeps the original experiment's path while
checking two mistakes that its former standalone model allowed: a zero-cost
answer oracle and treating a malformed circuit as a SAT instance.

`Idea41.williams_method` concludes `NEXP ⊄ P/poly` only from the explicit
`NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup`, and `FastCircuitSAT`
premises. It does not conclude `NP ⊄ P/poly` or `P ≠ NP` from the fast
algorithm.
-/

namespace WilliamsFramework

open Complexity Issue532.Circuits Issue532.Idea41

/-- Every answer from a shared machine costs at least one `Run` step. -/
theorem no_zero_step (m : Machine) (n : Nat) (C : Circuit) (b : Bool) :
    ¬ Run m (initial (encCircuit n C)) 0 b := by
  intro h
  cases h

/-- A classical answer function with a reported cost of zero cannot be
substituted for a machine, regardless of its answers. -/
theorem no_zero_cost_oracle (answer : Nat → Circuit → Bool) :
    ¬ ∃ m : Machine, ∀ n C, Run m (initial (encCircuit n C)) 0 (answer n C) := by
  rintro ⟨m, hm⟩
  exact no_zero_step m 1 [] (answer 1 []) (hm 1 [])

/-- Gate zero cannot read wire one when there is only one input wire. The
encoded instance is therefore rejected even if its output happens to be
true under the default out-of-range wire value. -/
theorem malformed_circuit_can_output_true :
    output [true] [(1, 0)] = true := by
  decide

theorem malformed_circuit_rejected :
    CircuitSAT (encCircuit 1 [(1, 0)]) = false := by
  cases h : CircuitSAT (encCircuit 1 [(1, 0)]) with
  | false => rfl
  | true =>
    have hw : WF 1 [(1, 0)] := ((circuitSAT_encode 1 [(1, 0)]).mp h).1
    simp [WF, WFfrom] at hw

end WilliamsFramework
