import proofs.experiments.issue532.lean.Idea41Core
import proofs.experiments.issue532.lean.CircuitVerifier

set_option maxRecDepth 4096

namespace Issue532.Idea41
open Complexity Issue532.Machines Issue532.Circuits

/-- Circuit satisfiability has a finite, polynomial-time certificate verifier. -/
theorem circuitSATInNP : CircuitSATInNP := by
  apply circuitSATInNP_of_verifier_run Issue532.CircuitVerifier.candidate ⟨221184, 3⟩
  intro x cert _
  obtain ⟨t, ht, hr⟩ := Issue532.CircuitVerifier.verifier_run x cert
  refine ⟨t, Nat.le_trans ht ?_, hr⟩
  have h : x.length + cert.length + 12 ≤ 6 * (x.length + cert.length + 2) := by omega
  have hb := Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left h 3)
  simpa only [Polynomial.eval, Nat.mul_pow, Nat.reducePow, ← Nat.mul_assoc,
    Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] using hb

/-- `P = NP` implies the obligation. -/
theorem fastCircuitSAT_of_pEqualsNP (h : PEqualsNP) : FastCircuitSAT :=
  fastCircuitSAT_of_inP (h CircuitSAT circuitSATInNP)

/-- A polynomial-time SAT decider implies the obligation, given Cook–Levin. -/
theorem fastCircuitSAT_of_inP_sat (hard : SATHard) (h : InP SAT) :
    FastCircuitSAT :=
  fastCircuitSAT_of_pEqualsNP (pEqualsNP_of_inP_sat hard h)

/-- **Bridge.** Refuting the obligation proves `P ≠ NP`. -/
theorem pNotEqualsNP_of_not_fastCircuitSAT (h : ¬ FastCircuitSAT) :
    PNotEqualsNP :=
  fun hEq => h (fastCircuitSAT_of_pEqualsNP hEq)

/-- `NEXP ⊆ P/poly` would prove `P ≠ NP`, given the known theorems. -/
theorem pNotEqualsNP_of_nexpSubsetPPoly (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (hsub : NEXPSubsetPPoly) :
    PNotEqualsNP :=
  pNotEqualsNP_of_not_fastCircuitSAT (not_fastCircuitSAT_of_nexpSubsetPPoly hier ewl speedup hsub)

/-- `P = NP` would refute `NEXP ⊆ P/poly`, given the known theorems. -/
theorem not_nexpSubsetPPoly_of_pEqualsNP (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (h : PEqualsNP) :
    ¬ NEXPSubsetPPoly :=
  williams_method hier ewl speedup (fastCircuitSAT_of_pEqualsNP h)

end Issue532.Idea41
