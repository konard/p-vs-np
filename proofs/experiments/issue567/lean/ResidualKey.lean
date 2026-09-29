import proofs.experiments.issue532.lean.Machines

/-!
# Issue 567: a scoped residual-state key counterexample

This challenges the proposed *coarse size key* for memoizing residual CNFs:
`(number of variables, number of clauses, encoded bit length)`. It says
nothing about a solver using a full canonical CNF key, and gives no time lower
bound for unrestricted SAT algorithms.
-/

namespace Issue567.ResidualKey

open Issue532.Machines

def posUnit : Clause := [⟨0, true⟩]
def negUnit : Clause := [⟨0, false⟩]

/-- Both families have `k + 2` clauses and use only variable zero. -/
def satFamily (k : Nat) : CNF := posUnit :: posUnit :: List.replicate k posUnit
def unsatFamily (k : Nat) : CNF := negUnit :: posUnit :: List.replicate k posUnit

/-- The exact information retained by the challenged memoization key. -/
def coarseKey (φ : CNF) : Nat × Nat × Nat :=
  (numVars φ, φ.length, (encodeCNF φ).length)

theorem coarseKey_collision (k : Nat) :
    coarseKey (satFamily k) = coarseKey (unsatFamily k) := by
  simp [coarseKey, satFamily, unsatFamily, posUnit, negUnit,
    numVars, clauseBound, encodeCNF, encodeClause, encodeLit, ticks]

theorem satFamily_satisfiable (k : Nat) : Satisfiable (satFamily k) := by
  have hrep : ∀ j : Nat,
      evalCNF (fun _ => true) (List.replicate j posUnit) = true := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        change (evalClause (fun _ => true) posUnit &&
          evalCNF (fun _ => true) (List.replicate j posUnit)) = true
        rw [show evalClause (fun _ => true) posUnit = true from rfl, Bool.true_and]
        exact ih
  refine ⟨fun _ => true, ?_⟩
  change (evalClause (fun _ => true) posUnit &&
    (evalClause (fun _ => true) posUnit &&
      evalCNF (fun _ => true) (List.replicate k posUnit))) = true
  rw [show evalClause (fun _ => true) posUnit = true from rfl, Bool.true_and,
    Bool.true_and]
  exact hrep k

theorem unsatFamily_unsatisfiable (k : Nat) : ¬ Satisfiable (unsatFamily k) := by
  rintro ⟨a, ha⟩
  cases h : a 0 <;>
    simp [unsatFamily, evalCNF, evalClause, evalLit, posUnit, negUnit, h] at ha

/-- One variable-zero unit clause costs four bits in the shared encoding. -/
theorem length_replicate_posUnit (k : Nat) :
    (encodeCNF (List.replicate k posUnit)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (encodeClause posUnit ++ encodeCNF (List.replicate k posUnit)).length =
        4 * (k + 1)
      rw [List.length_append, show (encodeClause posUnit).length = 4 from rfl, ih]
      omega

theorem family_encoded_lengths (k : Nat) :
    (encodeCNF (satFamily k)).length = 4 * (k + 2) ∧
    (encodeCNF (unsatFamily k)).length = 4 * (k + 2) := by
  change (encodeClause posUnit ++ encodeClause posUnit ++
      encodeCNF (List.replicate k posUnit)).length = 4 * (k + 2) ∧
    (encodeClause negUnit ++ encodeClause posUnit ++
      encodeCNF (List.replicate k posUnit)).length = 4 * (k + 2)
  simp only [List.length_append, length_replicate_posUnit]
  rw [show (encodeClause posUnit).length = 4 from rfl,
    show (encodeClause negUnit).length = 4 from rfl]
  omega

/-- For every `k`, the key merges opposite SAT answers at encoded length
`4 * (k + 2)`. Any cache that reuses answers solely by this key is unsound. -/
theorem coarseKey_not_satisfiability_complete (k : Nat) :
    coarseKey (satFamily k) = coarseKey (unsatFamily k) ∧
    Satisfiable (satFamily k) ∧ ¬ Satisfiable (unsatFamily k) :=
  ⟨coarseKey_collision k, satFamily_satisfiable k, unsatFamily_unsatisfiable k⟩

end Issue567.ResidualKey
