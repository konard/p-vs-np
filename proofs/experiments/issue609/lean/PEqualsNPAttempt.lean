import proofs.experiments.issue532.lean.SATVerifier

/-!
# A conditional P = NP route with the shared SAT semantics

This replaces the proof sketch in incoming PR #41. A candidate is an actual
`Complexity.Machine`, its bound measures `Complexity.Run` steps, and its answer
must equal `Issue532.Machines.SAT` on *every* word. Nothing here asserts that a
candidate exists. SAT membership in NP is proved by `SATVerifier.satInNP`;
the NP-hardness half of Cook--Levin remains the explicit premise `SATHard`.
-/

namespace Issue609.PEqualsNPAttempt

open Complexity Issue532.Machines

/-- The data needed for a polynomial-time SAT algorithm in the shared model. -/
structure Candidate where
  machine : Machine
  bound : Polynomial
  terminates : ∀ x : Word, ∃ t b,
    t ≤ bound.eval x.length ∧ Run machine (initial x) t b
  correct : ∀ x t b, Run machine (initial x) t b → b = SAT x

theorem candidate_decides (c : Candidate) : DecidesWithin c.machine c.bound SAT := by
  intro x
  obtain ⟨t, b, ht, hr⟩ := c.terminates x
  exact ⟨t, b, ht, hr, c.correct x t b hr⟩

/-- The missing research step is constructing `c`; SAT hardness is also named. -/
theorem pEqualsNP_of_candidate (hard : SATHard) (c : Candidate) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (inP_of_decidesWithin (candidate_decides c))

theorem candidate_of_inP (h : InP SAT) : Nonempty Candidate := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP SAT).mpr h
  refine ⟨⟨m, p, ?_, ?_⟩⟩
  · intro x
    obtain ⟨t, b, ht, hr, _⟩ := hm x
    exact ⟨t, b, ht, hr⟩
  · intro x t b hr
    obtain ⟨t', b', _, hr', hb'⟩ := hm x
    exact (run_deterministic hr hr').2.trans hb'

/-- The reverse direction uses the proved SAT verifier. With the named
`SATHard` premise, the candidate obligation is exactly P = NP. -/
theorem candidate_iff_pEqualsNP (hard : SATHard) : Nonempty Candidate ↔ PEqualsNP := by
  constructor
  · rintro ⟨c⟩
    exact pEqualsNP_of_candidate hard c
  · intro h
    exact candidate_of_inP (inP_sat_of_pEqualsNP Issue532.SATVerifier.satInNP h)

/-- Correctness means satisfiability of the decoded CNF, including negative
instances, rather than agreement with a constant `True` predicate. -/
theorem candidate_on_encodings (c : Candidate) (φ : CNF) :
    ∃ t b, t ≤ c.bound.eval (encodeCNF φ).length ∧
      Run c.machine (initial (encodeCNF φ)) t b ∧
      (b = true ↔ Satisfiable φ) := by
  obtain ⟨t, b, ht, hr⟩ := c.terminates (encodeCNF φ)
  refine ⟨t, b, ht, hr, ?_⟩
  rw [c.correct _ _ _ hr]
  exact sat_encode φ

/-- Regression witnesses: the shared SAT language has both answers. -/
theorem sat_has_yes_instance : SAT (encodeCNF ([] : CNF)) = true := by decide
theorem sat_has_no_instance : SAT (encodeCNF ([[]] : CNF)) = false := by decide

/-- Non-vacuity of the machine-cost obligation: some languages are outside P. -/
theorem not_every_language_inP : ¬ (∀ L : Language, InP L) := by
  intro h
  exact diag_not_inP (h Diag)

end Issue609.PEqualsNPAttempt
