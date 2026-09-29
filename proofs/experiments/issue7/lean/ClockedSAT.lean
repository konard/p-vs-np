import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue 7: the clocked-SAT sentence over the shared model

Issue #7 asked to "try prove P vs NP is undecidable", that is, independent of
ZFC. The roadmap `PROVING_P_VS_NP_UNDECIDABILITY.md` fixes the sentence whose
independence would be at stake:

```text
P = NP  ⇔  ∃ e,k ∀ input x, R(e,k,x)              (Σ⁰₂ form)
P ≠ NP  ⇔  ∀ e,k ∃ input x, ¬R(e,k,x)             (Π⁰₂ form)
```

Its first concrete task is to state that equivalence over the shared machine
model, with `SATHard` explicit, and to prove a clock lemma. This file does
that. It does **not** prove P = NP, P ≠ NP, or anything about ZFC.

The file proves:

* `runFor`, a fuel-bounded interpreter for `Complexity.Run`, is exact:
  `runFor m c n = some (t, b)` holds iff `Run m c t b` and `t ≤ n`
  (`runFor_iff`). This is the clock lemma;
* `clockCheck m p x : Bool` is the matrix `R(e,k,x)`: a total computable test,
  equivalent to the Prop-level condition used by `DecidesWithin`
  (`clockCheck_iff`);
* `ClockedSAT := ∃ m p, ∀ x, clockCheck m p x = true` is the Σ⁰₂ form. It is
  equivalent to `InP SAT` with no hypothesis (`clockedSAT_iff_inP_sat`). P = NP
  implies it with no hypothesis, because `SATInNP` is proved
  (`clockedSAT_of_pEqualsNP`). The converse needs the named premise `SATHard`
  (`pEqualsNP_of_clockedSAT`, `clockedSAT_iff_pEqualsNP`);
* the negation is the Π⁰₂ form with one fixed language, SAT, against every
  machine and clock (`not_clockedSAT_iff`). It implies P ≠ NP with no
  hypothesis (`pNotEqualsNP_of_pi2`); the converse needs `SATHard`
  (`pi2_of_pNotEqualsNP`);
* the quantifier order matters. "Every clocked machine fails on **some** NP
  language" is a theorem with no hypothesis (`per_machine_form_holds`), so it
  cannot express the open statement P ≠ NP;
* non-vacuity: `clockCheck` returns `true` and `false` on concrete inputs, and
  the rejecting machine is defeated at the empty formula for every clock.

`SATHard` (the hardness half of Cook–Levin) stays an explicit premise. The
translation of `ClockedSAT` into a ZFC sentence and any ZFC provability
predicate are **not** formalized here.
-/

namespace Issue7.ClockedSAT

open Complexity Issue532.Machines

/-! ## The clock lemma: a fuel-bounded interpreter for `Run` -/

/-- Run `m` from `c` for at most `fuel` steps. `some (t, b)` means the machine
halted with answer `b` after exactly `t` charged steps. -/
def runFor (m : Machine) : Config → Nat → Option (Nat × Bool)
  | _, 0 => none
  | c, fuel + 1 =>
    match step m c with
    | .inl b => some (1, b)
    | .inr c' => (runFor m c' fuel).map fun r => (r.1 + 1, r.2)

theorem runFor_sound (m : Machine) :
    ∀ (c : Config) (fuel t : Nat) (b : Bool),
      runFor m c fuel = some (t, b) → Run m c t b ∧ t ≤ fuel
  | _, 0, _, _, h => by simp [runFor] at h
  | c, fuel + 1, t, b, h => by
    unfold runFor at h
    split at h
    · rename_i b' hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Run.halt hs, by omega⟩
    · rename_i c' hs
      cases hr : runFor m c' fuel with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hrun, hle⟩ := runFor_sound m c' fuel r.1 r.2 hr
        exact ⟨Run.next hs hrun, by omega⟩

theorem runFor_complete {m : Machine} {c : Config} {t : Nat} {b : Bool}
    (h : Run m c t b) : ∀ fuel, t ≤ fuel → runFor m c fuel = some (t, b) := by
  induction h with
  | halt hs =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => simp [runFor, hs]
  | next hs _ ih =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => simp [runFor, hs, ih fuel (by omega)]

/-- The clock lemma: the interpreter returns exactly the runs that fit in the fuel. -/
theorem runFor_iff (m : Machine) (c : Config) (fuel t : Nat) (b : Bool) :
    runFor m c fuel = some (t, b) ↔ Run m c t b ∧ t ≤ fuel :=
  ⟨runFor_sound m c fuel t b, fun ⟨h, hle⟩ => runFor_complete h fuel hle⟩

/-! ## The matrix `R(e,k,x)` -/

/-- `R(e,k,x)`: `m` halts on `x` within the clock `p(|x|)` with the SAT answer. -/
def clockCheck (m : Machine) (p : Polynomial) (x : Word) : Bool :=
  match runFor m (initial x) (p.eval x.length) with
  | some (_, b) => b == SAT x
  | none => false

/-- The Prop-level matrix, as it occurs inside `DecidesWithin m p SAT`. -/
def ClockedCorrect (m : Machine) (p : Polynomial) (x : Word) : Prop :=
  ∃ t b, t ≤ p.eval x.length ∧ Run m (initial x) t b ∧ b = SAT x

/-- The computable test decides the Prop-level matrix. -/
theorem clockCheck_iff (m : Machine) (p : Polynomial) (x : Word) :
    clockCheck m p x = true ↔ ClockedCorrect m p x := by
  unfold clockCheck
  constructor
  · intro h
    split at h
    · rename_i t b hr
      obtain ⟨hrun, hle⟩ := (runFor_iff _ _ _ _ _).mp hr
      exact ⟨t, b, hle, hrun, by simpa using h⟩
    · cases h
  · rintro ⟨t, b, hle, hrun, rfl⟩
    rw [runFor_complete hrun _ hle]
    simp

/-! ## The Σ⁰₂ form and P = NP -/

/-- The Σ⁰₂ form: one machine and one polynomial clock are correct on SAT for
every input. -/
def ClockedSAT : Prop := ∃ (m : Machine) (p : Polynomial), ∀ x, clockCheck m p x = true

/-- `ClockedSAT` is `PolyDec SAT`, the machine-level SAT obligation. -/
theorem clockedSAT_iff_polyDec : ClockedSAT ↔ PolyDec SAT := by
  constructor
  · rintro ⟨m, p, h⟩
    exact ⟨m, p, fun x => (clockCheck_iff m p x).mp (h x)⟩
  · rintro ⟨m, p, h⟩
    exact ⟨m, p, fun x => (clockCheck_iff m p x).mpr (h x)⟩

/-- No hypothesis: the Σ⁰₂ form says exactly that SAT is in P. -/
theorem clockedSAT_iff_inP_sat : ClockedSAT ↔ InP SAT :=
  clockedSAT_iff_polyDec.trans (polyDec_iff_inP SAT)

/-- No hypothesis: P = NP gives the Σ⁰₂ form, because `SATInNP` is proved. -/
theorem clockedSAT_of_pEqualsNP (h : PEqualsNP) : ClockedSAT :=
  clockedSAT_iff_inP_sat.mpr (Issue532.SATVerifier.inP_sat_of_pEqualsNP' h)

/-- The converse needs the named hardness half of Cook–Levin. -/
theorem pEqualsNP_of_clockedSAT (hard : SATHard) (h : ClockedSAT) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (clockedSAT_iff_inP_sat.mp h)

/-- With `SATHard`, the Σ⁰₂ form is equivalent to P = NP. -/
theorem clockedSAT_iff_pEqualsNP (hard : SATHard) : ClockedSAT ↔ PEqualsNP :=
  ⟨pEqualsNP_of_clockedSAT hard, clockedSAT_of_pEqualsNP⟩

/-! ## The Π⁰₂ form and P ≠ NP -/

/-- The Π⁰₂ form: the single language SAT defeats every machine and clock. -/
theorem not_clockedSAT_iff :
    ¬ ClockedSAT ↔ ∀ (m : Machine) (p : Polynomial), ∃ x, clockCheck m p x = false := by
  constructor
  · intro h m p
    by_cases hx : ∃ x, clockCheck m p x = false
    · exact hx
    · exact absurd ⟨m, p, fun x => by
        cases hc : clockCheck m p x
        · exact absurd ⟨x, hc⟩ hx
        · rfl⟩ h
  · rintro h ⟨m, p, hall⟩
    obtain ⟨x, hx⟩ := h m p
    rw [hall x] at hx
    cases hx

/-- No hypothesis: the Π⁰₂ form gives P ≠ NP. -/
theorem pNotEqualsNP_of_pi2
    (h : ∀ (m : Machine) (p : Polynomial), ∃ x, clockCheck m p x = false) : PNotEqualsNP :=
  fun hp => not_clockedSAT_iff.mpr h (clockedSAT_of_pEqualsNP hp)

/-- The converse needs `SATHard`. -/
theorem pi2_of_pNotEqualsNP (hard : SATHard) (h : PNotEqualsNP) :
    ∀ (m : Machine) (p : Polynomial), ∃ x, clockCheck m p x = false :=
  not_clockedSAT_iff.mp fun hc => h (pEqualsNP_of_clockedSAT hard hc)

/-! ## Quantifier order: the per-machine form is a theorem

The corrected roadmap warns that "every polynomial-time machine fails to decide
some NP language" is not P ≠ NP. Here it is proved with no hypothesis: each
machine and clock fails on one of the two constant languages, and both are in P. -/

/-- The machine that halts with answer `b` in its first step. -/
def constMachine (b : Bool) : Machine := ⟨[List.replicate 4 (.halt b)]⟩

theorem step_constMachine (b : Bool) (c : Config) (h : c.state = 0) :
    step (constMachine b) c = .inl b := by
  obtain ⟨q, l, a, r⟩ := c
  simp only at h
  subst h
  cases a <;> rfl

theorem initial_state (x : Word) : (initial x).state = 0 := by
  cases x <;> rfl

theorem inP_const (b : Bool) : InP (fun _ => b) :=
  inP_of_decidesWithin (m := constMachine b) (p := ⟨1, 0⟩)
    fun x => ⟨1, b, by simp [Polynomial.eval], Run.halt (step_constMachine b _ (initial_state x)), rfl⟩

/-- For every machine and clock there is an NP language, even one in P, that the
machine does not decide within the clock. The language depends on the machine. -/
theorem per_machine_form_holds (m : Machine) (p : Polynomial) :
    ∃ L : Language, InNP L ∧ ¬ DecidesWithin m p L := by
  cases hr : runFor m (initial []) (p.eval ([] : Word).length) with
  | none =>
    refine ⟨fun _ => true, pSubsetNP _ (inP_const true), fun hd => ?_⟩
    obtain ⟨t, b, hle, hrun, _⟩ := hd []
    rw [runFor_complete hrun _ hle] at hr
    cases hr
  | some r =>
    refine ⟨fun _ => !r.2, pSubsetNP _ (inP_const (!r.2)), fun hd => ?_⟩
    obtain ⟨t, b, hle, hrun, hb⟩ := hd []
    rw [runFor_complete hrun _ hle, Option.some.injEq] at hr
    subst hr
    cases b <;> simp at hb

/-! ## Non-vacuity of `clockCheck` -/

/-- The empty table rejects in its first step. -/
def rejectAll : Machine := ⟨[]⟩

/-- `[[]]` has an empty clause, so the rejecting machine is right on it. -/
theorem clockCheck_rejectAll_empty_clause : clockCheck rejectAll ⟨1, 0⟩ (encodeCNF [[]]) = true := by
  decide

/-- The empty formula is satisfiable, so the rejecting machine is wrong on it. -/
theorem clockCheck_rejectAll_empty_cnf (p : Polynomial) :
    clockCheck rejectAll p (encodeCNF []) = false := by
  unfold clockCheck
  cases p.eval (encodeCNF []).length with
  | zero => rfl
  | succ n => rfl

/-- A concrete Π⁰₂ instance: one machine is defeated for every clock. -/
theorem rejectAll_defeated (p : Polynomial) : ∃ x, clockCheck rejectAll p x = false :=
  ⟨encodeCNF [], clockCheck_rejectAll_empty_cnf p⟩

/-- A zero clock admits no run, since every run charges at least one step. -/
theorem clockCheck_zero_clock (m : Machine) (x : Word) : clockCheck m ⟨0, 0⟩ x = false := by
  simp [clockCheck, Polynomial.eval, runFor]

end Issue7.ClockedSAT
