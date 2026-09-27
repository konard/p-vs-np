import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 01 — Exact SAT algorithm (brute force as the baseline)

This file develops the most direct route to P = NP: "write a uniform SAT
decider and prove it correct and fast".  It works in the repository's shared
machine model `proofs/experiments/issue532/lean/Machines.lean` (finite-table
single-tape Turing machines, `InP`, `PolyReduces`, and the language `SAT` of
encoded CNFs).  The CNF syntax, the brute-force decider `bruteForce`, its
correctness `bruteForce_correct`, the enumeration `allAssignments` with
`mem_allAssignments_iff`, and the lossless encoding `encodeCNF`
(`decode_encode`, `encode_injective`) are taken from that shared layer.

What this file proves (all general, for every CNF formula and every `n`):

* `length_allAssignments`, `nodup_allAssignments` — the enumeration
  `allAssignments n` has exactly `2^n` entries, without repetition.
* `bruteForceCost_le`, `bruteForceCost_unsat`, `hardFamily_cost` — the
  number of formula evaluations performed by brute force is at most `2^n`,
  is exactly `2^n` on every unsatisfiable formula, and for every `n ≥ 1`
  there is an unsatisfiable formula mentioning exactly the variables
  `0, …, n-1` on which it is `2^n`.
* `numVars_le_encodingLength`, `bruteForceCost_le_exp_size` — the cost is at
  most `2^(input length)` for the binary encoding `encodeCNF`.
* The open obligation `PolySATDecider := InP SAT` and its conditional
  theorems: `pEqualsNP_of_polySATDecider` (under the named hypothesis
  `SATHard`), `polySATDecider_of_pEqualsNP` (under `SATInNP`),
  `polySATDecider_iff` (under `CookLevin`), `pNotEqualsNP_of_not_polySATDecider`,
  and `polySAT_agrees_with_bruteForce` (the polynomial-time machine outputs
  exactly the brute-force answer on every encoded formula).
* `polySATDecider_not_trivial` — non-vacuity: `InP` is not satisfied by every
  language, so the obligation is a genuine constraint on `SAT`.

The Cook–Levin theorem is not mechanised; it enters only as the explicit
hypotheses `SATHard`, `SATInNP` or `CookLevin` of the shared layer.

Verdict: brute force is refuted as a polynomial-time algorithm (it performs
`2^n` evaluations on every unsatisfiable input with `n` variables); the route
"a uniform polynomial-time SAT decider" is `InP SAT`, which under Cook–Levin
is equivalent to P = NP and remains open.
-/

namespace Issue532.Idea01

open Complexity Issue532.Machines

/-! ## The enumeration of assignments -/

/-- The enumeration has exactly `2^n` entries. -/
theorem length_allAssignments (n : Nat) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

theorem nodup_map_cons (b : Bool) (L : List (List Bool)) (h : L.Nodup) :
    (L.map (b :: ·)).Nodup := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy hyx => h.1 ?_, ih h.2⟩
    have : y = x := List.cons.inj hyx |>.2
    exact this ▸ hy

/-- The enumeration has no repetitions: it lists `2^n` *distinct* vectors. -/
theorem nodup_allAssignments (n : Nat) : (allAssignments n).Nodup := by
  induction n with
  | zero => simp [allAssignments]
  | succ n ih =>
    simp only [allAssignments]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons false _ ih, nodup_map_cons true _ ih, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨w, _, rfl⟩ := hy
    exact Bool.noConfusion (List.cons.inj hxy).1

/-! ## Cost: number of formula evaluations -/

/-- Evaluations performed by a left-to-right search that stops at the first
satisfying vector. -/
def searchCount (φ : CNF) : List (List Bool) → Nat
  | [] => 0
  | v :: vs => if evalCNF (toAssign v) φ then 1 else 1 + searchCount φ vs

def bruteForceCost (n : Nat) (φ : CNF) : Nat := searchCount φ (allAssignments n)

theorem searchCount_le (φ : CNF) (L : List (List Bool)) : searchCount φ L ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons v L ih =>
    simp only [searchCount, List.length_cons]
    split <;> omega

theorem searchCount_all_false (φ : CNF) (L : List (List Bool))
    (h : ∀ v ∈ L, evalCNF (toAssign v) φ = false) : searchCount φ L = L.length := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [searchCount, List.length_cons]
    rw [h v (List.mem_cons_self ..), ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp; omega

/-- Brute force never uses more than `2^n` evaluations. -/
theorem bruteForceCost_le (n : Nat) (φ : CNF) : bruteForceCost n φ ≤ 2 ^ n := by
  have := searchCount_le φ (allAssignments n)
  rw [length_allAssignments] at this
  exact this

/-- On every unsatisfiable formula brute force uses exactly `2^n` evaluations. -/
theorem bruteForceCost_unsat (n : Nat) (φ : CNF) (h : ¬ Satisfiable φ) :
    bruteForceCost n φ = 2 ^ n := by
  unfold bruteForceCost
  rw [searchCount_all_false φ _ ?_, length_allAssignments]
  intro v _
  cases hv : evalCNF (toAssign v) φ with
  | false => rfl
  | true => exact absurd ⟨toAssign v, hv⟩ h

/-- `k` tautological clauses `x_i ∨ ¬x_i`, `i < k`. -/
def tautChain : Nat → CNF
  | 0 => []
  | k + 1 => [⟨k, true⟩, ⟨k, false⟩] :: tautChain k

/-- An unsatisfiable formula mentioning exactly the variables `0, …, n-1`. -/
def hardFamily (n : Nat) : CNF := [⟨0, true⟩] :: [⟨0, false⟩] :: tautChain n

theorem numVars_tautChain (k : Nat) : numVars (tautChain k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tautChain, numVars, clauseBound, ih]; omega

theorem hardFamily_unsat (n : Nat) : ¬ Satisfiable (hardFamily n) := by
  intro ⟨a, ha⟩
  simp only [hardFamily, evalCNF, evalClause, evalLit, Bool.or_false,
    Bool.and_eq_true] at ha
  obtain ⟨h1, h2, _⟩ := ha
  rw [beq_iff_eq] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Exponential cost for every size: for `n ≥ 1`, `hardFamily n` has exactly
`n` variables, is unsatisfiable, and brute force performs `2^n` evaluations. -/
theorem hardFamily_cost (n : Nat) (hn : 1 ≤ n) :
    numVars (hardFamily n) = n ∧ ¬ Satisfiable (hardFamily n) ∧
      bruteForceCost (numVars (hardFamily n)) (hardFamily n) = 2 ^ n := by
  have hv : numVars (hardFamily n) = n := by
    simp only [hardFamily, numVars, clauseBound, numVars_tautChain]; omega
  exact ⟨hv, hardFamily_unsat n, by rw [hv]; exact bruteForceCost_unsat n _ (hardFamily_unsat n)⟩

theorem length_ticks (v : Nat) : (ticks v).length = 2 * v := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [ticks, List.length_cons, ih]; omega

theorem clauseBound_le_length (c : Clause) : clauseBound c ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [clauseBound, encodeClause]
  | cons l c ih =>
    simp only [clauseBound, encodeClause, encodeLit, List.length_append, length_ticks,
      List.length_cons, List.length_nil]
    omega

/-- The number of variables is at most the input length. -/
theorem numVars_le_encodingLength (φ : CNF) : numVars φ ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => exact Nat.le_refl 0
  | cons c φ ih =>
    simp only [numVars, encodeCNF, List.length_append]
    have := clauseBound_le_length c
    omega

/-- Brute force is at most exponential in the input length. -/
theorem bruteForceCost_le_exp_size (φ : CNF) :
    bruteForceCost (numVars φ) φ ≤ 2 ^ (encodeCNF φ).length :=
  Nat.le_trans (bruteForceCost_le _ φ)
    (Nat.pow_le_pow_right (by decide) (numVars_le_encodingLength φ))


/-! ## The open obligation, in the shared machine model -/

/-- **Open obligation.**  `SAT` (satisfiability of encoded CNFs) is decided
by a single finite-table machine within a single polynomial bound on every
input word.  Stated in the shared machine model as `InP SAT`; it is a
`def … : Prop` and is never postulated. -/
def PolySATDecider : Prop := InP SAT

/-- The obligation, phrased with an explicit machine and polynomial. -/
theorem polySATDecider_iff_polyDec : PolySATDecider ↔ PolyDec SAT :=
  (polyDec_iff_inP SAT).symm

/-- Conditional theorem: under the named hypothesis `SATHard` (the hardness
half of Cook–Levin, not mechanised here) the obligation implies P = NP. -/
theorem pEqualsNP_of_polySATDecider (hard : SATHard) (h : PolySATDecider) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard h

/-- Conversely, under the named hypothesis `SATInNP`, P = NP implies the
obligation. -/
theorem polySATDecider_of_pEqualsNP (mem : SATInNP) (h : PEqualsNP) : PolySATDecider :=
  inP_sat_of_pEqualsNP mem h

/-- Under the named hypothesis `CookLevin` the obligation is exactly P = NP. -/
theorem polySATDecider_iff (hCL : CookLevin) : PolySATDecider ↔ PEqualsNP :=
  inP_sat_iff hCL

/-- Refuting the obligation would separate P from NP (given `SATInNP`). -/
theorem pNotEqualsNP_of_not_polySATDecider (mem : SATInNP) (h : ¬ PolySATDecider) :
    PNotEqualsNP :=
  fun hp => h (polySATDecider_of_pEqualsNP mem hp)

/-- Conditional theorem: a machine witnessing the obligation must output,
within its polynomial budget, exactly the brute-force answer on the encoding
of every CNF.  Brute force is the reference semantics any fast decider must
reproduce. -/
theorem polySAT_agrees_with_bruteForce (h : PolySATDecider) :
    ∃ (M : Machine) (p : Polynomial), ∀ φ : CNF, ∃ t,
      t ≤ p.eval (encodeCNF φ).length ∧
        Run M (initial (encodeCNF φ)) t (bruteForce (numVars φ) φ) := by
  obtain ⟨M, p, hM⟩ := inP_sat_on_encodings h
  refine ⟨M, p, fun φ => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hM φ
  have hbf := bruteForce_correct φ
  have : b = bruteForce (numVars φ) φ := by
    cases b <;> cases hbb : bruteForce (numVars φ) φ
    · rfl
    · exact absurd (hb.mpr (hbf.mp hbb)) (by decide)
    · exact absurd (hbf.mpr (hb.mp rfl)) (by simp [hbb])
    · rfl
  exact ⟨t, ht, this ▸ hr⟩

/-- Non-vacuity: the predicate `InP` used by the obligation is not satisfied
by every language (the shared diagonal language `Diag` is not in P), so
`PolySATDecider` is a genuine constraint on `SAT` rather than a tautology. -/
theorem polySATDecider_not_trivial : ¬ ∀ L : Language, InP L :=
  fun h => diag_not_inP (h Diag)

end Issue532.Idea01
