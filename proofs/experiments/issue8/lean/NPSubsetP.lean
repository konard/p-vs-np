import proofs.experiments.issue609.lean.PEqualsNPAttempt
import proofs.experiments.issue532.lean.Idea41

/-!
# Issue 8: the target `NP ⊆ P` and a verified DPLL search, over the shared model

Issue #8 asked to "try prove P = NP"; its corrected target is `NP ⊆ P`. This
file states that target over `Complexity`, proves how it relates to the class
equality and to SAT, and adds a concrete solver with a proved correctness and
cost statement. It does **not** prove `NP ⊆ P`.

The file proves:

* `NP ⊆ P` is the shared `Complexity.PEqualsNP`, and it is equivalent to the
  classes being equal because `P ⊆ NP` is proved (`pSubsetNP`);
* with the explicit premise `SATHard`, `NP ⊆ P` is equivalent to `SAT ∈ P` and
  to the existence of an issue #609 `Candidate`;
* PR #41's DPLL regression formula (issue #610) is satisfiable in the shared
  SAT semantics;
* `dpll`, a functional DPLL search with conflict detection, unit propagation
  and splitting, decides the shared `Issue532.Machines.SAT` language on every
  word (`dpllSAT_eq_SAT`). Each branch conditions its own copy of the formula,
  so there is no shared assignment trail to restore;
* its number of recursive calls, with the short-circuit of `||`, is less than
  `2^(|w|+1)` (`dpllSAT_calls_le`). That bound is not polynomial
  (`calls_bound_not_polynomial`). This is an upper bound on one algorithm; it
  is **not** a lower bound for SAT;
* the bridge: a `Complexity.Machine` that computes `dpllSAT` within a
  polynomial number of `Run` steps is a `Candidate`, so with `SATHard` it
  gives `NP ⊆ P`.

`dpll` is a Lean function, and its call count is not a count of `Run` steps.
Nothing here asserts an unproved theorem. `SATHard` stays an explicit premise.
-/

namespace Issue8.NPSubsetP

open Complexity Issue532.Machines Issue609.PEqualsNPAttempt

/-! ## The target: `NP ⊆ P` -/

/-- `NP ⊆ P`: every language in NP is in P. -/
def NPSubsetP : Prop := ∀ L : Language, InNP L → InP L

/-- The shared statement `PEqualsNP` is literally `NP ⊆ P`. -/
theorem npSubsetP_iff_pEqualsNP : NPSubsetP ↔ PEqualsNP := Iff.rfl

/-- Because `P ⊆ NP` is proved, `NP ⊆ P` says exactly that the classes are equal. -/
theorem npSubsetP_iff_classes_equal :
    NPSubsetP ↔ ∀ L : Language, InP L ↔ InNP L := by
  constructor
  · intro h L
    exact ⟨pSubsetNP L, h L⟩
  · intro h L hL
    exact (h L).2 hL

/-- With the named hardness premise, `NP ⊆ P` is the single statement `SAT ∈ P`.
The membership half uses the proved `SATVerifier.satInNP`. -/
theorem npSubsetP_iff_inP_sat (hard : SATHard) : NPSubsetP ↔ InP SAT :=
  (Issue532.SATVerifier.inP_sat_iff_of_hard hard).symm

/-- With the named hardness premise, `NP ⊆ P` is the existence of a polynomial-time
SAT machine (`Issue609.PEqualsNPAttempt.Candidate`). -/
theorem npSubsetP_iff_candidate (hard : SATHard) : NPSubsetP ↔ Nonempty Candidate :=
  (candidate_iff_pEqualsNP hard).symm

/-! ## The PR #41 DPLL regression in the shared SAT semantics

`(¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ (¬x1 ∨ ¬x3) ∧ (x1 ∨ ¬x2) ∧ (x1 ∨ x3)`, with `x1, x2, x3`
as variables `0, 1, 2`. PR #41's Python solver answered UNSAT (issue #610). -/

def issue610Formula : CNF :=
  [[⟨0, false⟩, ⟨1, true⟩], [⟨1, false⟩, ⟨2, true⟩], [⟨0, false⟩, ⟨2, false⟩],
   [⟨0, true⟩, ⟨1, false⟩], [⟨0, true⟩, ⟨2, true⟩]]

/-- `x1 = false, x2 = false, x3 = true` satisfies every clause. -/
theorem issue610_satisfiable : Satisfiable issue610Formula :=
  ⟨fun i => i == 2, by decide⟩

theorem issue610_sat : SAT (encodeCNF issue610Formula) = true :=
  (sat_encode _).2 issue610_satisfiable

/-! ## Conditioning a formula on one variable -/

/-- The assignment `a` with variable `v` set to `b`. -/
def upd (a : Assignment) (v : Nat) (b : Bool) : Assignment :=
  fun i => if i = v then b else a i

/-- `c` contains the literal `(v, b)`. -/
def hasLit (v : Nat) (b : Bool) : Clause → Bool
  | [] => false
  | l :: c => (l.var == v && l.pos == b) || hasLit v b c

/-- Delete the literals of variable `v`. -/
def dropVar (v : Nat) : Clause → Clause
  | [] => []
  | l :: c => if l.var = v then dropVar v c else l :: dropVar v c

/-- Condition on `x_v = b`: satisfied clauses go, false literals are deleted. -/
def assign (v : Nat) (b : Bool) : CNF → CNF
  | [] => []
  | c :: φ => if hasLit v b c then assign v b φ else dropVar v c :: assign v b φ

theorem evalClause_hasLit (a : Assignment) (v : Nat) (b : Bool) :
    ∀ c : Clause, hasLit v b c = true → evalClause (upd a v b) c = true
  | [], h => by simp [hasLit] at h
  | l :: c, h => by
    simp only [hasLit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    simp only [evalClause, Bool.or_eq_true]
    rcases h with ⟨hv, hb⟩ | h
    · left
      simp [evalLit, upd, hv, hb]
    · exact Or.inr (evalClause_hasLit a v b c h)

theorem evalClause_dropVar (a : Assignment) (v : Nat) (b : Bool) :
    ∀ c : Clause, hasLit v b c = false →
      evalClause (upd a v b) c = evalClause a (dropVar v c)
  | [], _ => rfl
  | l :: c, h => by
    simp only [hasLit, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq] at h
    obtain ⟨hl, hc⟩ := h
    have ih := evalClause_dropVar a v b c hc
    by_cases hv : l.var = v
    · have hp : l.pos ≠ b := by
        rcases hl with h | h
        · exact absurd hv h
        · exact h
      have hf : evalLit (upd a v b) l = false := by
        cases b <;> cases hq : l.pos <;> simp_all [evalLit, upd]
      simp only [evalClause, dropVar, hv, ↓reduceIte, hf, Bool.false_or]
      exact ih
    · have he : evalLit (upd a v b) l = evalLit a l := by
        simp [evalLit, upd, hv]
      simp only [evalClause, dropVar, hv, ↓reduceIte, he, ih]

/-- Conditioning is evaluation under the updated assignment. -/
theorem evalCNF_assign (a : Assignment) (v : Nat) (b : Bool) :
    ∀ φ : CNF, evalCNF a (assign v b φ) = evalCNF (upd a v b) φ
  | [] => rfl
  | c :: φ => by
    have ih := evalCNF_assign a v b φ
    cases hc : hasLit v b c
    · simp only [assign, hc, Bool.false_eq_true, ↓reduceIte, evalCNF,
        evalClause_dropVar a v b c hc, ih]
    · simp only [assign, hc, ↓reduceIte, evalCNF, evalClause_hasLit a v b c hc, ih,
        Bool.true_and]

theorem upd_self (a : Assignment) (v : Nat) : upd a v (a v) = a := by
  funext i
  by_cases h : i = v
  · subst h; simp [upd]
  · simp [upd, h]

theorem satisfiable_of_assign {v : Nat} {b : Bool} {φ : CNF}
    (h : Satisfiable (assign v b φ)) : Satisfiable φ := by
  obtain ⟨a, ha⟩ := h
  exact ⟨upd a v b, by rw [← evalCNF_assign]; exact ha⟩

theorem assign_satisfiable {a : Assignment} {v : Nat} {φ : CNF}
    (ha : evalCNF a φ = true) : Satisfiable (assign v (a v) φ) :=
  ⟨a, by rw [evalCNF_assign, upd_self]; exact ha⟩

/-- Splitting on `x_v`. -/
theorem satisfiable_split (v : Nat) (φ : CNF) :
    Satisfiable φ ↔ Satisfiable (assign v true φ) ∨ Satisfiable (assign v false φ) := by
  constructor
  · rintro ⟨a, ha⟩
    have h := assign_satisfiable (v := v) ha
    cases hv : a v
    · rw [hv] at h; exact Or.inr h
    · rw [hv] at h; exact Or.inl h
  · rintro (h | h)
    · exact satisfiable_of_assign h
    · exact satisfiable_of_assign h

theorem evalCNF_true_iff (a : Assignment) :
    ∀ φ : CNF, evalCNF a φ = true ↔ ∀ c ∈ φ, evalClause a c = true
  | [] => by simp [evalCNF]
  | c :: φ => by
    simp only [evalCNF, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp,
      evalCNF_true_iff a φ]

/-! ## Unit clauses and conflicts -/

/-- The literal of the first unit clause, if any. -/
def unitLit : CNF → Option Lit
  | [] => none
  | [l] :: _ => some l
  | _ :: φ => unitLit φ

/-- Some clause is empty. -/
def hasEmpty : CNF → Bool
  | [] => false
  | [] :: _ => true
  | _ :: φ => hasEmpty φ

theorem unitLit_mem : ∀ {φ : CNF} {l : Lit}, unitLit φ = some l → [l] ∈ φ
  | [], _, h => by simp [unitLit] at h
  | [] :: φ, l, h => List.mem_cons_of_mem _ (unitLit_mem (φ := φ) h)
  | [l'] :: φ, l, h => by
    simp only [unitLit, Option.some.injEq] at h
    subst h; exact List.mem_cons_self ..
  | (l₁ :: l₂ :: c) :: φ, l, h => List.mem_cons_of_mem _ (unitLit_mem (φ := φ) h)

theorem hasEmpty_mem : ∀ {φ : CNF}, hasEmpty φ = true → [] ∈ φ
  | [], h => by simp [hasEmpty] at h
  | [] :: _, _ => List.mem_cons_self ..
  | (_ :: _) :: φ, h => List.mem_cons_of_mem _ (hasEmpty_mem (φ := φ) h)

theorem not_satisfiable_of_empty {φ : CNF} (h : [] ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  have := (evalCNF_true_iff a φ).1 ha [] h
  simp [evalClause] at this

/-- A unit clause `[l]` forces its literal. -/
theorem satisfiable_unit {φ : CNF} {l : Lit} (h : [l] ∈ φ) :
    Satisfiable φ ↔ Satisfiable (assign l.var l.pos φ) := by
  constructor
  · rintro ⟨a, ha⟩
    have hl := (evalCNF_true_iff a φ).1 ha [l] h
    have hv : a l.var = l.pos := by
      simpa [evalClause, evalLit] using hl
    have := assign_satisfiable (v := l.var) ha
    rwa [hv] at this
  · exact satisfiable_of_assign

/-! ## The DPLL search

`k` is fuel: every call conditions on one variable, and `k` bounds the number
of distinct variables left. -/

def dpll : Nat → CNF → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | k + 1, c :: φ =>
    if hasEmpty (c :: φ) then false else
    match unitLit (c :: φ) with
    | some l => dpll k (assign l.var l.pos (c :: φ))
    | none =>
      match c with
      | [] => false
      | l :: _ => dpll k (assign l.var true (c :: φ)) || dpll k (assign l.var false (c :: φ))

/-- Every variable of `φ` is listed in `S`. -/
def VarsIn (S : List Nat) (φ : CNF) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var ∈ S

theorem mem_dropVar {v : Nat} {l : Lit} :
    ∀ {c : Clause}, l ∈ dropVar v c → l ∈ c ∧ l.var ≠ v
  | [], h => by simp [dropVar] at h
  | l' :: c, h => by
    by_cases hv : l'.var = v
    · simp only [dropVar, hv, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := mem_dropVar h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · simp only [dropVar, hv, ↓reduceIte, List.mem_cons] at h
      rcases h with h | h
      · subst h; exact ⟨List.mem_cons_self .., hv⟩
      · obtain ⟨h1, h2⟩ := mem_dropVar h
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem mem_assign {v : Nat} {b : Bool} {c' : Clause} :
    ∀ {φ : CNF}, c' ∈ assign v b φ → ∃ c ∈ φ, c' = dropVar v c
  | [], h => by simp [assign] at h
  | c :: φ, h => by
    cases hc : hasLit v b c
    · simp only [assign, hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨c, List.mem_cons_self .., h⟩
      · obtain ⟨d, hd, e⟩ := mem_assign h
        exact ⟨d, List.mem_cons_of_mem _ hd, e⟩
    · simp only [assign, hc, ↓reduceIte] at h
      obtain ⟨d, hd, e⟩ := mem_assign h
      exact ⟨d, List.mem_cons_of_mem _ hd, e⟩

/-- Conditioning on a listed variable removes it from the list. -/
theorem varsIn_assign {S : List Nat} {φ : CNF} (h : VarsIn S φ) (v : Nat) (b : Bool) :
    VarsIn (S.erase v) (assign v b φ) := by
  intro c' hc' l hl
  obtain ⟨c, hc, rfl⟩ := mem_assign hc'
  obtain ⟨hlc, hlv⟩ := mem_dropVar hl
  exact (List.mem_erase_of_ne hlv).2 (h c hc l hlc)

theorem length_erase_le {S : List Nat} {v k : Nat} (hv : v ∈ S) (hk : S.length ≤ k + 1) :
    (S.erase v).length ≤ k := by
  rw [List.length_erase_of_mem hv]
  omega

/-- `dpll` is correct whenever the fuel bounds the variables. -/
theorem dpll_correct : ∀ (k : Nat) (φ : CNF) (S : List Nat),
    VarsIn S φ → S.length ≤ k → (dpll k φ = true ↔ Satisfiable φ)
  | _, [], _, _, _ => by
    simp only [dpll, true_iff]
    exact ⟨fun _ => false, rfl⟩
  | 0, c :: φ, S, hS, hk => by
    have hS0 : S = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hS0
    have hc : c = [] := by
      cases c with
      | nil => rfl
      | cons l c => exact absurd (hS (l :: c) (List.mem_cons_self ..) l
          (List.mem_cons_self ..)) (List.not_mem_nil)
    subst hc
    simp only [dpll, Bool.false_eq_true, false_iff]
    exact not_satisfiable_of_empty (List.mem_cons_self ..)
  | k + 1, c :: φ, S, hS, hk => by
    by_cases he : hasEmpty (c :: φ) = true
    · simp only [dpll, he, ↓reduceIte, Bool.false_eq_true, false_iff]
      exact not_satisfiable_of_empty (hasEmpty_mem he)
    · simp only [Bool.not_eq_true] at he
      cases hu : unitLit (c :: φ) with
      | some l =>
        simp only [dpll, he, hu, Bool.false_eq_true, ↓reduceIte]
        have hmem := unitLit_mem hu
        have hv : l.var ∈ S := hS [l] hmem l (List.mem_singleton_self l)
        rw [satisfiable_unit hmem]
        exact dpll_correct k _ _ (varsIn_assign hS _ _) (length_erase_le hv hk)
      | none =>
        cases c with
        | nil => simp [hasEmpty] at he
        | cons l c =>
          simp only [dpll, he, hu, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
          have hv : l.var ∈ S := hS (l :: c) (List.mem_cons_self ..) l (List.mem_cons_self ..)
          rw [satisfiable_split l.var,
            dpll_correct k _ _ (varsIn_assign hS _ _) (length_erase_le hv hk),
            dpll_correct k _ _ (varsIn_assign hS _ _) (length_erase_le hv hk)]

/-! ## `dpll` decides the shared SAT language -/

/-- Run `dpll` on the decoded formula with the input length as fuel. -/
def dpllSAT : Language := fun w => dpll w.length (decode w)

theorem varsIn_range {n : Nat} {φ : CNF} (h : VarsBelow n φ) : VarsIn (List.range n) φ :=
  fun c hc l hl => List.mem_range.2 (h c hc l hl)

theorem dpllSAT_iff (w : Word) : dpllSAT w = true ↔ Satisfiable (decode w) :=
  dpll_correct w.length (decode w) (List.range w.length)
    (varsIn_range (Issue532.SATVerifier.varsBelow_decode w)) (by simp)

/-- The concrete solver agrees with `Issue532.Machines.SAT` on every word,
including words that are not encodings. -/
theorem dpllSAT_eq_SAT (w : Word) : dpllSAT w = SAT w := by
  apply Bool.eq_iff_iff.2
  rw [dpllSAT_iff, sat_iff]

/-- On encodings the answer is satisfiability of the formula. -/
theorem dpllSAT_encode (φ : CNF) : dpllSAT (encodeCNF φ) = true ↔ Satisfiable φ := by
  rw [dpllSAT_eq_SAT]
  exact sat_encode φ

/-- Regression tests: the issue #610 formula is accepted, and the formula with
one empty clause is rejected. -/
theorem dpllSAT_issue610 : dpllSAT (encodeCNF issue610Formula) = true := by decide
theorem dpllSAT_empty_clause : dpllSAT (encodeCNF [[]]) = false := by decide

/-! ## The call count

`dpllCalls` counts the calls `dpll` makes, including the short-circuit of `||`:
the `false` branch is searched only after the `true` branch fails. -/

def dpllCalls : Nat → CNF → Nat
  | _, [] => 1
  | 0, _ :: _ => 1
  | k + 1, c :: φ =>
    if hasEmpty (c :: φ) then 1 else
    match unitLit (c :: φ) with
    | some l => 1 + dpllCalls k (assign l.var l.pos (c :: φ))
    | none =>
      match c with
      | [] => 1
      | l :: _ =>
        if dpll k (assign l.var true (c :: φ)) then
          1 + dpllCalls k (assign l.var true (c :: φ))
        else
          1 + dpllCalls k (assign l.var true (c :: φ)) +
            dpllCalls k (assign l.var false (c :: φ))

/-- The search tree has fewer than `2^(k+1)` nodes. -/
theorem dpllCalls_lt : ∀ (k : Nat) (φ : CNF), dpllCalls k φ < 2 ^ (k + 1)
  | _, [] => by simp only [dpllCalls]; exact Nat.one_lt_two_pow (by omega)
  | 0, _ :: _ => by simp [dpllCalls]
  | k + 1, c :: φ => by
    have hp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have h1 : 1 < 2 ^ (k + 1 + 1) := Nat.one_lt_two_pow (by omega)
    by_cases he : hasEmpty (c :: φ) = true
    · simp only [dpllCalls, he, ↓reduceIte]
      exact h1
    · simp only [Bool.not_eq_true] at he
      cases hu : unitLit (c :: φ) with
      | some l =>
        have h2 := dpllCalls_lt k (assign l.var l.pos (c :: φ))
        simp only [dpllCalls, he, hu, Bool.false_eq_true, ↓reduceIte]
        omega
      | none =>
        cases c with
        | nil => simp [hasEmpty] at he
        | cons l c =>
          have h2 := dpllCalls_lt k (assign l.var true ((l :: c) :: φ))
          have h3 := dpllCalls_lt k (assign l.var false ((l :: c) :: φ))
          simp only [dpllCalls, he, hu, Bool.false_eq_true, ↓reduceIte]
          split <;> omega

/-- On input `w`, the solver makes fewer than `2^(|w|+1)` calls. -/
theorem dpllSAT_calls_le (w : Word) : dpllCalls w.length (decode w) < 2 ^ (w.length + 1) :=
  dpllCalls_lt w.length (decode w)

/-- The proved bound is not polynomial. This only says that the bound above does
not give a polynomial-time algorithm; it is not a lower bound for SAT. -/
theorem calls_bound_not_polynomial : ¬ PolynomiallyBounded (fun n => 2 ^ (n + 1)) := by
  rintro ⟨a, k, h⟩
  obtain ⟨N, hN⟩ := Issue532.Idea41.poly_le_two_pow (a + 1) k
  have h1 : 2 ^ (N + 1) ≤ a * (N + 1) ^ k := h N
  have h2 := hN N (Nat.le_refl N)
  have h3 : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [Nat.pow_succ]; omega
  have h4 : 0 < (N + 1) ^ k := Nat.pow_pos (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-! ## The bridge to `NP ⊆ P`

The remaining obligations are named: a machine computing `dpllSAT` within a
polynomial number of `Run` steps, and `SATHard`. -/

/-- A polynomial-time machine for `dpllSAT` is a `Candidate`. -/
theorem candidate_of_dpll_machine {m : Machine} {p : Polynomial}
    (h : DecidesWithin m p dpllSAT) : Nonempty Candidate := by
  refine ⟨⟨m, p, fun x => ?_, fun x t b hr => ?_⟩⟩
  · obtain ⟨t, b, ht, hr, _⟩ := h x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t', b', _, hr', hb'⟩ := h x
    rw [(run_deterministic hr hr').2, hb', dpllSAT_eq_SAT]

/-- With `SATHard`, such a machine proves `NP ⊆ P`. -/
theorem npSubsetP_of_dpll_machine (hard : SATHard) {m : Machine} {p : Polynomial}
    (h : DecidesWithin m p dpllSAT) : NPSubsetP := by
  obtain ⟨c⟩ := candidate_of_dpll_machine h
  exact pEqualsNP_of_candidate hard c

/-- Conversely, `NP ⊆ P` yields such a machine; no `SATHard` is needed here. -/
theorem dpll_machine_of_npSubsetP (h : NPSubsetP) :
    ∃ (m : Machine) (p : Polynomial), DecidesWithin m p dpllSAT := by
  obtain ⟨m, p, hm⟩ :=
    (polyDec_iff_inP SAT).2 (inP_sat_of_pEqualsNP Issue532.SATVerifier.satInNP h)
  refine ⟨m, p, fun x => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm x
  exact ⟨t, b, ht, hr, hb.trans (dpllSAT_eq_SAT x).symm⟩

end Issue8.NPSubsetP
