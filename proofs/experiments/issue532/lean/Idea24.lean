/-!
# Issue #532, Idea 24: unit propagation

Proved here, for every CNF:

* `unit_forces`: a unit clause `[l]` of `φ` is true under every assignment
  satisfying `φ`;
* `propagate_preserves`: if `l` is true under `a`, propagating `l`
  (restricting its variable to its sign) does not change the value of `φ`
  under `a`; `unit_step_equisat`: propagating a unit clause preserves
  satisfiability;
* `up_equisat`, `up_conflict_unsat`: fuel-bounded unit propagation `up`
  preserves satisfiability, so a derived empty clause certifies UNSAT;
* `up_noop`, `sq_unsat`, `up_incomplete_family`: incompleteness.  For every
  CNF `ψ` with all clauses of length at least 2 and every pair of
  variables `x, y`, the formula `sq x y ++ ψ` (with
  `sq x y = {x∨y, x∨¬y, ¬x∨y, ¬x∨¬y}`) is unsatisfiable, contains no empty
  clause, and is left unchanged by propagation with any fuel;
* `hornSolve_correct`: on Horn formulas (at most one positive literal per
  clause), propagating positive unit clauses and then answering with the
  all-false assignment decides satisfiability (Dowling–Gallier style).

**Verdict.** Correct tool, insufficient alone: unit propagation is sound,
complete on Horn formulas, and refuted as a general decision procedure by
a general parametric family.  Core Lean only.
-/

namespace Issue532.Idea24

/-! ## SAT core -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: C => evalLit a l || evalClause a C

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | C :: φ => evalClause a C && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a, evalCNF a φ = true

theorem evalClause_true_iff (a : Assignment) (C : Clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLit a l = true := by
  induction C with
  | nil => simp [evalClause]
  | cons l C ih => simp [evalClause, ih]

theorem evalCNF_true_iff (a : Assignment) (φ : CNF) :
    evalCNF a φ = true ↔ ∀ C ∈ φ, evalClause a C = true := by
  induction φ with
  | nil => simp [evalCNF]
  | cons C φ ih => simp [evalCNF, ih]

/-! ## Restriction -/

/-- `clauseHas v b C`: `C` contains the literal "`v` has value `b`". -/
def clauseHas (v : Nat) (b : Bool) : Clause → Bool
  | [] => false
  | l :: C => (l.var == v && l.pos == b) || clauseHas v b C

/-- Delete every literal on variable `v`. -/
def removeVar (v : Nat) : Clause → Clause
  | [] => []
  | l :: C => if l.var = v then removeVar v C else l :: removeVar v C

/-- Set `v := b`: drop satisfied clauses, shorten the others. -/
def restrict (v : Nat) (b : Bool) : CNF → CNF
  | [] => []
  | C :: φ => if clauseHas v b C then restrict v b φ else removeVar v C :: restrict v b φ

/-- Update an assignment at one variable. -/
def setVar (a : Assignment) (v : Nat) (b : Bool) : Assignment :=
  fun x => if x = v then b else a x

theorem evalClause_setVar (a : Assignment) (v : Nat) (b : Bool) (C : Clause) :
    evalClause (setVar a v b) C = (clauseHas v b C || evalClause a (removeVar v C)) := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    by_cases h : l.var = v
    · have e : evalLit (setVar a v b) l = (l.pos == b) := by
        cases hp : l.pos <;> cases b <;> simp [evalLit, setVar, h, hp]
      simp only [evalClause, clauseHas, removeVar, h, ↓reduceIte, e, ih]
      cases (l.pos == b) <;> cases clauseHas v b C <;> simp
    · have e : evalLit (setVar a v b) l = evalLit a l := by
        simp [evalLit, setVar, h]
      simp only [evalClause, clauseHas, removeVar, h, ↓reduceIte, e, ih]
      have hv : (l.var == v) = false := by simp [h]
      rw [hv, Bool.false_and, Bool.false_or]
      cases evalLit a l <;> cases clauseHas v b C <;> simp

/-- **Restriction lemma.** -/
theorem eval_restrict (a : Assignment) (v : Nat) (b : Bool) (φ : CNF) :
    evalCNF a (restrict v b φ) = evalCNF (setVar a v b) φ := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    rw [evalCNF, evalClause_setVar]
    cases h : clauseHas v b C
    · simp [restrict, h, evalCNF, ih]
    · simp [restrict, h, ih]

theorem setVar_self (a : Assignment) (v : Nat) : setVar a v (a v) = a := by
  funext x
  by_cases h : x = v
  · subst h; simp [setVar]
  · simp [setVar, h]

/-- **Splitting rule.** -/
theorem sat_split (φ : CNF) (v : Nat) :
    Satisfiable φ ↔ Satisfiable (restrict v true φ) ∨ Satisfiable (restrict v false φ) := by
  constructor
  · rintro ⟨a, ha⟩
    have hr : evalCNF a (restrict v (a v) φ) = true := by
      rw [eval_restrict, setVar_self]; exact ha
    cases hv : a v
    · rw [hv] at hr; exact Or.inr ⟨a, hr⟩
    · rw [hv] at hr; exact Or.inl ⟨a, hr⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨setVar a v true, by rw [← eval_restrict]; exact ha⟩
    · exact ⟨setVar a v false, by rw [← eval_restrict]; exact ha⟩

/-! ## Variables -/

/-- All variables of `φ` occur in `vs`. -/
def VarsIn (φ : CNF) (vs : List Nat) : Prop := ∀ C ∈ φ, ∀ l ∈ C, l.var ∈ vs

theorem mem_removeVar (v : Nat) (C : Clause) (l : Lit) :
    l ∈ removeVar v C → l ∈ C ∧ l.var ≠ v := by
  induction C with
  | nil => simp [removeVar]
  | cons l' C ih =>
    by_cases h : l'.var = v
    · simp only [removeVar, h, ↓reduceIte]
      intro hl
      have := ih hl
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · simp only [removeVar, h, ↓reduceIte, List.mem_cons]
      rintro (rfl | hl)
      · exact ⟨Or.inl rfl, h⟩
      · have := ih hl
        exact ⟨Or.inr this.1, this.2⟩

theorem mem_restrict (v : Nat) (b : Bool) (φ : CNF) (C' : Clause) :
    C' ∈ restrict v b φ → ∃ C ∈ φ, C' = removeVar v C := by
  induction φ with
  | nil => simp [restrict]
  | cons C φ ih =>
    cases h : clauseHas v b C
    · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rintro (e | hm)
      · exact ⟨C, Or.inl rfl, e⟩
      · obtain ⟨D, hD, e⟩ := ih hm
        exact ⟨D, Or.inr hD, e⟩
    · simp only [restrict, h, ↓reduceIte]
      intro hm
      obtain ⟨D, hD, e⟩ := ih hm
      exact ⟨D, List.mem_cons_of_mem _ hD, e⟩

theorem restrict_vars (φ : CNF) (v : Nat) (vs : List Nat) (b : Bool)
    (h : VarsIn φ (v :: vs)) : VarsIn (restrict v b φ) vs := by
  intro C' hC' l hl
  obtain ⟨C, hC, e⟩ := mem_restrict v b φ C' hC'
  rw [e] at hl
  obtain ⟨hlC, hne⟩ := mem_removeVar v C l hl
  have := h C hC l hlC
  rcases List.mem_cons.mp this with e | e
  · exact absurd e hne
  · exact e

theorem eval_congr (a a' : Assignment) (φ : CNF)
    (h : ∀ C ∈ φ, ∀ l ∈ C, a l.var = a' l.var) : evalCNF a φ = evalCNF a' φ := by
  have hc : ∀ C ∈ φ, evalClause a C = evalClause a' C := by
    intro C hC
    have hC' := h C hC
    clear hC
    induction C with
    | nil => rfl
    | cons l C ih =>
      have hl : evalLit a l = evalLit a' l := by
        simp [evalLit, hC' l (List.mem_cons_self ..)]
      simp only [evalClause, hl, ih (fun l' hl' => hC' l' (List.mem_cons_of_mem _ hl'))]
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    simp only [evalCNF, hc C (List.mem_cons_self ..),
      ih (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))
        (fun C' hC' => hc C' (List.mem_cons_of_mem _ hC'))]

theorem sat_no_vars (φ : CNF) (h : VarsIn φ []) :
    Satisfiable φ ↔ evalCNF (fun _ => false) φ = true := by
  constructor
  · rintro ⟨a, ha⟩
    rw [eval_congr (fun _ => false) a φ (fun C hC l hl => absurd (h C hC l hl) (by simp))]
    exact ha
  · intro h'; exact ⟨_, h'⟩


/-! ## Size and the variables of a formula -/

/-- Input size: number of literal occurrences plus number of clauses. -/
def size : CNF → Nat
  | [] => 0
  | C :: φ => C.length + 1 + size φ

theorem length_removeVar_le (v : Nat) (C : Clause) : (removeVar v C).length ≤ C.length := by
  induction C with
  | nil => simp [removeVar]
  | cons l C ih =>
    by_cases h : l.var = v
    · simp only [removeVar, h, ↓reduceIte, List.length_cons]; omega
    · simp only [removeVar, h, ↓reduceIte, List.length_cons]; omega

/-- Restriction never increases the size. -/
theorem size_restrict_le (v : Nat) (b : Bool) (φ : CNF) : size (restrict v b φ) ≤ size φ := by
  induction φ with
  | nil => simp [restrict, size]
  | cons C φ ih =>
    have := length_removeVar_le v C
    cases h : clauseHas v b C
    · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, size]; omega
    · simp only [restrict, h, ↓reduceIte, size]; omega
/-! ## Unit propagation: soundness -/

theorem evalLit_true_iff (a : Assignment) (l : Lit) : evalLit a l = true ↔ a l.var = l.pos := by
  cases hp : l.pos <;> cases ha : a l.var <;> simp [evalLit, hp, ha]

/-- **A unit clause forces its literal.** -/
theorem unit_forces (a : Assignment) (φ : CNF) (l : Lit) (h : [l] ∈ φ)
    (ha : evalCNF a φ = true) : evalLit a l = true := by
  have hc := (evalCNF_true_iff a φ).mp ha [l] h
  simpa [evalClause] using hc

/-- **Propagation preserves satisfying assignments.**  If `l` is true under
`a`, then `φ` and its propagation by `l` have the same value under `a`. -/
theorem propagate_preserves (a : Assignment) (φ : CNF) (l : Lit) (h : evalLit a l = true) :
    evalCNF a (restrict l.var l.pos φ) = evalCNF a φ := by
  rw [eval_restrict, ← (evalLit_true_iff a l).mp h, setVar_self]

/-- **One propagation step preserves satisfiability.** -/
theorem unit_step_equisat (l : Lit) (φ : CNF) (h : [l] ∈ φ) :
    Satisfiable (restrict l.var l.pos φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨setVar a l.var l.pos, by rw [← eval_restrict]; exact ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [propagate_preserves a φ l (unit_forces a φ l h ha)]; exact ha⟩

/-- The literal of a unit clause. -/
def unitOf : Clause → Option Lit
  | [l] => some l
  | _ => none

/-- The first unit clause of a CNF. -/
def findUnit : CNF → Option Lit
  | [] => none
  | C :: φ => match unitOf C with
    | some l => some l
    | none => findUnit φ

theorem unitOf_some (C : Clause) (l : Lit) (h : unitOf C = some l) : C = [l] := by
  match C, h with
  | [l'], h => simp [unitOf] at h; rw [h]

theorem findUnit_some (φ : CNF) (l : Lit) (h : findUnit φ = some l) : [l] ∈ φ := by
  induction φ with
  | nil => simp [findUnit] at h
  | cons C φ ih =>
    cases hu : unitOf C with
    | some l' =>
      simp [findUnit, hu] at h
      rw [unitOf_some C l' hu, h]
      exact List.mem_cons_self ..
    | none =>
      simp [findUnit, hu] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem unitOf_long (C : Clause) (h : 2 ≤ C.length) : unitOf C = none := by
  match C, h with
  | _ :: _ :: _, _ => rfl

theorem findUnit_none_of_long (φ : CNF) (h : ∀ C ∈ φ, 2 ≤ C.length) : findUnit φ = none := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    have hC := unitOf_long C (h C (List.mem_cons_self ..))
    simp only [findUnit, hC]
    exact ih (fun C' hC' => h C' (List.mem_cons_of_mem _ hC'))

/-- Unit propagation with fuel: repeatedly propagate the first unit clause. -/
def up : Nat → CNF → CNF
  | 0, φ => φ
  | n + 1, φ => match findUnit φ with
    | none => φ
    | some l => up n (restrict l.var l.pos φ)

/-- **Soundness of unit propagation.** -/
theorem up_equisat (n : Nat) (φ : CNF) : Satisfiable (up n φ) ↔ Satisfiable φ := by
  induction n generalizing φ with
  | zero => exact Iff.rfl
  | succ n ih =>
    cases h : findUnit φ with
    | none => simp only [up, h]
    | some l =>
      simp only [up, h]
      rw [ih]
      exact unit_step_equisat l φ (findUnit_some φ l h)

theorem empty_clause_unsat (φ : CNF) (h : ([] : Clause) ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  have := (evalCNF_true_iff a φ).mp ha [] h
  simp [evalClause] at this

/-- A conflict found by propagation certifies unsatisfiability. -/
theorem up_conflict_unsat (n : Nat) (φ : CNF) (h : ([] : Clause) ∈ up n φ) : ¬ Satisfiable φ :=
  fun hs => empty_clause_unsat _ h ((up_equisat n φ).mpr hs)

/-! ## Incompleteness -/

/-- Propagation does nothing on formulas without short clauses. -/
theorem up_noop (n : Nat) (φ : CNF) (h : ∀ C ∈ φ, 2 ≤ C.length) : up n φ = φ := by
  cases n with
  | zero => rfl
  | succ n => simp only [up, findUnit_none_of_long φ h]

/-- The four clauses on two variables. -/
def sq (x y : Nat) : CNF :=
  [[⟨x, true⟩, ⟨y, true⟩], [⟨x, true⟩, ⟨y, false⟩],
   [⟨x, false⟩, ⟨y, true⟩], [⟨x, false⟩, ⟨y, false⟩]]

/-- `sq x y` is unsatisfiable for all `x, y` (also for `x = y`). -/
theorem sq_unsat (x y : Nat) : ¬ Satisfiable (sq x y) := by
  rintro ⟨a, ha⟩
  simp only [sq, evalCNF, evalClause, evalLit, ↓reduceIte, Bool.false_eq_true] at ha
  cases hx : a x <;> cases hy : a y <;> simp [hx, hy] at ha

theorem sq_long (x y : Nat) : ∀ C ∈ sq x y, 2 ≤ C.length := by
  intro C hC
  simp only [sq, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with e | e | e | e <;> rw [e] <;> simp

/-- **Incompleteness of unit propagation (general family).**  For every
`ψ` whose clauses all have length at least 2, every `x, y` and every fuel
`n`: propagation leaves `sq x y ++ ψ` unchanged and finds no empty clause,
yet the formula is unsatisfiable. -/
theorem up_incomplete_family (ψ : CNF) (hψ : ∀ C ∈ ψ, 2 ≤ C.length) (x y n : Nat) :
    up n (sq x y ++ ψ) = sq x y ++ ψ ∧ ([] : Clause) ∉ up n (sq x y ++ ψ) ∧
      ¬ Satisfiable (sq x y ++ ψ) := by
  have hl : ∀ C ∈ sq x y ++ ψ, 2 ≤ C.length := by
    intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact sq_long x y C h
    · exact hψ C h
  refine ⟨up_noop n _ hl, ?_, ?_⟩
  · rw [up_noop n _ hl]
    intro h
    have := hl [] h
    simp at this
  · rintro ⟨a, ha⟩
    apply sq_unsat x y
    refine ⟨a, (evalCNF_true_iff a _).mpr ?_⟩
    intro C hC
    exact (evalCNF_true_iff a _).mp ha C (List.mem_append_left _ hC)

/-! ## Horn formulas -/

/-- Number of positive literals of a clause. -/
def posCount : Clause → Nat
  | [] => 0
  | l :: C => (if l.pos then 1 else 0) + posCount C

/-- Horn: every clause has at most one positive literal. -/
def IsHorn (φ : CNF) : Prop := ∀ C ∈ φ, posCount C ≤ 1

theorem posCount_removeVar_le (v : Nat) (C : Clause) : posCount (removeVar v C) ≤ posCount C := by
  induction C with
  | nil => simp [removeVar, posCount]
  | cons l C ih =>
    by_cases h : l.var = v
    · simp only [removeVar, h, ↓reduceIte, posCount]; omega
    · simp only [removeVar, h, ↓reduceIte, posCount]; omega

/-- Restriction preserves the Horn property. -/
theorem restrict_horn (v : Nat) (b : Bool) (φ : CNF) (h : IsHorn φ) : IsHorn (restrict v b φ) := by
  intro C' hC'
  obtain ⟨C, hC, e⟩ := mem_restrict v b φ C' hC'
  rw [e]
  exact Nat.le_trans (posCount_removeVar_le v C) (h C hC)

def hasEmpty : CNF → Bool
  | [] => false
  | [] :: _ => true
  | (_ :: _) :: φ => hasEmpty φ

theorem hasEmpty_iff (φ : CNF) : hasEmpty φ = true ↔ ([] : Clause) ∈ φ := by
  induction φ with
  | nil => simp [hasEmpty]
  | cons C φ ih =>
    cases C with
    | nil => simp [hasEmpty]
    | cons l C => simp [hasEmpty, ih]

/-- The variable of a positive unit clause. -/
def posUnitOf : Clause → Option Nat
  | [l] => if l.pos then some l.var else none
  | _ => none

def findPosUnit : CNF → Option Nat
  | [] => none
  | C :: φ => match posUnitOf C with
    | some v => some v
    | none => findPosUnit φ

theorem posUnitOf_some (C : Clause) (v : Nat) (h : posUnitOf C = some v) : C = [⟨v, true⟩] := by
  match C, h with
  | [⟨lv, lp⟩], h => cases lp <;> simp [posUnitOf] at h ⊢; exact h

theorem findPosUnit_some (φ : CNF) (v : Nat) (h : findPosUnit φ = some v) : [⟨v, true⟩] ∈ φ := by
  induction φ with
  | nil => simp [findPosUnit] at h
  | cons C φ ih =>
    cases hu : posUnitOf C with
    | some w =>
      simp [findPosUnit, hu] at h
      rw [posUnitOf_some C w hu, h]
      exact List.mem_cons_self ..
    | none =>
      simp [findPosUnit, hu] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem findPosUnit_none (φ : CNF) (h : findPosUnit φ = none) : ∀ C ∈ φ, posUnitOf C = none := by
  induction φ with
  | nil => intro C hC; simp at hC
  | cons D φ ih =>
    cases hu : posUnitOf D with
    | some w => simp [findPosUnit, hu] at h
    | none =>
      simp [findPosUnit, hu] at h
      intro C hC
      rcases List.mem_cons.mp hC with e | e
      · rw [e]; exact hu
      · exact ih h C e

theorem neg_or_allpos (C : Clause) : (∃ l ∈ C, l.pos = false) ∨ posCount C = C.length := by
  induction C with
  | nil => exact Or.inr rfl
  | cons l C ih =>
    cases hp : l.pos
    · exact Or.inl ⟨l, List.mem_cons_self .., hp⟩
    · rcases ih with ⟨l', hl', e⟩ | e
      · exact Or.inl ⟨l', List.mem_cons_of_mem _ hl', e⟩
      · right; simp [posCount, hp, e]; omega

/-- A nonempty Horn clause that is not a positive unit is satisfied by the
all-false assignment. -/
theorem horn_clause_sat (C : Clause) (hh : posCount C ≤ 1) (hne : C ≠ [])
    (hu : posUnitOf C = none) : evalClause (fun _ => false) C = true := by
  rcases neg_or_allpos C with ⟨l, hl, hp⟩ | e
  · exact (evalClause_true_iff _ C).mpr ⟨l, hl, by simp [evalLit, hp]⟩
  · match C, hh, hne, hu, e with
    | [l], _, _, hu, e =>
      cases hp : l.pos
      · simp [posCount, hp] at e
      · simp [posUnitOf, hp] at hu
    | _ :: _ :: _, hh, _, _, e =>
      simp only [List.length_cons] at e
      omega

/-- **Horn fixpoint lemma.**  A Horn CNF without empty clauses and without
positive unit clauses is satisfied by the all-false assignment. -/
theorem horn_fixpoint_sat (φ : CNF) (hh : IsHorn φ) (he : hasEmpty φ = false)
    (hu : findPosUnit φ = none) : evalCNF (fun _ => false) φ = true := by
  apply (evalCNF_true_iff _ φ).mpr
  intro C hC
  apply horn_clause_sat C (hh C hC) _ (findPosUnit_none φ hu C hC)
  intro e
  rw [e] at hC
  have := (hasEmpty_iff φ).mpr hC
  rw [he] at this
  exact Bool.false_ne_true this

/-- Propagating a unit clause strictly decreases the size. -/
theorem size_restrict_lt (φ : CNF) (l : Lit) (h : [l] ∈ φ) :
    size (restrict l.var l.pos φ) < size φ := by
  have hself : clauseHas l.var l.pos [l] = true := by simp [clauseHas]
  induction φ with
  | nil => simp at h
  | cons C φ ih =>
    rcases List.mem_cons.mp h with e | e
    · rw [← e]
      simp only [restrict, hself, ↓reduceIte, size]
      have := size_restrict_le l.var l.pos φ
      omega
    · have h1 := ih e
      have h2 := length_removeVar_le l.var C
      cases hc : clauseHas l.var l.pos C
      · simp only [restrict, hc, Bool.false_eq_true, ↓reduceIte, size]; omega
      · simp only [restrict, hc, ↓reduceIte, size]; omega

/-- Horn-SAT by positive unit propagation with fuel. -/
def hornUP : Nat → CNF → Bool
  | 0, φ => evalCNF (fun _ => false) φ
  | n + 1, φ => if hasEmpty φ then false else
      match findPosUnit φ with
      | none => true
      | some v => hornUP n (restrict v true φ)

theorem hornUP_correct (n : Nat) (φ : CNF) (hh : IsHorn φ) (hs : size φ ≤ n) :
    hornUP n φ = true ↔ Satisfiable φ := by
  induction n generalizing φ with
  | zero =>
    cases φ with
    | nil => exact ⟨fun _ => ⟨fun _ => false, rfl⟩, fun _ => rfl⟩
    | cons C φ => simp [size] at hs
  | succ n ih =>
    cases he : hasEmpty φ with
    | true =>
      simp only [hornUP, he, ↓reduceIte]
      exact ⟨fun h => absurd h Bool.false_ne_true,
        fun hsat => absurd hsat (empty_clause_unsat φ ((hasEmpty_iff φ).mp he))⟩
    | false =>
      cases hu : findPosUnit φ with
      | none =>
        simp only [hornUP, he, hu, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun _ => ⟨_, horn_fixpoint_sat φ hh he hu⟩, fun _ => trivial⟩
      | some v =>
        simp only [hornUP, he, hu, Bool.false_eq_true, ↓reduceIte]
        have hmem := findPosUnit_some φ v hu
        have hlt := size_restrict_lt φ ⟨v, true⟩ hmem
        rw [ih _ (restrict_horn v true φ hh) (by simp only at hlt; omega)]
        exact unit_step_equisat ⟨v, true⟩ φ hmem

/-- Horn-SAT solver: positive unit propagation, then the all-false assignment. -/
def hornSolve (φ : CNF) : Bool := hornUP (size φ) φ

/-- **Horn-SAT is decided by unit propagation.** -/
theorem hornSolve_correct (φ : CNF) (hh : IsHorn φ) : hornSolve φ = true ↔ Satisfiable φ :=
  hornUP_correct (size φ) φ hh (Nat.le_refl _)

end Issue532.Idea24
