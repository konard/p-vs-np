/-!
# Issue #532, Idea 21: exact SAT by branching (DPLL splitting)

Proved here for every CNF:

* `eval_restrict`: restricting variable `v` to `b` (drop satisfied clauses,
  delete the other literals on `v`) is evaluated exactly as the original
  formula under the updated assignment `setVar a v b`;
* `sat_split`: `φ` is satisfiable iff one of its two restrictions on `v` is;
* `solve_correct`: the pure splitting procedure over a variable list `vs`
  decides satisfiability for every CNF whose variables lie in `vs`;
* `dpll_correct`: the same with DPLL pruning (stop on the empty formula or
  on an empty clause);
* `leaves_eq`, `dpllLeaves_le`: the unpruned split tree has exactly
  `2 ^ vs.length` leaves, and the pruned tree has at most that many.

**Verdict.** Splitting is a correct, complete exact algorithm with an
exponential worst-case bound.  That DPLL and CDCL need exponential time on
some families, whatever the heuristics, is a published theorem: their
traces are tree-like or general resolution refutations
(Beame–Kautz–Sabharwal 2004; Pipatsrisawat–Darwiche 2011), and resolution
has exponential lower bounds (Haken 1985; Urquhart 1987;
Chvátal–Szemerédi 1988).  Those lower bounds are cited, not formalized.
Core Lean only.
-/

namespace Issue532.Idea21

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

/-! ## Splitting solvers -/

/-- Pure splitting over the variable list `vs`. -/
def solve : List Nat → CNF → Bool
  | [], φ => evalCNF (fun _ => false) φ
  | v :: vs, φ => solve vs (restrict v true φ) || solve vs (restrict v false φ)

/-- **Correctness of splitting.** -/
theorem solve_correct (vs : List Nat) (φ : CNF) (h : VarsIn φ vs) :
    solve vs φ = true ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => rw [sat_no_vars φ h]; rfl
  | cons v vs ih =>
    rw [sat_split φ v, solve, Bool.or_eq_true,
      ih _ (restrict_vars φ v vs true h), ih _ (restrict_vars φ v vs false h)]

/-- Leaves of the unpruned split tree. -/
def leaves : List Nat → CNF → Nat
  | [], _ => 1
  | v :: vs, φ => leaves vs (restrict v true φ) + leaves vs (restrict v false φ)

/-- **The unpruned split tree always has `2 ^ vs.length` leaves.** -/
theorem leaves_eq (vs : List Nat) (φ : CNF) : leaves vs φ = 2 ^ vs.length := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih => simp [leaves, ih, Nat.pow_succ]; omega

theorem empty_clause_unsat (φ : CNF) (h : ([] : Clause) ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  have := (evalCNF_true_iff a φ).mp ha [] h
  simp [evalClause] at this

/-- DPLL-style splitting with pruning: stop on the empty formula (satisfiable)
or on an empty clause (unsatisfiable). -/
def dpll : List Nat → CNF → Bool
  | [], φ => evalCNF (fun _ => false) φ
  | v :: vs, φ =>
    if φ = [] then true
    else if ([] : Clause) ∈ φ then false
    else dpll vs (restrict v true φ) || dpll vs (restrict v false φ)

/-- **Correctness of DPLL splitting.** -/
theorem dpll_correct (vs : List Nat) (φ : CNF) (h : VarsIn φ vs) :
    dpll vs φ = true ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => rw [sat_no_vars φ h]; rfl
  | cons v vs ih =>
    by_cases h0 : φ = []
    · subst h0; simp only [dpll, ↓reduceIte]
      exact ⟨fun _ => ⟨fun _ => false, rfl⟩, fun _ => by trivial⟩
    · by_cases h1 : ([] : Clause) ∈ φ
      · simp only [dpll, h0, h1, ↓reduceIte, ↓reduceIte]
        exact ⟨fun h => absurd h (by simp), fun hs => absurd hs (empty_clause_unsat φ h1)⟩
      · simp only [dpll, h0, h1, ↓reduceIte]
        rw [sat_split φ v, Bool.or_eq_true,
          ih _ (restrict_vars φ v vs true h), ih _ (restrict_vars φ v vs false h)]

/-- Leaves of the pruned DPLL tree. -/
def dpllLeaves : List Nat → CNF → Nat
  | [], _ => 1
  | v :: vs, φ =>
    if φ = [] then 1
    else if ([] : Clause) ∈ φ then 1
    else dpllLeaves vs (restrict v true φ) + dpllLeaves vs (restrict v false φ)

/-- Pruning never makes the tree larger than `2 ^ vs.length`; whether it makes
it polynomially small is exactly a resolution-size question. -/
theorem dpllLeaves_le (vs : List Nat) (φ : CNF) : dpllLeaves vs φ ≤ 2 ^ vs.length := by
  induction vs generalizing φ with
  | nil => exact Nat.le_refl _
  | cons v vs ih =>
    have h1 : 1 ≤ 2 ^ (vs.length + 1) := Nat.one_le_two_pow
    simp only [dpllLeaves]
    split
    · exact h1
    · split
      · exact h1
      · have a := ih (restrict v true φ)
        have b := ih (restrict v false φ)
        simp only [List.length_cons, Nat.pow_succ]
        omega

end Issue532.Idea21
