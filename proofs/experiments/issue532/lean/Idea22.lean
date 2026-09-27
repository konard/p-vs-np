/-!
# Issue #532, Idea 22: decision-to-search self-reduction for SAT

Proved here, for every CNF and every decision procedure `dec`:

* `search_correct`: if `dec` decides satisfiability (`Decides dec`), `φ` is
  satisfiable and all variables of `φ` lie in `vs`, then the assignment
  built by fixing the variables of `vs` one at a time (keep `true` when
  `dec` says the `true`-restriction is satisfiable, else `false`)
  satisfies `φ`;
* `search_calls`: the search asks the decider exactly `vs.length` questions;
* `searchCost_le`: if each question costs at most `c (s+1)^k` on a formula
  of size `s`, the whole search costs at most `vs.length * c (size φ + 1)^k`;
* `decision_to_search`: a polynomially bounded exact decider (the open
  obligation `ExactPolyDecider`, relative to a cost model) yields a search
  procedure of polynomially bounded total query cost (`PolySearch`);
* `search_gives_decider`: conversely, a correct search procedure yields a
  correct decider;
* `satDec_correct`, `zero_cost_trivial`: a correct (exponential) decider
  exists unconditionally, so the obligation is only meaningful for an
  honest cost model.

**Verdict.** Correct tool, insufficient alone.  Self-reducibility shows that
search is no harder than decision (up to a factor `size φ`), so P = NP is
equivalent to polynomial-time SAT search.  It does not produce a fast
decider; the remaining obligation is exactly a polynomial exact decider.
Core Lean only.
-/

namespace Issue532.Idea22

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

/-- The list of variable occurrences of `φ` (with repetitions). -/
def varsOf : CNF → List Nat
  | [] => []
  | C :: φ => C.map Lit.var ++ varsOf φ

theorem varsOf_spec (φ : CNF) : VarsIn φ (varsOf φ) := by
  induction φ with
  | nil => intro C hC; simp at hC
  | cons D φ ih =>
    intro C hC l hl
    simp only [varsOf, List.mem_append]
    rcases List.mem_cons.mp hC with e | e
    · rw [e] at hl; exact Or.inl (List.mem_map.mpr ⟨l, hl, rfl⟩)
    · exact Or.inr (ih C e l hl)

theorem varsOf_length_le (φ : CNF) : (varsOf φ).length ≤ size φ := by
  induction φ with
  | nil => simp [varsOf, size]
  | cons C φ ih => simp only [varsOf, size, List.length_append, List.length_map]; omega

/-! ## Deciders and the self-reduction -/

/-- `dec` decides satisfiability exactly, on every CNF. -/
def Decides (dec : CNF → Bool) : Prop := ∀ ψ, dec ψ = true ↔ Satisfiable ψ

/-- Fix the variables of `vs` in order, asking `dec` whether the
`true`-restriction is satisfiable.  Returns the assignment and the number of
questions asked. -/
def search (dec : CNF → Bool) : List Nat → CNF → Assignment × Nat
  | [], _ => (fun _ => false, 0)
  | v :: vs, φ =>
    let b := dec (restrict v true φ)
    let r := search dec vs (restrict v b φ)
    (setVar r.1 v b, r.2 + 1)

/-- **Search is correct.**  With an exact decider, the search returns a
satisfying assignment of every satisfiable CNF whose variables lie in `vs`. -/
theorem search_correct (dec : CNF → Bool) (hdec : Decides dec) (vs : List Nat) (φ : CNF)
    (hv : VarsIn φ vs) (hs : Satisfiable φ) : evalCNF (search dec vs φ).1 φ = true := by
  induction vs generalizing φ with
  | nil => exact (sat_no_vars φ hv).mp hs
  | cons v vs ih =>
    have hb : Satisfiable (restrict v (dec (restrict v true φ)) φ) := by
      cases h : dec (restrict v true φ)
      · have hn : ¬ Satisfiable (restrict v true φ) := by
          intro hsat
          have h' := (hdec _).mpr hsat
          rw [h] at h'
          exact Bool.false_ne_true h'
        rcases (sat_split φ v).mp hs with h1 | h2
        · exact absurd h1 hn
        · exact h2
      · exact (hdec _).mp h
    have hr := ih _ (restrict_vars φ v vs _ hv) hb
    show evalCNF (setVar (search dec vs (restrict v (dec (restrict v true φ)) φ)).1 v
      (dec (restrict v true φ))) φ = true
    rw [← eval_restrict]
    exact hr

/-- **Exact call count.**  The search asks exactly `vs.length` questions. -/
theorem search_calls (dec : CNF → Bool) (vs : List Nat) (φ : CNF) :
    (search dec vs φ).2 = vs.length := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    show (search dec vs (restrict v (dec (restrict v true φ)) φ)).2 + 1 = vs.length + 1
    rw [ih]

/-- The search output is a witness exactly when one exists. -/
theorem search_decides (dec : CNF → Bool) (hdec : Decides dec) (vs : List Nat) (φ : CNF)
    (hv : VarsIn φ vs) : evalCNF (search dec vs φ).1 φ = true ↔ Satisfiable φ :=
  ⟨fun h => ⟨_, h⟩, search_correct dec hdec vs φ hv⟩

/-- Search over all variable occurrences of `φ`. -/
def fullSearch (dec : CNF → Bool) (φ : CNF) : Assignment × Nat := search dec (varsOf φ) φ

theorem fullSearch_correct (dec : CNF → Bool) (hdec : Decides dec) (φ : CNF)
    (hs : Satisfiable φ) : evalCNF (fullSearch dec φ).1 φ = true :=
  search_correct dec hdec (varsOf φ) φ (varsOf_spec φ) hs

theorem fullSearch_calls_le (dec : CNF → Bool) (φ : CNF) : (fullSearch dec φ).2 ≤ size φ := by
  unfold fullSearch; rw [search_calls]; exact varsOf_length_le φ

/-- **Search to decision.**  Any procedure that returns a satisfying
assignment for every satisfiable CNF yields an exact decider (evaluate its
output). -/
theorem search_gives_decider (S : CNF → Assignment)
    (hS : ∀ φ, Satisfiable φ → evalCNF (S φ) φ = true) :
    Decides (fun φ => evalCNF (S φ) φ) :=
  fun φ => ⟨fun h => ⟨_, h⟩, hS φ⟩

/-! ## Costs -/

/-- Polynomials in the repository form `c * (n+1)^k`. -/
def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

theorem polyEval_mono (c k : Nat) {m n : Nat} (h : m ≤ n) : polyEval c k m ≤ polyEval c k n :=
  Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) k)

theorem mul_polyEval_le (c k n : Nat) : n * polyEval c k n ≤ polyEval c (k + 1) n := by
  unfold polyEval
  rw [Nat.pow_succ, Nat.mul_comm n, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.le_succ n)

/-- Total cost of the questions asked by `search`, for a per-question cost. -/
def searchCost (dec : CNF → Bool) (cost : CNF → Nat) : List Nat → CNF → Nat
  | [], _ => 0
  | v :: vs, φ =>
    cost (restrict v true φ) + searchCost dec cost vs (restrict v (dec (restrict v true φ)) φ)

/-- **Cost of the self-reduction.**  Polynomially bounded questions give a
total cost of at most `vs.length` times the bound at the input size. -/
theorem searchCost_le (dec : CNF → Bool) (cost : CNF → Nat) (c k : Nat)
    (hc : ∀ ψ, cost ψ ≤ polyEval c k (size ψ)) (vs : List Nat) (φ : CNF) :
    searchCost dec cost vs φ ≤ vs.length * polyEval c k (size φ) := by
  induction vs generalizing φ with
  | nil => simp [searchCost]
  | cons v vs ih =>
    simp only [searchCost, List.length_cons, Nat.succ_mul]
    have h1 : cost (restrict v true φ) ≤ polyEval c k (size φ) :=
      Nat.le_trans (hc _) (polyEval_mono c k (size_restrict_le v true φ))
    have h2 := Nat.le_trans (ih (restrict v (dec (restrict v true φ)) φ))
      (Nat.mul_le_mul_left vs.length (polyEval_mono c k (size_restrict_le v _ φ)))
    rw [Nat.add_comm (vs.length * _)]
    exact Nat.add_le_add h1 h2

/-- A cost model: the cost of running a decider on an input.  It must come
from a machine model, which is not formalized here. -/
abbrev CostModel := (CNF → Bool) → CNF → Nat

/-- **Open obligation.**  An exact SAT decider of polynomially bounded cost in
the cost model `Cost`.  For an honest model (Turing machine steps) this is
SAT ∈ P, i.e. P = NP. -/
def ExactPolyDecider (Cost : CostModel) : Prop :=
  ∃ dec c k, Decides dec ∧ ∀ ψ, Cost dec ψ ≤ polyEval c k (size ψ)

/-- Polynomially bounded search: a decider whose self-reduction finds a
satisfying assignment of every satisfiable CNF at polynomial total query cost. -/
def PolySearch (Cost : CostModel) : Prop :=
  ∃ dec c k, ∀ φ, (Satisfiable φ → evalCNF (fullSearch dec φ).1 φ = true) ∧
    searchCost dec (Cost dec) (varsOf φ) φ ≤ polyEval c (k + 1) (size φ)

/-- **Decision to search (conditional).**  The obligation yields polynomial
search with total query cost `c (size φ + 1)^(k+1)`. -/
theorem decision_to_search (Cost : CostModel) (h : ExactPolyDecider Cost) : PolySearch Cost := by
  obtain ⟨dec, c, k, hdec, hc⟩ := h
  refine ⟨dec, c, k, fun φ => ⟨fullSearch_correct dec hdec φ, ?_⟩⟩
  exact Nat.le_trans (searchCost_le dec (Cost dec) c k hc (varsOf φ) φ)
    (Nat.le_trans (Nat.mul_le_mul_right _ (varsOf_length_le φ)) (mul_polyEval_le c k (size φ)))

/-! ## An unconditional (exponential) decider -/

def solve : List Nat → CNF → Bool
  | [], φ => evalCNF (fun _ => false) φ
  | v :: vs, φ => solve vs (restrict v true φ) || solve vs (restrict v false φ)

theorem solve_correct (vs : List Nat) (φ : CNF) (h : VarsIn φ vs) :
    solve vs φ = true ↔ Satisfiable φ := by
  induction vs generalizing φ with
  | nil => exact (sat_no_vars φ h).symm
  | cons v vs ih =>
    rw [sat_split φ v, ← ih _ (restrict_vars φ v vs true h),
      ← ih _ (restrict_vars φ v vs false h)]
    simp [solve]

/-- The splitting decider of Idea 21, run on the variables of the input. -/
def satDec (φ : CNF) : Bool := solve (varsOf φ) φ

/-- An exact decider exists unconditionally; only its cost is in question. -/
theorem satDec_correct : Decides satDec := fun φ => solve_correct (varsOf φ) φ (varsOf_spec φ)

/-- In the dishonest cost model that charges nothing, the obligation holds
trivially: the obligation is meaningful only for an honest cost model. -/
theorem zero_cost_trivial : ExactPolyDecider (fun _ _ => 0) :=
  ⟨satDec, 0, 0, satDec_correct, fun _ => Nat.zero_le _⟩

/-- Unconditional search: with the exponential decider, the self-reduction
finds a satisfying assignment of every satisfiable CNF. -/
theorem unconditional_search (φ : CNF) (hs : Satisfiable φ) :
    evalCNF (fullSearch satDec φ).1 φ = true :=
  fullSearch_correct satDec satDec_correct φ hs

end Issue532.Idea22
