/-!
# Issue #532, Idea 18: structural restrictions and easy subclasses of SAT

Proved here, in general (for every CNF / every reduction):

* `allTrue_satisfies`, `allFalse_satisfies`: a CNF in which every clause has a
  positive (resp. negative) literal is satisfied by the all-true
  (resp. all-false) assignment ("1-valid" / "0-valid" in Schaefer's terms).
* `unitCNF_sat_iff`: a CNF whose clauses all have at most one literal is
  satisfiable iff it has no empty clause and no complementary pair of unit
  clauses.  `unitDecide` is a Boolean procedure proved correct for this class
  (`unitDecide_correct`).
* `reduction_into_trivial_class`, `no_reduction_of_nontrivial`: a
  yes/no-preserving map into a class on which the target predicate takes a single value
  forces the source predicate to take a single value.
* `no_sat_reduction_into_positive`, `no_sat_reduction_into_negative`: no
  satisfiability-preserving map whatsoever (computable or not) sends every
  CNF into the 1-valid or the 0-valid class.
* `restriction_transfer` and `poly_comp_bound`: if a restricted class `R`
  admits a correct decider and SAT reduces into `R` with polynomial size
  blow-up, then composing gives a correct SAT decider whose cost is bounded
  by a composed polynomial.  The hypothesis `PolySizeReductionInto R` is the
  open obligation (it is not proved for any class in P; doing so for a class
  with a polynomial-time decider would prove P = NP).

Verdict: special-case algorithms are correct, but refuted as a general route
unless the restriction is shown NP-hard (Schaefer 1978 classifies exactly
which Boolean constraint languages remain NP-complete).
-/

namespace Issue532.Idea18

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

/-- Size of a CNF: total number of literal occurrences plus number of clauses. -/
def size : CNF → Nat
  | [] => 0
  | C :: φ => C.length + 1 + size φ

/-! ## (a) 1-valid and 0-valid classes -/

/-- Every clause contains a positive literal (Schaefer's "1-valid"). -/
def PositiveClauses (φ : CNF) : Prop := ∀ C ∈ φ, ∃ l ∈ C, l.pos = true

/-- Every clause contains a negative literal (Schaefer's "0-valid"). -/
def NegativeClauses (φ : CNF) : Prop := ∀ C ∈ φ, ∃ l ∈ C, l.pos = false

/-- The all-true assignment satisfies every CNF whose clauses each contain a
positive literal. -/
theorem allTrue_satisfies (φ : CNF) (h : PositiveClauses φ) :
    evalCNF (fun _ => true) φ = true := by
  rw [evalCNF_true_iff]
  intro C hC
  obtain ⟨l, hl, hp⟩ := h C hC
  rw [evalClause_true_iff]
  exact ⟨l, hl, by simp [evalLit, hp]⟩

/-- The all-false assignment satisfies every CNF whose clauses each contain a
negative literal. -/
theorem allFalse_satisfies (φ : CNF) (h : NegativeClauses φ) :
    evalCNF (fun _ => false) φ = true := by
  rw [evalCNF_true_iff]
  intro C hC
  obtain ⟨l, hl, hp⟩ := h C hC
  rw [evalClause_true_iff]
  exact ⟨l, hl, by simp [evalLit, hp]⟩

theorem positive_satisfiable (φ : CNF) (h : PositiveClauses φ) : Satisfiable φ :=
  ⟨_, allTrue_satisfies φ h⟩

theorem negative_satisfiable (φ : CNF) (h : NegativeClauses φ) : Satisfiable φ :=
  ⟨_, allFalse_satisfies φ h⟩

/-! ## (b) Unit CNFs (every clause has at most one literal) -/

def IsUnitCNF (φ : CNF) : Prop := ∀ C ∈ φ, C.length ≤ 1

/-- Two unit clauses on the same variable with opposite signs. -/
def UnitClash (φ : CNF) : Prop :=
  ∃ l₁ l₂, [l₁] ∈ φ ∧ [l₂] ∈ φ ∧ l₁.var = l₂.var ∧ l₁.pos ≠ l₂.pos

theorem clause_of_length_le_one (C : Clause) (h : C.length ≤ 1) (hne : C ≠ []) :
    ∃ l, C = [l] := by
  match C, h, hne with
  | [l], _, _ => exact ⟨l, rfl⟩
  | _ :: _ :: _, h, _ => simp at h

/-- **Unit CNF characterization.**  A CNF whose clauses have at most one
literal is satisfiable iff it has no empty clause and no complementary pair of
unit clauses. -/
theorem unitCNF_sat_iff (φ : CNF) (hu : IsUnitCNF φ) :
    Satisfiable φ ↔ ([] ∉ φ ∧ ¬ UnitClash φ) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [evalCNF_true_iff] at ha
    refine ⟨fun hemp => ?_, ?_⟩
    · have := ha [] hemp
      simp [evalClause] at this
    · rintro ⟨l₁, l₂, h₁, h₂, hv, hp⟩
      have e₁ := ha _ h₁
      have e₂ := ha _ h₂
      simp only [evalClause, evalLit, Bool.or_false] at e₁ e₂
      rw [hv] at e₁
      cases hp₁ : l₁.pos <;> cases hp₂ : l₂.pos <;> simp_all
  · rintro ⟨hne, hclash⟩
    refine ⟨fun v => decide (([⟨v, true⟩] : Clause) ∈ φ), ?_⟩
    rw [evalCNF_true_iff]
    intro C hC
    have hCne : C ≠ [] := fun h => hne (h ▸ hC)
    obtain ⟨l, rfl⟩ := clause_of_length_le_one C (hu C hC) hCne
    simp only [evalClause, evalLit, Bool.or_false]
    cases hp : l.pos with
    | true =>
      have : l = ⟨l.var, true⟩ := by cases l; simp_all
      simp only [ite_true, decide_eq_true_iff]
      rw [← this]
      exact hC
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not]
      intro hmem
      exact hclash ⟨⟨l.var, true⟩, l, hmem, hC, rfl, by simp [hp]⟩

/-- A quadratic-time Boolean decision procedure for unit CNFs. -/
def unitDecide (φ : CNF) : Bool :=
  !(decide (([] : Clause) ∈ φ)) &&
  φ.all (fun C₁ => φ.all (fun C₂ =>
    match C₁, C₂ with
    | [l₁], [l₂] => !(decide (l₁.var = l₂.var) && decide (l₁.pos ≠ l₂.pos))
    | _, _ => true))

/-- `unitDecide` is correct on every unit CNF. -/
theorem unitDecide_correct (φ : CNF) (hu : IsUnitCNF φ) :
    unitDecide φ = true ↔ Satisfiable φ := by
  rw [unitCNF_sat_iff φ hu]
  unfold unitDecide
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hne, hall⟩
    refine ⟨hne, ?_⟩
    rintro ⟨l₁, l₂, h₁, h₂, hv, hp⟩
    rw [List.all_eq_true] at hall
    have h := hall _ h₁
    rw [List.all_eq_true] at h
    have h' := h _ h₂
    simp [hv, hp] at h'
  · rintro ⟨hne, hclash⟩
    refine ⟨hne, ?_⟩
    rw [List.all_eq_true]
    intro C₁ h₁
    rw [List.all_eq_true]
    intro C₂ h₂
    match C₁, C₂, h₁, h₂ with
    | [l₁], [l₂], h₁, h₂ =>
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases hv : l₁.var = l₂.var
      · right
        intro hp
        exact hclash ⟨l₁, l₂, h₁, h₂, hv, hp⟩
      · left; exact hv
    | [], _, _, _ => rfl
    | _ :: _ :: _, _, _, _ => rfl
    | [_], [], _, _ => rfl
    | [_], _ :: _ :: _, _, _ => rfl

/-! ## (c) Reductions into trivial classes -/

/-- If `L` reduces to `M` along `f` and `M` is identically true, `L` is
identically true. -/
theorem reduction_into_trivial_class {α β : Type} (L : α → Prop) (M : β → Prop)
    (f : α → β) (hred : ∀ x, L x ↔ M (f x)) (hconst : ∀ y, M y) : ∀ x, L x :=
  fun x => (hred x).mpr (hconst (f x))

/-- A predicate with a no-instance admits no reduction (by any function) to a
predicate that is identically true. -/
theorem no_reduction_of_nontrivial {α β : Type} (L : α → Prop) (M : β → Prop)
    (hno : ∃ x, ¬ L x) (hconst : ∀ y, M y) : ¬ ∃ f : α → β, ∀ x, L x ↔ M (f x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := hno
  exact hx (reduction_into_trivial_class L M f hf hconst x)

theorem empty_clause_unsat : ¬ Satisfiable [[]] := by
  rintro ⟨a, ha⟩
  simp [evalCNF, evalClause] at ha

/-- No satisfiability-preserving map (computable or not) lands inside the
1-valid class: SAT has an unsatisfiable instance, the class has none. -/
theorem no_sat_reduction_into_positive :
    ¬ ∃ f : CNF → CNF, (∀ φ, PositiveClauses (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) := by
  rintro ⟨f, hpos, hpres⟩
  exact empty_clause_unsat ((hpres [[]]).mpr (positive_satisfiable _ (hpos _)))

/-- Dually for the 0-valid class. -/
theorem no_sat_reduction_into_negative :
    ¬ ∃ f : CNF → CNF, (∀ φ, NegativeClauses (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) := by
  rintro ⟨f, hneg, hpres⟩
  exact empty_clause_unsat ((hpres [[]]).mpr (negative_satisfiable _ (hneg _)))

/-! ## The only useful direction: a hardness-preserving restriction -/

def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

/-- **Open obligation** for a restricted class `R`: SAT reduces into `R` by a
satisfiability-preserving map with polynomial size blow-up.  (Time to compute
the map must also be polynomial; this file has no machine model, so only the
size bound is recorded.)  For the classes of (a) this is false by
`no_sat_reduction_into_positive`; for Horn, 2-CNF or unit CNF it is
equivalent in strength to P = NP, because those classes are in P. -/
def PolySizeReductionInto (R : CNF → Prop) : Prop :=
  ∃ (f : CNF → CNF) (c k : Nat),
    (∀ φ, R (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) ∧
    (∀ φ, size (f φ) ≤ polyEval c k (size φ))

/-- Polynomials of the repository's form are closed under composition. -/
theorem poly_comp_bound (c k c' k' n : Nat) :
    polyEval c' k' (polyEval c k n) ≤ polyEval (c' * (c + 1) ^ k') (k * k') n := by
  unfold polyEval
  have h1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h3 : (c * (n + 1) ^ k + 1) ^ k' ≤ ((c + 1) * (n + 1) ^ k) ^ k' :=
    Nat.pow_le_pow_left h2 k'
  rw [Nat.mul_pow, ← Nat.pow_mul] at h3
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left c' h3

/-- **Conditional transfer.**  A decider `d` correct on `R`, composed with a
satisfiability-preserving reduction into `R`, decides SAT; if `d`'s cost is
bounded by a monotone polynomial in the size of its input, the composed cost
is bounded by a polynomial in the size of the original formula (the cost of
computing `f` must be added separately). -/
theorem restriction_transfer (R : CNF → Prop) (hR : PolySizeReductionInto R)
    (d : CNF → Bool) (hd : ∀ ψ, R ψ → (d ψ = true ↔ Satisfiable ψ))
    (dcost : CNF → Nat) (c' k' : Nat) (hcost : ∀ ψ, dcost ψ ≤ polyEval c' k' (size ψ)) :
    ∃ f : CNF → CNF, ∃ C K : Nat,
      (∀ φ, d (f φ) = true ↔ Satisfiable φ) ∧
      (∀ φ, dcost (f φ) ≤ polyEval C K (size φ)) := by
  obtain ⟨f, c, k, hfR, hfsat, hfsize⟩ := hR
  refine ⟨f, c' * (c + 1) ^ k', k * k', fun φ => ?_, fun φ => ?_⟩
  · rw [hd _ (hfR φ), ← hfsat φ]
  · have mono : polyEval c' k' (size (f φ)) ≤ polyEval c' k' (polyEval c k (size φ)) := by
      unfold polyEval
      exact Nat.mul_le_mul_left c' (Nat.pow_le_pow_left (by have := hfsize φ; unfold polyEval at this; omega) k')
    exact Nat.le_trans (hcost _) (Nat.le_trans mono (poly_comp_bound c k c' k' _))

end Issue532.Idea18
