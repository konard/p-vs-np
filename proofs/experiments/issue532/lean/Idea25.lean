/-!
# Issue #532, Idea 25: decomposable constraints (component splitting)

Verdict: **correct tool, insufficient alone (general theorem proved)**.

This file works with an explicit CNF model (literals over natural-number
variables, clauses as lists of literals, formulas as lists of clauses) and
proves, for *all* formulas:

* `eval_congr` — the value of a CNF under an assignment depends only on the
  assignment's values on the variables that occur in the CNF;
* `split_sat_iff` — if `φ₁` and `φ₂` have disjoint variable sets then
  `φ₁ ++ φ₂` is satisfiable iff both parts are satisfiable (the witness for the
  union is obtained by merging the two witnesses);
* `joinAll_sat_iff` — the same for any list of pairwise variable-disjoint
  components;
* `chain_not_splittable` — for every `n`, the chain formula
  `(x₀ ∨ x₁) ∧ (x₁ ∨ x₂) ∧ … ∧ (x_{n-1} ∨ x_n)` has no non-trivial split of
  its clauses into two variable-disjoint parts: every selection of clauses
  that is neither empty nor full contains two adjacent clauses, one selected
  and one not, sharing a variable.

The splitting lemma is exact, but it only helps when a formula actually falls
apart into small components. The chain family shows that already trivially
satisfiable formulas can be connected for every size; the hard families used
in complexity theory (random 3-CNF, Tseitin formulas on expanders) are
connected and even have linear treewidth. Component splitting therefore gives
no polynomial bound for SAT in general. See `../ideas/Idea25.md`.
-/

namespace Issue532.Idea25

/-! ## CNF core -/

/-- A literal: a variable index together with its polarity (`true` = positive). -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool :=
  if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a, evalCNF a φ = true

def clauseVars (c : Clause) : List Nat := c.map Lit.var

/-- The list of variable occurrences of a CNF (with repetitions). -/
def vars : CNF → List Nat
  | [] => []
  | c :: φ => clauseVars c ++ vars φ

theorem evalCNF_append (a : Assignment) (φ ψ : CNF) :
    evalCNF a (φ ++ ψ) = (evalCNF a φ && evalCNF a ψ) := by
  induction φ with
  | nil => simp [evalCNF]
  | cons c φ ih => simp [evalCNF, ih, Bool.and_assoc]

theorem vars_append (φ ψ : CNF) : vars (φ ++ ψ) = vars φ ++ vars ψ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp [vars, ih, List.append_assoc]

theorem evalClause_congr (a b : Assignment) (c : Clause)
    (h : ∀ v, v ∈ clauseVars c → a v = b v) : evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hl : a l.var = b l.var := h l.var (by simp [clauseVars])
    have hc : ∀ v, v ∈ clauseVars c → a v = b v := by
      intro v hv
      apply h v
      simp only [clauseVars, List.map_cons, List.mem_cons]
      exact Or.inr hv
    simp only [evalClause, evalLit, hl, ih hc]

/-- **Locality of evaluation.** Two assignments that agree on every variable
occurring in `φ` give `φ` the same value. -/
theorem eval_congr (a b : Assignment) (φ : CNF)
    (h : ∀ v, v ∈ vars φ → a v = b v) : evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have hc : ∀ v, v ∈ clauseVars c → a v = b v :=
      fun v hv => h v (by simp only [vars, List.mem_append]; exact Or.inl hv)
    have hφ : ∀ v, v ∈ vars φ → a v = b v :=
      fun v hv => h v (by simp only [vars, List.mem_append]; exact Or.inr hv)
    simp only [evalCNF, evalClause_congr a b c hc, ih hφ]

/-! ## Splitting into variable-disjoint components -/

/-- Disjointness of the variables of two CNFs. -/
def Disjoint (φ ψ : CNF) : Prop := ∀ v, v ∈ vars φ → v ∉ vars ψ

/-- The merged assignment: use `a₁` on the variables of `φ₁`, `a₂` elsewhere. -/
def merge (φ₁ : CNF) (a₁ a₂ : Assignment) : Assignment :=
  fun v => if v ∈ vars φ₁ then a₁ v else a₂ v

theorem merge_left (φ₁ : CNF) (a₁ a₂ : Assignment) :
    evalCNF (merge φ₁ a₁ a₂) φ₁ = evalCNF a₁ φ₁ :=
  eval_congr _ _ φ₁ (fun v hv => by simp [merge, hv])

theorem merge_right (φ₁ φ₂ : CNF) (a₁ a₂ : Assignment) (hd : Disjoint φ₁ φ₂) :
    evalCNF (merge φ₁ a₁ a₂) φ₂ = evalCNF a₂ φ₂ :=
  eval_congr _ _ φ₂ (fun v hv => by
    have : v ∉ vars φ₁ := fun h1 => hd v h1 hv
    simp [merge, this])

/-- **Component splitting theorem.** For variable-disjoint `φ₁`, `φ₂`,
`φ₁ ++ φ₂` is satisfiable iff each part is satisfiable. -/
theorem split_sat_iff (φ₁ φ₂ : CNF) (hd : Disjoint φ₁ φ₂) :
    Satisfiable (φ₁ ++ φ₂) ↔ Satisfiable φ₁ ∧ Satisfiable φ₂ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [evalCNF_append, Bool.and_eq_true] at ha
    exact ⟨⟨a, ha.1⟩, ⟨a, ha.2⟩⟩
  · rintro ⟨⟨a₁, h₁⟩, ⟨a₂, h₂⟩⟩
    refine ⟨merge φ₁ a₁ a₂, ?_⟩
    rw [evalCNF_append, merge_left, merge_right φ₁ φ₂ a₁ a₂ hd, h₁, h₂]
    rfl

/-- The direction `Satisfiable (φ₁ ++ φ₂) → …` needs no disjointness. -/
theorem sat_append_left (φ₁ φ₂ : CNF) (h : Satisfiable (φ₁ ++ φ₂)) :
    Satisfiable φ₁ ∧ Satisfiable φ₂ := by
  obtain ⟨a, ha⟩ := h
  rw [evalCNF_append, Bool.and_eq_true] at ha
  exact ⟨⟨a, ha.1⟩, ⟨a, ha.2⟩⟩

/-- Concatenation of a list of components. -/
def joinAll : List CNF → CNF
  | [] => []
  | φ :: rest => φ ++ joinAll rest

/-- Each component is variable-disjoint from the union of the later ones
(this is equivalent to pairwise disjointness). -/
def DisjointChain : List CNF → Prop
  | [] => True
  | φ :: rest => Disjoint φ (joinAll rest) ∧ DisjointChain rest

/-- **Many components.** For pairwise variable-disjoint components, the union
is satisfiable iff every component is. -/
theorem joinAll_sat_iff (φs : List CNF) (hd : DisjointChain φs) :
    Satisfiable (joinAll φs) ↔ ∀ φ, φ ∈ φs → Satisfiable φ := by
  induction φs with
  | nil =>
    simp only [joinAll, List.not_mem_nil, false_implies, implies_true, iff_true]
    exact ⟨fun _ => false, rfl⟩
  | cons φ rest ih =>
    obtain ⟨hφ, hrest⟩ := hd
    simp only [joinAll]
    rw [split_sat_iff φ (joinAll rest) hφ, ih hrest]
    constructor
    · rintro ⟨h1, h2⟩ ψ hψ
      rcases List.mem_cons.mp hψ with h | h
      · exact h ▸ h1
      · exact h2 ψ h
    · intro h
      exact ⟨h φ List.mem_cons_self, fun ψ hψ => h ψ (List.mem_cons_of_mem φ hψ)⟩

/-! ## Connected families cannot be split -/

/-- The `i`-th chain clause `xᵢ ∨ xᵢ₊₁`. -/
def chainClause (i : Nat) : Clause := [⟨i, true⟩, ⟨i + 1, true⟩]

/-- The chain formula with clauses `chainClause 0, …, chainClause (n-1)`. -/
def chain (n : Nat) : CNF := (List.range n).map chainClause

theorem chain_satisfiable (n : Nat) : Satisfiable (chain n) := by
  refine ⟨fun _ => true, ?_⟩
  simp only [chain]
  induction (List.range n) with
  | nil => rfl
  | cons i l ih => simp [evalCNF, chainClause, evalClause, evalLit, ih]

theorem chain_length (n : Nat) : (chain n).length = n := by
  simp [chain]

/-- Discrete intermediate value theorem: a Boolean sequence that changes value
between `i` and `i + d` changes value at some adjacent pair in between. -/
theorem adjacent_change (p : Nat → Bool) (i d : Nat) (h : p i ≠ p (i + d)) :
    ∃ k, i ≤ k ∧ k + 1 ≤ i + d ∧ p k ≠ p (k + 1) := by
  induction d with
  | zero => exact absurd rfl h
  | succ d ih =>
    by_cases hd : p i = p (i + d)
    · refine ⟨i + d, by omega, by omega, ?_⟩
      rw [← hd]
      exact h
    · obtain ⟨k, hk1, hk2, hk3⟩ := ih hd
      exact ⟨k, hk1, by omega, hk3⟩

/-- **The chain is connected for every `n`.** Let `p` select a set of clause
indices below `n` containing some index `i` and missing some index `j`. Then
there is an adjacent pair `k, k+1 < n` with exactly one of the two clauses
selected, and the variable `x_{k+1}` occurs in both clauses. Hence no split of
the chain's clauses into two non-empty parts is variable-disjoint, so
`split_sat_iff` never applies non-trivially. -/
theorem chain_not_splittable (n : Nat) (p : Nat → Bool) (i j : Nat)
    (hi : i < n) (hj : j < n) (hpi : p i = true) (hpj : p j = false) :
    ∃ k, k + 1 < n ∧ p k ≠ p (k + 1) ∧
      k + 1 ∈ clauseVars (chainClause k) ∧ k + 1 ∈ clauseVars (chainClause (k + 1)) := by
  have shared : ∀ k, k + 1 ∈ clauseVars (chainClause k) ∧
      k + 1 ∈ clauseVars (chainClause (k + 1)) := by
    intro k; simp [clauseVars, chainClause]
  rcases Nat.lt_or_ge i j with hij | hij
  · obtain ⟨k, _, hk2, hk3⟩ := adjacent_change p i (j - i)
      (by rw [Nat.add_sub_cancel' (Nat.le_of_lt hij), hpi, hpj]; decide)
    exact ⟨k, by omega, hk3, shared k⟩
  · obtain ⟨k, _, hk2, hk3⟩ := adjacent_change p j (i - j)
      (by rw [Nat.add_sub_cancel' hij, hpi, hpj]; decide)
    exact ⟨k, by omega, hk3, shared k⟩

/-- Brute force on components: splitting reduces `2^(a+b)` candidate
assignments to `2^a + 2^b`, but only if both components are non-trivial;
the largest component still costs `2^max`. -/
theorem split_cost (a b : Nat) : 2 ^ a + 2 ^ b ≤ 2 * 2 ^ (max a b) ∧
    2 ^ (max a b) ≤ 2 ^ a + 2 ^ b := by
  have ha : 2 ^ a ≤ 2 ^ (max a b) := Nat.pow_le_pow_right (by decide) (Nat.le_max_left a b)
  have hb : 2 ^ b ≤ 2 ^ (max a b) := Nat.pow_le_pow_right (by decide) (Nat.le_max_right a b)
  refine ⟨by omega, ?_⟩
  rcases Nat.le_total a b with h | h
  · have e : max a b = b := by omega
    rw [e]; exact Nat.le_add_left _ _
  · have e : max a b = a := by omega
    rw [e]; exact Nat.le_add_right _ _


/-! ## The open obligation -/

/-- The open obligation (FS): a map in the class `PolyTime` sending every CNF to
pairwise variable-disjoint components whose union is equisatisfiable, each
component having at most `w |φ|` variable occurrences. -/
def ComponentObligation (PolyTime : (CNF → List CNF) → Prop) (w : Nat → Nat) : Prop :=
  ∃ f : CNF → List CNF, PolyTime f ∧ ∀ φ, DisjointChain (f φ) ∧
    (∀ ψ, ψ ∈ f φ → (vars ψ).length ≤ w φ.length) ∧
    (Satisfiable φ ↔ Satisfiable (joinAll (f φ)))

/-- Conditional theorem: under the obligation, satisfiability of every CNF is
the conjunction of the satisfiability of its small components. -/
theorem component_obligation_splits (PolyTime : (CNF → List CNF) → Prop) (w : Nat → Nat)
    (h : ComponentObligation PolyTime w) :
    ∃ f : CNF → List CNF, PolyTime f ∧ ∀ φ,
      (∀ ψ, ψ ∈ f φ → (vars ψ).length ≤ w φ.length) ∧
      (Satisfiable φ ↔ ∀ ψ, ψ ∈ f φ → Satisfiable ψ) := by
  obtain ⟨f, hf, hall⟩ := h
  refine ⟨f, hf, fun φ => ?_⟩
  obtain ⟨hd, hw, hp⟩ := hall φ
  exact ⟨hw, hp.trans (joinAll_sat_iff (f φ) hd)⟩

end Issue532.Idea25
