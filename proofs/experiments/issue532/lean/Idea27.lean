/-!
# Issue #532, Idea 27: variable elimination (Davis–Putnam resolution)

Verdict: **refuted as a route (general theorem)** — elimination is exact for
every CNF, but the clause count can grow multiplicatively at every step.

Proved for all CNFs `φ` and variables `v`:

* `eliminate_sat_iff` (the Davis–Putnam theorem) — `φ` is satisfiable iff
  `eliminate v φ` is satisfiable. Here `eliminate v φ` keeps the clauses not
  mentioning `v`, drops clauses containing both `v` and `¬v` (tautological in
  `v`), and adds every resolvent on `v` of a clause containing `v` (only
  positively) with a clause containing `¬v` (only negatively). No side
  condition on `φ` is needed; the tautology handling makes the statement
  unconditional.
* `eliminate_no_v` — no clause of `eliminate v φ` mentions `v`.
* `eliminate_length` — `|eliminate v φ| = |rest| + |pos| · |neg|` exactly.
* `blowup_length` / `blowup_resolvent` — for every `p q`, a formula with
  `p + q` clauses of width 2 whose elimination on `x₀` yields exactly `p · q`
  clauses, namely all the width-2 clauses `xᵢ ∨ yⱼ`.

Repeated elimination therefore decides SAT exactly, but the intermediate
formulas can grow multiplicatively; DP elimination is a resolution procedure,
so Haken's exponential lower bound for the pigeonhole principle applies to it
(cited, not formalized). See `../ideas/Idea27.md`.
-/

namespace Issue532.Idea27

/-! ## CNF core -/

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

def vars : CNF → List Nat
  | [] => []
  | c :: φ => clauseVars c ++ vars φ

theorem evalCNF_append (a : Assignment) (φ ψ : CNF) :
    evalCNF a (φ ++ ψ) = (evalCNF a φ && evalCNF a ψ) := by
  induction φ with
  | nil => simp [evalCNF]
  | cons c φ ih => simp [evalCNF, ih, Bool.and_assoc]

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

theorem evalClause_iff (a : Assignment) (c : Clause) :
    evalClause a c = true ↔ ∃ l, l ∈ c ∧ evalLit a l = true := by
  induction c with
  | nil => simp [evalClause]
  | cons l c ih =>
    simp only [evalClause, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨l', hl', h'⟩)
      · exact ⟨l, Or.inl rfl, h⟩
      · exact ⟨l', Or.inr hl', h'⟩
    · rintro ⟨l', hl' | hl', h'⟩
      · subst hl'; exact Or.inl h'
      · exact Or.inr ⟨l', hl', h'⟩

theorem evalCNF_iff (a : Assignment) (φ : CNF) :
    evalCNF a φ = true ↔ ∀ c, c ∈ φ → evalClause a c = true := by
  induction φ with
  | nil => simp [evalCNF]
  | cons c φ ih =>
    simp only [evalCNF, Bool.and_eq_true, ih, List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ d (hd | hd)
      · subst hd; exact h1
      · exact h2 d hd
    · intro h
      exact ⟨h c (Or.inl rfl), fun d hd => h d (Or.inr hd)⟩

/-! ## Davis–Putnam elimination -/

/-- Does clause `c` contain the literal `⟨v, b⟩`? -/
def hasLit (v : Nat) (b : Bool) (c : Clause) : Bool :=
  c.any (fun l => l.var == v && l.pos == b)

/-- Does clause `c` mention variable `v` at all? -/
def mentions (v : Nat) (c : Clause) : Bool := c.any (fun l => l.var == v)

/-- `c` contains `v` positively but not negatively. -/
def isPos (v : Nat) (c : Clause) : Bool := hasLit v true c && !hasLit v false c

/-- `c` contains `v` negatively but not positively. -/
def isNeg (v : Nat) (c : Clause) : Bool := hasLit v false c && !hasLit v true c

/-- Remove every literal on `v`. -/
def strip (v : Nat) (c : Clause) : Clause := c.filter (fun l => l.var != v)

/-- The resolvent on `v` of a positive and a negative clause. -/
def resolvent (v : Nat) (c d : Clause) : Clause := strip v c ++ strip v d

def posClauses (v : Nat) (φ : CNF) : CNF := φ.filter (isPos v)
def negClauses (v : Nat) (φ : CNF) : CNF := φ.filter (isNeg v)
def restClauses (v : Nat) (φ : CNF) : CNF := φ.filter (fun c => !mentions v c)

/-- One Davis–Putnam elimination step. -/
def eliminate (v : Nat) (φ : CNF) : CNF :=
  restClauses v φ ++
    (posClauses v φ).flatMap (fun c => (negClauses v φ).map (resolvent v c))

theorem hasLit_iff (v : Nat) (b : Bool) (c : Clause) :
    hasLit v b c = true ↔ (⟨v, b⟩ : Lit) ∈ c := by
  simp only [hasLit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨w, b'⟩, hl, h1, h2⟩
    simp only at h1 h2
    subst h1; subst h2; exact hl
  · intro h
    exact ⟨⟨v, b⟩, h, rfl, rfl⟩

theorem mentions_iff (v : Nat) (c : Clause) :
    mentions v c = true ↔ ∃ l, l ∈ c ∧ l.var = v := by
  simp [mentions, List.any_eq_true]

theorem mentions_cases (v : Nat) (c : Clause) (h : mentions v c = true) :
    hasLit v true c = true ∨ hasLit v false c = true := by
  obtain ⟨⟨w, b⟩, hl, hw⟩ := (mentions_iff v c).mp h
  simp only at hw
  subst hw
  cases b
  · exact Or.inr ((hasLit_iff _ _ _).mpr hl)
  · exact Or.inl ((hasLit_iff _ _ _).mpr hl)

theorem mem_strip (v : Nat) (c : Clause) (l : Lit) :
    l ∈ strip v c ↔ l ∈ c ∧ l.var ≠ v := by
  simp [strip, List.mem_filter]

theorem evalClause_append (a : Assignment) (c d : Clause) :
    evalClause a (c ++ d) = (evalClause a c || evalClause a d) := by
  induction c with
  | nil => simp [evalClause]
  | cons l c ih => simp [evalClause, ih, Bool.or_assoc]

/-- A literal of `v` in a clause is either `⟨v,true⟩` or `⟨v,false⟩`. -/
theorem lit_of_var (l : Lit) (v : Nat) (h : l.var = v) : l = ⟨v, l.pos⟩ := by
  cases l; simp only at h; subst h; rfl

/-- **No clause of the eliminated formula mentions `v`.** -/
theorem eliminate_no_v (v : Nat) (φ : CNF) :
    ∀ c, c ∈ eliminate v φ → mentions v c = false := by
  intro c hc
  simp only [eliminate, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨c₁, _, d, _, rfl⟩
  · simp only [restClauses, List.mem_filter, Bool.not_eq_true'] at hc
    exact hc.2
  · cases h : mentions v (resolvent v c₁ d) with
    | false => rfl
    | true =>
      obtain ⟨l, hl, hv⟩ := (mentions_iff v _).mp h
      simp only [resolvent, List.mem_append, mem_strip] at hl
      rcases hl with ⟨_, h'⟩ | ⟨_, h'⟩ <;> exact absurd hv h'

/-- **Exact size of one elimination step.** -/
theorem eliminate_length (v : Nat) (φ : CNF) :
    (eliminate v φ).length =
      (restClauses v φ).length + (posClauses v φ).length * (negClauses v φ).length := by
  simp only [eliminate, List.length_append]
  congr 1
  generalize posClauses v φ = P
  induction P with
  | nil => simp
  | cons c P ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
      List.length_cons, Nat.succ_mul]
    omega

/-- Soundness direction: a model of `φ` is a model of `eliminate v φ`. -/
theorem eliminate_sound (v : Nat) (φ : CNF) (a : Assignment)
    (ha : evalCNF a φ = true) : evalCNF a (eliminate v φ) = true := by
  rw [evalCNF_iff] at ha ⊢
  intro c hc
  simp only [eliminate, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with hc | ⟨c₁, hc₁, d, hd, rfl⟩
  · exact ha c (List.mem_filter.mp hc).1
  · have hc₁' := List.mem_filter.mp hc₁
    have hd' := List.mem_filter.mp hd
    simp only [isPos, isNeg, Bool.and_eq_true, Bool.not_eq_true'] at hc₁' hd'
    rw [resolvent, evalClause_append, Bool.or_eq_true]
    cases hav : a v with
    | true =>
      -- `d` is satisfied by a literal not on `v`
      right
      obtain ⟨l, hl, hle⟩ := (evalClause_iff a d).mp (ha d hd'.1)
      refine (evalClause_iff a _).mpr ⟨l, (mem_strip v d l).mpr ⟨hl, ?_⟩, hle⟩
      intro hlv
      have e := lit_of_var l v hlv
      cases hp : l.pos with
      | true =>
        rw [hp] at e; rw [e] at hl
        rw [(hasLit_iff v true d).mpr hl] at hd'; exact Bool.noConfusion hd'.2.2
      | false =>
        simp only [evalLit, hp, hlv, hav] at hle; exact Bool.noConfusion hle
    | false =>
      left
      obtain ⟨l, hl, hle⟩ := (evalClause_iff a c₁).mp (ha c₁ hc₁'.1)
      refine (evalClause_iff a _).mpr ⟨l, (mem_strip v c₁ l).mpr ⟨hl, ?_⟩, hle⟩
      intro hlv
      have e := lit_of_var l v hlv
      cases hp : l.pos with
      | false =>
        rw [hp] at e; rw [e] at hl
        rw [(hasLit_iff v false c₁).mpr hl] at hc₁'; exact Bool.noConfusion hc₁'.2.2
      | true =>
        simp only [evalLit, hp, hlv, hav] at hle; exact Bool.noConfusion hle

/-- The value chosen for `v` when lifting a model of `eliminate v φ`:
`false` if every positive clause is already satisfied without `v`,
`true` otherwise. -/
def chooseVal (v : Nat) (φ : CNF) (b : Assignment) : Bool :=
  !((posClauses v φ).all (fun c => evalClause b (strip v c)))

def update (b : Assignment) (v : Nat) (val : Bool) : Assignment :=
  fun w => if w = v then val else b w

theorem update_strip (b : Assignment) (v : Nat) (val : Bool) (c : Clause) :
    evalClause (update b v val) (strip v c) = evalClause b (strip v c) := by
  apply evalClause_congr
  intro w hw
  simp only [clauseVars, List.mem_map] at hw
  obtain ⟨l, hl, rfl⟩ := hw
  have : l.var ≠ v := ((mem_strip v c l).mp hl).2
  simp [update, this]

theorem update_nomention (b : Assignment) (v : Nat) (val : Bool) (c : Clause)
    (h : mentions v c = false) : evalClause (update b v val) c = evalClause b c := by
  apply evalClause_congr
  intro w hw
  simp only [clauseVars, List.mem_map] at hw
  obtain ⟨l, hl, rfl⟩ := hw
  have : l.var ≠ v := by
    intro e
    have : mentions v c = true := (mentions_iff v c).mpr ⟨l, hl, e⟩
    rw [h] at this; exact Bool.noConfusion this
  simp [update, this]

theorem sat_of_strip (a : Assignment) (v : Nat) (c : Clause)
    (h : evalClause a (strip v c) = true) : evalClause a c = true := by
  obtain ⟨l, hl, hle⟩ := (evalClause_iff a _).mp h
  exact (evalClause_iff a c).mpr ⟨l, ((mem_strip v c l).mp hl).1, hle⟩

theorem sat_of_lit (b : Assignment) (v : Nat) (val : Bool) (c : Clause)
    (h : hasLit v val c = true) : evalClause (update b v val) c = true := by
  refine (evalClause_iff _ c).mpr ⟨⟨v, val⟩, (hasLit_iff v val c).mp h, ?_⟩
  cases val <;> simp [evalLit, update]

/-- Completeness direction: a model of `eliminate v φ` extends (by choosing
`v`) to a model of `φ`. -/
theorem eliminate_complete (v : Nat) (φ : CNF) (b : Assignment)
    (hb : evalCNF b (eliminate v φ) = true) :
    evalCNF (update b v (chooseVal v φ b)) φ = true := by
  rw [evalCNF_iff] at hb ⊢
  intro c hc
  cases hm : mentions v c with
  | false =>
    rw [update_nomention b v _ c hm]
    apply hb
    simp only [eliminate, List.mem_append]
    left
    simp [restClauses, List.mem_filter, hc, hm]
  | true =>
    cases hp : hasLit v true c <;> cases hn : hasLit v false c
    · rcases mentions_cases v c hm with h | h
      · rw [hp] at h; exact Bool.noConfusion h
      · rw [hn] at h; exact Bool.noConfusion h
    · -- negative clause
      cases hval : chooseVal v φ b with
      | false => exact sat_of_lit b v false c hn
      | true =>
        simp only [chooseVal, Bool.not_eq_true', List.all_eq_false] at hval
        obtain ⟨c₀, hc₀, hc₀f⟩ := hval
        have hres : evalClause b (resolvent v c₀ c) = true := by
          apply hb
          simp only [eliminate, List.mem_append, List.mem_flatMap, List.mem_map]
          right
          refine ⟨c₀, hc₀, c, ?_, rfl⟩
          simp [negClauses, List.mem_filter, isNeg, hc, hn, hp]
        rw [resolvent, evalClause_append, Bool.or_eq_true] at hres
        rcases hres with h | h
        · simp only [Bool.not_eq_true] at hc₀f; rw [hc₀f] at h; exact Bool.noConfusion h
        · apply sat_of_strip _ v c
          rw [update_strip]; exact h
    · -- positive clause
      cases hval : chooseVal v φ b with
      | true => exact sat_of_lit b v true c hp
      | false =>
        simp only [chooseVal, Bool.not_eq_false', List.all_eq_true] at hval
        have hpos : c ∈ posClauses v φ := by
          simp [posClauses, List.mem_filter, isPos, hc, hn, hp]
        apply sat_of_strip _ v c
        rw [update_strip]; exact hval c hpos
    · -- tautological in `v`
      cases hval : chooseVal v φ b with
      | true => exact sat_of_lit b v true c hp
      | false => exact sat_of_lit b v false c hn

/-- **Davis–Putnam theorem.** For every CNF `φ` and variable `v`,
`φ` is satisfiable iff `eliminate v φ` is satisfiable. -/
theorem eliminate_sat_iff (v : Nat) (φ : CNF) :
    Satisfiable φ ↔ Satisfiable (eliminate v φ) := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, eliminate_sound v φ a ha⟩
  · rintro ⟨b, hb⟩; exact ⟨_, eliminate_complete v φ b hb⟩

/-! ## Multiplicative blow-up -/

/-- Positive side clauses `x₀ ∨ x_{i+1}` for `i < p`. -/
def posSide (p : Nat) : CNF := (List.range p).map (fun i => [⟨0, true⟩, ⟨i + 1, true⟩])

/-- Negative side clauses `¬x₀ ∨ x_{p+1+j}` for `j < q`. -/
def negSide (p q : Nat) : CNF :=
  (List.range q).map (fun j => [⟨0, false⟩, ⟨p + 1 + j, true⟩])

/-- The blow-up formula: `p + q` clauses of width 2 over `p + q + 1` variables. -/
def blowup (p q : Nat) : CNF := posSide p ++ negSide p q

theorem blowup_clauses (p q : Nat) : (blowup p q).length = p + q := by
  simp [blowup, posSide, negSide]

theorem posClauses_blowup (p q : Nat) : posClauses 0 (blowup p q) = posSide p := by
  simp only [posClauses, blowup, List.filter_append]
  have h1 : (posSide p).filter (isPos 0) = posSide p := by
    rw [List.filter_eq_self]
    intro c hc
    simp only [posSide, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc
    simp [isPos, hasLit]
  have h2 : (negSide p q).filter (isPos 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp only [negSide, List.mem_map, List.mem_range] at hc
    obtain ⟨j, _, rfl⟩ := hc
    simp [isPos, hasLit]
  rw [h1, h2, List.append_nil]

theorem negClauses_blowup (p q : Nat) : negClauses 0 (blowup p q) = negSide p q := by
  simp only [negClauses, blowup, List.filter_append]
  have h1 : (posSide p).filter (isNeg 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    simp only [posSide, List.mem_map, List.mem_range] at hc
    obtain ⟨i, _, rfl⟩ := hc
    simp [isNeg, hasLit]
  have h2 : (negSide p q).filter (isNeg 0) = negSide p q := by
    rw [List.filter_eq_self]
    intro c hc
    simp only [negSide, List.mem_map, List.mem_range] at hc
    obtain ⟨j, _, rfl⟩ := hc
    simp [isNeg, hasLit]
  rw [h1, h2, List.nil_append]

theorem restClauses_blowup (p q : Nat) : restClauses 0 (blowup p q) = [] := by
  rw [restClauses, List.filter_eq_nil_iff]
  intro c hc
  simp only [blowup, posSide, negSide, List.mem_append, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ <;> simp [mentions]

/-- **Blow-up.** Eliminating `x₀` from `blowup p q` (with `p + q` clauses)
produces exactly `p · q` clauses. -/
theorem blowup_length (p q : Nat) : (eliminate 0 (blowup p q)).length = p * q := by
  rw [eliminate_length, posClauses_blowup, negClauses_blowup, restClauses_blowup]
  simp [posSide, negSide]

/-- Each resolvent is the width-2 clause `x_{i+1} ∨ x_{p+1+j}`; these are the
`p · q` pairwise different clauses of the eliminated formula. -/
theorem blowup_resolvent (p i j : Nat) :
    resolvent 0 [⟨0, true⟩, ⟨i + 1, true⟩] [⟨0, false⟩, ⟨p + 1 + j, true⟩] =
      [⟨i + 1, true⟩, ⟨p + 1 + j, true⟩] := by
  simp [resolvent, strip]

end Issue532.Idea27
