import proofs.experiments.issue624.lean.LocalCNF

/-! Compile the shared finite machine's instruction dispatch into local CNF.
The construction enumerates state/symbol pairs, never whole configurations or
certificates. It includes missing columns and proves the actual unary size.
Tape movement and complete accepting tableaux are separate obligations. -/
namespace Issue624.MachineCNF
open Complexity Issue532.Machines Issue624.LocalCNF

def Selected (a : Assignment) (base size value : Nat) : Prop :=
  value < size ∧ a (base + value) = true ∧
    ∀ i, i < size → a (base + i) = true → i = value

theorem oneHot_selected (a : Assignment) (base size : Nat) :
    evalCNF a (oneHot base size) = true ↔ ∃ v, Selected a base size v :=
  oneHot_models a base size

def lookupRules (first second output rows columns : Nat) (f : Nat → Nat → Nat) : CNF :=
  (List.range rows).flatMap fun i => (List.range columns).map fun j =>
    implies [⟨first + i, true⟩, ⟨second + j, true⟩] [⟨output + f i j, true⟩]

theorem lookupRules_models (a : Assignment) (first second output rows columns : Nat)
    (f : Nat → Nat → Nat) :
    evalCNF a (lookupRules first second output rows columns f) = true ↔
      ∀ i, i < rows → ∀ j, j < columns →
        a (first + i) = true → a (second + j) = true → a (output + f i j) = true := by
  simp [lookupRules, evalCNF_flatMap, evalCNF_map, implies_models,
    evalLit, evalClause]

theorem lookupRules_selected (a : Assignment) (first second output rows columns i j : Nat)
    (f : Nat → Nat → Nat) (hi : Selected a first rows i) (hj : Selected a second columns j) :
    evalCNF a (lookupRules first second output rows columns f) = true ↔
      a (output + f i j) = true := by
  rw [lookupRules_models]
  constructor
  · intro h; exact h i hi.1 j hj.1 hi.2.1 hj.2.1
  · intro h u hu v hv hau hav
    rw [hi.2.2 u hu hau, hj.2.2 v hv hav]
    exact h

theorem lookupRules_length (first second output rows columns : Nat) (f : Nat → Nat → Nat) :
    (lookupRules first second output rows columns f).length = rows * columns := by
  have h (xs : List Nat) : (xs.map (fun _ => columns)).sum = xs.length * columns := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa [lookupRules, List.length_flatMap] using h (List.range rows)

theorem lookupRules_bounds (first second output rows columns limit : Nat)
    (f : Nat → Nat → Nat) (hfirst : first + rows ≤ limit)
    (hsecond : second + columns ≤ limit)
    (hout : ∀ i, i < rows → ∀ j, j < columns → output + f i j < limit) :
    VarsBelow limit (lookupRules first second output rows columns f) ∧
      ∀ c ∈ lookupRules first second output rows columns f, c.length ≤ 3 := by
  have hc : ∀ c ∈ lookupRules first second output rows columns f,
      ∃ i, i < rows ∧ ∃ j, j < columns ∧
        c = implies [⟨first + i, true⟩, ⟨second + j, true⟩] [⟨output + f i j, true⟩] := by
    intro c h
    simp only [lookupRules, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨i, hi, j, hj, he⟩ := h
    exact ⟨i, hi, j, hj, he.symm⟩
  constructor
  · intro c h l hl
    obtain ⟨i, hi, j, hj, rfl⟩ := hc c h
    simp only [implies, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · simp only [negate]; omega
    · simp only [negate]; omega
    · exact hout i hi j hj
  · intro c h
    obtain ⟨i, hi, j, hj, rfl⟩ := hc c h
    simp [implies]

def symbols : List Symbol := [.blank, .zero, .one, .separator]
def symbolOfIndex : Nat → Symbol
  | 0 => .blank | 1 => .zero | 2 => .one | _ => .separator
def directionCode : Direction → Nat
  | .left => 0 | .right => 1 | .stay => 2
def instructionCode : Instruction → Nat
  | .halt false => 0 | .halt true => 1
  | .move q w d => 2 + 12 * q + 3 * w.index + directionCode d

theorem instructionCode_injective (i j : Instruction)
    (h : instructionCode i = instructionCode j) : i = j := by
  cases i with
  | halt b =>
    cases j with
    | halt c => cases b <;> cases c <;> simp_all [instructionCode]
    | move q w d => cases b <;> cases w <;> cases d <;>
        simp [instructionCode, Symbol.index, directionCode] at h <;> omega
  | move q w d =>
    cases j with
    | halt b => cases b <;> cases w <;> cases d <;>
        simp [instructionCode, Symbol.index, directionCode] at h <;> omega
    | move q' w' d' =>
      cases w <;> cases w' <;> cases d <;> cases d' <;>
        simp_all [instructionCode, Symbol.index, directionCode] <;> omega

@[simp] theorem symbolOfIndex_index (s : Symbol) : symbolOfIndex s.index = s := by
  cases s <;> rfl
theorem symbolIndex_lt (s : Symbol) : s.index < 4 := by cases s <;> decide
theorem symbolIndex_of_lt (i : Nat) (h : i < 4) : (symbolOfIndex i).index = i := by
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | _ + 4 => omega

def instructionCodes (m : Machine) : List Nat :=
  (List.range m.program.length).flatMap fun q =>
    symbols.map fun s => instructionCode (m.instruction q s)
def instructionBound (m : Machine) : Nat :=
  (instructionCodes m).foldr Nat.max 0 + 1

private theorem le_foldMax (xs : List Nat) (n : Nat) (h : n ∈ xs) :
    n ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem instructionCode_lt_bound (m : Machine) (q : Nat) (s : Symbol)
    (hq : q < m.program.length) : instructionCode (m.instruction q s) < instructionBound m := by
  have hs : s ∈ symbols := by cases s <;> simp [symbols]
  have hmem : instructionCode (m.instruction q s) ∈ instructionCodes m := by
    simp only [instructionCodes, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨q, hq, s, hs, rfl⟩
  have := le_foldMax _ _ hmem
  unfold instructionBound
  omega

def dispatchCNF (m : Machine) (base : Nat) : CNF :=
  let states := m.program.length
  let out := base + states + 4
  oneHot base states ++ oneHot (base + states) 4 ++
    oneHot out (instructionBound m) ++
    lookupRules base (base + states) out states 4
      (fun q s => instructionCode (m.instruction q (symbolOfIndex s)))

/-- Each model selects exactly the instruction of the existing shared table.
Default rejection for ragged rows is inherited from `Machine.instruction`. -/
theorem dispatchCNF_models (m : Machine) (base : Nat) (a : Assignment) :
    evalCNF a (dispatchCNF m base) = true ↔
      ∃ q s, Selected a base m.program.length q ∧
        Selected a (base + m.program.length) 4 s.index ∧
        Selected a (base + m.program.length + 4) (instructionBound m)
          (instructionCode (m.instruction q s)) := by
  simp only [dispatchCNF, evalCNF_append, Bool.and_eq_true, oneHot_selected]
  constructor
  · rintro ⟨⟨⟨⟨q, hq⟩, ⟨s, hs⟩⟩, ⟨v, hv⟩⟩, hr⟩
    have hout := (lookupRules_selected a _ _ _ _ _ q s _ hq hs).mp hr
    have hbound := instructionCode_lt_bound m q (symbolOfIndex s) hq.1
    have he := hv.2.2 _ hbound hout
    refine ⟨q, symbolOfIndex s, hq, ?_, ?_⟩
    · simpa [symbolIndex_of_lt s hs.1] using hs
    · rw [he]; exact hv
  · rintro ⟨q, s, hq, hs, ho⟩
    refine ⟨⟨⟨⟨q, hq⟩, ⟨s.index, hs⟩⟩, ⟨_, ho⟩⟩, ?_⟩
    apply (lookupRules_selected a _ _ _ _ _ q s.index _ hq hs).mpr
    simpa using ho.2.1

def dispatchAssignment (m : Machine) (base q : Nat) (s : Symbol) : Assignment :=
  fun v => v == base + q || v == base + m.program.length + s.index ||
    v == base + m.program.length + 4 + instructionCode (m.instruction q s)

theorem dispatchCNF_wrong_instruction (m : Machine) (base : Nat) (a : Assignment)
    (q value : Nat) (s : Symbol) (hq : Selected a base m.program.length q)
    (hs : Selected a (base + m.program.length) 4 s.index)
    (ho : Selected a (base + m.program.length + 4) (instructionBound m) value)
    (hwrong : instructionCode (m.instruction q s) ≠ value) :
    evalCNF a (dispatchCNF m base) = false := by
  cases he : evalCNF a (dispatchCNF m base) with
  | false => rfl
  | true =>
    simp only [dispatchCNF, evalCNF_append, Bool.and_eq_true] at he
    have hout := (lookupRules_selected a _ _ _ _ _ q s.index _ hq hs).mp he.2
    rw [symbolOfIndex_index] at hout
    exact False.elim (hwrong (ho.2.2 _ (instructionCode_lt_bound m q s hq.1) hout))

theorem dispatchAssignment_models (m : Machine) (base q : Nat) (s : Symbol)
    (hq : q < m.program.length) :
    evalCNF (dispatchAssignment m base q s) (dispatchCNF m base) = true := by
  have hs := symbolIndex_lt s
  have ho := instructionCode_lt_bound m q s hq
  apply (dispatchCNF_models m base _).mpr
  refine ⟨q, s, ⟨hq, ?_, ?_⟩, ⟨hs, ?_, ?_⟩, ⟨ho, ?_, ?_⟩⟩
  all_goals simp only [dispatchAssignment, Bool.or_eq_true, beq_iff_eq]
  · exact Or.inl (Or.inl trivial)
  · intro i hi h; rcases h with (h | h) | h <;> omega
  · exact Or.inl (Or.inr trivial)
  · intro i hi h; rcases h with (h | h) | h <;> omega
  · exact Or.inr trivial
  · intro i hi h; rcases h with (h | h) | h <;> omega

theorem dispatchCNF_instruction (m : Machine) (base : Nat) (a : Assignment)
    (q : Nat) (s : Symbol) (i : Instruction)
    (hq : Selected a base m.program.length q)
    (hs : Selected a (base + m.program.length) 4 s.index)
    (ho : Selected a (base + m.program.length + 4) (instructionBound m) (instructionCode i))
    (hmodel : evalCNF a (dispatchCNF m base) = true) : m.instruction q s = i := by
  simp only [dispatchCNF, evalCNF_append, Bool.and_eq_true] at hmodel
  have hout := (lookupRules_selected a _ _ _ _ _ q s.index _ hq hs).mp hmodel.2
  rw [symbolOfIndex_index] at hout
  exact instructionCode_injective _ _ (ho.2.2 _ (instructionCode_lt_bound m q s hq.1) hout)

/-- Dispatch agrees with the single charged shared step on the full config;
the tape update here remains the existing `moveHead`, not new semantics. -/
theorem dispatchCNF_step (m : Machine) (base : Nat) (a : Assignment)
    (c : Config) (i : Instruction)
    (hq : Selected a base m.program.length c.state)
    (hs : Selected a (base + m.program.length) 4 c.head.index)
    (ho : Selected a (base + m.program.length + 4) (instructionBound m) (instructionCode i))
    (hmodel : evalCNF a (dispatchCNF m base) = true) :
    step m c = match i with
      | .halt b => .inl b
      | .move q w d => .inr (moveHead c q w d) := by
  unfold step
  rw [dispatchCNF_instruction m base a c.state c.head i hq hs ho hmodel]
  cases i <;> rfl

theorem dispatchCNF_empty_unsatisfiable (base : Nat) :
    ¬ Satisfiable (dispatchCNF ⟨[]⟩ base) := by
  rintro ⟨a, ha⟩
  obtain ⟨q, s, hq, _⟩ := (dispatchCNF_models _ _ _).mp ha
  exact Nat.not_lt_zero q hq.1

/-- The identifiers in all three one-hot blocks contribute to the cost. -/
theorem dispatchCNF_encoded_size (m : Machine) (base : Nat) :
    (encodeCNF (dispatchCNF m base)).length ≤
      2 * (m.program.length * m.program.length + 4 * m.program.length +
        (instructionBound m) * (instructionBound m) + 19) *
        (1 + (m.program.length + instructionBound m + 7) *
          (base + m.program.length + instructionBound m + 5)) := by
  let q := m.program.length
  let k := instructionBound m
  let limit := base + q + 4 + k
  let width := q + k + 7
  have h1 := oneHot_bounds base q
  have h2 := oneHot_bounds (base + q) 4
  have h3 := oneHot_bounds (base + q + 4) k
  have h4 := lookupRules_bounds base (base + q) (base + q + 4) q 4 limit
    (fun i j => instructionCode (m.instruction i (symbolOfIndex j))) (by dsimp [limit]; omega)
    (by dsimp [limit]; omega) (by
      intro i hi j _
      have h := instructionCode_lt_bound m i (symbolOfIndex j) hi
      dsimp [limit, k]
      omega)
  have hv : VarsBelow limit (dispatchCNF m base) := by
    intro c hc l hl
    simp only [dispatchCNF, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have := h1.1 c hc l hl; dsimp [limit]; omega
    · have := h2.1 c hc l hl; dsimp [limit]; omega
    · exact h3.1 c hc l hl
    · exact h4.1 c hc l hl
  have hw : ∀ c ∈ dispatchCNF m base, c.length ≤ width := by
    intro c hc
    simp only [dispatchCNF, List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have := h1.2 c hc; dsimp [width]; omega
    · have := h2.2 c hc; dsimp [width]; omega
    · have := h3.2 c hc; dsimp [width]; omega
    · have := h4.2 c hc; dsimp [width]; omega
  have hl : (dispatchCNF m base).length ≤ q * q + 4 * q + k * k + 19 := by
    have ha := oneHot_length base q
    have hb := oneHot_length (base + q) 4
    have hc := oneHot_length (base + q + 4) k
    simp only [dispatchCNF, List.length_append, lookupRules_length]
    change (oneHot base q).length + (oneHot (base + q) 4).length +
      (oneHot (base + q + 4) k).length + q * 4 ≤ _
    omega
  have h := Nat.le_trans (cnf_encoded_size _ limit width hv hw)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hl))
  have he : limit + 1 = base + q + k + 5 := by dsimp [limit]; omega
  rw [he] at h
  exact h

def dispatchPolynomial (m : Machine) (p : Polynomial) : Polynomial :=
  let q := m.program.length
  let k := instructionBound m
  let count := q * q + 4 * q + k * k + 19
  ⟨2 * count * (1 + (q + k + 7) * (p.coefficient + q + k + 5)), p.degree⟩

theorem dispatchCNF_polynomial_size (m : Machine) (p : Polynomial) (n base : Nat)
    (hb : base ≤ p.eval n) :
    (encodeCNF (dispatchCNF m base)).length ≤ (dispatchPolynomial m p).eval n := by
  let q := m.program.length
  let k := instructionBound m
  have hp : 1 ≤ (n + 1) ^ p.degree := Nat.one_le_pow _ _ (by omega)
  have hbase : base + q + k + 5 ≤ (p.coefficient + q + k + 5) * (n + 1) ^ p.degree := by
    have hmul := Nat.mul_le_mul_left (q + k + 5) hp
    simp only [Polynomial.eval, Nat.add_mul, Nat.mul_one] at *
    omega
  have hwidth := Nat.mul_le_mul_left (q + k + 7) hbase
  have hcost : 1 + (q + k + 7) * (base + q + k + 5) ≤
      (1 + (q + k + 7) * (p.coefficient + q + k + 5)) * (n + 1) ^ p.degree := by
    simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] using Nat.add_le_add hp hwidth
  exact Nat.le_trans (dispatchCNF_encoded_size m base)
    (by simpa [dispatchPolynomial, Polynomial.eval, q, k, Nat.mul_assoc] using
      Nat.mul_le_mul_left (2 * (q * q + 4 * q + k * k + 19)) hcost)

end Issue624.MachineCNF
