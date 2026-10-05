import proofs.experiments.issue532.lean.Machines

/-! Finite local constraints, compiled into the repository's actual CNF and
unary literal encoding. These combinators enumerate cells or pairs of values,
not whole configurations, traces, or certificates. -/
namespace Issue624.LocalCNF
open Complexity Issue532.Machines

@[simp] theorem evalCNF_append (a : Assignment) (f g : CNF) :
    evalCNF a (f ++ g) = (evalCNF a f && evalCNF a g) := by
  induction f with
  | nil => simp [evalCNF]
  | cons c f ih => simp [evalCNF, ih, Bool.and_assoc]

@[simp] theorem evalCNF_map {α : Type} (a : Assignment) (cs : List α) (f : α → Clause) :
    evalCNF a (cs.map f) = true ↔ ∀ c ∈ cs, evalClause a (f c) = true := by
  induction cs with
  | nil => simp [evalCNF]
  | cons c cs ih => simp [evalCNF, ih]

@[simp] theorem evalCNF_flatMap {α : Type} (a : Assignment) (cs : List α) (f : α → CNF) :
    evalCNF a (cs.flatMap f) = true ↔ ∀ c ∈ cs, evalCNF a (f c) = true := by
  induction cs with
  | nil => simp [evalCNF]
  | cons c cs ih => simp [ih]

@[simp] theorem evalClause_map {α : Type} (a : Assignment) (cs : List α) (f : α → Lit) :
    evalClause a (cs.map f) = true ↔ ∃ c ∈ cs, evalLit a (f c) = true := by
  induction cs with
  | nil => simp [evalClause]
  | cons c cs ih => simp [evalClause, ih]

def negate (l : Lit) : Lit := ⟨l.var, !l.pos⟩

def implies (premises conclusion : Clause) : Clause :=
  premises.map negate ++ conclusion

@[simp] theorem evalLit_negate (a : Assignment) (l : Lit) :
    evalLit a (negate l) = !evalLit a l := by
  cases l with
  | mk v p => cases p <;> cases h : a v <;> simp [evalLit, negate, h]

/-- One clause expresses a conjunction of premises implying a disjunction.
An empty conclusion forbids the premise; empty premises force the conclusion. -/
theorem implies_models (a : Assignment) (premises conclusion : Clause) :
    evalClause a (implies premises conclusion) = true ↔
      ((∀ l ∈ premises, evalLit a l = true) → evalClause a conclusion = true) := by
  induction premises with
  | nil => simp [implies]
  | cons l ls ih =>
    simp only [implies, List.map_cons, List.cons_append, evalClause, evalLit_negate,
      Bool.or_eq_true, List.mem_cons, forall_eq_or_imp] at *
    cases h : evalLit a l <;> simp_all

def atMostOne (base : Nat) : Nat → CNF
  | 0 => []
  | n + 1 =>
    (List.range n).map (fun i => [⟨base, false⟩, ⟨base + 1 + i, false⟩]) ++
      atMostOne (base + 1) n

def oneHot (base size : Nat) : CNF :=
  [(List.range size).map (fun i => ⟨base + i, true⟩)] ++ atMostOne base size

private theorem atMostOne_models (a : Assignment) (base size : Nat) :
    evalCNF a (atMostOne base size) = true ↔
      ∀ i, i < size → ∀ j, j < size →
        a (base + i) = true → a (base + j) = true → i = j := by
  induction size generalizing base with
  | zero => simp [atMostOne, evalCNF]
  | succ n ih =>
    have hc (u v : Nat) : evalClause a [⟨u, false⟩, ⟨v, false⟩] = true ↔
        (a u = true → a v = false) := by
      cases hu : a u <;> cases hv : a v <;> simp [evalClause, evalLit, hu, hv]
    have hp : evalCNF a (atMostOne base (n + 1)) = true ↔
        (∀ j, j < n → a base = true → a (base + 1 + j) = false) ∧
        ∀ i, i < n → ∀ j, j < n →
          a (base + 1 + i) = true → a (base + 1 + j) = true → i = j := by
      simp only [atMostOne, evalCNF_append, Bool.and_eq_true, evalCNF_map,
        List.mem_range, ih, hc]
    rw [hp]
    constructor
    · rintro ⟨hfirst, hrest⟩ i hi j hj hai haj
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          have hj' : j < n := by omega
          have he := hfirst j hj' (by simpa using hai)
          have hjt : a (base + 1 + j) = true := by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using haj
          rw [hjt] at he
          cases he
      | succ i =>
        cases j with
        | zero =>
          have he := hfirst i (by omega) (by simpa using haj)
          have hit : a (base + 1 + i) = true := by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hai
          rw [hit] at he
          cases he
        | succ j =>
          have he := hrest i (by omega) j (by omega)
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hai)
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using haj)
          omega
    · intro h
      constructor
      · intro j hj hb
        cases ha : a (base + 1 + j) with
        | false => rfl
        | true =>
          have he := h 0 (by omega) (j + 1) (by omega) (by simpa using hb)
            (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ha)
          omega
      · intro i hi j hj hai haj
        have he := h (i + 1) (by omega) (j + 1) (by omega)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hai)
          (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using haj)
        omega

/-- Exactly one bounded value, including rejection when the domain is empty. -/
theorem oneHot_models (a : Assignment) (base size : Nat) :
    evalCNF a (oneHot base size) = true ↔
      ∃ v, v < size ∧ a (base + v) = true ∧
        ∀ w, w < size → a (base + w) = true → w = v := by
  simp only [oneHot, evalCNF_append, evalCNF, Bool.and_true, Bool.and_eq_true,
    evalClause_map, List.mem_range, evalLit, beq_iff_eq, atMostOne_models]
  constructor
  · rintro ⟨⟨v, hv, hav⟩, h⟩
    exact ⟨v, hv, hav, fun w hw haw => h w hw v hv haw hav⟩
  · rintro ⟨v, hv, hav, h⟩
    exact ⟨⟨v, hv, hav⟩, fun i hi j hj hai haj => (h i hi hai).trans (h j hj haj).symm⟩

private theorem ticks_length (n : Nat) : (ticks n).length = 2 * n := by
  induction n <;> simp_all [ticks]; omega

private theorem clause_encoded_size (c : Clause) (bound : Nat)
    (h : ∀ l ∈ c, l.var < bound) :
    (encodeClause c).length ≤ 2 * (1 + c.length * (bound + 1)) := by
  induction c with
  | nil => simp [encodeClause]
  | cons l c ih =>
    have hl := h l (List.mem_cons_self ..)
    have ht := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    simp only [encodeClause, encodeLit, List.length_append, ticks_length,
      List.length_cons, List.length_nil] at *
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega

/-- Actual encoded bit length, accounting for unary indices and delimiters. -/
theorem cnf_encoded_size (f : CNF) (bound width : Nat)
    (hv : VarsBelow bound f) (hw : ∀ c ∈ f, c.length ≤ width) :
    (encodeCNF f).length ≤ 2 * f.length * (1 + width * (bound + 1)) := by
  induction f with
  | nil => simp [encodeCNF]
  | cons c f ih =>
    have hc := clause_encoded_size c bound (hv c (List.mem_cons_self ..))
    have hl := hw c (List.mem_cons_self ..)
    have ht := ih (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc'))
      (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    have hm := Nat.mul_le_mul_right (bound + 1) hl
    simp only [encodeCNF, List.length_append, List.length_cons]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega

private theorem atMostOne_length (base size : Nat) :
    (atMostOne base size).length ≤ size * size := by
  induction size generalizing base with
  | zero => simp [atMostOne]
  | succ n ih =>
    have h := ih (base + 1)
    simp only [atMostOne, List.length_append, List.length_map, List.length_range]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at *
    omega

private theorem atMostOne_bounds (base size : Nat) :
    VarsBelow (base + size) (atMostOne base size) ∧
      ∀ c ∈ atMostOne base size, c.length ≤ 2 := by
  induction size generalizing base with
  | zero => simp [atMostOne, VarsBelow]
  | succ n ih =>
    have h := ih (base + 1)
    constructor
    · intro c hc l hl
      simp only [atMostOne, List.mem_append, List.mem_map, List.mem_range] at hc
      rcases hc with ⟨i, hi, rfl⟩ | hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp only <;> omega
      · have := h.1 c hc l hl; omega
    · intro c hc
      simp only [atMostOne, List.mem_append, List.mem_map, List.mem_range] at hc
      rcases hc with ⟨i, hi, rfl⟩ | hc
      · simp
      · exact h.2 c hc

theorem oneHot_encoded_size (base size : Nat) :
    (encodeCNF (oneHot base size)).length ≤
      2 * (size * size + 1) * (1 + (size + 2) * (base + size + 1)) := by
  have hv : VarsBelow (base + size) (oneHot base size) := by
    intro c hc l hl
    simp only [oneHot, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | hc
    · simp only [List.mem_map, List.mem_range] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      simp only
      omega
    · exact (atMostOne_bounds base size).1 c hc l hl
  have hw : ∀ c ∈ oneHot base size, c.length ≤ size + 2 := by
    intro c hc
    simp only [oneHot, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | hc
    · simp
    · have := (atMostOne_bounds base size).2 c hc; omega
  have hlen : (oneHot base size).length ≤ size * size + 1 := by
    have h := atMostOne_length base size
    simpa [oneHot] using Nat.add_le_add_left h 1
  exact Nat.le_trans (cnf_encoded_size _ _ _ hv hw)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hlen))

end Issue624.LocalCNF
