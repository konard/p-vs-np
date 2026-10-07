import proofs.experiments.issue532.lean.Circuits
import proofs.experiments.issue624.lean.LocalCNF

/-! Tseitin compilation of the existing NAND straight-line programs.
Each gate contributes three clauses. Auxiliary variables are the existing
wire indices, so the unary encoding cost is included in the size theorem. -/
namespace Issue624.CircuitCNF
open Complexity Issue532.Machines Issue532.Circuits Issue624.LocalCNF

/-- These clauses express `o = NAND(i,j)`, including aliased inputs. -/
def gateCNF (o i j : Nat) : CNF :=
  [[⟨o, true⟩, ⟨i, true⟩], [⟨o, true⟩, ⟨j, true⟩],
    [⟨o, false⟩, ⟨i, false⟩, ⟨j, false⟩]]

theorem gateCNF_models (a : Assignment) (o i j : Nat) :
    evalCNF a (gateCNF o i j) = true ↔ a o = !(a i && a j) := by
  cases ho : a o <;> cases hi : a i <;> cases hj : a j <;>
    simp [gateCNF, evalCNF, evalClause, evalLit, ho, hi, hj]

/-- Start the gate-output variables after the input wires. -/
def circuitCNF : Nat → Circuit → CNF
  | _, [] => []
  | n, (i, j) :: C => gateCNF n i j ++ circuitCNF (n + 1) C

def Agrees (a : Assignment) (w : Word) : Prop :=
  ∀ i, i < w.length → a i = wire w i

theorem agrees_prefix (a : Assignment) (w : Word) (C : Circuit)
    (h : Agrees a (wires w C)) : Agrees a w := by
  intro i hi
  rw [← wire_wires_lt w C i hi]
  exact h i (by rw [wires_length]; omega)

theorem agrees_append (a : Assignment) (w : Word) (b : Bool) :
    Agrees a (w ++ [b]) ↔ Agrees a w ∧ a w.length = b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [← wire_append_lt w b i hi]
      exact h i (by simp; omega)
    · simpa [wire_append_self] using h w.length (by simp)
  · rintro ⟨h, hb⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hit : i < w.length
    · rw [wire_append_lt w b i hit]; exact h i hit
    · have : i = w.length := by omega
      subst i
      rw [wire_append_self]; exact hb

/-- Assignment-by-assignment correctness, with arbitrary input values. -/
theorem circuitCNF_models (a : Assignment) (w : Word) (C : Circuit)
    (hw : WF w.length C) (ha : Agrees a w) :
    evalCNF a (circuitCNF w.length C) = true ↔ Agrees a (wires w C) := by
  induction C generalizing w with
  | nil => simp [circuitCNF, wires, evalCNF, ha]
  | cons g C ih =>
    obtain ⟨i, j⟩ := g
    obtain ⟨hi, hj, ht⟩ := hw
    let b := !(wire w i && wire w j)
    have hb : evalCNF a (gateCNF w.length i j) = true ↔ a w.length = b := by
      rw [gateCNF_models, ha i hi, ha j hj]
    have ht' : WF (w ++ [b]).length C := by simpa [WF] using ht
    simp only [circuitCNF, evalCNF_append, Bool.and_eq_true, wires]
    rw [hb]
    constructor
    · rintro ⟨hab, hf⟩
      have he := agrees_append a w b |>.mpr ⟨ha, hab⟩
      exact (ih (w ++ [b]) ht' he).mp (by simpa using hf)
    · intro he
      have hp := agrees_prefix a (w ++ [b]) C he
      have hab := (agrees_append a w b).mp hp |>.2
      exact ⟨hab, by simpa using (ih (w ++ [b]) ht' hp).mpr he⟩

/-- Assert the final output; no wire at all means the constant false circuit. -/
def acceptingCNF (n : Nat) (C : Circuit) : CNF :=
  circuitCNF n C ++ if n + C.length = 0 then [[]] else [[⟨n + C.length - 1, true⟩]]

private theorem lastD_wire (w : Word) : w.getLastD false = wire w (w.length - 1) := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, wire,
    List.getD_eq_getElem?_getD]

private theorem prefix_agrees (a : Assignment) (n : Nat) : Agrees a (prefixOf a n) := by
  intro i hi
  have hi' : i < n := by simpa [length_prefixOf] using hi
  rw [← toAssign_wire]; exact (toAssign_prefixOf a n i hi').symm

private theorem output_of_agrees (a : Assignment) (x : Word) (C : Circuit)
    (ha : Agrees a (wires x C)) (hp : 0 < x.length + C.length) :
    output x C = a (x.length + C.length - 1) := by
  rw [output, lastD_wire, wires_length]
  exact (ha _ (by rw [wires_length]; omega)).symm

/-- CNF satisfiability is exactly satisfiability of the shared circuit.
The empty and zero-input conventions are included, not assumed away. -/
theorem acceptingCNF_iff (n : Nat) (C : Circuit) (hw : WF n C) :
    Satisfiable (acceptingCNF n C) ↔
      ∃ x : Word, x.length = n ∧ output x C = true := by
  constructor
  · rintro ⟨a, ha⟩
    unfold acceptingCNF at ha
    simp only [evalCNF_append, Bool.and_eq_true] at ha
    by_cases hz : n + C.length = 0
    · simp [hz, evalCNF, evalClause] at ha
    · have hn : (prefixOf a n).length = n := length_prefixOf a n
      have hwa : WF (prefixOf a n).length C := by simpa only [hn] using hw
      have he := (circuitCNF_models a _ C hwa (prefix_agrees a n)).mp (by simpa only [hn] using ha.1)
      have ho : a (n + C.length - 1) = true := by
        simp only [hz, ↓reduceIte, evalCNF, evalClause, evalLit, Bool.or_false,
          Bool.and_true, beq_iff_eq] at ha
        exact ha.2
      exact ⟨prefixOf a n, hn, by
        rw [output_of_agrees a _ C he (by omega), hn, ho]⟩
  · rintro ⟨x, hx, ho⟩
    let a : Assignment := toAssign (wires x C)
    have he : Agrees a (wires x C) := fun i _ => toAssign_wire _ i
    have hp := agrees_prefix a x C he
    have hc := (circuitCNF_models a x C (hx ▸ hw) hp).mpr he
    have hz : n + C.length ≠ 0 := by
      intro hz
      have hn : n = 0 := by omega
      have hC : C = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hX : x = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hC hX
      cases ho
    refine ⟨a, ?_⟩
    simp only [acceptingCNF, evalCNF_append, Bool.and_eq_true, hz, ↓reduceIte]
    refine ⟨hx ▸ hc, ?_⟩
    have hab : a (n + C.length - 1) = true := by
      rw [← hx, ← output_of_agrees a x C he (by omega), ho]
    simp [evalCNF, evalClause, evalLit, hab]

private theorem circuitCNF_length (n : Nat) (C : Circuit) :
    (circuitCNF n C).length = 3 * C.length := by
  induction C generalizing n with
  | nil => rfl
  | cons g C ih => cases g; simp [circuitCNF, gateCNF, ih]; omega

private theorem circuitCNF_bounds (n : Nat) (C : Circuit) (hw : WF n C) :
    VarsBelow (n + C.length) (circuitCNF n C) ∧
      ∀ c ∈ circuitCNF n C, c.length ≤ 3 := by
  induction C generalizing n with
  | nil => simp [circuitCNF, VarsBelow]
  | cons g C ih =>
    obtain ⟨i, j⟩ := g
    obtain ⟨hi, hj, ht⟩ := hw
    have hb := ih (n + 1) ht
    constructor
    · intro c hc l hl
      simp only [circuitCNF, List.mem_append] at hc
      rcases hc with hc | hc
      · simp only [gateCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
          rcases hl with rfl | rfl | rfl <;> simp only <;> simp only [List.length_cons] <;> omega
      · have := hb.1 c hc l hl
        simp only [List.length_cons]; omega
    · intro c hc
      simp only [circuitCNF, List.mem_append] at hc
      rcases hc with hc | hc
      · simp only [gateCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp
      · exact hb.2 c hc

/-- Bound the actual unary encoded length, not just the number of gates. -/
theorem acceptingCNF_encoded_size (n : Nat) (C : Circuit) (hw : WF n C) :
    (encodeCNF (acceptingCNF n C)).length ≤
      8 * (3 * C.length + 1) * (n + C.length + 1) := by
  have hb := circuitCNF_bounds n C hw
  have hv : VarsBelow (n + C.length) (acceptingCNF n C) := by
    intro c hc l hl
    simp only [acceptingCNF, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hb.1 c hc l hl
    · split at hc
      · simp at hc; subst c; cases hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hl
        subst c
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst l
        simp only
        omega
  have hw' : ∀ c ∈ acceptingCNF n C, c.length ≤ 3 := by
    intro c hc
    simp only [acceptingCNF, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hb.2 c hc
    · split at hc <;> simp at hc <;> subst c <;> simp
  have hl : (acceptingCNF n C).length = 3 * C.length + 1 := by
    simp only [acceptingCNF, List.length_append, circuitCNF_length]
    split <;> simp
  have h := cnf_encoded_size _ _ 3 hv hw'
  rw [hl] at h
  have ht : 1 + 3 * (n + C.length + 1) ≤ 4 * (n + C.length + 1) := by omega
  exact Nat.le_trans h (by
    calc
      _ ≤ 2 * (3 * C.length + 1) * (4 * (n + C.length + 1)) :=
        Nat.mul_le_mul_left _ ht
      _ = _ := by
        simp only [← Nat.mul_assoc]
        rw [Nat.mul_right_comm 2 _ 4])

/-- Unary wire identifiers square a polynomial bound on the wire count. -/
def circuitPolynomial (p : Polynomial) : Polynomial :=
  ⟨8 * (3 * p.coefficient + 1) * (p.coefficient + 1), 2 * p.degree⟩

theorem acceptingCNF_polynomial_size (p : Polynomial) (inputLength n : Nat)
    (C : Circuit) (hw : WF n C) (hs : n + C.length ≤ p.eval inputLength) :
    (encodeCNF (acceptingCNF n C)).length ≤
      (circuitPolynomial p).eval inputLength := by
  have hz : 1 ≤ (inputLength + 1) ^ p.degree := Nat.one_le_pow _ _ (by omega)
  have hl : 3 * C.length + 1 ≤
      (3 * p.coefficient + 1) * (inputLength + 1) ^ p.degree := by
    simp only [Polynomial.eval, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at *
    omega
  have hr : n + C.length + 1 ≤
      (p.coefficient + 1) * (inputLength + 1) ^ p.degree := by
    simp only [Polynomial.eval, Nat.add_mul, Nat.one_mul] at *
    omega
  calc
    _ ≤ 8 * (3 * C.length + 1) * (n + C.length + 1) :=
      acceptingCNF_encoded_size n C hw
    _ ≤ 8 * ((3 * p.coefficient + 1) * (inputLength + 1) ^ p.degree) *
        ((p.coefficient + 1) * (inputLength + 1) ^ p.degree) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 hl) hr
    _ = _ := by
      simp only [circuitPolynomial, Polynomial.eval, Nat.mul_comm 2 p.degree,
        Nat.pow_mul, Nat.pow_two]
      ac_rfl

end Issue624.CircuitCNF
