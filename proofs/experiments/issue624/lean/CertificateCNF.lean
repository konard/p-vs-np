import proofs.experiments.issue532.lean.Machines

/-!
The variable-length certificate part of a Cook--Levin tableau. Cell `i` uses
variable `2*i` for presence and `2*i+1` for its bit. Absent cells have bit
false; absence is suffix-closed. A forced absent cell at the bound prevents
overlong certificates, including when the bound is zero.

This module encodes certificates, not transitions or acceptance. It does not
provide `tableauCNF`, a reduction machine, or SAT hardness.
-/

namespace Issue624.CertificateCNF

open Complexity Issue532.Machines

/-- Two clauses per cell and a negative unit clause for the blank sentinel. -/
def certificateCNF (start : Nat) : Nat → CNF
  | 0 => [[⟨2 * start, false⟩]]
  | n + 1 =>
    [⟨2 * start + 1, false⟩, ⟨2 * start, true⟩] ::
    [⟨2 * (start + 1), false⟩, ⟨2 * start, true⟩] ::
    certificateCNF (start + 1) n

/-- Representation includes all unused cells and the sentinel. -/
def Represents (a : Assignment) (start : Nat) : Word → Nat → Prop
  | [], 0 => a (2 * start) = false
  | _ :: _, 0 => False
  | [], n + 1 => a (2 * start) = false ∧ a (2 * start + 1) = false ∧
      Represents a (start + 1) [] n
  | b :: cert, n + 1 => a (2 * start) = true ∧ a (2 * start + 1) = b ∧
      Represents a (start + 1) cert n

/-- Stop at the first blank, with a finite bound on all reads. -/
def decodeCertificate (a : Assignment) (start : Nat) : Nat → Word
  | 0 => []
  | n + 1 => if a (2 * start) then
      a (2 * start + 1) :: decodeCertificate a (start + 1) n else []

/-- Every certificate has a canonical assignment, with blanks thereafter. -/
def encodeCertificate : Word → Assignment
  | [], _ => false
  | _ :: _, 0 => true
  | b :: _, 1 => b
  | _ :: cert, v + 2 => encodeCertificate cert v

theorem decodeCertificate_length (a : Assignment) (start bound : Nat) :
    (decodeCertificate a start bound).length ≤ bound := by
  induction bound generalizing start with
  | zero => simp [decodeCertificate]
  | succ n ih =>
    simp only [decodeCertificate]
    split
    · simp only [List.length_cons]; have := ih (start + 1); omega
    · simp

theorem represents_length {a : Assignment} {start bound : Nat} {cert : Word}
    (h : Represents a start cert bound) : cert.length ≤ bound := by
  induction bound generalizing start cert with
  | zero => cases cert <;> simp_all [Represents]
  | succ n ih =>
    cases cert with
    | nil => simp
    | cons b cert => have := ih h.2.2; simp only [List.length_cons]; omega

theorem represents_decode {a : Assignment} {start bound : Nat} {cert : Word}
    (h : Represents a start cert bound) : decodeCertificate a start bound = cert := by
  induction bound generalizing start cert with
  | zero => cases cert <;> simp_all [Represents, decodeCertificate]
  | succ n ih =>
    cases cert with
    | nil => simp [decodeCertificate, h.1]
    | cons b cert => simp [decodeCertificate, h.1, h.2.1, ih h.2.2]

private theorem represents_present {a : Assignment} {start bound : Nat} {cert : Word}
    (h : Represents a start cert bound) : a (2 * start) = !cert.isEmpty := by
  cases bound <;> cases cert <;> simp_all [Represents]

private theorem blank_of_model (a : Assignment) : ∀ start bound,
    evalCNF a (certificateCNF start bound) = true → a (2 * start) = false →
      Represents a start [] bound := by
  intro start bound
  induction bound generalizing start with
  | zero => intro _ hp; exact hp
  | succ n ih =>
    intro h hp
    simp only [certificateCNF, evalCNF, Bool.and_eq_true] at h
    have hb : a (2 * start + 1) = false := by
      simpa [evalClause, evalLit, hp] using h.1
    have hn : a (2 * (start + 1)) = false := by
      simpa [evalClause, evalLit, hp] using h.2.1
    exact ⟨hp, hb, ih (start + 1) h.2.2 hn⟩

/-- Every satisfying assignment denotes one bounded certificate, with no
holes or noncanonical unused cells. This is a model-by-model statement. -/
theorem certificateCNF_models (a : Assignment) (start bound : Nat) :
    evalCNF a (certificateCNF start bound) = true ↔
      Represents a start (decodeCertificate a start bound) bound := by
  induction bound generalizing start with
  | zero => simp [certificateCNF, evalCNF, evalClause, evalLit, Represents,
      decodeCertificate]
  | succ n ih =>
    constructor
    · intro h
      cases hp : a (2 * start) with
      | false =>
        simpa [decodeCertificate, hp] using blank_of_model a start (n + 1) h hp
      | true =>
        have ht : evalCNF a (certificateCNF (start + 1) n) = true := by
          simpa [certificateCNF, evalCNF, evalClause, evalLit, hp] using h
        simp only [decodeCertificate, hp, ↓reduceIte, Represents]
        exact ⟨True.intro, True.intro, (ih (start + 1)).mp ht⟩
    · intro h
      cases hp : a (2 * start) with
      | false =>
        simp only [decodeCertificate, hp, Bool.false_eq_true, ↓reduceIte, Represents] at h
        have hn := represents_present h.2.2
        simp only [List.isEmpty_nil, Bool.not_true] at hn
        have ht := (ih (start + 1)).mpr (by
          rw [represents_decode h.2.2]; exact h.2.2)
        simp [certificateCNF, evalCNF, evalClause, evalLit, hp, h.2.1, hn, ht]
      | true =>
        simp only [decodeCertificate, hp, ↓reduceIte, Represents] at h
        have ht := (ih (start + 1)).mpr h.2.2
        simp [certificateCNF, evalCNF, evalClause, evalLit, hp, ht]

private theorem represents_shift (a : Assignment) (off : Nat) (cert : Word) (bound : Nat) :
    ∀ start, Represents (fun v => a (v + 2 * off)) start cert bound ↔
      Represents a (start + off) cert bound := by
  induction bound generalizing cert with
  | zero => intro start; cases cert <;> simp [Represents, Nat.mul_add]
  | succ n ih =>
    intro start
    have he : 2 * start + 1 + 2 * off = 2 * (start + off) + 1 := by omega
    have hn : start + 1 + off = start + off + 1 := by omega
    cases cert <;> simp [Represents, Nat.mul_add, he, ih, hn]

private theorem encodeCertificate_represents (cert : Word) (bound : Nat)
    (h : cert.length ≤ bound) : Represents (encodeCertificate cert) 0 cert bound := by
  induction bound generalizing cert with
  | zero =>
    have : cert = [] := by simpa using h
    subst cert
    rfl
  | succ n ih =>
    cases cert with
    | nil =>
      refine ⟨rfl, rfl, ?_⟩
      exact (represents_shift (encodeCertificate []) 1 [] n 0).mp (ih [] (by simp))
    | cons b cert =>
      refine ⟨rfl, rfl, ?_⟩
      have ht := ih cert (by simpa using h)
      apply (represents_shift (encodeCertificate (b :: cert)) 1 cert n 0).mp
      exact ht

/-- Every certificate within the bound is represented, including the empty
one; no padding is passed to the verifier as certificate bits. -/
theorem encodeCertificate_models (cert : Word) (bound : Nat) (h : cert.length ≤ bound) :
    evalCNF (encodeCertificate cert) (certificateCNF 0 bound) = true := by
  have hr := encodeCertificate_represents cert bound h
  apply (certificateCNF_models _ _ _).mpr
  rw [represents_decode hr]
  exact hr

theorem decode_encodeCertificate (cert : Word) (bound : Nat) (h : cert.length ≤ bound) :
    decodeCertificate (encodeCertificate cert) 0 bound = cert :=
  represents_decode (encodeCertificate_represents cert bound h)

theorem certificateCNF_variables (start bound : Nat) :
    VarsBelow (2 * (start + bound) + 1) (certificateCNF start bound) := by
  induction bound generalizing start with
  | zero =>
    intro c hc l hl
    simp only [certificateCNF, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst l
    simp
  | succ n ih =>
    intro c hc l hl
    simp only [certificateCNF, List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega
    · have := ih (start + 1) c hc l hl
      omega

theorem represents_sentinel {a : Assignment} {start bound : Nat} {cert : Word}
    (h : Represents a start cert bound) : a (2 * (start + bound)) = false := by
  induction bound generalizing start cert with
  | zero => cases cert <;> simp_all [Represents]
  | succ n ih =>
    rw [show start + (n + 1) = start + 1 + n by omega]
    cases cert <;> exact ih h.2.2

private theorem encodeCertificate_present (cert : Word) (i : Nat) (h : i < cert.length) :
    encodeCertificate cert (2 * i) = true := by
  induction cert generalizing i with
  | nil => simp at h
  | cons b cert ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have he : 2 * (i + 1) = 2 * i + 2 := by omega
      rw [he]
      exact ih i (by simp only [List.length_cons] at h; omega)

/-- The sentinel rejects any attempted overlong certificate. -/
theorem overlong_rejected (cert : Word) (bound : Nat) (h : bound < cert.length) :
    evalCNF (encodeCertificate cert) (certificateCNF 0 bound) = false := by
  cases he : evalCNF (encodeCertificate cert) (certificateCNF 0 bound) with
  | false => rfl
  | true =>
    have hs := represents_sentinel ((certificateCNF_models _ _ _).mp he)
    simp only [Nat.zero_add] at hs
    rw [encodeCertificate_present cert bound h] at hs
    cases hs

private theorem ticks_length (n : Nat) : (ticks n).length = 2 * n := by
  induction n <;> simp_all [ticks]; omega

private theorem encodeLit_length (l : Lit) : (encodeLit l).length = 2 * l.var + 2 := by
  simp [encodeLit, ticks_length]

/-- Exact bit length, including unary variable identifiers and delimiters. -/
theorem encode_certificateCNF_length (start bound : Nat) :
    (encodeCNF (certificateCNF start bound)).length =
      8 * bound * bound + 14 * bound + 4 + (16 * bound + 4) * start := by
  induction bound generalizing start with
  | zero => simp [certificateCNF, encodeCNF, encodeClause, encodeLit_length]; omega
  | succ n ih =>
    simp only [certificateCNF, encodeCNF, encodeClause, List.length_append,
      encodeLit_length, List.length_cons, List.length_nil]
    rw [ih]
    simp only [Nat.mul_add, Nat.add_mul]
    omega

/-- Substituting the ClassNP certificate bound gives an explicit polynomial
for this fragment. It is not a size bound for the full machine tableau. -/
def certificatePolynomial (p : Polynomial) : Polynomial :=
  ⟨8 * p.coefficient * p.coefficient + 14 * p.coefficient + 4, 2 * p.degree⟩

theorem certificateCNF_polynomial_size (p : Polynomial) (n : Nat) :
    (encodeCNF (certificateCNF 0 (p.eval n))).length ≤ (certificatePolynomial p).eval n := by
  rw [encode_certificateCNF_length]
  simp only [Nat.mul_zero, Nat.add_zero, certificatePolynomial, Polynomial.eval]
  have hpow : 1 ≤ (n + 1) ^ p.degree := Nat.one_le_pow _ _ (by omega)
  have hsq : (n + 1) ^ (2 * p.degree) = (n + 1) ^ p.degree * (n + 1) ^ p.degree := by
    rw [Nat.mul_comm 2, Nat.pow_mul]; simp [Nat.pow_two]
  rw [hsq]
  have hsmall : (n + 1) ^ p.degree ≤ (n + 1) ^ p.degree * (n + 1) ^ p.degree := by
    simpa using Nat.mul_le_mul_left ((n + 1) ^ p.degree) hpow
  have hone : 1 ≤ (n + 1) ^ p.degree * (n + 1) ^ p.degree :=
    Nat.le_trans hpow hsmall
  calc
    _ ≤ 8 * p.coefficient * p.coefficient * ((n + 1) ^ p.degree * (n + 1) ^ p.degree) +
        14 * p.coefficient * ((n + 1) ^ p.degree * (n + 1) ^ p.degree) +
        4 * ((n + 1) ^ p.degree * (n + 1) ^ p.degree) := by
      have hm := Nat.mul_le_mul_left (14 * p.coefficient) hsmall
      have hc := Nat.mul_le_mul_left 4 hone
      have he : 8 * (p.coefficient * (n + 1) ^ p.degree) *
          (p.coefficient * (n + 1) ^ p.degree) =
          8 * p.coefficient * p.coefficient * ((n + 1) ^ p.degree * (n + 1) ^ p.degree) := by
        ac_rfl
      rw [he]
      simp only [← Nat.mul_assoc] at *
      omega
    _ = _ := by simp [Nat.add_mul]

end Issue624.CertificateCNF
