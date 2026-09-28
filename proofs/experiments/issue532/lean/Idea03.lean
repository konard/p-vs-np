/-!
# Issue #532, Idea 03 — A verifier for CNF-SAT (the NP side)

This file formalizes the *verifier* half of "SAT ∈ NP" for CNF formulas and
measures its cost.

* `verify φ cert` evaluates `φ` under the assignment given by the bit vector
  `cert`.
* `verify_sound`: an accepted certificate yields a satisfying assignment.
* `verify_complete`: if `φ` is satisfiable and its variables are `< n`, a
  certificate of length exactly `n` is accepted.
* `sat_iff_exists_cert`: `Satisfiable φ ↔ ∃ cert, cert.length = numVars φ ∧
  verify φ cert = true`, the NP characterization of SAT.
* `numVars_le_encodingLength`: the certificate is no longer than the input.
* `verifyRun` evaluates every literal once and counts the evaluations;
  `verifyRun_result` shows it computes `verify`, and `verify_cost_eq` shows the
  count is exactly `size φ` (the number of literal occurrences), whatever the
  certificate.  `verifyRunSC` short-circuits; it also computes `verify`
  (`verifyRunSC_result`) and costs at most `size φ` (`verifyRunSC_cost_le`).
* `size_le_encodingLength`: `2 * size φ ≤ |encodeCNF φ|`, so verification is
  linear in the input length (`verify_cost_le_encoding`).
* `unsat_iff_all_rejected`: unsatisfiability is the *universal* statement
  "every certificate of length `n` is rejected".
* `total_verification_cost`: checking all `2^n` certificates costs exactly
  `2^n * size φ` literal evaluations.

Verdict: correct tool, insufficient alone.  The NP side is easy and fully
proved here (linear-time checking, linear-size certificates, counted in
literal evaluations).  All the difficulty of P vs NP sits in replacing the
quantifier `∃ cert` (or `∀ cert` for unsatisfiability) by a polynomial
computation; that is the obligation `PolySATDecider` of Idea 01.  The cost is
counted in literal evaluations, not in Turing-machine steps; a machine-level
verifier is not formalized here.
-/

namespace Issue532.Idea03

/-! ## CNF syntax and semantics -/

/-- A literal: variable index and polarity (`pos = true` means `x_var`). -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := a l.var == l.pos

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a : Assignment, evalCNF a φ = true

/-- All variables of `φ` are `< n`. -/
def VarsBelow (n : Nat) (φ : CNF) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var < n

theorem evalClause_congr (a b : Assignment) (n : Nat) (c : Clause)
    (hab : ∀ i, i < n → a i = b i) (hc : ∀ l ∈ c, l.var < n) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, evalLit]
    rw [hab l.var (hc l (List.mem_cons_self ..)),
      ih (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))]

/-- Formulas with variables `< n` only look at the first `n` values. -/
theorem evalCNF_congr (a b : Assignment) (n : Nat) (φ : CNF)
    (hab : ∀ i, i < n → a i = b i) (hφ : VarsBelow n φ) :
    evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [evalCNF]
    rw [evalClause_congr a b n c hab (hφ c (List.mem_cons_self ..)),
      ih (fun c' hc' => hφ c' (List.mem_cons_of_mem _ hc'))]

/-! ## Enumerating all assignments -/

/-- All `2^n` bit vectors of length `n` (bit `0` is the head). -/
def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAssignments n).map (false :: ·) ++ (allAssignments n).map (true :: ·)

/-- Bit vector to assignment: index `i` ↦ bit `i`, `false` beyond the end. -/
def toAssign : List Bool → Assignment
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v, i + 1 => toAssign v i

/-- The first `n` values of an assignment, as a bit vector. -/
def prefixOf (a : Assignment) : Nat → List Bool
  | 0 => []
  | n + 1 => a 0 :: prefixOf (fun i => a (i + 1)) n

/-- The enumeration has exactly `2^n` entries. -/
theorem length_allAssignments (n : Nat) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

/-- The enumeration contains exactly the vectors of length `n`. -/
theorem mem_allAssignments_iff (n : Nat) (v : List Bool) :
    v ∈ allAssignments n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v => simp [allAssignments]
  | succ n ih =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v =>
      cases b <;> simp [allAssignments, ih]

theorem nodup_map_cons (b : Bool) (L : List (List Bool)) (h : L.Nodup) :
    (L.map (b :: ·)).Nodup := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy hyx => h.1 ?_, ih h.2⟩
    have : y = x := List.cons.inj hyx |>.2
    exact this ▸ hy

/-- The enumeration has no repetitions: it lists `2^n` *distinct* vectors. -/
theorem nodup_allAssignments (n : Nat) : (allAssignments n).Nodup := by
  induction n with
  | zero => simp [allAssignments]
  | succ n ih =>
    simp only [allAssignments]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons false _ ih, nodup_map_cons true _ ih, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨w, _, rfl⟩ := hy
    exact Bool.noConfusion (List.cons.inj hxy).1

theorem length_prefixOf (a : Assignment) (n : Nat) : (prefixOf a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [prefixOf, ih]

theorem toAssign_prefixOf (a : Assignment) (n i : Nat) (h : i < n) :
    toAssign (prefixOf a n) i = a i := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j + 1)) i (by omega)

/-! ## Number of variables -/

def clauseBound : Clause → Nat
  | [] => 0
  | l :: c => max (l.var + 1) (clauseBound c)

/-- One more than the largest variable index (0 for variable-free formulas). -/
def numVars : CNF → Nat
  | [] => 0
  | c :: φ => max (clauseBound c) (numVars φ)

theorem lt_clauseBound (c : Clause) : ∀ l ∈ c, l.var < clauseBound c := by
  induction c with
  | nil => intro l hl; cases hl
  | cons l c ih =>
    intro l' hl'
    simp only [clauseBound]
    rcases List.mem_cons.mp hl' with h | h
    · subst h; omega
    · have := ih l' h; omega

theorem varsBelow_numVars (φ : CNF) : VarsBelow (numVars φ) φ := by
  induction φ with
  | nil => intro c hc; cases hc
  | cons c φ ih =>
    intro c' hc' l hl
    simp only [numVars]
    rcases List.mem_cons.mp hc' with h | h
    · subst h; have := lt_clauseBound c' l hl; omega
    · have := ih c' h l hl; omega

/-! ## A lossless binary encoding of CNFs

Tokens are bit pairs: `11` = unary tick of the variable index, `0p` = end of
a literal with polarity `p`, `10` = end of clause.  The literal `(v, p)` is
`11^v 0p`; a clause is its literals followed by `10`. -/

def ticks : Nat → List Bool
  | 0 => []
  | k + 1 => true :: true :: ticks k

def encodeLit (l : Lit) : List Bool := ticks l.var ++ [false, l.pos]

def encodeClause : Clause → List Bool
  | [] => [true, false]
  | l :: c => encodeLit l ++ encodeClause c

def encodeCNF : CNF → List Bool
  | [] => []
  | c :: φ => encodeClause c ++ encodeCNF φ

def decodeAux : List Bool → Nat → Clause → CNF
  | true :: true :: rest, k, cur => decodeAux rest (k + 1) cur
  | false :: p :: rest, k, cur => decodeAux rest 0 (cur ++ [⟨k, p⟩])
  | true :: false :: rest, _, cur => cur :: decodeAux rest 0 []
  | _, _, _ => []

def decode (w : List Bool) : CNF := decodeAux w 0 []

theorem decodeAux_ticks (v : Nat) (r : List Bool) (k : Nat) (cur : Clause) :
    decodeAux (ticks v ++ r) k cur = decodeAux r (k + v) cur := by
  induction v generalizing k with
  | zero => rfl
  | succ v ih =>
    simp only [ticks, List.cons_append, decodeAux]
    rw [ih]; congr 1; omega

theorem decodeAux_clause (c : Clause) (r : List Bool) (cur : Clause) :
    decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 [] := by
  induction c generalizing cur with
  | nil => simp [encodeClause, decodeAux]
  | cons l c ih =>
    simp only [encodeClause, encodeLit, List.append_assoc]
    rw [decodeAux_ticks]
    simp only [List.cons_append, List.nil_append, decodeAux, Nat.zero_add]
    rw [ih]; simp

theorem decode_encode (φ : CNF) : decode (encodeCNF φ) = φ := by
  unfold decode
  induction φ with
  | nil => simp [encodeCNF, decodeAux]
  | cons c φ ih =>
    simp only [encodeCNF]
    rw [decodeAux_clause, ih]; rfl

/-- Distinct formulas have distinct encodings. -/
theorem encode_injective (φ ψ : CNF) (h : encodeCNF φ = encodeCNF ψ) : φ = ψ := by
  rw [← decode_encode φ, h, decode_encode]

theorem length_ticks (v : Nat) : (ticks v).length = 2 * v := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [ticks, List.length_cons, ih]; omega

theorem clauseBound_le_length (c : Clause) : clauseBound c ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [clauseBound, encodeClause]
  | cons l c ih =>
    simp only [clauseBound, encodeClause, encodeLit, List.length_append, length_ticks,
      List.length_cons, List.length_nil]
    omega

/-- The number of variables is at most the input length. -/
theorem numVars_le_encodingLength (φ : CNF) : numVars φ ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => exact Nat.le_refl 0
  | cons c φ ih =>
    simp only [numVars, encodeCNF, List.length_append]
    have := clauseBound_le_length c
    omega

/-- The number of literal occurrences in a formula. -/
def size : CNF → Nat
  | [] => 0
  | c :: φ => c.length + size φ

theorem two_size_le_encodeClause (c : Clause) : 2 * c.length ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [encodeClause]
  | cons l c ih =>
    simp only [encodeClause, encodeLit, List.length_append, length_ticks,
      List.length_cons, List.length_nil]
    omega

/-- Every literal occurrence costs at least two input bits. -/
theorem size_le_encodingLength (φ : CNF) : 2 * size φ ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => exact Nat.le_refl 0
  | cons c φ ih =>
    simp only [size, encodeCNF, List.length_append]
    have := two_size_le_encodeClause c
    omega

/-! ## The verifier -/

/-- Check a certificate (bit `i` is the value of variable `i`). -/
def verify (φ : CNF) (cert : List Bool) : Bool := evalCNF (toAssign cert) φ

/-- Soundness: an accepted certificate proves satisfiability. -/
theorem verify_sound (φ : CNF) (cert : List Bool) :
    verify φ cert = true → Satisfiable φ :=
  fun h => ⟨toAssign cert, h⟩

/-- Completeness: a satisfiable formula on variables `< n` has an accepted
certificate of length exactly `n`. -/
theorem verify_complete (n : Nat) (φ : CNF) (hφ : VarsBelow n φ) :
    Satisfiable φ → ∃ cert, cert.length = n ∧ verify φ cert = true := by
  intro ⟨a, ha⟩
  refine ⟨prefixOf a n, length_prefixOf a n, ?_⟩
  unfold verify
  rw [evalCNF_congr (toAssign (prefixOf a n)) a n φ
    (fun i hi => toAssign_prefixOf a n i hi) hφ]
  exact ha

/-- The NP characterization of SAT: satisfiable iff some certificate of length
`numVars φ` (at most the input length) is accepted. -/
theorem sat_iff_exists_cert (φ : CNF) :
    Satisfiable φ ↔ ∃ cert, cert.length = numVars φ ∧ verify φ cert = true := by
  constructor
  · exact verify_complete _ φ (varsBelow_numVars φ)
  · intro ⟨cert, _, h⟩; exact verify_sound φ cert h

/-- The certificate is polynomially (in fact linearly) short. -/
theorem cert_length_le_encoding (φ : CNF) (cert : List Bool)
    (h : cert.length = numVars φ) : cert.length ≤ (encodeCNF φ).length :=
  h ▸ numVars_le_encodingLength φ

/-! ## Cost of verification, counted in literal evaluations -/

/-- Evaluate a clause, counting every literal evaluation (no short-circuit). -/
def clauseRun (a : Assignment) : Clause → Bool × Nat
  | [] => (false, 0)
  | l :: c => (evalLit a l || (clauseRun a c).1, (clauseRun a c).2 + 1)

def cnfRun (a : Assignment) : CNF → Bool × Nat
  | [] => (true, 0)
  | c :: φ => ((clauseRun a c).1 && (cnfRun a φ).1, (clauseRun a c).2 + (cnfRun a φ).2)

/-- The instrumented verifier: answer and number of literal evaluations. -/
def verifyRun (φ : CNF) (cert : List Bool) : Bool × Nat := cnfRun (toAssign cert) φ

theorem clauseRun_fst (a : Assignment) (c : Clause) : (clauseRun a c).1 = evalClause a c := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [clauseRun, evalClause, ih]

theorem clauseRun_snd (a : Assignment) (c : Clause) : (clauseRun a c).2 = c.length := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [clauseRun, List.length_cons, ih]

theorem cnfRun_fst (a : Assignment) (φ : CNF) : (cnfRun a φ).1 = evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp only [cnfRun, evalCNF, ih, clauseRun_fst]

theorem cnfRun_snd (a : Assignment) (φ : CNF) : (cnfRun a φ).2 = size φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp only [cnfRun, size, ih, clauseRun_snd]

/-- The instrumented verifier computes `verify`. -/
theorem verifyRun_result (φ : CNF) (cert : List Bool) :
    (verifyRun φ cert).1 = verify φ cert := cnfRun_fst _ φ

/-- Verification costs exactly `size φ` literal evaluations, for every
certificate. -/
theorem verify_cost_eq (φ : CNF) (cert : List Bool) : (verifyRun φ cert).2 = size φ :=
  cnfRun_snd _ φ

/-- Verification is linear in the input length. -/
theorem verify_cost_le_encoding (φ : CNF) (cert : List Bool) :
    2 * (verifyRun φ cert).2 ≤ (encodeCNF φ).length := by
  rw [verify_cost_eq]; exact size_le_encodingLength φ

/-- Short-circuit evaluation: stop a clause at its first true literal and the
formula at its first false clause. -/
def clauseRunSC (a : Assignment) : Clause → Bool × Nat
  | [] => (false, 0)
  | l :: c => if evalLit a l then (true, 1) else ((clauseRunSC a c).1, (clauseRunSC a c).2 + 1)

def cnfRunSC (a : Assignment) : CNF → Bool × Nat
  | [] => (true, 0)
  | c :: φ =>
    if (clauseRunSC a c).1 then ((cnfRunSC a φ).1, (clauseRunSC a c).2 + (cnfRunSC a φ).2)
    else (false, (clauseRunSC a c).2)

def verifyRunSC (φ : CNF) (cert : List Bool) : Bool × Nat := cnfRunSC (toAssign cert) φ

theorem clauseRunSC_fst (a : Assignment) (c : Clause) :
    (clauseRunSC a c).1 = evalClause a c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [clauseRunSC, evalClause]
    cases evalLit a l <;> simp [ih]

theorem clauseRunSC_snd (a : Assignment) (c : Clause) : (clauseRunSC a c).2 ≤ c.length := by
  induction c with
  | nil => exact Nat.le_refl 0
  | cons l c ih =>
    simp only [clauseRunSC, List.length_cons]
    cases evalLit a l <;> simp <;> omega

theorem cnfRunSC_fst (a : Assignment) (φ : CNF) : (cnfRunSC a φ).1 = evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [cnfRunSC, evalCNF, ← clauseRunSC_fst a c]
    cases (clauseRunSC a c).1 <;> simp [ih]

theorem cnfRunSC_snd (a : Assignment) (φ : CNF) : (cnfRunSC a φ).2 ≤ size φ := by
  induction φ with
  | nil => exact Nat.le_refl 0
  | cons c φ ih =>
    simp only [cnfRunSC, size]
    have := clauseRunSC_snd a c
    cases (clauseRunSC a c).1 <;> simp <;> omega

/-- The short-circuit verifier computes `verify`. -/
theorem verifyRunSC_result (φ : CNF) (cert : List Bool) :
    (verifyRunSC φ cert).1 = verify φ cert := cnfRunSC_fst _ φ

/-- The short-circuit verifier costs at most `size φ`. -/
theorem verifyRunSC_cost_le (φ : CNF) (cert : List Bool) :
    (verifyRunSC φ cert).2 ≤ size φ := cnfRunSC_snd _ φ

/-! ## Where the difficulty lies: the quantifier over certificates -/

/-- Unsatisfiability is a universal statement over all `2^n` certificates. -/
theorem unsat_iff_all_rejected (n : Nat) (φ : CNF) (hφ : VarsBelow n φ) :
    ¬ Satisfiable φ ↔ ∀ cert ∈ allAssignments n, verify φ cert = false := by
  constructor
  · intro h cert _
    cases hv : verify φ cert with
    | false => rfl
    | true => exact absurd (verify_sound φ cert hv) h
  · intro h hs
    obtain ⟨cert, hlen, hv⟩ := verify_complete n φ hφ hs
    have := h cert ((mem_allAssignments_iff n cert).mpr hlen)
    rw [hv] at this; exact Bool.noConfusion this

/-- Total cost of verifying every certificate in a list. -/
def totalCost (φ : CNF) : List (List Bool) → Nat
  | [] => 0
  | v :: L => (verifyRun φ v).2 + totalCost φ L

theorem totalCost_eq (φ : CNF) (L : List (List Bool)) : totalCost φ L = L.length * size φ := by
  induction L with
  | nil => simp [totalCost]
  | cons v L ih =>
    simp only [totalCost, ih, verify_cost_eq, List.length_cons, Nat.succ_mul]
    omega

/-- Checking all certificates of length `n` costs exactly `2^n * size φ`. -/
theorem total_verification_cost (n : Nat) (φ : CNF) :
    totalCost φ (allAssignments n) = 2 ^ n * size φ := by
  rw [totalCost_eq, length_allAssignments]

end Issue532.Idea03
