/-!
# Issue #532, Idea 01 — Exact SAT algorithm (brute force as the baseline)

This file develops the most direct route to P = NP: "write a uniform SAT
decider and prove it correct and fast".  Everything is core Lean 4 (no
Mathlib, no imports).

What is proved (all general, for every CNF formula and every `n`):

* `length_allAssignments` — the enumeration `allAssignments n` has exactly
  `2^n` entries; `mem_allAssignments_iff` — it contains exactly the bit
  vectors of length `n`; `nodup_allAssignments` — without repetition.
* `brute_force_sound`, `brute_force_complete`, `bruteForce_correct` — the
  uniform brute-force decider is correct for every CNF.
* `bruteForceCost_le`, `bruteForceCost_unsat`, `hardFamily_cost` — the
  number of formula evaluations performed by brute force is at most `2^n`,
  is exactly `2^n` on every unsatisfiable formula, and for every `n ≥ 1`
  there is an unsatisfiable formula mentioning exactly the variables
  `0, …, n-1` on which it is `2^n`.
* `numVars_le_encodingLength`, `bruteForceCost_le_exp_size` — the cost is at
  most `2^(input length)` for the explicit binary encoding `encodeCNF`.
* `decode_encode`, `encode_injective` — the encoding is lossless.
* `polySAT_agrees_with_bruteForce` — conditional theorem: if the open
  obligation `PolySATDecider` holds, the polynomial-time machine computes
  exactly the brute-force answer on every formula.

The open obligation `PolySATDecider` is stated over an explicit finite-table
single-tape Turing machine (the same shape as the repository's
`proofs/complexity/lean/Complexity.lean`, re-declared here so that the file is
standalone).  It is a `def … : Prop`; it is never postulated.
Core Lean functions carry no intrinsic running time, which is why the
obligation must be phrased over a machine model rather than over a Lean
function `CNF → Bool` (brute force *is* such a function).

Verdict: brute force is refuted as a polynomial-time algorithm (it performs
`2^n` evaluations on every unsatisfiable input with `n` variables); the route
"a uniform polynomial-time SAT decider" is, by the Cook–Levin theorem (not
formalized here), equivalent to P = NP and remains open.
-/

namespace Issue532.Idea01

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

/-! ## The brute-force decider -/

/-- Try every vector of length `n`. -/
def bruteForce (n : Nat) (φ : CNF) : Bool :=
  (allAssignments n).any (fun v => evalCNF (toAssign v) φ)

/-- Soundness: acceptance yields a satisfying assignment. -/
theorem brute_force_sound (n : Nat) (φ : CNF) :
    bruteForce n φ = true → Satisfiable φ := by
  intro h
  obtain ⟨v, _, hv⟩ := List.any_eq_true.mp h
  exact ⟨toAssign v, hv⟩

/-- Completeness: if all variables are `< n`, every satisfiable formula is
accepted, because every assignment agrees on `0, …, n-1` with a listed vector. -/
theorem brute_force_complete (n : Nat) (φ : CNF) (hφ : VarsBelow n φ) :
    Satisfiable φ → bruteForce n φ = true := by
  intro ⟨a, ha⟩
  apply List.any_eq_true.mpr
  refine ⟨prefixOf a n, (mem_allAssignments_iff n _).mpr (length_prefixOf a n), ?_⟩
  rw [evalCNF_congr (toAssign (prefixOf a n)) a n φ
    (fun i hi => toAssign_prefixOf a n i hi) hφ]
  exact ha

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

/-- The uniform decider: brute force over the variables that occur. -/
theorem bruteForce_correct (φ : CNF) :
    bruteForce (numVars φ) φ = true ↔ Satisfiable φ :=
  ⟨brute_force_sound _ φ, brute_force_complete _ φ (varsBelow_numVars φ)⟩

/-! ## Cost: number of formula evaluations -/

/-- Evaluations performed by a left-to-right search that stops at the first
satisfying vector. -/
def searchCount (φ : CNF) : List (List Bool) → Nat
  | [] => 0
  | v :: vs => if evalCNF (toAssign v) φ then 1 else 1 + searchCount φ vs

def bruteForceCost (n : Nat) (φ : CNF) : Nat := searchCount φ (allAssignments n)

theorem searchCount_le (φ : CNF) (L : List (List Bool)) : searchCount φ L ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons v L ih =>
    simp only [searchCount, List.length_cons]
    split <;> omega

theorem searchCount_all_false (φ : CNF) (L : List (List Bool))
    (h : ∀ v ∈ L, evalCNF (toAssign v) φ = false) : searchCount φ L = L.length := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [searchCount, List.length_cons]
    rw [h v (List.mem_cons_self ..), ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    simp; omega

/-- Brute force never uses more than `2^n` evaluations. -/
theorem bruteForceCost_le (n : Nat) (φ : CNF) : bruteForceCost n φ ≤ 2 ^ n := by
  have := searchCount_le φ (allAssignments n)
  rw [length_allAssignments] at this
  exact this

/-- On every unsatisfiable formula brute force uses exactly `2^n` evaluations. -/
theorem bruteForceCost_unsat (n : Nat) (φ : CNF) (h : ¬ Satisfiable φ) :
    bruteForceCost n φ = 2 ^ n := by
  unfold bruteForceCost
  rw [searchCount_all_false φ _ ?_, length_allAssignments]
  intro v _
  cases hv : evalCNF (toAssign v) φ with
  | false => rfl
  | true => exact absurd ⟨toAssign v, hv⟩ h

/-- `k` tautological clauses `x_i ∨ ¬x_i`, `i < k`. -/
def tautChain : Nat → CNF
  | 0 => []
  | k + 1 => [⟨k, true⟩, ⟨k, false⟩] :: tautChain k

/-- An unsatisfiable formula mentioning exactly the variables `0, …, n-1`. -/
def hardFamily (n : Nat) : CNF := [⟨0, true⟩] :: [⟨0, false⟩] :: tautChain n

theorem numVars_tautChain (k : Nat) : numVars (tautChain k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tautChain, numVars, clauseBound, ih]; omega

theorem hardFamily_unsat (n : Nat) : ¬ Satisfiable (hardFamily n) := by
  intro ⟨a, ha⟩
  simp only [hardFamily, evalCNF, evalClause, evalLit, Bool.or_false,
    Bool.and_eq_true] at ha
  obtain ⟨h1, h2, _⟩ := ha
  rw [beq_iff_eq] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Exponential cost for every size: for `n ≥ 1`, `hardFamily n` has exactly
`n` variables, is unsatisfiable, and brute force performs `2^n` evaluations. -/
theorem hardFamily_cost (n : Nat) (hn : 1 ≤ n) :
    numVars (hardFamily n) = n ∧ ¬ Satisfiable (hardFamily n) ∧
      bruteForceCost (numVars (hardFamily n)) (hardFamily n) = 2 ^ n := by
  have hv : numVars (hardFamily n) = n := by
    simp only [hardFamily, numVars, clauseBound, numVars_tautChain]; omega
  exact ⟨hv, hardFamily_unsat n, by rw [hv]; exact bruteForceCost_unsat n _ (hardFamily_unsat n)⟩

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

/-- Brute force is at most exponential in the input length. -/
theorem bruteForceCost_le_exp_size (φ : CNF) :
    bruteForceCost (numVars φ) φ ≤ 2 ^ (encodeCNF φ).length :=
  Nat.le_trans (bruteForceCost_le _ φ)
    (Nat.pow_le_pow_right (by decide) (numVars_le_encodingLength φ))

/-! ## The open obligation, stated over an explicit machine model

A finite instruction table; one instruction per step.  This mirrors
`proofs/complexity/lean/Complexity.lean`. -/

inductive Symbol where
  | blank | zero | one
  deriving DecidableEq, Repr

def Symbol.ofBool : Bool → Symbol
  | false => .zero
  | true => .one

def Symbol.index : Symbol → Nat
  | .blank => 0
  | .zero => 1
  | .one => 2

inductive Direction where
  | left | right | stay
  deriving DecidableEq, Repr

inductive Instruction where
  | halt (answer : Bool)
  | move (nextState : Nat) (write : Symbol) (direction : Direction)
  deriving DecidableEq, Repr

/-- Row `q`, column `a` of the table; a missing entry rejects. -/
structure Machine where
  program : List (List Instruction)

structure Config where
  state : Nat
  left : List Symbol
  head : Symbol
  right : List Symbol

def initial (input : List Bool) : Config :=
  match input.map Symbol.ofBool with
  | [] => ⟨0, [], .blank, []⟩
  | a :: rest => ⟨0, [], a, rest⟩

def Machine.instruction (m : Machine) (q : Nat) (a : Symbol) : Instruction :=
  ((m.program[q]?).bind fun row => row[a.index]?).getD (.halt false)

def moveHead (c : Config) (next : Nat) (write : Symbol) : Direction → Config
  | .stay => ⟨next, c.left, write, c.right⟩
  | .left => match c.left with
      | [] => ⟨next, [], .blank, write :: c.right⟩
      | a :: rest => ⟨next, rest, a, write :: c.right⟩
  | .right => match c.right with
      | [] => ⟨next, write :: c.left, .blank, []⟩
      | a :: rest => ⟨next, write :: c.left, a, rest⟩

def step (m : Machine) (c : Config) : Bool ⊕ Config :=
  match m.instruction c.state c.head with
  | .halt b => .inl b
  | .move next write dir => .inr (moveHead c next write dir)

/-- `Run m c t b`: from `c`, the machine halts with answer `b` after `t` steps. -/
inductive Run (m : Machine) : Config → Nat → Bool → Prop where
  | halt {c b} : step m c = .inl b → Run m c 1 b
  | next {c c' t b} : step m c = .inr c' → Run m c' t b → Run m c (t + 1) b

structure Polynomial where
  coefficient : Nat
  degree : Nat

def Polynomial.eval (p : Polynomial) (n : Nat) : Nat := p.coefficient * (n + 1) ^ p.degree

/-- **Open obligation.**  A single finite machine and a single polynomial
such that, on the encoding of *every* CNF, the machine halts within the
polynomial bound with the correct satisfiability answer.  By Cook–Levin
(not formalized here) this is equivalent to P = NP. -/
def PolySATDecider : Prop :=
  ∃ (M : Machine) (p : Polynomial), ∀ φ : CNF, ∃ t b,
    t ≤ p.eval (encodeCNF φ).length ∧ Run M (initial (encodeCNF φ)) t b ∧
      (b = true ↔ Satisfiable φ)

/-- Conditional theorem: a machine witnessing the obligation must output,
within its polynomial budget, exactly the brute-force answer on every CNF.
Brute force is the reference semantics any fast decider must reproduce. -/
theorem polySAT_agrees_with_bruteForce (h : PolySATDecider) :
    ∃ (M : Machine) (p : Polynomial), ∀ φ : CNF, ∃ t,
      t ≤ p.eval (encodeCNF φ).length ∧
        Run M (initial (encodeCNF φ)) t (bruteForce (numVars φ) φ) := by
  obtain ⟨M, p, hM⟩ := h
  refine ⟨M, p, fun φ => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hM φ
  have hbf := bruteForce_correct φ
  have : b = bruteForce (numVars φ) φ := by
    cases b <;> cases hbb : bruteForce (numVars φ) φ
    · rfl
    · exact absurd (hb.mpr (hbf.mp hbb)) (by decide)
    · exact absurd (hbf.mpr (hb.mp rfl)) (by simp [hbb])
    · rfl
  exact ⟨t, ht, this ▸ hr⟩

end Issue532.Idea01
