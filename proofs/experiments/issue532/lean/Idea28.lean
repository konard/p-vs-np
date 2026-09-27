import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 28: definitional extensions (Tseitin transformation)

Verdict: **correct tool, insufficient alone (general theorem proved)**.
The Tseitin transformation shows that formula/circuit satisfiability reduces
to 3-SAT with linear blow-up (hardness preservation); it does not make any
instance easier. Adding definitions to a proof system gives extended
resolution, for which superpolynomial lower bounds are open.

Proved for every propositional formula `f` (inductive `var/neg/conj/disj`):

* `tseitin_equisat` — `Satisfiable (tseitinCNF f) ↔ ∃ a, f.eval a = true`.
* `tseitinCNF_length` — `#clauses ≤ 3 · #gates + 1`.
* `tseitinCNF_width` — every clause has at most 3 literals.
* `tseitinCNF_vars` — all variables are `< bound f + gates f`
  (one fresh variable per gate, `tseitin_next`).
* `transfer` — a correct 3-CNF decider composed with `tseitinCNF` decides
  formula satisfiability.
* `define_and_sat_iff` — adding `y ↔ x ∧ z` for fresh `y` preserves
  satisfiability of any CNF.
* `defGate_iff`, `er_sat`, `er_sound` — extended resolution (`ERDerives`:
  resolution plus weakening plus extension clauses `y ↔ l₁ ∧ l₂` for fresh
  `y`) is sound.
* `ERSuperpolyLowerBoundFor` — the lower-bound shape for a given family of
  CNFs (a schema).

Tie to the shared machine model. `toMachineCNF` translates this file's CNFs
into `Issue532.Machines.CNF` (`satisfiable_toMachine`), and `satWord φ` is the
word that `Issue532.Machines.SAT` reads (`sat_satWord`). The open obligation
`ERNotPolyBounded` says that extended resolution is not a polynomially bounded
refutation system for the words that SAT rejects. It is equivalent to the
existence of a family satisfying the schema (`erNotPolyBounded_iff_family`).

What it gives, honestly: a lower bound for one fixed proof system only shows
that this system (and every weaker one, e.g. resolution:
`resNotPolyBounded_of_er`) is not polynomially bounded. It does not give
NP ≠ coNP, and so not P ≠ NP: that needs a lower bound for *every* proof
system (Idea 39). The converse direction is a known theorem
(`CookReckhowER`, Cook–Reckhow 1979): NP ≠ coNP implies the obligation
(`erNotPolyBounded_of_npNeCoNP`). Non-vacuity of the shape: it holds for the
proof system with no rules and fails for a one-step system
(`noRules_notPolyBounded`, `oneStep_not_notPolyBounded`).

See `../ideas/Idea28.md`.
-/

namespace Issue532.Idea28

open Complexity
open Issue532.Machines (SAT NPEqualsCoNP)

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


theorem vars_append (φ ψ : CNF) : vars (φ ++ ψ) = vars φ ++ vars ψ := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simp [vars, ih, List.append_assoc]

/-- Update an assignment at one variable. -/
def update (b : Assignment) (y : Nat) (val : Bool) : Assignment :=
  fun w => if w = y then val else b w

theorem update_same (b : Assignment) (y : Nat) (val : Bool) : update b y val y = val := by
  simp [update]

theorem update_ne (b : Assignment) (y : Nat) (val : Bool) (w : Nat) (h : w ≠ y) :
    update b y val w = b w := by
  simp [update, h]

/-- Updating a variable that is above every variable of `φ` does not change `φ`. -/
theorem update_evalCNF (b : Assignment) (y : Nat) (val : Bool) (φ : CNF)
    (h : ∀ v, v ∈ vars φ → v < y) : evalCNF (update b y val) φ = evalCNF b φ :=
  eval_congr _ _ φ (fun v hv => update_ne b y val v (Nat.ne_of_lt (h v hv)))

/-! ## Gate clauses -/

def pl (v : Nat) : Lit := ⟨v, true⟩
def nl (v : Nat) : Lit := ⟨v, false⟩

/-- Clauses for `y ↔ ¬x`. -/
def negGate (y x : Nat) : CNF := [[pl y, pl x], [nl y, nl x]]
/-- Clauses for `y ↔ (x ∧ z)`. -/
def andGate (y x z : Nat) : CNF := [[nl y, pl x], [nl y, pl z], [pl y, nl x, nl z]]
/-- Clauses for `y ↔ (x ∨ z)`. -/
def orGate (y x z : Nat) : CNF := [[pl y, nl x], [pl y, nl z], [nl y, pl x, pl z]]

theorem negGate_iff (b : Assignment) (y x : Nat) :
    evalCNF b (negGate y x) = true ↔ b y = !(b x) := by
  cases hy : b y <;> cases hx : b x <;>
    simp [negGate, evalCNF, evalClause, evalLit, pl, nl, hy, hx]

theorem andGate_iff (b : Assignment) (y x z : Nat) :
    evalCNF b (andGate y x z) = true ↔ b y = (b x && b z) := by
  cases hy : b y <;> cases hx : b x <;> cases hz : b z <;>
    simp [andGate, evalCNF, evalClause, evalLit, pl, nl, hy, hx, hz]

theorem orGate_iff (b : Assignment) (y x z : Nat) :
    evalCNF b (orGate y x z) = true ↔ b y = (b x || b z) := by
  cases hy : b y <;> cases hx : b x <;> cases hz : b z <;>
    simp [orGate, evalCNF, evalClause, evalLit, pl, nl, hy, hx, hz]

theorem negGate_vars (y x : Nat) : ∀ v, v ∈ vars (negGate y x) → v = y ∨ v = x := by
  intro v hv
  simp [negGate, vars, clauseVars, pl, nl] at hv
  omega

theorem andGate_vars (y x z : Nat) :
    ∀ v, v ∈ vars (andGate y x z) → v = y ∨ v = x ∨ v = z := by
  intro v hv
  simp [andGate, vars, clauseVars, pl, nl] at hv
  omega

theorem orGate_vars (y x z : Nat) :
    ∀ v, v ∈ vars (orGate y x z) → v = y ∨ v = x ∨ v = z := by
  intro v hv
  simp [orGate, vars, clauseVars, pl, nl] at hv
  omega

/-! ## Propositional formulas -/

inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving Repr

namespace Formula

def eval (a : Assignment) : Formula → Bool
  | var i => a i
  | neg f => !(eval a f)
  | conj f g => eval a f && eval a g
  | disj f g => eval a f || eval a g

/-- Number of gates (`¬`, `∧`, `∨` nodes). -/
def gates : Formula → Nat
  | var _ => 0
  | neg f => gates f + 1
  | conj f g => gates f + gates g + 1
  | disj f g => gates f + gates g + 1

/-- A strict upper bound on the input variables. -/
def bound : Formula → Nat
  | var i => i + 1
  | neg f => bound f
  | conj f g => max (bound f) (bound g)
  | disj f g => max (bound f) (bound g)

end Formula

theorem Formula.eval_congr (a b : Assignment) (f : Formula)
    (h : ∀ v, v < f.bound → a v = b v) : f.eval a = f.eval b := by
  induction f with
  | var i => exact h i (by simp [Formula.bound])
  | neg f ih => simp only [Formula.eval, ih h]
  | conj f g ihf ihg =>
    simp only [Formula.bound] at h
    simp only [Formula.eval,
      ihf (fun v hv => h v (by omega)), ihg (fun v hv => h v (by omega))]
  | disj f g ihf ihg =>
    simp only [Formula.bound] at h
    simp only [Formula.eval,
      ihf (fun v hv => h v (by omega)), ihg (fun v hv => h v (by omega))]

/-! ## The Tseitin transformation -/

structure TOut where
  out : Nat
  cls : CNF
  next : Nat

/-- `tseitin f n` uses fresh variables `n, n+1, …`; one per gate, allocated
after the children. `out` is the variable carrying the value of `f`. -/
def tseitin : Formula → Nat → TOut
  | .var i, n => ⟨i, [], n⟩
  | .neg f, n =>
    let r := tseitin f n
    ⟨r.next, r.cls ++ negGate r.next r.out, r.next + 1⟩
  | .conj f g, n =>
    let r := tseitin f n
    let s := tseitin g r.next
    ⟨s.next, r.cls ++ s.cls ++ andGate s.next r.out s.out, s.next + 1⟩
  | .disj f g, n =>
    let r := tseitin f n
    let s := tseitin g r.next
    ⟨s.next, r.cls ++ s.cls ++ orGate s.next r.out s.out, s.next + 1⟩

/-- The Tseitin CNF of `f`: gate clauses plus the unit clause asserting the output. -/
def tseitinCNF (f : Formula) : CNF :=
  (tseitin f f.bound).cls ++ [[pl (tseitin f f.bound).out]]

/-- Exactly one fresh variable per gate. -/
theorem tseitin_next (f : Formula) : ∀ n, (tseitin f n).next = n + f.gates := by
  induction f with
  | var i => intro n; simp [tseitin, Formula.gates]
  | neg f ih => intro n; simp only [tseitin, Formula.gates, ih]; omega
  | conj f g ihf ihg => intro n; simp only [tseitin, Formula.gates, ihf, ihg]; omega
  | disj f g ihf ihg => intro n; simp only [tseitin, Formula.gates, ihf, ihg]; omega

/-- At most three clauses per gate. -/
theorem tseitin_length (f : Formula) : ∀ n, (tseitin f n).cls.length ≤ 3 * f.gates := by
  induction f with
  | var i => intro n; simp [tseitin]
  | neg f ih =>
    intro n; have := ih n
    simp only [tseitin, Formula.gates, List.length_append, negGate, List.length_cons,
      List.length_nil]; omega
  | conj f g ihf ihg =>
    intro n; have := ihf n; have := ihg (tseitin f n).next
    simp only [tseitin, Formula.gates, List.length_append, andGate, List.length_cons,
      List.length_nil]; omega
  | disj f g ihf ihg =>
    intro n; have := ihf n; have := ihg (tseitin f n).next
    simp only [tseitin, Formula.gates, List.length_append, orGate, List.length_cons,
      List.length_nil]; omega

/-- Every Tseitin clause has at most three literals. -/
theorem tseitin_width (f : Formula) : ∀ n c, c ∈ (tseitin f n).cls → c.length ≤ 3 := by
  induction f with
  | var i => intro n c hc; simp [tseitin] at hc
  | neg f ih =>
    intro n c hc
    simp only [tseitin, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih n c hc
    · simp [negGate] at hc; rcases hc with rfl | rfl <;> simp
  | conj f g ihf ihg =>
    intro n c hc
    simp only [tseitin, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ihf n c hc
    · exact ihg _ c hc
    · simp [andGate] at hc; rcases hc with rfl | rfl | rfl <;> simp
  | disj f g ihf ihg =>
    intro n c hc
    simp only [tseitin, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ihf n c hc
    · exact ihg _ c hc
    · simp [orGate] at hc; rcases hc with rfl | rfl | rfl <;> simp

/-- **Soundness.** Any model of the gate clauses gives the output variable
the value of the formula. -/
theorem tseitin_sound (f : Formula) : ∀ n b,
    evalCNF b (tseitin f n).cls = true → b (tseitin f n).out = f.eval b := by
  induction f with
  | var i => intro n b _; rfl
  | neg f ih =>
    intro n b h
    simp only [tseitin, evalCNF_append, Bool.and_eq_true] at h
    simp only [tseitin, Formula.eval]
    rw [(negGate_iff b _ _).1 h.2, ih n b h.1]
  | conj f g ihf ihg =>
    intro n b h
    simp only [tseitin, evalCNF_append, Bool.and_eq_true] at h
    simp only [tseitin, Formula.eval]
    rw [(andGate_iff b _ _ _).1 h.2, ihf n b h.1.1, ihg _ b h.1.2]
  | disj f g ihf ihg =>
    intro n b h
    simp only [tseitin, evalCNF_append, Bool.and_eq_true] at h
    simp only [tseitin, Formula.eval]
    rw [(orGate_iff b _ _ _).1 h.2, ihf n b h.1.1, ihg _ b h.1.2]

/-- Scope: when the inputs are below `n`, every variable used is below `next`. -/
theorem tseitin_scope (f : Formula) : ∀ n, f.bound ≤ n →
    (tseitin f n).out < (tseitin f n).next ∧
    ∀ v, v ∈ vars (tseitin f n).cls → v < (tseitin f n).next := by
  induction f with
  | var i =>
    intro n hn
    simp only [Formula.bound] at hn
    simp only [tseitin, vars, List.not_mem_nil, false_implies, implies_true, and_true]
    omega
  | neg f ih =>
    intro n hn
    simp only [Formula.bound] at hn
    have ⟨h1, h2⟩ := ih n hn
    simp only [tseitin, vars_append, List.mem_append]
    refine ⟨by omega, ?_⟩
    intro v hv
    rcases hv with hv | hv
    · have := h2 v hv; omega
    · rcases negGate_vars _ _ v hv with rfl | rfl <;> omega
  | conj f g ihf ihg =>
    intro n hn
    simp only [Formula.bound] at hn
    have ⟨h1, h2⟩ := ihf n (by omega)
    have hr := tseitin_next f n
    have ⟨h3, h4⟩ := ihg (tseitin f n).next (by omega)
    have hs := tseitin_next g (tseitin f n).next
    simp only [tseitin, vars_append, List.mem_append]
    refine ⟨by omega, ?_⟩
    intro v hv
    rcases hv with (hv | hv) | hv
    · have := h2 v hv; omega
    · have := h4 v hv; omega
    · rcases andGate_vars _ _ _ v hv with rfl | rfl | rfl <;> omega
  | disj f g ihf ihg =>
    intro n hn
    simp only [Formula.bound] at hn
    have ⟨h1, h2⟩ := ihf n (by omega)
    have hr := tseitin_next f n
    have ⟨h3, h4⟩ := ihg (tseitin f n).next (by omega)
    have hs := tseitin_next g (tseitin f n).next
    simp only [tseitin, vars_append, List.mem_append]
    refine ⟨by omega, ?_⟩
    intro v hv
    rcases hv with (hv | hv) | hv
    · have := h2 v hv; omega
    · have := h4 v hv; omega
    · rcases orGate_vars _ _ _ v hv with rfl | rfl | rfl <;> omega

/-- The canonical extension of an input assignment: each gate variable gets
the value of its subformula. -/
def extend : Formula → Nat → Assignment → Assignment
  | .var _, _, a => a
  | .neg f, n, a => update (extend f n a) (tseitin f n).next (!(f.eval a))
  | .conj f g, n, a =>
    update (extend g (tseitin f n).next (extend f n a))
      (tseitin g (tseitin f n).next).next (f.eval a && g.eval a)
  | .disj f g, n, a =>
    update (extend g (tseitin f n).next (extend f n a))
      (tseitin g (tseitin f n).next).next (f.eval a || g.eval a)

/-- The extension does not touch variables below `n`. -/
theorem extend_below (f : Formula) : ∀ n a v, v < n → extend f n a v = a v := by
  induction f with
  | var i => intro n a v _; rfl
  | neg f ih =>
    intro n a v hv
    have := tseitin_next f n
    simp only [extend]
    rw [update_ne _ _ _ _ (by omega), ih n a v hv]
  | conj f g ihf ihg =>
    intro n a v hv
    have := tseitin_next f n
    have := tseitin_next g (tseitin f n).next
    simp only [extend]
    rw [update_ne _ _ _ _ (by omega), ihg _ _ v (by omega), ihf n a v hv]
  | disj f g ihf ihg =>
    intro n a v hv
    have := tseitin_next f n
    have := tseitin_next g (tseitin f n).next
    simp only [extend]
    rw [update_ne _ _ _ _ (by omega), ihg _ _ v (by omega), ihf n a v hv]

/-- Helper for binary gates. -/
theorem extend_binary (f g : Formula) (n : Nat) (a : Assignment)
    (hf : f.bound ≤ n) (hg : g.bound ≤ n)
    (ihf : evalCNF (extend f n a) (tseitin f n).cls = true ∧
      extend f n a (tseitin f n).out = f.eval a)
    (ihg : evalCNF (extend g (tseitin f n).next (extend f n a))
        (tseitin g (tseitin f n).next).cls = true ∧
      extend g (tseitin f n).next (extend f n a) (tseitin g (tseitin f n).next).out =
        g.eval (extend f n a))
    (val : Bool) :
    let r := tseitin f n
    let s := tseitin g r.next
    let b := update (extend g r.next (extend f n a)) s.next val
    evalCNF b (r.cls ++ s.cls) = true ∧ b r.out = f.eval a ∧ b s.out = g.eval a := by
  intro r s b
  have hr : r.next = n + f.gates := tseitin_next f n
  have hs : s.next = r.next + g.gates := tseitin_next g r.next
  have o1 : r.out < r.next := (tseitin_scope f n hf).1
  have v1 : ∀ v, v ∈ vars r.cls → v < r.next := (tseitin_scope f n hf).2
  have o2 : s.out < s.next := (tseitin_scope g r.next (by omega)).1
  have v2 : ∀ v, v ∈ vars s.cls → v < s.next := (tseitin_scope g r.next (by omega)).2
  have hga : g.eval (extend f n a) = g.eval a :=
    Formula.eval_congr _ _ g (fun v hv => extend_below f n a v (by omega))
  have b2r : evalCNF (extend g r.next (extend f n a)) r.cls = true := by
    rw [eval_congr _ (extend f n a) r.cls (fun v hv => extend_below g r.next _ v (v1 v hv))]
    exact ihf.1
  refine ⟨?_, ?_, ?_⟩
  · rw [evalCNF_append, update_evalCNF _ _ _ _ (fun v hv => by have := v1 v hv; omega),
      update_evalCNF _ _ _ _ v2, b2r, ihg.1]
    rfl
  · simp only [b]
    rw [update_ne _ _ _ _ (by omega), extend_below g r.next _ _ o1, ihf.2]
  · simp only [b]
    rw [update_ne _ _ _ _ (by omega), ihg.2, hga]

/-- **Completeness.** The canonical extension satisfies the gate clauses and
gives the output variable the value of the formula. -/
theorem extend_correct (f : Formula) : ∀ n a, f.bound ≤ n →
    evalCNF (extend f n a) (tseitin f n).cls = true ∧
    extend f n a (tseitin f n).out = f.eval a := by
  induction f with
  | var i => intro n a _; exact ⟨rfl, rfl⟩
  | neg f ih =>
    intro n a hn
    simp only [Formula.bound] at hn
    have ⟨c1, e1⟩ := ih n a hn
    have ⟨o1, v1⟩ := tseitin_scope f n hn
    simp only [tseitin, extend, Formula.eval]
    refine ⟨?_, update_same _ _ _⟩
    rw [evalCNF_append, update_evalCNF _ _ _ _ v1, c1, Bool.true_and, negGate_iff,
      update_same, update_ne _ _ _ _ (Nat.ne_of_lt o1), e1]
  | conj f g ihf ihg =>
    intro n a hn
    simp only [Formula.bound] at hn
    have ihf' := ihf n a (by omega)
    have ihg' := ihg (tseitin f n).next (extend f n a)
      (by have := tseitin_next f n; omega)
    have ⟨c, e1, e2⟩ := extend_binary f g n a (by omega) (by omega) ihf' ihg'
      (f.eval a && g.eval a)
    simp only [tseitin, extend, Formula.eval]
    refine ⟨?_, update_same _ _ _⟩
    rw [evalCNF_append, c, Bool.true_and, andGate_iff, update_same, e1, e2]
  | disj f g ihf ihg =>
    intro n a hn
    simp only [Formula.bound] at hn
    have ihf' := ihf n a (by omega)
    have ihg' := ihg (tseitin f n).next (extend f n a)
      (by have := tseitin_next f n; omega)
    have ⟨c, e1, e2⟩ := extend_binary f g n a (by omega) (by omega) ihf' ihg'
      (f.eval a || g.eval a)
    simp only [tseitin, extend, Formula.eval]
    refine ⟨?_, update_same _ _ _⟩
    rw [evalCNF_append, c, Bool.true_and, orGate_iff, update_same, e1, e2]

/-- **Tseitin equisatisfiability**, for every formula. -/
theorem tseitin_equisat (f : Formula) :
    Satisfiable (tseitinCNF f) ↔ ∃ a, f.eval a = true := by
  constructor
  · rintro ⟨b, hb⟩
    simp only [tseitinCNF, evalCNF_append, Bool.and_eq_true] at hb
    refine ⟨b, ?_⟩
    rw [← tseitin_sound f _ b hb.1]
    simpa [evalCNF, evalClause, evalLit, pl] using hb.2
  · rintro ⟨a, ha⟩
    have ⟨c, e⟩ := extend_correct f f.bound a (Nat.le_refl _)
    refine ⟨extend f f.bound a, ?_⟩
    simp only [tseitinCNF, evalCNF_append, c, Bool.true_and]
    simp [evalCNF, evalClause, evalLit, pl, e, ha]

/-- **Linear size.** `#clauses ≤ 3 · #gates + 1`. -/
theorem tseitinCNF_length (f : Formula) : (tseitinCNF f).length ≤ 3 * f.gates + 1 := by
  have := tseitin_length f f.bound
  simp only [tseitinCNF, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **3-CNF.** Every clause of the Tseitin CNF has at most three literals. -/
theorem tseitinCNF_width (f : Formula) : ∀ c, c ∈ tseitinCNF f → c.length ≤ 3 := by
  intro c hc
  simp only [tseitinCNF, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact tseitin_width f _ c hc
  · simp

/-- **Count of variables.** All variables are below `bound f + gates f`. -/
theorem tseitinCNF_vars (f : Formula) :
    ∀ v, v ∈ vars (tseitinCNF f) → v < f.bound + f.gates := by
  intro v hv
  have ⟨o, h⟩ := tseitin_scope f f.bound (Nat.le_refl _)
  have e := tseitin_next f f.bound
  simp only [tseitinCNF, vars_append, List.mem_append] at hv
  rcases hv with hv | hv
  · have := h v hv; omega
  · simp [vars, clauseVars, pl] at hv; omega

/-- **Transfer (hardness preservation).** A decider that is correct on all
CNFs of width ≤ 3 yields, composed with `tseitinCNF`, a decider for formula
satisfiability. This is the reduction circuit-SAT ≤ 3-SAT. -/
theorem transfer (D : CNF → Bool)
    (hD : ∀ φ : CNF, (∀ c, c ∈ φ → c.length ≤ 3) → (D φ = true ↔ Satisfiable φ))
    (f : Formula) : D (tseitinCNF f) = true ↔ ∃ a, f.eval a = true := by
  rw [hD _ (tseitinCNF_width f), tseitin_equisat]

/-- **Single definition.** Adding `y ↔ (x ∧ z)` for a fresh `y` preserves
satisfiability in both directions, for every CNF. -/
theorem define_and_sat_iff (φ : CNF) (y x z : Nat) (hy : y ∉ vars φ)
    (hx : y ≠ x) (hz : y ≠ z) :
    Satisfiable (φ ++ andGate y x z) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨b, hb⟩
    simp only [evalCNF_append, Bool.and_eq_true] at hb
    exact ⟨b, hb.1⟩
  · rintro ⟨a, ha⟩
    refine ⟨update a y (a x && a z), ?_⟩
    have e : evalCNF (update a y (a x && a z)) φ = evalCNF a φ :=
      eval_congr _ _ φ (fun v hv => update_ne _ _ _ _ (fun h => hy (h ▸ hv)))
    rw [evalCNF_append, e, ha, Bool.true_and, andGate_iff, update_same,
      update_ne _ _ _ _ (Ne.symm hx), update_ne _ _ _ _ (Ne.symm hz)]

/-! ## Extended resolution and the open obligation -/

/-- Negation of a literal. -/
def negLit (l : Lit) : Lit := ⟨l.var, !l.pos⟩

theorem evalLit_negLit (b : Assignment) (l : Lit) : evalLit b (negLit l) = !(evalLit b l) := by
  cases h : l.pos <;> simp [evalLit, negLit, h]

theorem evalLit_update (b : Assignment) (y : Nat) (val : Bool) (l : Lit) (h : l.var ≠ y) :
    evalLit (update b y val) l = evalLit b l := by
  simp [evalLit, update_ne _ _ _ _ h]

/-- The extension-rule clauses for `y ↔ (l₁ ∧ l₂)` with literals `l₁, l₂`
(a complete basis, as in Tseitin's extension rule). -/
def defGate (y : Nat) (l1 l2 : Lit) : CNF :=
  [[nl y, l1], [nl y, l2], [pl y, negLit l1, negLit l2]]

theorem defGate_iff (b : Assignment) (y : Nat) (l1 l2 : Lit) :
    evalCNF b (defGate y l1 l2) = true ↔ b y = (evalLit b l1 && evalLit b l2) := by
  have e1 : evalLit b (nl y) = !(b y) := rfl
  have e2 : evalLit b (pl y) = b y := rfl
  simp only [defGate, evalCNF, evalClause, e1, e2, evalLit_negLit]
  generalize b y = p
  generalize evalLit b l1 = q
  generalize evalLit b l2 = r
  cases p <;> cases q <;> cases r <;> decide

/-- `andGate` is the special case of `defGate` with two positive literals. -/
theorem andGate_eq_defGate (y x z : Nat) : andGate y x z = defGate y (pl x) (pl z) := rfl

/-- Extended-resolution derivations from `φ`. The current clause list starts
as `φ`. A step either adds a resolvent on `v` of two present clauses (keeping
every other literal; extra literals are allowed as weakening) or adds the
three extension clauses `defGate y l₁ l₂` for a variable `y` that occurs
nowhere yet and differs from the variables of `l₁, l₂`. -/
inductive ERDerives (φ : CNF) : CNF → Prop
  | start : ERDerives φ φ
  | res (π : CNF) (c1 c2 c : Clause) (v : Nat) :
      ERDerives φ π → c1 ∈ π → c2 ∈ π →
      (∀ l, l ∈ c1 → l ≠ pl v → l ∈ c) → (∀ l, l ∈ c2 → l ≠ nl v → l ∈ c) →
      ERDerives φ (c :: π)
  | ext (π : CNF) (y : Nat) (l1 l2 : Lit) :
      ERDerives φ π → y ∉ vars π → l1.var ≠ y → l2.var ≠ y →
      ERDerives φ (defGate y l1 l2 ++ π)

/-- Soundness of extended resolution: a satisfiable `φ` has an assignment
satisfying every derived clause. -/
theorem er_sat (φ : CNF) (π : CNF) (h : ERDerives φ π) :
    Satisfiable φ → Satisfiable π := by
  intro hs
  induction h with
  | start => exact hs
  | res π c1 c2 c v _ h1 h2 k1 k2 ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨b, ?_⟩
    have hb' := (evalCNF_iff b π).1 hb
    simp only [evalCNF, hb, Bool.and_true]
    cases hv : b v
    · obtain ⟨l, hl, he⟩ := (evalClause_iff b c1).1 (hb' c1 h1)
      refine (evalClause_iff b c).2 ⟨l, k1 l hl ?_, he⟩
      intro e; subst e; simp [evalLit, pl, hv] at he
    · obtain ⟨l, hl, he⟩ := (evalClause_iff b c2).1 (hb' c2 h2)
      refine (evalClause_iff b c).2 ⟨l, k2 l hl ?_, he⟩
      intro e; subst e; simp [evalLit, nl, hv] at he
  | ext π y l1 l2 _ hy h1 h2 ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨update b y (evalLit b l1 && evalLit b l2), ?_⟩
    have e : evalCNF (update b y (evalLit b l1 && evalLit b l2)) π = evalCNF b π :=
      eval_congr _ _ π (fun v hv => update_ne _ _ _ _ (fun h => hy (h ▸ hv)))
    rw [evalCNF_append, e, hb, Bool.and_true, defGate_iff, update_same,
      evalLit_update _ _ _ _ h1, evalLit_update _ _ _ _ h2]

/-- **Extended resolution is sound:** a derivation containing the empty
clause refutes `φ`. -/
theorem er_sound (φ π : CNF) (h : ERDerives φ π) (hempty : [] ∈ π) :
    ¬ Satisfiable φ := by
  intro hs
  obtain ⟨b, hb⟩ := er_sat φ π h hs
  have := (evalCNF_iff b π).1 hb [] hempty
  simp [evalClause] at this

/-- Size of a CNF: clauses plus literal occurrences. -/
def size : CNF → Nat
  | [] => 0
  | c :: φ => c.length + 1 + size φ

/-- Schema: a family of unsatisfiable CNFs whose extended-resolution
refutations are superpolynomially longer than the formulas. The family is a
parameter; the obligation on the shared machine model is `ERNotPolyBounded`. No
such family is known (Cook–Reckhow 1979). -/
def ERSuperpolyLowerBoundFor (family : Nat → CNF) : Prop :=
  (∀ n, ¬ Satisfiable (family n)) ∧
  ∀ c k : Nat, ∃ n, ∀ π, ERDerives (family n) π → [] ∈ π →
    c * (size (family n) + 1) ^ k < π.length

/-- Any family witnessing the lower bound consists of unsatisfiable formulas
and has no refutation of length bounded by a fixed polynomial. -/
theorem obligation_excludes_poly_bound (family : Nat → CNF)
    (h : ERSuperpolyLowerBoundFor family) (c k : Nat) :
    ¬ (∀ n, ∃ π, ERDerives (family n) π ∧ [] ∈ π ∧
        π.length ≤ c * (size (family n) + 1) ^ k) := by
  intro hall
  obtain ⟨n, hn⟩ := h.2 c k
  obtain ⟨π, hπ, he, hl⟩ := hall n
  have := hn π hπ he
  omega

/-! ## Bridge to the shared machine model -/

/-- A literal of this file as a literal of `Issue532.Machines`. -/
def toMachineLit (l : Lit) : Issue532.Machines.Lit := ⟨l.var, l.pos⟩

/-- A CNF of this file as a CNF of `Issue532.Machines`. -/
def toMachineCNF (φ : CNF) : Issue532.Machines.CNF := φ.map (List.map toMachineLit)

theorem evalLit_toMachine (a : Assignment) (l : Lit) :
    Issue532.Machines.evalLit a (toMachineLit l) = evalLit a l := by
  cases hp : l.pos <;> cases ha : a l.var <;>
    simp [Issue532.Machines.evalLit, toMachineLit, evalLit, hp, ha]

theorem evalClause_toMachine (a : Assignment) (c : Clause) :
    Issue532.Machines.evalClause a (c.map toMachineLit) = evalClause a c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [List.map_cons, Issue532.Machines.evalClause, evalClause, evalLit_toMachine, ih]

theorem evalCNF_toMachine (a : Assignment) (φ : CNF) :
    Issue532.Machines.evalCNF a (toMachineCNF φ) = evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [toMachineCNF, List.map_cons, Issue532.Machines.evalCNF, evalCNF,
      evalClause_toMachine] at ih ⊢
    rw [ih]

theorem satisfiable_toMachine (φ : CNF) :
    Issue532.Machines.Satisfiable (toMachineCNF φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← evalCNF_toMachine]; exact ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [evalCNF_toMachine]; exact ha⟩

/-- The word that `Issue532.Machines.SAT` reads for the CNF `φ`. -/
def satWord (φ : CNF) : Word := Issue532.Machines.encodeCNF (toMachineCNF φ)

theorem sat_satWord (φ : CNF) : SAT (satWord φ) = true ↔ Satisfiable φ := by
  rw [satWord, Issue532.Machines.sat_encode, satisfiable_toMachine]

theorem sat_satWord_false (φ : CNF) : SAT (satWord φ) = false ↔ ¬ Satisfiable φ := by
  rw [← sat_satWord]
  cases SAT (satWord φ) <;> simp

/-! ## The obligation -/

/-- Schema: the refutation system `D` (`D φ π`: `π` is derivable from `φ`) is
not polynomially bounded on the words that SAT rejects. `D` is a parameter; the
obligation is the instance `ERNotPolyBounded`. -/
def NotPolyBoundedFor (D : CNF → CNF → Prop) : Prop :=
  ∀ c k : Nat, ∃ φ : CNF, SAT (satWord φ) = false ∧
    ∀ π, D φ π → [] ∈ π → c * (size φ + 1) ^ k < π.length

/-- **Open obligation.** Extended resolution is not polynomially bounded on the
unsatisfiable instances of `Issue532.Machines.SAT`: for every `c k` some CNF
`φ` with `SAT (satWord φ) = false` has no extended-resolution refutation with
at most `c * (size φ + 1) ^ k` clauses. Open since Cook–Reckhow (1979). -/
def ERNotPolyBounded : Prop :=
  ∀ c k : Nat, ∃ φ : CNF, SAT (satWord φ) = false ∧
    ∀ π, ERDerives φ π → [] ∈ π → c * (size φ + 1) ^ k < π.length

theorem erNotPolyBounded_iff_for : ERNotPolyBounded ↔ NotPolyBoundedFor ERDerives := Iff.rfl

/-- Extended resolution is polynomially bounded: every unsatisfiable CNF has a
refutation with polynomially many clauses. -/
def ERPolyBounded : Prop :=
  ∃ c k : Nat, ∀ φ : CNF, SAT (satWord φ) = false →
    ∃ π, ERDerives φ π ∧ [] ∈ π ∧ π.length ≤ c * (size φ + 1) ^ k

theorem erNotPolyBounded_iff : ERNotPolyBounded ↔ ¬ ERPolyBounded := by
  constructor
  · rintro h ⟨c, k, hb⟩
    obtain ⟨φ, hφ, hlb⟩ := h c k
    obtain ⟨π, hπ, he, hl⟩ := hb φ hφ
    have := hlb π hπ he
    omega
  · intro h c k
    apply Classical.byContradiction
    intro hno
    apply h
    refine ⟨c, k, fun φ hφ => Classical.byContradiction fun hnone => hno ⟨φ, hφ, fun π hπ he => ?_⟩⟩
    apply Classical.byContradiction
    intro hlt
    exact hnone ⟨π, hπ, he, by omega⟩

/-- The obligation is exactly the existence of a family meeting the schema. -/
theorem erNotPolyBounded_iff_family :
    ERNotPolyBounded ↔ ∃ family : Nat → CNF, ERSuperpolyLowerBoundFor family := by
  constructor
  · intro h
    refine ⟨fun n => Classical.choose (h n n), fun n => ?_, fun c k => ⟨c + k, fun π hπ he => ?_⟩⟩
    · exact (sat_satWord_false _).mp (Classical.choose_spec (h n n)).1
    · have hlb := (Classical.choose_spec (h (c + k) (c + k))).2 π hπ he
      have h1 : c ≤ c + k := Nat.le_add_right c k
      have h2 : (size (Classical.choose (h (c + k) (c + k))) + 1) ^ k ≤
          (size (Classical.choose (h (c + k) (c + k))) + 1) ^ (c + k) :=
        Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left k c)
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul h1 h2) hlb
  · rintro ⟨family, hu, hlb⟩ c k
    obtain ⟨n, hn⟩ := hlb c k
    exact ⟨family n, (sat_satWord_false _).mpr (hu n), hn⟩

/-! ## What the obligation gives: weaker systems only -/

/-- Resolution derivations (with weakening): extended resolution without the
extension rule. -/
inductive ResDerives (φ : CNF) : CNF → Prop
  | start : ResDerives φ φ
  | res (π : CNF) (c1 c2 c : Clause) (v : Nat) :
      ResDerives φ π → c1 ∈ π → c2 ∈ π →
      (∀ l, l ∈ c1 → l ≠ pl v → l ∈ c) → (∀ l, l ∈ c2 → l ≠ nl v → l ∈ c) →
      ResDerives φ (c :: π)

theorem erDerives_of_res {φ π : CNF} (h : ResDerives φ π) : ERDerives φ π := by
  induction h with
  | start => exact ERDerives.start
  | res π c1 c2 c v _ h1 h2 k1 k2 ih => exact ERDerives.res π c1 c2 c v ih h1 h2 k1 k2

/-- Resolution is not polynomially bounded on the words SAT rejects. This is a
known theorem (Haken 1985), not mechanised here; below it is derived from the
extended-resolution obligation. -/
def ResNotPolyBounded : Prop := NotPolyBoundedFor ResDerives

/-- **Conditional theorem** (the honest conclusion). A lower bound for extended
resolution transfers to every weaker system, here resolution. It says nothing
about proof systems that are not simulated by extended resolution. -/
theorem resNotPolyBounded_of_er (h : ERNotPolyBounded) : ResNotPolyBounded := by
  intro c k
  obtain ⟨φ, hφ, hlb⟩ := h c k
  exact ⟨φ, hφ, fun π hπ he => hlb π (erDerives_of_res hπ) he⟩

/-- Known theorem, not mechanised here (Cook and Reckhow, "The relative
efficiency of propositional proof systems", J. Symbolic Logic 44 (1979)):
extended resolution is a propositional proof system (refutations are checkable
in polynomial time), so if it were polynomially bounded the complement of SAT
would be in NP and NP = coNP. Contrapositive: NP ≠ coNP implies
`ERNotPolyBounded`. -/
def CookReckhowER : Prop := ¬ NPEqualsCoNP → ERNotPolyBounded

/-- The obligation is implied by NP ≠ coNP (via the known theorem); it is not
known to imply NP ≠ coNP or P ≠ NP. -/
theorem erNotPolyBounded_of_npNeCoNP (hCR : CookReckhowER) (h : ¬ NPEqualsCoNP) :
    ERNotPolyBounded :=
  hCR h

/-! ## Non-vacuity of the shape -/

/-- `x₀ ∧ ¬x₀` as a CNF. -/
def contra : CNF := [[pl 0], [nl 0]]

theorem sat_contra : SAT (satWord contra) = false := by decide

/-- The shape holds for the system with no rules (only `φ` itself is derived),
since `contra` does not contain the empty clause. -/
theorem noRules_notPolyBounded : NotPolyBoundedFor (fun φ π => π = φ) := by
  intro c k
  refine ⟨contra, sat_contra, fun π hπ he => ?_⟩
  subst hπ
  simp [contra, pl, nl] at he

/-- The shape fails for a (unsound) system that derives the empty clause in
one step from anything. -/
theorem oneStep_not_notPolyBounded : ¬ NotPolyBoundedFor (fun _ π => π = [[]]) := by
  intro h
  obtain ⟨φ, _, hlb⟩ := h 1 0
  have := hlb [[]] rfl (by simp)
  simp at this

/-- The family schema fails for the formula consisting of the empty clause,
which extended resolution refutes in zero steps. -/
theorem emptyClause_not_superpoly : ¬ ERSuperpolyLowerBoundFor (fun _ => [[]]) := by
  intro h
  obtain ⟨n, hn⟩ := h.2 1 0
  have := hn [[]] ERDerives.start (by simp)
  simp at this

end Issue532.Idea28
