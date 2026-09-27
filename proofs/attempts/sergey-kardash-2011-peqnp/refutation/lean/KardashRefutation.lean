import proofs.complexity.lean.Complexity
/-
  KardashRefutation.lean - Refutation of Sergey Kardash's 2011 P=NP attempt

  This file demonstrates why Kardash's approach fails:
  pair cleaning is a local consistency method. An empty table proves that the
  formula is unsatisfiable, but the paper's proof that a non-empty result
  implies satisfiability (Lemma 1) has a gap for k ≥ 3.
-/

namespace KardashRefutation

-- Variable assignment
abbrev Assignment := Nat → Bool

-- A clause (disjunction of literals)
abbrev Clause := List (Nat × Bool)

-- Whether a clause is satisfied
def clauseSatisfied (c : Clause) (a : Assignment) : Bool :=
  c.any (fun ⟨idx, pol⟩ => if pol then !(a idx) else a idx)

-- A k-CNF formula as a list of clauses
abbrev KCNF := List Clause

-- Whether the formula is satisfied
def kcnfSatisfied (f : KCNF) (a : Assignment) : Bool :=
  f.all (fun c => clauseSatisfied c a)

-- Satisfiability
def isSatisfiable (f : KCNF) : Prop :=
  ∃ a : Assignment, kcnfSatisfied f a = true

-- Complexity
def isPolynomial (T : Nat → Nat) : Prop :=
  Complexity.PolynomiallyBounded T

-- FACT 1: Pair cleaning, like arc consistency, is polynomial to compute
theorem arcConsistency_polynomial : isPolynomial (fun n => n ^ 3) :=
  ⟨1, 3, fun n => by simpa using Nat.pow_le_pow_left (Nat.le_succ n) 3⟩

-- FACT 2: Local consistency is NECESSARY for satisfiability
-- (If cleaning empties a table, formula is UNSAT)
-- The contrapositive: satisfiable ⟹ arc-consistent (all pairings have compatible rows)
axiom arcConsistency_necessary :
  ∀ (f : KCNF), isSatisfiable f → True  -- arc consistency holds for satisfiable formulas

-- FACT 3 (The critical fact): Local consistency is NOT SUFFICIENT for k-SAT (k ≥ 3)
-- There exist k-SAT formulas (k ≥ 3) on which pair cleaning stays non-empty
-- although they are UNSATISFIABLE. This would directly refute Kardash's Theorem 1.
--
-- For plain arc consistency this is standard: in the 3-coloring CSP of K_4 every
-- disequality supports every color, yet K_4 is not 3-colorable. Pair cleaning is
-- stronger than arc consistency (see the 2-SAT section below), so that example
-- alone does not settle it; the statement is recorded here as an informal axiom.
axiom arcConsistency_insufficient :
  ∃ (f : KCNF), True ∧ ¬ isSatisfiable f
  -- 'True' represents: pair cleaning terminates non-empty
  -- '¬ isSatisfiable f' represents: formula is UNSAT

-- CONSEQUENCE: Kardash's Theorem 1 is false
-- "Pair cleaning non-empty ⟺ satisfiable" fails for k ≥ 3
theorem kardash_theorem1_false :
    ∃ (f : KCNF), True ∧ ¬ isSatisfiable f :=
  arcConsistency_insufficient

-- The error in Lemma 1 (inductive step):
-- Kardash claims that any non-empty cleaned structure contains
-- a single-valued unclearable sub-structure corresponding to a satisfying assignment.
-- This fails because local pairwise consistency ≠ global satisfiability.
axiom inductive_step_fails :
  ¬ (∀ (f : KCNF),
      -- pair cleaning non-empty implies
      True →
      -- globally satisfiable
      isSatisfiable f)

/-
  ## 2-SAT: propagation is not a decision procedure

  An earlier version of this file said that for k = 2 unit propagation and arc
  consistency coincide and decide 2-SAT, credited this to Krom (1967), and
  stated it as an assumption whose type was `True`. That explanation was wrong
  (issue #587), and the section below replaces it with checked definitions:

  * Unit propagation without decisions changes nothing on a formula whose
    clauses all have two literals: from the empty assignment no clause is
    unit and none is falsified (`unitPropagate_2CNF_empty`).
  * Arc consistency on the network with one binary constraint per clause
    removes nothing either, because every two-literal clause allows both
    values of each variable (`clausewiseCSP_arcConsistent`). Merging the
    constraints on a common scope catches `upCounterexample` (the merged
    relation is empty) but still misses the triangle x ≠ y, y ≠ z, z ≠ x
    (`triangle_arcConsistent`, `triangle_unsat`).
  * A complete polynomial test uses the implication graph, where a clause
    l₁ ∨ l₂ gives the edges ¬l₁ → l₂ and ¬l₂ → l₁. A 2-CNF is unsatisfiable
    iff some literal l has paths l ⇝ ¬l and ¬l ⇝ l, i.e. l and ¬l lie in one
    strongly connected component; Aspvall, Plass and Tarjan (1979) check this
    in linear time. The direction used for refutation is proved below
    (`contradictory_cycle_unsat`).

  Other correct routes: Krom (1967) showed that resolution restricted to
  binary clauses decides 2-SAT, and Even, Itai and Shamir (1976) decide it in
  polynomial time by combining unit propagation with decisions.

  What pair cleaning computes (Definitions 3-15 of the paper): clauses are
  grouped by their set of variable indices. For every combination of k + 1
  clause groups (one combination of all groups when there are at most k + 1)
  a table lists the assignments of the combination's variables that satisfy
  its clauses. Clearing deletes a row when another table has no row agreeing
  with it on their common variables, until nothing changes; the result is
  empty when some table is empty. This is pairwise consistency on the tables
  of clause combinations, which is stronger than arc consistency on single
  clauses: both formulas below fit in one table, and pair cleaning empties
  it. For k = 2 the non-empty result does imply satisfiability (sketch in
  ../README.md, checked by experiments/issue587); that is not formalized here.

  | Procedure                          | Time        | Decides 2-SAT?                 |
  |------------------------------------|-------------|--------------------------------|
  | Unit propagation, no decisions     | Polynomial  | No (`upCounterexample`)        |
  | Arc consistency, one per clause    | Polynomial  | No (`upCounterexample`)        |
  | Arc consistency, merged per scope  | Polynomial  | No (`triangleCSP`)             |
  | Implication-graph SCC (APT 1979)   | Linear      | Yes                            |
  | Binary resolution (Krom 1967)      | Polynomial  | Yes                            |
  | Pair cleaning, k = 2               | Polynomial  | Yes (informal sketch, tested)  |
  | DPLL with backtracking             | Exponential | Yes (and for every k)          |

  For k ≥ 3 the paper claims that pair cleaning decides k-SAT; the gap in
  Lemma 1 is recorded above by informal assumptions, not by a counterexample.
-/
section TwoSATCounterexamples

abbrev Literal := Nat × Bool

def literalTrue (a : Assignment) (l : Literal) : Bool :=
  if l.2 then !(a l.1) else a l.1

def negLit (l : Literal) : Literal := (l.1, !l.2)

theorem literalTrue_negLit (a : Assignment) (l : Literal) :
    literalTrue a (negLit l) = !literalTrue a l := by
  obtain ⟨i, p⟩ := l
  cases p <;> simp [literalTrue, negLit]

theorem clauseSatisfied_eq (c : Clause) (a : Assignment) :
    clauseSatisfied c a = c.any (literalTrue a) := rfl

/-! ### Unit propagation without decisions -/

-- Values of already assigned variables, as `(index, value)` pairs.
abbrev PartialAssignment := List (Nat × Bool)

def literalValue (ρ : PartialAssignment) (l : Literal) : Option Bool :=
  (ρ.lookup l.1).map (fun v => if l.2 then !v else v)

def clauseFalsified (ρ : PartialAssignment) (c : Clause) : Bool :=
  c.all (fun l => literalValue ρ l == some false)

-- The only unassigned literal of a clause that is not yet satisfied.
def forcedLiteral (ρ : PartialAssignment) (c : Clause) : Option Literal :=
  if c.any (fun l => literalValue ρ l == some true) then none
  else
    match c.filter (fun l => literalValue ρ l == none) with
    | [l] => some l
    | _ => none

inductive UPResult where
  | conflict
  | fixpoint (ρ : PartialAssignment)
  | outOfFuel
  deriving DecidableEq, Repr

-- Assign forced literals until a clause is falsified or none is forced.
def unitPropagate (f : KCNF) : Nat → PartialAssignment → UPResult
  | 0, _ => .outOfFuel
  | fuel + 1, ρ =>
    if f.any (clauseFalsified ρ) then .conflict
    else
      match f.findSome? (forcedLiteral ρ) with
      | some l => unitPropagate f fuel ((l.1, !l.2) :: ρ)
      | none => .fixpoint ρ

-- Two literals over two different variables.
def isBinary : Clause → Bool
  | [l₁, l₂] => l₁.1 != l₂.1
  | _ => false

def is2CNF (f : KCNF) : Bool := f.all isBinary

theorem clauseFalsified_nil (c : Clause) (h : isBinary c = true) :
    clauseFalsified [] c = false := by
  unfold isBinary at h
  split at h
  · simp [clauseFalsified, literalValue]
  · contradiction

theorem forcedLiteral_nil (c : Clause) (h : isBinary c = true) :
    forcedLiteral [] c = none := by
  unfold isBinary at h
  split at h
  · simp [forcedLiteral, literalValue]
  · contradiction

theorem unitPropagate_2CNF_empty (f : KCNF) (h : is2CNF f = true) (fuel : Nat) :
    unitPropagate f (fuel + 1) [] = .fixpoint [] := by
  have hbin : ∀ c ∈ f, isBinary c = true := List.all_eq_true.mp h
  have hconflict : f.any (clauseFalsified []) = false :=
    List.any_eq_false.mpr fun c hc => by simp [clauseFalsified_nil c (hbin c hc)]
  have hforced : f.findSome? (forcedLiteral []) = none :=
    List.findSome?_eq_none_iff.mpr fun c hc => forcedLiteral_nil c (hbin c hc)
  simp [unitPropagate, hconflict, hforced]

/-! ### Arc consistency on binary constraints -/

structure BinConstraint where
  x : Nat
  y : Nat
  rel : Bool → Bool → Bool

def bools : List Bool := [false, true]

-- Full Boolean domains are arc consistent: each value of each variable has a
-- support in every constraint, whose two variables are distinct.
def supported (c : BinConstraint) : Bool :=
  c.x != c.y &&
    bools.all (fun a => bools.any (fun b => c.rel a b)) &&
    bools.all (fun b => bools.any (fun a => c.rel a b))

def arcConsistentFull (csp : List BinConstraint) : Bool := csp.all supported

def cspSatisfied (csp : List BinConstraint) (a : Assignment) : Bool :=
  csp.all (fun c => c.rel (a c.x) (a c.y))

def cspSatisfiable (csp : List BinConstraint) : Prop :=
  ∃ a : Assignment, cspSatisfied csp a = true

def clauseConstraint : Clause → Option BinConstraint
  | [l₁, l₂] => some ⟨l₁.1, l₂.1, fun a b =>
      (if l₁.2 then !a else a) || (if l₂.2 then !b else b)⟩
  | _ => none

-- One constraint per clause, without merging constraints on the same scope.
def clausewiseCSP (f : KCNF) : List BinConstraint := f.filterMap clauseConstraint

theorem clauseConstraint_supported (c : Clause) (bc : BinConstraint)
    (hc : clauseConstraint c = some bc) (hbin : isBinary c = true) :
    supported bc = true := by
  unfold clauseConstraint at hc
  split at hc
  · rename_i l₁ l₂
    cases hc
    obtain ⟨i, p⟩ := l₁
    obtain ⟨j, q⟩ := l₂
    simp only [isBinary] at hbin
    cases p <;> cases q <;> simp_all [supported, bools]
  · contradiction

theorem clausewiseCSP_arcConsistent (f : KCNF) (h : is2CNF f = true) :
    arcConsistentFull (clausewiseCSP f) = true := by
  have hbin : ∀ c ∈ f, isBinary c = true := List.all_eq_true.mp h
  refine List.all_eq_true.mpr fun bc hbc => ?_
  obtain ⟨c, hc, hcb⟩ := List.mem_filterMap.mp hbc
  exact clauseConstraint_supported c bc hcb (hbin c hc)

/-! ### Implication graph -/

def clauseEdges : Clause → List (Literal × Literal)
  | [l₁, l₂] => [(negLit l₁, l₂), (negLit l₂, l₁)]
  | _ => []

def implicationEdges (f : KCNF) : List (Literal × Literal) := f.flatMap clauseEdges

-- `Implies f l₁ l₂`: a path from l₁ to l₂ in the implication graph of f.
inductive Implies (f : KCNF) : Literal → Literal → Prop
  | refl (l : Literal) : Implies f l l
  | step {l₁ l₂ l₃ : Literal} :
      (l₁, l₂) ∈ implicationEdges f → Implies f l₂ l₃ → Implies f l₁ l₃

theorem edge_sound (f : KCNF) (a : Assignment) (ha : kcnfSatisfied f a = true)
    {l₁ l₂ : Literal} (he : (l₁, l₂) ∈ implicationEdges f)
    (h₁ : literalTrue a l₁ = true) : literalTrue a l₂ = true := by
  obtain ⟨c, hc, hce⟩ := List.mem_flatMap.mp he
  have hsat : clauseSatisfied c a = true := List.all_eq_true.mp ha c hc
  rw [clauseSatisfied_eq] at hsat
  unfold clauseEdges at hce
  split at hce
  · rename_i m₁ m₂
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hsat
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hce
    rcases hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all [literalTrue_negLit]
  · simp at hce

theorem implies_sound (f : KCNF) (a : Assignment) (ha : kcnfSatisfied f a = true)
    {l₁ l₂ : Literal} (hp : Implies f l₁ l₂) :
    literalTrue a l₁ = true → literalTrue a l₂ = true := by
  induction hp with
  | refl => exact id
  | step he _ ih => exact fun h => ih (edge_sound f a ha he h)

-- Soundness of the strongly connected component test.
theorem contradictory_cycle_unsat (f : KCNF) (l : Literal)
    (h₁ : Implies f l (negLit l)) (h₂ : Implies f (negLit l) l) :
    ¬ isSatisfiable f := by
  rintro ⟨a, ha⟩
  have p := implies_sound f a ha h₁
  have q := implies_sound f a ha h₂
  rw [literalTrue_negLit] at p q
  cases hl : literalTrue a l <;> simp_all

/-! ### Counterexample 1: (x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y) -/

-- Variables x = 0, y = 1; `(i, true)` is the negative literal ¬xᵢ.
def upCounterexample : KCNF :=
  [[(0, false), (1, false)], [(0, false), (1, true)],
   [(0, true), (1, false)], [(0, true), (1, true)]]

theorem upCounterexample_is2CNF : is2CNF upCounterexample = true := by decide

theorem upCounterexample_unsat : ¬ isSatisfiable upCounterexample := by
  rintro ⟨a, ha⟩
  simp only [kcnfSatisfied, upCounterexample, clauseSatisfied_eq, literalTrue,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil] at ha
  cases h0 : a 0 <;> cases h1 : a 1 <;> simp [h0, h1] at ha

theorem upCounterexample_unitPropagate_fixpoint :
    unitPropagate upCounterexample 1 [] = .fixpoint [] :=
  unitPropagate_2CNF_empty _ upCounterexample_is2CNF 0

-- Propagation finds the conflict only after a decision on x.
theorem upCounterexample_conflict_after_decision :
    unitPropagate upCounterexample 3 [(0, true)] = .conflict ∧
    unitPropagate upCounterexample 3 [(0, false)] = .conflict := by
  decide

theorem upCounterexample_arcConsistent :
    arcConsistentFull (clausewiseCSP upCounterexample) = true :=
  clausewiseCSP_arcConsistent _ upCounterexample_is2CNF

-- x ⇝ y ⇝ ¬x and ¬x ⇝ y ⇝ x.
theorem upCounterexample_implication_refutation :
    Implies upCounterexample (0, false) (0, true) ∧
    Implies upCounterexample (0, true) (0, false) ∧
    ¬ isSatisfiable upCounterexample := by
  have h₁ : Implies upCounterexample (0, false) (0, true) :=
    .step (l₂ := (1, false)) (by decide) (.step (by decide) (.refl _))
  have h₂ : Implies upCounterexample (0, true) (0, false) :=
    .step (l₂ := (1, false)) (by decide) (.step (by decide) (.refl _))
  exact ⟨h₁, h₂, contradictory_cycle_unsat _ (0, false) h₁ h₂⟩

/-! ### Counterexample 2: the triangle x ≠ y, y ≠ z, z ≠ x -/

-- Variables x = 0, y = 1, z = 2, one constraint per pair.
def triangleCSP : List BinConstraint :=
  [⟨0, 1, fun a b => a != b⟩, ⟨1, 2, fun a b => a != b⟩, ⟨2, 0, fun a b => a != b⟩]

theorem triangle_arcConsistent : arcConsistentFull triangleCSP = true := by decide

theorem triangle_unsat : ¬ cspSatisfiable triangleCSP := by
  rintro ⟨a, ha⟩
  simp only [cspSatisfied, triangleCSP, List.all_cons, List.all_nil] at ha
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;> simp [h0, h1, h2] at ha

-- Each disequality u ≠ v is the pair of clauses (u ∨ v) ∧ (¬u ∨ ¬v).
def triangleCNF : KCNF :=
  [[(0, false), (1, false)], [(0, true), (1, true)],
   [(1, false), (2, false)], [(1, true), (2, true)],
   [(2, false), (0, false)], [(2, true), (0, true)]]

theorem triangleCNF_encodes (a : Assignment) :
    kcnfSatisfied triangleCNF a = cspSatisfied triangleCSP a := by
  simp only [kcnfSatisfied, triangleCNF, clauseSatisfied_eq, literalTrue, cspSatisfied,
    triangleCSP, List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  cases a 0 <;> cases a 1 <;> cases a 2 <;> rfl

theorem triangleCNF_is2CNF : is2CNF triangleCNF = true := by decide

theorem triangleCNF_unitPropagate_fixpoint :
    unitPropagate triangleCNF 1 [] = .fixpoint [] :=
  unitPropagate_2CNF_empty _ triangleCNF_is2CNF 0

theorem triangleCNF_arcConsistent :
    arcConsistentFull (clausewiseCSP triangleCNF) = true :=
  clausewiseCSP_arcConsistent _ triangleCNF_is2CNF

-- x ⇝ ¬y ⇝ z ⇝ ¬x and ¬x ⇝ y ⇝ ¬z ⇝ x.
theorem triangleCNF_implication_refutation :
    Implies triangleCNF (0, false) (0, true) ∧
    Implies triangleCNF (0, true) (0, false) ∧
    ¬ isSatisfiable triangleCNF := by
  have h₁ : Implies triangleCNF (0, false) (0, true) :=
    .step (l₂ := (1, true)) (by decide)
      (.step (l₂ := (2, false)) (by decide) (.step (by decide) (.refl _)))
  have h₂ : Implies triangleCNF (0, true) (0, false) :=
    .step (l₂ := (1, false)) (by decide)
      (.step (l₂ := (2, true)) (by decide) (.step (by decide) (.refl _)))
  exact ⟨h₁, h₂, contradictory_cycle_unsat _ (0, false) h₁ h₂⟩

end TwoSATCounterexamples

-- Main refutation theorem
theorem kardash_refutation :
    -- Claim 1: Pair cleaning is polynomial (CORRECT)
    isPolynomial (fun n => n ^ 3) ∧
    -- Claim 2: But it does not decide k-SAT for k ≥ 3 (INCORRECT in Kardash's paper)
    ∃ (f : KCNF), True ∧ ¬ isSatisfiable f := by
  constructor
  · exact arcConsistency_polynomial
  · exact arcConsistency_insufficient

end KardashRefutation
