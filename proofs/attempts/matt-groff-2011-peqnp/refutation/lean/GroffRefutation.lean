import Init.Data.Nat.Lemmas

/-
  A finite-field collision for the raw truth-table polynomial described in
  Groff (2011), Section 2. Each Fin 8 clause below denotes the three-literal
  disjunction falsified by that one assignment to x₀,x₁,x₂. Thus the formulas
  are actual 3-CNF inputs, not arbitrary Nat → Nat functions.

  This does not model the paper's later coefficient transformations, repeated
  evaluations, or linear-system reconstruction. The collision refutes only
  recovery of SAT from one raw polynomial value at x=3 modulo 271.
-/

namespace GroffRefutation

abbrev Assignment := Fin 8
abbrev Clause := Fin 8
abbrev Formula := List Clause

-- Bit i is the value of variable xᵢ. The clause indexed by c contains xᵢ
-- when c's bit is 0 and ¬xᵢ when c's bit is 1.
def bit (a : Assignment) (i : Fin 3) : Bool :=
  a.val / (2 ^ i.val) % 2 == 1

def clauseSatisfied (c : Clause) (a : Assignment) : Bool :=
  (List.range 3).any (fun i =>
    bit a ⟨i % 3, by omega⟩ != bit c ⟨i % 3, by omega⟩)

theorem clause_falsified_at_one_assignment :
    ∀ c a : Assignment, clauseSatisfied c a = false ↔ c = a := by
  decide

def satisfies (f : Formula) (a : Assignment) : Bool :=
  f.all (fun c => clauseSatisfied c a)

-- Both formulas have eight full three-literal clauses. Repetition is allowed
-- in CNF. The first excludes assignments 1,2,4,6,7 and is satisfied at 0,3,5.
-- The second excludes all eight assignments.
def satFormula : Formula := [1, 2, 4, 6, 7, 1, 2, 4]
def unsatFormula : Formula := [0, 1, 2, 3, 4, 5, 6, 7]

theorem formulas_have_eight_clauses :
    satFormula.length = 8 ∧ unsatFormula.length = 8 := by decide

theorem sat_formula_has_witness :
    satisfies satFormula 0 = true := by decide

theorem unsat_formula_has_no_witness :
    ¬ ∃ a : Assignment, satisfies unsatFormula a = true := by decide

-- The raw clause-polynomial coefficient at exponent i is 1 precisely when
-- assignment i satisfies the whole formula. The value is computed in GF(271).
def rawPolynomialValue (f : Formula) : Nat :=
  ((List.range 8).foldl (fun total i =>
    total + if satisfies f ⟨i % 8, by omega⟩ then 3 ^ i else 0) 0) % 271

def satisfyingCount (f : Formula) : Nat :=
  ((List.range 8).filter (fun i =>
    satisfies f ⟨i % 8, by omega⟩)).length

theorem field_and_input_conditions :
    (∀ d : Fin 17, d.val > 1 → 271 % d.val ≠ 0) ∧
    271 > (2 * satFormula.length) ^ 2 ∧
    271 > (2 * unsatFormula.length) ^ 2 := by decide

theorem raw_evaluation_collision :
    rawPolynomialValue satFormula = 0 ∧
    rawPolynomialValue unsatFormula = 0 ∧
    satisfyingCount satFormula = 3 ∧
    satisfyingCount unsatFormula = 0 := by decide

-- The disputed inference "one raw field value determines whether the number
-- of satisfying assignments is zero" has this explicit counterexample.
theorem raw_value_does_not_determine_satisfiability :
    ∃ fSat fUnsat : Formula,
      fSat.length = 8 ∧ fUnsat.length = 8 ∧
      rawPolynomialValue fSat = rawPolynomialValue fUnsat ∧
      satisfyingCount fSat > 0 ∧ satisfyingCount fUnsat = 0 := by
  exact ⟨satFormula, unsatFormula, by decide, by decide,
    by decide, by decide, by decide⟩

end GroffRefutation
