import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 18: structural restrictions and easy subclasses of SAT

Proved here, in general (for every CNF / every reduction):

* `allTrue_satisfies`, `allFalse_satisfies`: a CNF in which every clause has a
  positive (resp. negative) literal is satisfied by the all-true
  (resp. all-false) assignment ("1-valid" / "0-valid" in Schaefer's terms).
* `unitCNF_sat_iff`: a CNF whose clauses all have at most one literal is
  satisfiable iff it has no empty clause and no complementary pair of unit
  clauses.  `unitDecide` is a Boolean procedure proved correct for this class
  (`unitDecide_correct`).
* `reduction_into_trivial_class`, `no_reduction_of_nontrivial`: a
  yes/no-preserving map into a class on which the target predicate takes a single value
  forces the source predicate to take a single value.
* `no_sat_reduction_into_positive`, `no_sat_reduction_into_negative`: no
  satisfiability-preserving map whatsoever (computable or not) sends every
  CNF into the 1-valid or the 0-valid class.
* `restriction_transfer` and `poly_comp_bound`: if a restricted class `R`
  admits a correct decider and SAT reduces into `R` with polynomial size
  blow-up, then composing gives a correct SAT decider whose cost is bounded
  by a composed polynomial.  The schema `PolySizeReductionIntoFor R` records
  only the size bound; without a computability requirement it holds for unit
  CNF (`unit_size_reduction_exists`, via a non-constructive map).
* Machine model (`ReducesInto`, `SATInPOn`): the map is computed by a
  `Complexity.Machine` within a polynomial (`Computes`), and the restricted
  decider is a machine correct on the promise "decodes into `R`"
  (`DecidesOn`).  `inP_of_reducesInto` composes them into `InP`;
  `pEqualsNP_of_unitReduction` turns the open obligation `UnitReduction` (SAT
  reduces into unit CNF) into `PEqualsNP`, given the named known theorem
  `UnitSATInP` and `SATHard`.  In the machine model the trivial classes are
  refuted again (`reducesInto_positive_const`, `not_reducesInto_positive`),
  and `not_forall_reducesInto` shows that no class makes the reduction
  statement hold for every language.

Verdict: special-case algorithms are correct, but refuted as a general route
unless the restriction is shown NP-hard (Schaefer 1978 classifies exactly
which Boolean constraint languages remain NP-complete).
-/

namespace Issue532.Idea18

/-! ## SAT core -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: C => evalLit a l || evalClause a C

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | C :: φ => evalClause a C && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a, evalCNF a φ = true

theorem evalClause_true_iff (a : Assignment) (C : Clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLit a l = true := by
  induction C with
  | nil => simp [evalClause]
  | cons l C ih => simp [evalClause, ih]

theorem evalCNF_true_iff (a : Assignment) (φ : CNF) :
    evalCNF a φ = true ↔ ∀ C ∈ φ, evalClause a C = true := by
  induction φ with
  | nil => simp [evalCNF]
  | cons C φ ih => simp [evalCNF, ih]

/-- Size of a CNF: total number of literal occurrences plus number of clauses. -/
def size : CNF → Nat
  | [] => 0
  | C :: φ => C.length + 1 + size φ

/-! ## (a) 1-valid and 0-valid classes -/

/-- Every clause contains a positive literal (Schaefer's "1-valid"). -/
def PositiveClauses (φ : CNF) : Prop := ∀ C ∈ φ, ∃ l ∈ C, l.pos = true

/-- Every clause contains a negative literal (Schaefer's "0-valid"). -/
def NegativeClauses (φ : CNF) : Prop := ∀ C ∈ φ, ∃ l ∈ C, l.pos = false

/-- The all-true assignment satisfies every CNF whose clauses each contain a
positive literal. -/
theorem allTrue_satisfies (φ : CNF) (h : PositiveClauses φ) :
    evalCNF (fun _ => true) φ = true := by
  rw [evalCNF_true_iff]
  intro C hC
  obtain ⟨l, hl, hp⟩ := h C hC
  rw [evalClause_true_iff]
  exact ⟨l, hl, by simp [evalLit, hp]⟩

/-- The all-false assignment satisfies every CNF whose clauses each contain a
negative literal. -/
theorem allFalse_satisfies (φ : CNF) (h : NegativeClauses φ) :
    evalCNF (fun _ => false) φ = true := by
  rw [evalCNF_true_iff]
  intro C hC
  obtain ⟨l, hl, hp⟩ := h C hC
  rw [evalClause_true_iff]
  exact ⟨l, hl, by simp [evalLit, hp]⟩

theorem positive_satisfiable (φ : CNF) (h : PositiveClauses φ) : Satisfiable φ :=
  ⟨_, allTrue_satisfies φ h⟩

theorem negative_satisfiable (φ : CNF) (h : NegativeClauses φ) : Satisfiable φ :=
  ⟨_, allFalse_satisfies φ h⟩

/-! ## (b) Unit CNFs (every clause has at most one literal) -/

def IsUnitCNF (φ : CNF) : Prop := ∀ C ∈ φ, C.length ≤ 1

/-- Two unit clauses on the same variable with opposite signs. -/
def UnitClash (φ : CNF) : Prop :=
  ∃ l₁ l₂, [l₁] ∈ φ ∧ [l₂] ∈ φ ∧ l₁.var = l₂.var ∧ l₁.pos ≠ l₂.pos

theorem clause_of_length_le_one (C : Clause) (h : C.length ≤ 1) (hne : C ≠ []) :
    ∃ l, C = [l] := by
  match C, h, hne with
  | [l], _, _ => exact ⟨l, rfl⟩
  | _ :: _ :: _, h, _ => simp at h

/-- **Unit CNF characterization.**  A CNF whose clauses have at most one
literal is satisfiable iff it has no empty clause and no complementary pair of
unit clauses. -/
theorem unitCNF_sat_iff (φ : CNF) (hu : IsUnitCNF φ) :
    Satisfiable φ ↔ ([] ∉ φ ∧ ¬ UnitClash φ) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [evalCNF_true_iff] at ha
    refine ⟨fun hemp => ?_, ?_⟩
    · have := ha [] hemp
      simp [evalClause] at this
    · rintro ⟨l₁, l₂, h₁, h₂, hv, hp⟩
      have e₁ := ha _ h₁
      have e₂ := ha _ h₂
      simp only [evalClause, evalLit, Bool.or_false] at e₁ e₂
      rw [hv] at e₁
      cases hp₁ : l₁.pos <;> cases hp₂ : l₂.pos <;> simp_all
  · rintro ⟨hne, hclash⟩
    refine ⟨fun v => decide (([⟨v, true⟩] : Clause) ∈ φ), ?_⟩
    rw [evalCNF_true_iff]
    intro C hC
    have hCne : C ≠ [] := fun h => hne (h ▸ hC)
    obtain ⟨l, rfl⟩ := clause_of_length_le_one C (hu C hC) hCne
    simp only [evalClause, evalLit, Bool.or_false]
    cases hp : l.pos with
    | true =>
      have : l = ⟨l.var, true⟩ := by cases l; simp_all
      simp only [ite_true, decide_eq_true_iff]
      rw [← this]
      exact hC
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not]
      intro hmem
      exact hclash ⟨⟨l.var, true⟩, l, hmem, hC, rfl, by simp [hp]⟩

/-- A quadratic-time Boolean decision procedure for unit CNFs. -/
def unitDecide (φ : CNF) : Bool :=
  !(decide (([] : Clause) ∈ φ)) &&
  φ.all (fun C₁ => φ.all (fun C₂ =>
    match C₁, C₂ with
    | [l₁], [l₂] => !(decide (l₁.var = l₂.var) && decide (l₁.pos ≠ l₂.pos))
    | _, _ => true))

/-- `unitDecide` is correct on every unit CNF. -/
theorem unitDecide_correct (φ : CNF) (hu : IsUnitCNF φ) :
    unitDecide φ = true ↔ Satisfiable φ := by
  rw [unitCNF_sat_iff φ hu]
  unfold unitDecide
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hne, hall⟩
    refine ⟨hne, ?_⟩
    rintro ⟨l₁, l₂, h₁, h₂, hv, hp⟩
    rw [List.all_eq_true] at hall
    have h := hall _ h₁
    rw [List.all_eq_true] at h
    have h' := h _ h₂
    simp [hv, hp] at h'
  · rintro ⟨hne, hclash⟩
    refine ⟨hne, ?_⟩
    rw [List.all_eq_true]
    intro C₁ h₁
    rw [List.all_eq_true]
    intro C₂ h₂
    match C₁, C₂, h₁, h₂ with
    | [l₁], [l₂], h₁, h₂ =>
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases hv : l₁.var = l₂.var
      · right
        intro hp
        exact hclash ⟨l₁, l₂, h₁, h₂, hv, hp⟩
      · left; exact hv
    | [], _, _, _ => rfl
    | _ :: _ :: _, _, _, _ => rfl
    | [_], [], _, _ => rfl
    | [_], _ :: _ :: _, _, _ => rfl

/-! ## (c) Reductions into trivial classes -/

/-- If `L` reduces to `M` along `f` and `M` is identically true, `L` is
identically true. -/
theorem reduction_into_trivial_class {α β : Type} (L : α → Prop) (M : β → Prop)
    (f : α → β) (hred : ∀ x, L x ↔ M (f x)) (hconst : ∀ y, M y) : ∀ x, L x :=
  fun x => (hred x).mpr (hconst (f x))

/-- A predicate with a no-instance admits no reduction (by any function) to a
predicate that is identically true. -/
theorem no_reduction_of_nontrivial {α β : Type} (L : α → Prop) (M : β → Prop)
    (hno : ∃ x, ¬ L x) (hconst : ∀ y, M y) : ¬ ∃ f : α → β, ∀ x, L x ↔ M (f x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := hno
  exact hx (reduction_into_trivial_class L M f hf hconst x)

theorem empty_clause_unsat : ¬ Satisfiable [[]] := by
  rintro ⟨a, ha⟩
  simp [evalCNF, evalClause] at ha

/-- No satisfiability-preserving map (computable or not) lands inside the
1-valid class: SAT has an unsatisfiable instance, the class has none. -/
theorem no_sat_reduction_into_positive :
    ¬ ∃ f : CNF → CNF, (∀ φ, PositiveClauses (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) := by
  rintro ⟨f, hpos, hpres⟩
  exact empty_clause_unsat ((hpres [[]]).mpr (positive_satisfiable _ (hpos _)))

/-- Dually for the 0-valid class. -/
theorem no_sat_reduction_into_negative :
    ¬ ∃ f : CNF → CNF, (∀ φ, NegativeClauses (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) := by
  rintro ⟨f, hneg, hpres⟩
  exact empty_clause_unsat ((hpres [[]]).mpr (negative_satisfiable _ (hneg _)))

/-! ## The only useful direction: a hardness-preserving restriction -/

def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

/-- Size-only schema for a restricted class `R`: SAT reduces into `R` by a
satisfiability-preserving map with polynomial size blow-up.  The map is an
arbitrary function, so this schema records no running time: for the classes
of (a) it is false by `no_sat_reduction_into_positive`, and for unit CNF it is
provable (`unit_size_reduction_exists`).  The machine version, with the map
computed by a `Complexity.Machine`, is `ReducesInto` below. -/
def PolySizeReductionIntoFor (R : CNF → Prop) : Prop :=
  ∃ (f : CNF → CNF) (c k : Nat),
    (∀ φ, R (f φ)) ∧ (∀ φ, Satisfiable φ ↔ Satisfiable (f φ)) ∧
    (∀ φ, size (f φ) ≤ polyEval c k (size φ))

/-- Without a computability requirement the size-only obligation holds for unit
CNF: send satisfiable formulas to `[]` and the rest to `[[]]`.  The map is
defined by classical case analysis and is not claimed to be efficient. -/
theorem unit_size_reduction_exists : PolySizeReductionIntoFor IsUnitCNF := by
  classical
  refine ⟨fun φ => if Satisfiable φ then [] else [[]], 1, 0, ?_, ?_, ?_⟩
  · intro φ C hC
    by_cases h : Satisfiable φ
    · simp [h] at hC
    · simp [h] at hC
      subst hC
      simp
  · intro φ
    by_cases h : Satisfiable φ
    · simp only [h, ite_true, true_iff]
      exact ⟨fun _ => true, rfl⟩
    · simp only [h, ite_false, false_iff]
      exact empty_clause_unsat
  · intro φ
    by_cases h : Satisfiable φ
    · simp [h, size, polyEval]
    · simp [h, size, polyEval]

/-- Polynomials of the repository's form are closed under composition. -/
theorem poly_comp_bound (c k c' k' n : Nat) :
    polyEval c' k' (polyEval c k n) ≤ polyEval (c' * (c + 1) ^ k') (k * k') n := by
  unfold polyEval
  have h1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h3 : (c * (n + 1) ^ k + 1) ^ k' ≤ ((c + 1) * (n + 1) ^ k) ^ k' :=
    Nat.pow_le_pow_left h2 k'
  rw [Nat.mul_pow, ← Nat.pow_mul] at h3
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left c' h3

/-- **Conditional transfer.**  A decider `d` correct on `R`, composed with a
satisfiability-preserving reduction into `R`, decides SAT; if `d`'s cost is
bounded by a monotone polynomial in the size of its input, the composed cost
is bounded by a polynomial in the size of the original formula (the cost of
computing `f` must be added separately). -/
theorem restriction_transfer (R : CNF → Prop) (hR : PolySizeReductionIntoFor R)
    (d : CNF → Bool) (hd : ∀ ψ, R ψ → (d ψ = true ↔ Satisfiable ψ))
    (dcost : CNF → Nat) (c' k' : Nat) (hcost : ∀ ψ, dcost ψ ≤ polyEval c' k' (size ψ)) :
    ∃ f : CNF → CNF, ∃ C K : Nat,
      (∀ φ, d (f φ) = true ↔ Satisfiable φ) ∧
      (∀ φ, dcost (f φ) ≤ polyEval C K (size φ)) := by
  obtain ⟨f, c, k, hfR, hfsat, hfsize⟩ := hR
  refine ⟨f, c' * (c + 1) ^ k', k * k', fun φ => ?_, fun φ => ?_⟩
  · rw [hd _ (hfR φ), ← hfsat φ]
  · have mono : polyEval c' k' (size (f φ)) ≤ polyEval c' k' (polyEval c k (size φ)) := by
      unfold polyEval
      exact Nat.mul_le_mul_left c' (Nat.pow_le_pow_left (by have := hfsize φ; unfold polyEval at this; omega) k')
    exact Nat.le_trans (hcost _) (Nat.le_trans mono (poly_comp_bound c k c' k' _))

/-! ## The machine model: a polynomial-time reduction into a restricted class -/

open Complexity

/-- A CNF of the shared machine model, read in this file's syntax. -/
def ofM (φ : Machines.CNF) : CNF := φ.map (List.map fun l => ⟨l.var, l.pos⟩)

theorem evalClause_ofM (a : Assignment) (C : Machines.Clause) :
    evalClause a (C.map fun l => (⟨l.var, l.pos⟩ : Lit)) = Machines.evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [List.map_cons, evalClause, Machines.evalClause, ih, evalLit, Machines.evalLit]
    cases l.pos <;> cases a l.var <;> rfl

theorem evalCNF_ofM (a : Assignment) (φ : Machines.CNF) :
    evalCNF a (ofM φ) = Machines.evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    simp only [ofM, List.map_cons, evalCNF, Machines.evalCNF] at ih ⊢
    rw [evalClause_ofM, ih]

/-- The machine-model language `SAT` is satisfiability in this file's syntax. -/
theorem sat_ofM (w : Word) : Machines.SAT w = true ↔ Satisfiable (ofM (Machines.decode w)) := by
  rw [Machines.sat_iff]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [evalCNF_ofM]; exact ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← evalCNF_ofM]; exact ha⟩

/-- A polynomial-time machine reduction of `L` into the class `R`: a
`Complexity.Machine` computes `f` within a polynomial, every output decodes to a
CNF in `R`, and `L x = SAT (f x)`. -/
def ReducesInto (L : Language) (R : CNF → Prop) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
    ∀ x, R (ofM (Machines.decode (f x))) ∧ L x = Machines.SAT (f x)

/-- SAT restricted to `R` is decided by a polynomial-time machine that is correct
on every word decoding to a CNF in `R` (a promise problem). -/
def SATInPOn (R : CNF → Prop) : Prop :=
  ∃ (d : Machine) (p : Polynomial),
    Machines.DecidesOn d p (fun w => R (ofM (Machines.decode w))) Machines.SAT

/-- **Transfer in the machine model.** A polynomial-time reduction into `R`
followed by a polynomial-time decider correct on `R` puts `L` in P. -/
theorem inP_of_reducesInto {L : Language} {R : CNF → Prop} (h : ReducesInto L R)
    (hR : SATInPOn R) : InP L := by
  obtain ⟨m, f, p, hm, hf⟩ := h
  obtain ⟨d, p', hd⟩ := hR
  exact Machines.inP_of_promise_reduction hm (fun x => (hf x).1) (fun x => (hf x).2) hd

/-- The machine-model version of the size schema's correctness half: a machine
reduction into `R` is a satisfiability-preserving map of CNFs into `R`. -/
theorem reducesInto_preserves {R : CNF → Prop} (h : ReducesInto Machines.SAT R) :
    ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
      ∀ φ : Machines.CNF, R (ofM (Machines.decode (f (Machines.encodeCNF φ)))) ∧
        (Satisfiable (ofM φ) ↔ Satisfiable (ofM (Machines.decode (f (Machines.encodeCNF φ))))) := by
  obtain ⟨m, f, p, hm, hf⟩ := h
  refine ⟨m, f, p, hm, fun φ => ⟨(hf _).1, ?_⟩⟩
  have e := (hf (Machines.encodeCNF φ)).2
  rw [← sat_ofM, ← e, sat_ofM, Machines.decode_encode]

/-- **Known theorem, not mechanised here.** Satisfiability of unit CNFs (every
clause has at most one literal) is decided in polynomial time: check for an
empty clause and for a complementary pair of unit clauses (a quadratic scan;
its correctness is `unitCNF_sat_iff` / `unitDecide_correct` above, and it is a
special case of Horn-SAT, Dowling–Gallier 1984, and of 2-SAT, Aspvall–Plass–
Tarjan 1979).  What is not mechanised is a `Complexity.Machine` implementing
the scan on encoded formulas. -/
def UnitSATInP : Prop := SATInPOn IsUnitCNF

/-- **Open obligation.** SAT reduces into unit CNF by a polynomial-time machine:
a `Complexity.Machine` computes, within a polynomial number of `Run` steps, a map
`f` such that every `f x` decodes to a unit CNF and `SAT x = SAT (f x)`. -/
def UnitReduction : Prop := ReducesInto Machines.SAT IsUnitCNF

/-- **Conditional theorem.** The open obligation and the known unit-CNF decider
put SAT in P. -/
theorem inP_sat_of_unitReduction (hU : UnitSATInP) (h : UnitReduction) : InP Machines.SAT :=
  inP_of_reducesInto h hU

/-- **Conditional theorem.** With the hardness half of Cook–Levin, the open
obligation gives P = NP. -/
theorem pEqualsNP_of_unitReduction (hard : Machines.SATHard) (hU : UnitSATInP)
    (h : UnitReduction) : PEqualsNP :=
  Machines.pEqualsNP_of_inP_sat hard (inP_sat_of_unitReduction hU h)

/-- The same route for any class `R` with a polynomial-time promise decider. -/
theorem pEqualsNP_of_reducesInto (hard : Machines.SATHard) {R : CNF → Prop}
    (hR : SATInPOn R) (h : ReducesInto Machines.SAT R) : PEqualsNP :=
  Machines.pEqualsNP_of_inP_sat hard (inP_of_reducesInto h hR)

/-- A machine reduction into the 1-valid class forces a constant answer. -/
theorem reducesInto_positive_const {L : Language} (h : ReducesInto L PositiveClauses) :
    ∀ x, L x = true := by
  obtain ⟨m, f, p, _, hf⟩ := h
  intro x
  rw [(hf x).2]
  exact (sat_ofM (f x)).mpr (positive_satisfiable _ (hf x).1)

theorem machine_empty_clause_unsat : Machines.SAT (Machines.encodeCNF [[]]) = false := by
  cases h : Machines.SAT (Machines.encodeCNF [[]]) with
  | false => rfl
  | true =>
    obtain ⟨a, ha⟩ := (Machines.sat_encode [[]]).mp h
    simp [Machines.evalCNF, Machines.evalClause] at ha

/-- **Refutation in the machine model.** SAT has no polynomial-time (indeed no)
machine reduction into the 1-valid class. -/
theorem not_reducesInto_positive : ¬ ReducesInto Machines.SAT PositiveClauses := by
  intro h
  have := reducesInto_positive_const h (Machines.encodeCNF [[]])
  rw [machine_empty_clause_unsat] at this
  cases this

/-- The language obtained by running the machine `m` as a reduction into `M`. -/
noncomputable def viaMachine (M : Language) (m : Machine) : Language :=
  fun x => @decide (∃ (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧ M (f x) = true)
    (Classical.propDecidable _)

theorem viaMachine_eq {M : Language} {m : Machine} {f : Word → Word} {p : Polynomial}
    (hm : Machines.Computes m f p) : viaMachine M m = fun x => M (f x) := by
  funext x
  unfold viaMachine
  cases h : M (f x) with
  | true => exact @decide_eq_true _ (Classical.propDecidable _) ⟨f, p, hm, h⟩
  | false =>
    apply @decide_eq_false _ (Classical.propDecidable _)
    rintro ⟨g, q, hg, hgx⟩
    rw [← Machines.computes_unique hm hg, h] at hgx
    cases hgx

/-- **Cantor over machines.** For every target language `M` some language has no
machine map `f` with `L x = M (f x)`. -/
theorem exists_not_reducible (M : Language) :
    ∃ L : Language, ∀ (m : Machine) (f : Word → Word) (p : Polynomial),
      Machines.Computes m f p → ∃ x, L x ≠ M (f x) := by
  obtain ⟨L, hL⟩ := Machines.exists_language_not_in_family Machines.encMachine
    (fun _ _ h => Machines.encMachine_injective h) (viaMachine M)
  refine ⟨L, fun m f p hm => Classical.byContradiction fun hno => hL m ?_⟩
  rw [viaMachine_eq hm]
  funext x
  exact Classical.byContradiction fun hx => hno ⟨x, fun h => hx h.symm⟩

/-- **Non-vacuity.** For every class `R`, some language has no polynomial-time
machine reduction into `R`; so `ReducesInto Machines.SAT R` is a statement about
SAT and not a consequence of the definitions. -/
theorem not_forall_reducesInto (R : CNF → Prop) : ¬ ∀ L : Language, ReducesInto L R := by
  intro h
  obtain ⟨L, hL⟩ := exists_not_reducible Machines.SAT
  obtain ⟨m, f, p, hm, hf⟩ := h L
  obtain ⟨x, hx⟩ := hL m f p hm
  exact hx (hf x).2

end Issue532.Idea18
