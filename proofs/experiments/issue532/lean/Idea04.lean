/-!
# Issue #532, Idea 04 — Local consistency does not imply global satisfiability

A *disequality system* is a list of pairs `(i, j)`, read as the constraint
`x_i ≠ x_j` over Boolean variables.  The *XOR cycle* on `n` variables is

  `cycle n = [(0,1), (1,2), …, (n-2, n-1), (n-1, 0)]`,

that is, `x_i ≠ x_{(i+1) mod n}` for `i < n`.

Proved here, for every `n`:

* `cycle_sat_iff`: the cycle is satisfiable iff `n` is even
  (`cycle_even_sat`, `cycle_odd_unsat`, the parity argument);
* `missing_constraint_sat`: every subsystem of the cycle that misses at least
  one of its constraints is satisfiable (explicit alternating assignment);
* `short_subsystem_sat`: in particular every subsystem with fewer than `n`
  constraints is satisfiable (pigeonhole over the `n` distinct constraints);
* `odd_cycle_locally_consistent`: for odd `n` the cycle is
  `(n-1)`-locally consistent (every subsystem of at most `n-1` constraints is
  satisfiable) and yet unsatisfiable;
* `local_consistency_insufficient`: for every `k` there is an unsatisfiable
  system (the cycle of length `2k+1`) that is `k`-locally consistent, so no
  check of bounded-size subsystems decides satisfiability;
* `sysCNF_iff`, `cycleCNF_sat_iff`: the same systems as 2-CNF formulas
  (`x_i ≠ x_j` is `(x_i ∨ x_j) ∧ (¬x_i ∨ ¬x_j)`).

Verdict: "check every bounded-size piece and conclude global satisfiability"
is refuted for every bound.  Stronger propagation-based consistency (bounded
width) does solve these particular 2-CNF systems, but fails on other families
(linear equations mod 2, Tseitin formulas, and hence 3-SAT); those published
results are cited in `ideas/Idea04.md` and not formalized here.
-/

namespace Issue532.Idea04

/-! ## Disequality systems -/

/-- A list of constraints `x_i ≠ x_j`. -/
abbrev System := List (Nat × Nat)

/-- `x` satisfies every constraint of `sys`. -/
def Solves (x : Nat → Bool) (sys : System) : Prop := ∀ p ∈ sys, x p.1 ≠ x p.2

def SatSys (sys : System) : Prop := ∃ x : Nat → Bool, Solves x sys

/-- The XOR cycle: `x_i ≠ x_{(i+1) mod n}` for `i < n`. -/
def cycle (n : Nat) : System := (List.range n).map (fun i => (i, (i + 1) % n))

theorem mem_cycle (n : Nat) (p : Nat × Nat) :
    p ∈ cycle n ↔ ∃ i, i < n ∧ p = (i, (i + 1) % n) := by
  unfold cycle
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- Parity bit: `true` for odd `i`. -/
def par (i : Nat) : Bool := i % 2 == 1

theorem par_succ (i : Nat) : par (i + 1) = !par i := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have : (i + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (i + 1) % 2 = 0 := by omega
    simp [h, this]

theorem par_ne_succ (i : Nat) : par i ≠ par (i + 1) := by
  rw [par_succ]; cases par i <;> decide

theorem par_eq_false_iff (i : Nat) : par i = false ↔ i % 2 = 0 := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

theorem succ_mod_of_lt (i n : Nat) (h : i + 1 < n) : (i + 1) % n = i + 1 :=
  Nat.mod_eq_of_lt h

theorem succ_mod_of_eq (i n : Nat) (h : i + 1 = n) : (i + 1) % n = 0 := by
  rw [h]; exact Nat.mod_self n

/-! ## Even cycles are satisfiable, odd cycles are not -/

/-- Even cycles: the alternating assignment `x_i = par i` works. -/
theorem cycle_even_sat (n : Nat) (h : n % 2 = 0) : SatSys (cycle n) := by
  refine ⟨par, fun p hp => ?_⟩
  obtain ⟨i, hi, rfl⟩ := (mem_cycle n p).mp hp
  show par i ≠ par ((i + 1) % n)
  by_cases hlt : i + 1 < n
  · rw [succ_mod_of_lt i n hlt]; exact par_ne_succ i
  · rw [succ_mod_of_eq i n (by omega)]
    have : par i = true := by
      cases hpi : par i with
      | true => rfl
      | false => have := (par_eq_false_iff i).mp hpi; omega
    rw [this]; decide

/-- Along the path part of the cycle, a solution alternates:
`x i = x 0 ↔ i` is even. -/
theorem solution_alternates (n : Nat) (x : Nat → Bool) (hx : Solves x (cycle n)) :
    ∀ i, i < n → (x i = x 0 ↔ i % 2 = 0) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hc := hx (i, (i + 1) % n) ((mem_cycle n _).mpr ⟨i, by omega, rfl⟩)
    simp only [succ_mod_of_lt i n hi] at hc
    have ih' := ih (by omega)
    have hpar : (i + 1) % 2 = 0 ↔ ¬ i % 2 = 0 := by omega
    rw [hpar]
    constructor
    · intro h1 h2; exact hc (ih'.mpr h2 ▸ h1 ▸ rfl)
    · intro h1
      cases hxi : x i <;> cases hxs : x (i + 1) <;> cases hx0 : x 0 <;>
        simp_all

/-- Odd cycles are unsatisfiable (parity argument). -/
theorem cycle_odd_unsat (n : Nat) (h : n % 2 = 1) : ¬ SatSys (cycle n) := by
  intro ⟨x, hx⟩
  have hn : n - 1 < n := by omega
  have halt := (solution_alternates n x hx (n - 1) hn).mpr (by omega)
  have hc := hx (n - 1, (n - 1 + 1) % n) ((mem_cycle n _).mpr ⟨n - 1, hn, rfl⟩)
  rw [succ_mod_of_eq (n - 1) n (by omega)] at hc
  exact hc halt

/-- The XOR cycle is satisfiable exactly for even length. -/
theorem cycle_sat_iff (n : Nat) : SatSys (cycle n) ↔ n % 2 = 0 := by
  constructor
  · intro hs
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact h
    · exact absurd hs (cycle_odd_unsat n h)
  · exact cycle_even_sat n

/-! ## Every proper piece of the cycle is satisfiable -/

/-- Alternating assignment that "breaks" the cycle after position `j`
(used for odd `n`). -/
def pathAssign (j : Nat) (i : Nat) : Bool := if i ≤ j then par i else par (i + 1)

/-- Removing the constraint at position `j` leaves a satisfiable system. -/
theorem path_sat (n j : Nat) (hj : j < n) :
    ∃ x : Nat → Bool, ∀ i, i < n → i ≠ j → x i ≠ x ((i + 1) % n) := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · obtain ⟨x, hx⟩ := cycle_even_sat n hn
    exact ⟨x, fun i hi _ => hx (i, (i + 1) % n) ((mem_cycle n _).mpr ⟨i, hi, rfl⟩)⟩
  · refine ⟨pathAssign j, fun i hi hij => ?_⟩
    by_cases hlt : i + 1 < n
    · rw [succ_mod_of_lt i n hlt]
      unfold pathAssign
      by_cases h1 : i < j
      · rw [ite_eq_left (by omega : i ≤ j), ite_eq_left (by omega : i + 1 ≤ j)]
        exact par_ne_succ i
      · rw [ite_eq_right (by omega : ¬ i ≤ j), ite_eq_right (by omega : ¬ i + 1 ≤ j)]
        exact par_ne_succ (i + 1)
    · rw [succ_mod_of_eq i n (by omega)]
      unfold pathAssign
      rw [ite_eq_right (by omega : ¬ i ≤ j), ite_eq_left (Nat.zero_le j)]
      have h1 : par (i + 1) = true := by
        cases hp : par (i + 1) with
        | true => rfl
        | false => have := (par_eq_false_iff (i + 1)).mp hp; omega
      rw [h1]; decide

/-- Any subsystem of the cycle that misses one of its constraints is
satisfiable. -/
theorem missing_constraint_sat (n : Nat) (S : System) (hS : ∀ p ∈ S, p ∈ cycle n)
    (hmiss : ∃ j, j < n ∧ (j, (j + 1) % n) ∉ S) : SatSys S := by
  obtain ⟨j, hj, hjS⟩ := hmiss
  obtain ⟨x, hx⟩ := path_sat n j hj
  refine ⟨x, fun p hp => ?_⟩
  obtain ⟨i, hi, rfl⟩ := (mem_cycle n p).mp (hS p hp)
  have hij : i ≠ j := by
    intro h; subst h; exact hjS hp
  exact hx i hi hij

/-- Every subsystem with fewer than `n` constraints misses a constraint of the
cycle (pigeonhole over the `n` distinct first components). -/
theorem short_subsystem_misses (n : Nat) (S : System) (hlen : S.length < n) :
    ∃ j, j < n ∧ (j, (j + 1) % n) ∉ S := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ j, j < n → (j, (j + 1) % n) ∈ S := fun j hj =>
    Classical.byContradiction fun hj' => hno ⟨j, hj, hj'⟩
  have hsub : List.range n ⊆ S.map Prod.fst := by
    intro j hj
    have hj' := List.mem_range.mp hj
    exact List.mem_map.mpr ⟨(j, (j + 1) % n), hall j hj', rfl⟩
  have := List.Nodup.length_le_of_subset List.nodup_range hsub
  rw [List.length_range, List.length_map] at this
  omega

/-- Every subsystem of the cycle with fewer than `n` constraints is
satisfiable. -/
theorem short_subsystem_sat (n : Nat) (S : System) (hS : ∀ p ∈ S, p ∈ cycle n)
    (hlen : S.length < n) : SatSys S :=
  missing_constraint_sat n S hS (short_subsystem_misses n S hlen)

/-! ## Local consistency -/

/-- `k`-local consistency: every subsystem of at most `k` constraints (taken
from `sys`) is satisfiable. -/
def LocallyConsistent (k : Nat) (sys : System) : Prop :=
  ∀ S : System, (∀ p ∈ S, p ∈ sys) → S.length ≤ k → SatSys S

theorem locallyConsistent_mono (k k' : Nat) (sys : System) (h : k' ≤ k)
    (hk : LocallyConsistent k sys) : LocallyConsistent k' sys :=
  fun S hS hlen => hk S hS (Nat.le_trans hlen h)

/-- Odd cycles are `(n-1)`-locally consistent and unsatisfiable. -/
theorem odd_cycle_locally_consistent (n : Nat) (h : n % 2 = 1) :
    LocallyConsistent (n - 1) (cycle n) ∧ ¬ SatSys (cycle n) :=
  ⟨fun S hS hlen => short_subsystem_sat n S hS (by omega), cycle_odd_unsat n h⟩

/-- No bound `k` on the size of inspected subsystems suffices: for every `k`
there is an unsatisfiable, `k`-locally consistent system. -/
theorem local_consistency_insufficient (k : Nat) :
    ∃ sys : System, LocallyConsistent k sys ∧ ¬ SatSys sys := by
  have h := odd_cycle_locally_consistent (2 * k + 1) (by omega)
  exact ⟨cycle (2 * k + 1), locallyConsistent_mono _ k _ (by omega) h.1, h.2⟩

/-- Consequently, "`k`-locally consistent ⇒ satisfiable" is false for every
`k`. -/
theorem no_local_to_global (k : Nat) :
    ¬ (∀ sys : System, LocallyConsistent k sys → SatSys sys) := by
  intro hall
  obtain ⟨sys, hloc, hunsat⟩ := local_consistency_insufficient k
  exact hunsat (hall sys hloc)

/-! ## The same systems as 2-CNF formulas -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause

def evalLit (a : Nat → Bool) (l : Lit) : Bool := a l.var == l.pos

def evalClause (a : Nat → Bool) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Nat → Bool) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a : Nat → Bool, evalCNF a φ = true

/-- `x_i ≠ x_j` as the two clauses `(x_i ∨ x_j) ∧ (¬x_i ∨ ¬x_j)`. -/
def sysCNF : System → CNF
  | [] => []
  | (i, j) :: s => [⟨i, true⟩, ⟨j, true⟩] :: [⟨i, false⟩, ⟨j, false⟩] :: sysCNF s

/-- The 2-CNF translation is exact, assignment by assignment. -/
theorem sysCNF_iff (x : Nat → Bool) (sys : System) :
    evalCNF x (sysCNF sys) = true ↔ Solves x sys := by
  induction sys with
  | nil => simp [sysCNF, evalCNF, Solves]
  | cons p s ih =>
    obtain ⟨i, j⟩ := p
    simp only [sysCNF, evalCNF, evalClause, evalLit, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · show x i ≠ x j
        cases hi : x i <;> cases hj : x j <;> simp_all
      · exact h3 q hq
    · intro h
      have hij : x i ≠ x j := h (i, j) (List.mem_cons_self ..)
      refine ⟨?_, ?_, fun q hq => h q (List.mem_cons_of_mem _ hq)⟩ <;>
        cases hi : x i <;> cases hj : x j <;> simp_all

/-- The 2-CNF form of the XOR cycle is satisfiable iff `n` is even. -/
theorem cycleCNF_sat_iff (n : Nat) : Satisfiable (sysCNF (cycle n)) ↔ n % 2 = 0 := by
  rw [← cycle_sat_iff]
  constructor
  · intro ⟨x, hx⟩; exact ⟨x, (sysCNF_iff x _).mp hx⟩
  · intro ⟨x, hx⟩; exact ⟨x, (sysCNF_iff x _).mpr hx⟩

end Issue532.Idea04
