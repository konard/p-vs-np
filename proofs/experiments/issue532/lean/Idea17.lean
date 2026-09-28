import proofs.experiments.issue532.lean.Machines
import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue #532, Idea 17: enumeration accounting (exponential versus polynomial)

This file makes the accounting of exhaustive search exact and general.

* `allVecs n` enumerates all Boolean vectors of length `n`.  We prove, for
  every `n`, that it has length `2 ^ n` (`allVecs_length`), contains no
  duplicates (`allVecs_nodup`) and contains every vector of length `n` and
  nothing else (`mem_allVecs`).
* `bruteForce f n` searches that list.  It is correct for every predicate and
  every `n` (`bruteForce_correct`), and on a predicate with no witness it
  examines exactly `2 ^ n` candidates (`searchCost_no_witness`).
* The growth theorem `exp_beats_poly` states that for all `c k` there is an
  explicit threshold `N` (namely `2 ^ (2 * (c + k) + 1)`) such that
  `c * (n + 1) ^ k < 2 ^ n` for every `n ≥ N`.  The left-hand side is exactly
  the repository's `Complexity.Polynomial.eval` (coefficient `c`, degree `k`);
  `polyEval_eq` records the identification.
* Consequently no polynomial bounds the number of candidates of exhaustive
  enumeration (`enumeration_not_polynomial`).

Verdict: the accounting is correct and exhaustive enumeration is refuted as a
polynomial-time method in general.  The file also proves
(`enumeration_cost_is_not_problem_cost`) that the exponential cost of
enumeration says nothing about the difficulty of the problem itself: for the
unsatisfiable predicate, enumeration costs `2 ^ n` while a fixed-answer procedure
answers correctly.  A lower bound for a problem must quantify over all
algorithms.

The abstract schema `AllAlgorithmsSuperpolynomialFor M` quantifies over the
algorithms of an arbitrary `AlgorithmModel`.  It is instantiated on the shared
machine model by `machineModel L`: the algorithms are `Complexity.Machine`s
that halt with the answer `L x` on every input, and the cost at length `n` is
the worst `Complexity.Run` step count over the `2 ^ n` inputs of length `n`
(`worstTime`, computed with the same enumeration `allVecs`).  On this model the
schema is *exactly* `¬ InP L` (`allMachinesSuperpolynomial_iff_not_inP`), so:

* the open obligation is `SATMachinesSuperpolynomial` (every total machine
  decider for `Issue532.Machines.SAT` has superpolynomial worst-case step
  count), and it is equivalent to `¬ InP SAT`;
* with `SATInNP` it implies `PNotEqualsNP`
  (`pNotEqualsNP_of_satMachinesSuperpolynomial`); `SATInNP` is proved in
  `SATVerifier.lean` (`SATVerifier.satInNP`), so
  `pNotEqualsNP_of_satMachinesSuperpolynomial'` drops that premise; with `CookLevin` it is
  equivalent to `PNotEqualsNP` (`satMachinesSuperpolynomial_iff_pNotEqualsNP`);
* the statement is not vacuous: it holds for the diagonal language
  `Issue532.Machines.Diag` and fails for the constant-false language, whose
  one-step machine has worst-case cost `1` at every length
  (`worstTime_emptyMachine`), the machine-level form of
  `enumeration_cost_is_not_problem_cost`.

Nothing here proves the obligation.
-/

namespace Issue532.Idea17

open Complexity
open Issue532.Machines (DecidesWithin run_deterministic inP_of_decidesWithin Diag diag_not_inP
  SAT SATInNP CookLevin inP_sat_iff inP_sat_of_pEqualsNP)

/-! ## Enumeration of Boolean vectors -/

/-- All Boolean vectors of length `n`, false-branch first. -/
def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).map (List.cons false) ++ (allVecs n).map (List.cons true)

/-- The enumeration has exactly `2 ^ n` entries, for every `n`. -/
theorem allVecs_length (n : Nat) : (allVecs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allVecs, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

/-- Membership: a vector occurs in `allVecs n` iff it has length `n`. -/
theorem mem_allVecs (n : Nat) (v : List Bool) : v ∈ allVecs n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    constructor
    · intro h
      simp [allVecs] at h
      subst h
      rfl
    · intro h
      cases v with
      | nil => simp [allVecs]
      | cons _ _ => simp at h
  | succ n ih =>
    constructor
    · intro h
      simp only [allVecs, List.mem_append, List.mem_map] at h
      rcases h with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
      · simp [(ih w).mp hw]
      · simp [(ih w).mp hw]
    · intro h
      cases v with
      | nil => simp at h
      | cons b w =>
        have hw : w ∈ allVecs n := (ih w).mpr (by simp at h; exact h)
        simp only [allVecs, List.mem_append, List.mem_map]
        cases b with
        | false => exact Or.inl ⟨w, hw, rfl⟩
        | true => exact Or.inr ⟨w, hw, rfl⟩

/-- Helper: mapping `cons b` preserves duplicate-freeness. -/
theorem nodup_map_cons (b : Bool) (l : List (List Bool)) (h : l.Nodup) :
    (l.map (List.cons b)).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨y, hy, hyx⟩ := hm
    have : y = x := by injection hyx
    subst this
    exact h.1 hy

/-- The enumeration contains no duplicates, for every `n`. -/
theorem allVecs_nodup (n : Nat) : (allVecs n).Nodup := by
  induction n with
  | zero => simp [allVecs]
  | succ n ih =>
    simp only [allVecs]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons false _ ih, nodup_map_cons true _ ih, ?_⟩
    intro a ha b hb hab
    rw [List.mem_map] at ha hb
    obtain ⟨x, _, rfl⟩ := ha
    obtain ⟨y, _, rfl⟩ := hb
    injection hab with h1 _
    cases h1

/-! ## Brute-force search and its exact cost -/

/-- Brute force: does some vector of length `n` satisfy `f`? -/
def bruteForce (f : List Bool → Bool) (n : Nat) : Bool := (allVecs n).any f

/-- Brute force is correct for every predicate and every length. -/
theorem bruteForce_correct (f : List Bool → Bool) (n : Nat) :
    bruteForce f n = true ↔ ∃ v, v.length = n ∧ f v = true := by
  unfold bruteForce
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hf⟩
    exact ⟨v, (mem_allVecs n v).mp hv, hf⟩
  · rintro ⟨v, hv, hf⟩
    exact ⟨v, (mem_allVecs n v).mpr hv, hf⟩

/-- Number of candidates examined by a left-to-right search that stops at the
first success (the successful candidate is counted). -/
def searchCost (f : List Bool → Bool) : List (List Bool) → Nat
  | [] => 0
  | v :: vs => if f v then 1 else 1 + searchCost f vs

/-- With no witness, the search examines every candidate. -/
theorem searchCost_all_false (f : List Bool → Bool) (l : List (List Bool))
    (h : ∀ v ∈ l, f v = false) : searchCost f l = l.length := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    have hv : f v = false := h v (by simp)
    simp only [searchCost, hv, List.length_cons]
    have := ih (fun w hw => h w (by simp [hw]))
    simp at this ⊢
    omega

/-- Worst case of enumeration: on a predicate with no witness of length `n`,
exhaustive search examines exactly `2 ^ n` candidates. -/
theorem searchCost_no_witness (f : List Bool → Bool) (n : Nat)
    (h : ∀ v, v.length = n → f v = false) : searchCost f (allVecs n) = 2 ^ n := by
  rw [searchCost_all_false f _ (fun v hv => h v ((mem_allVecs n v).mp hv)), allVecs_length]

/-! ## Exponential beats every polynomial -/

/-- Mirror of `Complexity.Polynomial.eval` from
`proofs/complexity/lean/Complexity.lean`: coefficient `c`, degree `k`. -/
def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

/-- `polyEval` is the repository's `Polynomial.eval`. -/
theorem polyEval_eq (c k n : Nat) : polyEval c k n = (Polynomial.mk c k).eval n := rfl

theorem succ_le_two_pow (q : Nat) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.pow_succ]; omega

theorem lt_two_pow_self (a : Nat) : a < 2 ^ a := by
  have := succ_le_two_pow a
  omega

/-- Linear versus exponential: `a * (q + 1) < 2 ^ q` whenever `q ≥ 2a + 1`. -/
theorem linear_lt_exp (a q : Nat) (hq : 2 * a + 1 ≤ q) : a * (q + 1) < 2 ^ q := by
  obtain ⟨d, rfl⟩ : ∃ d, q = 2 * a + 1 + d := ⟨q - (2 * a + 1), by omega⟩
  induction d with
  | zero =>
    -- a * (2a + 2) = a * (2 * (a + 1)) ≤ a * (2 * 2 ^ a) < 2 ^ a * (2 * 2 ^ a)
    have h1 : a + 1 ≤ 2 ^ a := succ_le_two_pow a
    have h2 : a < 2 ^ a := lt_two_pow_self a
    have e : 2 ^ (2 * a + 1 + 0) = 2 ^ a * (2 * 2 ^ a) := by
      rw [show 2 * a + 1 + 0 = a + (a + 1) by omega, Nat.pow_add, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ a) 2]
    rw [e, show 2 * a + 1 + 0 + 1 = 2 * (a + 1) by omega]
    have h3 : 2 * (a + 1) ≤ 2 * 2 ^ a := by omega
    have hpos : 0 < 2 * 2 ^ a := by omega
    calc a * (2 * (a + 1)) ≤ a * (2 * 2 ^ a) := Nat.mul_le_mul_left a h3
      _ < 2 ^ a * (2 * 2 ^ a) := Nat.mul_lt_mul_of_pos_right h2 hpos
  | succ d ih =>
    have ih := ih (by omega)
    have ha : a ≤ a * (2 * a + 1 + d + 1) := Nat.le_mul_of_pos_right a (by omega)
    rw [show 2 * a + 1 + (d + 1) = (2 * a + 1 + d) + 1 by omega, Nat.pow_succ,
      Nat.mul_add, Nat.mul_one]
    omega

/-- Every positive `n` lies in a dyadic bracket `2 ^ L ≤ n < 2 ^ (L + 1)`. -/
theorem dyadic_bracket (n : Nat) (hn : 1 ≤ n) : ∃ L, 2 ^ L ≤ n ∧ n < 2 ^ (L + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  induction d with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ d ih =>
    obtain ⟨L, h1, h2⟩ := ih (by omega)
    by_cases h : 1 + (d + 1) < 2 ^ (L + 1)
    · exact ⟨L, by omega, h⟩
    · refine ⟨L + 1, by omega, ?_⟩
      rw [Nat.pow_succ 2 (L + 1)]
      omega

/-- **Growth theorem.** For all `c k` and all `n ≥ 2 ^ (2 * (c + k) + 1)`,
`c * (n + 1) ^ k < 2 ^ n`.  Hence `2 ^ n` eventually exceeds every polynomial
of the repository's form `Polynomial.eval`. -/
theorem exp_beats_poly (c k : Nat) :
    ∀ n, 2 ^ (2 * (c + k) + 1) ≤ n → polyEval c k n < 2 ^ n := by
  intro n hn
  unfold polyEval
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.one_le_two_pow) hn
  obtain ⟨L, hL1, hL2⟩ := dyadic_bracket n hn1
  -- the bracket exponent is large
  have hLbig : 2 * (c + k) + 1 ≤ L := by
    apply Classical.byContradiction
    intro hlt
    have : 2 ^ (L + 1) ≤ 2 ^ (2 * (c + k) + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- linear-versus-exponential at L
  have hlin : (c + k) * (L + 1) < 2 ^ L := linear_lt_exp (c + k) L hLbig
  have hsum : c + k * (L + 1) < n := by
    have : c + k * (L + 1) ≤ (c + k) * (L + 1) := by
      rw [Nat.add_mul]
      have : c ≤ c * (L + 1) := Nat.le_mul_of_pos_right c (by omega)
      omega
    omega
  -- (n + 1) ^ k ≤ 2 ^ (k * (L + 1))
  have hbase : (n + 1) ^ k ≤ 2 ^ ((L + 1) * k) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) k
  have hc : c < 2 ^ c := lt_two_pow_self c
  have hpos : 0 < 2 ^ ((L + 1) * k) := Nat.two_pow_pos _
  calc c * (n + 1) ^ k ≤ c * 2 ^ ((L + 1) * k) := Nat.mul_le_mul_left c hbase
    _ < 2 ^ c * 2 ^ ((L + 1) * k) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (c + (L + 1) * k) := (Nat.pow_add 2 c _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)

/-- Existential form requested in the plan: some threshold works for all larger `n`. -/
theorem exists_threshold (c k : Nat) : ∃ N, ∀ n, N ≤ n → c * (n + 1) ^ k < 2 ^ n :=
  ⟨2 ^ (2 * (c + k) + 1), exp_beats_poly c k⟩

/-- **Exhaustive enumeration is not polynomial.** For every polynomial
`c * (n + 1) ^ k` there is a threshold beyond which the enumeration of
length-`n` vectors is strictly longer, and so is the worst-case brute-force
search cost on a predicate with no witness. -/
theorem enumeration_not_polynomial (c k : Nat) :
    ∃ N, ∀ n, N ≤ n →
      polyEval c k n < (allVecs n).length ∧
      polyEval c k n < searchCost (fun _ => false) (allVecs n) := by
  refine ⟨2 ^ (2 * (c + k) + 1), fun n hn => ?_⟩
  have h := exp_beats_poly c k n hn
  rw [allVecs_length, searchCost_no_witness (fun _ => false) n (fun _ _ => rfl)]
  exact ⟨h, h⟩

/-! ## What the accounting does *not* show -/

/-- **Enumeration cost is not problem cost.**  For the predicate with no
witness, exhaustive search costs `2 ^ n` candidates at every length, yet the
always-`false` procedure answers the same question correctly at every
length.  So an exponential enumeration count is never, by itself, a lower
bound for the underlying decision problem (COMMON_ERRORS family 1). -/
theorem enumeration_cost_is_not_problem_cost (n : Nat) :
    searchCost (fun _ => false) (allVecs n) = 2 ^ n ∧
    (bruteForce (fun _ => false) n = (fun _ => false) n) := by
  refine ⟨searchCost_no_witness _ n (fun _ _ => rfl), ?_⟩
  cases h : bruteForce (fun _ => false) n with
  | false => rfl
  | true =>
    obtain ⟨_, _, hv⟩ := (bruteForce_correct _ n).mp h
    cases hv

/-- An abstract algorithm model: each algorithm has a correctness predicate
and a worst-case cost at each input length. -/
structure AlgorithmModel where
  Alg : Type
  correct : Alg → Prop
  cost : Alg → Nat → Nat

/-- A correct algorithm is polynomially bounded if its cost is bounded by some
`c * (n + 1) ^ k` at every length. -/
def PolyBounded (M : AlgorithmModel) (A : M.Alg) : Prop :=
  ∃ c k, ∀ n, M.cost A n ≤ polyEval c k n

/-- Schema (the shape of a lower-bound statement over an arbitrary model).
Every correct algorithm in the model has super-polynomial cost: for each
polynomial there are arbitrarily large lengths where the cost exceeds it.  The
model `M` is a parameter, so this is a schema, not a claim; its instance on the
shared machine model is `SATMachinesSuperpolynomial` below. -/
def AllAlgorithmsSuperpolynomialFor (M : AlgorithmModel) : Prop :=
  ∀ A, M.correct A → ∀ c k N, ∃ n, N ≤ n ∧ polyEval c k n < M.cost A n

/-- Conditional: the obligation excludes every polynomially bounded correct
algorithm.  (Its content is entirely in the hypothesis.) -/
theorem superpolynomial_excludes_poly (M : AlgorithmModel)
    (h : AllAlgorithmsSuperpolynomialFor M) : ∀ A, M.correct A → ¬ PolyBounded M A := by
  intro A hA hpoly
  obtain ⟨c, k, hb⟩ := hpoly
  obtain ⟨n, _, hn⟩ := h A hA c k 0
  have := hb n
  omega

/-- The single-algorithm fact proved above does not discharge the obligation:
a model containing brute force *and* an O(1)-time correct algorithm has a
super-polynomial member but is not `AllAlgorithmsSuperpolynomialFor`. -/
def twoAlgModel : AlgorithmModel where
  Alg := Bool            -- `false` = brute force, `true` = fixed answer
  correct := fun _ => True
  cost := fun a n => if a then 1 else 2 ^ n

theorem one_slow_algorithm_is_not_a_lower_bound :
    (∀ c k N, ∃ n, N ≤ n ∧ polyEval c k n < twoAlgModel.cost false n) ∧
    ¬ AllAlgorithmsSuperpolynomialFor twoAlgModel := by
  constructor
  · intro c k N
    refine ⟨N + 2 ^ (2 * (c + k) + 1), Nat.le_add_right _ _, ?_⟩
    exact exp_beats_poly c k _ (Nat.le_add_left _ _)
  · intro h
    obtain ⟨n, _, hn⟩ := h true trivial 1 0 0
    simp [twoAlgModel, polyEval] at hn

/-! ## The schema on the shared machine model -/

/-- `m` halts with the answer `L x` on every input (no time bound). -/
def TotalDecider (m : Machine) (L : Language) : Prop :=
  ∀ x, ∃ t, Run m (initial x) t (L x)

open Classical in
/-- The `Complexity.Run` step count of `m` on input `x` (`0` if `m` never halts
on `x`; runs are unique by `run_deterministic`). -/
noncomputable def runTime (m : Machine) (x : Word) : Nat :=
  if h : ∃ t b, Run m (initial x) t b then Classical.choose h else 0

theorem runTime_eq {m : Machine} {x : Word} {t : Nat} {b : Bool}
    (hr : Run m (initial x) t b) : runTime m x = t := by
  have h : ∃ t b, Run m (initial x) t b := ⟨t, b, hr⟩
  unfold runTime
  split
  · rename_i h'
    obtain ⟨b', hb'⟩ := Classical.choose_spec h'
    exact (run_deterministic hb' hr).1
  · contradiction

/-- Worst-case step count of `m` over the `2 ^ n` inputs of length `n`,
computed over the enumeration `allVecs n`. -/
noncomputable def worstTime (m : Machine) (n : Nat) : Nat :=
  ((allVecs n).map (runTime m)).foldr max 0

theorem le_foldr_max (l : List Nat) (a : Nat) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_le (l : List Nat) (B : Nat) (h : ∀ a ∈ l, a ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons y l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h y (by simp), ih (fun a ha => h a (by simp [ha]))⟩

theorem runTime_le_worstTime (m : Machine) (x : Word) : runTime m x ≤ worstTime m x.length :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨x, (mem_allVecs _ x).mpr rfl, rfl⟩)

theorem worstTime_le (m : Machine) (n B : Nat) (h : ∀ x : Word, x.length = n → runTime m x ≤ B) :
    worstTime m n ≤ B := by
  apply foldr_max_le
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact h x ((mem_allVecs n x).mp hx)

/-- The shared machine model as an `AlgorithmModel` for the language `L`:
algorithms are machines that decide `L` on every input, and the cost at length
`n` is the worst-case `Run` step count over inputs of length `n`. -/
noncomputable def machineModel (L : Language) : AlgorithmModel where
  Alg := Machine
  correct := fun m => TotalDecider m L
  cost := worstTime

/-- **On the machine model the schema is exactly "not in P".** -/
theorem allMachinesSuperpolynomial_iff_not_inP (L : Language) :
    AllAlgorithmsSuperpolynomialFor (machineModel L) ↔ ¬ InP L := by
  constructor
  · intro h hP
    obtain ⟨m, p, hd⟩ := (Issue532.Machines.polyDec_iff_inP L).mpr hP
    have hm : TotalDecider m L := fun x => by
      obtain ⟨t, b, _, hr, hb⟩ := hd x
      exact ⟨t, hb ▸ hr⟩
    obtain ⟨n, _, hn⟩ := h m hm p.coefficient p.degree 0
    have hle : worstTime m n ≤ p.eval n := by
      apply worstTime_le
      intro x hx
      obtain ⟨t, b, ht, hr, _⟩ := hd x
      rw [runTime_eq hr, ← hx]
      exact ht
    have : polyEval p.coefficient p.degree n = p.eval n := rfl
    change polyEval p.coefficient p.degree n < worstTime m n at hn
    omega
  · intro hnot m hm c k N
    apply Classical.byContradiction
    intro hno
    have hbig : ∀ n, N ≤ n → worstTime m n ≤ polyEval c k n := by
      intro n hn
      apply Classical.byContradiction
      intro hlt
      exact hno ⟨n, hn, by change polyEval c k n < worstTime m n; omega⟩
    let B := ((List.range N).map (worstTime m)).foldr max 0
    have hall : ∀ n, worstTime m n ≤ (B + c) * (n + 1) ^ k := by
      intro n
      have hpos : 0 < (n + 1) ^ k := Nat.pow_pos (Nat.succ_pos n)
      rw [Nat.add_mul]
      by_cases hn : N ≤ n
      · have := hbig n hn
        unfold polyEval at this
        omega
      · have h1 : worstTime m n ≤ B :=
          le_foldr_max _ _ (List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩)
        have h2 : B ≤ B * (n + 1) ^ k := Nat.le_mul_of_pos_right B hpos
        omega
    apply hnot
    apply inP_of_decidesWithin (m := m) (p := ⟨B + c, k⟩)
    intro x
    obtain ⟨t, hr⟩ := hm x
    refine ⟨t, L x, ?_, hr, rfl⟩
    have := runTime_le_worstTime m x
    rw [runTime_eq hr] at this
    exact Nat.le_trans this (hall x.length)

/-- **Open obligation** (the lower bound for SAT on the shared machine model).
Every `Complexity.Machine` that halts with the answer `SAT x` on every input has,
for each polynomial `c * (n + 1) ^ k`, arbitrarily large lengths `n` at which its
worst-case `Run` step count over inputs of length `n` exceeds the polynomial.
Equivalent to `¬ InP SAT` (`satMachinesSuperpolynomial_iff_not_inP`). -/
def SATMachinesSuperpolynomial : Prop :=
  ∀ m : Machine, TotalDecider m SAT → ∀ c k N, ∃ n, N ≤ n ∧ polyEval c k n < worstTime m n

/-- The obligation is the schema instantiated on the machine model for SAT. -/
theorem satMachinesSuperpolynomial_iff_for :
    SATMachinesSuperpolynomial ↔ AllAlgorithmsSuperpolynomialFor (machineModel SAT) := Iff.rfl

theorem satMachinesSuperpolynomial_iff_not_inP : SATMachinesSuperpolynomial ↔ ¬ InP SAT :=
  allMachinesSuperpolynomial_iff_not_inP SAT

/-- **Conditional theorem.** With `SATInNP`, the obligation gives P ≠ NP. -/
theorem pNotEqualsNP_of_satMachinesSuperpolynomial (mem : SATInNP)
    (h : SATMachinesSuperpolynomial) : PNotEqualsNP := fun hPNP =>
  satMachinesSuperpolynomial_iff_not_inP.mp h (inP_sat_of_pEqualsNP mem hPNP)

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem pNotEqualsNP_of_satMachinesSuperpolynomial' (h : SATMachinesSuperpolynomial) :
    PNotEqualsNP :=
  pNotEqualsNP_of_satMachinesSuperpolynomial SATVerifier.satInNP h

/-- With the Cook–Levin hypothesis the obligation is equivalent to P ≠ NP. -/
theorem satMachinesSuperpolynomial_iff_pNotEqualsNP (hCL : CookLevin) :
    SATMachinesSuperpolynomial ↔ PNotEqualsNP := by
  rw [satMachinesSuperpolynomial_iff_not_inP, inP_sat_iff hCL]
  exact Iff.rfl

/-! ## Non-vacuity on the machine model -/

/-- The machine with no instructions halts with `false` after one step. -/
theorem emptyMachine_run (x : Word) : Run ⟨[]⟩ (initial x) 1 false := Run.halt rfl

theorem emptyMachine_totalDecider : TotalDecider ⟨[]⟩ (fun _ => false) :=
  fun x => ⟨1, emptyMachine_run x⟩

/-- Machine form of `enumeration_cost_is_not_problem_cost`: the constant-false
language, whose brute-force search costs `2 ^ n`, has a machine decider with
worst-case cost `1` at every length. -/
theorem worstTime_emptyMachine (n : Nat) : worstTime ⟨[]⟩ n = 1 := by
  apply Nat.le_antisymm
  · exact worstTime_le _ n 1 (fun x _ => by rw [runTime_eq (emptyMachine_run x)]; exact Nat.le_refl 1)
  · have := runTime_le_worstTime ⟨[]⟩ (List.replicate n false)
    rw [runTime_eq (emptyMachine_run _), List.length_replicate] at this
    exact this

theorem inP_const_false : InP (fun _ => false) :=
  inP_of_decidesWithin (m := ⟨[]⟩) (p := ⟨1, 0⟩)
    (fun x => ⟨1, false, by simp [Polynomial.eval], emptyMachine_run x, rfl⟩)

/-- Non-vacuity, false side: the machine-model statement fails for the
constant-false language. -/
theorem const_false_not_superpolynomial :
    ¬ AllAlgorithmsSuperpolynomialFor (machineModel (fun _ => false)) := fun h =>
  (allMachinesSuperpolynomial_iff_not_inP _).mp h inP_const_false

/-- Non-vacuity, true side: the machine-model statement holds for the diagonal
language `Diag`, which is outside P. -/
theorem diag_superpolynomial : AllAlgorithmsSuperpolynomialFor (machineModel Diag) :=
  (allMachinesSuperpolynomial_iff_not_inP Diag).mpr diag_not_inP

/-- The shape of `SATMachinesSuperpolynomial` is satisfiable and refutable. -/
theorem machine_schema_nontrivial :
    (∃ L, AllAlgorithmsSuperpolynomialFor (machineModel L)) ∧
    (∃ L, ¬ AllAlgorithmsSuperpolynomialFor (machineModel L)) :=
  ⟨⟨Diag, diag_superpolynomial⟩, ⟨_, const_false_not_superpolynomial⟩⟩

end Issue532.Idea17
