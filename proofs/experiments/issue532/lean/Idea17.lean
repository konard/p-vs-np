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
  the repository's `Complexity.Polynomial.eval` (coefficient `c`, degree `k`),
  mirrored locally as `polyEval` to keep this file standalone.
* Consequently no polynomial bounds the number of candidates of exhaustive
  enumeration (`enumeration_not_polynomial`).

Verdict: the accounting is correct and exhaustive enumeration is refuted as a
polynomial-time method in general.  The file also proves
(`enumeration_cost_is_not_problem_cost`) that the exponential cost of
enumeration says nothing about the difficulty of the problem itself: for the
unsatisfiable predicate, enumeration costs `2 ^ n` while a fixed-answer procedure
answers correctly.  A lower bound for a problem must quantify over all
algorithms; that obligation is recorded as `AllAlgorithmsSuperpolynomial`
and is not proved here.
-/

namespace Issue532.Idea17

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

/-- Local mirror of `Complexity.Polynomial.eval` from
`proofs/complexity/lean/Complexity.lean`: coefficient `c`, degree `k`. -/
def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

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

/-- **Open obligation** (the real lower-bound statement).  Every correct
algorithm in the model has super-polynomial cost: for each polynomial there are
arbitrarily large lengths where the cost exceeds it.  With `M` instantiated by
polynomial-time deterministic machines deciding SAT, this is P ≠ NP.  It is a
definition, not an assumption; nothing here proves it. -/
def AllAlgorithmsSuperpolynomial (M : AlgorithmModel) : Prop :=
  ∀ A, M.correct A → ∀ c k N, ∃ n, N ≤ n ∧ polyEval c k n < M.cost A n

/-- Conditional: the obligation excludes every polynomially bounded correct
algorithm.  (Its content is entirely in the hypothesis.) -/
theorem superpolynomial_excludes_poly (M : AlgorithmModel)
    (h : AllAlgorithmsSuperpolynomial M) : ∀ A, M.correct A → ¬ PolyBounded M A := by
  intro A hA hpoly
  obtain ⟨c, k, hb⟩ := hpoly
  obtain ⟨n, _, hn⟩ := h A hA c k 0
  have := hb n
  omega

/-- The single-algorithm fact proved above does not discharge the obligation:
a model containing brute force *and* an O(1)-time correct algorithm has a
super-polynomial member but is not `AllAlgorithmsSuperpolynomial`. -/
def twoAlgModel : AlgorithmModel where
  Alg := Bool            -- `false` = brute force, `true` = fixed answer
  correct := fun _ => True
  cost := fun a n => if a then 1 else 2 ^ n

theorem one_slow_algorithm_is_not_a_lower_bound :
    (∀ c k N, ∃ n, N ≤ n ∧ polyEval c k n < twoAlgModel.cost false n) ∧
    ¬ AllAlgorithmsSuperpolynomial twoAlgModel := by
  constructor
  · intro c k N
    refine ⟨N + 2 ^ (2 * (c + k) + 1), Nat.le_add_right _ _, ?_⟩
    exact exp_beats_poly c k _ (Nat.le_add_left _ _)
  · intro h
    obtain ⟨n, _, hn⟩ := h true trivial 1 0 0
    simp [twoAlgModel, polyEval] at hn

end Issue532.Idea17
