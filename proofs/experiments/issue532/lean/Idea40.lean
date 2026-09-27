/-!
# Issue #532, Idea 40: size-uniform invariant (induction with resource bounds)

"Induction on the input size" proves correctness of a recursive algorithm, but its
running time depends on how the cost grows from size `n` to size `n + 1`. This
file proves both sides in general.

* `tested`: the induction principle used for correctness invariants.
* `additive_bound`: if `T 0 ≤ c` and `T (n+1) ≤ T n + q n` with `q` monotone, then
  `T n ≤ c + n · q n`. With `q n = a · (n+1)^k` this gives
  `T n ≤ (c + a) · (n+1)^(k+1)` (`additive_poly`).
* `doubling_exact`: `T 0 = 1` and `T (n+1) = 2 · T n` give `T n = 2^n`.
  `branching_lower`: `T 0 ≥ 1` and `T (n+1) ≥ 2 · T n` give `T n ≥ 2^n`.
* `poly_lt_two_pow`: for all `c k` there is `n` with `c · (n+1)^k < 2^n`
  (standalone proof). Hence `branching_not_poly`: a branching recurrence is not
  polynomially bounded, and `branchCost_exponential` covers the
  "try both values of a variable" self-reduction.
* `run_correct`, `runCost_bound`, `obligation_gives_poly_solver`: a self-reduction
  with **one** recursive call of the same answer and polynomial step cost yields a
  correct polynomial-cost solver. `AdditiveSelfReduction` states this as the open
  obligation; for SAT it would give P = NP.

Verdict: correct tool, insufficient alone. Induction yields a polynomial algorithm
only when each step adds, rather than multiplies, polynomial cost.
-/

namespace Issue532.Idea40

/-- **Induction principle for correctness invariants** (old `tested`). -/
theorem tested (P : Nat → Prop) (base : P 0)
    (step : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact step n ih

/-! ## (a) Additive recurrences are polynomial -/

/-- **Additive recurrence.** `T 0 ≤ c` and `T (n+1) ≤ T n + q n` with `q` monotone give
`T n ≤ c + n · q n`. -/
theorem additive_bound (T q : Nat → Nat) (c : Nat) (h0 : T 0 ≤ c)
    (hstep : ∀ n, T (n + 1) ≤ T n + q n) (hmono : ∀ m n, m ≤ n → q m ≤ q n) :
    ∀ n, T n ≤ c + n * q n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := hstep n
    have h2 : q n ≤ q (n + 1) := hmono n (n + 1) (Nat.le_succ n)
    have h3 : n * q n ≤ n * q (n + 1) := Nat.mul_le_mul_left n h2
    have h4 : (n + 1) * q (n + 1) = n * q (n + 1) + q (n + 1) := Nat.succ_mul n _
    omega

/-- `c + n · a (n+1)^k ≤ (c + a) (n+1)^(k+1)`. -/
theorem additive_poly_closed (c a k n : Nat) :
    c + n * (a * (n + 1) ^ k) ≤ (c + a) * (n + 1) ^ (k + 1) := by
  have hx : 0 < (n + 1) ^ (k + 1) := Nat.pow_pos (Nat.succ_pos n)
  have h1 : c ≤ c * (n + 1) ^ (k + 1) := Nat.le_mul_of_pos_right c hx
  have h2 : n * (a * (n + 1) ^ k) ≤ a * (n + 1) ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm n, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ n))
  rw [Nat.add_mul]
  omega

/-- **Additive polynomial recurrence.** If each step adds at most `a (n+1)^k`, then
`T n ≤ (c + a) (n+1)^(k+1)`. -/
theorem additive_poly (T : Nat → Nat) (c a k : Nat) (h0 : T 0 ≤ c)
    (hstep : ∀ n, T (n + 1) ≤ T n + a * (n + 1) ^ k) :
    ∀ n, T n ≤ (c + a) * (n + 1) ^ (k + 1) := fun n =>
  Nat.le_trans
    (additive_bound T (fun n => a * (n + 1) ^ k) c h0 hstep
      (fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) n)
    (additive_poly_closed c a k n)

/-! ## (b) Multiplicative recurrences are exponential -/

/-- **Doubling.** `T 0 = 1` and `T (n+1) = 2 T n` give `T n = 2^n`. -/
theorem doubling_exact (T : Nat → Nat) (h0 : T 0 = 1) (hs : ∀ n, T (n + 1) = 2 * T n) :
    ∀ n, T n = 2 ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [hs, ih, Nat.pow_succ, Nat.mul_comm]

/-- **Branching.** `T 0 ≥ 1` and `T (n+1) ≥ 2 T n` give `T n ≥ 2^n`. -/
theorem branching_lower (T : Nat → Nat) (h0 : 1 ≤ T 0) (hs : ∀ n, 2 * T n ≤ T (n + 1)) :
    ∀ n, 2 ^ n ≤ T n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have := hs n
    rw [Nat.pow_succ]
    omega

theorem succ_le_two_pow (q : Nat) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.pow_succ]; omega

theorem lt_two_pow_self (a : Nat) : a < 2 ^ a := by
  have := succ_le_two_pow a
  omega

theorem linear_lt_exp (a q : Nat) (hq : 2 * a + 1 ≤ q) : a * (q + 1) < 2 ^ q := by
  obtain ⟨d, rfl⟩ : ∃ d, q = 2 * a + 1 + d := ⟨q - (2 * a + 1), by omega⟩
  induction d with
  | zero =>
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

/-- `c * (n + 1) ^ k < 2 ^ n` for all `n ≥ 2 ^ (2 * (c + k) + 1)`. -/
theorem exp_beats_poly (c k : Nat) :
    ∀ n, 2 ^ (2 * (c + k) + 1) ≤ n → c * (n + 1) ^ k < 2 ^ n := by
  intro n hn
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.one_le_two_pow) hn
  obtain ⟨L, hL1, hL2⟩ := dyadic_bracket n hn1
  have hLbig : 2 * (c + k) + 1 ≤ L := by
    rcases Nat.lt_or_ge L (2 * (c + k) + 1) with hlt | hge
    · have : 2 ^ (L + 1) ≤ 2 ^ (2 * (c + k) + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hge
  have hlin : (c + k) * (L + 1) < 2 ^ L := linear_lt_exp (c + k) L hLbig
  have hsum : c + k * (L + 1) < n := by
    have : c + k * (L + 1) ≤ (c + k) * (L + 1) := by
      rw [Nat.add_mul]
      have : c ≤ c * (L + 1) := Nat.le_mul_of_pos_right c (by omega)
      omega
    omega
  have hbase : (n + 1) ^ k ≤ 2 ^ ((L + 1) * k) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) k
  have hc : c < 2 ^ c := lt_two_pow_self c
  have hpos : 0 < 2 ^ ((L + 1) * k) := Nat.two_pow_pos _
  calc c * (n + 1) ^ k ≤ c * 2 ^ ((L + 1) * k) := Nat.mul_le_mul_left c hbase
    _ < 2 ^ c * 2 ^ ((L + 1) * k) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (c + (L + 1) * k) := (Nat.pow_add 2 c _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)

/-- **Exponential beats every polynomial.** For all `c k` there is `n` with
`c · (n+1)^k < 2^n`. -/
theorem poly_lt_two_pow (c k : Nat) : ∃ n, c * (n + 1) ^ k < 2 ^ n :=
  ⟨2 ^ (2 * (c + k) + 1), exp_beats_poly c k _ (Nat.le_refl _)⟩

/-- **Branching recurrences are not polynomial.** -/
theorem branching_not_poly (T : Nat → Nat) (h0 : 1 ≤ T 0) (hs : ∀ n, 2 * T n ≤ T (n + 1)) :
    ¬ ∃ c k, ∀ n, T n ≤ c * (n + 1) ^ k := by
  rintro ⟨c, k, hb⟩
  obtain ⟨n, hn⟩ := poly_lt_two_pow c k
  have := branching_lower T h0 hs n
  have := hb n
  omega

/-- The doubling recurrence itself is not polynomially bounded. -/
theorem doubling_not_poly (T : Nat → Nat) (h0 : T 0 = 1) (hs : ∀ n, T (n + 1) = 2 * T n) :
    ∀ c k, ∃ n, c * (n + 1) ^ k < T n := by
  intro c k
  obtain ⟨n, hn⟩ := poly_lt_two_pow c k
  exact ⟨n, by rw [doubling_exact T h0 hs n]; exact hn⟩

/-- Cost of the "try both values of the next variable" self-reduction: two recursive
calls plus overhead `q n`. -/
def branchCost (q : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * branchCost q n + q n

/-- **Two-branch self-reduction is exponential**, whatever the overhead. -/
theorem branchCost_exponential (q : Nat → Nat) : ∀ n, 2 ^ n ≤ branchCost q n :=
  branching_lower (branchCost q) (by simp [branchCost])
    (fun n => by simp only [branchCost]; omega)

/-! ## Self-reduction with one call: the obligation -/

variable {Inst : Type}

/-- Follow `step` `n` times, then answer with `base`. -/
def run (base : Inst → Bool) (step : Inst → Inst) : Nat → Inst → Bool
  | 0, I => base I
  | n + 1, I => run base step n (step I)

/-- Cost of `run`: `baseCost` at the bottom plus `stepCost` at each level. -/
def runCost (baseCost stepCost : Inst → Nat) (step : Inst → Inst) : Nat → Inst → Nat
  | 0, I => baseCost I
  | n + 1, I => stepCost I + runCost baseCost stepCost step n (step I)

/-- **Correctness by size induction.** -/
theorem run_correct (size : Inst → Nat) (answer base : Inst → Bool) (step : Inst → Inst)
    (hbase : ∀ I, size I = 0 → base I = answer I)
    (hstep : ∀ I n, size I = n + 1 → size (step I) = n ∧ answer (step I) = answer I) :
    ∀ n I, size I = n → run base step n I = answer I := by
  intro n
  induction n with
  | zero => intro I h; exact hbase I h
  | succ n ih =>
    intro I hI
    obtain ⟨h1, h2⟩ := hstep I n hI
    simp only [run]
    rw [ih (step I) h1, h2]

/-- **Additive cost by size induction.** -/
theorem runCost_bound (size : Inst → Nat) (step : Inst → Inst) (baseCost stepCost : Inst → Nat)
    (c a k : Nat) (hsize : ∀ I n, size I = n + 1 → size (step I) = n)
    (hbc : ∀ I, baseCost I ≤ c) (hcost : ∀ I, stepCost I ≤ a * (size I + 1) ^ k) :
    ∀ n I, size I = n → runCost baseCost stepCost step n I ≤ c + n * (a * (n + 1) ^ k) := by
  intro n
  induction n with
  | zero => intro I _; simpa [runCost] using hbc I
  | succ n ih =>
    intro I hI
    have h1 := ih (step I) (hsize I n hI)
    have h2 := hcost I
    rw [hI] at h2
    have h3 : a * (n + 1) ^ k ≤ a * (n + 1 + 1) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have h4 : n * (a * (n + 1) ^ k) ≤ n * (a * (n + 1 + 1) ^ k) := Nat.mul_le_mul_left _ h3
    have h5 : (n + 1) * (a * (n + 1 + 1) ^ k) = n * (a * (n + 1 + 1) ^ k) + a * (n + 1 + 1) ^ k :=
      Nat.succ_mul n _
    simp only [runCost]
    omega

/-- **Open obligation.** An additive-cost self-reduction for the language `answer`:
size-0 instances are answered by `base` (cost at most `c`), and one step maps a size-`(n+1)`
instance to a size-`n` instance **with the same answer** at polynomial cost. For SAT
(with `size` = number of variables, and `base`, `step` polynomial-time computable
with the stated costs) this would give P = NP. -/
def AdditiveSelfReduction (size : Inst → Nat) (answer : Inst → Bool) : Prop :=
  ∃ (base : Inst → Bool) (step : Inst → Inst) (baseCost stepCost : Inst → Nat) (c a k : Nat),
    (∀ I, size I = 0 → base I = answer I) ∧ (∀ I, baseCost I ≤ c) ∧
    (∀ I n, size I = n + 1 → size (step I) = n ∧ answer (step I) = answer I) ∧
    (∀ I, stepCost I ≤ a * (size I + 1) ^ k)

/-- **The obligation yields a correct solver with polynomial cost.** -/
theorem obligation_gives_poly_solver (size : Inst → Nat) (answer : Inst → Bool)
    (h : AdditiveSelfReduction size answer) :
    ∃ (solve : Inst → Bool) (cost : Inst → Nat) (c' k' : Nat),
      ∀ I, solve I = answer I ∧ cost I ≤ c' * (size I + 1) ^ k' := by
  obtain ⟨base, step, baseCost, stepCost, c, a, k, hbase, hbc, hstep, hcost⟩ := h
  refine ⟨fun I => run base step (size I) I, fun I => runCost baseCost stepCost step (size I) I,
    c + a, k + 1, fun I => ⟨?_, ?_⟩⟩
  · exact run_correct size answer base step hbase hstep (size I) I rfl
  · exact Nat.le_trans
      (runCost_bound size step baseCost stepCost c a k (fun I n h => (hstep I n h).1) hbc hcost
        (size I) I rfl)
      (additive_poly_closed c a k (size I))

/-- Check: the two-branch cost with zero overhead is exactly `2^n` at `n = 5`. -/
example : branchCost (fun _ => 0) 5 = 32 := by decide

end Issue532.Idea40
