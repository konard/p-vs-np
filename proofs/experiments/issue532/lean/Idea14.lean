/-!
# Issue #532, Idea 14: randomized search

A randomized algorithm for input `x` is modelled as `A x : Nat → Bool`, a
deterministic function of a seed `i < s x`. Counting is done honestly:
`cnt s P` counts the seeds `i < s` with `P i`, and `countT s k Q` counts the
length-`k` seed tuples (lists over `[0, s)`) satisfying `Q`, by enumerating
the first seed and recursing.

Proved for all parameters:

* `countT_true`, `countT_all`: there are `s^k` tuples, and exactly
  `(cnt s P)^k` of them consist only of seeds satisfying `P`.
* `amplification_count`, `rp_amplification`: if at most half the seeds are
  bad (`2·b ≤ s`), then the tuples on which `k` independent repetitions
  all fail number at most `s^k / 2^k`.
* `observed_success_no_guarantee`: for every list of observed seeds and every
  seed-space size `s`, some algorithm succeeds on every observed seed but
  fails on at least `s − |obs|` seeds, so observing success on test seeds
  gives no error bound.
* `enumeration_decides`, `poly_seeds_derandomize`, `polySeedRP_implies_poly`:
  a one-sided-error algorithm is derandomized by trying all seeds, in time
  `(number of seeds) × (time per run)`; this is polynomial exactly when the
  seed space is polynomial (logarithmic seed length).
* `rp_sat_with_seed_compression`: conditional theorem, `NPinRP` plus
  `SeedCompression` gives a polynomial deterministic decider.

Verdict: randomness changes the target class (RP/BPP instead of P), and
turning it back into P needs a derandomization step that is open. The
obligations `NPinRP` and `SeedCompression` are definitions, never assumed.
Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea14

variable {α : Type}

/-- `sumTo n f = f 0 + ⋯ + f (n-1)`. -/
def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

/-- Number of seeds `i < s` with `P i`. -/
def cnt (s : Nat) (P : Nat → Bool) : Nat := sumTo s (fun i => if P i then 1 else 0)

/-- Number of length-`k` seed tuples over `[0, s)` satisfying `Q`. -/
def countT (s : Nat) : Nat → (List Nat → Bool) → Nat
  | 0, Q => if Q [] then 1 else 0
  | k + 1, Q => sumTo s (fun i => countT s k (fun t => Q (i :: t)))

theorem sumTo_const (s X : Nat) : sumTo s (fun _ => X) = s * X := by
  induction s with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih, Nat.succ_mul]

theorem sumTo_ite_mul (s X : Nat) (P : Nat → Bool) :
    sumTo s (fun i => if P i then X else 0) = cnt s P * X := by
  induction s with
  | zero => simp [sumTo, cnt]
  | succ n ih =>
    simp only [cnt, sumTo] at *
    rw [ih, Nat.add_mul]
    cases P n <;> simp

theorem countT_false (s k : Nat) : countT s k (fun _ => false) = 0 := by
  induction k with
  | zero => simp [countT]
  | succ k ih => simp only [countT, ih, sumTo_const, Nat.mul_zero]

/-- There are exactly `s^k` tuples of length `k`. -/
theorem countT_true (s k : Nat) : countT s k (fun _ => true) = s ^ k := by
  induction k with
  | zero => simp [countT]
  | succ k ih => simp only [countT, ih, sumTo_const, Nat.pow_succ, Nat.mul_comm]

/-- Exactly `(cnt s P)^k` tuples consist only of seeds satisfying `P`. -/
theorem countT_all (s k : Nat) (P : Nat → Bool) :
    countT s k (fun t => t.all P) = cnt s P ^ k := by
  induction k with
  | zero => simp [countT]
  | succ k ih =>
    have h : (fun i => countT s k (fun t => (i :: t).all P)) =
        (fun i => if P i then countT s k (fun t => t.all P) else 0) := by
      funext i
      cases hi : P i <;> simp [List.all_cons, hi, countT_false]
    simp only [countT]
    rw [h, sumTo_ite_mul, ih, Nat.pow_succ, Nat.mul_comm]

/-- Amplification arithmetic: `2b ≤ s` implies `b^k · 2^k ≤ s^k`. -/
theorem amplification_count (b s k : Nat) (h : 2 * b ≤ s) : b ^ k * 2 ^ k ≤ s ^ k := by
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega) k

theorem not_any_eq_all (A : Nat → Bool) (t : List Nat) :
    (!t.any A) = t.all (fun i => !A i) := by
  induction t with
  | nil => rfl
  | cons a t ih => cases h : A a <;> simp [List.any_cons, List.all_cons, h, ih]

/--
One-sided amplification: if at most half of the `s` seeds make `A` reject
wrongly, then at most `s^k / 2^k` of the `s^k` seed tuples make all `k`
repetitions reject.
-/
theorem rp_amplification (A : Nat → Bool) (s k : Nat) (h : 2 * cnt s (fun i => !A i) ≤ s) :
    countT s k (fun t => !t.any A) * 2 ^ k ≤ s ^ k := by
  have e : (fun t : List Nat => !t.any A) = (fun t => t.all (fun i => !A i)) :=
    funext (not_any_eq_all A)
  rw [e, countT_all]
  exact amplification_count _ _ _ h

theorem cnt_compl (s : Nat) (P : Nat → Bool) : cnt s P + cnt s (fun i => !P i) = s := by
  induction s with
  | zero => simp [cnt, sumTo]
  | succ n ih =>
    simp only [cnt, sumTo] at *
    rcases Bool.eq_false_or_eq_true (P n) with h | h <;> simp only [h, Bool.not_true, Bool.not_false, reduceIte, Bool.false_eq_true] <;> omega

/-- Boolean membership of a seed in a list. -/
def memB (i : Nat) : List Nat → Bool
  | [] => false
  | a :: l => decide (i = a) || memB i l

theorem cnt_eq_le (s a : Nat) : cnt s (fun i => decide (i = a)) ≤ 1 := by
  have : cnt s (fun i => decide (i = a)) = if a < s then 1 else 0 := by
    induction s with
    | zero => simp [cnt, sumTo]
    | succ n ih =>
      simp only [cnt, sumTo] at *
      rw [ih]
      by_cases h1 : a < n
      · have : n ≠ a := by omega
        simp [h1, this, show a < n + 1 by omega]
      · by_cases h2 : n = a
        · subst h2; simp
        · simp [h1, h2, show ¬ a < n + 1 by omega]
  rw [this]; split <;> omega

theorem cnt_or_le (s : Nat) (P Q : Nat → Bool) :
    cnt s (fun i => P i || Q i) ≤ cnt s P + cnt s Q := by
  induction s with
  | zero => simp [cnt, sumTo]
  | succ n ih =>
    simp only [cnt, sumTo] at *
    rcases Bool.eq_false_or_eq_true (P n) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (Q n) with h2 | h2 <;>
      simp only [h1, h2, Bool.or_true, Bool.or_false, reduceIte, Bool.false_eq_true] <;> omega

theorem cnt_memB_le (s : Nat) (obs : List Nat) : cnt s (fun i => memB i obs) ≤ obs.length := by
  induction obs with
  | nil => simp [cnt, memB, sumTo_const]
  | cons a l ih =>
    have h1 := cnt_or_le s (fun i => decide (i = a)) (fun i => memB i l)
    have h2 := cnt_eq_le s a
    simp only [memB, List.length_cons] at *
    omega

/--
Observed success is no guarantee: for every list `obs` of tested seeds and
every seed-space size `s`, some algorithm accepts on all tested seeds yet
fails on at least `s − |obs|` of the `s` seeds.
-/
theorem observed_success_no_guarantee (obs : List Nat) (s : Nat) :
    ∃ A : Nat → Bool, (∀ i, i ∈ obs → A i = true) ∧ s ≤ cnt s (fun i => !A i) + obs.length := by
  refine ⟨fun i => memB i obs, ?_, ?_⟩
  · intro i hi
    induction obs with
    | nil => cases hi
    | cons a l ih =>
      simp only [memB]
      cases hi with
      | head => simp
      | tail _ h => simp [ih h]
  · have := cnt_compl s (fun i => memB i obs)
    show s ≤ cnt s (fun i => !memB i obs) + obs.length
    have := cnt_memB_le s obs
    omega

/--
One-sided error: at least one seed, no false acceptances, and on
yes-instances at most half the seeds reject.
-/
def OneSided (L : α → Bool) (A : α → Nat → Bool) (s : α → Nat) : Prop :=
  ∀ x, 0 < s x ∧ (L x = false → ∀ i, A x i = false) ∧
    (L x = true → 2 * cnt (s x) (fun i => !A x i) ≤ s x)

/-- Try all seeds `i < s`. -/
def anySeed : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, f => anySeed n f || f n

theorem anySeed_false (s : Nat) (f : Nat → Bool) (h : ∀ i, f i = false) : anySeed s f = false := by
  induction s with
  | zero => rfl
  | succ n ih => simp [anySeed, ih, h n]

theorem anySeed_cnt (s : Nat) (f : Nat → Bool) (h : anySeed s f = false) : cnt s f = 0 := by
  induction s with
  | zero => rfl
  | succ n ih =>
    simp only [anySeed, Bool.or_eq_false_iff] at h
    simp only [cnt, sumTo] at *
    rw [ih h.1, h.2]; rfl

/-- One-sided amplification for a whole algorithm. -/
theorem one_sided_amplified (L : α → Bool) (A : α → Nat → Bool) (s : α → Nat)
    (hA : OneSided L A s) (x : α) (k : Nat) :
    (L x = false → ∀ t : List Nat, t.any (A x) = false) ∧
    (L x = true → countT (s x) k (fun t => !t.any (A x)) * 2 ^ k ≤ s x ^ k) := by
  obtain ⟨_, hno, hyes⟩ := hA x
  refine ⟨fun h t => ?_, fun h => rp_amplification (A x) (s x) k (hyes h)⟩
  induction t with
  | nil => rfl
  | cons a t ih => simp [List.any_cons, hno h a, ih]

/-- Derandomization by enumerating all seeds is correct. -/
theorem enumeration_decides (L : α → Bool) (A : α → Nat → Bool) (s : α → Nat)
    (hA : OneSided L A s) (x : α) : anySeed (s x) (A x) = L x := by
  obtain ⟨hpos, hno, hyes⟩ := hA x
  cases hL : L x
  · exact anySeed_false _ _ (hno hL)
  · cases he : anySeed (s x) (A x)
    · have h0 := anySeed_cnt _ _ he
      have hc := cnt_compl (s x) (A x)
      have := hyes hL
      omega
    · rfl

/--
Enumeration is polynomial when the seed space is: `s x ≤ e(n+1)^k` seeds and
`T x ≤ c(n+1)^d` time per run give total time `≤ e·c·(n+1)^(k+d)`.
-/
theorem poly_seeds_derandomize (sz : α → Nat) (L : α → Bool) (A : α → Nat → Bool) (s T : α → Nat)
    (c d e k : Nat) (hA : OneSided L A s) (hs : ∀ x, s x ≤ e * (sz x + 1) ^ k)
    (hT : ∀ x, T x ≤ c * (sz x + 1) ^ d) :
    ∀ x, anySeed (s x) (A x) = L x ∧ s x * T x ≤ e * c * (sz x + 1) ^ (k + d) := by
  intro x
  refine ⟨enumeration_decides L A s hA x, ?_⟩
  have h := Nat.mul_le_mul (hs x) (hT x)
  rw [Nat.mul_mul_mul_comm, ← Nat.pow_add] at h
  exact h

/-- A polynomial-time deterministic decider. -/
def PolyDec (sz : α → Nat) (L : α → Bool) : Prop :=
  ∃ (D : α → Bool) (t : α → Nat) (c d : Nat), (∀ x, D x = L x) ∧ ∀ x, t x ≤ c * (sz x + 1) ^ d

/-- A polynomial-time one-sided algorithm with seeds of polynomial length `r x` (`2^(r x)` seeds). -/
def RPDecider (sz : α → Nat) (L : α → Bool) : Prop :=
  ∃ (A : α → Nat → Bool) (r T : α → Nat) (c d : Nat), OneSided L A (fun x => 2 ^ r x) ∧
    ∀ x, r x ≤ c * (sz x + 1) ^ d ∧ T x ≤ c * (sz x + 1) ^ d

/-- A polynomial-time one-sided algorithm with only polynomially many seeds. -/
def PolySeedRP (sz : α → Nat) (L : α → Bool) : Prop :=
  ∃ (A : α → Nat → Bool) (s T : α → Nat) (c d : Nat), OneSided L A s ∧
    ∀ x, s x ≤ c * (sz x + 1) ^ d ∧ T x ≤ c * (sz x + 1) ^ d

/-- Polynomially many seeds can be enumerated deterministically in polynomial time. -/
theorem polySeedRP_implies_poly (sz : α → Nat) (L : α → Bool) (h : PolySeedRP sz L) : PolyDec sz L := by
  obtain ⟨A, s, T, c, d, hA, hb⟩ := h
  refine ⟨fun x => anySeed (s x) (A x), fun x => s x * T x, c * c, d + d, fun x => ?_, fun x => ?_⟩
  · exact enumeration_decides L A s hA x
  · exact (poly_seeds_derandomize sz L A s T c d c d hA (fun x => (hb x).1) (fun x => (hb x).2) x).2

/-- Open obligation (not assumed): `L` (e.g. SAT) has a polynomial one-sided randomized decider. -/
def NPinRP (sz : α → Nat) (L : α → Bool) : Prop := RPDecider sz L

/--
Open obligation (not assumed): seed compression for `L`, i.e. every
polynomial one-sided algorithm can be replaced by one with polynomially many
seeds (what a suitable pseudorandom generator would provide).
-/
def SeedCompression (sz : α → Nat) (L : α → Bool) : Prop := RPDecider sz L → PolySeedRP sz L

/-- Conditional theorem: `NPinRP` and `SeedCompression` together give a polynomial decider. -/
theorem rp_sat_with_seed_compression (sz : α → Nat) (L : α → Bool)
    (h1 : NPinRP sz L) (h2 : SeedCompression sz L) : PolyDec sz L :=
  polySeedRP_implies_poly sz L (h2 h1)

end Issue532.Idea14
