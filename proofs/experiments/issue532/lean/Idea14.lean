import proofs.experiments.issue532.lean.Machines

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
* `enumeration_decides`, `poly_seeds_derandomize`: a one-sided-error
  algorithm is derandomized by trying all seeds, in time
  `(number of seeds) × (time per run)`; this is polynomial exactly when the
  seed space is polynomial (logarithmic seed length).

Over the shared machine model (`Complexity.Machine`, time = step count of
`Complexity.Run`, random string appended with `Complexity.pairedInput`):

* `seedWord`, `seedWord_surjective`: seeds `i < 2^ℓ` enumerate every random
  string of length `ℓ`; `two_pow_logSeed`: logarithmic seeds are at most
  `(n+1)^k`.
* `HaltsWithin`, `RPMachine`, `InRP`: the class RP with an explicit polynomial
  random-string length; `PolySeedMachine`, `PolySeedRP`: the same with
  logarithmic seeds.
* Open obligations `NPinRP : InRP SAT` and `SeedCompression SAT`; named known
  theorem `SeedEnumeration` (enumerating logarithmic seeds is polynomial),
  whose mathematical core is `logSeed_enumeration`.
* `rp_sat_with_seed_compression`, `rp_route_gives_pEqualsNP`: the conditional
  theorems to `PolyDec SAT` and `PEqualsNP`.
* `not_forall_inRP`: non-vacuity, `InRP` fails for some language
  (diagonalisation against `rpLanguage`).

Verdict: developed to an open obligation. Randomness changes the target class
(RP/BPP instead of P), and turning it back into P needs a derandomization step
that is open. The obligations `NPinRP` and `SeedCompression` are definitions,
never assumed.
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

/-! ## The obligations over the shared machine model

A randomised decider is a `Complexity.Machine` run on `x ⊔ separator ⊔ r`
(`Complexity.pairedInput`) for a random string `r`; its time is the step count
of `Complexity.Run`. The random-string length is an explicit polynomial `R`
(for RP) or `k · ⌊log₂(n+1)⌋` (for seed-compressed algorithms); it is never an
arbitrary function of the input length, which would smuggle in advice. -/

open Complexity Issue532.Machines

/-- The `i`-th random string of length `ℓ` (binary, least significant bit first). -/
def seedWord : Nat → Nat → Word
  | 0, _ => []
  | ℓ + 1, i => (i % 2 == 1) :: seedWord ℓ (i / 2)

theorem seedWord_length (ℓ i : Nat) : (seedWord ℓ i).length = ℓ := by
  induction ℓ generalizing i with
  | zero => rfl
  | succ ℓ ih => simp [seedWord, ih]

/-- Seeds `i < 2^ℓ` enumerate every random string of length `ℓ`. -/
theorem seedWord_surjective (r : Word) : ∃ i, i < 2 ^ r.length ∧ seedWord r.length i = r := by
  induction r with
  | nil => exact ⟨0, by decide, rfl⟩
  | cons b r ih =>
    obtain ⟨i, hi, hr⟩ := ih
    refine ⟨2 * i + (if b then 1 else 0), ?_, ?_⟩
    · simp only [List.length_cons, Nat.pow_succ]
      cases b <;> simp <;> omega
    · simp only [List.length_cons, seedWord]
      have h2 : (2 * i + (if b then 1 else 0)) / 2 = i := by cases b <;> simp <;> omega
      rw [h2, hr]
      cases b <;> simp <;> omega

/-- `m` halts within `p` on input `x` with every random string of length `ℓ(|x|)`. -/
def HaltsWithin (m : Machine) (p : Polynomial) (ℓ : Nat → Nat) : Prop :=
  ∀ x i, ∃ t b, t ≤ p.eval (x.length + ℓ x.length + 1) ∧
    Run m (pairedInput x (seedWord (ℓ x.length) i)) t b

open Classical in
/-- Seed `i` makes `m` accept `x`. -/
noncomputable def seedAccepts (m : Machine) (ℓ : Nat → Nat) (x : Word) (i : Nat) : Bool :=
  decide (∃ t, Run m (pairedInput x (seedWord (ℓ x.length) i)) t true)

/-- A polynomial-time one-sided randomised machine for `L`: random strings of
length `R(|x|)`, never accepts a no-instance, accepts a yes-instance on at least
half of the random strings. -/
def RPMachine (m : Machine) (p R : Polynomial) (L : Language) : Prop :=
  HaltsWithin m p R.eval ∧ OneSided L (seedAccepts m R.eval) (fun x => 2 ^ R.eval x.length)

/-- The class RP of the shared machine model. -/
def InRP (L : Language) : Prop := ∃ (m : Machine) (p R : Polynomial), RPMachine m p R L

/-- **Open obligation.** SAT has a polynomial-time one-sided randomised machine
decider (NP ⊆ RP). -/
def NPinRP : Prop := InRP SAT

/-- Logarithmic seed length `k · ⌊log₂(n+1)⌋`. -/
def logSeed (k n : Nat) : Nat := k * Nat.log2 (n + 1)

/-- Logarithmic seeds are polynomially many: `2^(k·⌊log₂(n+1)⌋) ≤ (n+1)^k`. -/
theorem two_pow_logSeed (k n : Nat) : 2 ^ logSeed k n ≤ (n + 1) ^ k := by
  unfold logSeed
  rw [Nat.mul_comm, Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.log2_self_le (Nat.succ_ne_zero n)) k

/-- A polynomial-time one-sided randomised machine with logarithmic seeds. -/
def PolySeedMachine (m : Machine) (p : Polynomial) (k : Nat) (L : Language) : Prop :=
  HaltsWithin m p (logSeed k) ∧
    OneSided L (seedAccepts m (logSeed k)) (fun x => 2 ^ logSeed k x.length)

def PolySeedRP (L : Language) : Prop := ∃ (m : Machine) (p : Polynomial) (k : Nat), PolySeedMachine m p k L

/-- **Open obligation.** Seed compression for `L`: a polynomial-time one-sided
randomised machine can be replaced by one with logarithmic seeds (what a
suitable pseudorandom generator provides). -/
def SeedCompression (L : Language) : Prop := InRP L → PolySeedRP L

/-- Known theorem, not mechanised here: a machine that tries all
`2^(k·⌊log₂(n+1)⌋) ≤ (n+1)^k` seeds, each run within `p`, decides `L`
deterministically in polynomial time. The mathematics is
`logSeed_enumeration`; the missing part is the single-tape machine that
enumerates the seeds and simulates `m`. -/
def SeedEnumeration : Prop := ∀ L, PolySeedRP L → InP L

/-- The mathematical core of `SeedEnumeration`: trying every seed gives the
right answer, there are at most `(n+1)^k` seeds, and each run halts within
`p(n + k·⌊log₂(n+1)⌋ + 1)` steps. -/
theorem logSeed_enumeration {m : Machine} {p : Polynomial} {k : Nat} {L : Language}
    (h : PolySeedMachine m p k L) (x : Word) :
    anySeed (2 ^ logSeed k x.length) (seedAccepts m (logSeed k) x) = L x ∧
      2 ^ logSeed k x.length ≤ (x.length + 1) ^ k ∧
      ∀ i, ∃ t b, t ≤ p.eval (x.length + logSeed k x.length + 1) ∧
        Run m (pairedInput x (seedWord (logSeed k x.length) i)) t b :=
  ⟨enumeration_decides L _ _ h.2 x, two_pow_logSeed k x.length, h.1 x⟩

/-- Conditional theorem: `NPinRP`, `SeedCompression SAT` and the known
`SeedEnumeration` give a polynomial-time machine decider for SAT. -/
theorem rp_sat_with_seed_compression (h1 : NPinRP) (h2 : SeedCompression SAT)
    (h3 : SeedEnumeration) : PolyDec SAT :=
  (polyDec_iff_inP SAT).mpr (h3 SAT (h2 h1))

/-- With the hardness half of Cook–Levin the conclusion is P = NP. -/
theorem rp_route_gives_pEqualsNP (h1 : NPinRP) (h2 : SeedCompression SAT)
    (h3 : SeedEnumeration) (hard : SATHard) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (h3 SAT (h2 h1))

/-- The language a one-sided randomised machine decides is determined by the
machine and the random-string length. -/
noncomputable def rpLanguage (x : Machine × Polynomial) : Language :=
  fun w => anySeed (2 ^ x.2.eval w.length) (seedAccepts x.1 x.2.eval w)

/-- **Non-vacuity.** `InRP` does not hold for every language, so `NPinRP` is a
statement about SAT, not a consequence of the definitions. -/
theorem not_forall_inRP : ¬ ∀ L : Language, InRP L := by
  intro hall
  obtain ⟨L, hL⟩ := exists_language_not_in_family encMachinePoly encMachinePoly_injective rpLanguage
  obtain ⟨m, p, R, _, hone⟩ := hall L
  exact hL (m, R) (funext fun x => enumeration_decides L _ _ hone x)

end Issue532.Idea14
