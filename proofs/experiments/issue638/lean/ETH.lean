import proofs.experiments.issue532.lean.SATVerifier
import proofs.experiments.issue532.lean.Idea41

/-!
# Issue #638: the Exponential Time Hypothesis in the shared machine model

On 26–27 October 2026 OpenAI (`openai/math`, `SubexponentialSAT`) and Anthropic
(`anthropics/formal-math`, `eth/`) each published a Lean proof of a deterministic
algorithm that decides (and counts) k-SAT in time `2^{O_k(n·polyloglog n/√log n)}`.
Such an algorithm refutes the Exponential Time Hypothesis (ETH) and, because it
covers every fixed k, also the Strong Exponential Time Hypothesis (SETH). Those
proofs use other machine models: Mathlib's `Turing.FinTM2` and OpenAI's
`PrimitiveMachine`. This file does not re-prove them. The
`external-lean-reverification` workflow rebuilds them. This file states ETH and
SETH over the repository's single machine model `Complexity.Machine` and proves
how they relate to `P = NP`:

* `Width`, `DecidesKSATWithin`, `KSATExpTime`, `ETH`, `SETH`: k-SAT in time
  `c · 2^{(a/d)·n} · (|x|+1)^c` on encodings `encodeCNF φ`, where `n = numVars φ`.
  This is the usual `O*(2^{δn})` with `δ = a/d`, polynomial in the input
  length `|x|`.
* `ksatExpTime_of_inP_sat`, `not_eth_of_pEqualsNP`, `pNotEqualsNP_of_eth`,
  `not_seth_of_pEqualsNP`, `pNotEqualsNP_of_seth`: `P = NP` refutes ETH and SETH.
  Contrapositively, ETH and SETH each imply `P ≠ NP`. These results need no
  Cook–Levin hypothesis, because `SAT ∈ NP` is the proved
  `SATVerifier.satInNP`.
* `ksatExpTime_width_mono`, `ksatExpTime_exp_mono`: k-SAT time is monotone in k
  and in δ.
* `SubexpKSAT`, `SubexpAllK`, `not_eth_of_subexp3`, `eth_iff_not_subexp3`,
  `not_seth_of_subexpAllK`: the shape of the October 2026 claims (k-SAT in
  `O*(2^{δn})` for every `δ > 0`) refutes ETH, and for every k also SETH.
* `logBudget`, `logBudget_le`, `subexpKSAT_of_logBudget`, `logBudget_not_polynomial`:
  the budget `2^{⌊n/(⌊log₂ n⌋+1)⌋}` is at most `2^{2^d}·2^{n/d}` for every
  `d > 0`, so a k-SAT algorithm in this budget gives `SubexpKSAT k`. The budget
  is not polynomially bounded. The labs' bounds `2^{c·n·loglog n/√log n}` are at
  least this budget for every `c ≥ 1` and every large n. A refutation of ETH
  therefore does not by its bound give `SAT ∈ P`, and nothing here derives
  `P = NP` from `¬ ETH`.
* `swap_eq_id_sub_singlet`, `singlet_sq`, `swap_sq`: the one-bit algebra of
  Anthropic's key idea, SWAP = I − 2·singlet, over the integers.

What is not proved: the sparsification lemma, and hence "SETH implies ETH", and
any simulation between `Complexity.Machine` and the labs' machine models. The
labs' theorems enter only as the named hypotheses `SubexpKSAT` and `SubexpAllK`.
-/

namespace Issue638.ETH

open Complexity
open Issue532.Machines

/-! ## k-SAT in exponential time -/

/-- Every clause has at most `k` literals. -/
def Width (k : Nat) (φ : CNF) : Prop := ∀ c ∈ φ, c.length ≤ k

/-- `m` decides k-SAT within `T n |x|` steps, where `n = numVars φ` and `x = encodeCNF φ`. -/
def DecidesKSATWithin (k : Nat) (m : Machine) (T : Nat → Nat → Nat) : Prop :=
  ∀ φ : CNF, Width k φ → ∃ t b, t ≤ T (numVars φ) (encodeCNF φ).length ∧
    Run m (initial (encodeCNF φ)) t b ∧ (b = true ↔ Satisfiable φ)

/-- The time `c · 2^{⌊a·n/d⌋} · (len+1)^c`. With `d = 0` it is polynomial in `len`. -/
def expTime (c a d : Nat) (n len : Nat) : Nat := c * 2 ^ (a * n / d) * (len + 1) ^ c

/-- k-SAT is decidable in time `O*(2^{(a/d)·n})`. -/
def KSATExpTime (k a d : Nat) : Prop :=
  ∃ (m : Machine) (c : Nat), DecidesKSATWithin k m (expTime c a d)

/-- **ETH** (Impagliazzo–Paturi 2001): for some `δ = 1/d > 0`, 3-SAT is not
decidable in time `O*(2^{δn})`. -/
def ETH : Prop := ∃ d, 0 < d ∧ ¬ KSATExpTime 3 1 d

/-- **SETH** (Impagliazzo–Paturi 2001; Calabro–Impagliazzo–Paturi 2009): for
every `ε = 1/d > 0` some k-SAT is not decidable in time `O*(2^{(1-ε)n})`. -/
def SETH : Prop := ∀ d, 0 < d → ∃ k, ¬ KSATExpTime k (d - 1) d

theorem decides_mono {k : Nat} {m : Machine} {T T' : Nat → Nat → Nat}
    (hT : ∀ n len, T n len ≤ T' n len) (h : DecidesKSATWithin k m T) :
    DecidesKSATWithin k m T' := by
  intro φ hφ
  obtain ⟨t, b, ht, hr, hb⟩ := h φ hφ
  exact ⟨t, b, Nat.le_trans ht (hT _ _), hr, hb⟩

theorem decides_width_mono {k k' : Nat} {m : Machine} {T : Nat → Nat → Nat}
    (hk : k ≤ k') (h : DecidesKSATWithin k' m T) : DecidesKSATWithin k m T :=
  fun φ hφ => h φ fun c hc => Nat.le_trans (hφ c hc) hk

/-- A k'-SAT algorithm is a k-SAT algorithm for every `k ≤ k'`. -/
theorem ksatExpTime_width_mono {k k' a d : Nat} (hk : k ≤ k') :
    KSATExpTime k' a d → KSATExpTime k a d := by
  rintro ⟨m, c, h⟩
  exact ⟨m, c, decides_width_mono hk h⟩

theorem expTime_mono {c x y len : Nat} (hxy : x ≤ y) :
    c * 2 ^ x * (len + 1) ^ c ≤ c * 2 ^ y * (len + 1) ^ c :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by decide) hxy))

/-- `a/d ≤ a'/d'` gives `⌊a·n/d⌋ ≤ ⌊a'·n/d'⌋`. -/
theorem exp_div_mono {a d a' d' : Nat} (n : Nat) (hd : 0 < d) (hd' : 0 < d')
    (h : a * d' ≤ a' * d) : a * n / d ≤ a' * n / d' := by
  rw [Nat.le_div_iff_mul_le hd']
  have hq : a * n / d * d ≤ a * n := Nat.div_mul_le_self _ _
  apply Nat.le_of_mul_le_mul_right _ hd
  calc a * n / d * d' * d = a * n / d * d * d' := by
          rw [Nat.mul_assoc, Nat.mul_comm d' d, ← Nat.mul_assoc]
    _ ≤ a * n * d' := Nat.mul_le_mul_right _ hq
    _ = n * (a * d') := by rw [Nat.mul_comm a n, Nat.mul_assoc]
    _ ≤ n * (a' * d) := Nat.mul_le_mul_left _ h
    _ = a' * n * d := by rw [Nat.mul_comm a' n, Nat.mul_assoc]

/-- A larger exponent `a'/d' ≥ a/d` is a weaker requirement. -/
theorem ksatExpTime_exp_mono {k a d a' d' : Nat} (hd : 0 < d) (hd' : 0 < d')
    (h : a * d' ≤ a' * d) : KSATExpTime k a d → KSATExpTime k a' d' := by
  rintro ⟨m, c, hm⟩
  exact ⟨m, c, decides_mono (fun n _ => expTime_mono (exp_div_mono n hd hd' h)) hm⟩

/-! ## P = NP refutes ETH and SETH -/

/-- A polynomial-time `SAT` decider decides k-SAT in time `O*(2^{(a/d)·n})` for all `k, a, d`. -/
theorem ksatExpTime_of_inP_sat (h : InP SAT) (k a d : Nat) : KSATExpTime k a d := by
  obtain ⟨m, p, hm⟩ := inP_sat_on_encodings h
  refine ⟨m, p.coefficient + p.degree, fun φ _ => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm φ
  refine ⟨t, b, Nat.le_trans ht ?_, hr, hb⟩
  unfold Polynomial.eval expTime
  have h2 : 1 ≤ 2 ^ (a * numVars φ / d) := Nat.one_le_two_pow
  have h1 : p.coefficient ≤ (p.coefficient + p.degree) * 2 ^ (a * numVars φ / d) :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ h2)
  exact Nat.mul_le_mul h1
    (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _))

theorem not_eth_of_inP_sat (h : InP SAT) : ¬ ETH :=
  fun ⟨d, _, hd⟩ => hd (ksatExpTime_of_inP_sat h 3 1 d)

theorem not_seth_of_inP_sat (h : InP SAT) : ¬ SETH := by
  intro hs
  obtain ⟨k, hk⟩ := hs 1 Nat.one_pos
  exact hk (ksatExpTime_of_inP_sat h k 0 1)

/-- `P = NP` refutes ETH. Unconditional: `SAT ∈ NP` is `SATVerifier.satInNP`. -/
theorem not_eth_of_pEqualsNP (h : PEqualsNP) : ¬ ETH :=
  not_eth_of_inP_sat (inP_sat_of_pEqualsNP Issue532.SATVerifier.satInNP h)

/-- ETH implies `P ≠ NP`. -/
theorem pNotEqualsNP_of_eth (h : ETH) : PNotEqualsNP :=
  fun hp => not_eth_of_pEqualsNP hp h

/-- `P = NP` refutes SETH. -/
theorem not_seth_of_pEqualsNP (h : PEqualsNP) : ¬ SETH :=
  not_seth_of_inP_sat (inP_sat_of_pEqualsNP Issue532.SATVerifier.satInNP h)

/-- SETH implies `P ≠ NP`. -/
theorem pNotEqualsNP_of_seth (h : SETH) : PNotEqualsNP :=
  fun hp => not_seth_of_pEqualsNP hp h

/-! ## The shape of the October 2026 claims -/

/-- k-SAT in time `O*(2^{δn})` for every `δ = 1/d > 0`. -/
def SubexpKSAT (k : Nat) : Prop := ∀ d, 0 < d → KSATExpTime k 1 d

/-- The claims of both labs, transported to this model: `SubexpKSAT k` for every k. -/
def SubexpAllK : Prop := ∀ k, SubexpKSAT k

theorem not_eth_of_subexp3 (h : SubexpKSAT 3) : ¬ ETH :=
  fun ⟨d, hd, hn⟩ => hn (h d hd)

theorem eth_iff_not_subexp3 : ETH ↔ ¬ SubexpKSAT 3 := by
  constructor
  · exact fun he hs => not_eth_of_subexp3 hs he
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro d hd
    apply Classical.byContradiction
    intro hk
    exact hne ⟨d, hd, hk⟩

/-- For every k at once, the claims also refute SETH (take `ε = 1/2`). -/
theorem not_seth_of_subexpAllK (h : SubexpAllK) : ¬ SETH := by
  intro hs
  obtain ⟨k, hk⟩ := hs 2 (by decide)
  exact hk (h k 2 (by decide))

/-- `SubexpKSAT k'` gives `SubexpKSAT k` for `k ≤ k'`. -/
theorem subexpKSAT_width_mono {k k' : Nat} (hk : k ≤ k') (h : SubexpKSAT k') : SubexpKSAT k :=
  fun d hd => ksatExpTime_width_mono hk (h d hd)

/-! ## A subexponential budget that is not polynomial -/

/-- `2^{⌊n/(⌊log₂ n⌋+1)⌋}`, below the labs' bounds `2^{c·n·loglog n/√log n}` (`c ≥ 1`, large n). -/
def logBudget (n : Nat) : Nat := 2 ^ (n / (Nat.log2 n + 1))

/-- For every `d > 0`: `logBudget n ≤ 2^{2^d} · 2^{n/d}` for all n. -/
theorem logBudget_le (d n : Nat) (hd : 0 < d) : logBudget n ≤ 2 ^ (2 ^ d) * 2 ^ (n / d) := by
  unfold logBudget
  by_cases h : 2 ^ d ≤ n
  · have hn : n ≠ 0 := by
      have := Nat.one_le_two_pow (n := d)
      omega
    have hl : d ≤ Nat.log2 n := (Nat.le_log2 hn).2 h
    have hdiv : n / (Nat.log2 n + 1) ≤ n / d := Nat.div_le_div_left (by omega) hd
    calc 2 ^ (n / (Nat.log2 n + 1)) ≤ 2 ^ (n / d) := Nat.pow_le_pow_right (by decide) hdiv
      _ ≤ 2 ^ (2 ^ d) * 2 ^ (n / d) := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  · have hdiv : n / (Nat.log2 n + 1) ≤ 2 ^ d :=
      Nat.le_trans (Nat.div_le_self _ _) (by omega)
    calc 2 ^ (n / (Nat.log2 n + 1)) ≤ 2 ^ (2 ^ d) := Nat.pow_le_pow_right (by decide) hdiv
      _ ≤ 2 ^ (2 ^ d) * 2 ^ (n / d) := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow

/-- A k-SAT decider within `c · logBudget n · (|x|+1)^c` gives `SubexpKSAT k`. -/
theorem subexpKSAT_of_logBudget {k : Nat} {m : Machine} {c : Nat}
    (h : DecidesKSATWithin k m fun n len => c * logBudget n * (len + 1) ^ c) :
    SubexpKSAT k := by
  intro d hd
  refine ⟨m, c * 2 ^ (2 ^ d), decides_mono (fun n len => ?_) h⟩
  unfold expTime
  rw [Nat.one_mul]
  have hb := logBudget_le d n hd
  have hpow : (len + 1) ^ c ≤ (len + 1) ^ (c * 2 ^ (2 ^ d)) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
  calc c * logBudget n * (len + 1) ^ c
      ≤ c * (2 ^ (2 ^ d) * 2 ^ (n / d)) * (len + 1) ^ (c * 2 ^ (2 ^ d)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c hb) hpow
    _ = c * 2 ^ (2 ^ d) * 2 ^ (n / d) * (len + 1) ^ (c * 2 ^ (2 ^ d)) := by
        simp only [Nat.mul_assoc]

/-- A 3-SAT decider within the budget refutes ETH. -/
theorem not_eth_of_logBudget {m : Machine} {c : Nat}
    (h : DecidesKSATWithin 3 m fun n len => c * logBudget n * (len + 1) ^ c) : ¬ ETH :=
  not_eth_of_subexp3 (subexpKSAT_of_logBudget h)

/-- Deciders within the budget for every k refute SETH. -/
theorem not_seth_of_logBudget
    (h : ∀ k, ∃ (m : Machine) (c : Nat),
      DecidesKSATWithin k m fun n len => c * logBudget n * (len + 1) ^ c) : ¬ SETH :=
  not_seth_of_subexpAllK fun k => by
    obtain ⟨m, c, hm⟩ := h k
    exact subexpKSAT_of_logBudget hm

theorem logBudget_two_pow (m : Nat) : logBudget (2 ^ m) = 2 ^ (2 ^ m / (m + 1)) := by
  simp [logBudget, Nat.log2_two_pow]

/-- The budget is not polynomially bounded: a subexponential bound does not give `SAT ∈ P`. -/
theorem logBudget_not_polynomial : ¬ PolynomiallyBounded logBudget := by
  rintro ⟨a, k, h⟩
  obtain ⟨N, hN⟩ := Issue532.Idea41.poly_le_two_pow (k + a) 2
  have h1 := h (2 ^ N)
  rw [logBudget_two_pow] at h1
  have hbase : 2 ^ N + 1 ≤ 2 ^ (N + 1) := by
    have := Nat.one_le_two_pow (n := N)
    rw [Nat.pow_succ]
    omega
  have h2 : (2 ^ N + 1) ^ k ≤ 2 ^ ((N + 1) * k) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left hbase k
  have h3 : a < 2 ^ a := Nat.lt_two_pow_self
  have h4 : a + (N + 1) * k ≤ 2 ^ N / (N + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos N)]
    have hN' := hN N (Nat.le_refl _)
    have ha : a ≤ (N + 1) * a := Nat.le_mul_of_pos_left _ (Nat.succ_pos N)
    calc (a + (N + 1) * k) * (N + 1) ≤ ((N + 1) * a + (N + 1) * k) * (N + 1) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_right ha _)
      _ = (k + a) * (N + 1) ^ 2 := by
          rw [← Nat.mul_add, Nat.pow_two, Nat.add_comm a k]
          rw [Nat.mul_comm (N + 1) (k + a), Nat.mul_assoc]
      _ ≤ 2 ^ N := hN'
  have h5 : a * 2 ^ ((N + 1) * k) < 2 ^ (a + (N + 1) * k) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h3 (Nat.two_pow_pos _)
  have h6 : 2 ^ (a + (N + 1) * k) ≤ 2 ^ (2 ^ N / (N + 1)) :=
    Nat.pow_le_pow_right (by decide) h4
  have h7 : a * (2 ^ N + 1) ^ k ≤ a * 2 ^ ((N + 1) * k) := Nat.mul_le_mul_left a h2
  omega

/-- The budget lies strictly between polynomial and every `2^{δn}`. -/
theorem logBudget_gap :
    (∀ d, 0 < d → ∃ C, ∀ n, logBudget n ≤ C * 2 ^ (n / d)) ∧
      ¬ PolynomiallyBounded logBudget :=
  ⟨fun d hd => ⟨2 ^ (2 ^ d), fun n => logBudget_le d n hd⟩, logBudget_not_polynomial⟩

/-! ## The one-bit algebra of Anthropic's key idea -/

/-- Basis index `2a + b` for the two bits `(a, b)`. -/
def swapM (i j : Fin 4) : Int :=
  if j.val = (match i.val with | 1 => 2 | 2 => 1 | v => v) then 1 else 0

def idM (i j : Fin 4) : Int := if i = j then 1 else 0

/-- The singlet vector `|01⟩ − |10⟩`. Twice the singlet projector is `u uᵀ`. -/
def u (i : Fin 4) : Int := match i.val with | 1 => 1 | 2 => -1 | _ => 0

def singlet2 (i j : Fin 4) : Int := u i * u j

def mul4 (A B : Fin 4 → Fin 4 → Int) (i j : Fin 4) : Int :=
  A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j

/-- SWAP = I − 2·singlet. -/
theorem swap_eq_id_sub_singlet : ∀ i j : Fin 4, swapM i j = idM i j - singlet2 i j := by
  decide

/-- `(2·singlet)² = 2·(2·singlet)`: the singlet is a projector. -/
theorem singlet_sq : ∀ i j : Fin 4, mul4 singlet2 singlet2 i j = 2 * singlet2 i j := by
  decide

/-- SWAP² = I. -/
theorem swap_sq : ∀ i j : Fin 4, mul4 swapM swapM i j = idM i j := by
  decide

end Issue638.ETH
