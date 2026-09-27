/-!
# Issue #532, Idea 37: parameterized structure

A fixed-parameter tractable (FPT) algorithm runs in time `f(k) · n^c`, where
`k` is a structural parameter of the instance (treewidth, solution size, number
of variables, ...). This file proves exactly when such a bound is polynomial.

Main results:

* `fpt_param_bound_poly`: if `f(k) ≤ n^a` then `f(k) · n^c ≤ n^(a+c)`.
* `fpt_log_param_poly`: if `2^k ≤ n` (the parameter is at most `log₂ n`) then
  `2^k · n^c ≤ n^(c+1)`.
* `exp_beats_poly`, `exists_threshold`, `poly_lt_two_pow`: for every `c, d`,
  eventually `c · (n+1)^d < 2^n`; in particular `∃ n, c · (n+1)^d < 2^n`.
* `fpt_full_param_not_poly`: when the parameter equals the input size
  (`k = n`), the FPT bound `2^n · n^c` beats every polynomial `a · (n+1)^d`
  somewhere, so it is not a polynomial bound.
* `fpt_log_param_polytime`, `LogParamFPTObligation`,
  `obligation_gives_poly_time`: an FPT algorithm with a logarithmically bounded
  parameter on **all** instances is a polynomial-time algorithm. For an
  NP-complete problem this is the open obligation, and it implies P = NP.
* `tested`: a monotone cost is bounded when the parameter is bounded.
-/

namespace Issue532.Idea37

/-- **Monotone parameter cost.** If the cost is monotone in the parameter and the
parameter is at most `cap`, the cost is at most `cost cap`. -/
theorem tested (cost : Nat → Nat) (k cap : Nat)
    (monotone : ∀ a b, a ≤ b → cost a ≤ cost b)
    (bounded : k ≤ cap) : cost k ≤ cost cap := by
  exact monotone k cap bounded

/-! ## (a) Bounded parameter functions give polynomial time -/

/-- **Polynomially bounded parameter function.** If `f k ≤ n^a` then the FPT bound
`f k · n^c` is at most `n^(a+c)`. -/
theorem fpt_param_bound_poly (f : Nat → Nat) (k n a c : Nat) (h : f k ≤ n ^ a) :
    f k * n ^ c ≤ n ^ (a + c) := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_right _ h

/-- **Logarithmic parameter.** If `2^k ≤ n`, then `2^k · n^c ≤ n^(c+1)`. -/
theorem fpt_log_param_poly (k n c : Nat) (h : 2 ^ k ≤ n) :
    2 ^ k * n ^ c ≤ n ^ (c + 1) := by
  calc 2 ^ k * n ^ c ≤ n * n ^ c := Nat.mul_le_mul_right _ h
    _ = n ^ (c + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-! ## (b) Exponential beats every polynomial -/

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

/-- **Growth theorem.** For all `c d` and all `n ≥ 2 ^ (2 * (c + d) + 1)`,
`c * (n + 1) ^ d < 2 ^ n`. -/
theorem exp_beats_poly (c d : Nat) :
    ∀ n, 2 ^ (2 * (c + d) + 1) ≤ n → c * (n + 1) ^ d < 2 ^ n := by
  intro n hn
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.one_le_two_pow) hn
  obtain ⟨L, hL1, hL2⟩ := dyadic_bracket n hn1
  have hLbig : 2 * (c + d) + 1 ≤ L := by
    rcases Nat.lt_or_ge L (2 * (c + d) + 1) with hlt | hge
    · have : 2 ^ (L + 1) ≤ 2 ^ (2 * (c + d) + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hge
  have hlin : (c + d) * (L + 1) < 2 ^ L := linear_lt_exp (c + d) L hLbig
  have hsum : c + d * (L + 1) < n := by
    have : c + d * (L + 1) ≤ (c + d) * (L + 1) := by
      rw [Nat.add_mul]
      have : c ≤ c * (L + 1) := Nat.le_mul_of_pos_right c (by omega)
      omega
    omega
  have hbase : (n + 1) ^ d ≤ 2 ^ ((L + 1) * d) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) d
  have hc : c < 2 ^ c := lt_two_pow_self c
  have hpos : 0 < 2 ^ ((L + 1) * d) := Nat.two_pow_pos _
  calc c * (n + 1) ^ d ≤ c * 2 ^ ((L + 1) * d) := Nat.mul_le_mul_left c hbase
    _ < 2 ^ c * 2 ^ ((L + 1) * d) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (c + (L + 1) * d) := (Nat.pow_add 2 c _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)

/-- Threshold form: `c * (n + 1) ^ d < 2 ^ n` for all sufficiently large `n`. -/
theorem exists_threshold (c d : Nat) : ∃ N, ∀ n, N ≤ n → c * (n + 1) ^ d < 2 ^ n :=
  ⟨2 ^ (2 * (c + d) + 1), exp_beats_poly c d⟩

/-- **Local growth lemma.** For every `c d` there is `n` with `c * (n + 1) ^ d < 2 ^ n`;
with `c = 1` this is `(n + 1) ^ d < 2 ^ n`. -/
theorem poly_lt_two_pow (c d : Nat) : ∃ n, c * (n + 1) ^ d < 2 ^ n := by
  obtain ⟨N, hN⟩ := exists_threshold c d
  exact ⟨N, hN N (Nat.le_refl N)⟩

/-- **Unbounded parameter.** When the parameter equals the input size, the FPT bound
`2^n · n^c` exceeds every polynomial `a · (n+1)^d` at some `n`. -/
theorem fpt_full_param_not_poly (a d c : Nat) : ∃ n, a * (n + 1) ^ d < 2 ^ n * n ^ c := by
  obtain ⟨N, hN⟩ := exists_threshold a d
  refine ⟨N + 1, ?_⟩
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hpos : 0 < (N + 1) ^ c := Nat.pow_pos (Nat.succ_pos N)
  exact Nat.lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ hpos)

/-! ## The obligation -/

/-- Running time `time I` is bounded by `f(param I) · (size I)^c`. -/
def FPTBound {Inst : Type} (time size param : Inst → Nat) (f : Nat → Nat) (c : Nat) : Prop :=
  ∀ I, time I ≤ f (param I) * size I ^ c

/-- The parameter is logarithmic on every instance: `2^(param I) ≤ (size I)^b`. -/
def LogBoundedParam {Inst : Type} (size param : Inst → Nat) (b : Nat) : Prop :=
  ∀ I, 2 ^ param I ≤ size I ^ b

/-- **FPT with a logarithmic parameter is polynomial time.** -/
theorem fpt_log_param_polytime {Inst : Type} (time size param : Inst → Nat) (c b : Nat)
    (hfpt : FPTBound time size param (fun k => 2 ^ k) c)
    (hlog : LogBoundedParam size param b) :
    ∀ I, time I ≤ size I ^ (b + c) := by
  intro I
  exact Nat.le_trans (hfpt I) (fpt_param_bound_poly (fun k => 2 ^ k) (param I) (size I) b c (hlog I))

/-- **Open obligation.** A correct algorithm for the problem with a `2^k · n^c` FPT bound
for a parameter that is logarithmic on **all** instances. For an NP-complete problem,
with `Correct` and `time` the real correctness predicate and step count, meeting it
gives P = NP. -/
def LogParamFPTObligation {Inst Alg : Type} (Correct : Alg → Prop)
    (time : Alg → Inst → Nat) (size : Inst → Nat) : Prop :=
  ∃ (A : Alg) (param : Inst → Nat) (c b : Nat),
    Correct A ∧ FPTBound (time A) size param (fun k => 2 ^ k) c ∧ LogBoundedParam size param b

/-- **The obligation yields a correct polynomial-time algorithm.** -/
theorem obligation_gives_poly_time {Inst Alg : Type} (Correct : Alg → Prop)
    (time : Alg → Inst → Nat) (size : Inst → Nat)
    (h : LogParamFPTObligation Correct time size) :
    ∃ A d, Correct A ∧ ∀ I, time A I ≤ size I ^ d := by
  obtain ⟨A, param, c, b, hA, hfpt, hlog⟩ := h
  exact ⟨A, b + c, hA, fpt_log_param_polytime (time A) size param c b hfpt hlog⟩

/-- Numerical check: at `n = 16, k = 4, c = 2`: `2^4 · 16^2 = 4096 = 16^3`. -/
example : 2 ^ 4 * 16 ^ 2 ≤ 16 ^ 3 := by decide

end Issue532.Idea37
