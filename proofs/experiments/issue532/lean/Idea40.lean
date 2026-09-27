import proofs.experiments.issue532.lean.Machines

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
* `run_correct`, `runCost_bound`, `poly_solver_for`, `self_reduction_solver_bound`:
  schema (abstract costs). A self-reduction with **one** recursive call of the
  same answer and polynomial step cost yields a correct polynomial-cost solver
  (`AdditiveSelfReductionFor`).
* Machine model (`Issue532.Machines`, time = `Run` step count). The open
  obligation `SATMachineSelfReduction` (= `MachineSelfReductionOf SAT`) asks for
  a polynomial-time `Complexity.Machine` step map (`Computes`) that never
  lengthens the word, removes one variable (`satSize`) and keeps `SAT`, plus a
  machine deciding `SAT` on variable-free formulas (`DecidesOn`).
  `inP_sat_of_machineSelfReduction` and `pEqualsNP_of_machineSelfReduction`
  derive `InP SAT` and `PEqualsNP`; the iteration step is the named known
  theorem `IterationClosure` and SAT hardness is the hypothesis `SATHard`. The
  composition itself is mechanised (`iterate_length_spec`,
  `inP_of_promise_reduction`). `not_forall_machineSelfReductionOf` shows the
  machine predicate is not satisfied by every language.

Verdict: correct tool, insufficient alone. Induction yields a polynomial algorithm
only when each step adds, rather than multiplies, polynomial cost; for SAT the
one-call step is the open obligation `SATMachineSelfReduction`.
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

/-- **Schema** (abstract, no machine model): an additive-cost self-reduction for
the predicate `answer`. Size-0 instances are answered by `base` (cost at most `c`),
and one step maps a size-`(n+1)` instance to a size-`n` instance **with the same
answer** at polynomial cost. The costs here are free functions, so this schema is
only the bookkeeping part of the idea; the statement about real machines is
`SATMachineSelfReduction` below. -/
def AdditiveSelfReductionFor (size : Inst → Nat) (answer : Inst → Bool) : Prop :=
  ∃ (base : Inst → Bool) (step : Inst → Inst) (baseCost stepCost : Inst → Nat) (c a k : Nat),
    (∀ I, size I = 0 → base I = answer I) ∧ (∀ I, baseCost I ≤ c) ∧
    (∀ I n, size I = n + 1 → size (step I) = n ∧ answer (step I) = answer I) ∧
    (∀ I, stepCost I ≤ a * (size I + 1) ^ k)

/-- **Schema theorem.** Data meeting `AdditiveSelfReductionFor` yield a correct
solver whose (abstract) cost is polynomial in the size. -/
theorem poly_solver_for (size : Inst → Nat) (answer : Inst → Bool)
    (h : AdditiveSelfReductionFor size answer) :
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

/-- **Explicit solver bound.** For any data meeting the conditions of
`AdditiveSelfReductionFor`, the specific solver `run base step (size I)` is correct and its
cost `runCost` is at most `(c + a) * (size I + 1) ^ (k + 1)`. -/
theorem self_reduction_solver_bound (size : Inst → Nat) (answer base : Inst → Bool)
    (step : Inst → Inst) (baseCost stepCost : Inst → Nat) (c a k : Nat)
    (hbase : ∀ I, size I = 0 → base I = answer I) (hbc : ∀ I, baseCost I ≤ c)
    (hstep : ∀ I n, size I = n + 1 → size (step I) = n ∧ answer (step I) = answer I)
    (hcost : ∀ I, stepCost I ≤ a * (size I + 1) ^ k) (I : Inst) :
    run base step (size I) I = answer I ∧
      runCost baseCost stepCost step (size I) I ≤ (c + a) * (size I + 1) ^ (k + 1) :=
  ⟨run_correct size answer base step hbase hstep (size I) I rfl,
   Nat.le_trans
     (runCost_bound size step baseCost stepCost c a k (fun I n h => (hstep I n h).1) hbc hcost
       (size I) I rfl)
     (additive_poly_closed c a k (size I))⟩

/-- Check: the two-branch cost with zero overhead is exactly `2^n` at `n = 5`. -/
example : branchCost (fun _ => 0) 5 = 32 := by decide

/-! ## The machine model: one-call self-reduction for SAT

From here on the cost is the step count of a `Complexity.Machine` run. SAT is the
shared-model language `Issue532.Machines.SAT` on words, and the size of a word is
the number of variables of the formula it denotes, `numVars (decode x)`. -/

section MachineModel

open Complexity (Machine Polynomial Run initial Word Language InP PEqualsNP)
open Issue532.Machines (Computes DecidesOn SAT SATHard numVars decode decodeAux clauseBound
  Clause run_deterministic inP_of_promise_reduction pEqualsNP_of_inP_sat computes_unique
  encMachine encMachine_injective encList_prefixFree encInstruction_prefixFree
  exists_language_not_in_family)

/-- Size of a word for the self-reduction: the number of variables of the formula
it denotes (`0` for variable-free formulas). -/
def satSize (x : Word) : Nat := numVars (decode x)

theorem clauseBound_append (cur : Clause) (l : Issue532.Machines.Lit) :
    clauseBound (cur ++ [l]) = max (clauseBound cur) (l.var + 1) := by
  induction cur with
  | nil => simp [clauseBound]
  | cons l' c ih => simp only [List.cons_append, clauseBound, ih]; omega

theorem numVars_decodeAux_le : (w : List Bool) → (k : Nat) → (cur : Clause) →
    numVars (decodeAux w k cur) ≤ max (clauseBound cur) (k + w.length)
  | [], k, cur => by simp [decodeAux, numVars]
  | [b], k, cur => by cases b <;> simp [decodeAux, numVars]
  | true :: true :: rest, k, cur => by
    have ih := numVars_decodeAux_le rest (k + 1) cur
    simp only [decodeAux, List.length_cons]
    omega
  | false :: p :: rest, k, cur => by
    have ih := numVars_decodeAux_le rest 0 (cur ++ [⟨k, p⟩])
    simp only [decodeAux, List.length_cons]
    rw [clauseBound_append] at ih
    have hv : (⟨k, p⟩ : Issue532.Machines.Lit).var = k := rfl
    omega
  | true :: false :: rest, k, cur => by
    have ih := numVars_decodeAux_le rest 0 []
    simp only [decodeAux, numVars, List.length_cons]
    simp only [clauseBound] at ih
    omega

/-- A word of length `n` denotes a formula with at most `n` variables. -/
theorem satSize_le_length (x : Word) : satSize x ≤ x.length := by
  have := numVars_decodeAux_le x 0 []
  simp only [clauseBound, Nat.zero_add] at this
  unfold satSize decode
  omega

/-- `iter f n x` applies `f` to `x` `n` times. -/
def iter (f : Word → Word) : Nat → Word → Word
  | 0, x => x
  | n + 1, x => iter f n (f x)

/-- A **machine self-reduction with one call per level** for the language `L`,
with size `satSize`: a machine `m` computes a step map `f` in polynomial time that
never lengthens its input, lowers the size by one (down to `0`) and keeps the
answer of `L`; a machine `d` decides `L` in polynomial time on words of size `0`.
This is the machine version of `AdditiveSelfReductionFor`. -/
def MachineSelfReductionOf (L : Language) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial) (d : Machine) (q : Polynomial),
    Computes m f p ∧ (∀ x, (f x).length ≤ x.length) ∧
    (∀ x, satSize (f x) ≤ satSize x - 1 ∧ L (f x) = L x) ∧
    DecidesOn d q (fun y => satSize y = 0) L

/-- **Open obligation.** SAT has a polynomial-time machine self-reduction with one
recursive call per level (`MachineSelfReductionOf SAT`): a `Complexity.Machine`
(`Computes`) maps every encoded formula, in polynomial time and without
lengthening it, to an equisatisfiable formula (`SAT (f x) = SAT x`) with one
variable fewer, and a machine decides `SAT` on variable-free formulas
(`DecidesOn`). The familiar self-reduction ("set the next variable to both
values") makes two calls per level and is exponential (`branchCost_exponential`). -/
def SATMachineSelfReduction : Prop := MachineSelfReductionOf SAT

/-- **Known theorem, not mechanised here** (closure of polynomial time under
iteration of a length-non-increasing polynomial-time map a linear number of
times). If a machine computes `f` in polynomial time and `|f x| ≤ |x|`, then some
machine computes `x ↦ iter f |x| x` in polynomial time: run `f` `|x|` times while
keeping a counter, at cost at most `|x| · (p(|x|) + O(|x|))` on a multi-tape
machine, and simulate that machine on one tape with quadratic overhead.
References: M. Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
Theorem 7.8 (multi-tape to single-tape simulation) and Section 7.2 (polynomial
composition); S. Arora and B. Barak, *Computational Complexity: A Modern
Approach*, Claim 1.6 and Section 1.6 (robustness of the model). -/
def IterationClosure : Prop :=
  ∀ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p →
    (∀ x, (f x).length ≤ x.length) →
    ∃ (m' : Machine) (p' : Polynomial), Computes m' (fun x => iter f x.length x) p'

/-- `n` steps lower the size by `n` and keep the answer. -/
theorem iterate_spec (L : Language) (f : Word → Word)
    (hf : ∀ x, satSize (f x) ≤ satSize x - 1 ∧ L (f x) = L x) :
    ∀ n x, satSize (iter f n x) ≤ satSize x - n ∧ L (iter f n x) = L x := by
  intro n
  induction n with
  | zero => intro x; simp [iter]
  | succ n ih =>
    intro x
    show satSize (iter f n (f x)) ≤ _ ∧ L (iter f n (f x)) = _
    obtain ⟨h1, h2⟩ := ih (f x)
    obtain ⟨h3, h4⟩ := hf x
    exact ⟨by omega, by rw [h2, h4]⟩

/-- Iterating the step `|x|` times reaches size `0` with the same answer. -/
theorem iterate_length_spec (L : Language) (f : Word → Word)
    (hf : ∀ x, satSize (f x) ≤ satSize x - 1 ∧ L (f x) = L x) (x : Word) :
    satSize (iter f x.length x) = 0 ∧ L x = L (iter f x.length x) := by
  obtain ⟨h1, h2⟩ := iterate_spec L f hf x.length x
  have := satSize_le_length x
  exact ⟨by omega, h2.symm⟩

/-- **Additive cost on machines.** Given the iteration closure, a machine
self-reduction with one call per level puts `L` in P: iterate the step `|x|`
times (a polynomial-time map into the size-`0` promise, by `IterationClosure`) and
compose with the base decider (`inP_of_promise_reduction`). -/
theorem inP_of_machineSelfReduction (hI : IterationClosure) {L : Language}
    (h : MachineSelfReductionOf L) : InP L := by
  obtain ⟨m, f, p, d, q, hm, hlen, hf, hd⟩ := h
  obtain ⟨m', p', hm'⟩ := hI m f p hm hlen
  exact inP_of_promise_reduction hm' (fun x => (iterate_length_spec L f hf x).1)
    (fun x => (iterate_length_spec L f hf x).2) hd

/-- **Conditional theorem.** The obligation puts SAT in P. -/
theorem inP_sat_of_machineSelfReduction (hI : IterationClosure)
    (h : SATMachineSelfReduction) : InP SAT :=
  inP_of_machineSelfReduction hI h

/-- **Conditional theorem.** With the Cook–Levin hardness of SAT (`SATHard`, a
hypothesis), the obligation gives P = NP. -/
theorem pEqualsNP_of_machineSelfReduction (hI : IterationClosure) (hard : SATHard)
    (h : SATMachineSelfReduction) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (inP_sat_of_machineSelfReduction hI h)

/-! ### Non-vacuity: not every language has a machine self-reduction -/

open Classical in
/-- The map computed by `m`, if it computes one in polynomial time. -/
noncomputable def mapOf (m : Machine) : Word → Word :=
  if h : ∃ (f : Word → Word) (p : Polynomial), Computes m f p then Classical.choose h else id

theorem mapOf_eq {m : Machine} {f : Word → Word} {p : Polynomial} (hm : Computes m f p) :
    mapOf m = f := by
  unfold mapOf
  split
  · rename_i h
    obtain ⟨p', hp'⟩ := Classical.choose_spec h
    exact computes_unique hp' hm
  · rename_i h
    exact absurd ⟨f, p, hm⟩ h

open Classical in
/-- The answer of `d` on `y`: whether some run of `d` from `y` accepts. -/
noncomputable def acceptsOf (d : Machine) : Language :=
  fun y => decide (∃ t, Run d (initial y) t true)

open Classical in
theorem acceptsOf_eq {d : Machine} {y : Word} {t : Nat} {b : Bool}
    (h : Run d (initial y) t b) : acceptsOf d y = b := by
  unfold acceptsOf
  cases b with
  | true => exact decide_eq_true ⟨t, h⟩
  | false =>
    refine decide_eq_false ?_
    rintro ⟨t', h'⟩
    exact Bool.noConfusion (run_deterministic h h').2

/-- The language determined by a step machine and a base machine. -/
noncomputable def selfReductionLanguage (md : Machine × Machine) : Language :=
  fun x => acceptsOf md.2 (iter (mapOf md.1) x.length x)

def encPair (md : Machine × Machine) : Word := encMachine md.1 ++ encMachine md.2

theorem encPair_injective (a b : Machine × Machine) (h : encPair a = encPair b) : a = b := by
  obtain ⟨m, d⟩ := a
  obtain ⟨m', d'⟩ := b
  obtain ⟨h1, h2⟩ := encList_prefixFree (encList_prefixFree encInstruction_prefixFree)
    m.program m'.program _ _ h
  have hm : m = m' := by cases m; cases m'; simp only at h1; rw [h1]
  simp only at h2
  rw [hm, encMachine_injective h2]

/-- A language with a machine self-reduction is the language of its pair of
machines. -/
theorem machineSelfReductionOf_eq {L : Language} (h : MachineSelfReductionOf L) :
    ∃ md, selfReductionLanguage md = L := by
  obtain ⟨m, f, p, d, q, hm, _, hf, hd⟩ := h
  refine ⟨(m, d), funext fun x => ?_⟩
  obtain ⟨h0, hL⟩ := iterate_length_spec L f hf x
  obtain ⟨t, b, _, hrun, hb⟩ := hd _ h0
  show acceptsOf d (iter (mapOf m) x.length x) = L x
  rw [mapOf_eq hm, acceptsOf_eq hrun, hb, hL]

/-- **Non-vacuity.** `MachineSelfReductionOf` is not a property of every
language (Cantor's argument over pairs of machines), so the obligation
`SATMachineSelfReduction` is a real constraint on SAT. -/
theorem not_forall_machineSelfReductionOf : ¬ ∀ L : Language, MachineSelfReductionOf L := by
  intro hall
  obtain ⟨L, hL⟩ := exists_language_not_in_family encPair encPair_injective selfReductionLanguage
  obtain ⟨md, hmd⟩ := machineSelfReductionOf_eq (hall L)
  exact hL md hmd

end MachineModel

end Issue532.Idea40
