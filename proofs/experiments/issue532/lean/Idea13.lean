import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 13: from approximation to exactness

Integer-valued optimisation problems are modelled by an optimum
`opt : α → Nat`; a ratio `(q+1)/q` or `num/den` is written multiplicatively
to stay in `Nat`.

Proved for all values and all parameters:

* `approx_exact_nat` (minimisation) and `approx_exact_max` (maximisation):
  a `(1 + 1/q)`-approximation is exact whenever `OPT < q` (resp. `OPT ≤ q`),
  because the error is an integer smaller than 1.
* `threshold_sharp`: the condition cannot be weakened: for every `q ≥ 1` there
  is a `(1+1/q)`-approximate value that is not optimal with `OPT = q`.
* `ratio_two_not_exact`: for every `OPT ≥ 1` a 2-approximate value need not be
  optimal.
* `scheme_exact_below_bound`, `fptas_poly_bounded_exact`: an approximation
  scheme run with `q = B(x) > OPT(x)` is exact; if its time is polynomial in
  `|x| + q` and `B` is polynomially bounded, the exact algorithm is
  polynomial (Garey–Johnson's argument for strongly NP-hard problems).
* `approx_decides_gap`: an algorithm with ratio `num/den` decides every gap
  promise problem whose gap exceeds `num/den`; this is how PCP-based
  inapproximability turns better approximation into P = NP.

Verdict: approximation gives exactness only below an integrality gap; the
open obligation `PolyApprox` beyond a published NP-hardness threshold would
itself prove P = NP. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea13

variable {α : Type}

/--
Minimisation: if `OPT ≤ A`, `A·q ≤ OPT·(q+1)` (ratio `1 + 1/q`) and `OPT < q`,
then `A = OPT`.
-/
theorem approx_exact_nat (A OPT q : Nat) (h1 : OPT ≤ A) (h2 : A * q ≤ OPT * (q + 1))
    (h3 : OPT < q) : A = OPT := by
  apply Nat.le_antisymm _ h1
  apply Nat.le_of_not_lt
  intro hlt
  have : (OPT + 1) * q ≤ A * q := Nat.mul_le_mul_right q hlt
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one] at *
  omega

/--
Maximisation: if `A ≤ OPT`, `OPT·q ≤ A·(q+1)` (ratio `q/(q+1)`) and `OPT ≤ q`,
then `A = OPT`.
-/
theorem approx_exact_max (A OPT q : Nat) (h1 : A ≤ OPT) (h2 : OPT * q ≤ A * (q + 1))
    (h3 : OPT ≤ q) : A = OPT := by
  apply Nat.le_antisymm h1
  apply Nat.le_of_not_lt
  intro hlt
  have : (A + 1) * (q + 1) ≤ OPT * (q + 1) := Nat.mul_le_mul_right (q + 1) hlt
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one] at *
  have : OPT * (q + 1) = OPT * q + OPT := by rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The bound `OPT < q` is sharp: with `OPT = q`, the value `q + 1` is `(1+1/q)`-approximate but not optimal. -/
theorem threshold_sharp (q : Nat) :
    q ≤ q + 1 ∧ (q + 1) * q ≤ q * (q + 1) ∧ q + 1 ≠ q := by
  refine ⟨by omega, ?_, by omega⟩
  rw [Nat.mul_comm]; exact Nat.le_refl _

/-- For every `OPT ≥ 1`, the value `2·OPT` is a 2-approximation that is not optimal. -/
theorem ratio_two_not_exact (OPT : Nat) (h : 1 ≤ OPT) :
    ∃ A, OPT ≤ A ∧ A ≤ 2 * OPT ∧ A ≠ OPT :=
  ⟨2 * OPT, by omega, Nat.le_refl _, by omega⟩

/--
An approximation scheme `S q x` with ratio `1 + 1/q`, run with `q = B x` for a
bound `OPT x < B x`, returns the exact optimum.
-/
theorem scheme_exact_below_bound (opt : α → Nat) (S : Nat → α → Nat) (B : α → Nat)
    (hS : ∀ q x, opt x ≤ S q x ∧ S q x * q ≤ opt x * (q + 1)) (hB : ∀ x, opt x < B x) :
    ∀ x, S (B x) x = opt x :=
  fun x => approx_exact_nat _ _ _ (hS (B x) x).1 (hS (B x) x).2 (hB x)

/--
Polynomially bounded optimum + fully polynomial scheme ⇒ polynomial exact
algorithm, with explicit constants. `T q x` is the running time of `S q x`.
-/
theorem fptas_poly_bounded_exact (sz opt : α → Nat) (S T : Nat → α → Nat) (B : α → Nat)
    (c d e k : Nat)
    (hS : ∀ q x, opt x ≤ S q x ∧ S q x * q ≤ opt x * (q + 1))
    (hT : ∀ q x, T q x ≤ c * (sz x + q + 1) ^ d)
    (hB : ∀ x, opt x < B x) (hBpoly : ∀ x, B x ≤ e * (sz x + 1) ^ k) :
    ∀ x, S (B x) x = opt x ∧ T (B x) x ≤ c * (e + 1) ^ d * (sz x + 1) ^ ((k + 1) * d) := by
  intro x
  refine ⟨scheme_exact_below_bound opt S B hS hB x, ?_⟩
  have p1 : sz x + 1 ≤ (sz x + 1) ^ (k + 1) := by
    have := Nat.pow_le_pow_right (n := sz x + 1) (by omega) (show 1 ≤ k + 1 by omega)
    rw [Nat.pow_one] at this; exact this
  have p2 : (sz x + 1) ^ k ≤ (sz x + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : e * (sz x + 1) ^ k ≤ e * (sz x + 1) ^ (k + 1) := Nat.mul_le_mul_left e p2
  have hbase : sz x + B x + 1 ≤ (e + 1) * (sz x + 1) ^ (k + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    have := hBpoly x
    omega
  have hpow : (sz x + B x + 1) ^ d ≤ ((e + 1) * (sz x + 1) ^ (k + 1)) ^ d := Nat.pow_le_pow_left hbase d
  rw [Nat.mul_pow, ← Nat.pow_mul] at hpow
  rw [Nat.mul_assoc]
  exact Nat.le_trans (hT (B x) x) (Nat.mul_le_mul_left c hpow)

/--
Gap decision: suppose every instance satisfies the promise `opt x ≤ a` or
`opt x · den > a · num`. An algorithm with `opt x ≤ A x` and
`A x · den ≤ opt x · num` decides which case holds by testing `A x · den ≤ a · num`.
-/
theorem approx_decides_gap (opt A : α → Nat) (a num den : Nat)
    (hA : ∀ x, opt x ≤ A x ∧ A x * den ≤ opt x * num)
    (hgap : ∀ x, opt x ≤ a ∨ a * num < opt x * den) :
    ∀ x, (A x * den ≤ a * num ↔ opt x ≤ a) := by
  intro x
  obtain ⟨h1, h2⟩ := hA x
  constructor
  · intro h
    rcases hgap x with h' | h'
    · exact h'
    · have : opt x * den ≤ A x * den := Nat.mul_le_mul_right den h1
      omega
  · intro h
    have : opt x * num ≤ a * num := Nat.mul_le_mul_right num h
    omega

/-! ## The obligation over the shared machine model

An approximation algorithm is a `Complexity.Machine` that computes (in the
sense of `Issue532.Machines.Computes`, with the step count of the run as its
time) a binary word whose value is the approximate optimum. Instances are words
of the shared model. -/

open Complexity Issue532.Machines

/-- Value of a binary word, least significant bit first. -/
def wordValue : Word → Nat
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * wordValue w

/-- **Open obligation.** A polynomial-time machine that outputs, for every
instance `x`, a value `A x` with `opt x ≤ A x` and `A x · den ≤ opt x · num`
(ratio `num/den` for the minimisation problem `opt`). For problems and ratios
below a published NP-hardness-of-approximation threshold, this statement
implies P = NP (via `approx_decides_gap` and the corresponding PCP reduction). -/
def PolyApprox (opt : Word → Nat) (num den : Nat) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p ∧
    ∀ x, opt x ≤ wordValue (f x) ∧ wordValue (f x) * den ≤ opt x * num

/-- Conditional theorem: `PolyApprox` for ratio `num/den` gives a
polynomial-time machine whose output answers every gap promise problem with gap
larger than `num/den` by the single comparison `A x · den ≤ a · num`. -/
theorem polyApprox_decides_gap (opt : Word → Nat) (a num den : Nat)
    (h : PolyApprox opt num den) (hgap : ∀ x, opt x ≤ a ∨ a * num < opt x * den) :
    ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p ∧
      ∀ x, (wordValue (f x) * den ≤ a * num ↔ opt x ≤ a) := by
  obtain ⟨m, f, p, hm, hA⟩ := h
  exact ⟨m, f, p, hm, approx_decides_gap opt (fun x => wordValue (f x)) a num den hA hgap⟩

/-- A language as a minimisation problem: optimum `1` on members and
`num + 1` on non-members. -/
def optOf (L : Language) (num : Nat) (x : Word) : Nat := if L x then 1 else num + 1

open Classical in
/-- The language read off a machine's output by the threshold `num`. -/
noncomputable def thresholdLanguage (num : Nat) (m : Machine) : Language := fun x =>
  decide (∃ (f : Word → Word) (p : Polynomial), Computes m f p ∧ wordValue (f x) ≤ num)

/-- **Non-vacuity.** For every ratio with `den ≥ 1`, some problem has no
polynomial-time machine approximation: `PolyApprox` is not provable for every
`opt`. -/
theorem not_forall_polyApprox (num den : Nat) (hden : 1 ≤ den) :
    ¬ ∀ opt : Word → Nat, PolyApprox opt num den := by
  intro hall
  obtain ⟨L, hL⟩ := exists_language_not_in_family encMachine
    (fun _ _ h => encMachine_injective h) (thresholdLanguage num)
  obtain ⟨m, f, p, hm, hA⟩ := hall (optOf L num)
  apply hL m
  funext x
  have hval : (∃ (g : Word → Word) (q : Polynomial), Computes m g q ∧ wordValue (g x) ≤ num) ↔
      wordValue (f x) ≤ num := by
    constructor
    · rintro ⟨g, q, hg, hgx⟩
      rwa [computes_unique hm hg]
    · intro hx
      exact ⟨f, p, hm, hx⟩
  have hden' : wordValue (f x) ≤ wordValue (f x) * den := Nat.le_mul_of_pos_right _ hden
  obtain ⟨h1, h2⟩ := hA x
  classical
  unfold thresholdLanguage
  cases hLx : L x with
  | true =>
    simp only [optOf, hLx, ite_true, Nat.one_mul] at h1 h2
    exact decide_eq_true (hval.mpr (by omega))
  | false =>
    simp only [optOf, hLx] at h1 h2
    exact decide_eq_false (fun hx => by have := hval.mp hx; simp at h1; omega)

end Issue532.Idea13
