import proofs.experiments.issue532.lean.Circuits

/-!
# Issue #532, Idea 15: circuit depth versus size

Boolean formulas (fan-out-1 circuits) over variables, NOT and fan-in-2
AND/OR, with gate-counting `size` (leaves and gates), `leaves` and `depth`.

Proved for all formulas and all parameters:

* `size_le_pow_depth`, `leaves_le_pow_depth`, `depth_lt_size`:
  `depth f < size f < 2^(depth f + 1)` and `leaves f ≤ 2^(depth f)`.
  Depth is therefore at least `log₂(size + 1) − 1` and at most `size − 1`.
* `chain_size`, `chain_depth`, `eval_chain`: the left-deep AND chain on
  `n + 1` variables has size `2n + 1` and depth `n` (the upper extreme).
* `bal_size`, `bal_depth`, `eval_bal`: the balanced AND tree on `2^d`
  variables has size `2^(d+1) − 1` and depth `d` (the lower extreme).
* `same_function_different_depth`: for every `d`, the chain and the balanced
  tree compute the same function (AND of `2^d` variables) with the same size
  `2^(d+1) − 1`, but depths `2^d − 1` and `d`.
* `sizeLB_implies_depthLB`: a superpolynomial formula-size lower bound for a
  family implies a superlogarithmic depth lower bound for it.

Tie to the shared machine model. `FormulaSizeLBFor` and `DepthLBFor` are
schemas over a formula family. Their instances for the language
`Issue532.Machines.SAT`, read at length `n` through
`Issue532.Circuits.slice SAT n`, are the open obligations `SATFormulaSizeLB`
and `SATDepthLB`; `satSizeLB_implies_satDepthLB` relates them.

* `npNotInLogDepth_of_satDepthLB`: with `SATInNP`, `SATDepthLB` gives
  `NPNotInLogDepth` (an explicit NP language needs superlogarithmic formula
  depth), an NC¹-type separation. That is the honest conclusion.
* It does not give P ≠ NP: `pNotEqualsNP_of_satDepthLB` needs in addition
  `PSubsetLogDepth` (every language in P has logarithmic-depth formulas, a
  P ⊆ NC¹-type statement that is open and not assumed anywhere).
* Non-vacuity of the shapes: `andPow_sizeLB` and `andPow_depthLB` (a family
  that reads `2 ^ n` variables satisfies both), `var0_not_depthLB` (a family
  computed by one leaf satisfies neither).

Verdict: size and depth are distinct resources, related exactly by the
bounds above. Depth lower bounds are the right tool for NC¹-type
separations, but even the open obligation `SATDepthLB` would give NP ⊄ NC¹,
not P ≠ NP. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea15

open Complexity
open Issue532.Machines (SAT SATInNP)
open Issue532.Circuits (slice two_mul_sq_lt_two_pow)

/-- Formulas over variables `var i`, NOT, and fan-in-2 AND/OR. -/
inductive F where
  | var : Nat → F
  | neg : F → F
  | conj : F → F → F
  | disj : F → F → F

open F

def eval (ρ : Nat → Bool) : F → Bool
  | var i => ρ i
  | neg f => !eval ρ f
  | conj f g => eval ρ f && eval ρ g
  | disj f g => eval ρ f || eval ρ g

/-- Number of nodes (leaves and gates). -/
def size : F → Nat
  | var _ => 1
  | neg f => size f + 1
  | conj f g => size f + size g + 1
  | disj f g => size f + size g + 1

def leaves : F → Nat
  | var _ => 1
  | neg f => leaves f
  | conj f g => leaves f + leaves g
  | disj f g => leaves f + leaves g

def depth : F → Nat
  | var _ => 0
  | neg f => depth f + 1
  | conj f g => max (depth f) (depth g) + 1
  | disj f g => max (depth f) (depth g) + 1

theorem two_pow_mono (a b : Nat) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h

/-- A formula of depth `d` has fewer than `2^(d+1)` nodes. -/
theorem size_le_pow_depth (f : F) : size f + 1 ≤ 2 ^ (depth f + 1) := by
  induction f with
  | var _ => simp [size, depth]
  | neg f ih =>
    simp only [size, depth, Nat.pow_succ] at *
    omega
  | conj f g ihf ihg =>
    have h1 := two_pow_mono (depth f + 1) (max (depth f) (depth g) + 1) (by omega)
    have h2 := two_pow_mono (depth g + 1) (max (depth f) (depth g) + 1) (by omega)
    simp only [size, depth]
    rw [Nat.pow_succ 2 (max (depth f) (depth g) + 1)]
    omega
  | disj f g ihf ihg =>
    have h1 := two_pow_mono (depth f + 1) (max (depth f) (depth g) + 1) (by omega)
    have h2 := two_pow_mono (depth g + 1) (max (depth f) (depth g) + 1) (by omega)
    simp only [size, depth]
    rw [Nat.pow_succ 2 (max (depth f) (depth g) + 1)]
    omega

/-- A formula of depth `d` has at most `2^d` leaves. -/
theorem leaves_le_pow_depth (f : F) : leaves f ≤ 2 ^ depth f := by
  induction f with
  | var _ => simp [leaves, depth]
  | neg f ih =>
    have := two_pow_mono (depth f) (depth f + 1) (by omega)
    simp only [leaves, depth]; omega
  | conj f g ihf ihg =>
    have h1 := two_pow_mono (depth f) (max (depth f) (depth g)) (by omega)
    have h2 := two_pow_mono (depth g) (max (depth f) (depth g)) (by omega)
    simp only [leaves, depth, Nat.pow_succ]; omega
  | disj f g ihf ihg =>
    have h1 := two_pow_mono (depth f) (max (depth f) (depth g)) (by omega)
    have h2 := two_pow_mono (depth g) (max (depth f) (depth g)) (by omega)
    simp only [leaves, depth, Nat.pow_succ]; omega

/-- Depth is less than size. -/
theorem depth_lt_size (f : F) : depth f < size f := by
  induction f with
  | var _ => simp [size, depth]
  | neg f ih => simp only [size, depth]; omega
  | conj f g ihf ihg => simp only [size, depth]; omega
  | disj f g ihf ihg => simp only [size, depth]; omega

/-- Left-deep AND chain `((x₀ ∧ x₁) ∧ x₂) ∧ ⋯ ∧ xₙ`. -/
def chain : Nat → F
  | 0 => var 0
  | n + 1 => conj (chain n) (var (n + 1))

/-- Balanced AND tree on the `2^d` variables `x_{i·2^d}, …, x_{(i+1)·2^d − 1}`. -/
def bal : Nat → Nat → F
  | 0, i => var i
  | d + 1, i => conj (bal d (2 * i)) (bal d (2 * i + 1))

/-- `andRange a m ρ = ρ a ∧ ⋯ ∧ ρ (a + m − 1)`. -/
def andRange (a : Nat) : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | m + 1, ρ => andRange a m ρ && ρ (a + m)

theorem andRange_add (a m n : Nat) (ρ : Nat → Bool) :
    andRange a (m + n) ρ = (andRange a m ρ && andRange (a + m) n ρ) := by
  induction n with
  | zero => simp [andRange]
  | succ n ih =>
    rw [← Nat.add_assoc, andRange, ih, andRange, Bool.and_assoc, Nat.add_assoc]

theorem chain_size (n : Nat) : size (chain n) = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chain, size, ih]; omega

theorem chain_depth (n : Nat) : depth (chain n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [chain, depth, ih]; omega

theorem eval_chain (n : Nat) (ρ : Nat → Bool) : eval ρ (chain n) = andRange 0 (n + 1) ρ := by
  induction n with
  | zero => simp [chain, eval, andRange]
  | succ n ih => simp [chain, eval, andRange, ih] at *

theorem bal_size (d i : Nat) : size (bal d i) + 1 = 2 ^ (d + 1) := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    have h1 := ih (2 * i)
    have h2 := ih (2 * i + 1)
    simp only [bal, size]
    rw [Nat.pow_succ 2 (d + 1)]
    omega

theorem bal_depth (d i : Nat) : depth (bal d i) = d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp only [bal, depth, ih]; omega

theorem eval_bal (d i : Nat) (ρ : Nat → Bool) :
    eval ρ (bal d i) = andRange (i * 2 ^ d) (2 ^ d) ρ := by
  induction d generalizing i with
  | zero => simp [bal, eval, andRange]
  | succ d ih =>
    have e1 : i * 2 ^ (d + 1) = 2 * i * 2 ^ d := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, ← Nat.mul_assoc, Nat.mul_comm i 2]
    have e2 : (2 * i + 1) * 2 ^ d = 2 * i * 2 ^ d + 2 ^ d := by rw [Nat.add_mul, Nat.one_mul]
    have e3 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ, Nat.mul_two]
    simp only [bal, eval, ih]
    rw [e1, e3, andRange_add, e2]

/--
Same function, same size, exponentially different depth: for every `d`, the
chain and the balanced tree both compute the AND of `x₀, …, x_{2^d − 1}` with
`2^(d+1) − 1` nodes, but have depths `2^d − 1` and `d`.
-/
theorem same_function_different_depth (d : Nat) :
    (∀ ρ, eval ρ (chain (2 ^ d - 1)) = eval ρ (bal d 0)) ∧
    size (chain (2 ^ d - 1)) = size (bal d 0) ∧
    depth (chain (2 ^ d - 1)) = 2 ^ d - 1 ∧ depth (bal d 0) = d := by
  have hpos : 1 ≤ 2 ^ d := two_pow_mono 0 d (Nat.zero_le d)
  refine ⟨fun ρ => ?_, ?_, chain_depth _, bal_depth d 0⟩
  · rw [eval_chain, eval_bal, Nat.zero_mul, Nat.sub_add_cancel hpos]
  · have h1 := bal_size d 0
    rw [chain_size, Nat.pow_succ] at *
    omega

/-- `f` computes the Boolean function `g`. -/
def FormulaComputes (f : F) (g : (Nat → Bool) → Bool) : Prop := ∀ ρ, eval ρ f = g ρ

/--
Schema: the family `fam` has superpolynomial formula size: for every `c` there
is an `n` where every formula for `fam n` has size at least
`2^(c·(log₂ n + 1))` (roughly `n^c`). The family is a parameter; the SAT
instance is `SATFormulaSizeLB`.
-/
def FormulaSizeLBFor (fam : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c, ∃ n, ∀ f, FormulaComputes f (fam n) → 2 ^ (c * (Nat.log2 n + 1)) ≤ size f

/--
Schema: a superlogarithmic formula-depth lower bound for `fam`. The SAT
instance is `SATDepthLB`.
-/
def DepthLBFor (fam : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c, ∃ n, ∀ f, FormulaComputes f (fam n) → c * (Nat.log2 n + 1) ≤ depth f

/-- A superpolynomial size lower bound implies a superlogarithmic depth lower bound. -/
theorem sizeLB_implies_depthLB (fam : Nat → (Nat → Bool) → Bool) (h : FormulaSizeLBFor fam) :
    DepthLBFor fam := by
  intro c
  obtain ⟨n, hn⟩ := h c
  refine ⟨n, fun f hf => ?_⟩
  have h1 := hn f hf
  have h2 := size_le_pow_depth f
  apply Nat.le_of_not_lt
  intro hlt
  have := two_pow_mono (depth f + 1) (c * (Nat.log2 n + 1)) hlt
  omega

/-! ## The obligations on the shared machine model -/

/--
**Open obligation.** SAT (the language `Issue532.Machines.SAT`) has
superpolynomial formula size: for every `c` there is a length `n` at which
every formula computing SAT on words of length `n` has size at least
`2^(c·(log₂ n + 1))`.
-/
def SATFormulaSizeLB : Prop :=
  ∀ c, ∃ n, ∀ f, FormulaComputes f (slice SAT n) → 2 ^ (c * (Nat.log2 n + 1)) ≤ size f

/--
**Open obligation.** SAT needs superlogarithmic formula depth: for every `c`
there is a length `n` at which every formula computing SAT on words of length
`n` has depth at least `c·(log₂ n + 1)`.
-/
def SATDepthLB : Prop :=
  ∀ c, ∃ n, ∀ f, FormulaComputes f (slice SAT n) → c * (Nat.log2 n + 1) ≤ depth f

theorem satFormulaSizeLB_iff_for : SATFormulaSizeLB ↔ FormulaSizeLBFor (slice SAT) := Iff.rfl

theorem satDepthLB_iff_for : SATDepthLB ↔ DepthLBFor (slice SAT) := Iff.rfl

/-- The size obligation implies the depth obligation. -/
theorem satSizeLB_implies_satDepthLB (h : SATFormulaSizeLB) : SATDepthLB :=
  sizeLB_implies_depthLB (slice SAT) h

/--
**Open obligation** (the honest target, NP ⊄ NC¹-type). Some language with
`InNP` needs superlogarithmic formula depth.
-/
def NPNotInLogDepth : Prop :=
  ∃ L : Language, InNP L ∧
    ∀ c, ∃ n, ∀ f, FormulaComputes f (slice L n) → c * (Nat.log2 n + 1) ≤ depth f

/-- **Conditional theorem** (honest conclusion). With `SATInNP`, the depth
obligation for SAT gives `NPNotInLogDepth`. -/
theorem npNotInLogDepth_of_satDepthLB (mem : SATInNP) (h : SATDepthLB) : NPNotInLogDepth :=
  ⟨SAT, mem, h⟩

theorem npNotInLogDepth_of_satFormulaSizeLB (mem : SATInNP) (h : SATFormulaSizeLB) :
    NPNotInLogDepth :=
  npNotInLogDepth_of_satDepthLB mem (satSizeLB_implies_satDepthLB h)

/--
Not known, and not assumed anywhere: every language in P has formulas of
logarithmic depth (a P ⊆ NC¹-type statement, open and widely believed false).
Stated only to show what a depth lower bound would additionally need in order
to give P ≠ NP.
-/
def PSubsetLogDepth : Prop :=
  ∀ L : Language, InP L → ∃ c, ∀ n, ∃ f, FormulaComputes f (slice L n) ∧
    depth f < c * (Nat.log2 n + 1)

/-- The gap, made explicit: `SATDepthLB` gives P ≠ NP only together with the
unproved `PSubsetLogDepth`. -/
theorem pNotEqualsNP_of_satDepthLB (mem : SATInNP) (hPL : PSubsetLogDepth) (h : SATDepthLB) :
    PNotEqualsNP := by
  intro hPNP
  obtain ⟨c, hc⟩ := hPL SAT (hPNP SAT mem)
  obtain ⟨n, hn⟩ := h c
  obtain ⟨f, hf, hd⟩ := hc n
  have := hn f hf
  omega

/-! ## Non-vacuity of the lower-bound shapes -/

/-- Variables read by a formula, one entry per leaf. -/
def vars : F → List Nat
  | var i => [i]
  | neg f => vars f
  | conj f g => vars f ++ vars g
  | disj f g => vars f ++ vars g

theorem vars_length (f : F) : (vars f).length = leaves f := by
  induction f with
  | var _ => rfl
  | neg f ih => simp only [vars, leaves, ih]
  | conj f g ihf ihg => simp only [vars, leaves, List.length_append, ihf, ihg]
  | disj f g ihf ihg => simp only [vars, leaves, List.length_append, ihf, ihg]

theorem leaves_le_size (f : F) : leaves f ≤ size f := by
  induction f with
  | var _ => simp [leaves, size]
  | neg f ih => simp only [leaves, size]; omega
  | conj f g ihf ihg => simp only [leaves, size]; omega
  | disj f g ihf ihg => simp only [leaves, size]; omega

/-- A formula only depends on the variables it reads. -/
theorem eval_congr (f : F) (ρ σ : Nat → Bool) (h : ∀ i ∈ vars f, ρ i = σ i) :
    eval ρ f = eval σ f := by
  induction f with
  | var i => exact h i (by simp [vars])
  | neg f ih => simp only [eval, ih h]
  | conj f g ihf ihg =>
    simp only [eval]
    rw [ihf (fun i hi => h i (by simp [vars, hi])), ihg (fun i hi => h i (by simp [vars, hi]))]
  | disj f g ihf ihg =>
    simp only [eval]
    rw [ihf (fun i hi => h i (by simp [vars, hi])), ihg (fun i hi => h i (by simp [vars, hi]))]

theorem andRange_true (a m : Nat) : andRange a m (fun _ => true) = true := by
  induction m with
  | zero => rfl
  | succ m ih => simp [andRange, ih]

theorem andRange_false (a m i : Nat) (ρ : Nat → Bool) (h1 : a ≤ i) (h2 : i < a + m)
    (hi : ρ i = false) : andRange a m ρ = false := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [andRange]
    by_cases e : i = a + m
    · subst e; simp [hi]
    · rw [ih (by omega)]; rfl

/-- The AND of the first `2 ^ n` variables. It reads `2 ^ n` variables, so it
is not a function "on `n` variables"; it only shows that the lower-bound shapes
can be met. -/
def andPow (n : Nat) (ρ : Nat → Bool) : Bool := andRange 0 (2 ^ n) ρ

/-- Every formula for `andPow n` reads all `2 ^ n` variables. -/
theorem andPow_leaves (n : Nat) (f : F) (hf : FormulaComputes f (andPow n)) :
    2 ^ n ≤ leaves f := by
  rw [← vars_length, ← List.length_range (n := 2 ^ n)]
  apply List.Nodup.length_le_of_subset List.nodup_range
  intro i hi
  have hi' : i < 2 ^ n := List.mem_range.mp hi
  apply Classical.byContradiction
  intro hni
  have e := eval_congr f (fun _ => true) (fun j => !(j == i)) (fun j hj => by
    have : (j == i) = false := by
      cases hji : (j == i)
      · rfl
      · rw [beq_iff_eq] at hji; subst hji; exact absurd hj hni
    simp [this])
  rw [hf, hf] at e
  unfold andPow at e
  rw [andRange_true, andRange_false 0 (2 ^ n) i _ (Nat.zero_le i) (by omega) (by simp)] at e
  cases e

theorem mul_succ_le_two_pow (c : Nat) : c * (c + 7 + 1) ≤ 2 ^ (c + 7) := by
  have h := two_mul_sq_lt_two_pow (c + 7) (by omega)
  have h1 : c * (c + 7 + 1) ≤ (c + 7) * (c + 7 + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (c + 7) * (c + 7 + 1) = (c + 7) * (c + 7) + (c + 7) := Nat.mul_succ _ _
  have h3 : c + 7 ≤ (c + 7) * (c + 7) := Nat.le_mul_of_pos_right _ (by omega)
  generalize (c + 7) * (c + 7 + 1) = u at h1 h2
  generalize (c + 7) * (c + 7) = v at h h2 h3
  omega

/-- Non-vacuity (true side): `andPow` meets the size lower-bound shape. -/
theorem andPow_sizeLB : FormulaSizeLBFor andPow := by
  intro c
  refine ⟨2 ^ (c + 7), fun f hf => ?_⟩
  rw [Nat.log2_two_pow]
  have h1 := andPow_leaves _ f hf
  have h2 := leaves_le_size f
  have h3 : 2 ^ (c * (c + 7 + 1)) ≤ 2 ^ (2 ^ (c + 7)) := two_pow_mono _ _ (mul_succ_le_two_pow c)
  omega

/-- Non-vacuity (true side): `andPow` meets the depth lower-bound shape. -/
theorem andPow_depthLB : DepthLBFor andPow := sizeLB_implies_depthLB andPow andPow_sizeLB

/-- Non-vacuity (false side): a family computed by the single leaf `var 0`
meets neither shape. -/
theorem var0_not_depthLB : ¬ DepthLBFor (fun _ ρ => ρ 0) := by
  intro h
  obtain ⟨n, hn⟩ := h 1
  have := hn (var 0) (fun _ => rfl)
  simp [depth] at this

theorem var0_not_sizeLB : ¬ FormulaSizeLBFor (fun _ ρ => ρ 0) := fun h =>
  var0_not_depthLB (sizeLB_implies_depthLB _ h)

end Issue532.Idea15
