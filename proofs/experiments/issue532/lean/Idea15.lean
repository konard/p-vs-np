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

Verdict: size and depth are distinct resources, related exactly by the
bounds above. Depth lower bounds are the right tool for NC¹-type
separations, but even the open obligation `DepthLB` for an explicit NP family
would give NP ⊄ NC¹, not P ≠ NP. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea15

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
def Computes (f : F) (g : (Nat → Bool) → Bool) : Prop := ∀ ρ, eval ρ f = g ρ

/--
Open obligation (not assumed): the family `fam` (with `fam n` on `n`
variables) has superpolynomial formula size: for every `c` there is an `n`
where every formula for `fam n` has size at least `2^(c·(log₂ n + 1))`
(roughly `n^c`).
-/
def FormulaSizeLB (fam : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c, ∃ n, ∀ f, Computes f (fam n) → 2 ^ (c * (Nat.log2 n + 1)) ≤ size f

/--
Open obligation (not assumed): a superlogarithmic formula-depth lower bound
for `fam`. For an explicit NP family it would give NP ⊄ NC¹.
-/
def DepthLB (fam : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c, ∃ n, ∀ f, Computes f (fam n) → c * (Nat.log2 n + 1) ≤ depth f

/-- A superpolynomial size lower bound implies a superlogarithmic depth lower bound. -/
theorem sizeLB_implies_depthLB (fam : Nat → (Nat → Bool) → Bool) (h : FormulaSizeLB fam) :
    DepthLB fam := by
  intro c
  obtain ⟨n, hn⟩ := h c
  refine ⟨n, fun f hf => ?_⟩
  have h1 := hn f hf
  have h2 := size_le_pow_depth f
  apply Nat.le_of_not_lt
  intro hlt
  have := two_pow_mono (depth f + 1) (c * (Nat.log2 n + 1)) hlt
  omega

end Issue532.Idea15
