/-
  Basic.lean - Simple foundational proofs in Lean 4

  This file serves as a bootstrap for formal verification in Lean,
  demonstrating basic proof techniques and serving as a template for
  future P vs NP related proofs.
-/

-- Basic logical proofs
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := hpq hp

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq => ⟨hpq.2, hpq.1⟩

theorem or_commutative (p q : Prop) : p ∨ q → q ∨ p :=
  fun hpq => hpq.elim Or.inr Or.inl

-- Basic arithmetic proofs
theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

theorem zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

theorem add_comm (m n : Nat) : m + n = n + m := Nat.add_comm m n

theorem mul_one (n : Nat) : n * 1 = n := Nat.mul_one n

theorem one_mul (n : Nat) : 1 * n = n := Nat.one_mul n

-- Example: Proving a simple identity
theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := Nat.add_assoc a b c

-- Proof that double is even (useful for complexity theory)
def isEven (n : Nat) : Prop := ∃ k, n = 2 * k

theorem double_is_even (n : Nat) : isEven (2 * n) := ⟨n, rfl⟩

-- Simple function verification
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [factorial]
    omega

-- Basic list operations (relevant for algorithm complexity)
theorem list_length_append {α : Type} (l1 l2 : List α) :
  (l1 ++ l2).length = l1.length + l2.length := by
  induction l1 with
  | nil => simp
  | cons _ _ ih => simp [List.length, ih, Nat.add_assoc, Nat.add_comm]

-- Identity proof (foundation for rewriting)
theorem refl_eq {α : Type} (x : α) : x = x := rfl

#check modus_ponens
#check add_comm
#check factorial_pos
#check list_length_append

-- Verification successful
#print "✓ Basic Lean proofs verified successfully"
