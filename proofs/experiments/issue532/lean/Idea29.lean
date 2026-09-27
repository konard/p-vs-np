/-!
# Issue #532, Idea 29: reduction chains and polynomial composition

**Verdict: correct tool, insufficient alone (general theorem proved).**

Polynomial-time many-one (Karp) reductions compose: the explicit
repository-style polynomials `⟨coefficient, degree⟩` with
`eval n = coefficient * (n + 1) ^ degree` are closed under addition and
under substitution, so the running time and output size of a chain
`f` then `g` are again polynomially bounded, and correctness composes.
Consequently membership in a polynomial-time class is inherited backwards
along reductions.

The same theorem shows why "reduce NP to P" is not a shortcut: reducing a
language `L` to *some* language already decidable in polynomial time is
*equivalent* to deciding `L` in polynomial time (`reducesToP_iff_inP`).
Every such claimed proof therefore owes a real, polynomially bounded,
correctness-preserving reduction, which for an NP-complete `L` is exactly
P = NP.  Nothing here decides P vs NP.

The file is standalone (Lean core only); the polynomial structure mirrors
`Complexity.Polynomial` field for field.  Running time is an abstract cost
function supplied together with the map; the theorems hold for every such
cost function.
-/

namespace Issue532.Idea29

/-- Explicit polynomial bound `coefficient * (n + 1) ^ degree`. -/
structure Poly where
  coefficient : Nat
  degree : Nat
  deriving Repr

/-- Evaluation of an explicit polynomial bound. -/
def Poly.eval (p : Poly) (n : Nat) : Nat :=
  p.coefficient * (n + 1) ^ p.degree

/-- Sum bound: coefficients add, degree is the maximum. -/
def Poly.add (p q : Poly) : Poly :=
  ⟨p.coefficient + q.coefficient, max p.degree q.degree⟩

/-- Substitution bound for `q ∘ p`. -/
def Poly.comp (p q : Poly) : Poly :=
  ⟨q.coefficient * (p.coefficient + 1) ^ q.degree, p.degree * q.degree⟩

/-- The identity-size bound `n ≤ 1 * (n + 1) ^ 1`. -/
def Poly.linear : Poly := ⟨1, 1⟩

/-- The zero bound. -/
def Poly.zero : Poly := ⟨0, 0⟩

theorem pow_pos_succ (n k : Nat) : 1 ≤ (n + 1) ^ k :=
  Nat.pow_pos (Nat.succ_pos n)

/-- Explicit polynomials are monotone in the input length. -/
theorem Poly.eval_mono (p : Poly) {m n : Nat} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  unfold Poly.eval
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) _)

/-- Closure under addition: `p.eval n + q.eval n ≤ (p.add q).eval n` for all `n`. -/
theorem Poly.add_bound (p q : Poly) (n : Nat) :
    p.eval n + q.eval n ≤ (p.add q).eval n := by
  unfold Poly.eval Poly.add
  simp only
  have hp : (n + 1) ^ p.degree ≤ (n + 1) ^ max p.degree q.degree :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left _ _)
  have hq : (n + 1) ^ q.degree ≤ (n + 1) ^ max p.degree q.degree :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right _ _)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)

/-- Closure under composition: `q.eval (p.eval n) ≤ (p.comp q).eval n` for all `n`. -/
theorem Poly.comp_bound (p q : Poly) (n : Nat) :
    q.eval (p.eval n) ≤ (p.comp q).eval n := by
  unfold Poly.eval Poly.comp
  simp only
  have hX : 1 ≤ (n + 1) ^ p.degree := pow_pos_succ n p.degree
  have h1 : p.coefficient * (n + 1) ^ p.degree + 1
      ≤ (p.coefficient + 1) * (n + 1) ^ p.degree := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left hX _
  have h2 : (p.coefficient * (n + 1) ^ p.degree + 1) ^ q.degree
      ≤ ((p.coefficient + 1) * (n + 1) ^ p.degree) ^ q.degree :=
    Nat.pow_le_pow_left h1 _
  rw [Nat.mul_pow, ← Nat.pow_mul] at h2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h2

/-- The existential form of closure under composition. -/
theorem poly_comp_exists (p q : Poly) : ∃ r : Poly, ∀ n, q.eval (p.eval n) ≤ r.eval n :=
  ⟨p.comp q, Poly.comp_bound p q⟩

/-- The existential form of closure under addition. -/
theorem poly_add_exists (p q : Poly) : ∃ r : Poly, ∀ n, p.eval n + q.eval n ≤ r.eval n :=
  ⟨p.add q, Poly.add_bound p q⟩

/-- `f` is a many-one reduction from `L` to `M`. -/
def IsReduction {α β : Type} (f : α → β) (L : α → Prop) (M : β → Prop) : Prop :=
  ∀ x, L x ↔ M (f x)

/-- Correctness of reductions composes. -/
theorem IsReduction.comp {α β γ : Type} {f : α → β} {g : β → γ}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (hf : IsReduction f L M) (hg : IsReduction g M N) :
    IsReduction (g ∘ f) L N :=
  fun x => Iff.trans (hf x) (hg (f x))

/-- The identity is a reduction from a language to itself. -/
theorem IsReduction.id {α : Type} (L : α → Prop) : IsReduction (fun x => x) L L :=
  fun _ => Iff.rfl

/-- A map with an abstract cost function and explicit polynomial bounds on its
time and on the size of its output. -/
structure PolyMap {α β : Type} (sa : α → Nat) (sb : β → Nat) where
  fn : α → β
  time : α → Nat
  timeBound : Poly
  sizeBound : Poly
  time_le : ∀ x, time x ≤ timeBound.eval (sa x)
  size_le : ∀ x, sb (fn x) ≤ sizeBound.eval (sa x)

/-- Running `f` then `g`: time is the sum, bounds are explicit. -/
def PolyMap.comp {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    (f : PolyMap sa sb) (g : PolyMap sb sc) : PolyMap sa sc where
  fn := fun x => g.fn (f.fn x)
  time := fun x => f.time x + g.time (f.fn x)
  timeBound := f.timeBound.add (f.sizeBound.comp g.timeBound)
  sizeBound := f.sizeBound.comp g.sizeBound
  time_le := by
    intro x
    have h1 := f.time_le x
    have h2 : g.time (f.fn x) ≤ g.timeBound.eval (f.sizeBound.eval (sa x)) :=
      Nat.le_trans (g.time_le (f.fn x)) (g.timeBound.eval_mono (f.size_le x))
    have h3 := Poly.comp_bound f.sizeBound g.timeBound (sa x)
    have h4 := Poly.add_bound f.timeBound (f.sizeBound.comp g.timeBound) (sa x)
    omega
  size_le := by
    intro x
    exact Nat.le_trans (Nat.le_trans (g.size_le (f.fn x))
      (g.sizeBound.eval_mono (f.size_le x))) (Poly.comp_bound _ _ _)

/-- The time of a composed chain of polynomially bounded maps is polynomial. -/
theorem comp_time_poly {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    (f : PolyMap sa sb) (g : PolyMap sb sc) :
    ∃ r : Poly, ∀ x, f.time x + g.time (f.fn x) ≤ r.eval (sa x) :=
  ⟨(f.comp g).timeBound, (f.comp g).time_le⟩

/-- The identity map with zero cost. -/
def PolyMap.ident {α : Type} (sa : α → Nat) : PolyMap sa sa where
  fn := fun x => x
  time := fun _ => 0
  timeBound := Poly.zero
  sizeBound := Poly.linear
  time_le := fun _ => Nat.zero_le _
  size_le := by
    intro x
    unfold Poly.eval Poly.linear
    simp only [Nat.pow_one, Nat.one_mul]
    exact Nat.le_succ _

/-- A polynomially bounded reduction from `L` to `M`. -/
structure PolyReduction {α β : Type} (sa : α → Nat) (sb : β → Nat)
    (L : α → Prop) (M : β → Prop) extends PolyMap sa sb where
  correct : IsReduction fn L M

/-- Polynomially bounded reductions compose. -/
def PolyReduction.comp {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (f : PolyReduction sa sb L M) (g : PolyReduction sb sc M N) :
    PolyReduction sa sc L N :=
  { f.toPolyMap.comp g.toPolyMap with
    correct := fun x => Iff.trans (f.correct x) (g.correct (f.fn x)) }

/-- The composed reduction computes `g ∘ f`. -/
theorem PolyReduction.comp_fn {α β γ : Type} {sa : α → Nat} {sb : β → Nat} {sc : γ → Nat}
    {L : α → Prop} {M : β → Prop} {N : γ → Prop}
    (f : PolyReduction sa sb L M) (g : PolyReduction sb sc M N) :
    (f.comp g).fn = g.fn ∘ f.fn := rfl

/-- A decider with an abstract cost function and an explicit polynomial time bound. -/
structure PolyDecider {α : Type} (sa : α → Nat) (L : α → Prop) where
  decide : α → Bool
  time : α → Nat
  bound : Poly
  correct : ∀ x, L x ↔ decide x = true
  time_le : ∀ x, time x ≤ bound.eval (sa x)

/-- Abstract polynomial-time class relative to a size function. -/
def InP {α : Type} (sa : α → Nat) (L : α → Prop) : Prop :=
  Nonempty (PolyDecider sa L)

/-- Pull a decider back along a polynomially bounded reduction. -/
def PolyDecider.pullback {α β : Type} {sa : α → Nat} {sb : β → Nat}
    {L : α → Prop} {M : β → Prop}
    (r : PolyReduction sa sb L M) (d : PolyDecider sb M) : PolyDecider sa L where
  decide := fun x => d.decide (r.fn x)
  time := fun x => r.time x + d.time (r.fn x)
  bound := r.timeBound.add (r.sizeBound.comp d.bound)
  correct := fun x => Iff.trans (r.correct x) (d.correct (r.fn x))
  time_le := by
    intro x
    have h1 := r.time_le x
    have h2 : d.time (r.fn x) ≤ d.bound.eval (r.sizeBound.eval (sa x)) :=
      Nat.le_trans (d.time_le (r.fn x)) (d.bound.eval_mono (r.size_le x))
    have h3 := Poly.comp_bound r.sizeBound d.bound (sa x)
    have h4 := Poly.add_bound r.timeBound (r.sizeBound.comp d.bound) (sa x)
    omega

/-- The polynomial-time class is closed backwards under polynomial reductions. -/
theorem inP_of_reduction {α β : Type} {sa : α → Nat} {sb : β → Nat}
    {L : α → Prop} {M : β → Prop}
    (r : PolyReduction sa sb L M) (h : InP sb M) : InP sa L :=
  match h with
  | ⟨d⟩ => ⟨d.pullback r⟩

/-- An abstract class of languages over `α` closed backwards under reductions. -/
def ClosedUnderReductions {α : Type} (sa : α → Nat) (C : (α → Prop) → Prop) : Prop :=
  ∀ L M, Nonempty (PolyReduction sa sa L M) → C M → C L

/-- `InP` is such a class. -/
theorem inP_closed {α : Type} (sa : α → Nat) : ClosedUnderReductions sa (InP sa) :=
  fun _ _ hr hM => match hr with
    | ⟨r⟩ => inP_of_reduction r hM

/-- Any class closed under reductions that contains one language complete for a
family contains the whole family. -/
theorem closed_contains_family {α : Type} (sa : α → Nat) (C : (α → Prop) → Prop)
    (hC : ClosedUnderReductions sa C) (family : (α → Prop) → Prop) (K : α → Prop)
    (hard : ∀ L, family L → Nonempty (PolyReduction sa sa L K)) (hK : C K) :
    ∀ L, family L → C L :=
  fun L hL => hC L K (hard L hL) hK

/-- The open obligation of any "reduce `L` to an easy problem" argument:
a real polynomially bounded reduction of `L` to a language already in `InP`. -/
def ReducesToP {α : Type} (sa : α → Nat) (L : α → Prop) : Prop :=
  ∃ (β : Type) (sb : β → Nat) (M : β → Prop),
    Nonempty (PolyReduction sa sb L M) ∧ InP sb M

/-- The obligation is exactly as hard as the goal: reducing `L` to some
polynomial-time language is equivalent to `L` itself being polynomial-time. -/
theorem reducesToP_iff_inP {α : Type} (sa : α → Nat) (L : α → Prop) :
    ReducesToP sa L ↔ InP sa L := by
  constructor
  · intro ⟨_, _, _, ⟨r⟩, hM⟩
    exact inP_of_reduction r hM
  · intro h
    exact ⟨α, sa, L, ⟨{ PolyMap.ident sa with correct := IsReduction.id L }⟩, h⟩

end Issue532.Idea29
