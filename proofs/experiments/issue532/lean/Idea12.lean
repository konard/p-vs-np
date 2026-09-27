/-!
# Issue #532, Idea 12: reduction verification

Many-one reductions `f : α → β` from `L : α → Bool` to `M : β → Bool`
(`IsReduction f L M := ∀ x, L x = M (f x)`), first without resources and
then with an explicit polynomial cost model.

Proved for all types, languages and maps:

* `reduction_id`, `reduction_comp`, `reduction_complement`: reductions form a
  preorder and commute with complement.
* `const_reduction_iff`, `const_not_reduction`: a const (single-valued) map reduces `L`
  exactly when `L` is const (single-valued), so it never reduces a nontrivial language.
* `trivial_target`, `nontrivial_target`: a reduction into a trivial language
  forces the source to be trivial.
* `decider_transfer`: a decider for `M` on the image of `f` yields a decider
  for `L`.
* `yes_preserving_not_sufficient`: for every nontrivial `L`, a map sending all
  yes-instances to yes-instances need not be a reduction.
* `reduces_to_any_nontrivial`: every `L` reduces to every nontrivial `M` if the
  reduction may be as expensive as deciding `L`; so resource bounds on the
  reduction are essential, and "X reduces to SAT" says nothing about the
  hardness of X.
* `poly_bound_compose`, `poly_sum_bound`, `poly_decider_transfer`,
  `poly_reduction_comp`, `hardness_transfer`: in a cost model where algorithms
  carry a time function and reductions carry an output-size bound, polynomial
  deciders pull back along polynomial reductions with explicit constants,
  polynomial reductions compose, and hardness pushes forward.

Verdict: reductions are the correct tool for transferring algorithms and
hardness, but they are insufficient alone: they move the question between
problems and never answer it. Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea12

variable {α β γ : Type}

/-- `f` is a many-one reduction from `L` to `M`. -/
def IsReduction (f : α → β) (L : α → Bool) (M : β → Bool) : Prop := ∀ x, L x = M (f x)

/-- `L` has a yes-instance and a no-instance. -/
def Nontrivial (L : α → Bool) : Prop := ∃ a b, L a = true ∧ L b = false

theorem reduction_id (L : α → Bool) : IsReduction id L L := fun _ => rfl

/-- Reductions compose. -/
theorem reduction_comp (f : α → β) (g : β → γ) (L : α → Bool) (M : β → Bool) (N : γ → Bool)
    (hf : IsReduction f L M) (hg : IsReduction g M N) : IsReduction (fun x => g (f x)) L N :=
  fun x => (hf x).trans (hg (f x))

/-- A reduction also reduces the complements. -/
theorem reduction_complement (f : α → β) (L : α → Bool) (M : β → Bool) (h : IsReduction f L M) :
    IsReduction f (fun x => !L x) (fun y => !M y) := by
  intro x; simp only [h x]

/-- A const map is a reduction iff `L` is const with value `M c`. -/
theorem const_reduction_iff (L : α → Bool) (M : β → Bool) (c : β) :
    IsReduction (fun _ : α => c) L M ↔ ∀ x, L x = M c := Iff.rfl

/-- A const map never reduces a nontrivial language. -/
theorem const_not_reduction (L : α → Bool) (M : β → Bool) (hL : Nontrivial L) (c : β) :
    ¬ IsReduction (fun _ : α => c) L M := by
  intro h
  obtain ⟨a, b, ha, hb⟩ := hL
  have h1 := h a
  have h2 := h b
  simp only at h1 h2
  rw [ha] at h1; rw [hb] at h2
  rw [← h1] at h2
  exact Bool.noConfusion h2

/-- A reduction into a const language forces the source to be const. -/
theorem trivial_target (f : α → β) (L : α → Bool) (M : β → Bool) (b : Bool)
    (hM : ∀ y, M y = b) (h : IsReduction f L M) : ∀ x, L x = b :=
  fun x => (h x).trans (hM (f x))

/-- Reductions preserve nontriviality: the target of a reduction from a nontrivial language is nontrivial. -/
theorem nontrivial_target (f : α → β) (L : α → Bool) (M : β → Bool)
    (h : IsReduction f L M) (hL : Nontrivial L) : Nontrivial M := by
  obtain ⟨a, b, ha, hb⟩ := hL
  exact ⟨f a, f b, (h a).symm.trans ha, (h b).symm.trans hb⟩

/-- A decider for `M` that is correct on the image of `f` gives a decider for `L`. -/
theorem decider_transfer (f : α → β) (L : α → Bool) (M : β → Bool) (P : β → Prop)
    (hP : ∀ x, P (f x)) (g : β → Bool) (hg : ∀ y, P y → g y = M y) (h : IsReduction f L M) :
    ∀ x, g (f x) = L x :=
  fun x => (hg (f x) (hP x)).trans (h x).symm

/--
One-directional maps are not reductions: for every nontrivial `L` and every
yes-instance `y` of `M`, the const map to `y` sends yes to yes but is not a
reduction.
-/
theorem yes_preserving_not_sufficient (L : α → Bool) (M : β → Bool) (hL : Nontrivial L)
    (y : β) (hy : M y = true) :
    (∀ x, L x = true → M ((fun _ : α => y) x) = true) ∧ ¬ IsReduction (fun _ : α => y) L M :=
  ⟨fun _ _ => hy, const_not_reduction L M hL y⟩

/--
Every language reduces to every nontrivial language when the reduction is
allowed to decide `L` itself. Hence a reduction *to* a hard problem is no
evidence of hardness, and cost bounds on reductions are essential.
-/
theorem reduces_to_any_nontrivial (L : α → Bool) (M : β → Bool) (hM : Nontrivial M) :
    ∃ f : α → β, IsReduction f L M := by
  obtain ⟨a, b, ha, hb⟩ := hM
  refine ⟨fun x => if L x then a else b, fun x => ?_⟩
  cases hx : L x
  · simp [hx, hb]
  · simp [hx, ha]

/-! ### Polynomial cost model -/

/-- An algorithm: its input/output behaviour and its running time on each input. -/
structure Algo (α β : Type) where
  run : α → β
  time : α → Nat

/-- `t` is bounded by `c · (sz x + 1)^d`. -/
def PolyBounded (sz : α → Nat) (t : α → Nat) : Prop := ∃ c d, ∀ x, t x ≤ c * (sz x + 1) ^ d

/-- `L` has a polynomial-time decider (w.r.t. the input size `sz`). -/
def PolyDecider (sz : α → Nat) (L : α → Bool) : Prop :=
  ∃ A : Algo α Bool, (∀ x, A.run x = L x) ∧ PolyBounded sz A.time

/-- A polynomial reduction: correct, polynomial time, and polynomial output size. -/
def PolyReduction (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool) (R : Algo α β) : Prop :=
  IsReduction R.run L M ∧
    ∃ e k, ∀ x, R.time x ≤ e * (szA x + 1) ^ k ∧ szB (R.run x) ≤ e * (szA x + 1) ^ k

/-- Composing polynomial bounds, with explicit constants. -/
theorem poly_bound_compose (n a b e k c d : Nat) (ha : a ≤ e * (n + 1) ^ k)
    (hb : b ≤ c * (a + 1) ^ d) : b ≤ c * (e + 1) ^ d * (n + 1) ^ (k * d) := by
  have hpos : 1 ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) (Nat.zero_le k)
  have h1 : a + 1 ≤ (e + 1) * (n + 1) ^ k := by rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (a + 1) ^ d ≤ ((e + 1) * (n + 1) ^ k) ^ d := Nat.pow_le_pow_left h1 d
  rw [Nat.mul_pow, ← Nat.pow_mul] at h2
  rw [Nat.mul_assoc]
  exact Nat.le_trans hb (Nat.mul_le_mul_left c h2)

/-- Summing two polynomial bounds into one. -/
theorem poly_sum_bound (n e k C d : Nat) :
    e * (n + 1) ^ k + C * (n + 1) ^ (k * d) ≤ (e + C) * (n + 1) ^ (k * d + k) := by
  have h1 : (n + 1) ^ k ≤ (n + 1) ^ (k * d + k) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ (k * d) ≤ (n + 1) ^ (k * d + k) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left e h1) (Nat.mul_le_mul_left C h2)

/--
Polynomial deciders pull back along polynomial reductions: if `L` reduces to
`M` in polynomial time and output size and `M` has a polynomial decider, then
so does `L` (the composed algorithm, with explicit constants).
-/
theorem poly_decider_transfer (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool)
    (R : Algo α β) (hR : PolyReduction szA szB L M R) (hM : PolyDecider szB M) :
    PolyDecider szA L := by
  obtain ⟨hred, e, k, hek⟩ := hR
  obtain ⟨A, hA, c, d, hcd⟩ := hM
  refine ⟨⟨fun x => A.run (R.run x), fun x => R.time x + A.time (R.run x)⟩, ?_, ?_⟩
  · intro x
    show A.run (R.run x) = L x
    rw [hA, hred x]
  · refine ⟨e + c * (e + 1) ^ d, k * d + k, fun x => ?_⟩
    show R.time x + A.time (R.run x) ≤ _
    have h1 := (hek x).1
    have h2 := poly_bound_compose (szA x) (szB (R.run x)) (A.time (R.run x)) e k c d (hek x).2 (hcd _)
    have h3 := poly_sum_bound (szA x) e k (c * (e + 1) ^ d) d
    omega

/-- Polynomial reductions compose (with explicit constants). -/
theorem poly_reduction_comp (szA : α → Nat) (szB : β → Nat) (szC : γ → Nat)
    (L : α → Bool) (M : β → Bool) (N : γ → Bool) (R : Algo α β) (S : Algo β γ)
    (hR : PolyReduction szA szB L M R) (hS : PolyReduction szB szC M N S) :
    PolyReduction szA szC L N ⟨fun x => S.run (R.run x), fun x => R.time x + S.time (R.run x)⟩ := by
  obtain ⟨hr, e, k, hek⟩ := hR
  obtain ⟨hs, e', k', hek'⟩ := hS
  refine ⟨reduction_comp R.run S.run L M N hr hs, e + e' * (e + 1) ^ k', k * k' + k, fun x => ?_⟩
  have h3 := poly_sum_bound (szA x) e k (e' * (e + 1) ^ k') k'
  have ht := poly_bound_compose (szA x) (szB (R.run x)) (S.time (R.run x)) e k e' k' (hek x).2 (hek' _).1
  have hz := poly_bound_compose (szA x) (szB (R.run x)) (szC (S.run (R.run x))) e k e' k' (hek x).2 (hek' _).2
  have h1 := (hek x).1
  constructor
  · show R.time x + S.time (R.run x) ≤ _
    omega
  · show szC (S.run (R.run x)) ≤ _
    omega

/--
Hardness transfers forward: if `L` reduces polynomially to `M` and `L` has no
polynomial decider, then neither has `M`.
-/
theorem hardness_transfer (szA : α → Nat) (szB : β → Nat) (L : α → Bool) (M : β → Bool)
    (R : Algo α β) (hR : PolyReduction szA szB L M R) (hL : ¬ PolyDecider szA L) :
    ¬ PolyDecider szB M :=
  fun hM => hL (poly_decider_transfer szA szB L M R hR hM)

end Issue532.Idea12
