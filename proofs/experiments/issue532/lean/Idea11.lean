/-!
# Issue #532, Idea 11: LP relaxation exactness (vertex cover integrality gap)

Fractional vertex covers are measured in *half units* to stay in `Nat`: a
half-integral fractional cover of a graph on vertices `0, …, n−1` is
`x : Nat → Nat` with `x i ≤ 2` (meaning `0, 1/2, 1`) and `x u + x v ≥ 2` on
every edge. Its LP value is `sumTo x n / 2`. An integral cover is
`s : Nat → Bool`; its cost is `card s n`.

Proved for every `n` (and every graph where stated):

* `half_feasible_complete`: on the complete graph `Kₙ` the all-`1/2` vector
  is feasible with value `n/2`.
* `frac_lower_complete`: for `n ≥ 2` every half-integral fractional cover of
  `Kₙ` has value at least `n/2`, so `n/2` is the half-integral LP optimum.
* `complete_cover_large`, `complete_cover_exact`: every integral cover of `Kₙ`
  has at least `n − 1` vertices, and `n − 1` is attained.
* `gap_family`: on `K_{2q}` the LP value is `q` while every integral cover
  has size `≥ 2q − 1`; the integrality gap `(2q − 1)/q = 2 − 1/q` tends to 2.
* `not_LPExact_complete`: for every `n ≥ 3` the relaxation is not exact on `Kₙ`.
* `rounding_two_approx`: for every graph, rounding all values `≥ 1/2` up gives
  an integral cover of cost at most twice the LP value.

Verdict: "the LP relaxation is automatically exact" is refuted by a general
theorem, and exact polynomial-size LPs for NP-hard polytopes are refuted in
full strength by Fiorini–Massar–Pokutta–Tiwary–de Wolf (2012/2015) (not
formalized). Nothing here proves or refutes P = NP.
-/

namespace Issue532.Idea11

/-- `sumTo x n = x 0 + … + x (n−1)`. -/
def sumTo (x : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo x n + x n

/-- Indicator of a Boolean. -/
def ind (b : Bool) : Nat := if b then 1 else 0

/-- Number of chosen vertices among `0, …, n−1`. -/
def card (s : Nat → Bool) (n : Nat) : Nat := sumTo (fun i => ind (s i)) n

/-- Half-integral fractional vertex cover of the graph `adj` on vertices `< n` (half units). -/
def FracCover (n : Nat) (adj : Nat → Nat → Bool) (x : Nat → Nat) : Prop :=
  (∀ i, i < n → x i ≤ 2) ∧ ∀ u v, u < n → v < n → adj u v = true → 2 ≤ x u + x v

/-- Integral vertex cover of the graph `adj` on vertices `< n`. -/
def IntCover (n : Nat) (adj : Nat → Nat → Bool) (s : Nat → Bool) : Prop :=
  ∀ u v, u < n → v < n → adj u v = true → s u = true ∨ s v = true

/-- The complete graph. -/
def complete (u v : Nat) : Bool := u != v

theorem sumTo_le (x y : Nat → Nat) : ∀ n, (∀ i, i < n → x i ≤ y i) → sumTo x n ≤ sumTo y n := by
  intro n
  induction n with
  | zero => intro _; exact Nat.le_refl 0
  | succ n ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    simp only [sumTo]; omega

theorem sumTo_const_le (x : Nat → Nat) (c : Nat) :
    ∀ n, (∀ i, i < n → c ≤ x i) → c * n ≤ sumTo x n := by
  intro n
  induction n with
  | zero => intro _; simp [sumTo]
  | succ n ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    simp only [sumTo, Nat.mul_succ]; omega

theorem sumTo_except (x : Nat → Nat) (c u : Nat) :
    ∀ n, u < n → (∀ i, i < n → i ≠ u → c ≤ x i) → c * (n - 1) ≤ sumTo x n := by
  intro n
  induction n with
  | zero => intro hu; omega
  | succ n ih =>
    intro hu h
    simp only [sumTo, Nat.add_sub_cancel]
    by_cases e : u = n
    · have := sumTo_const_le x c n (fun i hi => h i (by omega) (by omega))
      omega
    · have h1 := ih (by omega) (fun i hi hne => h i (by omega) hne)
      have h2 := h n (by omega) (fun h' => e h'.symm)
      cases n with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel] at h1
        rw [Nat.mul_succ]; omega

theorem card_all (s : Nat → Bool) : ∀ n, (∀ i, i < n → s i = true) → card s n = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [card, sumTo] at *
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]
    rfl

/-- On `Kₙ` the all-`1/2` vector is a fractional cover of value `n/2` (`n` half units). -/
theorem half_feasible_complete (n : Nat) :
    FracCover n complete (fun _ => 1) ∧ sumTo (fun _ => 1) n = n := by
  refine ⟨⟨fun _ _ => by simp, fun _ _ _ _ _ => by simp⟩, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]

theorem exists_zero_or_all_pos (x : Nat → Nat) :
    ∀ n, (∃ u, u < n ∧ x u = 0) ∨ (∀ i, i < n → 1 ≤ x i) := by
  intro n
  induction n with
  | zero => exact Or.inr (fun i hi => by omega)
  | succ n ih =>
    rcases ih with ⟨u, hu, hx⟩ | h
    · exact Or.inl ⟨u, by omega, hx⟩
    · by_cases e : x n = 0
      · exact Or.inl ⟨n, by omega, e⟩
      · refine Or.inr (fun i hi => ?_)
        by_cases ei : i = n
        · subst ei; omega
        · exact h i (by omega)

/--
For `n ≥ 2`, every half-integral fractional cover of `Kₙ` has value at least
`n/2`: the half-integral LP optimum of `Kₙ` is exactly `n/2`.
-/
theorem frac_lower_complete (n : Nat) (hn : 2 ≤ n) (x : Nat → Nat)
    (hx : FracCover n complete x) : n ≤ sumTo x n := by
  rcases exists_zero_or_all_pos x n with ⟨u, hu, h0⟩ | hall
  · have h2 : ∀ i, i < n → i ≠ u → 2 ≤ x i := by
      intro i hi hne
      have := hx.2 u i hu hi (by simp [complete]; omega)
      omega
    have := sumTo_except x 2 u n hu h2
    omega
  · have := sumTo_const_le x 1 n hall
    omega

/-- Every integral vertex cover of `Kₙ` has at least `n − 1` vertices. -/
theorem complete_cover_large (s : Nat → Bool) :
    ∀ n, IntCover n complete s → n ≤ card s n + 1 := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
    intro h
    have hsub : IntCover n complete s := fun u v hu hv ha => h u v (by omega) (by omega) ha
    have h1 := ih hsub
    cases hs : s n with
    | true =>
      simp only [card, sumTo, hs, ind] at *
      simp only [ite_true] at *
      omega
    | false =>
      have hall : ∀ i, i < n → s i = true := by
        intro i hi
        rcases h i n (by omega) (by omega) (by simp [complete]; omega) with h' | h'
        · exact h'
        · rw [hs] at h'; exact absurd h' (by decide)
      have := card_all s n hall
      simp only [card, sumTo, hs, ind] at *
      omega

theorem card_nonzero (n : Nat) : card (fun i => i != 0) (n + 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [card, sumTo] at *
    rw [ih]
    have : (n + 1 != 0) = true := by simp
    simp [ind, this]

/-- The bound `n − 1` is attained on `Kₙ` (take every vertex except `0`). -/
theorem complete_cover_exact (n : Nat) (hn : 1 ≤ n) :
    IntCover n complete (fun i => i != 0) ∧ card (fun i => i != 0) n = n - 1 := by
  constructor
  · intro u v _ _ ha
    simp only [complete, bne_iff_ne, ne_eq] at ha
    by_cases hu : u = 0
    · right; simp; omega
    · left; simp; omega
  · cases n with
    | zero => omega
    | succ m => rw [card_nonzero]; rfl

/--
Integrality gap family: on `K_{2q}` (`q ≥ 1`) the LP value is `q`
(`2q` half units) while every integral cover has at least `2q − 1` vertices,
so integral/LP `≥ 2 − 1/q`.
-/
theorem gap_family (q : Nat) (hq : 1 ≤ q) :
    FracCover (2 * q) complete (fun _ => 1) ∧ sumTo (fun _ => 1) (2 * q) = 2 * q ∧
    ∀ s, IntCover (2 * q) complete s → 2 * q - 1 ≤ card s (2 * q) := by
  obtain ⟨h1, h2⟩ := half_feasible_complete (2 * q)
  refine ⟨h1, h2, fun s hs => ?_⟩
  have := complete_cover_large s (2 * q) hs
  omega

/--
The relaxation is *exact* on a graph if every fractional value is matched by
an integral cover of at most the same cost.
-/
def LPExact (n : Nat) (adj : Nat → Nat → Bool) : Prop :=
  ∀ x, FracCover n adj x → ∃ s, IntCover n adj s ∧ 2 * card s n ≤ sumTo x n

/-- For every `n ≥ 3` the vertex cover LP is not exact on `Kₙ`. -/
theorem not_LPExact_complete (n : Nat) (hn : 3 ≤ n) : ¬ LPExact n complete := by
  intro h
  obtain ⟨hf, hv⟩ := half_feasible_complete n
  obtain ⟨s, hs, hc⟩ := h _ hf
  have := complete_cover_large s n hs
  rw [hv] at hc
  omega

/-- Threshold rounding: take every vertex with value at least `1/2`. -/
def round (x : Nat → Nat) (i : Nat) : Bool := decide (1 ≤ x i)

/--
Rounding is a 2-approximation against the LP, on every graph: the rounded set
is a cover and its size is at most `sumTo x n` half units, i.e. twice the LP value.
-/
theorem rounding_two_approx (n : Nat) (adj : Nat → Nat → Bool) (x : Nat → Nat)
    (hx : FracCover n adj x) :
    IntCover n adj (round x) ∧ card (round x) n ≤ sumTo x n := by
  constructor
  · intro u v hu hv ha
    have := hx.2 u v hu hv ha
    by_cases h : 1 ≤ x u
    · left; simp [round, h]
    · right; simp [round]; omega
  · apply sumTo_le
    intro i _
    by_cases h : 1 ≤ x i
    · simp [round, ind, h]
    · simp [round, ind, h]

end Issue532.Idea11
