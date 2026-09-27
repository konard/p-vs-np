import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 33: average-case to worst-case transfer

We work with languages `L : List Bool → Bool` and candidate algorithms
`A : List Bool → Bool` (plain functions in the counting part; machines of
the shared model in the machine part). Inputs of length `n`
are enumerated explicitly by `allInputs n` (a list of length `2^n` containing
every length-`n` bit string, without duplicates).

Main results (all general, for every language `L` and every length `n`):

* `allInputs_length`, `mem_allInputs`, `allInputs_nodup`: the enumeration is
  exactly the uniform sample space of size `2^n`.
* `flipOne_errors`: the algorithm `flipOne L`, which flips the answer of `L`
  on the all-false input of each length, errs on exactly one of the `2^n`
  inputs of length `n`.
* `flipOne_agreements`: it is correct on exactly `2^n - 1` inputs.
* `flipOne_error_vanishes`: for every `k`, once `n ≥ k` the error count times
  `k` is at most `2^n` (the error fraction `1/2^n` tends to `0`).
* `flipOne_worst_case_wrong`: yet at every length it is wrong on some input.
* `average_case_does_not_imply_worst_case`: the combined statement.
* `obligation_not_automatic`: the abstract schema
  `WorstToAverageObligationFor` fails for a suitable algorithm class for
  every language, so it can never follow from counting alone;
* `obligation_transfers`: the schema turns average-case easiness into
  worst-case easiness;
* machine part: `AvgPolyDec L δ` (a `Complexity.Machine` halting within a
  polynomial and wrong on at most `δ n` inputs of length `n`) and its
  transfer `WorstToAverage L δ := AvgPolyDec L δ → InP L`; budget zero is
  exactly P (`avgPolyDec_zero_iff`); the transfer for SAT with an
  average-case decider gives `InP SAT` and, with `SATHard`, P = NP
  (`pEqualsNP_of_worstToAverage`); refuting it gives P ≠ NP
  (`pNotEqualsNP_of_not_worstToAverage`); and some language has no
  average-case decider with one error per length (`exists_not_avgPolyDec`).

Verdict: "average-case success implies worst-case success" is refuted as an
automatic inference, for every language and every length. The full-strength
route requires a worst-case-to-average-case reduction for an NP-complete
problem, which is open and known to be limited (Feigenbaum–Fortnow 1993,
Bogdanov–Trevisan 2006; not formalized here).
-/

namespace Issue532.Idea33

/-- Every bit string of length `n`, in lexicographic order. -/
def allInputs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allInputs n).map (List.cons false) ++ (allInputs n).map (List.cons true)

/-- Number of list elements satisfying a Boolean test (via `filter`). -/
def count {α : Type} (p : α → Bool) (l : List α) : Nat := (l.filter p).length

theorem count_append {α : Type} (p : α → Bool) (l₁ l₂ : List α) :
    count p (l₁ ++ l₂) = count p l₁ + count p l₂ := by
  induction l₁ with
  | nil => simp [count]
  | cons a l ih =>
    cases h : p a <;> simp_all [count] <;> omega

theorem count_map {α β : Type} (p : β → Bool) (f : α → β) (l : List α) :
    count p (l.map f) = count (fun a => p (f a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : p (f a) <;> simp_all [count]

theorem count_false {α : Type} (l : List α) : count (fun _ => false) l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [count]

theorem count_le_length {α : Type} (p : α → Bool) (l : List α) :
    count p l ≤ l.length := by
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    cases h : p a <;> simp_all [count] <;> omega

/-- `count p` and `count (not ∘ p)` partition the list. -/
theorem count_add_count_not {α : Type} (p : α → Bool) (l : List α) :
    count p l + count (fun a => !p a) l = l.length := by
  induction l with
  | nil => simp [count]
  | cons a l ih =>
    cases h : p a <;> simp_all [count] <;> omega

/-- The enumeration has exactly `2^n` elements. -/
theorem allInputs_length (n : Nat) : (allInputs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allInputs, ih, Nat.pow_succ]; omega

/-- Every enumerated string has length `n`. -/
theorem length_of_mem_allInputs {n : Nat} {x : List Bool} (h : x ∈ allInputs n) :
    x.length = n := by
  induction n generalizing x with
  | zero => simp [allInputs] at h; simp [h]
  | succ n ih =>
    simp [allInputs] at h
    rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [ih hy]

/-- Every string of length `n` is enumerated (the sample space is complete). -/
theorem mem_allInputs (x : List Bool) : x ∈ allInputs x.length := by
  induction x with
  | nil => simp [allInputs]
  | cons b x ih => cases b <;> simp [allInputs, ih]

/-- The enumeration has no duplicates, so it is the uniform sample space. -/
theorem allInputs_nodup (n : Nat) : (allInputs n).Nodup := by
  induction n with
  | zero => simp [allInputs]
  | succ n ih =>
    simp only [allInputs]
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map _ (fun a b hab h => hab (List.cons.inj h).2) ih
    · exact List.Pairwise.map _ (fun a b hab h => hab (List.cons.inj h).2) ih
    · intro a ha b hb hab
      simp at ha hb
      rcases ha with ⟨y, _, rfl⟩
      rcases hb with ⟨z, _, rfl⟩
      simp at hab

/-- The all-false input of length `n`. -/
def zeros (n : Nat) : List Bool := List.replicate n false

/-- Test whether an input is the all-false string of its own length. -/
def isZeros : List Bool → Bool
  | [] => true
  | b :: x => !b && isZeros x

theorem isZeros_zeros (n : Nat) : isZeros (zeros n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [zeros, List.replicate_succ, isZeros] using ih

/-- The algorithm: `L` with the answer flipped on the all-false input of each length. -/
def flipOne (L : List Bool → Bool) (x : List Bool) : Bool :=
  if isZeros x then !L x else L x

/-- Exactly one input of each length is all-false. -/
theorem count_isZeros (n : Nat) : count isZeros (allInputs n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : count (fun a => isZeros (false :: a)) (allInputs n) = 1 := by
      simpa [isZeros] using ih
    have h1 : count (fun a => isZeros (true :: a)) (allInputs n) = 0 := by
      simp [count, isZeros]
    simp only [allInputs, count_append, count_map, h0, h1]

theorem flipOne_disagree_iff (L : List Bool → Bool) (x : List Bool) :
    (flipOne L x != L x) = isZeros x := by
  unfold flipOne
  cases isZeros x <;> cases L x <;> rfl

/-- **Average case.** `flipOne L` errs on exactly one of the `2^n` inputs of length `n`. -/
theorem flipOne_errors (L : List Bool → Bool) (n : Nat) :
    count (fun x => flipOne L x != L x) (allInputs n) = 1 := by
  have : (fun x => flipOne L x != L x) = isZeros := funext (flipOne_disagree_iff L)
  rw [this, count_isZeros]

/-- **Average case.** `flipOne L` is correct on exactly `2^n - 1` inputs of length `n`. -/
theorem flipOne_agreements (L : List Bool → Bool) (n : Nat) :
    count (fun x => flipOne L x == L x) (allInputs n) = 2 ^ n - 1 := by
  have hpart := count_add_count_not (fun x => flipOne L x == L x) (allInputs n)
  have hswap : (fun x => !(flipOne L x == L x)) = (fun x => flipOne L x != L x) := by
    funext x; cases flipOne L x <;> cases L x <;> rfl
  rw [hswap, flipOne_errors, allInputs_length] at hpart
  omega

theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem two_pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-- **Vanishing error.** For every `k`, from length `k` on the error fraction is `≤ 1/k`. -/
theorem flipOne_error_vanishes (L : List Bool → Bool) (k : Nat) :
    ∀ n, k ≤ n → count (fun x => flipOne L x != L x) (allInputs n) * k ≤ 2 ^ n := by
  intro n hn
  rw [flipOne_errors, Nat.one_mul]
  exact Nat.le_trans (Nat.le_of_lt (lt_two_pow_self k)) (two_pow_mono hn)

theorem flipOne_zeros (L : List Bool → Bool) (n : Nat) :
    flipOne L (zeros n) ≠ L (zeros n) := by
  unfold flipOne
  rw [isZeros_zeros]
  cases L (zeros n) <;> decide

theorem flipOne_zeros_ne (L : List Bool → Bool) (n : Nat) :
    ∃ x, flipOne L x ≠ L x := ⟨zeros n, flipOne_zeros L n⟩

/-- **Worst case.** At every length `n`, `flipOne L` is wrong on some input of length `n`. -/
theorem flipOne_worst_case_wrong (L : List Bool → Bool) (n : Nat) :
    ∃ x : List Bool, x.length = n ∧ flipOne L x ≠ L x :=
  ⟨zeros n, by simp [zeros], flipOne_zeros L n⟩

/-- **Main refutation.** For every language there is an algorithm that is correct on
`2^n - 1` of the `2^n` inputs of every length, with error fraction tending to `0`,
but that is not worst-case correct at any length. -/
theorem average_case_does_not_imply_worst_case (L : List Bool → Bool) :
    ∃ A : List Bool → Bool,
      (∀ n, count (fun x => A x == L x) (allInputs n) = 2 ^ n - 1) ∧
      (∀ n, count (fun x => A x != L x) (allInputs n) = 1) ∧
      (∀ n, ∃ x : List Bool, x.length = n ∧ A x ≠ L x) :=
  ⟨flipOne L, flipOne_agreements L, flipOne_errors L, flipOne_worst_case_wrong L⟩

/-- `A` solves `L` on average with at most `δ n` errors at each length `n`. -/
def AvgCorrect (A L : List Bool → Bool) (δ : Nat → Nat) : Prop :=
  ∀ n, count (fun x => A x != L x) (allInputs n) ≤ δ n

/-- `A` solves `L` on every input. -/
def WorstCorrect (A L : List Bool → Bool) : Prop := ∀ x, A x = L x

/-- Worst-case correctness always implies average-case correctness (the easy direction). -/
theorem worst_implies_avg (A L : List Bool → Bool) (δ : Nat → Nat)
    (h : WorstCorrect A L) : AvgCorrect A L δ := by
  intro n
  have : (fun x => A x != L x) = (fun _ => false) := funext fun x => by simp [h x]
  rw [this, count_false]
  exact Nat.zero_le _

/-- Average-case correctness with zero errors is worst-case correctness. -/
theorem avg_zero_implies_worst (A L : List Bool → Bool)
    (h : AvgCorrect A L (fun _ => 0)) : WorstCorrect A L := by
  intro x
  have hx := mem_allInputs x
  have h0 : count (fun y => A y != L y) (allInputs x.length) ≤ 0 := h x.length
  cases hA : A x == L x with
  | true => simpa using hA
  | false =>
    exfalso
    have hpos : 0 < count (fun y => A y != L y) (allInputs x.length) := by
      unfold count
      apply List.length_pos_of_mem (a := x)
      simp only [List.mem_filter]
      refine ⟨hx, ?_⟩
      simpa [bne] using hA
    omega

/-- Generic schema over a free algorithm class `Efficient`, a language `L` and
an error budget `δ`: an efficient average-case solver yields an efficient
worst-case solver.  Its truth depends on the choice of `Efficient`
(`obligation_not_automatic`); the machine instance is `WorstToAverage`
below, with `Efficient` replaced by `Complexity.Run` step counts. -/
def WorstToAverageObligationFor (Efficient : (List Bool → Bool) → Prop)
    (L : List Bool → Bool) (δ : Nat → Nat) : Prop :=
  (∃ A, Efficient A ∧ AvgCorrect A L δ) → ∃ B, Efficient B ∧ WorstCorrect B L

/-- **The obligation is not automatic.** For every language `L` there is an algorithm class
(all algorithms that err somewhere) for which the obligation fails even with a budget of
one error per length. Hence the obligation cannot follow from counting alone: it must
use specific properties of `L` and of the class of efficient algorithms. -/
theorem obligation_not_automatic (L : List Bool → Bool) :
    ∃ Efficient : (List Bool → Bool) → Prop,
      ¬ WorstToAverageObligationFor Efficient L (fun _ => 1) := by
  refine ⟨fun A => ∃ x, A x ≠ L x, ?_⟩
  intro hob
  have hA : ∃ A, (∃ x, A x ≠ L x) ∧ AvgCorrect A L (fun _ => 1) :=
    ⟨flipOne L, flipOne_zeros_ne L 0, fun n => Nat.le_of_eq (flipOne_errors L n)⟩
  obtain ⟨B, ⟨x, hx⟩, hB⟩ := hob hA
  exact hx (hB x)

/-- **Conditional theorem.** If the obligation is proved, average-case easiness of `L`
transfers to worst-case easiness. -/
theorem obligation_transfers (Efficient : (List Bool → Bool) → Prop)
    (L : List Bool → Bool) (δ : Nat → Nat)
    (hob : WorstToAverageObligationFor Efficient L δ)
    (A : List Bool → Bool) (hA : Efficient A) (hAvg : AvgCorrect A L δ) :
    ∃ B, Efficient B ∧ WorstCorrect B L :=
  hob ⟨A, hA, hAvg⟩

/-- Sanity check at size 3: seven of eight inputs agree. -/
example : count (fun x => flipOne (fun _ => true) x == true) (allInputs 3) = 7 := by decide

/-! # Machine part: average-case deciders in the shared model

An average-case decider is a `Complexity.Machine` that halts within a
polynomial on every input and whose answer is wrong on at most `δ n` of the
`2^n` inputs of each length `n` (uniform distribution on words). -/

section MachinePart

open Complexity
open Issue532.Machines (SAT SATInNP SATHard DecidesWithin run_deterministic polyDec_iff_inP
  inP_of_decidesWithin pEqualsNP_of_inP_sat inP_sat_of_pEqualsNP encMachinePoly
  encMachinePoly_injective)

open Classical in
/-- The answer of `m` within the clock `p`: accept iff it accepts within
`p(|x|)` steps. -/
noncomputable def machineAnswer (m : Machine) (p : Polynomial) : Language :=
  fun x => decide (∃ t, t ≤ p.eval x.length ∧ Run m (initial x) t true)

theorem machineAnswer_eq {m : Machine} {p : Polynomial} {x : Word} {t : Nat} {b : Bool}
    (ht : t ≤ p.eval x.length) (hr : Run m (initial x) t b) : machineAnswer m p x = b := by
  classical
  simp only [machineAnswer]
  cases b with
  | true => exact decide_eq_true ⟨t, ht, hr⟩
  | false =>
    refine decide_eq_false fun ⟨t', _, hr'⟩ => ?_
    obtain ⟨_, h⟩ := run_deterministic hr hr'
    cases h

/-- `L` has a polynomial-time machine that halts on every input within the
clock and errs on at most `δ n` inputs of each length `n`. -/
def AvgPolyDec (L : Language) (δ : Nat → Nat) : Prop :=
  ∃ (m : Machine) (p : Polynomial),
    (∀ x, ∃ t b, t ≤ p.eval x.length ∧ Run m (initial x) t b) ∧ AvgCorrect (machineAnswer m p) L δ

/-- Machine instance of the schema: an average-case polynomial-time machine
decider for `L` with error budget `δ` gives a worst-case one.  The
distribution is uniform on words; for `SAT` most words decode to a CNF that
contains the empty clause, so this is not the samplable-distribution
statement of the literature (see the dossier). -/
def WorstToAverage (L : Language) (δ : Nat → Nat) : Prop :=
  AvgPolyDec L δ → InP L

/-- A worst-case decider is an average-case decider for every budget. -/
theorem avgPolyDec_of_inP {L : Language} (h : InP L) (δ : Nat → Nat) : AvgPolyDec L δ := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  refine ⟨m, p, fun x => ?_, worst_implies_avg _ _ δ fun x => ?_⟩
  · obtain ⟨t, b, ht, hr, _⟩ := hm x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t, b, ht, hr, hb⟩ := hm x
    rw [machineAnswer_eq ht hr, hb]

/-- With budget zero an average-case decider is a worst-case decider. -/
theorem inP_of_avgPolyDec_zero {L : Language} (h : AvgPolyDec L (fun _ => 0)) : InP L := by
  obtain ⟨m, p, hhalt, havg⟩ := h
  have hw := avg_zero_implies_worst _ _ havg
  apply inP_of_decidesWithin (m := m) (p := p)
  intro x
  obtain ⟨t, b, ht, hr⟩ := hhalt x
  exact ⟨t, b, ht, hr, by rw [← hw x, machineAnswer_eq ht hr]⟩

theorem avgPolyDec_zero_iff (L : Language) : AvgPolyDec L (fun _ => 0) ↔ InP L :=
  ⟨inP_of_avgPolyDec_zero, fun h => avgPolyDec_of_inP h _⟩

theorem worstToAverage_of_inP {L : Language} (h : InP L) (δ : Nat → Nat) : WorstToAverage L δ :=
  fun _ => h

theorem worstToAverage_zero (L : Language) : WorstToAverage L (fun _ => 0) :=
  inP_of_avgPolyDec_zero

/-- **Conditional theorem (proved).**  The transfer for SAT plus an
average-case machine decider for SAT gives `InP SAT`. -/
theorem inP_sat_of_worstToAverage {δ : Nat → Nat} (h : WorstToAverage SAT δ)
    (havg : AvgPolyDec SAT δ) : InP SAT :=
  h havg

/-- **Conditional theorem (proved).**  With SAT's NP-hardness (a named
hypothesis) the same data give P = NP. -/
theorem pEqualsNP_of_worstToAverage (hard : SATHard) {δ : Nat → Nat}
    (h : WorstToAverage SAT δ) (havg : AvgPolyDec SAT δ) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (h havg)

/-- Under P = NP (and SAT ∈ NP) the transfer for SAT holds for every budget. -/
theorem worstToAverage_sat_of_pEqualsNP (mem : SATInNP) (hp : PEqualsNP) (δ : Nat → Nat) :
    WorstToAverage SAT δ :=
  worstToAverage_of_inP (inP_sat_of_pEqualsNP mem hp) δ

/-- **Conditional theorem (proved).**  Refuting the transfer for SAT at any
budget proves P ≠ NP (given SAT ∈ NP). -/
theorem pNotEqualsNP_of_not_worstToAverage (mem : SATInNP) {δ : Nat → Nat}
    (h : ¬ WorstToAverage SAT δ) : PNotEqualsNP :=
  fun hp => h (worstToAverage_sat_of_pEqualsNP mem hp δ)

/-! ## Non-vacuity: a language far from every machine -/

theorem two_le_count {α : Type} [DecidableEq α] (q : α → Bool) (l : List α)
    {x y : α} (hxy : x ≠ y) (hx : x ∈ l) (hy : y ∈ l) (hqx : q x = true) (hqy : q y = true) :
    2 ≤ count q l := by
  have hsub : [x, y] ⊆ l.filter q := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact List.mem_filter.mpr ⟨hx, hqx⟩
    · exact List.mem_filter.mpr ⟨hy, hqy⟩
  have hnd : [x, y].Nodup := by simp [hxy]
  exact hnd.length_le_of_subset hsub

/-- **Two-point Cantor argument.**  For an injectively encoded family of
languages there is a language that differs from the `a`-th member on both
one-bit extensions of the code of `a`. -/
theorem exists_language_far_from_family {T : Type} (e : T → Word)
    (he : ∀ a b, e a = e b → a = b) (F : T → Language) :
    ∃ L : Language, ∀ a (b : Bool), F a (e a ++ [b]) ≠ L (e a ++ [b]) := by
  classical
  refine ⟨fun w => decide (¬ ∃ a b, w = e a ++ [b] ∧ F a w = true), fun a b hFa => ?_⟩
  cases hF : F a (e a ++ [b]) with
  | true =>
    rw [hF] at hFa
    exact (decide_eq_true_iff.mp hFa.symm) ⟨a, b, rfl, hF⟩
  | false =>
    rw [hF] at hFa
    obtain ⟨a', b', hw, hF'⟩ := Classical.not_not.mp (decide_eq_false_iff_not.mp hFa.symm)
    have := he a a' (List.append_inj' hw rfl).1
    subst this
    rw [hF] at hF'
    cases hF'

/-- **Non-vacuity.**  Some language has no average-case polynomial-time
machine decider even with one error per length allowed, so `AvgPolyDec`
with budget one is not everything. -/
theorem exists_not_avgPolyDec : ∃ L : Language, ¬ AvgPolyDec L (fun _ => 1) := by
  obtain ⟨L, hL⟩ := exists_language_far_from_family encMachinePoly encMachinePoly_injective
    (fun a => machineAnswer a.1 a.2)
  refine ⟨L, fun ⟨m, p, _, havg⟩ => ?_⟩
  let w := encMachinePoly (m, p)
  have hlen : ∀ b : Bool, (w ++ [b]).length = w.length + 1 := fun b => by simp
  have hmem : ∀ b : Bool, w ++ [b] ∈ allInputs (w.length + 1) := fun b => by
    rw [← hlen b]; exact mem_allInputs _
  have herr : ∀ b : Bool, (machineAnswer m p (w ++ [b]) != L (w ++ [b])) = true := fun b => by
    have := hL (m, p) b
    simpa [bne_iff_ne] using this
  have h2 := two_le_count (fun x => machineAnswer m p x != L x) _ (x := w ++ [false]) (y := w ++ [true])
    (by simp) (hmem false) (hmem true) (herr false) (herr true)
  have h1 : count (fun x => machineAnswer m p x != L x) (allInputs (w.length + 1)) ≤ 1 :=
    havg (w.length + 1)
  omega

/-- Non-vacuity of the transfer: it fails for no language in P and holds at
budget zero for every language; `exists_not_avgPolyDec` shows that its
hypothesis is not automatic at budget one. -/
theorem worstToAverage_nontrivial :
    (∀ L, WorstToAverage L (fun _ => 0)) ∧ ∃ L : Language, ¬ AvgPolyDec L (fun _ => 1) :=
  ⟨worstToAverage_zero, exists_not_avgPolyDec⟩

end MachinePart

end Issue532.Idea33
