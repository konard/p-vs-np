import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 20: parallel and physical cost models

A parallel execution is modelled as a *schedule*: a list of rounds, each
round a list of task identifiers executed simultaneously.  With `p`
processors every round has at most `p` tasks.  This file proves:

* `work_bound`, `rounds_lower_bound`: executing `W` distinct tasks on `p`
  processors takes at least `W / p` rounds (`W ≤ p * rounds`);
* `span_bound`: a dependency chain of length `d` needs at least `d` rounds;
* `brent_lower_bound`: both bounds together;
* `sequential_simulation`, `poly_parallel_in_poly_sequential`: a schedule is
  simulated sequentially in `totalWork ≤ p * rounds` steps, so polynomially
  many processors for polynomially many rounds give polynomial sequential
  work (the abstract content of NC ⊆ P);
* `exp_work_forces_superpoly_processors`,
  `poly_parallel_cannot_hide_exponential_work`: `2^n` units of work cannot
  be finished in polynomially many rounds on polynomially many processors,
  for all large `n`;
* `physical_conditional`, `dishonest_model_collapses`: an abstract physical
  model obeys the same bound if and only if it satisfies the resource
  accounting `work ≤ time * resource`.  The requirement that every physically
  realisable model does so is the schema `PhysicalResourceHonestyFor`, a
  postulate about physics that is defined but not proved;
* machine part: runs of polynomial-time deciders of the shared model are
  resource honest (`physicalResourceHonesty_machine`) and cannot perform
  `2^n` work (`machine_run_not_exponential`).

**Verdict.** Parallelism with polynomial resources cannot collapse
exponential work to polynomial time.  This is a general theorem, and it
refutes the route.  Physical models escape it only by paying an unaccounted
resource.  Core Lean only.
-/

namespace Issue532.Idea20

/-! ## Schedules -/

/-- A schedule: rounds of simultaneously executed task identifiers. -/
abbrev Schedule := List (List Nat)

/-- All tasks of a schedule, in execution order. -/
def flat : Schedule → List Nat
  | [] => []
  | r :: s => r ++ flat s

/-- Sequential work of a schedule: total number of task executions. -/
def totalWork : Schedule → Nat
  | [] => 0
  | r :: s => r.length + totalWork s

theorem length_flat (s : Schedule) : (flat s).length = totalWork s := by
  induction s with
  | nil => rfl
  | cons r s ih => simp [flat, totalWork, ih]

theorem mem_flat (s : Schedule) (t : Nat) : t ∈ flat s ↔ ∃ r ∈ s, t ∈ r := by
  induction s with
  | nil => simp [flat]
  | cons r s ih =>
    simp only [flat, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨r', hr', ht⟩)
      · exact ⟨r, Or.inl rfl, h⟩
      · exact ⟨r', Or.inr hr', ht⟩
    · rintro ⟨r', hr' | hr', ht⟩
      · subst hr'; exact Or.inl ht
      · exact Or.inr ⟨r', hr', ht⟩

/-- `s` runs on `p` processors: no round has more than `p` tasks. -/
def UsesAtMost (p : Nat) (s : Schedule) : Prop := ∀ r ∈ s, r.length ≤ p

/-- `s` executes each of the tasks `0, …, W-1` at least once. -/
def Covers (W : Nat) (s : Schedule) : Prop := ∀ t, t < W → ∃ r ∈ s, t ∈ r

/-- **Work bound.**  With at most `p` tasks per round, total work is at most
`p` times the number of rounds. -/
theorem work_bound (p : Nat) (s : Schedule) (h : UsesAtMost p s) :
    totalWork s ≤ p * s.length := by
  induction s with
  | nil => simp [totalWork]
  | cons r s ih =>
    have hr : r.length ≤ p := h r (List.mem_cons_self ..)
    have hs : totalWork s ≤ p * s.length :=
      ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [totalWork, List.length_cons, Nat.mul_succ]
    omega

/-- Covering `W` distinct tasks needs total work at least `W`. -/
theorem covers_work (W : Nat) (s : Schedule) (h : Covers W s) : W ≤ totalWork s := by
  have hsub : List.range W ⊆ flat s := by
    intro t ht
    exact (mem_flat s t).mpr (h t (List.mem_range.mp ht))
  have := List.Nodup.length_le_of_subset List.nodup_range hsub
  rw [List.length_range, length_flat] at this
  exact this

/-- **Rounds lower bound.**  `W` tasks on `p` processors need
`W ≤ p * rounds`. -/
theorem rounds_lower_bound (W p : Nat) (s : Schedule) (hp : UsesAtMost p s)
    (hW : Covers W s) : W ≤ p * s.length :=
  Nat.le_trans (covers_work W s hW) (work_bound p s hp)

/-- **Span bound.**  If the tasks of a chain of length `d` are placed in
strictly increasing rounds, all below `R`, then `d ≤ R`. -/
theorem span_bound (d R : Nat) (round : Nat → Nat)
    (hinc : ∀ i, i + 1 < d → round i < round (i + 1))
    (hlt : ∀ i, i < d → round i < R) : d ≤ R := by
  have key : ∀ i, i < d → i ≤ round i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hinc i hi
      omega
  cases d with
  | zero => exact Nat.zero_le _
  | succ d =>
    have h1 := key d (by omega)
    have h2 := hlt d (by omega)
    omega

/-- **Brent-style lower bound.**  A schedule on `p` processors that covers
`W` tasks and respects a chain of length `d` has at least `d` rounds and
`p * rounds ≥ W`. -/
theorem brent_lower_bound (W p d : Nat) (s : Schedule) (hp : UsesAtMost p s)
    (hW : Covers W s) (round : Nat → Nat)
    (hinc : ∀ i, i + 1 < d → round i < round (i + 1))
    (hlt : ∀ i, i < d → round i < s.length) :
    W ≤ p * s.length ∧ d ≤ s.length :=
  ⟨rounds_lower_bound W p s hp hW, span_bound d s.length round hinc hlt⟩

/-! ## Polynomial resources -/

/-- Local mirror of `Complexity.Polynomial.eval`. -/
def polyEval (c k n : Nat) : Nat := c * (n + 1) ^ k

/-- A schedule is simulated sequentially, one task at a time, in
`totalWork s ≤ p * rounds` steps. -/
theorem sequential_simulation (p : Nat) (s : Schedule) (h : UsesAtMost p s) :
    (flat s).length ≤ p * s.length := by
  rw [length_flat]; exact work_bound p s h

/-- **Abstract NC ⊆ P.**  Polynomially many processors for polynomially many
rounds give polynomially bounded sequential work. -/
theorem poly_parallel_in_poly_sequential (c k c' k' n : Nat) (s : Schedule)
    (hp : UsesAtMost (polyEval c k n) s) (hT : s.length ≤ polyEval c' k' n) :
    totalWork s ≤ polyEval (c * c') (k + k') n := by
  have h1 := work_bound _ s hp
  have h2 : polyEval c k n * s.length ≤ polyEval c k n * polyEval c' k' n :=
    Nat.mul_le_mul_left _ hT
  have e : polyEval c k n * polyEval c' k' n = polyEval (c * c') (k + k') n := by
    unfold polyEval
    rw [Nat.pow_add]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]
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

/-- For all `n ≥ 2^(2(c+k)+1)`, `c * (n+1)^k < 2^n` (as in Idea 17). -/
theorem exp_beats_poly (c k : Nat) :
    ∀ n, 2 ^ (2 * (c + k) + 1) ≤ n → polyEval c k n < 2 ^ n := by
  intro n hn
  unfold polyEval
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

/-- **Exponential work needs `p * rounds ≥ 2^n`.** -/
theorem exp_work_forces_superpoly_processors (n p : Nat) (s : Schedule)
    (hp : UsesAtMost p s) (hW : Covers (2 ^ n) s) : 2 ^ n ≤ p * s.length :=
  rounds_lower_bound (2 ^ n) p s hp hW

/-- **Polynomial processors and polynomial rounds cannot cover `2^n` tasks**
for any `n ≥ 2^(2(c c' + k + k')+1)`. -/
theorem poly_parallel_cannot_hide_exponential_work (c k c' k' : Nat) :
    ∀ n, 2 ^ (2 * (c * c' + (k + k')) + 1) ≤ n →
      ∀ s : Schedule, UsesAtMost (polyEval c k n) s → Covers (2 ^ n) s →
        polyEval c' k' n < s.length := by
  intro n hn s hp hW
  rcases Nat.lt_or_ge (polyEval c' k' n) s.length with h | h
  · exact h
  · have h1 := covers_work _ s hW
    have h2 := poly_parallel_in_poly_sequential c k c' k' n s hp h
    have h3 := exp_beats_poly (c * c') (k + k') n hn
    omega

/-! ## Physical models -/

/-- An abstract physical run: elementary operations performed, elapsed time,
and a resource (processors, energy, space, or precision) as functions of the
input size. -/
structure PhysicalRun where
  work : Nat → Nat
  time : Nat → Nat
  resource : Nat → Nat

/-- Resource accounting: each time step performs at most `resource` elementary
operations. -/
def ResourceHonest (m : PhysicalRun) : Prop := ∀ n, m.work n ≤ m.time n * m.resource n

/-- Schedules are resource honest, with processors as the resource. -/
theorem schedule_is_honest (p : Nat) (s : Schedule) (h : UsesAtMost p s) :
    totalWork s ≤ s.length * p := by
  rw [Nat.mul_comm]; exact work_bound p s h

/-- Generic schema over a free physical predicate `Realizable`: every
realisable run is resource honest.  `Realizable` is supplied by physics, so
this is a postulate and not a statement of complexity theory; its machine
instance `physicalResourceHonesty_machine` is proved below. -/
def PhysicalResourceHonestyFor (Realizable : PhysicalRun → Prop) : Prop :=
  ∀ m, Realizable m → ResourceHonest m

/-- **Conditional theorem.**  Under the obligation, a realisable run with
work `2^n` and polynomial time uses more than any given polynomial amount of
the resource, for all large `n`. -/
theorem physical_conditional (Realizable : PhysicalRun → Prop)
    (hphys : PhysicalResourceHonestyFor Realizable) (m : PhysicalRun) (hm : Realizable m)
    (hwork : ∀ n, m.work n = 2 ^ n) (c' k' : Nat) (htime : ∀ n, m.time n ≤ polyEval c' k' n)
    (c k : Nat) :
    ∀ n, 2 ^ (2 * (c * c' + (k + k')) + 1) ≤ n → polyEval c k n < m.resource n := by
  intro n hn
  rcases Nat.lt_or_ge (polyEval c k n) (m.resource n) with h | h
  · exact h
  · have h1 := hphys m hm n
    rw [hwork n] at h1
    have h2 : m.time n * m.resource n ≤ polyEval c' k' n * polyEval c k n :=
      Nat.mul_le_mul (htime n) h
    have e : polyEval c' k' n * polyEval c k n = polyEval (c * c') (k + k') n := by
      unfold polyEval
      rw [Nat.pow_add]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have h3 := exp_beats_poly (c * c') (k + k') n hn
    omega

/-- Without the obligation nothing follows: a run with exponential work in
unit time and unit resource is a consistent mathematical object. -/
theorem dishonest_model_collapses :
    ∃ m : PhysicalRun, (∀ n, m.work n = 2 ^ n) ∧ (∀ n, m.time n = 1) ∧
      (∀ n, m.resource n = 1) ∧ ¬ ResourceHonest m := by
  refine ⟨⟨fun n => 2 ^ n, fun _ => 1, fun _ => 1⟩, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun h => ?_⟩
  have := h 1
  simp at this

/-! ## Machine part: sequential machines as physical runs -/

section MachinePart

open Complexity
open Issue532.Machines (DecidesWithin)

/-- The physical run of a machine decider clocked by `p`: work and time are
both the step bound `p(n)` of `Complexity.Run`, on one processor. -/
def machinePhysicalRun (p : Polynomial) : PhysicalRun := ⟨p.eval, p.eval, fun _ => 1⟩

/-- The physical runs of polynomial-time machine deciders of the shared model. -/
def MachineRealizable (R : PhysicalRun) : Prop :=
  ∃ (m : Machine) (p : Polynomial) (L : Language), DecidesWithin m p L ∧ R = machinePhysicalRun p

/-- **Machine instance of the schema (proved).**  Runs of machine deciders are
resource honest with one processor. -/
theorem physicalResourceHonesty_machine : PhysicalResourceHonestyFor MachineRealizable := by
  rintro R ⟨m, p, L, _, rfl⟩ n
  simp [machinePhysicalRun]

/-- **A polynomial-time machine does not perform `2^n` work** (proved from
`exp_beats_poly`). -/
theorem machine_run_not_exponential (R : PhysicalRun) (hR : MachineRealizable R) :
    ¬ ∀ n, R.work n = 2 ^ n := by
  obtain ⟨m, p, L, _, rfl⟩ := hR
  intro h
  let n := 2 ^ (2 * (p.coefficient + p.degree) + 1)
  have h1 := exp_beats_poly p.coefficient p.degree n (Nat.le_refl _)
  have h2 := h n
  simp only [machinePhysicalRun, Polynomial.eval] at h2
  unfold polyEval at h1
  omega

end MachinePart

end Issue532.Idea20
