/-!
# Issue #532, Idea 09: description length versus running time

This file tests the heuristic "the shortest program is also the fastest one"
(issue #532, Part I item 5) and develops the positive meta-algorithmic idea
behind it (Part I item 8) into Levin's universal search.

## Part A: a loop language with explicit size and cost semantics

`Prog` has three constructors: `inc` (add one), `seq p q`, and `loop k b`
(run `b` exactly `k` times). The size of `loop k b` charges the binary length
`bits k` of the counter, so sizes are honest description lengths. The cost
of `loop k b` is `k * (cost b + 1) + 1` (one bookkeeping step per iteration plus
one exit test).

Proved for **all** programs and all `k`:

* `run_eq`: every program maps `v` to `v + gain p` in exactly `cost p` steps.
* `cost_ge_gain`: every program needs at least as many steps as the amount it
  adds, so `k` steps is the optimum for the function `v ↦ v + k`.
* `time_optimal_is_loop_free`, `loopFree_size_eq_cost`: a time-optimal program
  contains no loop, and then its size equals its cost; hence every fastest
  program for `v ↦ v + k` has size exactly `k` (`fastest_programs_have_size_k`).
* `loop_inc_size` and `bits_spec`: `loop k inc` computes `v ↦ v + k` with size
  `bits k + 2`, i.e. `O(log k)`, and cost `2k + 1`; `loop_inc_exponential_gap`
  shows cost is at least `2 ^ (size - 2)`.
* `shortest_is_never_fastest`: for every `k ≥ 6`, every program for
  `v ↦ v + k` that is no longer than `loop k inc` is strictly slower than the
  fastest program. In particular no minimum-size program is time-optimal.
* `shorter_not_implies_faster`, `faster_not_implies_shorter`: neither
  monotone relation between size and time holds in this language.
* `loopFree_size_eq_cost`: in the loop-free fragment size and time coincide,
  confirming the issue's remark that the separation "relies on allowing reuse,
  loops, and iteration".

## Part B: Levin universal search (abstract, restart semantics)

Programs are indexed by `i`; `runs i t` is what program `i` outputs within `t`
steps (monotone in `t`); `V` is a verifier. In phase `j` programs `0..j` are
each run for `2 ^ (j - i)` steps. Proved:

* `search_sound`: every returned witness is verified.
* `levin_finds`: if program `i` outputs a verified witness within `t ≤ 2^L`
  steps, the search succeeds by phase `i + L`.
* `totalWork_lt`: the total simulated work up to phase `J` is below
  `2 ^ (J + 2)`.
* `levin_search_bound`: success with total work `< 8 * 2^i * t`.
* `levin_poly_of_obligation`: if the open obligation
  `PolyTimeWitnessProgramExists` holds, Levin search is polynomial on every
  satisfiable instance.

## Verdict

"Shortest program implies fastest program" is refuted as a route by the
general theorem `shortest_is_never_fastest`. Levin search is developed: it is
optimal up to the fixed factor `2^i` (plus verification overhead), but
whether its running time is polynomial is exactly the open obligation
`PolyTimeWitnessProgramExists`, which for SAT is equivalent to P = NP. Nothing
here proves or refutes P = NP.
-/

namespace Issue532.Idea09

/-! ## Part A -/

/-- Binary length of a natural number (`bits 0 = bits 1 = 1`). -/
def bits (n : Nat) : Nat := if n < 2 then 1 else bits (n / 2) + 1
decreasing_by omega

/-- `bits n` is the binary length: `n < 2 ^ bits n ≤ 2 n` for `n ≥ 1`. -/
theorem bits_spec (n : Nat) (hn : 1 ≤ n) : n < 2 ^ bits n ∧ 2 ^ bits n ≤ 2 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [bits]
    by_cases h : n < 2
    · simp [h]; omega
    · simp [h]
      have h1 := ih (n / 2) (by omega) (by omega)
      rw [Nat.pow_succ]
      omega

/-- A tiny loop language. -/
inductive Prog where
  | inc : Prog
  | seq : Prog → Prog → Prog
  | loop : Nat → Prog → Prog

open Prog

/-- Description length; a loop counter `k` costs `bits k` symbols. -/
def size : Prog → Nat
  | inc => 1
  | seq p q => size p + size q
  | loop k b => bits k + 1 + size b

/-- Iterate a (value, steps) semantics `k` times with loop overhead. -/
def iter : Nat → (Nat → Nat × Nat) → Nat → Nat × Nat
  | 0, _, v => (v, 1)
  | k + 1, f, v =>
    let r := f v
    let r2 := iter k f r.1
    (r2.1, r.2 + 1 + r2.2)

/-- Operational semantics: `run p v = (output value, steps used)`. -/
def run : Prog → Nat → Nat × Nat
  | inc, v => (v + 1, 1)
  | seq p q, v =>
    let r := run p v
    let r2 := run q r.1
    (r2.1, r.2 + r2.2)
  | loop k b, v => iter k (run b) v

/-- The amount a program adds to its input. -/
def gain : Prog → Nat
  | inc => 1
  | seq p q => gain p + gain q
  | loop k b => k * gain b

/-- The number of steps a program takes (independent of the input). -/
def cost : Prog → Nat
  | inc => 1
  | seq p q => cost p + cost q
  | loop k b => k * (cost b + 1) + 1

/-- Does the program contain no loop? -/
def loopFree : Prog → Bool
  | inc => true
  | seq p q => loopFree p && loopFree q
  | loop _ _ => false

theorem iter_eq (f : Nat → Nat × Nat) (g c : Nat) (hf : ∀ v, f v = (v + g, c)) :
    ∀ k v, iter k f v = (v + k * g, k * (c + 1) + 1) := by
  intro k
  induction k with
  | zero => intro v; simp [iter]
  | succ k ih =>
    intro v
    simp only [iter, hf, ih]
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

/-- Every program maps `v` to `v + gain p` using exactly `cost p` steps. -/
theorem run_eq : ∀ (p : Prog) (v : Nat), run p v = (v + gain p, cost p) := by
  intro p
  induction p with
  | inc => intro v; rfl
  | seq p q ihp ihq =>
    intro v
    simp only [run, ihp, ihq, gain, cost, Nat.add_assoc]
  | loop k b ihb =>
    intro v
    simp only [run, gain, cost]
    exact iter_eq (run b) (gain b) (cost b) ihb k v

/-- Time is at least the amount added: no program for `v ↦ v + k` beats `k` steps. -/
theorem cost_ge_gain : ∀ p : Prog, gain p ≤ cost p := by
  intro p
  induction p with
  | inc => simp [gain, cost]
  | seq p q ihp ihq => simp only [gain, cost]; omega
  | loop k b ihb =>
    simp only [gain, cost]
    have : k * gain b ≤ k * (cost b + 1) := Nat.mul_le_mul_left k (by omega)
    omega

/-- A time-optimal program (cost equals gain) contains no loop. -/
theorem time_optimal_is_loop_free : ∀ p : Prog, cost p = gain p → loopFree p = true := by
  intro p
  induction p with
  | inc => intro _; rfl
  | seq p q ihp ihq =>
    intro h
    simp only [cost, gain] at h
    have h1 := cost_ge_gain p
    have h2 := cost_ge_gain q
    simp only [loopFree, Bool.and_eq_true]
    exact ⟨ihp (by omega), ihq (by omega)⟩
  | loop k b _ =>
    intro h
    simp only [cost, gain] at h
    have h1 := cost_ge_gain b
    have : k * gain b ≤ k * (cost b + 1) := Nat.mul_le_mul_left k (by omega)
    omega

/-- In the loop-free fragment, size, time, and gain coincide. -/
theorem loopFree_size_eq_cost : ∀ p : Prog, loopFree p = true → size p = cost p ∧ size p = gain p := by
  intro p
  induction p with
  | inc => intro _; simp [size, cost, gain]
  | seq p q ihp ihq =>
    intro h
    simp only [loopFree, Bool.and_eq_true] at h
    have a := ihp h.1
    have b := ihq h.2
    simp only [size, cost, gain]
    omega
  | loop _ _ _ => intro h; simp [loopFree] at h

/-- Every fastest program for `v ↦ v + k` (cost exactly `k`) has size exactly `k`. -/
theorem fastest_programs_have_size_k (p : Prog) (k : Nat) (hg : gain p = k) (hc : cost p = k) :
    size p = k := by
  have h := loopFree_size_eq_cost p (time_optimal_is_loop_free p (by omega))
  omega

/-- The unrolled program `inc; inc; ...; inc` with `m + 1` increments. -/
def unroll : Nat → Prog
  | 0 => inc
  | m + 1 => seq inc (unroll m)

/-- The unrolled program is loop-free, adds `m + 1`, and has size = time = `m + 1`. -/
theorem unroll_spec (m : Nat) :
    gain (unroll m) = m + 1 ∧ cost (unroll m) = m + 1 ∧ size (unroll m) = m + 1 := by
  induction m with
  | zero => simp [unroll, gain, cost, size]
  | succ m ih => simp only [unroll, gain, cost, size]; omega

/-- `loop k inc` adds `k`, takes `2k + 1` steps, and has size `bits k + 2`. -/
theorem loop_inc_size (k : Nat) :
    gain (loop k inc) = k ∧ cost (loop k inc) = 2 * k + 1 ∧ size (loop k inc) = bits k + 2 := by
  refine ⟨?_, ?_, ?_⟩
  · show k * 1 = k
    omega
  · show k * (1 + 1) + 1 = 2 * k + 1
    omega
  · show bits k + 1 + 1 = bits k + 2
    omega

/-- Time can be exponential in description length: `2 ^ size ≤ 4 * cost` for `loop k inc`, `k ≥ 1`. -/
theorem loop_inc_exponential_gap (k : Nat) (hk : 1 ≤ k) :
    2 ^ size (loop k inc) ≤ 4 * cost (loop k inc) := by
  have h := bits_spec k hk
  have hs := loop_inc_size k
  rw [hs.2.2, hs.2.1, Nat.pow_succ, Nat.pow_succ]
  omega

theorem small_lt_pow (m : Nat) (hm : 4 ≤ m) : 2 * m + 4 < 2 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Nat.pow_succ]
    by_cases h : m = 3
    · subst h; decide
    · have := ih (by omega); omega

/-- For `k ≥ 6`, `loop k inc` is strictly shorter than `k`. -/
theorem loop_inc_short (k : Nat) (hk : 6 ≤ k) : size (loop k inc) < k := by
  have h := bits_spec k (by omega)
  rw [(loop_inc_size k).2.2]
  apply Nat.lt_of_not_le
  intro hle
  have hb : k - 2 ≤ bits k := by omega
  have h2 : 2 ^ (k - 2) ≤ 2 ^ bits k := Nat.pow_le_pow_right (by decide) hb
  have h3 := small_lt_pow (k - 2) (by omega)
  omega

/--
Main refutation. For every `k ≥ 6`, every program `q` computing `v ↦ v + k`
whose size is at most that of `loop k inc` is strictly slower than the fastest
program `unroll (k - 1)` (which takes `k` steps). Hence no shortest program for
`v ↦ v + k` is a fastest one.
-/
theorem shortest_is_never_fastest (k : Nat) (hk : 6 ≤ k) (q : Prog)
    (hq : gain q = k) (hs : size q ≤ size (loop k inc)) :
    cost (unroll (k - 1)) < cost q := by
  have hshort := loop_inc_short k hk
  have hu := unroll_spec (k - 1)
  have hge := cost_ge_gain q
  have hne : cost q ≠ k := by
    intro hc
    have := fastest_programs_have_size_k q k hq hc
    omega
  omega

/-- A program `p` computes the same function as `q`. -/
def SameFunction (p q : Prog) : Prop := ∀ v, (run p v).1 = (run q v).1

/-- "Shorter implies at least as fast" is false (counterexample family at `k = 6`). -/
theorem shorter_not_implies_faster :
    ¬ ∀ p q : Prog, SameFunction p q → size p ≤ size q → cost p ≤ cost q := by
  intro h
  have hsame : SameFunction (loop 6 inc) (unroll 5) := by
    intro v; rw [run_eq, run_eq, (loop_inc_size 6).1, (unroll_spec 5).1]
  have := h (loop 6 inc) (unroll 5) hsame
    (Nat.le_of_lt (by have := loop_inc_short 6 (by decide); rw [(unroll_spec 5).2.2]; omega))
  rw [(loop_inc_size 6).2.1, (unroll_spec 5).2.1] at this
  omega

/-- "Faster implies at least as short" is false (same family, read the other way). -/
theorem faster_not_implies_shorter :
    ¬ ∀ p q : Prog, SameFunction p q → cost p ≤ cost q → size p ≤ size q := by
  intro h
  have hsame : SameFunction (unroll 5) (loop 6 inc) := by
    intro v; rw [run_eq, run_eq, (loop_inc_size 6).1, (unroll_spec 5).1]
  have := h (unroll 5) (loop 6 inc) hsame
    (by rw [(loop_inc_size 6).2.1, (unroll_spec 5).2.1]; decide)
  have hs := loop_inc_short 6 (by decide)
  rw [(unroll_spec 5).2.2] at this
  omega

/-- Padding: for every `k`, a longer program can also be slower (so there is no inverse law either). -/
theorem padding_longer_and_slower (k : Nat) :
    SameFunction (loop k inc) (seq (loop k inc) (loop 0 inc)) ∧
    size (loop k inc) < size (seq (loop k inc) (loop 0 inc)) ∧
    cost (loop k inc) < cost (seq (loop k inc) (loop 0 inc)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v; rw [run_eq, run_eq]; simp [gain]
  · simp only [size]; omega
  · simp only [cost]; omega

/-! ## Part B: Levin universal search -/

section Levin

variable {W : Type}

/-- Restart semantics: once program `i` has output `w` within `t` steps, it outputs `w` within any larger budget. -/
def MonotoneRuns (runs : Nat → Nat → Option W) : Prop :=
  ∀ i t t' w, t ≤ t' → runs i t = some w → runs i t' = some w

/-- Keep an output only if the verifier accepts it. -/
def check (V : W → Bool) : Option W → Option W
  | some w => if V w then some w else none
  | none => none

/-- Phase `j`, scanning programs `0, ..., m - 1`, each with budget `2 ^ (j - i)`. -/
def phaseAux (runs : Nat → Nat → Option W) (V : W → Bool) (j : Nat) : Nat → Option W
  | 0 => none
  | i + 1 =>
    match phaseAux runs V j i with
    | some w => some w
    | none => check V (runs i (2 ^ (j - i)))

/-- Phase `j` of Levin search: programs `0..j`. -/
def phase (runs : Nat → Nat → Option W) (V : W → Bool) (j : Nat) : Option W :=
  phaseAux runs V j (j + 1)

/-- Levin search through phases `0..J`, returning the first verified output. -/
def search (runs : Nat → Nat → Option W) (V : W → Bool) : Nat → Option W
  | 0 => phase runs V 0
  | J + 1 =>
    match search runs V J with
    | some w => some w
    | none => phase runs V (J + 1)

/-- Work of phase `j` restricted to programs `0..m-1`. -/
def phaseWorkAux (j : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => phaseWorkAux j i + 2 ^ (j - i)

/-- Total simulated steps in phase `j`. -/
def phaseWork (j : Nat) : Nat := phaseWorkAux j (j + 1)

/-- Total simulated steps in phases `0..J`. -/
def totalWork : Nat → Nat
  | 0 => phaseWork 0
  | J + 1 => totalWork J + phaseWork (J + 1)

theorem check_sound (V : W → Bool) (o : Option W) (w : W) (h : check V o = some w) : V w = true := by
  cases o with
  | none => simp [check] at h
  | some u =>
    simp only [check] at h
    by_cases hu : V u = true
    · simp [hu] at h; subst h; exact hu
    · simp [hu] at h

theorem phaseAux_sound (runs : Nat → Nat → Option W) (V : W → Bool) (j : Nat) :
    ∀ m w, phaseAux runs V j m = some w → V w = true := by
  intro m
  induction m with
  | zero => intro w h; simp [phaseAux] at h
  | succ m ih =>
    intro w h
    simp only [phaseAux] at h
    cases hp : phaseAux runs V j m with
    | some u => rw [hp] at h; simp at h; subst h; exact ih u hp
    | none => rw [hp] at h; exact check_sound V _ w h

/-- Soundness: whatever Levin search returns is verified. -/
theorem search_sound (runs : Nat → Nat → Option W) (V : W → Bool) :
    ∀ J w, search runs V J = some w → V w = true := by
  intro J
  induction J with
  | zero => intro w h; exact phaseAux_sound runs V 0 1 w h
  | succ J ih =>
    intro w h
    simp only [search] at h
    cases hs : search runs V J with
    | some u => rw [hs] at h; simp at h; subst h; exact ih u hs
    | none => rw [hs] at h; exact phaseAux_sound runs V (J + 1) (J + 2) w h

theorem phaseAux_finds (runs : Nat → Nat → Option W) (V : W → Bool) (j i : Nat) (w : W)
    (hi : check V (runs i (2 ^ (j - i))) = some w) :
    ∀ m, i < m → ∃ w', phaseAux runs V j m = some w' := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    simp only [phaseAux]
    cases hp : phaseAux runs V j m with
    | some u => exact ⟨u, rfl⟩
    | none =>
      have him : i = m := by
        by_cases e : i = m
        · exact e
        · obtain ⟨u, hu⟩ := ih (by omega); rw [hp] at hu; simp at hu
      subst him
      exact ⟨w, hi⟩

theorem search_mono (runs : Nat → Nat → Option W) (V : W → Bool) (j : Nat) (w : W)
    (hj : phase runs V j = some w) : ∀ J, j ≤ J → ∃ w', search runs V J = some w' := by
  intro J
  induction J with
  | zero =>
    intro h
    have : j = 0 := by omega
    subst this
    exact ⟨w, hj⟩
  | succ J ih =>
    intro h
    simp only [search]
    cases hs : search runs V J with
    | some u => exact ⟨u, rfl⟩
    | none =>
      have hjJ : j = J + 1 := by
        by_cases e : j = J + 1
        · exact e
        · obtain ⟨u, hu⟩ := ih (by omega); rw [hs] at hu; simp at hu
      subst hjJ
      exact ⟨w, hj⟩

/--
Completeness: if program `i` outputs a verified witness within `t ≤ 2 ^ L`
steps, Levin search has found a verified witness by phase `i + L`.
-/
theorem levin_finds (runs : Nat → Nat → Option W) (V : W → Bool) (hmono : MonotoneRuns runs)
    (i t L : Nat) (w : W) (hrun : runs i t = some w) (hV : V w = true) (hL : t ≤ 2 ^ L) :
    ∃ w', search runs V (i + L) = some w' ∧ V w' = true := by
  have hbudget : i + L - i = L := by omega
  have hr : runs i (2 ^ (i + L - i)) = some w := by
    rw [hbudget]; exact hmono i t (2 ^ L) w hL hrun
  have hc : check V (runs i (2 ^ (i + L - i))) = some w := by
    rw [hr]; simp [check, hV]
  obtain ⟨w1, hw1⟩ := phaseAux_finds runs V (i + L) i w hc (i + L + 1) (by omega)
  obtain ⟨w2, hw2⟩ := search_mono runs V (i + L) w1 hw1 (i + L) (Nat.le_refl _)
  exact ⟨w2, hw2, search_sound runs V (i + L) w2 hw2⟩

theorem phaseWorkAux_eq (j : Nat) : ∀ i, i ≤ j + 1 → phaseWorkAux j i + 2 ^ (j + 1 - i) = 2 ^ (j + 1) := by
  intro i
  induction i with
  | zero => intro _; simp [phaseWorkAux]
  | succ i ih =>
    intro h
    have e1 := ih (by omega)
    have e2 : j + 1 - i = (j - i) + 1 := by omega
    rw [e2, Nat.pow_succ] at e1
    have e3 : j + 1 - (i + 1) = j - i := by omega
    simp only [phaseWorkAux]
    rw [e3]
    omega

/-- Phase `j` simulates exactly `2 ^ (j + 1) - 1` steps. -/
theorem phaseWork_eq (j : Nat) : phaseWork j + 1 = 2 ^ (j + 1) := by
  have h := phaseWorkAux_eq j (j + 1) (Nat.le_refl _)
  simp only [Nat.sub_self, Nat.pow_zero] at h
  exact h

/-- Total simulated work through phase `J` is below `2 ^ (J + 2)`. -/
theorem totalWork_lt : ∀ J, totalWork J + 1 < 2 ^ (J + 2) := by
  intro J
  induction J with
  | zero => decide
  | succ J ih =>
    simp only [totalWork]
    have h := phaseWork_eq (J + 1)
    have e : 2 ^ (J + 1 + 2) = 2 * 2 ^ (J + 2) := by rw [Nat.pow_succ]; omega
    have e2 : 2 ^ (J + 2) = 2 ^ (J + 1 + 1) := rfl
    omega

/-- For `t ≥ 1` there is `L` with `t ≤ 2^L < 2t` (a ceiling logarithm). -/
theorem exists_ceil_log (t : Nat) (ht : 1 ≤ t) : ∃ L, t ≤ 2 ^ L ∧ 2 ^ L < 2 * t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h0 : t = 0
    · subst h0; exact ⟨0, by decide, by decide⟩
    · obtain ⟨L, h1, h2⟩ := ih (by omega)
      by_cases h3 : t + 1 ≤ 2 ^ L
      · exact ⟨L, h3, by omega⟩
      · refine ⟨L + 1, ?_, ?_⟩ <;> rw [Nat.pow_succ] <;> omega

/--
Quantitative Levin bound: if program `i` outputs a verified witness within
`t ≥ 1` steps, some phase `J` returns a verified witness and the total
simulated work through phase `J` is below `8 * 2^i * t`.
-/
theorem levin_search_bound (runs : Nat → Nat → Option W) (V : W → Bool) (hmono : MonotoneRuns runs)
    (i t : Nat) (ht : 1 ≤ t) (w : W) (hrun : runs i t = some w) (hV : V w = true) :
    ∃ J w', search runs V J = some w' ∧ V w' = true ∧ totalWork J < 8 * 2 ^ i * t := by
  obtain ⟨L, h1, h2⟩ := exists_ceil_log t ht
  obtain ⟨w', hs, hv⟩ := levin_finds runs V hmono i t L w hrun hV h1
  refine ⟨i + L, w', hs, hv, ?_⟩
  have hw := totalWork_lt (i + L)
  have e : 2 ^ (i + L + 2) = 4 * (2 ^ i * 2 ^ L) := by
    rw [Nat.pow_add, Nat.pow_add]; simp [Nat.mul_comm]
  have hm : 2 ^ i * 2 ^ L < 2 ^ i * (2 * t) := Nat.mul_lt_mul_of_pos_left h2 (Nat.two_pow_pos i)
  have e2 : 8 * 2 ^ i * t = 4 * (2 ^ i * (2 * t)) := by
    rw [Nat.mul_left_comm (2 ^ i) 2 t, Nat.mul_assoc 8]
    omega
  omega

end Levin

/-! ## Instance-indexed Levin search and the open obligation -/

/--
Open obligation (NOT assumed anywhere): a single program index `i` finds a
verified witness within `c * n^d + c` steps on every satisfiable instance of
size `n`. For SAT with a fixed polynomial-time universal machine this is
equivalent to P = NP (via search-to-decision self-reducibility); it is not
proved or refuted here.
-/
def PolyTimeWitnessProgramExists {X W : Type} (sz : X → Nat)
    (runs : Nat → X → Nat → Option W) (V : X → W → Bool) : Prop :=
  ∃ i c d : Nat, ∀ x, (∃ w, V x w = true) →
    ∃ t w, t ≤ c * sz x ^ d + c ∧ runs i x t = some w ∧ V x w = true

/--
Conditional theorem: under the obligation, Levin search (which does not need
to know `i`, `c`, or `d`) finds a verified witness on every satisfiable
instance with total simulated work below `K * (c * n^d + c + 1)` for a fixed
`K = 8 * 2^i`.
-/
theorem levin_poly_of_obligation {X W : Type} (sz : X → Nat)
    (runs : Nat → X → Nat → Option W) (V : X → W → Bool)
    (hmono : ∀ x, MonotoneRuns (runs · x))
    (hob : PolyTimeWitnessProgramExists sz runs V) :
    ∃ K c d : Nat, ∀ x, (∃ w, V x w = true) →
      ∃ J w, search (runs · x) (V x) J = some w ∧ V x w = true ∧
        totalWork J < K * (c * sz x ^ d + c + 1) := by
  obtain ⟨i, c, d, h⟩ := hob
  refine ⟨8 * 2 ^ i, c, d, ?_⟩
  intro x hx
  obtain ⟨t, w, ht, hr, hv⟩ := h x hx
  have hr' : runs i x (t + 1) = some w := hmono x i t (t + 1) w (by omega) hr
  obtain ⟨J, w', hs, hv', hw⟩ :=
    levin_search_bound (runs · x) (V x) (hmono x) i (t + 1) (by omega) w hr' hv
  refine ⟨J, w', hs, hv', ?_⟩
  have : 8 * 2 ^ i * (t + 1) ≤ 8 * 2 ^ i * (c * sz x ^ d + c + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end Issue532.Idea09
