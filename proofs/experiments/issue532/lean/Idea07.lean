/-!
# Issue #532, Idea 07: lossless compression (pigeonhole and incompressibility)

Summary.
* Exact counting: `allStrings n` lists the `2^n` strings of length `n` without
  repetition, and `shorter n` lists the `2^n − 1` strings of length `< n`
  (`length_allStrings`, `length_shorter`).
* `pigeonhole`: a duplicate-free list contained in `M` is no longer than `M`
  (proved directly by induction with `List.erase`).
* `no_universal_compression`: every encoder that is injective on the strings
  of length `n` leaves some string of length `n` unshortened.
  `shortening_forces_collision`: an encoder that shortens every string of
  length `n` merges two different strings.
* `count_describable_le`: for every decoder, at most `2^m − 1` strings of
  length `n` have a description shorter than `m` bits.
  `incompressible_exists`: for every decoder and every `n` some string of
  length `n` has no description shorter than `n` bits.
* Positive side: a structured family (runs of one repeated bit) is
  identified by a one-bit code (`runCode_injective_on_runs`).

Verdict: refuted as a route (general theorem). "Compress every instance (or
every solution) losslessly" is impossible by counting. Compression must exploit
structure specific to a family, and deciding which strings are compressible
is a separate, hard problem.
-/

namespace Issue532.Idea07

/-! ## Strings and their enumeration -/

/-- A bit string. -/
abbrev Str := List Bool

/-- All `2^n` bit strings of length `n`. -/
def allStrings : Nat → List Str
  | 0 => [[]]
  | n + 1 => (allStrings n).map (false :: ·) ++ (allStrings n).map (true :: ·)

/-- All bit strings of length `< n`, shortest first. -/
def shorter : Nat → List Str
  | 0 => []
  | n + 1 => shorter n ++ allStrings n

/-- There are exactly `2^n` strings of length `n`. -/
theorem length_allStrings (n : Nat) : (allStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allStrings, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

/-- `allStrings n` lists exactly the strings of length `n`. -/
theorem mem_allStrings_iff (n : Nat) (v : Str) : v ∈ allStrings n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v with
    | nil => simp [allStrings]
    | cons b v => simp [allStrings]
  | succ n ih =>
    cases v with
    | nil => simp [allStrings]
    | cons b v => cases b <;> simp [allStrings, ih]

theorem nodup_map_cons (b : Bool) (L : List Str) (h : L.Nodup) :
    (L.map (b :: ·)).Nodup := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy hyx => h.1 ?_, ih h.2⟩
    have : y = x := List.cons.inj hyx |>.2
    exact this ▸ hy

/-- `allStrings n` has no repetitions. -/
theorem nodup_allStrings (n : Nat) : (allStrings n).Nodup := by
  induction n with
  | zero => simp [allStrings]
  | succ n ih =>
    simp only [allStrings]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons false _ ih, nodup_map_cons true _ ih, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨w, _, rfl⟩ := hy
    exact Bool.noConfusion (List.cons.inj hxy).1

/-- There are exactly `2^n − 1` strings of length `< n`
(`1 + 2 + … + 2^(n−1)`). -/
theorem length_shorter (n : Nat) : (shorter n).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [shorter, List.length_append, ih, length_allStrings]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ]; omega

/-- `shorter n` lists exactly the strings of length `< n`. -/
theorem mem_shorter_iff (n : Nat) (v : Str) : v ∈ shorter n ↔ v.length < n := by
  induction n with
  | zero => simp [shorter]
  | succ n ih =>
    simp only [shorter, List.mem_append, ih, mem_allStrings_iff]
    omega

/-! ## Pigeonhole principle over lists -/

/-- **Pigeonhole.** A duplicate-free list contained in `M` is no longer than `M`.
Proved directly by induction, removing one matched element of `M` per step. -/
theorem pigeonhole {α : Type} [DecidableEq α] (L M : List α) (hL : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ M) : L.length ≤ M.length := by
  induction L generalizing M with
  | nil => exact Nat.zero_le _
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    have hx : x ∈ M := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ L, y ∈ M.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hL.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy))
    have h1 := ih (M.erase x) hL.2 hsub'
    have h2 := List.length_erase_of_mem hx
    have h3 : 0 < M.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

/-- A map that is injective on a duplicate-free list keeps it duplicate-free. -/
theorem nodup_map_of_injOn {α β : Type} (f : α → β) (L : List α) (hL : L.Nodup)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun y hy hyx => hL.1 ?_, ih hL.2 ?_⟩
    · have : y = x := hinj y (List.mem_cons_of_mem _ hy) x (List.mem_cons_self ..) hyx
      exact this ▸ hy
    · intro a ha b hb hab
      exact hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab

/-! ## No lossless compressor shortens every string -/

/-- Injectivity of `enc` on the strings of length `n` (lossless on that slice). -/
def InjectiveOnLength (enc : Str → Str) (n : Nat) : Prop :=
  ∀ x y, x.length = n → y.length = n → enc x = enc y → x = y

/-- **No universal lossless compression.** If `enc` is injective on strings of
length `n`, some string of length `n` is not shortened: `n ≤ |enc x|`. -/
theorem no_universal_compression (enc : Str → Str) (n : Nat)
    (hinj : InjectiveOnLength enc n) : ∃ x : Str, x.length = n ∧ n ≤ (enc x).length := by
  apply Classical.byContradiction
  intro hno
  have hshort : ∀ x : Str, x.length = n → (enc x).length < n := by
    intro x hx
    apply Classical.byContradiction
    intro hlt
    exact hno ⟨x, hx, by omega⟩
  have hnd : ((allStrings n).map enc).Nodup := by
    apply nodup_map_of_injOn _ _ (nodup_allStrings n)
    intro x hx y hy hxy
    exact hinj x y ((mem_allStrings_iff n x).mp hx) ((mem_allStrings_iff n y).mp hy) hxy
  have hsub : ∀ z ∈ (allStrings n).map enc, z ∈ shorter n := by
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (mem_shorter_iff n _).mpr (hshort x ((mem_allStrings_iff n x).mp hx))
  have hle := pigeonhole _ _ hnd hsub
  rw [List.length_map, length_allStrings, length_shorter] at hle
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- **Shortening forces collisions.** If `enc` maps every string of length `n`
to a strictly shorter string, two different strings of length `n` share a code:
such an encoder is lossy. -/
theorem shortening_forces_collision (enc : Str → Str) (n : Nat)
    (hshort : ∀ x : Str, x.length = n → (enc x).length < n) :
    ∃ x y : Str, x.length = n ∧ y.length = n ∧ x ≠ y ∧ enc x = enc y := by
  apply Classical.byContradiction
  intro hno
  have hinj : InjectiveOnLength enc n := by
    intro x y hx hy hxy
    apply Classical.byContradiction
    intro hne
    exact hno ⟨x, y, hx, hy, hne, hxy⟩
  obtain ⟨x, hx, hge⟩ := no_universal_compression enc n hinj
  have := hshort x hx
  omega

/-! ## Incompressible strings (Kolmogorov-style counting) -/

/-- `x` has a description shorter than `m` bits under the decoder `dec`. -/
def Describable (dec : Str → Str) (m : Nat) (x : Str) : Prop :=
  ∃ p : Str, p.length < m ∧ dec p = x

theorem describable_iff (dec : Str → Str) (m : Nat) (x : Str) :
    Describable dec m x ↔ x ∈ (shorter m).map dec := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact List.mem_map.mpr ⟨p, (mem_shorter_iff m p).mpr hp, rfl⟩
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact ⟨p, (mem_shorter_iff m p).mp hp, rfl⟩

/-- **Counting bound.** For every decoder `dec` (any description method,
computable or not) and all `n, m`, at most `2^m − 1` strings of length `n`
have a description shorter than `m` bits. With `m = n − c`, fewer than a
`2^(−c)` fraction of `n`-bit strings compress by `c` or more bits. -/
theorem count_describable_le (dec : Str → Str) (n m : Nat) :
    ((allStrings n).filter (fun x => decide (x ∈ (shorter m).map dec))).length
      ≤ 2 ^ m - 1 := by
  have hnd : ((allStrings n).filter (fun x => decide (x ∈ (shorter m).map dec))).Nodup :=
    List.Nodup.sublist List.filter_sublist (nodup_allStrings n)
  have hsub : ∀ x ∈ (allStrings n).filter (fun x => decide (x ∈ (shorter m).map dec)),
      x ∈ (shorter m).map dec := by
    intro x hx
    simpa using (List.mem_filter.mp hx).2
  have hle := pigeonhole _ _ hnd hsub
  rw [List.length_map, length_shorter] at hle
  exact hle

/-- **Incompressible strings exist.** For every decoder `dec` and every `n`,
some string of length `n` has no description shorter than `n` bits. -/
theorem incompressible_exists (dec : Str → Str) (n : Nat) :
    ∃ x : Str, x.length = n ∧ ¬ Describable dec n x := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ x ∈ allStrings n, x ∈ (shorter n).map dec := by
    intro x hx
    apply (describable_iff dec n x).mp
    apply Classical.byContradiction
    intro hnd
    exact hno ⟨x, (mem_allStrings_iff n x).mp hx, hnd⟩
  have hle := pigeonhole _ _ (nodup_allStrings n) hall
  rw [List.length_map, length_allStrings, length_shorter] at hle
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-! ## Compression that exploits structure -/

/-- Run-of-equal-bits strings: `b` repeated `n` times. -/
def run (b : Bool) (n : Nat) : Str := List.replicate n b

/-- A code for runs: keep only the first bit. It is not injective on all
strings; it is designed for the structured family of runs. -/
def runCode (x : Str) : Str := [x.headD false]

/-- **Structure permits compression.** On the two runs of length `n ≥ 1`,
the one-bit code `runCode` is injective. -/
theorem runCode_injective_on_runs (n : Nat) (hn : 1 ≤ n) (b c : Bool)
    (h : runCode (run b n) = runCode (run c n)) : run b n = run c n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [runCode, run, List.replicate_succ] at h
  rw [h]

/-- The code is exponentially shorter than the run it describes. -/
theorem runCode_length (b : Bool) (n : Nat) : (runCode (run b n)).length = 1 := rfl
end Issue532.Idea07
