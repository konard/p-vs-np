/-!
# Issue #532, Idea 08: program induction and generalization from finite examples

Summary.
* `two_consistent_extensions`: for every consistent finite sample `S` and
  every unobserved input `x`, two total functions consistent with `S`
  disagree at `x`.
* `all_patterns_consistent`, `realised_patterns`: for `k` distinct unobserved
  inputs, each of the `2^k` bit patterns on them is realised by a function
  consistent with `S`. The data say nothing about unseen points.
* `lookup_consistent`: the lookup table fits every consistent sample. Fitting
  the data is never the difficulty; choosing among the fits is.
* Positive side, restricted classes. `elimination_identifies`: if the target
  is in a finite class `H` and the observed inputs separate `H`, the
  survivors of consistent elimination all equal the target.
  `no_separation_unrestricted`: for the class of all functions, no finite
  sample separates.

Verdict: refuted as a route (general theorem). Generalization without a
restricted hypothesis class is impossible. With a restricted class it becomes
learning theory, where the cost moves to finding a consistent hypothesis,
which can be NP-hard.
-/

namespace Issue532.Idea08

/-! ## Samples and consistency -/

/-- A finite sample of input/output examples. -/
abbrev Sample := List (Nat × Bool)

/-- `f` agrees with every example of `S`. -/
def Consistent (f : Nat → Bool) (S : Sample) : Prop := ∀ p ∈ S, f p.1 = p.2

/-- Some total function agrees with `S` (no input carries two labels). -/
def SampleConsistent (S : Sample) : Prop := ∃ f : Nat → Bool, Consistent f S

/-- The observed inputs. -/
def inputs (S : Sample) : List Nat := S.map Prod.fst

theorem not_mem_inputs {S : Sample} {x : Nat} (hx : x ∉ inputs S) :
    ∀ p ∈ S, p.1 ≠ x := by
  intro p hp h
  apply hx
  exact List.mem_map.mpr ⟨p, hp, h⟩

/-- **Two consistent generalizations disagree on every unseen input.** For a
consistent sample `S` and any `x` not among its inputs, there are total
functions `f, g`, both consistent with `S`, with `f x ≠ g x`. -/
theorem two_consistent_extensions (S : Sample) (hS : SampleConsistent S) (x : Nat)
    (hx : x ∉ inputs S) :
    ∃ f g : Nat → Bool, Consistent f S ∧ Consistent g S ∧ f x ≠ g x := by
  obtain ⟨f0, hf0⟩ := hS
  refine ⟨fun y => if y = x then true else f0 y, fun y => if y = x then false else f0 y,
    ?_, ?_, by simp⟩
  · intro p hp
    have hne := not_mem_inputs hx p hp
    simp only [hne, ↓reduceIte]
    exact hf0 p hp
  · intro p hp
    have hne := not_mem_inputs hx p hp
    simp only [hne, ↓reduceIte]
    exact hf0 p hp

/-! ## Every labelling of the unseen points is consistent -/

/-- Overwrite `f0` on the points `U` with the bits `m` (position by position). -/
def ext (f0 : Nat → Bool) : List Nat → List Bool → Nat → Bool
  | u :: U, b :: m, y => if y = u then b else ext f0 U m y
  | _, _, y => f0 y

theorem ext_outside (f0 : Nat → Bool) (U : List Nat) (m : List Bool) (y : Nat)
    (hy : y ∉ U) : ext f0 U m y = f0 y := by
  induction U generalizing m with
  | nil => cases m <;> rfl
  | cons u U ih =>
    cases m with
    | nil => rfl
    | cons b m =>
      have hne : ¬ (y = u) := fun h => hy (h ▸ List.mem_cons_self ..)
      have hy' : y ∉ U := fun h => hy (List.mem_cons_of_mem _ h)
      simp only [ext, hne, ↓reduceIte]
      exact ih m hy'

/-- `ext` realises the pattern `m` exactly on the distinct points `U`. -/
theorem ext_pattern (f0 : Nat → Bool) (U : List Nat) (m : List Bool) (hU : U.Nodup)
    (hm : m.length = U.length) : U.map (ext f0 U m) = m := by
  induction U generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons b m => simp at hm
  | cons u U ih =>
    cases m with
    | nil => simp at hm
    | cons b m =>
      rw [List.nodup_cons] at hU
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hm
      simp only [List.map_cons, ext, ↓reduceIte, List.cons.injEq, true_and]
      refine Eq.trans ?_ (ih m hU.2 hm)
      apply List.map_congr_left
      intro y hy
      have hne : ¬ (y = u) := fun h => hU.1 (h ▸ hy)
      simp only [hne, ↓reduceIte]

/-- **All `2^k` labellings of `k` unseen points are consistent with the
sample.** Let `S` be consistent and `U` a list of `k` distinct inputs, none of
them observed. For every bit pattern `m` of length `k` there is a total
function consistent with `S` whose values on `U` are exactly `m`. Distinct
patterns give functions that differ on `U`, so there are at least `2^k`
pairwise different consistent generalizations (`length_allStrings`). -/
theorem all_patterns_consistent (S : Sample) (hS : SampleConsistent S) (U : List Nat)
    (hU : U.Nodup) (hdisj : ∀ u ∈ U, u ∉ inputs S) (m : List Bool)
    (hm : m.length = U.length) :
    ∃ f : Nat → Bool, Consistent f S ∧ U.map f = m := by
  obtain ⟨f0, hf0⟩ := hS
  refine ⟨ext f0 U m, ?_, ext_pattern f0 U m hU hm⟩
  intro p hp
  have hp' : p.1 ∉ U := by
    intro hin
    exact hdisj p.1 hin (List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [ext_outside f0 U m p.1 hp']
  exact hf0 p hp

/-- All `2^n` bit strings of length `n`. -/
def allStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrings n).map (false :: ·) ++ (allStrings n).map (true :: ·)

/-- There are exactly `2^n` bit patterns of length `n`. -/
theorem length_allStrings (n : Nat) : (allStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allStrings, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]; omega

theorem mem_allStrings_iff (n : Nat) (v : List Bool) : v ∈ allStrings n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v with
    | nil => simp [allStrings]
    | cons b v => simp [allStrings]
  | succ n ih =>
    cases v with
    | nil => simp [allStrings]
    | cons b v => cases b <;> simp [allStrings, ih]

/-- **Counting form.** Every one of the `2^|U|` patterns in `allStrings |U|`
is realised on `U` by a function consistent with `S`. -/
theorem realised_patterns (S : Sample) (hS : SampleConsistent S) (U : List Nat)
    (hU : U.Nodup) (hdisj : ∀ u ∈ U, u ∉ inputs S) :
    (allStrings U.length).length = 2 ^ U.length ∧
      ∀ m ∈ allStrings U.length, ∃ f : Nat → Bool, Consistent f S ∧ U.map f = m :=
  ⟨length_allStrings _, fun m hm =>
    all_patterns_consistent S hS U hU hdisj m ((mem_allStrings_iff _ m).mp hm)⟩

/-! ## The lookup table always fits -/

/-- The lookup table: answer with the first matching example, `false` otherwise. -/
def lookup : Sample → Nat → Bool
  | [], _ => false
  | (a, b) :: S, y => if y = a then b else lookup S y

/-- **The lookup table is consistent** with every consistent sample. It memorises
the data and says nothing principled about unseen inputs, where it answers
`false` by fiat. -/
theorem lookup_consistent (S : Sample) (hS : SampleConsistent S) : Consistent (lookup S) S := by
  obtain ⟨f0, hf0⟩ := hS
  induction S with
  | nil => intro p hp; cases hp
  | cons q S ih =>
    obtain ⟨a, b⟩ := q
    have hq : f0 a = b := hf0 (a, b) (List.mem_cons_self ..)
    have ih' := ih (fun p hp => hf0 p (List.mem_cons_of_mem _ hp))
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · subst h; simp [lookup]
    · by_cases hpa : p.1 = a
      · simp only [lookup, hpa, ↓reduceIte]
        rw [← hq, ← hpa]
        exact hf0 p hp
      · simp only [lookup, hpa, ↓reduceIte]
        exact ih' p h

/-! ## Restricted classes: consistent hypothesis elimination -/

/-- Label the inputs `xs` with the target `t`. -/
def labelWith (t : Nat → Bool) (xs : List Nat) : Sample := xs.map (fun x => (x, t x))

/-- Hypotheses of `H` that agree with every example of `S`. -/
def survivors (H : List (Nat → Bool)) (S : Sample) : List (Nat → Bool) :=
  H.filter (fun h => S.all (fun p => h p.1 == p.2))

/-- The inputs `xs` separate `H`: two hypotheses of `H` that agree on `xs`
agree everywhere. -/
def Separates (xs : List Nat) (H : List (Nat → Bool)) : Prop :=
  ∀ h ∈ H, ∀ h' ∈ H, (∀ x ∈ xs, h x = h' x) → ∀ y, h y = h' y

theorem mem_survivors (H : List (Nat → Bool)) (t : Nat → Bool) (xs : List Nat)
    (h : Nat → Bool) :
    h ∈ survivors H (labelWith t xs) ↔ h ∈ H ∧ ∀ x ∈ xs, h x = t x := by
  simp [survivors, labelWith, List.mem_filter, List.all_eq_true]

/-- **Consistent hypothesis elimination.** If the target `t` is in the finite
class `H` and the observed inputs `xs` separate `H`, then `t` survives, and
every survivor agrees with `t` on every input, so the sample identifies the
target. -/
theorem elimination_identifies (H : List (Nat → Bool)) (t : Nat → Bool) (xs : List Nat)
    (ht : t ∈ H) (hsep : Separates xs H) :
    t ∈ survivors H (labelWith t xs) ∧
      ∀ h ∈ survivors H (labelWith t xs), ∀ y, h y = t y := by
  refine ⟨(mem_survivors H t xs t).mpr ⟨ht, fun _ _ => rfl⟩, ?_⟩
  intro h hh y
  obtain ⟨hH, hagree⟩ := (mem_survivors H t xs h).mp hh
  exact hsep h hH t ht hagree y

/-- **Without restriction no finite sample separates.** If `H` contains all
consistent completions, then no sample missing an input `x` separates `H`:
two members disagree at `x` although they agree on all of `xs`. -/
theorem no_separation_unrestricted (xs : List Nat) (x : Nat) (hx : x ∉ xs)
    (f0 : Nat → Bool) :
    ∃ f g : Nat → Bool, (∀ y ∈ xs, f y = g y) ∧ f x ≠ g x := by
  refine ⟨fun y => if y = x then true else f0 y, fun y => if y = x then false else f0 y,
    ?_, by simp⟩
  intro y hy
  have hne : ¬ (y = x) := fun h => hx (h ▸ hy)
  simp only [hne, ↓reduceIte]
end Issue532.Idea08
