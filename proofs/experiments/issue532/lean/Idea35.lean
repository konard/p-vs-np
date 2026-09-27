/-!
# Issue #532, Idea 35: exact compression of solution sets

A Boolean function on `n` variables (the solution set of a formula) is
represented by its truth table: the list of its values on `allInputs n`, a
list of length `2^n`. There are `2^(2^n)` truth tables.

Main results:

* `lossless_injective`: a lossless encoder (with a decoder) is injective.
* `inj_length_le`: list pigeonhole — an injective map from a duplicate-free
  list into a list `l'` forces `length ≤ length l'`.
* `inputsBelow_length`: there are exactly `2^m - 1` bit strings of length `< m`.
* `no_injective_into_shorter`: every injective code on the `2^M` bit strings
  of length `M` gives some string a code of length `≥ M`.
* `few_compressible`: for every `b`, at most `2^b - 1` of them get codes of
  length `< b` (so at most a `2^-c` fraction saves `c` bits).
* `truthTable_ofTable`: every table of length `2^n` is the truth table of an
  explicit function.
* `exact_representation_needs_long_codes`: every representation scheme
  `rep : (List Bool → Bool) → List Bool` that is exact on length-`n` inputs
  gives some Boolean function a representation of length `≥ 2^n`.
* `compactness_alone_trivial`, `decider_gives_compilation`,
  `compilation_decides`: the open obligation `CompactTractableCompilation`
  (compact **and** queryable) is equivalent to having a SAT decider, so the
  whole difficulty lies in the cost of compiling and querying.

Verdict: "compress every solution space exactly into polynomial size" is
refuted by counting, for every `n`. Compact exact representations of the
solution sets of small formulas are not ruled out by counting (the formula
itself is one). They are useful only if they support fast queries, and
requiring that is the same as requiring a fast SAT algorithm.
-/

namespace Issue532.Idea35

/-- **Lossless ⇒ injective.** An encoder with a left-inverse decoder is injective. -/
theorem lossless_injective {X Code : Type} (encode : X → Code) (decode : Code → X)
    (roundTrip : ∀ x, decode (encode x) = x) :
    ∀ x y, encode x = encode y → x = y := by
  intro x y h
  calc
    x = decode (encode x) := (roundTrip x).symm
    _ = decode (encode y) := congrArg decode h
    _ = y := roundTrip y

/-! ## List pigeonhole -/

theorem nodup_subset_length_le {β : Type} [DecidableEq β] :
    ∀ (l l' : List β), l.Nodup → (∀ x, x ∈ l → x ∈ l') → l.length ≤ l'.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l', hnd, hsub => by
    have ha : a ∈ l' := hsub a (List.mem_cons_self)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ x, x ∈ l → x ∈ l'.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hnd'.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub x (List.mem_cons_of_mem a hx))
    have ih := nodup_subset_length_le l (l'.erase a) hnd'.2 hsub'
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < l'.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ (l : List α), l.Nodup → (∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y) →
      (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro hmem
      obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
      have := hinj a List.mem_cons_self y (List.mem_cons_of_mem a hy) hfy.symm
      exact hnd'.1 (this ▸ hy)
    · exact nodup_map_of_inj f l hnd'.2
        (fun x hx y hy h => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) h)

/-- **Pigeonhole for lists.** An injective map from a duplicate-free list `l` into the
members of `l'` forces `l.length ≤ l'.length`. -/
theorem inj_length_le {α β : Type} [DecidableEq β] (f : α → β) (l : List α) (l' : List β)
    (hnd : l.Nodup) (hinj : ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y)
    (hmem : ∀ x, x ∈ l → f x ∈ l') : l.length ≤ l'.length := by
  have h := nodup_subset_length_le (l.map f) l' (nodup_map_of_inj f l hnd hinj)
    (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact hmem x hx)
  simpa using h

/-! ## Enumerations -/

/-- All bit strings of length `n`. -/
def allInputs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allInputs n).map (List.cons false) ++ (allInputs n).map (List.cons true)

theorem allInputs_length (n : Nat) : (allInputs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allInputs, ih, Nat.pow_succ]; omega

theorem length_of_mem_allInputs {n : Nat} {x : List Bool} (h : x ∈ allInputs n) :
    x.length = n := by
  induction n generalizing x with
  | zero => simp [allInputs] at h; simp [h]
  | succ n ih =>
    simp [allInputs] at h
    rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;> simp [ih hy]

theorem mem_allInputs (x : List Bool) : x ∈ allInputs x.length := by
  induction x with
  | nil => simp [allInputs]
  | cons b x ih => cases b <;> simp [allInputs, ih]

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

/-- All bit strings of length `< m`. -/
def inputsBelow : Nat → List (List Bool)
  | 0 => []
  | m + 1 => inputsBelow m ++ allInputs m

theorem mem_inputsBelow (x : List Bool) (m : Nat) (h : x.length < m) : x ∈ inputsBelow m := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    simp only [inputsBelow, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact Or.inl (ih hlt)
    · right; rw [← heq]; exact mem_allInputs x

theorem one_le_two_pow (m : Nat) : 1 ≤ 2 ^ m := Nat.one_le_two_pow

/-- There are exactly `2^m - 1` strings of length `< m`. -/
theorem inputsBelow_length (m : Nat) : (inputsBelow m).length = 2 ^ m - 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [inputsBelow, List.length_append, ih, allInputs_length, Nat.pow_succ]
    have := one_le_two_pow m
    omega

/-! ## Counting theorems for codes -/

/-- **No exact code into shorter strings.** Every code that is injective on the `2^M`
strings of length `M` gives one of them a code of length at least `M`. -/
theorem no_injective_into_shorter (M : Nat) (code : List Bool → List Bool)
    (inj : ∀ s, s ∈ allInputs M → ∀ t, t ∈ allInputs M → code s = code t → s = t) :
    ∃ t, t ∈ allInputs M ∧ M ≤ (code t).length := by
  apply Classical.byContradiction
  intro hno
  have hshort : ∀ t, t ∈ allInputs M → code t ∈ inputsBelow M := by
    intro t ht
    apply mem_inputsBelow
    apply Nat.lt_of_not_le
    intro hle
    exact hno ⟨t, ht, hle⟩
  have h := inj_length_le code (allInputs M) (inputsBelow M) (allInputs_nodup M) inj hshort
  rw [allInputs_length, inputsBelow_length] at h
  have := one_le_two_pow M
  omega

/-- **Few strings are compressible.** For an injective code on the strings of length `M`,
at most `2^b - 1` of them receive codes shorter than `b`. With `b = M - c`, at most a
`2^-c` fraction saves `c` bits. -/
theorem few_compressible (M b : Nat) (code : List Bool → List Bool)
    (inj : ∀ s, s ∈ allInputs M → ∀ t, t ∈ allInputs M → code s = code t → s = t) :
    ((allInputs M).filter (fun t => decide ((code t).length < b))).length ≤ 2 ^ b - 1 := by
  rw [← inputsBelow_length]
  apply inj_length_le code
  · exact List.Nodup.sublist List.filter_sublist (allInputs_nodup M)
  · intro s hs t ht h
    exact inj s (List.mem_filter.mp hs).1 t (List.mem_filter.mp ht).1 h
  · intro t ht
    apply mem_inputsBelow
    simpa using (List.mem_filter.mp ht).2

/-! ## From truth tables to Boolean functions -/

/-- The truth table of `f` on `n` variables. -/
def truthTable (n : Nat) (f : List Bool → Bool) : List Bool := (allInputs n).map f

theorem truthTable_length (n : Nat) (f : List Bool → Bool) :
    (truthTable n f).length = 2 ^ n := by
  simp [truthTable, allInputs_length]

theorem map_eq_imp_eq_on {α β : Type} (f g : α → β) :
    ∀ l : List α, l.map f = l.map g → ∀ x, x ∈ l → f x = g x
  | [], _, _, hx => by cases hx
  | a :: l, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at h
    cases hx with
    | head => exact h.1
    | tail _ hx' => exact map_eq_imp_eq_on f g l h.2 x hx'

/-- Equal truth tables means agreement on every input of length `n`. -/
theorem truthTable_eq_iff (n : Nat) (f g : List Bool → Bool) :
    truthTable n f = truthTable n g ↔ ∀ x, x.length = n → f x = g x := by
  constructor
  · intro h x hx
    exact map_eq_imp_eq_on f g (allInputs n) h x (hx ▸ mem_allInputs x)
  · intro h
    apply List.map_congr_left
    intro x hx
    exact h x (length_of_mem_allInputs hx)

/-- The function whose truth table is `t` (first half: first bit false). -/
def ofTable : Nat → List Bool → List Bool → Bool
  | 0, t, _ => t.headD false
  | _ + 1, _, [] => false
  | n + 1, t, b :: y => if b then ofTable n (t.drop (2 ^ n)) y else ofTable n (t.take (2 ^ n)) y

/-- **Every table is a truth table.** -/
theorem truthTable_ofTable : ∀ (n : Nat) (t : List Bool), t.length = 2 ^ n →
    truthTable n (ofTable n t) = t
  | 0, t, h => by
    match t, h with
    | [a], _ => rfl
  | n + 1, t, h => by
    have h0 : (fun y => ofTable (n + 1) t (false :: y)) = ofTable n (t.take (2 ^ n)) := by
      funext y; simp [ofTable]
    have h1 : (fun y => ofTable (n + 1) t (true :: y)) = ofTable n (t.drop (2 ^ n)) := by
      funext y; simp [ofTable]
    have ht : (t.take (2 ^ n)).length = 2 ^ n := by
      rw [List.length_take, h, Nat.pow_succ]; omega
    have hd : (t.drop (2 ^ n)).length = 2 ^ n := by
      rw [List.length_drop, h, Nat.pow_succ]; omega
    have e0 := truthTable_ofTable n _ ht
    have e1 := truthTable_ofTable n _ hd
    unfold truthTable at e0 e1 ⊢
    simp only [allInputs, List.map_append, List.map_map]
    have c0 : (ofTable (n + 1) t ∘ List.cons false) = ofTable n (t.take (2 ^ n)) := h0
    have c1 : (ofTable (n + 1) t ∘ List.cons true) = ofTable n (t.drop (2 ^ n)) := h1
    rw [c0, c1, e0, e1, List.take_append_drop]

/-- A representation scheme is exact on `n` variables if equal representations force
agreement on every length-`n` input. -/
def ExactOn (n : Nat) (rep : (List Bool → Bool) → List Bool) : Prop :=
  ∀ f g, rep f = rep g → ∀ x, x.length = n → f x = g x

/-- **Main counting theorem.** Every exact representation scheme for Boolean functions on
`n` variables represents some function by a string of length at least `2^n`. -/
theorem exact_representation_needs_long_codes (n : Nat)
    (rep : (List Bool → Bool) → List Bool) (exact : ExactOn n rep) :
    ∃ f : List Bool → Bool, 2 ^ n ≤ (rep f).length := by
  have inj : ∀ s, s ∈ allInputs (2 ^ n) → ∀ t, t ∈ allInputs (2 ^ n) →
      rep (ofTable n s) = rep (ofTable n t) → s = t := by
    intro s hs t ht h
    have hs' := length_of_mem_allInputs hs
    have ht' := length_of_mem_allInputs ht
    have heq := (truthTable_eq_iff n _ _).mpr (exact _ _ h)
    rw [truthTable_ofTable n s hs', truthTable_ofTable n t ht'] at heq
    exact heq
  obtain ⟨t, _, hlen⟩ := no_injective_into_shorter (2 ^ n) (fun t => rep (ofTable n t)) inj
  exact ⟨ofTable n t, hlen⟩

/-! ## The open obligation: compact and queryable -/

/-- **Open obligation.** A compilation of formulas into representations of size at most
`q (size φ)` from which satisfiability is read off by `query`. With `compile` and
`query` required to run in polynomial time, this is a polynomial-time SAT algorithm. -/
def CompactTractableCompilation {Formula Rep : Type} (size : Formula → Nat)
    (repSize : Rep → Nat) (sat : Formula → Bool) (q : Nat → Nat)
    (compile : Formula → Rep) (query : Rep → Bool) : Prop :=
  (∀ φ, repSize (compile φ) ≤ q (size φ)) ∧ ∀ φ, query (compile φ) = sat φ

/-- **Compactness alone is trivial.** The formula is a compact exact representation of
its own solution set; everything depends on the cost of `query`. -/
theorem compactness_alone_trivial {Formula : Type} (size : Formula → Nat)
    (sat : Formula → Bool) :
    CompactTractableCompilation size size sat (fun s => s) (fun φ => φ) sat :=
  ⟨fun _ => Nat.le_refl _, fun _ => rfl⟩

/-- **A decider gives a one-bit compilation.** -/
theorem decider_gives_compilation {Formula : Type} (size : Formula → Nat)
    (sat : Formula → Bool) :
    CompactTractableCompilation size (fun _ : Bool => 1) sat (fun _ => 1) sat (fun b => b) :=
  ⟨fun _ => Nat.le_refl _, fun _ => rfl⟩

/-- **A compilation gives a decider** (`query ∘ compile`). -/
theorem compilation_decides {Formula Rep : Type} (size : Formula → Nat)
    (repSize : Rep → Nat) (sat : Formula → Bool) (q : Nat → Nat)
    (compile : Formula → Rep) (query : Rep → Bool)
    (h : CompactTractableCompilation size repSize sat q compile query) :
    ∀ φ, sat φ = query (compile φ) :=
  fun φ => (h.2 φ).symm

/-- Size check: 16 functions on 2 variables, 15 strings shorter than 4. -/
example : (allInputs (2 ^ 2)).length = 16 ∧ (inputsBelow (2 ^ 2)).length = 15 := by decide

end Issue532.Idea35
