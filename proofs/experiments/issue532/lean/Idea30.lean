/-!
# Issue #532, Idea 30: unrestricted circuit lower bounds (transfer and counting)

**Verdict: developed to an open obligation (conditional theorem proved).**

Two general facts are machine-checked.

* *Transfer* (`lower_bound_transfer`, `no_fast_algorithm`): a circuit lower
  bound, a simulation of fast algorithms by small circuits, and a size bound
  together exclude a fast algorithm.  The simulation (P ⊆ P/poly) is a
  hypothesis here, not a theorem of this file.
* *Shannon counting* (`uncovered_table`, `shannon_circuits`): lists of length
  `s` over an alphabet of size `m` are exactly `m ^ s`; truth tables on `n`
  bits are exactly `2 ^ (2 ^ n)` and duplicate-free; a list of codes shorter
  than a duplicate-free list cannot cover it.  Hence, for the concrete NAND
  straight-line circuit model below, if `(g + 1) * ((n + g) * (n + g)) ^ g`
  is below `2 ^ (2 ^ n)`, some Boolean function on `n` bits has no circuit
  with at most `g` gates.

Counting is non-explicit: it never names the hard function.  The open
obligation (`ExplicitNPLowerBound`) is an explicit NP function with a
superpolynomial circuit lower bound; with the simulation hypothesis it
separates P from NP (`explicit_lower_bound_separates`).  Nothing here proves
such a bound.  Natural proofs, relativization and algebrization constrain
how it could be proved.
-/

namespace Issue532.Idea30

/-- The abstract conditional contradiction. -/
theorem lower_bound_transfer {Algorithm Circuit : Type}
    (compile : Algorithm → Circuit) (fast : Algorithm → Prop)
    (correct expensive : Circuit → Prop)
    (lowerBound : ∀ c, correct c → expensive c)
    (simulation : ∀ a, fast a → correct (compile a))
    (sizeBound : ∀ a, fast a → ¬ expensive (compile a)) :
    ∀ a, ¬ fast a :=
  fun a ha => (sizeBound a ha) (lowerBound (compile a) (simulation a ha))

/-! ## Words over a finite alphabet -/

/-- Prefix every word of `W` with every letter of `alph`. -/
def consAll {α : Type} : List α → List (List α) → List (List α)
  | [], _ => []
  | a :: l, W => W.map (fun w => a :: w) ++ consAll l W

/-- All words of length `s` over `alph`. -/
def words {α : Type} (alph : List α) : Nat → List (List α)
  | 0 => [[]]
  | s + 1 => consAll alph (words alph s)

theorem consAll_length {α : Type} (l : List α) (W : List (List α)) :
    (consAll l W).length = l.length * W.length := by
  induction l with
  | nil => simp [consAll]
  | cons a l ih => simp [consAll, ih, Nat.succ_mul, Nat.add_comm]

/-- There are exactly `m ^ s` words of length `s` over an alphabet of size `m`. -/
theorem words_length {α : Type} (alph : List α) (s : Nat) :
    (words alph s).length = alph.length ^ s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [words, consAll_length, ih, Nat.pow_succ, Nat.mul_comm]

theorem mem_consAll {α : Type} (l : List α) (W : List (List α)) (w : List α) :
    w ∈ consAll l W ↔ ∃ a, a ∈ l ∧ ∃ v, v ∈ W ∧ w = a :: v := by
  induction l with
  | nil => simp [consAll]
  | cons b l ih =>
    simp only [consAll, List.mem_append, List.mem_map, ih, List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl h => obtain ⟨v, hv, e⟩ := h; exact ⟨b, Or.inl rfl, v, hv, e.symm⟩
      | inr h => obtain ⟨a, ha, v, hv, e⟩ := h; exact ⟨a, Or.inr ha, v, hv, e⟩
    · intro ⟨a, ha, v, hv, e⟩
      cases ha with
      | inl hab => subst hab; exact Or.inl ⟨v, hv, e.symm⟩
      | inr ha => exact Or.inr ⟨a, ha, v, hv, e⟩

/-- `words alph s` contains exactly the words of length `s` over `alph`
(soundness and completeness). -/
theorem mem_words {α : Type} (alph : List α) (s : Nat) (w : List α) :
    w ∈ words alph s ↔ w.length = s ∧ ∀ a, a ∈ w → a ∈ alph := by
  induction s generalizing w with
  | zero =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words]
  | succ s ih =>
    simp only [words, mem_consAll]
    constructor
    · intro ⟨a, ha, v, hv, e⟩
      subst e
      have := (ih v).1 hv
      refine ⟨by simp [this.1], ?_⟩
      intro b hb
      cases hb with
      | head => exact ha
      | tail _ hb => exact this.2 b hb
    · intro ⟨hl, hall⟩
      cases w with
      | nil => simp at hl
      | cons a v =>
        refine ⟨a, hall a (List.Mem.head _), v, (ih v).2 ⟨?_, ?_⟩, rfl⟩
        · simp at hl; exact hl
        · intro b hb; exact hall b (List.Mem.tail _ hb)

theorem nodup_map_cons {α : Type} (a : α) (W : List (List α)) (h : W.Nodup) :
    (W.map (fun w => a :: w)).Nodup := by
  induction W with
  | nil => exact List.nodup_nil
  | cons v W ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih h.2⟩
    intro ⟨u, hu, e⟩
    have : u = v := List.cons.inj e |>.2
    subst this
    exact h.1 hu

theorem consAll_nodup {α : Type} (l : List α) (W : List (List α))
    (hl : l.Nodup) (hW : W.Nodup) : (consAll l W).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [consAll]
    rw [List.nodup_append]
    refine ⟨nodup_map_cons a W hW, ih hl.2, ?_⟩
    intro x hx y hy e
    obtain ⟨v, _, ev⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, u, _, eu⟩ := (mem_consAll l W y).1 hy
    subst ev; subst eu
    have : a = b := (List.cons.inj e).1
    subst this
    exact hl.1 hb

/-- Words over a duplicate-free alphabet are duplicate-free. -/
theorem words_nodup {α : Type} (alph : List α) (h : alph.Nodup) (s : Nat) :
    (words alph s).Nodup := by
  induction s with
  | zero => simp [words]
  | succ s ih => exact consAll_nodup alph _ h ih

/-! ## Truth tables -/

/-- All Boolean inputs of length `n`. -/
def allBool (n : Nat) : List (List Bool) := words [false, true] n

theorem allBool_length (n : Nat) : (allBool n).length = 2 ^ n := words_length _ n

theorem allBool_nodup (n : Nat) : (allBool n).Nodup :=
  words_nodup _ (by decide) n

theorem mem_allBool (n : Nat) (x : List Bool) : x ∈ allBool n ↔ x.length = n := by
  unfold allBool
  rw [mem_words]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro b _
    cases b <;> simp

/-- Truth tables of `n`-bit functions: exactly `2 ^ (2 ^ n)` of them. -/
theorem tables_length (n : Nat) : (allBool (2 ^ n)).length = 2 ^ (2 ^ n) :=
  allBool_length _

/-- The function whose truth table (in the order of `allBool n`) is `tt`. -/
def fnOfTable : Nat → List Bool → List Bool → Bool
  | 0, tt, _ => tt.headD false
  | _ + 1, _, [] => false
  | n + 1, tt, b :: x => fnOfTable n (if b then tt.drop (2 ^ n) else tt.take (2 ^ n)) x

theorem allBool_succ (n : Nat) :
    allBool (n + 1) = (allBool n).map (fun w => false :: w)
      ++ (allBool n).map (fun w => true :: w) := by
  simp [allBool, words, consAll]

/-- Every table of length `2 ^ n` is the truth table of a function. -/
theorem table_of_fnOfTable (n : Nat) (tt : List Bool) (h : tt.length = 2 ^ n) :
    (allBool n).map (fnOfTable n tt) = tt := by
  induction n generalizing tt with
  | zero =>
    match tt, h with
    | [b], _ => rfl
  | succ n ih =>
    rw [allBool_succ, List.map_append, List.map_map, List.map_map]
    have ht : (tt.take (2 ^ n)).length = 2 ^ n := by
      rw [List.length_take, h, Nat.pow_succ]; omega
    have hd : (tt.drop (2 ^ n)).length = 2 ^ n := by
      rw [List.length_drop, h, Nat.pow_succ]; omega
    have e1 : (allBool n).map (fnOfTable (n + 1) tt ∘ fun w => false :: w)
        = tt.take (2 ^ n) := by
      rw [← ih _ ht]; rfl
    have e2 : (allBool n).map (fnOfTable (n + 1) tt ∘ fun w => true :: w)
        = tt.drop (2 ^ n) := by
      rw [← ih _ hd]; rfl
    rw [e1, e2, List.take_append_drop]

/-! ## Pigeonhole -/

/-- A duplicate-free list covered by the image of `codes` is no longer than `codes`. -/
theorem cover_length {Code : Type} (decode : Code → List Bool)
    (targets : List (List Bool)) (codes : List Code) (hnd : targets.Nodup)
    (hcov : ∀ t, t ∈ targets → ∃ c, c ∈ codes ∧ decode c = t) :
    targets.length ≤ codes.length := by
  have hsub : targets ⊆ codes.map decode := by
    intro t ht
    obtain ⟨c, hc, e⟩ := hcov t ht
    exact List.mem_map.2 ⟨c, hc, e⟩
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_map] at this
  exact this

/-- Abstract Shannon counting: fewer codes than truth tables leaves a table uncovered. -/
theorem uncovered_table {Code : Type} (decode : Code → List Bool) (n : Nat)
    (codes : List Code) (h : codes.length < 2 ^ (2 ^ n)) :
    ∃ t, t ∈ allBool (2 ^ n) ∧ ∀ c, c ∈ codes → decode c ≠ t := by
  apply Classical.byContradiction
  intro hno
  have hcov : ∀ t, t ∈ allBool (2 ^ n) → ∃ c, c ∈ codes ∧ decode c = t := by
    intro t ht
    apply Classical.byContradiction
    intro hc
    exact hno ⟨t, ht, fun c hcm e => hc ⟨c, hcm, e⟩⟩
  have := cover_length decode _ codes (allBool_nodup _) hcov
  rw [tables_length] at this
  omega

/-- Codes of length `≤ s` over an alphabet of size `m`, as one list. -/
def codesUpTo {α : Type} (alph : List α) : Nat → List (List α)
  | 0 => words alph 0
  | s + 1 => codesUpTo alph s ++ words alph (s + 1)

theorem codesUpTo_length {α : Type} (alph : List α) (h : 1 ≤ alph.length) (s : Nat) :
    (codesUpTo alph s).length ≤ (s + 1) * alph.length ^ s := by
  induction s with
  | zero => simp [codesUpTo, words]
  | succ s ih =>
    simp only [codesUpTo, List.length_append, words_length]
    have hp : alph.length ^ s ≤ alph.length ^ (s + 1) := Nat.pow_le_pow_right h (Nat.le_succ s)
    have : (s + 1) * alph.length ^ s ≤ (s + 1) * alph.length ^ (s + 1) :=
      Nat.mul_le_mul_left _ hp
    rw [Nat.succ_mul (s + 1)]
    omega

theorem mem_codesUpTo {α : Type} (alph : List α) (s : Nat) (w : List α)
    (hl : w.length ≤ s) (ha : ∀ a, a ∈ w → a ∈ alph) : w ∈ codesUpTo alph s := by
  induction s with
  | zero =>
    have : w.length = 0 := by omega
    simp only [codesUpTo]; exact (mem_words alph 0 w).2 ⟨this, ha⟩
  | succ s ih =>
    simp only [codesUpTo, List.mem_append]
    by_cases hs : w.length ≤ s
    · exact Or.inl (ih hs)
    · exact Or.inr ((mem_words alph (s + 1) w).2 ⟨by omega, ha⟩)

/-- Shannon counting for any code-based description of functions: if there are
fewer codes of length `≤ s` (over an alphabet of size `m ≥ 1`) than functions on
`n` bits, some table is not described by any such code. -/
theorem shannon_codes {α : Type} (alph : List α) (h1 : 1 ≤ alph.length)
    (decode : List α → List Bool) (n s : Nat)
    (h : (s + 1) * alph.length ^ s < 2 ^ (2 ^ n)) :
    ∃ t, t ∈ allBool (2 ^ n) ∧ ∀ w, w.length ≤ s → (∀ a, a ∈ w → a ∈ alph) →
      decode w ≠ t := by
  obtain ⟨t, ht, hno⟩ := uncovered_table decode n (codesUpTo alph s)
    (Nat.lt_of_le_of_lt (codesUpTo_length alph h1 s) h)
  exact ⟨t, ht, fun w hl ha => hno w (mem_codesUpTo alph s w hl ha)⟩

/-! ## A concrete circuit model: NAND straight-line programs -/

/-- Gate `(i, j)` appends the NAND of wires `i` and `j`. -/
abbrev Circuit := List (Nat × Nat)

def wire (w : List Bool) (i : Nat) : Bool := w.getD i false

def run (w : List Bool) : Circuit → List Bool
  | [] => w
  | (i, j) :: C => run (w ++ [!(wire w i && wire w j)]) C

/-- The output is the last wire. -/
def output (x : List Bool) (C : Circuit) : Bool := (run x C).getLastD false

/-- Gate `k` only reads the `n` inputs and earlier gates. -/
def WFfrom : Nat → Circuit → Prop
  | _, [] => True
  | N, (i, j) :: C => i < N ∧ j < N ∧ WFfrom (N + 1) C

def WF (n : Nat) (C : Circuit) : Prop := WFfrom n C

/-- All pairs from two lists. -/
def pairsOf : List Nat → List Nat → List (Nat × Nat)
  | [], _ => []
  | a :: l, m => m.map (fun b => (a, b)) ++ pairsOf l m

theorem pairsOf_length (l m : List Nat) : (pairsOf l m).length = l.length * m.length := by
  induction l with
  | nil => simp [pairsOf]
  | cons a l ih => simp [pairsOf, ih, Nat.succ_mul, Nat.add_comm]

theorem mem_pairsOf (l m : List Nat) (a b : Nat) (ha : a ∈ l) (hb : b ∈ m) :
    (a, b) ∈ pairsOf l m := by
  induction l with
  | nil => cases ha
  | cons c l ih =>
    simp only [pairsOf, List.mem_append, List.mem_map]
    cases ha with
    | head => exact Or.inl ⟨b, hb, rfl⟩
    | tail _ ha => exact Or.inr (ih ha)

theorem wf_bound (N : Nat) (C : Circuit) (h : WFfrom N C) :
    ∀ p, p ∈ C → p.1 < N + C.length ∧ p.2 < N + C.length := by
  induction C generalizing N with
  | nil => intro p hp; cases hp
  | cons q C ih =>
    obtain ⟨i, j⟩ := q
    obtain ⟨hi, hj, hC⟩ := h
    intro p hp
    simp only [List.length_cons]
    cases hp with
    | head => exact ⟨by simp; omega, by simp; omega⟩
    | tail _ hp =>
      have := ih (N + 1) hC p hp
      omega

/-- The gate alphabet for circuits with at most `g` gates on `n` inputs. -/
def gateAlphabet (n g : Nat) : List (Nat × Nat) := pairsOf (List.range (n + g)) (List.range (n + g))

theorem gateAlphabet_length (n g : Nat) : (gateAlphabet n g).length = (n + g) * (n + g) := by
  simp [gateAlphabet, pairsOf_length]

theorem wf_in_alphabet (n g : Nat) (C : Circuit) (hw : WF n C) (hl : C.length ≤ g) :
    ∀ p, p ∈ C → p ∈ gateAlphabet n g := by
  intro p hp
  have := wf_bound n C hw p hp
  obtain ⟨i, j⟩ := p
  exact mem_pairsOf _ _ i j (List.mem_range.2 (by simp at this; omega))
    (List.mem_range.2 (by simp at this; omega))

/-- Shannon's counting theorem for NAND circuits: if
`(g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n)`, some Boolean function on
`n` bits is computed by no well-formed circuit with at most `g` gates. -/
theorem shannon_circuits (n g : Nat)
    (h : (g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n)) :
    ∃ f : List Bool → Bool, ∀ C, WF n C → C.length ≤ g →
      ∃ x, x.length = n ∧ output x C ≠ f x := by
  have h1 : 1 ≤ (gateAlphabet n g).length ∨ (gateAlphabet n g).length = 0 := by omega
  cases h1 with
  | inr h0 =>
    -- n + g = 0: the only circuit is empty and reads no input
    have hng : n + g = 0 := by
      rw [gateAlphabet_length] at h0
      cases Nat.mul_eq_zero.1 h0 <;> assumption
    have hn : n = 0 := by omega
    have hg : g = 0 := by omega
    subst hn; subst hg
    refine ⟨fun _ => true, ?_⟩
    intro C _ hl
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], rfl, by decide⟩
  | inl h1 =>
    rw [← gateAlphabet_length] at h
    obtain ⟨t, ht, hno⟩ := shannon_codes (gateAlphabet n g) h1
      (fun C => (allBool n).map (fun x => output x C)) n g h
    have htl : t.length = 2 ^ n := (mem_allBool _ t).1 ht
    refine ⟨fnOfTable n t, ?_⟩
    intro C hw hl
    apply Classical.byContradiction
    intro hall
    apply hno C hl (wf_in_alphabet n g C hw hl)
    rw [← table_of_fnOfTable n t htl]
    apply List.map_congr_left
    intro x hx
    apply Classical.byContradiction
    intro hne
    exact hall ⟨x, (mem_allBool n x).1 hx, hne⟩

/-- Concrete instance: some Boolean function on 4 bits needs more than 2 NAND gates. -/
theorem four_bit_function_needs_three_gates :
    ∃ f : List Bool → Bool, ∀ C, WF 4 C → C.length ≤ 2 →
      ∃ x, x.length = 4 ∧ output x C ≠ f x :=
  shannon_circuits 4 2 (by decide)

/-! ## The open obligation -/

/-- Explicit polynomial bound `coefficient * (n + 1) ^ degree`. -/
structure Poly where
  coefficient : Nat
  degree : Nat

def Poly.eval (p : Poly) (n : Nat) : Nat := p.coefficient * (n + 1) ^ p.degree

/-- `f` has polynomial-size NAND circuits at every input length. -/
def PolySizeCircuits (f : List Bool → Bool) : Prop :=
  ∃ p : Poly, ∀ n, ∃ C, WF n C ∧ C.length ≤ p.eval n ∧
    ∀ x, x.length = n → output x C = f x

/-- `f` has a superpolynomial circuit lower bound. -/
def SuperpolyLowerBound (f : List Bool → Bool) : Prop :=
  ∀ p : Poly, ∃ n, ∀ C, WF n C → C.length ≤ p.eval n →
    ∃ x, x.length = n ∧ output x C ≠ f x

/-- The open obligation: an explicit function in the class `InNP` with a
superpolynomial circuit lower bound. -/
def ExplicitNPLowerBound (InNP : (List Bool → Bool) → Prop) : Prop :=
  ∃ f, InNP f ∧ SuperpolyLowerBound f

/-- A superpolynomial lower bound excludes polynomial-size circuits. -/
theorem superpoly_excludes_poly_circuits (f : List Bool → Bool)
    (h : SuperpolyLowerBound f) : ¬ PolySizeCircuits f := by
  intro ⟨p, hp⟩
  obtain ⟨n, hn⟩ := h p
  obtain ⟨C, hw, hl, hc⟩ := hp n
  obtain ⟨x, hx, hne⟩ := hn C hw hl
  exact hne (hc x hx)

/-- Transfer to algorithms, given the simulation of fast algorithms by
polynomial-size circuits as a hypothesis. -/
theorem no_fast_algorithm {Algorithm : Type} (computes : Algorithm → List Bool → Bool)
    (fast : Algorithm → Prop)
    (simulation : ∀ a, fast a → PolySizeCircuits (computes a))
    (f : List Bool → Bool) (h : SuperpolyLowerBound f) :
    ∀ a, fast a → computes a ≠ f := by
  intro a ha e
  apply superpoly_excludes_poly_circuits f h
  rw [← e]
  exact simulation a ha

/-- Conditional separation: the obligation plus the simulation hypothesis yields
a function in `InNP` computed by no fast algorithm. -/
theorem explicit_lower_bound_separates {Algorithm : Type}
    (InNP : (List Bool → Bool) → Prop) (computes : Algorithm → List Bool → Bool)
    (fast : Algorithm → Prop)
    (simulation : ∀ a, fast a → PolySizeCircuits (computes a))
    (h : ExplicitNPLowerBound InNP) :
    ∃ f, InNP f ∧ ∀ a, fast a → computes a ≠ f := by
  obtain ⟨f, hf, hlb⟩ := h
  exact ⟨f, hf, no_fast_algorithm computes fast simulation f hlb⟩

end Issue532.Idea30
