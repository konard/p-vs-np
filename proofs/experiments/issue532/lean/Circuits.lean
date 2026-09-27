import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532: a shared circuit model and the bridge to the machine model

Circuit lower bounds in the idea files are stated for the machine-model
language `Issue532.Machines.SAT`, over one concrete circuit model: NAND
straight-line programs. The model is honest: a circuit is a list of gates, its
size is the number of gates, and its output is computed by `output`.

* `Circuit`, `output`, `WF`: NAND straight-line programs on `n` input wires.
* `InPPoly`, `SuperpolyLowerBound`, `superpoly_iff_not_inPPoly`: the class
  P/poly and a superpolynomial circuit lower bound, which are complementary.
* `PSubsetPPoly`: every language in P has polynomial-size circuits
  (Savage 1972; Pippenger–Fischer 1979; Arora–Barak Theorem 6.6). It is a
  known theorem that this file does **not** prove; every use is an explicit
  hypothesis named `PSubsetPPoly`.
* `pNotEqualsNP_of_superpoly_sat`: under `SATInNP` and `PSubsetPPoly`, a
  superpolynomial circuit lower bound for SAT gives P ≠ NP.
* Circuit requirements are imposed only at positive input lengths: a
  well-formed circuit on `0` inputs is empty and outputs `false`, and counting
  length `0` would make `SuperpolyLowerBound SAT` trivially true and
  `PSubsetPPoly` false. `inPPoly_const` checks the convention.
* `shannon_circuits` (moved from Idea 30): Shannon counting over this model.
* `exists_superpolyLowerBound`, `exists_not_inPPoly`: some (non-explicit)
  language has a superpolynomial circuit lower bound, so the circuit
  obligations are not vacuous.
* `slice L n`: the Boolean function that `L` computes at length `n`, for
  formula models that evaluate under an assignment `Nat → Bool`.
-/

namespace Issue532.Circuits

open Complexity Issue532.Machines

/-- Gate `(i, j)` appends the NAND of wires `i` and `j`. -/
abbrev Circuit := List (Nat × Nat)

def wire (w : List Bool) (i : Nat) : Bool := w.getD i false

/-- All wire values: the inputs followed by one wire per gate. -/
def wires (w : List Bool) : Circuit → List Bool
  | [] => w
  | (i, j) :: C => wires (w ++ [!(wire w i && wire w j)]) C

/-- The output is the last wire. -/
def output (x : Word) (C : Circuit) : Bool := (wires x C).getLastD false

/-- Gate `k` only reads the `N` earlier wires. -/
def WFfrom : Nat → Circuit → Prop
  | _, [] => True
  | N, (i, j) :: C => i < N ∧ j < N ∧ WFfrom (N + 1) C

/-- A well-formed circuit on `n` inputs. -/
def WF (n : Nat) (C : Circuit) : Prop := WFfrom n C

/-- `C` is a well-formed circuit on `n` inputs that agrees with `L` on every
word of length `n`. -/
def CircuitDecides (n : Nat) (C : Circuit) (L : Language) : Prop :=
  WF n C ∧ ∀ x : Word, x.length = n → output x C = L x

/-- The class P/poly: `L` has circuits with polynomially many gates at every
positive input length.

Length `0` is excluded on purpose. A well-formed circuit on `0` inputs has no
gates (`WF 0 C` forces `C = []`), so its output is the constant `false`. If
length `0` counted, every language with `L [] = true` (SAT among them, since
the empty CNF is satisfiable) would be outside P/poly for a trivial reason,
and `PSubsetPPoly` would be false. One word per length changes no asymptotic
notion. -/
def InPPoly (L : Language) : Prop :=
  ∃ p : Polynomial, ∀ n, 0 < n → ∃ C : Circuit, C.length ≤ p.eval n ∧ CircuitDecides n C L

/-- A superpolynomial circuit lower bound: for every polynomial some positive
input length defeats every circuit of that size (see `InPPoly` for why the
length is positive). -/
def SuperpolyLowerBound (L : Language) : Prop :=
  ∀ p : Polynomial, ∃ n, 0 < n ∧ ∀ C : Circuit, C.length ≤ p.eval n → WF n C →
    ∃ x : Word, x.length = n ∧ output x C ≠ L x

theorem superpoly_iff_not_inPPoly (L : Language) : SuperpolyLowerBound L ↔ ¬ InPPoly L := by
  constructor
  · rintro h ⟨p, hp⟩
    obtain ⟨n, hn0, hn⟩ := h p
    obtain ⟨C, hl, hw, hc⟩ := hp n hn0
    obtain ⟨x, hx, hne⟩ := hn C hl hw
    exact hne (hc x hx)
  · intro h p
    apply Classical.byContradiction
    intro hno
    apply h
    refine ⟨p, fun n hn0 => ?_⟩
    apply Classical.byContradiction
    intro hC
    apply hno
    refine ⟨n, hn0, fun C hl hw => ?_⟩
    apply Classical.byContradiction
    intro hx
    apply hC
    refine ⟨C, hl, hw, fun x hlen => ?_⟩
    apply Classical.byContradiction
    intro hne
    exact hx ⟨x, hlen, hne⟩

/-- **Known theorem, not mechanised here.** Every language decided by a
polynomial-time `Complexity.Machine` has polynomial-size NAND circuits
(Savage 1972; Pippenger–Fischer 1979; Arora–Barak Theorem 6.6). The missing
part is the tableau construction for this machine model. -/
def PSubsetPPoly : Prop := ∀ L : Language, InP L → InPPoly L

/-- A language outside P/poly is outside P, given `PSubsetPPoly`. -/
theorem not_inP_of_not_inPPoly (hP : PSubsetPPoly) {L : Language} (h : ¬ InPPoly L) :
    ¬ InP L :=
  fun hL => h (hP L hL)

/-- **Bridge.** A superpolynomial circuit lower bound for SAT gives P ≠ NP,
using the membership half of Cook–Levin and `PSubsetPPoly`. -/
theorem pNotEqualsNP_of_superpoly_sat (mem : SATInNP) (hP : PSubsetPPoly)
    (h : SuperpolyLowerBound SAT) : PNotEqualsNP := fun hEq =>
  not_inP_of_not_inPPoly hP ((superpoly_iff_not_inPPoly SAT).mp h) (inP_sat_of_pEqualsNP mem hEq)

/-- The same bridge for any NP language. -/
theorem pNotEqualsNP_of_superpoly (hP : PSubsetPPoly) {L : Language} (mem : InNP L)
    (h : SuperpolyLowerBound L) : PNotEqualsNP := fun hEq =>
  not_inP_of_not_inPPoly hP ((superpoly_iff_not_inPPoly L).mp h) (hEq L mem)


/-! ## Sanity check: constant languages are in P/poly

With the positive-length convention every constant language has two- or
three-gate circuits, so `PSubsetPPoly` is not refuted by a degenerate case. -/

theorem wire_append_self (x : List Bool) (b : Bool) : wire (x ++ [b]) x.length = b := by
  simp [wire]

theorem wire_append_lt (x : List Bool) (b : Bool) (i : Nat) (h : i < x.length) :
    wire (x ++ [b]) i = wire x i := by
  simp [wire, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- The circuit `[(0,0), (0,n)]` outputs `true` on every input of positive length. -/
theorem output_const_true (x : Word) (hx : 0 < x.length) :
    output x [(0, 0), (0, x.length)] = true := by
  simp only [output, wires]
  rw [wire_append_self, wire_append_lt _ _ _ hx]
  cases wire x 0 <;> simp

/-- The circuit `[(0,0), (0,n), (n+1,n+1)]` outputs `false` on every input of positive length. -/
theorem output_const_false (x : Word) (hx : 0 < x.length) :
    output x [(0, 0), (0, x.length), (x.length + 1, x.length + 1)] = false := by
  simp only [output, wires]
  have e : x.length + 1 = (x ++ [!(wire x 0 && wire x 0)]).length := by simp
  rw [e, wire_append_self, wire_append_self, wire_append_lt _ _ _ hx]
  cases wire x 0 <;> simp

/-- Every constant language is in P/poly. -/
theorem inPPoly_const (b : Bool) : InPPoly (fun _ => b) := by
  refine ⟨⟨3, 0⟩, fun n hn => ?_⟩
  cases b
  · refine ⟨[(0, 0), (0, n), (n + 1, n + 1)], by simp [Polynomial.eval], ?_, ?_⟩
    · simp [WF, WFfrom]; omega
    · intro x hx; subst hx; exact output_const_false x hn
  · refine ⟨[(0, 0), (0, n)], by simp [Polynomial.eval], ?_, ?_⟩
    · simp [WF, WFfrom]; omega
    · intro x hx; subst hx; exact output_const_true x hn

/-! # Shannon counting over the shared circuit model

Moved from Idea 30 and stated over the shared `wires`, `output` and `WF`.
Lists of length `s` over an alphabet of size `m` are exactly `m ^ s`; truth
tables on `n` bits are exactly `2 ^ (2 ^ n)` and duplicate-free; a list of codes
shorter than a duplicate-free list cannot cover it. Hence, if
`(g + 1) * ((n + g) * (n + g)) ^ g < 2 ^ (2 ^ n)`, some Boolean function on
`n` bits has no circuit with at most `g` gates (`shannon_circuits`). -/

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

/-! ## Circuits as codes -/

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

/-! ## A language outside P/poly

Counting is non-explicit. The language `HardLang` below takes, at every
length `n = 2 ^ a`, a function that no circuit with `2 ^ (a * a)` gates computes;
it is chosen with `Classical.choose` and is not known to lie in NP. Its role is
non-vacuity: `¬ InPPoly L` and `SuperpolyLowerBound L` are satisfiable. -/

/-- The gate budget at length `n`: `2 ^ (log₂ n)²`, superpolynomial in `n`. -/
def gateBudget (n : Nat) : Nat := 2 ^ (Nat.log2 n * Nat.log2 n)

/-- The Shannon inequality for `n` inputs and budget `gateBudget n`. -/
abbrev ShannonAt (n : Nat) : Prop :=
  (gateBudget n + 1) * ((n + gateBudget n) * (n + gateBudget n)) ^ gateBudget n < 2 ^ (2 ^ n)

/-- A function on `n` bits with no circuit of `gateBudget n` gates, when the
Shannon inequality holds; otherwise the constant `false`. -/
noncomputable def hardAt (n : Nat) : Language :=
  if h : ShannonAt n then Classical.choose (shannon_circuits n (gateBudget n) h)
  else fun _ => false

theorem hardAt_spec (n : Nat) (h : ShannonAt n) :
    ∀ C, WF n C → C.length ≤ gateBudget n → ∃ x, x.length = n ∧ output x C ≠ hardAt n x := by
  unfold hardAt
  split
  · exact Classical.choose_spec (shannon_circuits n (gateBudget n) h)
  · contradiction

/-- The hard language: at length `n` it agrees with `hardAt n`. -/
noncomputable def HardLang : Language := fun x => hardAt x.length x

theorem sq_step (m : Nat) (hm : 7 ≤ m) (ih : 2 * (m * m) + 2 < 2 ^ m) :
    2 * ((m + 1) * (m + 1)) + 2 < 2 ^ (m + 1) := by
  have e : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have hmm : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
  rw [e, Nat.pow_succ]
  generalize m * m = s at *
  generalize 2 ^ m = t at *
  omega

theorem two_mul_sq_lt_two_pow (a : Nat) (ha : 7 ≤ a) : 2 * (a * a) + 2 < 2 ^ a := by
  obtain ⟨d, rfl⟩ : ∃ d, a = 7 + d := ⟨a - 7, by omega⟩
  induction d with
  | zero => decide
  | succ d ih =>
    have := sq_step (7 + d) (by omega) (ih (by omega))
    rwa [show 7 + (d + 1) = 7 + d + 1 by omega]

theorem le_two_pow_self (a : Nat) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.pow_succ]; omega

/-- The Shannon inequality holds at every length `2 ^ a` with `a ≥ 7`. -/
theorem shannonAt_two_pow (a : Nat) (ha : 7 ≤ a) : ShannonAt (2 ^ a) := by
  unfold ShannonAt gateBudget
  rw [Nat.log2_two_pow]
  generalize hB : a * a = B
  have haB : a ≤ B := by rw [← hB]; exact Nat.le_mul_of_pos_left a (by omega)
  have hkey : 2 * B + 2 < 2 ^ a := by rw [← hB]; exact two_mul_sq_lt_two_pow a ha
  -- `n + g ≤ 2 ^ (B + 1)`
  have hn : 2 ^ a ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) haB
  have hsum : 2 ^ a + 2 ^ B ≤ 2 ^ (B + 1) := by rw [Nat.pow_succ]; omega
  have hsq : (2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B) ≤ 2 ^ (2 * B + 2) := by
    have := Nat.mul_le_mul hsum hsum
    rw [← Nat.pow_add] at this
    rw [show 2 * B + 2 = B + 1 + (B + 1) by omega]
    exact this
  have hpow : ((2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B)) ^ 2 ^ B ≤ 2 ^ ((2 * B + 2) * 2 ^ B) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left hsq _
  have hg1 : 2 ^ B + 1 ≤ 2 ^ (2 ^ B) := by
    have h1 : 2 ^ B + 1 ≤ 2 ^ (B + 1) := by rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := B); omega
    exact Nat.le_trans h1 (Nat.pow_le_pow_right (by decide) (by
      have := le_two_pow_self B
      have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
      omega))
  have htot : (2 ^ B + 1) * ((2 ^ a + 2 ^ B) * (2 ^ a + 2 ^ B)) ^ 2 ^ B
      ≤ 2 ^ ((2 * B + 3) * 2 ^ B) := by
    have := Nat.mul_le_mul hg1 hpow
    rw [← Nat.pow_add] at this
    rw [show (2 * B + 3) * 2 ^ B = 2 ^ B + (2 * B + 2) * 2 ^ B by
      rw [Nat.add_mul (2 * B + 2) 1]; omega]
    exact this
  have hexp : (2 * B + 3) * 2 ^ B < 2 ^ (2 ^ a) := by
    have h1 : 2 * B + 3 ≤ 2 ^ (B + 2) := by
      have := le_two_pow_self (B + 2)
      have : 2 ^ (B + 2) = 4 * 2 ^ B := by rw [Nat.pow_add]; omega
      have := le_two_pow_self B
      omega
    have h2 : (2 * B + 3) * 2 ^ B ≤ 2 ^ (2 * B + 2) := by
      have := Nat.mul_le_mul_right (2 ^ B) h1
      rw [← Nat.pow_add, show B + 2 + B = 2 * B + 2 by omega] at this
      exact this
    exact Nat.lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by decide) hkey)
  exact Nat.lt_of_le_of_lt htot (Nat.pow_lt_pow_right (by decide) hexp)

/-- A polynomial is below the gate budget at length `2 ^ a` once `a` is large. -/
theorem poly_le_gateBudget (p : Polynomial) (a : Nat) (ha : p.coefficient + p.degree + 1 ≤ a) :
    p.eval (2 ^ a) ≤ gateBudget (2 ^ a) := by
  unfold gateBudget Polynomial.eval
  rw [Nat.log2_two_pow]
  obtain ⟨c, k⟩ := p
  simp only at ha ⊢
  have h1 : 2 ^ a + 1 ≤ 2 ^ (a + 1) := by
    rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := a); omega
  have h2 : (2 ^ a + 1) ^ k ≤ 2 ^ ((a + 1) * k) := by
    rw [Nat.pow_mul]; exact Nat.pow_le_pow_left h1 k
  have hc : c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
  have h3 : c * (2 ^ a + 1) ^ k ≤ 2 ^ (c + (a + 1) * k) := by
    rw [Nat.pow_add]; exact Nat.mul_le_mul hc h2
  refine Nat.le_trans h3 (Nat.pow_le_pow_right (by decide) ?_)
  -- `c + (a + 1) * k ≤ a * a`, using `a ≥ c + k + 1`
  obtain ⟨d, rfl⟩ : ∃ d, a = c + k + 1 + d := ⟨a - (c + k + 1), by omega⟩
  have e1 : (c + k + 1 + d + 1) * k = (c + k + 1 + d) * k + k := by
    rw [Nat.add_mul, Nat.one_mul]
  have e2 : (c + k + 1 + d) * (c + k + 1 + d) = (c + k + 1 + d) * c + (c + k + 1 + d) * k
      + (c + k + 1 + d) * (1 + d) := by
    rw [← Nat.mul_add, ← Nat.mul_add]; congr 1; omega
  have h4 : c ≤ (c + k + 1 + d) * c := Nat.le_mul_of_pos_left c (by omega)
  have h5 : k ≤ (c + k + 1 + d) * (1 + d) := by
    have : c + k + 1 + d ≤ (c + k + 1 + d) * (1 + d) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  omega

/-- **Non-vacuity of circuit lower bounds.** Some language has a
superpolynomial circuit lower bound. The witness `HardLang` comes from Shannon
counting and is not claimed to be in NP. -/
theorem exists_superpolyLowerBound : ∃ L : Language, SuperpolyLowerBound L := by
  refine ⟨HardLang, fun p => ?_⟩
  let a := p.coefficient + p.degree + 8
  refine ⟨2 ^ a, Nat.two_pow_pos a, fun C hl hw => ?_⟩
  have hsh := shannonAt_two_pow a (by omega)
  have hle := poly_le_gateBudget p a (by omega)
  obtain ⟨x, hx, hne⟩ := hardAt_spec (2 ^ a) hsh C hw (Nat.le_trans hl hle)
  refine ⟨x, hx, ?_⟩
  show output x C ≠ hardAt x.length x
  rw [hx]; exact hne

/-- **Non-vacuity of `¬ InPPoly`.** Some language is outside P/poly. -/
theorem exists_not_inPPoly : ∃ L : Language, ¬ InPPoly L := by
  obtain ⟨L, hL⟩ := exists_superpolyLowerBound
  exact ⟨L, (superpoly_iff_not_inPPoly L).mp hL⟩

/-- `InPPoly` is not the trivial class: it contains every constant language
and misses `HardLang`. -/
theorem inPPoly_nontrivial : (∃ L, InPPoly L) ∧ (∃ L, ¬ InPPoly L) :=
  ⟨⟨fun _ => true, inPPoly_const true⟩, exists_not_inPPoly⟩

/-! ## Slices: from a language to finite Boolean functions

Formula models in the idea files evaluate under an assignment `Nat → Bool`.
`slice L n` is the Boolean function on variables `0, …, n - 1` that `L`
computes at input length `n`. It ties a formula family to a language. -/

/-- `L` restricted to inputs of length `n`, read from variables `0, …, n - 1`. -/
def slice (L : Language) (n : Nat) (ρ : Nat → Bool) : Bool :=
  L ((List.range n).map ρ)

/-- `slice L n` evaluated on the bits of a word of length `n` is `L` of that word. -/
theorem slice_word (L : Language) (x : Word) :
    slice L x.length (fun i => x.getD i false) = L x := by
  unfold slice
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

end Issue532.Circuits
