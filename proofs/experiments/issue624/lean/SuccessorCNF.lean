import proofs.experiments.issue624.lean.MachineCNF
import proofs.experiments.issue624.lean.FixedWindow

/-! CNF for one charged move between finite tape rows. Only states, head
positions, cells, and four symbol values are enumerated. The correspondence
uses the original `step`, including its two-way boundary behavior. -/
namespace Issue624.SuccessorCNF
open Complexity Issue532.Machines Issue568.Tableau Issue624.LocalCNF Issue624.MachineCNF

def flatten (c : Config) : List Symbol := c.left.reverse ++ c.head :: c.right
def cell (c : Config) (i : Nat) : Symbol := ((flatten c)[i]?).getD .blank
def decodeConfig (q h : Nat) (xs : List Symbol) : Config :=
  ⟨q, (xs.take h).reverse, (xs[h]?).getD .blank, xs.drop (h + 1)⟩

@[simp] theorem flatten_length (c : Config) : (flatten c).length = span c := by
  simp only [flatten, List.length_append, List.length_reverse, List.length_cons]
  unfold span
  omega

@[simp] theorem cell_head (c : Config) : cell c c.left.length = c.head := by
  simp [cell, flatten]

theorem decodeConfig_flatten (c : Config) :
    decodeConfig c.state c.left.length (flatten c) = c := by
  rcases c with ⟨q, l, h, r⟩
  simp [decodeConfig, flatten, List.drop_append]

theorem flatten_injective (c d : Config) (hq : c.state = d.state)
    (hh : c.left.length = d.left.length) (ht : flatten c = flatten d) : c = d := by
  rw [← decodeConfig_flatten c, ← decodeConfig_flatten d, hq, hh, ht]

def nextHead (h : Nat) : Direction → Nat
  | .left => h - 1 | .right => h + 1 | .stay => h
def Inside (width h : Nat) : Direction → Prop
  | .left => 0 < h | .right => h + 1 < width | .stay => True
instance (width h : Nat) (dir : Direction) : Decidable (Inside width h dir) :=
  match dir with
  | .left => inferInstanceAs (Decidable (0 < h))
  | .right => inferInstanceAs (Decidable (h + 1 < width))
  | .stay => inferInstanceAs (Decidable True)

theorem moveHead_flatten (c : Config) (q : Nat) (w : Symbol) (dir : Direction)
    (hi : Inside (span c) c.left.length dir) :
    flatten (moveHead c q w dir) = (flatten c).set c.left.length w ∧
      (moveHead c q w dir).left.length = nextHead c.left.length dir := by
  rcases c with ⟨state, l, a, r⟩
  cases dir with
  | stay => simp [flatten, moveHead, nextHead, List.set_append_right]
  | left =>
    cases l with
    | nil => simp [Inside] at hi
    | cons b ls =>
      simp [flatten, moveHead, nextHead, List.reverse_cons, List.set_append_right,
        List.append_assoc]
  | right =>
    cases r with
    | nil => simp [Inside, span] at hi
    | cons b rs =>
      simp [flatten, moveHead, nextHead, List.reverse_cons, List.set_append_right,
        List.append_assoc]

def stateVar (base q : Nat) : Nat := base + q
def headVar (base states h : Nat) : Nat := base + states + h
def tapeBase (base states width i : Nat) : Nat := base + states + width + 4 * i
def tapeVar (base states width i s : Nat) : Nat := tapeBase base states width i + s

def RowRepresents (a : Assignment) (base states width : Nat) (c : Config) : Prop :=
  span c = width ∧ Selected a base states c.state ∧
    Selected a (base + states) width c.left.length ∧
    ∀ i, i < width → Selected a (tapeBase base states width i) 4 (cell c i).index

def rowCNF (base states width : Nat) : CNF :=
  oneHot base states ++ oneHot (base + states) width ++
    (List.range width).flatMap fun i => oneHot (tapeBase base states width i) 4

def rowAssignment (base states width : Nat) (c : Config) : Assignment := fun v =>
  if v < base then false
  else if v < base + states then v == stateVar base c.state
  else if v < base + states + width then v == headVar base states c.left.length
  else if v < base + states + 5 * width then
    let k := v - (base + states + width)
    k % 4 == (cell c (k / 4)).index
  else false

theorem rowAssignment_state (base states width : Nat) (c : Config) (q : Nat)
    (hq : q < states) : rowAssignment base states width c (base + q) = (q == c.state) := by
  have h0 : ¬base + q < base := by omega
  have h1 : base + q < base + states := by omega
  simp [rowAssignment, stateVar, h0, h1, Bool.beq_eq_decide_eq]

theorem rowAssignment_head (base states width : Nat) (c : Config) (h : Nat)
    (hh : h < width) : rowAssignment base states width c (base + states + h) = (h == c.left.length) := by
  have h0 : ¬base + states + h < base := by omega
  have h1 : ¬base + states + h < base + states := by omega
  have h2 : base + states + h < base + states + width := by omega
  simp [rowAssignment, headVar, h0, h1, h2, Bool.beq_eq_decide_eq]

theorem rowAssignment_cell (base states width : Nat) (c : Config) (i s : Nat)
    (hi : i < width) (hs : s < 4) :
    rowAssignment base states width c (tapeVar base states width i s) = (s == (cell c i).index) := by
  have h0 : ¬tapeVar base states width i s < base := by dsimp [tapeVar, tapeBase]; omega
  have h1 : ¬tapeVar base states width i s < base + states := by dsimp [tapeVar, tapeBase]; omega
  have h2 : ¬tapeVar base states width i s < base + states + width := by dsimp [tapeVar, tapeBase]; omega
  have h3 : tapeVar base states width i s < base + states + 5 * width := by
    dsimp [tapeVar, tapeBase]; omega
  have hk : tapeVar base states width i s - (base + states + width) = 4 * i + s := by
    dsimp [tapeVar, tapeBase]; omega
  have hd : (4 * i + s) / 4 = i := by omega
  have hm : (4 * i + s) % 4 = s := by omega
  simp [rowAssignment, h0, h1, h2, h3, hk, hd, hm]

/-- Every bounded fixed-width configuration has a constructive row model. -/
theorem rowAssignment_represents (base states width : Nat) (c : Config)
    (hc : span c = width) (hq : c.state < states) :
    RowRepresents (rowAssignment base states width c) base states width c := by
  have hh : c.left.length < width := by unfold span at hc; omega
  refine ⟨hc, ⟨hq, ?_, ?_⟩, ⟨hh, ?_, ?_⟩, ?_⟩
  · simp [rowAssignment_state _ _ _ _ _ hq]
  · intro q hb he
    simpa [rowAssignment_state _ _ _ _ _ hb] using he
  · simp [rowAssignment_head _ _ _ _ _ hh]
  · intro h hb he
    simpa [rowAssignment_head _ _ _ _ _ hb] using he
  · intro i hi
    refine ⟨symbolIndex_lt _, ?_, ?_⟩
    · change rowAssignment base states width c (tapeVar base states width i (cell c i).index) = true
      rw [rowAssignment_cell _ _ _ _ i _ hi (symbolIndex_lt _)]
      simp
    · intro s hs he
      change rowAssignment base states width c (tapeVar base states width i s) = true at he
      simpa only [rowAssignment_cell _ _ _ _ i s hi hs, beq_iff_eq] using he

theorem rowRepresents_models (a : Assignment) (base states width : Nat) (c : Config)
    (h : RowRepresents a base states width c) : evalCNF a (rowCNF base states width) = true := by
  simp only [rowCNF, evalCNF_append, Bool.and_eq_true, oneHot_selected,
    evalCNF_flatMap, List.mem_range]
  exact ⟨⟨⟨c.state, h.2.1⟩, ⟨c.left.length, h.2.2.1⟩⟩,
    fun i hi => ⟨(cell c i).index, h.2.2.2 i hi⟩⟩

def selectedIndex (a : Assignment) (base size : Nat) : Nat :=
  ((List.range size).find? fun i => a (base + i)).getD 0

private theorem find_selected (a : Assignment) (base v : Nat) (xs : List Nat)
    (hv : v ∈ xs) (ht : a (base + v) = true)
    (hu : ∀ j ∈ xs, a (base + j) = true → j = v) :
    (xs.find? fun i => a (base + i)) = some v := by
  induction xs with
  | nil => simp at hv
  | cons j xs ih =>
    cases hj : a (base + j) with
    | true => simpa [List.find?_cons, hj] using congrArg some (hu j (by simp) hj)
    | false =>
      have hv' : v ∈ xs := by
        rcases List.mem_cons.mp hv with he | he
        · subst v; rw [hj] at ht; cases ht
        · exact he
      simpa [List.find?_cons, hj] using ih hv' (fun k hk => hu k (by simp [hk]))

theorem selectedIndex_selected (a : Assignment) (base size v : Nat)
    (hv : Selected a base size v) : selectedIndex a base size = v := by
  unfold selectedIndex
  rw [find_selected a base v _ (List.mem_range.mpr hv.1) hv.2.1
    (fun j hj => hv.2.2 j (List.mem_range.mp hj))]
  rfl

theorem decodeConfig_shape (q h : Nat) (xs : List Symbol) (hh : h < xs.length) :
    flatten (decodeConfig q h xs) = xs ∧
      (decodeConfig q h xs).left.length = h ∧ span (decodeConfig q h xs) = xs.length := by
  have hf : flatten (decodeConfig q h xs) = xs := by
    simp only [flatten, decodeConfig, List.reverse_reverse,
      List.getElem?_eq_getElem hh, Option.getD_some]
    rw [← List.drop_eq_getElem_cons hh, List.take_append_drop]
  refine ⟨hf, ?_, ?_⟩
  · simp [decodeConfig, Nat.min_eq_left (Nat.le_of_lt hh)]
  · rw [← flatten_length, hf]

def decodeRow (a : Assignment) (base states width : Nat) : Config :=
  decodeConfig (selectedIndex a base states) (selectedIndex a (base + states) width)
    ((List.range width).map fun i =>
      symbolOfIndex (selectedIndex a (tapeBase base states width i) 4))

/-- The row clauses alone extract a configuration from every satisfying
assignment. Decoding is a bounded search and does not use classical choice. -/
theorem rowCNF_models (a : Assignment) (base states width : Nat) :
    evalCNF a (rowCNF base states width) = true ↔
      RowRepresents a base states width (decodeRow a base states width) := by
  constructor
  · intro hf
    simp only [rowCNF, evalCNF_append, Bool.and_eq_true, oneHot_selected,
      evalCNF_flatMap, List.mem_range] at hf
    obtain ⟨⟨⟨q, hq⟩, ⟨h, hh⟩⟩, ht⟩ := hf
    have hshape := decodeConfig_shape q h
      ((List.range width).map fun i => symbolOfIndex (selectedIndex a (tapeBase base states width i) 4))
      (by simpa using hh.1)
    unfold decodeRow
    rw [selectedIndex_selected _ _ _ _ hq, selectedIndex_selected _ _ _ _ hh]
    refine ⟨by simpa using hshape.2.2, hq, ?_, ?_⟩
    · simpa only [hshape.2.1] using hh
    · intro i hi
      obtain ⟨s, hs⟩ := ht i hi
      unfold cell
      rw [hshape.1]
      simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
        Option.getD_some, selectedIndex_selected _ _ _ _ hs, symbolIndex_of_lt s hs.1]
      exact hs
  · exact rowRepresents_models a base states width _

theorem selected_true_iff (a : Assignment) (base size v j : Nat)
    (hv : Selected a base size v) (hj : j < size) : a (base + j) = true ↔ j = v :=
  ⟨hv.2.2 j hj, fun he => he ▸ hv.2.1⟩

def guard (base states width q h s : Nat) : Clause :=
  [⟨stateVar base q, true⟩, ⟨headVar base states h, true⟩,
    ⟨tapeVar base states width h s, true⟩]

theorem guard_models (a : Assignment) (base states width : Nat) (c : Config)
    (hc : RowRepresents a base states width c) (q h s : Nat)
    (hq : q < states) (hh : h < width) (hs : s < 4) :
    (∀ l ∈ guard base states width q h s, evalLit a l = true) ↔
      q = c.state ∧ h = c.left.length ∧ symbolOfIndex s = c.head := by
  have hg : (∀ l ∈ guard base states width q h s, evalLit a l = true) ↔
      a (base + q) = true ∧ a (base + states + h) = true ∧
        a (tapeBase base states width h + s) = true := by
    simp [guard, evalLit, stateVar, headVar, tapeVar]
  rw [hg]
  rw [selected_true_iff _ _ _ _ _ hc.2.1 hq,
    selected_true_iff _ _ _ _ _ hc.2.2.1 hh,
    selected_true_iff _ _ _ _ _ (hc.2.2.2 h hh) hs]
  constructor
  · rintro ⟨hq, hh, he⟩
    exact ⟨hq, hh, by rw [he, hh, cell_head, symbolOfIndex_index]⟩
  · rintro ⟨hq, hh, he⟩
    exact ⟨hq, hh, by rw [hh, cell_head, ← he, symbolIndex_of_lt s hs]⟩

def copyRules (prem : Clause) (base next states width h : Nat) (write : Symbol) : CNF :=
  (List.range width).flatMap fun i => (List.range 4).map fun s =>
    implies (prem ++ [⟨tapeVar base states width i s, true⟩])
      [⟨tapeVar next states width i (if i = h then write.index else s), true⟩]

def instructionRules (m : Machine) (base next width q h s : Nat) : CNF :=
  let states := m.program.length
  let prem := guard base states width q h s
  match m.instruction q (symbolOfIndex s) with
  | .halt _ => [implies prem []]
  | .move target write dir =>
    if target < states ∧ Inside width h dir then
      [implies prem [⟨stateVar next target, true⟩],
       implies prem [⟨headVar next states (nextHead h dir), true⟩]] ++
        copyRules prem base next states width h write
    else [implies prem []]

def transitionCNF (m : Machine) (base next width : Nat) : CNF :=
  (List.range m.program.length).flatMap fun q =>
    (List.range width).flatMap fun h =>
      (List.range 4).flatMap fun s => instructionRules m base next width q h s

def successorCNF (m : Machine) (base next width : Nat) : CNF :=
  rowCNF base m.program.length width ++ rowCNF next m.program.length width ++
    transitionCNF m base next width

theorem inside_of_moveHead_span (c : Config) (q : Nat) (w : Symbol) (dir : Direction)
    (hs : span (moveHead c q w dir) = span c) : Inside (span c) c.left.length dir := by
  rcases c with ⟨state, l, a, r⟩
  cases dir <;> cases l <;> cases r <;> simp_all [Inside, span, moveHead] <;> omega

theorem moveHead_cells (c : Config) (q : Nat) (w : Symbol) (dir : Direction)
    (hi : Inside (span c) c.left.length dir) (i : Nat) (_hb : i < span c) :
    cell (moveHead c q w dir) i = if i = c.left.length then w else cell c i := by
  have hh : c.left.length < span c := by unfold span; omega
  unfold cell
  rw [(moveHead_flatten c q w dir hi).1, List.getElem?_set]
  by_cases he : i = c.left.length
  · simp [he, flatten_length, hh]
  · simp [he, Ne.symm he]

theorem config_eq_of_cells (c d : Config) (hq : c.state = d.state)
    (hh : c.left.length = d.left.length) (hw : span c = span d)
    (hc : ∀ i, i < span c → cell c i = cell d i) : c = d := by
  apply flatten_injective c d hq hh
  apply List.ext_getElem (by simpa using hw)
  intro i hi hj
  simpa only [cell, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some] using hc i (by simpa using hi)

theorem decodeRow_represents (a : Assignment) (base states width : Nat) (c : Config)
    (hc : RowRepresents a base states width c) : decodeRow a base states width = c := by
  have hd := (rowCNF_models a base states width).mp (rowRepresents_models _ _ _ _ _ hc)
  apply config_eq_of_cells
  · exact hc.2.1.2.2 _ hd.2.1.1 hd.2.1.2.1
  · exact hc.2.2.1.2.2 _ hd.2.2.1.1 hd.2.2.1.2.1
  · exact hd.1.trans hc.1.symm
  · intro i hi
    rw [hd.1] at hi
    apply symbol_index_injective
    exact (hc.2.2.2 i (by omega)).2.2 _ (symbolIndex_lt _) (hd.2.2.2 i (by omega)).2.1

theorem moveHead_matches (c d : Config) (states width q : Nat) (w : Symbol)
    (dir : Direction) (hc : span c = width) (hd : span d = width)
    (hq : d.state < states) : moveHead c q w dir = d ↔
      q < states ∧ Inside width c.left.length dir ∧ d.state = q ∧
        d.left.length = nextHead c.left.length dir ∧
        ∀ i, i < width → cell d i = if i = c.left.length then w else cell c i := by
  have hs : (moveHead c q w dir).state = q := by
    rcases c with ⟨state, l, a, r⟩
    cases dir <;> cases l <;> cases r <;> rfl
  constructor
  · intro he
    have hi := inside_of_moveHead_span c q w dir (by rw [he, hc, hd])
    refine ⟨by rw [← he, hs] at hq; exact hq, hc ▸ hi, by rw [← he, hs],
      by rw [← he, (moveHead_flatten c q w dir hi).2], ?_⟩
    intro i hb
    rw [← he]
    exact moveHead_cells c q w dir hi i (hc ▸ hb)
  · rintro ⟨_, hi, hstate, hhead, hcells⟩
    have hi' := hc.symm ▸ hi
    apply config_eq_of_cells (moveHead c q w dir) d (hs.trans hstate.symm)
      ((moveHead_flatten c q w dir hi').2.trans hhead.symm)
    · rw [← flatten_length, (moveHead_flatten c q w dir hi').1]
      simpa using hc.trans hd.symm
    · intro i hb
      have hwidth : span (moveHead c q w dir) = width := by
        rw [← flatten_length, (moveHead_flatten c q w dir hi').1]
        simpa using hc
      rw [moveHead_cells c q w dir hi' i (by omega), hcells i (by omega)]

theorem copyRules_models (a : Assignment) (prem : Clause) (base next states width h : Nat)
    (write : Symbol) : evalCNF a (copyRules prem base next states width h write) = true ↔
      ((∀ l ∈ prem, evalLit a l = true) → ∀ i, i < width → ∀ s, s < 4 →
        a (tapeVar base states width i s) = true →
        a (tapeVar next states width i (if i = h then write.index else s)) = true) := by
  simp only [copyRules, evalCNF_flatMap, List.mem_range, evalCNF_map,
    implies_models, evalClause, evalLit, Bool.or_false, beq_iff_eq]
  constructor
  · intro hf hp i hi s hs ht
    apply hf i hi s hs
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hp l hl
    · simp only [List.mem_singleton] at hl
      subst l
      simpa [evalLit] using ht
  · intro hf i hi s hs hp
    apply hf (fun l hl => hp l (List.mem_append_left _ hl)) i hi s hs
    simpa [evalLit] using hp ⟨tapeVar base states width i s, true⟩
      (List.mem_append_right _ (List.mem_singleton_self _))

theorem copyRules_cells (a : Assignment) (base next states width h : Nat) (write : Symbol)
    (c d : Config) (hc : RowRepresents a base states width c)
    (hd : RowRepresents a next states width d) :
    (∀ i, i < width → ∀ s, s < 4 → a (tapeVar base states width i s) = true →
      a (tapeVar next states width i (if i = h then write.index else s)) = true) ↔
      ∀ i, i < width → cell d i = if i = h then write else cell c i := by
  constructor
  · intro hf i hi
    have hs := symbolIndex_lt (cell c i)
    have ho := hf i hi _ hs (hc.2.2.2 i hi).2.1
    have hout : (if i = h then write.index else (cell c i).index) < 4 := by
      split <;> exact symbolIndex_lt _
    have he := (hd.2.2.2 i hi).2.2 _ hout ho
    apply symbol_index_injective
    by_cases heq : i = h <;> simp only [heq, ite_true, ite_false] at he ⊢ <;> exact he.symm
  · intro hf i hi s hs ht
    have he := (hc.2.2.2 i hi).2.2 s hs ht
    have hd' := (hd.2.2.2 i hi).2.1
    have he' : (if i = h then write.index else s) = (cell d i).index := by
      rw [hf i hi, he]
      split <;> rfl
    exact he'.symm ▸ hd'

theorem instructionRules_models (m : Machine) (base next width q h s : Nat) (a : Assignment) :
    evalCNF a (instructionRules m base next width q h s) = true ↔
      ((∀ l ∈ guard base m.program.length width q h s, evalLit a l = true) →
        match m.instruction q (symbolOfIndex s) with
        | .halt _ => False
        | .move target write dir =>
          target < m.program.length ∧ Inside width h dir ∧
            a (stateVar next target) = true ∧
            a (headVar next m.program.length (nextHead h dir)) = true ∧
            ∀ i, i < width → ∀ t, t < 4 →
              a (tapeVar base m.program.length width i t) = true →
              a (tapeVar next m.program.length width i (if i = h then write.index else t)) = true) := by
  unfold instructionRules
  cases m.instruction q (symbolOfIndex s) with
  | halt b => simp [evalCNF, implies_models, evalClause]
  | move target write dir =>
    by_cases hi : target < m.program.length ∧ Inside width h dir
    · simp only [ite_eq_left hi, evalCNF_append, Bool.and_eq_true, evalCNF,
        Bool.and_true, implies_models, evalClause, evalLit, Bool.or_false,
        beq_iff_eq, copyRules_models]
      constructor
      · rintro ⟨⟨hq, hh⟩, ht⟩ hp
        exact ⟨hi.1, hi.2, hq hp, hh hp, ht hp⟩
      · intro hf
        exact ⟨⟨fun hp => (hf hp).2.2.1, fun hp => (hf hp).2.2.2.1⟩,
          fun hp => (hf hp).2.2.2.2⟩
    · simp only [ite_eq_right hi, evalCNF, Bool.and_true, implies_models,
        evalClause, Bool.false_eq_true]
      constructor
      · intro hf hp
        exact False.elim (hf hp)
      · intro hf hp
        exact hi ⟨(hf hp).1, (hf hp).2.1⟩

theorem nextHead_lt (width h : Nat) (dir : Direction) (hh : h < width)
    (hi : Inside width h dir) : nextHead h dir < width := by
  cases dir <;> simp_all [nextHead, Inside] <;> omega

theorem instructionRules_step (m : Machine) (base next width q h s : Nat) (a : Assignment)
    (c d : Config) (hc : RowRepresents a base m.program.length width c)
    (hd : RowRepresents a next m.program.length width d)
    (hq : q < m.program.length) (hh : h < width) (hs : s < 4) :
    evalCNF a (instructionRules m base next width q h s) = true ↔
      ((∀ l ∈ guard base m.program.length width q h s, evalLit a l = true) → step m c = .inr d) := by
  rw [instructionRules_models]
  constructor
  · intro hf hp
    have hout := hf hp
    obtain ⟨rfl, rfl, he⟩ := (guard_models a _ _ _ c hc q h s hq hh hs).mp hp
    rw [he] at hout
    unfold step
    cases hi : m.instruction c.state c.head with
    | halt b => simp [hi] at hout
    | move target write dir =>
      simp only [hi] at hout
      obtain ⟨ht, hi', hstate, hhead, hcopy⟩ := hout
      have hstate' := (hd.2.1).2.2 target ht hstate
      have hhead' := (hd.2.2.1).2.2 _ (nextHead_lt width _ dir hh hi') hhead
      have hcells := (copyRules_cells a base next _ width _ write c d hc hd).mp hcopy
      exact congrArg Sum.inr ((moveHead_matches c d _ width target write dir hc.1 hd.1 hd.2.1.1).mpr
        ⟨ht, hi', hstate'.symm, hhead'.symm, hcells⟩)
  · intro hf hp
    have hstep := hf hp
    obtain ⟨rfl, rfl, he⟩ := (guard_models a _ _ _ c hc q h s hq hh hs).mp hp
    rw [he]
    unfold step at hstep
    cases hi : m.instruction c.state c.head with
    | halt b => rw [hi] at hstep; cases hstep
    | move target write dir =>
      rw [hi] at hstep
      have hmove := Sum.inr.inj hstep
      obtain ⟨ht, hi', hstate, hhead, hcells⟩ :=
        (moveHead_matches c d _ width target write dir hc.1 hd.1 hd.2.1.1).mp hmove
      refine ⟨ht, hi', ?_, ?_, ?_⟩
      · exact hstate ▸ hd.2.1.2.1
      · exact hhead ▸ hd.2.2.1.2.1
      · exact (copyRules_cells a base next _ width _ write c d hc hd).mpr hcells

/-- The local compiler is sound and complete for the original charged step
between represented rows. Halts, missing instructions, invalid states, and
window exits cannot masquerade as successor moves. -/
theorem transitionCNF_step (m : Machine) (base next width : Nat) (a : Assignment)
    (c d : Config) (hc : RowRepresents a base m.program.length width c)
    (hd : RowRepresents a next m.program.length width d) :
    evalCNF a (transitionCNF m base next width) = true ↔ step m c = .inr d := by
  simp only [transitionCNF, evalCNF_flatMap, List.mem_range]
  constructor
  · intro hf
    have h := (instructionRules_step m base next width c.state c.left.length c.head.index a
      c d hc hd hc.2.1.1 hc.2.2.1.1 (symbolIndex_lt c.head)).mp
        (hf _ hc.2.1.1 _ hc.2.2.1.1 _ (symbolIndex_lt c.head))
    apply h
    exact (guard_models a _ _ _ c hc _ _ _ hc.2.1.1 hc.2.2.1.1
      (symbolIndex_lt c.head)).mpr ⟨rfl, rfl, symbolOfIndex_index c.head⟩
  · intro hs q hq h hh s hb
    exact (instructionRules_step m base next width q h s a c d hc hd hq hh hb).mpr
      (fun _ => hs)

theorem successorCNF_step (m : Machine) (base next width : Nat) (a : Assignment)
    (c d : Config) (hc : RowRepresents a base m.program.length width c)
    (hd : RowRepresents a next m.program.length width d) :
    evalCNF a (successorCNF m base next width) = true ↔ step m c = .inr d := by
  simp only [successorCNF, evalCNF_append, rowRepresents_models a _ _ _ c hc,
    rowRepresents_models a _ _ _ d hd, Bool.true_and]
  exact transitionCNF_step m base next width a c d hc hd

theorem successorCNF_models (m : Machine) (base next width : Nat) (a : Assignment) :
    evalCNF a (successorCNF m base next width) = true ↔
      RowRepresents a base m.program.length width (decodeRow a base m.program.length width) ∧
      RowRepresents a next m.program.length width (decodeRow a next m.program.length width) ∧
      step m (decodeRow a base m.program.length width) =
        .inr (decodeRow a next m.program.length width) := by
  constructor
  · intro hf
    have h := hf
    simp only [successorCNF, evalCNF_append, Bool.and_eq_true] at h
    have hc := (rowCNF_models a base m.program.length width).mp h.1.1
    have hd := (rowCNF_models a next m.program.length width).mp h.1.2
    exact ⟨hc, hd, (successorCNF_step m base next width a _ _ hc hd).mp hf⟩
  · rintro ⟨hc, hd, hs⟩
    exact (successorCNF_step m base next width a _ _ hc hd).mpr hs

theorem successorCNF_sound (m : Machine) (base next width : Nat) (a : Assignment)
    (hf : evalCNF a (successorCNF m base next width) = true) :
    step m (decodeRow a base m.program.length width) =
      .inr (decodeRow a next m.program.length width) :=
  ((successorCNF_models m base next width a).mp hf).2.2

theorem successorCNF_decoded_wrong_successor (m : Machine) (base next width : Nat) (a : Assignment)
    (hs : step m (decodeRow a base m.program.length width) ≠
      .inr (decodeRow a next m.program.length width)) :
    evalCNF a (successorCNF m base next width) = false := by
  cases he : evalCNF a (successorCNF m base next width) with
  | false => rfl
  | true => exact False.elim (hs (successorCNF_sound m base next width a he))

theorem successorCNF_wrong_successor (m : Machine) (base next width : Nat) (a : Assignment)
    (c d : Config) (hc : RowRepresents a base m.program.length width c)
    (hd : RowRepresents a next m.program.length width d) (h : step m c ≠ .inr d) :
    evalCNF a (successorCNF m base next width) = false := by
  cases he : evalCNF a (successorCNF m base next width) with
  | false => rfl
  | true => exact False.elim (h ((successorCNF_step m base next width a c d hc hd).mp he))

private theorem flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (bound : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) : (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem rowCNF_length (base states width : Nat) :
    (rowCNF base states width).length ≤ states * states + width * width + 17 * width + 2 := by
  have hs := oneHot_length base states
  have hh := oneHot_length (base + states) width
  have ht := flatMap_length_le (List.range width)
    (fun i => oneHot (tapeBase base states width i) 4) 17
      (fun i _ => oneHot_length _ 4)
  simp only [rowCNF, List.length_append, List.length_range] at *
  omega

theorem rowCNF_bounds (base states width : Nat) :
    VarsBelow (base + states + 5 * width) (rowCNF base states width) ∧
      ∀ c ∈ rowCNF base states width, c.length ≤ states + width + 6 := by
  constructor
  · intro c hc l hl
    simp only [rowCNF, List.mem_append, List.mem_flatMap, List.mem_range] at hc
    rcases hc with (hc | hc) | ⟨i, hi, hc⟩
    · have := (oneHot_bounds base states).1 c hc l hl; omega
    · have := (oneHot_bounds (base + states) width).1 c hc l hl; omega
    · have := (oneHot_bounds (tapeBase base states width i) 4).1 c hc l hl
      unfold tapeBase at this; omega
  · intro c hc
    simp only [rowCNF, List.mem_append, List.mem_flatMap, List.mem_range] at hc
    rcases hc with (hc | hc) | ⟨i, _, hc⟩
    · have := (oneHot_bounds base states).2 c hc; omega
    · have := (oneHot_bounds (base + states) width).2 c hc; omega
    · have := (oneHot_bounds (tapeBase base states width i) 4).2 c hc; omega

theorem instructionRules_length (m : Machine) (base next width q h s : Nat) :
    (instructionRules m base next width q h s).length ≤ 4 * width + 2 := by
  have hcopy (prem : Clause) (write : Symbol) :
      (copyRules prem base next m.program.length width h write).length ≤ 4 * width := by
    have hb := flatMap_length_le (List.range width)
      (fun i => (List.range 4).map fun t => implies
        (prem ++ [⟨tapeVar base m.program.length width i t, true⟩])
        [⟨tapeVar next m.program.length width i (if i = h then write.index else t), true⟩]) 4
        (by intro i _; simp)
    simpa [copyRules, Nat.mul_comm] using hb
  unfold instructionRules
  cases m.instruction q (symbolOfIndex s) with
  | halt b => simp
  | move target write dir =>
    simp only
    split
    · have := hcopy (guard base m.program.length width q h s) write
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp

theorem instructionRules_bounds (m : Machine) (base next width q h s : Nat)
    (hq : q < m.program.length) (hh : h < width) (hs : s < 4) :
    VarsBelow (max base next + m.program.length + 5 * width)
      (instructionRules m base next width q h s) ∧
      ∀ c ∈ instructionRules m base next width q h s, c.length ≤ 5 := by
  let bound := max base next + m.program.length + 5 * width
  have hb : base ≤ max base next := Nat.le_max_left ..
  have hn : next ≤ max base next := Nat.le_max_right ..
  have hg : ∀ l ∈ guard base m.program.length width q h s, l.var < bound := by
    intro l hl
    simp only [guard, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> dsimp [stateVar, headVar, tapeVar, tapeBase, bound] <;> omega
  have hcl (prem conclusion : Clause)
      (hp : ∀ l ∈ prem, l.var < bound) (ht : ∀ l ∈ conclusion, l.var < bound) :
      ∀ l ∈ implies prem conclusion, l.var < bound := by
    intro l hl
    simp only [implies, List.mem_append, List.mem_map] at hl
    rcases hl with ⟨v, hv, rfl⟩ | hl
    · exact hp v hv
    · exact ht l hl
  have hforbid : (∀ l ∈ implies (guard base m.program.length width q h s) [], l.var < bound) ∧
      (implies (guard base m.program.length width q h s) []).length ≤ 5 :=
    ⟨hcl _ _ hg (by simp), by simp [implies, guard]⟩
  unfold instructionRules
  cases m.instruction q (symbolOfIndex s) with
  | halt b => simpa [VarsBelow] using hforbid
  | move target write dir =>
    simp only
    split
    · rename_i hi
      have hh' := nextHead_lt width h dir hh hi.2
      have ht : (stateVar next target) < bound := by dsimp [stateVar, bound]; omega
      have hh'' : (headVar next m.program.length (nextHead h dir)) < bound := by
        dsimp [headVar, bound]; omega
      have hc : ∀ c ∈ copyRules (guard base m.program.length width q h s)
          base next m.program.length width h write,
          (∀ l ∈ c, l.var < bound) ∧ c.length ≤ 5 := by
        intro c hc
        simp only [copyRules, List.mem_flatMap, List.mem_map, List.mem_range] at hc
        obtain ⟨i, hi, t, hts, rfl⟩ := hc
        constructor
        · apply hcl
          · intro l hl
            rcases List.mem_append.mp hl with hl | hl
            · exact hg l hl
            · simp only [List.mem_singleton] at hl; subst l
              dsimp [tapeVar, tapeBase, bound]; omega
          · intro l hl
            simp only [List.mem_singleton] at hl; subst l
            have hw := symbolIndex_lt write
            dsimp [tapeVar, tapeBase, bound]
            split <;> omega
        · simp [implies, guard]
      constructor
      · intro c hc' l hl
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with (rfl | rfl) | hc'
        · exact hcl _ _ hg (by simpa using ht) l hl
        · exact hcl _ _ hg (by simpa using hh'') l hl
        · exact (hc c hc').1 l hl
      · intro c hc'
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with (rfl | rfl) | hc'
        · simp [implies, guard]
        · simp [implies, guard]
        · exact (hc c hc').2
    · simpa [VarsBelow] using hforbid

def successorCount (m : Machine) (width : Nat) : Nat :=
  2 * (m.program.length * m.program.length + width * width + 17 * width + 2) +
    4 * m.program.length * width * (4 * width + 2)
def successorSize (m : Machine) (base next width : Nat) : Nat :=
  2 * successorCount m width *
    (1 + (m.program.length + width + 6) * (max base next + m.program.length + 5 * width + 1))

theorem successorCNF_length (m : Machine) (base next width : Nat) :
    (successorCNF m base next width).length ≤ successorCount m width := by
  have hi q h : ((List.range 4).flatMap fun s => instructionRules m base next width q h s).length ≤
      4 * (4 * width + 2) := by
    exact flatMap_length_le _ _ _ (fun s _ => instructionRules_length m base next width q h s)
  have hh q := flatMap_length_le (List.range width)
    (fun h => (List.range 4).flatMap fun s => instructionRules m base next width q h s)
      (4 * (4 * width + 2)) (fun h _ => hi q h)
  have hq := flatMap_length_le (List.range m.program.length)
    (fun q => (List.range width).flatMap fun h => (List.range 4).flatMap fun s =>
      instructionRules m base next width q h s) (width * (4 * (4 * width + 2)))
      (fun q _ => by simpa using hh q)
  have ht : (transitionCNF m base next width).length ≤
      4 * m.program.length * width * (4 * width + 2) := by
    simpa [transitionCNF, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq
  have hr := rowCNF_length base m.program.length width
  have hr' := rowCNF_length next m.program.length width
  simp only [successorCNF, List.length_append, successorCount]
  omega

theorem successorCNF_bounds (m : Machine) (base next width : Nat) :
    VarsBelow (max base next + m.program.length + 5 * width) (successorCNF m base next width) ∧
      ∀ c ∈ successorCNF m base next width, c.length ≤ m.program.length + width + 6 := by
  have hb := rowCNF_bounds base m.program.length width
  have hn := rowCNF_bounds next m.program.length width
  have ht : ∀ c ∈ transitionCNF m base next width,
      (∀ l ∈ c, l.var < max base next + m.program.length + 5 * width) ∧ c.length ≤ 5 := by
    intro c hc
    simp only [transitionCNF, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨q, hq, h, hh, s, hs, hc⟩ := hc
    have hi := instructionRules_bounds m base next width q h s hq hh hs
    exact ⟨hi.1 c hc, hi.2 c hc⟩
  constructor
  · intro c hc l hl
    simp only [successorCNF, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have := hb.1 c hc l hl
      have := Nat.le_max_left base next; omega
    · have := hn.1 c hc l hl
      have := Nat.le_max_right base next; omega
    · exact (ht c hc).1 l hl
  · intro c hc
    simp only [successorCNF, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hb.2 c hc
    · exact hn.2 c hc
    · have := (ht c hc).2; omega

/-- Count unary variable identifiers, delimiters, and all copy constraints. -/
theorem successorCNF_encoded_size (m : Machine) (base next width : Nat) :
    (encodeCNF (successorCNF m base next width)).length ≤ successorSize m base next width := by
  have hb := successorCNF_bounds m base next width
  exact Nat.le_trans (cnf_encoded_size _ _ _ hb.1 hb.2)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (successorCNF_length m base next width)))

end Issue624.SuccessorCNF
