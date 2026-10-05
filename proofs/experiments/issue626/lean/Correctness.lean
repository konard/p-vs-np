import proofs.experiments.issue626.lean.Simulation

/-! Row encoding and NAND simulation correctness for the shared finite-table
machine. The final theorem packages the compiler into P ⊆ P/poly. -/

namespace Issue626.Simulation
open Complexity Issue532.Circuits Issue626.NandCompiler

def bit (s : Symbol) (lane : Nat) : Bool :=
  if lane = 0 then decide (s.index ≥ 2) else decide (s.index % 2 = 1)

def done : Bool ⊕ Config → Bool | .inl _ => true | .inr _ => false
def answer : Bool ⊕ Config → Bool | .inl b => b | .inr _ => false
def scanned : Bool ⊕ Config → Symbol | .inl _ => .blank | .inr c => c.head
def stateBit : Bool ⊕ Config → Nat → Bool
  | .inl _, _ => false | .inr c, q => decide (c.state = q)
def tape : Bool ⊕ Config → Bool → Nat → Symbol
  | .inl _, _, _ => .blank
  | .inr c, side, cell => (if side then c.right else c.left).getD cell .blank

/-- The row relation states the meaning of every stored bit, rather than
assuming that a supplied circuit simulates a machine. -/
structure Encodes (m : Machine) (cells : Nat) (x : List Bool)
    (r : List Expr) (c : Bool ⊕ Config) : Prop where
  doneBit : (ref r 0).eval x = done c
  answerBit : (ref r 1).eval x = answer c
  headBits : ∀ lane, lane < 2 → (ref r (2 + lane)).eval x = bit (scanned c) lane
  stateBits : ∀ q, q < m.program.length →
    (ref r (4 + q)).eval x = stateBit c q
  tapeBits : ∀ side cell lane, cell < cells → lane < 2 →
    (tapeRef m.program.length cells r side cell lane).eval x = bit (tape c side cell) lane

@[simp] theorem eval_symbolBit (x : List Bool) (s : Symbol) (lane : Nat) :
    (symbolBit s lane).eval x = bit s lane := rfl

@[simp] theorem eval_ref (x : List Bool) (r : List Expr) (i : Nat) :
    (ref r i).eval x = (r.map (Expr.eval x)).getD i false := by
  induction r generalizing i with
  | nil => rfl
  | cons a r ih => cases i with
    | zero => rfl
    | succ i => exact ih i

@[simp] theorem ref_range (x : List Bool) (f : Nat → Expr) (k i : Nat) (hi : i < k) :
    (ref ((List.range k).map f) i).eval x = (f i).eval x := by
  simp [ref, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem chooseSymbol_eval (m : Machine) (cells : Nat) (x : List Bool)
    (r : List Expr) (c : Bool ⊕ Config) (h : Encodes m cells x r c) (f : Symbol → Expr) :
    (chooseSymbol r f).eval x = (f (scanned c)).eval x := by
  have h0 := h.headBits 0 (by omega)
  have h1 := h.headBits 1 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at h0 h1
  simp only [chooseSymbol, eval_mux, h0, h1]
  cases c with
  | inl b => rfl
  | inr c => cases hs : c.head <;> simp [scanned, hs, bit, Symbol.index]

/-- Table lookup defaults to reject for a missing state or symbol column. -/
theorem instruction_getD (m : Machine) (q : Nat) (s : Symbol) :
    m.instruction q s = (m.program.getD q []).getD s.index (.halt false) := by
  simp only [Machine.instruction, List.getD_eq_getElem?_getD]
  cases m.program[q]? <;> simp

theorem chooseState_eval (m : Machine) (cells : Nat) (x : List Bool)
    (r : List Expr) (c : Config) (h : Encodes m cells x r (.inr c))
    (f : Instruction → Expr) (q : Nat) (rows : List (List Instruction))
    (hlen : q + rows.length ≤ m.program.length) (hq : q ≤ c.state) :
    (chooseState m r f q rows).eval x =
      (f ((rows.getD (c.state - q) []).getD c.head.index (.halt false))).eval x := by
  induction rows generalizing q with
  | nil => simp [chooseState]
  | cons row rows ih =>
      have hb := h.stateBits q (by simp at hlen; omega)
      simp only [stateBit] at hb
      simp only [chooseState, eval_mux, hb]
      by_cases he : c.state = q
      · simp only [he, decide_true, ↓reduceIte, Nat.sub_self, List.getD_cons_zero]
        exact chooseSymbol_eval m cells x r (.inr c) h _
      · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hs : c.state - q = (c.state - (q + 1)) + 1 := by omega
        rw [hs, List.getD_cons_succ]
        exact ih (q + 1) (by simp at hlen; omega) (by omega)

theorem chosen_instruction_eval (m : Machine) (cells : Nat) (x : List Bool)
    (r : List Expr) (c : Config) (h : Encodes m cells x r (.inr c))
    (f : Instruction → Expr) :
    (chooseState m r f 0 m.program).eval x = (f (m.instruction c.state c.head)).eval x := by
  rw [chooseState_eval m cells x r c h f 0 m.program (by omega) (Nat.zero_le _)]
  simp [instruction_getD]

theorem pad_getD (k : Nat) (l : List Symbol) (i : Nat) (hi : i < k) :
    (Window.pad k l).getD i .blank = l.getD i .blank := by
  induction k generalizing l i with
  | zero => omega
  | succ k ih =>
      cases l <;> cases i <;> simp only [Window.pad, List.getD_cons_zero,
        List.getD_cons_succ, List.getD_nil]
      · exact ih [] _ (by omega)
      · exact ih _ _ (by omega)

theorem tape_window (k : Nat) (c : Config) (side : Bool) (i : Nat) (hi : i < k) :
    tape (.inr (Window.window k c)) side i = tape (.inr c) side i := by
  cases side <;> exact pad_getD k _ i hi

theorem moved_head (c : Config) (q : Nat) (s : Symbol) (d : Direction) :
    (moveHead c q s d).head = match d with
      | .stay => s | .left => c.left.getD 0 .blank | .right => c.right.getD 0 .blank := by
  cases c with
  | mk st l hd r => cases d <;> cases l <;> cases r <;> rfl

theorem moved_tape (c : Config) (q : Nat) (s : Symbol) (d : Direction)
    (side : Bool) (cell : Nat) :
    tape (.inr (moveHead c q s d)) side cell =
      match d, side with
      | .stay, _ => tape (.inr c) side cell
      | .left, false | .right, true => tape (.inr c) side (cell + 1)
      | .right, false | .left, true =>
          if cell = 0 then s else tape (.inr c) side (cell - 1) := by
  cases c with
  | mk st l hd r =>
      cases d <;> cases side <;> cases l <;> cases r <;> cases cell <;>
        simp [tape, moveHead]

theorem moved_state (c : Config) (q : Nat) (s : Symbol) (d : Direction) :
    (moveHead c q s d).state = q := by
  cases c with
  | mk st l hd r => cases d <;> cases l <;> cases r <;> rfl

def rowExpr (m : Machine) (cells : Nat) (r : List Expr) (i : Nat) : Expr :=
  (ref r 0).mux (if i = 0 then .lit true else if i = 1 then ref r 1 else .lit false)
    (chooseState m r (instructionBit m cells r i) 0 m.program)

theorem row_live (m : Machine) (cells : Nat) (x : List Bool) (r : List Expr)
    (c : Config) (h : Encodes m cells x r (.inr c)) (i : Nat) :
    (rowExpr m cells r i).eval x =
      (instructionBit m cells r i (m.instruction c.state c.head)).eval x := by
  simp only [rowExpr, eval_mux, h.doneBit, done, Bool.false_eq_true, ↓reduceIte]
  exact chosen_instruction_eval m cells x r c h _

theorem step_ref (m : Machine) (cells : Nat) (x : List Bool) (r : List Expr)
    (i : Nat) (hi : i < width m.program.length (cells - 1)) :
    (ref (stepExprs m cells r) i).eval x = (rowExpr m cells r i).eval x :=
  ref_range x _ _ i hi

theorem rowIndex_lt (states cells : Nat) (side : Bool) (cell lane : Nat)
    (hc : cell < cells) (hl : lane < 2) :
    4 + states + (if side then 2 * cells else 0) + 2 * cell + lane < width states cells := by
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> unfold width <;> omega

theorem moved_tape_eval (m : Machine) (cells : Nat) (x : List Bool) (r : List Expr)
    (c : Config) (h : Encodes m cells x r (.inr c)) (side : Bool) (cell lane q : Nat)
    (s : Symbol) (d : Direction) (hc : cell < cells - 1) (hl : lane < 2) :
    (movedBit m cells r
      (4 + m.program.length + (if side then 2 * (cells - 1) else 0) + 2 * cell + lane)
      q s d).eval x = bit (tape (.inr (moveHead c q s d)) side cell) lane := by
  let i := 4 + m.program.length + (if side then 2 * (cells - 1) else 0) + 2 * cell + lane
  have h0 : i ≠ 0 := by dsimp [i]; split <;> omega
  have h1 : i ≠ 1 := by dsimp [i]; split <;> omega
  have h4 : ¬i < 4 := by dsimp [i]; split <;> omega
  have hq : ¬i < 4 + m.program.length := by dsimp [i]; split <;> omega
  have hside : decide (i - (4 + m.program.length) ≥ 2 * (cells - 1)) = side := by
    cases side <;> dsimp [i] <;> simp <;> omega
  have hoff : (if side then i - (4 + m.program.length) - 2 * (cells - 1)
    else i - (4 + m.program.length)) = 2 * cell + lane := by
    cases side <;> dsimp [i] <;> omega
  have hdiv : (2 * cell + lane) / 2 = cell := by omega
  have hmod : (2 * cell + lane) % 2 = lane := by omega
  change (movedBit m cells r i q s d).eval x = _
  simp only [movedBit, h0, h1, h4, hq, ↓reduceIte, hside, hoff, hdiv, hmod]
  rw [moved_tape]
  cases d <;> cases side
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals first
    | exact h.tapeBits _ _ _ (by omega) hl
    | split
      · rfl
      · exact h.tapeBits _ _ _ (by omega) hl

theorem step_encodes (m : Machine) (cells : Nat) (x : List Bool) (r : List Expr)
    (c : Bool ⊕ Config) (h : Encodes m cells x r c) (hk : 0 < cells) :
    Encodes m (cells - 1) x (stepExprs m cells r) (Window.next m (cells - 1) c) := by
  cases c with
  | inl b =>
      have hev : ∀ i, (rowExpr m cells r i).eval x =
        if i = 0 then true else if i = 1 then b else false := by
        intro i
        by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
          simp [rowExpr, eval_mux, h.doneBit, done, h0, h1, h.answerBit, answer, Expr.eval]
      constructor
      · rw [step_ref _ _ _ _ _ (by unfold width; omega), hev]; rfl
      · rw [step_ref _ _ _ _ _ (by unfold width; omega), hev]; rfl
      · intro lane hl
        rw [step_ref _ _ _ _ _ (by unfold width; omega), hev]
        simp [Window.next, scanned, bit, Symbol.index]; omega
      · intro q hq
        rw [step_ref _ _ _ _ _ (by unfold width; omega), hev]
        simp [Window.next, stateBit]; omega
      · intro side cell lane hc hl
        unfold tapeRef
        rw [step_ref _ _ _ _ _ (rowIndex_lt _ _ _ _ _ hc hl), hev]
        cases side <;> simp [Window.next, tape, bit, Symbol.index] <;> omega
  | inr c =>
      have hstep : Window.next m (cells - 1) (.inr c) =
        match m.instruction c.state c.head with
        | .halt b => .inl b
        | .move q s d => .inr (Window.window (cells - 1) (moveHead c q s d)) := by
          simp only [Window.next, step]
          cases m.instruction c.state c.head <;> rfl
      constructor
      · rw [step_ref _ _ _ _ _ (by unfold width; omega), row_live _ _ _ _ _ h, hstep]
        cases m.instruction c.state c.head <;> rfl
      · rw [step_ref _ _ _ _ _ (by unfold width; omega), row_live _ _ _ _ _ h, hstep]
        cases m.instruction c.state c.head <;> rfl
      · intro lane hl
        rw [step_ref _ _ _ _ _ (by unfold width; omega), row_live _ _ _ _ _ h, hstep]
        cases hi : m.instruction c.state c.head with
        | halt b =>
            have h0 : 2 + lane ≠ 0 := by omega
            have h1 : 2 + lane ≠ 1 := by omega
            simp [instructionBit, scanned, bit, Symbol.index, h0, h1, Expr.eval]
        | move q s d =>
            have h0 : 2 + lane ≠ 0 := by omega
            have h1 : 2 + lane ≠ 1 := by omega
            have h4 : 2 + lane < 4 := by omega
            simp only [instructionBit, movedBit, h0, h1, h4, ↓reduceIte]
            change (match d with
              | .stay => symbolBit s (2 + lane - 2)
              | .left => tapeRef m.program.length cells r false 0 (2 + lane - 2)
              | .right => tapeRef m.program.length cells r true 0 (2 + lane - 2)).eval x =
              bit (moveHead c q s d).head lane
            rw [moved_head]
            have hsub : 2 + lane - 2 = lane := by omega
            rw [hsub]
            cases d
            · exact h.tapeBits false 0 lane hk hl
            · exact h.tapeBits true 0 lane hk hl
            · rfl
      · intro q hq
        rw [step_ref _ _ _ _ _ (by unfold width; omega), row_live _ _ _ _ _ h, hstep]
        cases hi : m.instruction c.state c.head with
        | halt b =>
            have h0 : 4 + q ≠ 0 := by omega
            have h1 : 4 + q ≠ 1 := by omega
            simp [instructionBit, stateBit, h0, h1, Expr.eval]
        | move q' s d =>
            have h0 : 4 + q ≠ 0 := by omega
            have h1 : 4 + q ≠ 1 := by omega
            have h4 : ¬4 + q < 4 := by omega
            have hM : 4 + q < 4 + m.program.length := by omega
            simp only [instructionBit, movedBit, h0, h1, h4, hM, ↓reduceIte, Expr.eval,
              stateBit, Window.window]
            simp [moved_state, eq_comm]
      · intro side cell lane hc hl
        unfold tapeRef
        rw [step_ref _ _ _ _ _ (rowIndex_lt _ _ _ _ _ hc hl),
          row_live _ _ _ _ _ h, hstep]
        cases hi : m.instruction c.state c.head with
        | halt b =>
            have h0 : 4 + m.program.length + (if side then 2 * (cells - 1) else 0) +
              2 * cell + lane ≠ 0 := by split <;> omega
            have h1 : 4 + m.program.length + (if side then 2 * (cells - 1) else 0) +
              2 * cell + lane ≠ 1 := by split <;> omega
            simp [instructionBit, tape, bit, Symbol.index, h0, h1, Expr.eval]
        | move q s d =>
            rw [instructionBit, moved_tape_eval _ _ _ _ _ h side cell lane q s d hc hl]
            rw [tape_window _ _ _ _ hc]

theorem getD_map_bounded {α β : Type} (l : List α) (f : α → β)
    (i : Nat) (da : α) (db : β) (hi : i < l.length) :
    (l.map f).getD i db = f (l.getD i da) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at hi; omega)

theorem getD_ge {α : Type} (l : List α) (i : Nat) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => cases i with
    | zero => simp at hi
    | succ i => exact ih i (by simp at hi; omega)

theorem inputSymbolBit_eval (x : List Bool) (cell lane : Nat) :
    (inputSymbolBit x.length cell lane).eval x =
      bit ((x.map Symbol.ofBool).getD cell .blank) lane := by
  unfold inputSymbolBit
  split
  · rename_i hc
    rw [getD_map_bounded x Symbol.ofBool cell false .blank hc]
    by_cases hl : lane = 0
    · simp only [hl, ↓reduceIte, Expr.eval]
      change wire x cell = bit (Symbol.ofBool (wire x cell)) 0
      cases wire x cell <;> rfl
    · simp only [hl, ↓reduceIte, Expr.neg, Expr.eval]
      change (!(wire x cell && wire x cell)) = bit (Symbol.ofBool (wire x cell)) lane
      cases wire x cell <;> simp [Symbol.ofBool, bit, Symbol.index, hl]
  · rename_i hc
    rw [getD_ge (x.map Symbol.ofBool) cell .blank (by simp; omega)]
    simp [Expr.eval, bit, Symbol.index]

theorem initial_head (x : Word) : (initial x).head = (x.map Symbol.ofBool).getD 0 .blank := by
  cases x <;> rfl

theorem initial_tape (x : Word) (side : Bool) (cell : Nat) :
    tape (.inr (initial x)) side cell =
      if side then (x.map Symbol.ofBool).getD (cell + 1) .blank else .blank := by
  cases side <;> cases x <;> rfl

theorem encodes_window (m : Machine) (cells : Nat) (x : List Bool) (r : List Expr)
    (c : Config) (h : Encodes m cells x r (.inr c)) :
    Encodes m cells x r (.inr (Window.window cells c)) := by
  refine ⟨h.doneBit, h.answerBit, h.headBits, h.stateBits, ?_⟩
  intro side cell lane hc hl
  rw [tape_window _ _ _ _ hc]
  exact h.tapeBits side cell lane hc hl

theorem initial_encodes (m : Machine) (cells : Nat) (x : Word) :
    Encodes m cells x (initialExprs m x.length cells) (.inr (initial x)) := by
  have hr : ∀ i, i < width m.program.length cells →
    (ref (initialExprs m x.length cells) i).eval x =
      (if i < 2 then Expr.lit false
      else if i < 4 then inputSymbolBit x.length 0 (i - 2)
      else if i < 4 + m.program.length then Expr.lit (i = 4)
      else let j := i - (4 + m.program.length)
        if j < 2 * cells then Expr.lit false
        else inputSymbolBit x.length ((j - 2 * cells) / 2 + 1) ((j - 2 * cells) % 2)).eval x := by
    intro i hi
    exact ref_range x _ _ i hi
  constructor
  · rw [hr 0 (by unfold width; omega)]; rfl
  · rw [hr 1 (by unfold width; omega)]; rfl
  · intro lane hl
    rw [hr (2 + lane) (by unfold width; omega)]
    have h2 : ¬2 + lane < 2 := by omega
    have h4 : 2 + lane < 4 := by omega
    simp only [h2, h4, ↓reduceIte]
    rw [inputSymbolBit_eval]
    simp [scanned, initial_head]
  · intro q hq
    rw [hr (4 + q) (by unfold width; omega)]
    have h2 : ¬4 + q < 2 := by omega
    have h4 : ¬4 + q < 4 := by omega
    have hM : 4 + q < 4 + m.program.length := by omega
    simp only [h2, h4, hM, ↓reduceIte, Expr.eval, stateBit]
    cases x <;> simp [initial, initialSymbols, eq_comm]
  · intro side cell lane hc hl
    unfold tapeRef
    rw [hr _ (rowIndex_lt _ _ _ _ _ hc hl), initial_tape]
    have hdiv : (2 * cell + lane) / 2 = cell := by omega
    have hmod : (2 * cell + lane) % 2 = lane := by omega
    cases side
    · have h2 : ¬4 + m.program.length + 0 + 2 * cell + lane < 2 := by omega
      have h4 : ¬4 + m.program.length + 0 + 2 * cell + lane < 4 := by omega
      have hM : ¬4 + m.program.length + 0 + 2 * cell + lane < 4 + m.program.length := by omega
      have hj : 4 + m.program.length + 0 + 2 * cell + lane - (4 + m.program.length) =
        2 * cell + lane := by omega
      have hspan : 2 * cell + lane < 2 * cells := by omega
      simp only [Nat.add_zero] at h2 h4 hM hj
      simp [h2, h4, hM, hj, hspan, Expr.eval, bit, Symbol.index]
    · have h2 : ¬4 + m.program.length + 2 * cells + 2 * cell + lane < 2 := by omega
      have h4 : ¬4 + m.program.length + 2 * cells + 2 * cell + lane < 4 := by omega
      have hM : ¬4 + m.program.length + 2 * cells + 2 * cell + lane < 4 + m.program.length := by omega
      have hj : 4 + m.program.length + 2 * cells + 2 * cell + lane - (4 + m.program.length) =
        2 * cells + (2 * cell + lane) := by omega
      have hspan : ¬2 * cells + (2 * cell + lane) < 2 * cells := by omega
      have hoff : 2 * cells + (2 * cell + lane) - 2 * cells = 2 * cell + lane := by omega
      simp only [↓reduceIte, h2, h4, hM, hj, hspan, hoff, hdiv, hmod]
      exact inputSymbolBit_eval x (cell + 1) lane

theorem compileMany_encodes (m : Machine) (cells : Nat) (x : List Bool) (es : List Expr)
    (c : Bool ⊕ Config) (hx : 0 < x.length) (hb : ∀ a ∈ es, a.Bounded x.length)
    (h : Encodes m cells x es c) :
    Encodes m cells (wires x (compileMany x.length es).1)
      ((compileMany x.length es).2.map Expr.input) c := by
  have he := compileMany_correct x es hx hb
  have hr : ∀ i,
    (ref ((compileMany x.length es).2.map Expr.input) i).eval
      (wires x (compileMany x.length es).1) = (ref es i).eval x := by
    intro i
    simp only [eval_ref, List.map_map, Function.comp_def, Expr.eval, he]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact h.doneBit
  · rw [hr]; exact h.answerBit
  · intro lane hl; rw [hr]; exact h.headBits lane hl
  · intro q hq; rw [hr]; exact h.stateBits q hq
  · intro side cell lane hc hl
    unfold tapeRef
    rw [hr]; exact h.tapeBits side cell lane hc hl

theorem finish_correct (x : List Bool) (refs : List Nat) :
    output x (finish x.length refs) = wire x (refs.getD 1 0) := by
  simp only [finish, output, wires]
  rw [wire_append_self]
  cases wire x (refs.getD 1 0) <;> simp

/-- Composition follows the window rows, carrying both wire bounds and the
meaning of the answer bit. No run or language is an argument of the compiler. -/
theorem compileRows_correct (m : Machine) (t cells : Nat) (x : List Bool) (refs : List Nat)
    (c : Bool ⊕ Config) (hx : 0 < x.length) (hw : ∀ i ∈ refs, i < x.length)
    (hlen : 2 ≤ refs.length) (ht : t ≤ cells)
    (h : Encodes m cells x (refs.map Expr.input) c) :
    output x (compileRows m t cells x.length refs) = answer (Window.runWindow m t cells c) := by
  induction t generalizing cells x refs c with
  | zero =>
      rw [compileRows, finish_correct]
      have ha := h.answerBit
      rw [eval_ref, List.map_map] at ha
      change (refs.map (wire x)).getD 1 false = answer c at ha
      rw [getD_map_bounded refs (wire x) 1 0 false (by omega)] at ha
      exact ha
  | succ t ih =>
      let es := stepExprs m cells (refs.map Expr.input)
      let A := (compileMany x.length es).1
      let js := (compileMany x.length es).2
      let y := wires x A
      have hy : y.length = x.length + A.length := wires_length x A
      have hb : ∀ e ∈ es, e.Bounded x.length := stepExprs_bounded _ _ _ _ (by
        intro e he
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
        exact hw i hi)
      have hn : 0 < cells := by omega
      have hc := step_encodes m cells x (refs.map Expr.input) c h hn
      have hr := compileMany_encodes m (cells - 1) x es (Window.next m (cells - 1) c) hx hb hc
      have hj := (compileMany_WF x.length es hx hb).2
      have hjlen : 2 ≤ js.length := by
        rw [show js.length = es.length from compileMany_outputs_length _ _]
        simp only [es, stepExprs, List.length_map, List.length_range, width]
        omega
      have he := ih (cells - 1) y js (Window.next m (cells - 1) c)
        (by omega) (by simpa [hy, js, A] using hj) hjlen (by omega) hr
      change output x (A ++ compileRows m t (cells - 1) (x.length + A.length) js) = _
      simp only [output, wires_append]
      rw [← hy]
      exact he

/-- The actual circuit follows every run that halts within its polynomial
clock; extra clock rows preserve an early answer. -/
theorem simCircuit_correct (m : Machine) (p : Polynomial) (x : Word)
    (hx : 0 < x.length) (t : Nat) (b : Bool)
    (hr : Run m (initial x) t b) (ht : t ≤ p.eval x.length) :
    output x (simCircuit m p x.length) = b := by
  let clock := p.eval x.length
  let cells := x.length + clock + 1
  let es := initialExprs m x.length cells
  let A := (compileMany x.length es).1
  let js := (compileMany x.length es).2
  let y := wires x A
  have hy : y.length = x.length + A.length := wires_length x A
  have hb := initialExprs_bounded m x.length cells
  have hi := encodes_window m cells x es (initial x) (initial_encodes m cells x)
  have hj := (compileMany_WF x.length es hx hb).2
  have hc := compileMany_encodes m cells x es (.inr (Window.window cells (initial x))) hx hb hi
  have hl : 2 ≤ js.length := by
    rw [show js.length = es.length from compileMany_outputs_length _ _]
    simp only [es, initialExprs, List.length_map, List.length_range, width]
    omega
  have he := compileRows_correct m clock cells y js (.inr (Window.window cells (initial x)))
    (by omega) (by simpa [hy, js, A] using hj) hl (by dsimp [cells]; omega) hc
  have hrun := Window.runWindow_correct hr clock cells ht (by dsimp [cells]; omega)
  rw [hrun] at he
  change output x (A ++ compileRows m clock cells (x.length + A.length) js) = b
  simp only [output, wires_append]
  rw [← hy]
  exact he

/-- The shared local tableau certifies the same circuit answer, and its
configurations fit the cell budget used by the compiler. -/
theorem simCircuit_correct_of_localTrace (m : Machine) (p : Polynomial) (x : Word)
    (trace : List Config) (b : Bool) (hx : 0 < x.length)
    (hstart : trace.head? = some (initial x)) (ht : trace.length ≤ p.eval x.length)
    (hlocal : Issue568.Tableau.LocalTrace m b trace) :
    output x (simCircuit m p x.length) = b ∧
      ∀ d ∈ trace, Issue568.Tableau.span d ≤ x.length + p.eval x.length + 1 := by
  have hr := (Issue568.Tableau.localTrace_iff_run m (initial x) trace.length b).mp
    ⟨trace, hstart, rfl, hlocal⟩
  exact ⟨simCircuit_correct m p x hx trace.length b hr ht,
    fun d hd => Issue568.Tableau.bounded_initial_span m x (p.eval x.length) b
      trace hstart ht hlocal d hd⟩

theorem machine_inPPoly (P : ClassP) : InPPoly P.language := by
  refine ⟨simulationPolynomial P.machine P.bound, fun n hn => ?_⟩
  refine ⟨simCircuit P.machine P.bound n, simCircuit_polynomial_size _ _ _, simCircuit_WF _ _ _ hn, ?_⟩
  intro x hx
  obtain ⟨t, b, ht, hr⟩ := P.terminates x
  subst n
  have ho := simCircuit_correct P.machine P.bound x hn t b hr ht
  rw [ho]
  have he := P.correct x t b hr
  cases hb : b <;> cases hl : P.language x <;> simp_all

theorem pSubsetPPoly : PSubsetPPoly := by
  intro L hL
  obtain ⟨P, rfl⟩ := hL
  exact machine_inPPoly P

end Issue626.Simulation
