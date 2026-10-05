import proofs.experiments.issue626.lean.NandCompiler
import proofs.experiments.issue626.lean.Window

/-! The executable bounded NAND compiler, with wire and polynomial-size proofs.
`Correctness.lean` proves that its encoded rows follow the shared `Run`
semantics and derives P ⊆ P/poly. -/

namespace Issue626.Simulation
open Complexity Issue532.Circuits Issue626.NandCompiler

/-- Two bits for a symbol: blank=00, zero=01, one=10, separator=11. -/
def symbolBit (s : Symbol) (lane : Nat) : Expr :=
  .lit (if lane = 0 then s.index ≥ 2 else s.index % 2 = 1)

def width (states cells : Nat) : Nat := 4 + states + 4 * cells

/-- Layout: done, answer, two head bits, one-hot state bits, then pairs
for the left stack and the right stack (nearest cells first). -/
def ref (r : List Expr) (i : Nat) : Expr := r.getD i (.lit false)

def tapeRef (states cells : Nat) (r : List Expr) (right : Bool)
    (cell lane : Nat) : Expr :=
  ref r (4 + states + (if right then 2 * cells else 0) + 2 * cell + lane)

def chooseSymbol (r : List Expr) (f : Symbol → Expr) : Expr :=
  (ref r 2).mux ((ref r 3).mux (f .separator) (f .one))
    ((ref r 3).mux (f .zero) (f .blank))

def chooseState (m : Machine) (r : List Expr) (f : Instruction → Expr)
    (q : Nat) : List (List Instruction) → Expr
  | [] => f (.halt false)
  | row :: rows => (ref r (4 + q)).mux
      (chooseSymbol r (fun s => f (row.getD s.index (.halt false))))
      (chooseState m r f (q + 1) rows)

def movedBit (m : Machine) (cells : Nat) (r : List Expr) (i q : Nat)
    (s : Symbol) (d : Direction) : Expr :=
  if i = 0 then .lit false
  else if i = 1 then .lit false
  else if i < 4 then
    match d with
    | .stay => symbolBit s (i - 2)
    | .left => tapeRef m.program.length cells r false 0 (i - 2)
    | .right => tapeRef m.program.length cells r true 0 (i - 2)
  else if i < 4 + m.program.length then .lit (i - 4 = q)
  else
    let j := i - (4 + m.program.length)
    let right := decide (j ≥ 2 * (cells - 1))
    let off := if right then j - 2 * (cells - 1) else j
    let cell := off / 2
    let lane := off % 2
    match d, right with
    | .stay, _ => tapeRef m.program.length cells r right cell lane
    | .left, false | .right, true =>
        tapeRef m.program.length cells r right (cell + 1) lane
    | .right, false | .left, true =>
        if cell = 0 then symbolBit s lane
        else tapeRef m.program.length cells r right (cell - 1) lane

def instructionBit (m : Machine) (cells : Nat) (r : List Expr) (i : Nat) :
    Instruction → Expr
  | .halt b => .lit (if i = 0 then true else if i = 1 then b else false)
  | .move q s d => movedBit m cells r i q s d

def stepExprs (m : Machine) (cells : Nat) (r : List Expr) : List Expr :=
  (List.range (width m.program.length (cells - 1))).map fun i =>
    (ref r 0).mux (if i = 0 then .lit true else if i = 1 then ref r 1 else .lit false)
      (chooseState m r (instructionBit m cells r i) 0 m.program)

def inputSymbolBit (n cell lane : Nat) : Expr :=
  if cell < n then
    if lane = 0 then .input cell else (Expr.input cell).neg
  else .lit false

def initialExprs (m : Machine) (n cells : Nat) : List Expr :=
  (List.range (width m.program.length cells)).map fun i =>
    if i < 2 then .lit false
    else if i < 4 then inputSymbolBit n 0 (i - 2)
    else if i < 4 + m.program.length then .lit (i = 4)
    else
      let j := i - (4 + m.program.length)
      if j < 2 * cells then .lit false
      else inputSymbolBit n ((j - 2 * cells) / 2 + 1) ((j - 2 * cells) % 2)

/-- Append a double negation so the answer wire becomes the last wire. -/
def finish (n : Nat) (refs : List Nat) : Circuit :=
  let a := refs.getD 1 0
  [(a, a), (n, n)]

def compileRows (m : Machine) : Nat → Nat → Nat → List Nat → Circuit
  | 0, _, n, refs => finish n refs
  | t + 1, cells, n, refs =>
      let (A, js) := compileMany n (stepExprs m cells (refs.map Expr.input))
      A ++ compileRows m t (cells - 1) (n + A.length) js

/-- Only machine data, its clock polynomial and input length are compiler
inputs. The actual input bits remain the first `n` wires of the circuit. -/
def simCircuit (m : Machine) (p : Polynomial) (n : Nat) : Circuit :=
  let clock := p.eval n
  let cells := n + clock + 1
  let (A, js) := compileMany n (initialExprs m n cells)
  A ++ compileRows m clock cells (n + A.length) js

theorem ref_bounded (r : List Expr) (n : Nat) (hr : ∀ e ∈ r, e.Bounded n) (i : Nat) :
    (ref r i).Bounded n := by
  unfold ref
  rw [List.getD_eq_getElem?_getD]
  cases hi : r[i]? with
  | none => trivial
  | some e => exact hr e (List.mem_of_getElem? hi)

theorem mux_bounded (s a b : Expr) (n : Nat)
    (hs : s.Bounded n) (ha : a.Bounded n) (hb : b.Bounded n) :
    (s.mux a b).Bounded n := by
  simp only [Expr.mux, Expr.neg, Expr.Bounded]
  exact ⟨⟨hs, ha⟩, ⟨⟨hs, hs⟩, hb⟩⟩

theorem chooseSymbol_bounded (r : List Expr) (n : Nat) (f : Symbol → Expr)
    (hr : ∀ e ∈ r, e.Bounded n) (hf : ∀ s, (f s).Bounded n) :
    (chooseSymbol r f).Bounded n := by
  apply mux_bounded _ _ _ n (ref_bounded _ _ hr _)
  · exact mux_bounded _ _ _ n (ref_bounded _ _ hr _) (hf _) (hf _)
  · exact mux_bounded _ _ _ n (ref_bounded _ _ hr _) (hf _) (hf _)

theorem chooseState_bounded (m : Machine) (r : List Expr) (n : Nat)
    (f : Instruction → Expr) (hr : ∀ e ∈ r, e.Bounded n)
    (hf : ∀ s, (f s).Bounded n) (q : Nat) (rows : List (List Instruction)) :
    (chooseState m r f q rows).Bounded n := by
  induction rows generalizing q with
  | nil => exact hf _
  | cons row rows ih =>
      exact mux_bounded _ _ _ n (ref_bounded _ _ hr _)
        (chooseSymbol_bounded _ _ _ hr (fun _ => hf _)) (ih _)

theorem movedBit_bounded (m : Machine) (cells : Nat) (r : List Expr) (n : Nat)
    (hr : ∀ e ∈ r, e.Bounded n) (i q : Nat) (s : Symbol) (d : Direction) :
    (movedBit m cells r i q s d).Bounded n := by
  have ht : ∀ right cell lane, (tapeRef m.program.length cells r right cell lane).Bounded n :=
    fun _ _ _ => ref_bounded r n hr _
  unfold movedBit
  split <;> try trivial
  split <;> try trivial
  split
  · cases d <;> first | trivial | exact ht _ _ _
  · split <;> try trivial
    cases d <;> cases h : decide (i - (4 + m.program.length) ≥ 2 * (cells - 1)) <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat first | trivial | exact ht _ _ _ | split

theorem stepExprs_bounded (m : Machine) (cells : Nat) (r : List Expr) (n : Nat)
    (hr : ∀ e ∈ r, e.Bounded n) :
    ∀ e ∈ stepExprs m cells r, e.Bounded n := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  apply mux_bounded _ _ _ n (ref_bounded _ _ hr _)
  · split <;> first | trivial | split <;> first | exact ref_bounded _ _ hr _ | trivial
  · apply chooseState_bounded _ _ _ _ hr
    intro instr
    cases instr with
    | halt b => trivial
    | move q s d => exact movedBit_bounded _ _ _ _ hr _ _ _ _

theorem initialExprs_bounded (m : Machine) (n cells : Nat) :
    ∀ e ∈ initialExprs m n cells, e.Bounded n := by
  have hi : ∀ cell lane, (inputSymbolBit n cell lane).Bounded n := by
    intro cell lane
    unfold inputSymbolBit
    split
    · split
      · assumption
      · exact ⟨by assumption, by assumption⟩
    · trivial
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  simp only
  split <;> try trivial
  split <;> try exact hi _ _
  split <;> try trivial
  split <;> first | trivial | exact hi _ _

theorem getD_lt (refs : List Nat) (n : Nat) (hn : 0 < n)
    (hr : ∀ i ∈ refs, i < n) (j : Nat) : refs.getD j 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : refs[j]? with
  | none => exact hn
  | some i => exact hr i (List.mem_of_getElem? hi)

theorem compileRows_WF (m : Machine) (t cells n : Nat) (refs : List Nat)
    (hn : 0 < n) (hr : ∀ i ∈ refs, i < n) : WFfrom n (compileRows m t cells n refs) := by
  induction t generalizing cells n refs with
  | zero =>
      have hi := getD_lt refs n hn hr 1
      simp only [compileRows, finish, WFfrom]
      exact ⟨hi, hi, by omega, by omega, trivial⟩
  | succ t ih =>
      have he : ∀ e ∈ refs.map Expr.input, e.Bounded n := by
        intro e he; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he; exact hr i hi
      obtain ⟨hw, hj⟩ := compileMany_WF n _ hn (stepExprs_bounded m cells _ n he)
      exact (WFfrom_append _ _ _).mpr ⟨hw, ih _ _ _ (by omega) hj⟩

theorem simCircuit_WF (m : Machine) (p : Polynomial) (n : Nat) (hn : 0 < n) :
    WF n (simCircuit m p n) := by
  obtain ⟨hw, hj⟩ := compileMany_WF n _ hn (initialExprs_bounded m n (n + p.eval n + 1))
  exact (WFfrom_append _ _ _).mpr ⟨hw, compileRows_WF m _ _ _ _ (by omega) hj⟩

theorem lit_cost_le (b : Bool) : (Expr.lit b).cost ≤ 3 := by cases b <;> decide

theorem ref_cost_le (r : List Expr) (hr : ∀ e ∈ r, e.cost ≤ 3) (i : Nat) :
    (ref r i).cost ≤ 3 := by
  unfold ref
  rw [List.getD_eq_getElem?_getD]
  cases hi : r[i]? with
  | none => decide
  | some e => exact hr e (List.mem_of_getElem? hi)

theorem mux_cost (s a b : Expr) :
    (s.mux a b).cost = 3 * s.cost + a.cost + b.cost + 4 := by
  simp only [Expr.mux, Expr.neg, Expr.cost]; omega

theorem chooseSymbol_cost (r : List Expr) (f : Symbol → Expr)
    (hr : ∀ e ∈ r, e.cost ≤ 3) (hf : ∀ s, (f s).cost ≤ 3) :
    (chooseSymbol r f).cost ≤ 51 := by
  simp only [chooseSymbol, mux_cost]
  have := ref_cost_le r hr 2
  have := ref_cost_le r hr 3
  have := hf .separator
  have := hf .one
  have := hf .zero
  have := hf .blank
  omega

theorem chooseState_cost (m : Machine) (r : List Expr) (f : Instruction → Expr)
    (hr : ∀ e ∈ r, e.cost ≤ 3) (hf : ∀ s, (f s).cost ≤ 3)
    (q : Nat) (rows : List (List Instruction)) :
    (chooseState m r f q rows).cost ≤ 64 * rows.length + 3 := by
  induction rows generalizing q with
  | nil => exact hf _
  | cons row rows ih =>
      have := ih (q + 1)
      have := ref_cost_le r hr (4 + q)
      have := chooseSymbol_cost r (fun s => f (row.getD s.index (.halt false))) hr (fun _ => hf _)
      simp only [chooseState, mux_cost, List.length_cons]
      omega

theorem movedBit_cost (m : Machine) (cells : Nat) (r : List Expr)
    (hr : ∀ e ∈ r, e.cost ≤ 3) (i q : Nat) (s : Symbol) (d : Direction) :
    (movedBit m cells r i q s d).cost ≤ 3 := by
  have ht : ∀ right cell lane, (tapeRef m.program.length cells r right cell lane).cost ≤ 3 :=
    fun _ _ _ => ref_cost_le r hr _
  have hs : ∀ lane, (symbolBit s lane).cost ≤ 3 := fun _ => lit_cost_le _
  unfold movedBit
  split <;> try exact lit_cost_le _
  split <;> try exact lit_cost_le _
  split
  · cases d <;> first | exact hs _ | exact ht _ _ _
  · split <;> try exact lit_cost_le _
    cases d <;> cases h : decide (i - (4 + m.program.length) ≥ 2 * (cells - 1)) <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat first | exact hs _ | exact ht _ _ _ | split

theorem stepExprs_cost (m : Machine) (cells : Nat) (r : List Expr)
    (hr : ∀ e ∈ r, e.cost ≤ 3) :
    ∀ e ∈ stepExprs m cells r, e.cost ≤ 64 * m.program.length + 19 := by
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  have hi : ∀ instr, (instructionBit m cells r i instr).cost ≤ 3 := by
    intro instr
    cases instr with
    | halt b => exact lit_cost_le _
    | move q s d => exact movedBit_cost _ _ _ hr _ _ _ _
  have hc := chooseState_cost m r _ hr hi 0 m.program
  have hd := ref_cost_le r hr 0
  have hh : (if i = 0 then Expr.lit true else if i = 1 then ref r 1 else .lit false).cost ≤ 3 := by
    split <;> first | exact lit_cost_le _ | split <;> first | exact ref_cost_le r hr _ | exact lit_cost_le _
  simp only [mux_cost]
  omega

theorem initialExprs_cost (m : Machine) (n cells : Nat) :
    ∀ e ∈ initialExprs m n cells, e.cost ≤ 3 := by
  have hi : ∀ cell lane, (inputSymbolBit n cell lane).cost ≤ 3 := by
    intro cell lane
    unfold inputSymbolBit
    split
    · split <;> simp [Expr.cost, Expr.neg]
    · decide
  intro e he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  simp only
  split <;> try exact lit_cost_le _
  split <;> try exact hi _ _
  split <;> try exact lit_cost_le _
  split <;> first | exact lit_cost_le _ | exact hi _ _

theorem totalCost_le (es : List Expr) (k : Nat) (he : ∀ e ∈ es, e.cost ≤ k) :
    totalCost es ≤ k * es.length := by
  induction es with
  | nil => simp [totalCost]
  | cons e es ih =>
      have := ih (fun a ha => he a (by simp [ha]))
      have := he e (by simp)
      change e.cost + totalCost es ≤ k * (es.length + 1)
      rw [Nat.mul_succ]
      omega

def rowCost (m : Machine) : Nat := 64 * m.program.length + 19

theorem compileRows_length (m : Machine) (t cells n : Nat) (refs : List Nat) :
    (compileRows m t cells n refs).length ≤ t * (rowCost m * width m.program.length cells) + 2 := by
  induction t generalizing cells n refs with
  | zero => simp [compileRows, finish]
  | succ t ih =>
      let es := stepExprs m cells (refs.map Expr.input)
      have he := stepExprs_cost m cells (refs.map Expr.input) (by
        intro e he; obtain ⟨i, _, rfl⟩ := List.mem_map.mp he; simp [Expr.cost])
      have ha : (compileMany n es).1.length ≤ rowCost m * width m.program.length (cells - 1) := by
        rw [compileMany_cost]
        have := totalCost_le es (rowCost m) he
        simpa [es, stepExprs] using this
      have hb := ih (cells - 1) (n + (compileMany n es).1.length) (compileMany n es).2
      dsimp [es] at ha hb
      have hw : width m.program.length (cells - 1) ≤ width m.program.length cells := by
        unfold width; omega
      change ((compileMany n es).1 ++ _).length ≤ _
      rw [List.length_append]
      dsimp [es]
      calc
        _ ≤ (t + 1) * (rowCost m * width m.program.length (cells - 1)) + 2 := by
          rw [Nat.add_mul]; omega
        _ ≤ (t + 1) * (rowCost m * width m.program.length cells) + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)) 2

theorem simCircuit_length (m : Machine) (p : Polynomial) (n : Nat) :
    (simCircuit m p n).length ≤
      (p.eval n * rowCost m + 3) * width m.program.length (n + p.eval n + 1) + 2 := by
  have ha := totalCost_le (initialExprs m n (n + p.eval n + 1)) 3 (initialExprs_cost _ _ _)
  have hb := compileRows_length m (p.eval n) (n + p.eval n + 1)
    (n + (compileMany n (initialExprs m n (n + p.eval n + 1))).1.length)
    (compileMany n (initialExprs m n (n + p.eval n + 1))).2
  have hl : (initialExprs m n (n + p.eval n + 1)).length =
      width m.program.length (n + p.eval n + 1) := by simp [initialExprs]
  rw [hl] at ha
  have hA : (compileMany n (initialExprs m n (n + p.eval n + 1))).1.length ≤
      3 * width m.program.length (n + p.eval n + 1) := by rw [compileMany_cost]; exact ha
  simp only [simCircuit, List.length_append]
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- An explicit coarse polynomial in the clock polynomial's coefficient and
degree. This accounts for row initialization, all clocks, and the output copy. -/
def simulationPolynomial (m : Machine) (p : Polynomial) : Polynomial :=
  ⟨(p.coefficient * rowCost m + 3) * (m.program.length + 4 * p.coefficient + 8) + 2,
    2 * p.degree + 1⟩

theorem simCircuit_polynomial_size (m : Machine) (p : Polynomial) (n : Nat) :
    (simCircuit m p n).length ≤ (simulationPolynomial m p).eval n := by
  let E := (n + 1) ^ (p.degree + 1)
  let F := (n + 1) ^ p.degree
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
  have hF : 1 ≤ F := Nat.one_le_pow _ _ (by omega)
  have hnE : n + 1 ≤ E := by
    have := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 1 ≤ p.degree + 1 by omega)
    simpa [E] using this
  have hFE : F ≤ E := Nat.pow_le_pow_right (by omega) (by omega)
  have hpE : p.eval n ≤ p.coefficient * E := Nat.mul_le_mul_left _ hFE
  have hk : n + p.eval n + 1 ≤ (p.coefficient + 1) * E := by
    rw [Nat.add_mul]; omega
  have hw : width m.program.length (n + p.eval n + 1) ≤
      (m.program.length + 4 * p.coefficient + 8) * E := by
    have hs : m.program.length + 4 ≤ (m.program.length + 4) * E := by
      simpa using Nat.mul_le_mul_left (m.program.length + 4) hE
    calc
      _ = m.program.length + 4 + 4 * (n + p.eval n + 1) := by unfold width; omega
      _ ≤ (m.program.length + 4) * E + 4 * ((p.coefficient + 1) * E) :=
        Nat.add_le_add hs (Nat.mul_le_mul_left 4 hk)
      _ = _ := by simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]; omega
  have hc : p.eval n * rowCost m + 3 ≤ (p.coefficient * rowCost m + 3) * F := by
    have h3 := Nat.mul_le_mul_left 3 hF
    calc
      _ = (p.coefficient * rowCost m) * F + 3 := by dsimp [F]; simp only [Polynomial.eval]; congr 1; ac_rfl
      _ ≤ _ := by rw [Nat.add_mul]; omega
  have hpow : F * E = (n + 1) ^ (2 * p.degree + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hh := Nat.mul_le_mul hc hw
  have h2 := Nat.mul_le_mul_left 2 (Nat.one_le_pow (2 * p.degree + 1) (n + 1) (by omega))
  calc
    (simCircuit m p n).length ≤
        (p.eval n * rowCost m + 3) * width m.program.length (n + p.eval n + 1) + 2 :=
      simCircuit_length m p n
    _ ≤ ((p.coefficient * rowCost m + 3) * F) *
        ((m.program.length + 4 * p.coefficient + 8) * E) + 2 := Nat.add_le_add_right hh 2
    _ = ((p.coefficient * rowCost m + 3) * (m.program.length + 4 * p.coefficient + 8)) *
        (n + 1) ^ (2 * p.degree + 1) + 2 := by rw [← hpow]; ac_rfl
    _ ≤ (simulationPolynomial m p).eval n := by
      simp only [simulationPolynomial, Polynomial.eval, Nat.add_mul]
      omega

end Issue626.Simulation
