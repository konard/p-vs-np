import proofs.experiments.issue624.lean.SuccessorCNF

/-! A bounded accepting prefix of finite tape rows, using the original
`LocalTrace`. Each row has one stop bit. Stopping requires an accepting halt;
continuing requires the shared successor CNF and the remaining prefix.
Inactive suffixes are unconstrained. No configurations or traces are enumerated.
This module does not yet wire the input and certificate into row zero. -/
namespace Issue624.RunCNF
open Complexity Issue532.Machines Issue568.Tableau Issue624.LocalCNF
open Issue624.MachineCNF Issue624.SuccessorCNF

def guarded (l : Lit) (f : CNF) : CNF := f.map (implies [l])

theorem guarded_models (a : Assignment) (l : Lit) (f : CNF) :
    evalCNF a (guarded l f) = true ↔ (evalLit a l = true → evalCNF a f = true) := by
  simp only [guarded, evalCNF_map, implies_models, List.mem_singleton, forall_eq]
  have hall : evalCNF a f = true ↔ ∀ c ∈ f, evalClause a c = true := by
    induction f with
    | nil => simp [evalCNF]
    | cons c f ih => simp [evalCNF, ih]
  rw [hall]
  constructor
  · intro hf hl c hc; exact hf c hc hl
  · intro hf c hc hl; exact hf hl c hc

def haltRule (m : Machine) (base width q h s : Nat) : CNF :=
  if m.instruction q (symbolOfIndex s) = .halt true then []
  else [implies (guard base m.program.length width q h s) []]

def haltCNF (m : Machine) (base width : Nat) : CNF :=
  (List.range m.program.length).flatMap fun q =>
    (List.range width).flatMap fun h =>
      (List.range 4).flatMap fun s => haltRule m base width q h s

theorem haltRule_models (m : Machine) (base width q h s : Nat) (a : Assignment) :
    evalCNF a (haltRule m base width q h s) = true ↔
      ((∀ l ∈ guard base m.program.length width q h s, evalLit a l = true) →
        m.instruction q (symbolOfIndex s) = .halt true) := by
  unfold haltRule
  split <;> simp_all [evalCNF, implies_models, evalClause]

theorem haltCNF_step (m : Machine) (base width : Nat) (a : Assignment) (c : Config)
    (hc : RowRepresents a base m.program.length width c) :
    evalCNF a (haltCNF m base width) = true ↔ step m c = .inl true := by
  have hs : step m c = .inl true ↔ m.instruction c.state c.head = .halt true := by
    unfold step
    cases m.instruction c.state c.head <;> simp
  rw [hs]
  simp only [haltCNF, evalCNF_flatMap, List.mem_range, haltRule_models]
  constructor
  · intro hf
    have hg := (guard_models a _ _ _ c hc _ _ _ hc.2.1.1 hc.2.2.1.1
      (symbolIndex_lt c.head)).mpr ⟨rfl, rfl, symbolOfIndex_index c.head⟩
    simpa using hf _ hc.2.1.1 _ hc.2.2.1.1 _ (symbolIndex_lt c.head) hg
  · intro hf q hq h hh s hs hg
    obtain ⟨rfl, rfl, he⟩ := (guard_models a _ _ _ c hc q h s hq hh hs).mp hg
    simpa [he] using hf

def stride (states width : Nat) : Nat := states + 5 * width + 1
def stopVar (base states width : Nat) : Nat := base + states + 5 * width
def nextBase (base states width : Nat) : Nat := base + stride states width

def runCNF (m : Machine) (base width : Nat) : Nat → CNF
  | 0 => [[]]
  | k + 1 =>
    let stop := stopVar base m.program.length width
    let next := nextBase base m.program.length width
    rowCNF base m.program.length width ++ guarded ⟨stop, true⟩ (haltCNF m base width) ++
      guarded ⟨stop, false⟩ (successorCNF m base next width ++ runCNF m next width k)

def TraceRepresents (a : Assignment) (base states width : Nat) : List Config → Prop
  | [] => False
  | c :: rest => RowRepresents a base states width c ∧
      a (stopVar base states width) = rest.isEmpty ∧
      (rest ≠ [] → TraceRepresents a (nextBase base states width) states width rest)

def decodeTrace (m : Machine) (base width : Nat) : Nat → Assignment → List Config
  | 0, _ => []
  | k + 1, a => decodeRow a base m.program.length width ::
      if a (stopVar base m.program.length width) then []
      else decodeTrace m (nextBase base m.program.length width) width k a

theorem runCNF_unfold (m : Machine) (base width k : Nat) (a : Assignment) :
    evalCNF a (runCNF m base width (k + 1)) = true ↔
      evalCNF a (rowCNF base m.program.length width) = true ∧
      (a (stopVar base m.program.length width) = true → evalCNF a (haltCNF m base width) = true) ∧
      (a (stopVar base m.program.length width) = false →
        evalCNF a (successorCNF m base (nextBase base m.program.length width) width) = true ∧
        evalCNF a (runCNF m (nextBase base m.program.length width) width k) = true) := by
  simp only [runCNF, evalCNF_append, Bool.and_eq_true, guarded_models, evalLit]
  cases a (stopVar base m.program.length width) <;> simp

theorem decodeTrace_length (m : Machine) (base width fuel : Nat) (a : Assignment) :
    (decodeTrace m base width fuel a).length ≤ fuel := by
  induction fuel generalizing base with
  | zero => simp [decodeTrace]
  | succ k ih =>
    simp only [decodeTrace, List.length_cons]
    split
    · simp
    · have := ih (nextBase base m.program.length width); omega

/-- Every satisfying assignment extracts an actual accepting local trace.
The bound includes the final charged halting instruction. -/
theorem runCNF_sound (m : Machine) (base width fuel : Nat) (a : Assignment)
    (hf : evalCNF a (runCNF m base width fuel) = true) :
    TraceRepresents a base m.program.length width (decodeTrace m base width fuel a) ∧
      LocalTrace m true (decodeTrace m base width fuel a) := by
  induction fuel generalizing base with
  | zero => simp [runCNF, evalCNF, evalClause] at hf
  | succ k ih =>
    obtain ⟨hr, ht, hn⟩ := (runCNF_unfold m base width k a).mp hf
    have hc := (rowCNF_models a base m.program.length width).mp hr
    cases he : a (stopVar base m.program.length width) with
    | true =>
      simp only [decodeTrace, he, ite_true, TraceRepresents, List.isEmpty_nil]
      exact ⟨⟨hc, trivial, by simp⟩, (haltCNF_step m base width a _ hc).mp (ht he)⟩
    | false =>
      obtain ⟨hs, hf'⟩ := hn he
      obtain ⟨hrep, hlocal⟩ := ih _ hf'
      generalize hd : decodeTrace m (nextBase base m.program.length width) width k a = rest at *
      cases rest with
      | nil => exact False.elim hlocal
      | cons d tail =>
        have hstep := ((successorCNF_models m base (nextBase base m.program.length width) width a).mp hs).2.2
        rw [decodeRow_represents _ _ _ _ d hrep.1] at hstep
        simp only [decodeTrace, he, Bool.false_eq_true, ite_false, hd, TraceRepresents,
          List.isEmpty_cons]
        exact ⟨⟨hc, trivial, fun _ => hrep⟩, hstep, hlocal⟩

theorem runCNF_complete (m : Machine) (base width fuel : Nat) (a : Assignment)
    (trace : List Config) (hr : TraceRepresents a base m.program.length width trace)
    (hl : LocalTrace m true trace) (hb : trace.length ≤ fuel) :
    evalCNF a (runCNF m base width fuel) = true := by
  induction fuel generalizing base trace with
  | zero => cases trace <;> simp_all [TraceRepresents]
  | succ k ih =>
    cases trace with
    | nil => exact False.elim hr
    | cons c rest =>
      obtain ⟨hc, he, ht⟩ := hr
      apply (runCNF_unfold m base width k a).mpr
      refine ⟨rowRepresents_models _ _ _ _ _ hc, ?_, ?_⟩
      · intro hstop
        cases rest with
        | nil => exact (haltCNF_step m base width a c hc).mpr hl
        | cons d tail => simp_all
      · intro hgo
        cases rest with
        | nil => simp_all
        | cons d tail =>
          have hd := ht (by simp)
          exact ⟨(successorCNF_step m base _ width a c d hc hd.1).mpr hl.1,
            ih _ _ hd hl.2 (by simpa using Nat.le_of_succ_le_succ hb)⟩

theorem runCNF_models (m : Machine) (base width fuel : Nat) (a : Assignment) :
    evalCNF a (runCNF m base width fuel) = true ↔
      ∃ trace, TraceRepresents a base m.program.length width trace ∧
        trace.length ≤ fuel ∧ LocalTrace m true trace := by
  constructor
  · intro hf
    have h := runCNF_sound m base width fuel a hf
    exact ⟨_, h.1, decodeTrace_length m base width fuel a, h.2⟩
  · rintro ⟨trace, hr, hb, hl⟩
    exact runCNF_complete m base width fuel a trace hr hl hb

theorem runCNF_wrong_successor_rejected (m : Machine) (base width fuel : Nat)
    (a : Assignment) (c d : Config) (rest : List Config)
    (hs : step m c ≠ .inr d) (hd : decodeTrace m base width fuel a = c :: d :: rest) :
    evalCNF a (runCNF m base width fuel) = false := by
  cases hf : evalCNF a (runCNF m base width fuel) with
  | false => rfl
  | true =>
    have hl := (runCNF_sound m base width fuel a hf).2
    rw [hd] at hl
    exact False.elim (hs hl.1)

def traceAssignment (base states width : Nat) : List Config → Assignment
  | [] => fun _ => false
  | c :: rest => fun v =>
      if v < stopVar base states width then rowAssignment base states width c v
      else if v = stopVar base states width then rest.isEmpty
      else traceAssignment (nextBase base states width) states width rest v

theorem rowRepresents_congr (a b : Assignment) (base states width : Nat) (c : Config)
    (he : ∀ v, base ≤ v → v < stopVar base states width → a v = b v)
    (hc : RowRepresents a base states width c) : RowRepresents b base states width c := by
  have hs (offset size value : Nat) (hb : base ≤ offset)
      (hu : offset + size ≤ stopVar base states width) (h : Selected a offset size value) :
      Selected b offset size value := by
    refine ⟨h.1, ?_, ?_⟩
    · rw [← he (offset + value) (by omega) (by have := h.1; omega)]; exact h.2.1
    · intro j hj hj'
      apply h.2.2 j hj
      rw [he (offset + j) (by omega) (by omega)]; exact hj'
  refine ⟨hc.1, hs base states _ (by omega) (by dsimp [stopVar]; omega) hc.2.1,
    hs (base + states) width _ (by omega) (by dsimp [stopVar]; omega) hc.2.2.1, ?_⟩
  intro i hi
  exact hs (tapeBase base states width i) 4 _ (by dsimp [tapeBase]; omega)
    (by dsimp [tapeBase, stopVar]; omega) (hc.2.2.2 i hi)

theorem traceRepresents_congr (a b : Assignment) (base states width : Nat) (trace : List Config)
    (he : ∀ v, base ≤ v → a v = b v) (hr : TraceRepresents a base states width trace) :
    TraceRepresents b base states width trace := by
  induction trace generalizing base with
  | nil => exact False.elim hr
  | cons c rest ih =>
    refine ⟨rowRepresents_congr a b base states width c (fun v hv _ => he v hv) hr.1, ?_, ?_⟩
    · rw [← he _ (by dsimp [stopVar]; omega)]; exact hr.2.1
    · intro hrest
      apply ih _ (fun v hv => he v (by dsimp [nextBase, stride] at hv; omega)) (hr.2.2 hrest)

/-- The row and stop blocks are disjoint, and the canonical assignment
represents every fixed-width trace, regardless of whether its edges are legal. -/
theorem traceAssignment_represents (base states width : Nat) (trace : List Config)
    (hne : trace ≠ []) (hc : ∀ c ∈ trace, span c = width ∧ c.state < states) :
    TraceRepresents (traceAssignment base states width trace) base states width trace := by
  induction trace generalizing base with
  | nil => exact False.elim (hne rfl)
  | cons c rest ih =>
    have hrow := rowAssignment_represents base states width c
      (hc c (by simp)).1 (hc c (by simp)).2
    refine ⟨rowRepresents_congr _ _ base states width c ?_ hrow, ?_, ?_⟩
    · intro v _ hv; simp [traceAssignment, hv]
    · simp [traceAssignment]
    · intro ht
      have hr := ih (nextBase base states width) ht (fun d hd => hc d (List.mem_cons_of_mem c hd))
      apply traceRepresents_congr _ _ _ states width rest ?_ hr
      intro v hv
      have h0 : ¬v < stopVar base states width := by dsimp [nextBase, stride, stopVar] at *; omega
      have h1 : v ≠ stopVar base states width := by dsimp [nextBase, stride, stopVar] at *; omega
      simp [traceAssignment, h0, h1]

theorem decodeTrace_represents (m : Machine) (base width fuel : Nat) (a : Assignment)
    (trace : List Config) (hr : TraceRepresents a base m.program.length width trace)
    (hb : trace.length ≤ fuel) : decodeTrace m base width fuel a = trace := by
  induction fuel generalizing base trace with
  | zero => cases trace <;> simp_all [TraceRepresents]
  | succ k ih =>
    cases trace with
    | nil => exact False.elim hr
    | cons c rest =>
      simp only [decodeTrace, decodeRow_represents a _ _ _ c hr.1, hr.2.1]
      cases rest with
      | nil => simp
      | cons d tail =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
        rw [ih _ _ (hr.2.2 (by simp)) (by simpa using Nat.le_of_succ_le_succ hb)]

theorem runCNF_traceAssignment (m : Machine) (base width fuel : Nat) (trace : List Config)
    (hl : LocalTrace m true trace) (hb : trace.length ≤ fuel)
    (hw : ∀ c ∈ trace, span c = width) :
    evalCNF (traceAssignment base m.program.length width trace) (runCNF m base width fuel) = true ∧
      decodeTrace m base width fuel (traceAssignment base m.program.length width trace) = trace := by
  have hne : trace ≠ [] := by intro h; subst trace; exact hl
  have hrep := traceAssignment_represents base m.program.length width trace hne
    (fun c hc => ⟨hw c hc, Issue624.FixedWindow.accepting_trace_state_lt m trace hl c hc⟩)
  exact ⟨runCNF_complete m base width fuel _ trace hrep hl hb,
    decodeTrace_represents m base width fuel _ trace hrep hb⟩

theorem traceRepresents_width (a : Assignment) (base states width : Nat) (trace : List Config)
    (hr : TraceRepresents a base states width trace) : ∀ c ∈ trace, span c = width := by
  induction trace generalizing base with
  | nil => exact False.elim hr
  | cons c rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hr.1.1
    · exact ih _ (hr.2.2 (by intro he; simp [he] at hd)) d hd

/-- Satisfiability is exactly existence of a bounded accepting trace of
the fixed width. Initial input/certificate wiring is a separate constraint. -/
theorem runCNF_iff (m : Machine) (base width fuel : Nat) :
    Satisfiable (runCNF m base width fuel) ↔
      ∃ trace, trace.length ≤ fuel ∧ LocalTrace m true trace ∧ ∀ c ∈ trace, span c = width := by
  constructor
  · rintro ⟨a, hf⟩
    obtain ⟨trace, hr, hb, hl⟩ := (runCNF_models m base width fuel a).mp hf
    exact ⟨trace, hb, hl, traceRepresents_width _ _ _ _ _ hr⟩
  · rintro ⟨trace, hb, hl, hw⟩
    exact ⟨_, (runCNF_traceAssignment m base width fuel trace hl hb hw).1⟩

theorem runCNF_rejecting_unsatisfiable (m : Machine) (base width fuel : Nat)
    (hm : ∀ c, step m c = .inl false) : ¬Satisfiable (runCNF m base width fuel) := by
  intro hf
  obtain ⟨trace, _, hl, _⟩ := (runCNF_iff m base width fuel).mp hf
  cases trace with
  | nil => exact hl
  | cons c rest =>
    cases rest with
    | nil => rw [LocalTrace, hm c] at hl; cases hl
    | cons d tail => have hs := hl.1; rw [hm c] at hs; cases hs

theorem haltCNF_length (m : Machine) (base width : Nat) :
    (haltCNF m base width).length ≤ 4 * m.program.length * width := by
  have hi (q h : Nat) : ((List.range 4).flatMap fun s => haltRule m base width q h s).length ≤ 4 := by
    have := flatMap_length_le (List.range 4) (fun s => haltRule m base width q h s) 1
      (by intro s _; unfold haltRule; split <;> simp)
    simpa using this
  have hh (q : Nat) := flatMap_length_le (List.range width)
    (fun h => (List.range 4).flatMap fun s => haltRule m base width q h s) 4
    (fun h _ => hi q h)
  have hq := flatMap_length_le (List.range m.program.length)
    (fun q => (List.range width).flatMap fun h => (List.range 4).flatMap fun s => haltRule m base width q h s)
    (width * 4) (fun q _ => by simpa using hh q)
  simpa [haltCNF, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq

theorem haltCNF_bounds (m : Machine) (base width : Nat) :
    VarsBelow (stopVar base m.program.length width) (haltCNF m base width) ∧
      ∀ c ∈ haltCNF m base width, c.length ≤ 3 := by
  have hb : ∀ c ∈ haltCNF m base width,
      (∀ l ∈ c, l.var < stopVar base m.program.length width) ∧ c.length ≤ 3 := by
    intro c hc
    simp only [haltCNF, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨q, hq, h, hh, s, hs, hc⟩ := hc
    unfold haltRule at hc
    split at hc
    · simp at hc
    · simp only [List.mem_singleton] at hc
      subst c
      constructor
      · intro l hl
        simp only [implies, SuccessorCNF.guard, List.map_cons, List.map_nil, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;>
          dsimp [negate, stateVar, headVar, tapeVar, tapeBase, stopVar] <;> omega
      · simp [implies, SuccessorCNF.guard]
  exact ⟨fun c hc => (hb c hc).1, fun c hc => (hb c hc).2⟩

def runCount (m : Machine) (width : Nat) : Nat :=
  m.program.length * m.program.length + width * width + 17 * width + 2 +
    4 * m.program.length * width + successorCount m width

theorem runCNF_length (m : Machine) (base width fuel : Nat) :
    (runCNF m base width fuel).length ≤ fuel * runCount m width + 1 := by
  induction fuel generalizing base with
  | zero => simp [runCNF]
  | succ k ih =>
    have hr := rowCNF_length base m.program.length width
    have hh := haltCNF_length m base width
    have hs := successorCNF_length m base (nextBase base m.program.length width) width
    have ht := ih (nextBase base m.program.length width)
    simp only [runCNF, guarded, List.length_map, List.length_append, Nat.succ_mul]
    unfold runCount at ht ⊢
    omega

theorem guarded_bounds (l : Lit) (f : CNF) (bound width : Nat) (hl : l.var < bound)
    (hv : VarsBelow bound f) (hw : ∀ c ∈ f, c.length ≤ width) :
    VarsBelow bound (guarded l f) ∧ ∀ c ∈ guarded l f, c.length ≤ width + 1 := by
  constructor
  · intro c hc t ht
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simp only [implies, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hl
    · exact hv d hd t ht
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have := hw d hd
    simpa [implies] using Nat.add_le_add_left this 1

theorem runCNF_bounds (m : Machine) (base width fuel : Nat) :
    VarsBelow (base + (fuel + 1) * stride m.program.length width) (runCNF m base width fuel) ∧
      ∀ c ∈ runCNF m base width fuel, c.length ≤ m.program.length + width + 6 + fuel := by
  induction fuel generalizing base with
  | zero => simp [runCNF, VarsBelow]
  | succ k ih =>
    let next := nextBase base m.program.length width
    let bound := base + (k + 1 + 1) * stride m.program.length width
    let cw := m.program.length + width + 6 + k
    have hb : stopVar base m.program.length width < bound := by
      dsimp [stopVar, bound, stride]; simp only [Nat.add_mul, Nat.one_mul]; omega
    have hn := ih next
    have hr := rowCNF_bounds base m.program.length width
    have hh := haltCNF_bounds m base width
    have hs := successorCNF_bounds m base next width
    have he : next + (k + 1) * stride m.program.length width = bound := by
      dsimp [next, nextBase, bound]; simp only [Nat.add_mul, Nat.one_mul]; omega
    have hmax : max base next = next := by dsimp [next, nextBase]; omega
    have hsbound : next + m.program.length + 5 * width ≤ bound := by
      dsimp [next, nextBase, bound, stride]; simp only [Nat.add_mul, Nat.one_mul]; omega
    have hhalt := guarded_bounds ⟨stopVar base m.program.length width, true⟩
      (haltCNF m base width) bound cw hb
      (fun c hc l hl => Nat.lt_of_lt_of_le (hh.1 c hc l hl) (by omega))
      (fun c hc => Nat.le_trans (hh.2 c hc) (by dsimp [cw]; omega))
    have hgo := guarded_bounds ⟨stopVar base m.program.length width, false⟩
      (successorCNF m base next width ++ runCNF m next width k) bound cw hb
      (by
        intro c hc l hl
        rcases List.mem_append.mp hc with hc | hc
        · have := hs.1 c hc l hl; rw [hmax] at this; omega
        · rw [← he]; exact hn.1 c hc l hl)
      (by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact Nat.le_trans (hs.2 c hc) (by dsimp [cw]; omega)
        · exact hn.2 c hc)
    constructor
    · intro c hc l hl
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · have := hr.1 c hc l hl; dsimp [bound, stride]; simp only [Nat.add_mul, Nat.one_mul]; omega
        · exact hhalt.1 c hc l hl
      · exact hgo.1 c hc l hl
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · exact Nat.le_trans (hr.2 c hc) (by omega)
        · exact hhalt.2 c hc
      · exact hgo.2 c hc

def runSize (m : Machine) (base width fuel : Nat) : Nat :=
  2 * (fuel * runCount m width + 1) *
    (1 + (m.program.length + width + 6 + fuel) *
      (base + (fuel + 1) * stride m.program.length width + 1))

theorem runCNF_encoded_size (m : Machine) (base width fuel : Nat) :
    (encodeCNF (runCNF m base width fuel)).length ≤ runSize m base width fuel := by
  have hb := runCNF_bounds m base width fuel
  exact Nat.le_trans (cnf_encoded_size _ _ _ hb.1 hb.2)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (runCNF_length m base width fuel)))

/-- An explicit envelope assembled with the shared polynomial arithmetic.
The three arguments bound the offset, window width, and charged clock. -/
def runPolynomial (m : Machine) (b w t : Polynomial) : Polynomial :=
  let c (n : Nat) : Polynomial := ⟨n, 0⟩
  let q := c m.program.length
  let row := polyAdd (polyAdd (polyAdd (polyMul q q) (polyMul w w)) (polyMul (c 17) w)) (c 2)
  let moves := polyMul (polyMul (polyMul (c 4) q) w) (polyAdd (polyMul (c 4) w) (c 2))
  let count := polyAdd (polyAdd row (polyMul (polyMul (c 4) q) w))
    (polyAdd (polyMul (c 2) row) moves)
  let stepWidth := polyAdd (polyAdd (polyAdd q w) (c 6)) t
  let stepStride := polyAdd (polyAdd q (polyMul (c 5) w)) (c 1)
  let variables := polyAdd (polyAdd b (polyMul (polyAdd t (c 1)) stepStride)) (c 1)
  polyMul (polyMul (c 2) (polyAdd (polyMul t count) (c 1)))
    (polyAdd (c 1) (polyMul stepWidth variables))

theorem runCNF_polynomial_size (m : Machine) (b w t : Polynomial) (n base width fuel : Nat)
    (hb : base ≤ b.eval n) (hw : width ≤ w.eval n) (ht : fuel ≤ t.eval n) :
    (encodeCNF (runCNF m base width fuel)).length ≤ (runPolynomial m b w t).eval n := by
  have add (p q : Polynomial) (u v : Nat) (hu : u ≤ p.eval n) (hv : v ≤ q.eval n) :
      u + v ≤ (polyAdd p q).eval n := Nat.le_trans (Nat.add_le_add hu hv) (polyAdd_eval p q n)
  have mul (p q : Polynomial) (u v : Nat) (hu : u ≤ p.eval n) (hv : v ≤ q.eval n) :
      u * v ≤ (polyMul p q).eval n := Nat.le_trans (Nat.mul_le_mul hu hv) (Nat.le_of_eq (polyMul_eval p q n))
  have const (k : Nat) : k ≤ (⟨k, 0⟩ : Polynomial).eval n := by simp [Polynomial.eval]
  have hrow := add _ _ _ _ (add _ _ _ _
    (add _ _ _ _ (mul _ _ _ _ (const m.program.length) (const m.program.length))
      (mul _ _ _ _ hw hw)) (mul _ _ _ _ (const 17) hw)) (const 2)
  have hprod := mul _ _ _ _ (mul _ _ _ _ (const 4) (const m.program.length)) hw
  have hcount := add _ _ _ _ (add _ _ _ _ hrow hprod)
    (add _ _ _ _ (mul _ _ _ _ (const 2) hrow)
      (mul _ _ _ _ hprod (add _ _ _ _ (mul _ _ _ _ (const 4) hw) (const 2))))
  have hwidth := add _ _ _ _ (add _ _ _ _ (add _ _ _ _ (const m.program.length) hw) (const 6)) ht
  have hstride := add _ _ _ _ (add _ _ _ _ (const m.program.length) (mul _ _ _ _ (const 5) hw)) (const 1)
  have hvars := add _ _ _ _ (add _ _ _ _ hb (mul _ _ _ _ (add _ _ _ _ ht (const 1)) hstride)) (const 1)
  have hsize := mul _ _ _ _ (mul _ _ _ _ (const 2) (add _ _ _ _ (mul _ _ _ _ ht hcount) (const 1)))
    (add _ _ _ _ (const 1) (mul _ _ _ _ hwidth hvars))
  exact Nat.le_trans (runCNF_encoded_size m base width fuel) hsize

end Issue624.RunCNF
