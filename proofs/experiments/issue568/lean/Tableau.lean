import proofs.complexity.lean.Complexity

/-!
The first Cook--Levin slice: a bounded list of complete configurations with
one constraint for each adjacent pair and a halting constraint at the end.
The list contains the configuration *before* every charged instruction.
This uses the shared finite machine and does not yet encode the list as CNF.
-/

namespace Issue568.Tableau

open Complexity

/-- Local transition and final-answer constraints on a nonempty trace. -/
def LocalTrace (m : Machine) (b : Bool) : List Config → Prop
  | [] => False
  | [c] => step m c = .inl b
  | c :: d :: rest => step m c = .inr d ∧ LocalTrace m b (d :: rest)

/-- A tableau starts at `c`, fits the clock, and ends with answer `b`. -/
def BoundedTableau (m : Machine) (c : Config) (clock : Nat) (b : Bool) : Prop :=
  ∃ trace : List Config,
    trace.head? = some c ∧ trace.length ≤ clock ∧ LocalTrace m b trace

/-- Number of explicitly represented tape cells, including the head. -/
def span (c : Config) : Nat := c.left.length + 1 + c.right.length

private theorem moveHead_span_le (c : Config) (q : Nat) (w : Symbol)
    (dir : Direction) : span (moveHead c q w dir) ≤ span c + 1 := by
  cases c with
  | mk state left head right =>
    cases dir <;> cases left <;> cases right <;>
      simp [span, moveHead] <;> omega

private theorem step_span_le {m : Machine} {c d : Config}
    (hs : step m c = .inr d) : span d ≤ span c + 1 := by
  unfold step at hs
  cases hi : m.instruction c.state c.head with
  | halt b => simp [hi] at hs
  | move q w dir =>
    simp [hi] at hs
    subst d
    exact moveHead_span_le c q w dir

/-- Every cell explicitly present in a legal trace fits a tape window that
grows by at most one cell per charged instruction. -/
theorem trace_span_bound (m : Machine) (b : Bool) :
    ∀ (trace : List Config) (c d : Config),
      trace.head? = some c → LocalTrace m b trace → d ∈ trace →
        span d ≤ span c + trace.length := by
  intro trace
  induction trace with
  | nil =>
    intro c d hhead _ _
    simp at hhead
  | cons first rest ih =>
    cases rest with
    | nil =>
      intro c d hhead _ hd
      simp at hhead hd
      subst c
      subst d
      omega
    | cons next tail =>
      intro c d hhead hlocal hd
      simp at hhead
      subst c
      obtain ⟨hs, ht⟩ := hlocal
      simp only [List.mem_cons] at hd
      rcases hd with rfl | htail
      · omega
      · have hrest := ih next d rfl ht (by simpa only [List.mem_cons] using htail)
        have hstep := step_span_le hs
        simp only [List.length_cons] at hrest ⊢
        omega

theorem initial_span_le (x : Word) : span (initial x) ≤ x.length + 1 := by
  cases x with
  | nil => simp [span, initial, initialSymbols]
  | cons bit rest =>
    simp [span, initial, initialSymbols]
    omega

/-- A clock `k` bounds every represented configuration width by encoded
input length plus `k + 1`. This is a cell bound, not a CNF bit-size bound. -/
theorem bounded_initial_span (m : Machine) (x : Word) (clock : Nat) (b : Bool)
    (trace : List Config) (hstart : trace.head? = some (initial x))
    (hclock : trace.length ≤ clock) (hlocal : LocalTrace m b trace)
    (d : Config) (hd : d ∈ trace) :
    span d ≤ x.length + clock + 1 := by
  have hspan := trace_span_bound m b trace (initial x) d hstart hlocal hd
  have hinit := initial_span_le x
  omega

private theorem trace_sound (m : Machine) (b : Bool) :
    ∀ trace : List Config, LocalTrace m b trace →
      ∃ c, trace.head? = some c ∧ Run m c trace.length b := by
  intro trace
  induction trace with
  | nil => intro h; exact False.elim h
  | cons c rest ih =>
    cases rest with
    | nil =>
      intro h
      exact ⟨c, rfl, Run.halt h⟩
    | cons d tail =>
      intro h
      obtain ⟨hs, ht⟩ := h
      obtain ⟨c', hc', hr⟩ := ih ht
      simp at hc'
      subst c'
      exact ⟨c, rfl, Run.next hs hr⟩

private theorem trace_complete (m : Machine) {c : Config} {t : Nat} {b : Bool}
    (hr : Run m c t b) :
    ∃ trace : List Config,
      trace.head? = some c ∧ trace.length = t ∧ LocalTrace m b trace := by
  induction hr with
  | @halt c b hs => exact ⟨[c], rfl, rfl, hs⟩
  | @next c d t b hs _ ih =>
    obtain ⟨trace, hhead, hlen, hlocal⟩ := ih
    cases trace with
    | nil => simp at hhead
    | cons first rest =>
      simp at hhead
      subst first
      exact ⟨c :: d :: rest, rfl, by simp [hlen], ⟨hs, hlocal⟩⟩

/-- The local constraints are sound and complete for the shared `Run` relation,
including the exact number of charged instructions. -/
theorem localTrace_iff_run (m : Machine) (c : Config) (t : Nat) (b : Bool) :
    (∃ trace : List Config,
      trace.head? = some c ∧ trace.length = t ∧ LocalTrace m b trace) ↔
      Run m c t b := by
  constructor
  · rintro ⟨trace, hhead, hlen, hlocal⟩
    obtain ⟨c', hc', hr⟩ := trace_sound m b trace hlocal
    rw [hhead] at hc'
    cases hc'
    simpa [hlen] using hr
  · exact trace_complete m

/-- A clocked accepting tableau exists exactly when the machine accepts by
that clock. The clock counts the final halting instruction. -/
theorem boundedAccept_iff_run (m : Machine) (c : Config) (clock : Nat) :
    BoundedTableau m c clock true ↔
      ∃ t, t ≤ clock ∧ Run m c t true := by
  constructor
  · rintro ⟨trace, hhead, hbound, hlocal⟩
    exact ⟨trace.length, hbound,
      (localTrace_iff_run m c trace.length true).mp ⟨trace, hhead, rfl, hlocal⟩⟩
  · rintro ⟨t, hbound, hr⟩
    obtain ⟨trace, hhead, hlen, hlocal⟩ :=
      (localTrace_iff_run m c t true).mpr hr
    exact ⟨trace, hhead, hlen ▸ hbound, hlocal⟩

/-! Small semantic regressions for degenerate and malformed tableaux. -/

def acceptMachine : Machine := ⟨[[.halt true]]⟩
def loopMachine : Machine := ⟨[[.move 0 .blank .right]]⟩
def moveThenAccept : Machine :=
  ⟨[[.move 1 .blank .stay],
    [.halt true, .halt true, .halt true, .halt true]]⟩
def goodSuccessor : Config := ⟨1, [], .blank, []⟩
def wrongSuccessor : Config := ⟨1, [], .one, []⟩

theorem empty_rejected (m : Machine) (b : Bool) : ¬ LocalTrace m b [] := by
  intro h
  exact h

theorem singleton_accepts : LocalTrace acceptMachine true [initial []] := by
  rfl

theorem wrong_answer_rejected : ¬ LocalTrace acceptMachine false [initial []] := by
  simp [LocalTrace, acceptMachine, step, Machine.instruction, initial,
    initialSymbols, Symbol.index]

theorem premature_halt_rejected :
    ¬ LocalTrace acceptMachine true [initial [], initial []] := by
  simp [LocalTrace, acceptMachine, step, Machine.instruction, initial,
    initialSymbols, Symbol.index]

theorem missing_halt_rejected : ¬ LocalTrace loopMachine true [initial []] := by
  simp [LocalTrace, loopMachine, step, Machine.instruction, initial,
    initialSymbols, Symbol.index]

theorem two_step_accepts :
    LocalTrace moveThenAccept true [initial [], goodSuccessor] := by
  exact ⟨rfl, rfl⟩

theorem wrong_successor_halts : step moveThenAccept wrongSuccessor = .inl true := by
  rfl

/-- The final configuration accepts, but its predecessor cannot reach it. -/
theorem wrong_successor_rejected :
    ¬ LocalTrace moveThenAccept true [initial [], wrongSuccessor] := by
  simp [LocalTrace, moveThenAccept, wrongSuccessor, step, Machine.instruction,
    initial, initialSymbols, Symbol.index, moveHead]

theorem zero_clock_rejected (m : Machine) (c : Config) :
    ¬ BoundedTableau m c 0 true := by
  rintro ⟨trace, hhead, hbound, _⟩
  cases trace with
  | nil => simp at hhead
  | cons _ _ => simp at hbound

theorem one_clock_accepts : BoundedTableau acceptMachine (initial []) 1 true := by
  exact ⟨[initial []], rfl, by decide, singleton_accepts⟩

end Issue568.Tableau
