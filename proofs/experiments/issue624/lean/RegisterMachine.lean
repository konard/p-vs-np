import proofs.experiments.issue624.lean.UnaryCounter

/-! Home-preserving register primitives. Generated tables come from
`experiments/issue624/generate_register_machine.py`; each execution step is
charged in the existing `Reaches` semantics. Home is the unique blank before
the input and delimited registers/output. -/
namespace Issue624.RegisterMachine
open Complexity Issue532.Machines

def seekRows (base : Nat) : Nat → List (List Instruction)
  | 0 => []
  | k + 1 => [.halt false, .move base .zero .right, .move base .one .right, .move (base + 1) .separator .right] :: seekRows (base + 1) k

def seek (slot : Nat) : Machine := ⟨[.move 1 .blank .right, .halt false, .halt false, .halt false] :: seekRows 1 slot⟩

def grow (b : Bool) : Machine := ⟨[
  [.halt false, .move 0 .zero .right, .move 0 .one .right, .move 3 (.ofBool b) .right],
  [.move 4 .zero .stay, .move 1 .zero .right, .move 2 .zero .right, .move 3 .zero .right],
  [.move 4 .one .stay, .move 1 .one .right, .move 2 .one .right, .move 3 .one .right],
  [.move 4 .separator .stay, .move 1 .separator .right, .move 2 .separator .right, .move 3 .separator .right],
  [.move 5 .blank .stay, .move 4 .zero .left, .move 4 .one .left, .move 4 .separator .left]]⟩

def push (slot : Nat) (b : Bool) : Machine := appendMachine (seek slot) (grow b)

def pushWord (slot : Nat) : Word → Machine
  | [] => ⟨[]⟩
  | b :: w => appendMachine (push slot b) (pushWord slot w)
def incr (slot count : Nat) : Machine := pushWord (slot+1) (List.replicate count true)
def emitConst (registers : Nat) (w : Word) : Machine := pushWord (registers+1) w

def deleteFirst : Machine := ⟨[
  [.halt false, .halt false, .move 1 .blank .right, .move 8 .separator .left],
  [.move 7 .blank .left, .move 2 .zero .left, .move 3 .one .left, .move 4 .separator .left],
  [.move 5 .zero .right, .halt false, .halt false, .halt false],
  [.move 5 .one .right, .halt false, .halt false, .halt false],
  [.move 5 .separator .right, .halt false, .halt false, .halt false],
  [.halt false, .move 1 .blank .right, .move 1 .blank .right, .move 1 .blank .right],
  [.move 9 .blank .stay, .move 6 .zero .left, .move 6 .one .left, .move 6 .separator .left],
  [.move 6 .blank .left, .halt false, .halt false, .halt false],
  [.move 10 .blank .stay, .move 8 .zero .left, .move 8 .one .left, .move 8 .separator .left]]⟩
def pop (slot : Nat) : Machine := appendMachine (seek slot) deleteFirst

def clearTarget (slot q : Nat) : Nat :=
  if q < (pop slot).program.length then q else
  if q = (pop slot).program.length then 0 else (pop slot).program.length

def clear (slot : Nat) : Machine := retargetMachine (pop slot) (clearTarget slot)

def repeatHeadTarget (slot : Nat) (body : Machine) (q : Nat) : Nat :=
  if q < (pop slot).program.length + 1 then q else
    (pop slot).program.length + body.program.length + 2
def repeatHead (slot : Nat) (body : Machine) : Machine :=
  retargetMachine (pop slot) (repeatHeadTarget slot body)
def repeatJump : Machine := ⟨[[.move 1 .blank .stay, .halt false, .halt false, .halt false]]⟩
def repeatBase (slot : Nat) (body : Machine) : Machine :=
  appendMachine (repeatHead slot body) (appendMachine body repeatJump)
def repeatMachine (slot : Nat) (body : Machine) : Machine :=
  retargetMachine (repeatBase slot body) (clearTargetFor (repeatBase slot body).program.length)
where clearTargetFor size q := if q < size then q else if q = size then 0 else size

-- END GENERATED REGISTER TABLES

def tape (blocks : List Word) : List Symbol :=
  blocks.flatMap (fun w => w.map Symbol.ofBool ++ [.separator])
def home (q : Nat) (blocks : List Word) : Config := ⟨q, [], .blank, tape blocks⟩
def pushTime (blocks : List Word) : Nat := 2 * (tape blocks).length + 4

@[simp] theorem tape_append (pre post : List Word) :
    tape (pre ++ post) = tape pre ++ tape post := by simp [tape]
@[simp] theorem tape_cons (w : Word) (post : List Word) :
    tape (w :: post) = w.map Symbol.ofBool ++ .separator :: tape post := by simp [tape]
theorem tape_nonblank (blocks : List Word) : ∀ a ∈ tape blocks, a ≠ .blank := by
  intro a ha
  obtain ⟨w, _, ha⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h
    cases b <;> decide
  · simp at h; subst a; decide

@[simp] theorem seekRows_length (base slot : Nat) : (seekRows base slot).length = slot := by
  induction slot generalizing base <;> simp_all [seekRows]
@[simp] theorem seek_states (slot : Nat) : (seek slot).program.length = slot + 1 := by
  simp [seek]
@[simp] theorem push_states (slot : Nat) (b : Bool) : (push slot b).program.length = slot + 6 := by
  simp [push, appendMachine, seek, grow]

theorem seekRows_get (base count i : Nat) (hi : i < count) :
    (seekRows base count)[i]? = some
      [.halt false, .move (base+i) .zero .right, .move (base+i) .one .right,
        .move (base+i+1) .separator .right] := by
  induction count generalizing base i with
  | zero => omega
  | succ count ih =>
    cases i with
    | zero => simp [seekRows]
    | succ i => simpa [seekRows, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (ih (base+1) i (by omega))

theorem seek_instruction (slot i : Nat) (hi : i < slot) (a : Symbol) :
    (seek slot).instruction (i+1) a =
      match a with
      | .blank => .halt false
      | .zero => .move (i+1) .zero .right
      | .one => .move (i+1) .one .right
      | .separator => .move (i+2) .separator .right := by
  have hrow : (seek slot).program[i+1]? = some
      [.halt false, .move (1+i) .zero .right, .move (1+i) .one .right,
        .move (1+i+1) .separator .right] := by
    simpa [seek] using seekRows_get 1 slot i hi
  unfold Machine.instruction
  rw [hrow]
  cases a <;> simp [Symbol.index] <;> omega

theorem seek_scan (slot off : Nat) (pre : List Word) (l tail : List Symbol)
    (h : off + pre.length ≤ slot) :
    Reaches (seek slot) (scanConfig (off+1) l (tape pre ++ tail)) (tape pre).length
      (scanConfig (off+1+pre.length) ((tape pre).reverse ++ l) tail) := by
  induction pre generalizing off l with
  | nil => simpa [tape] using Reaches.refl (scanConfig (off+1) l tail)
  | cons w pre ih =>
    have hi : off < slot := by simp at h; omega
    have hs := scan_right (seek slot) (off+1) (w.map Symbol.ofBool) l
      (.separator :: (tape pre ++ tail)) (by
        intro a ha
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
        cases b <;> exact seek_instruction slot off hi _)
    have hsep : step (seek slot)
        ⟨off+1, (w.map Symbol.ofBool).reverse ++ l, .separator, tape pre ++ tail⟩ =
        .inr (scanConfig (off+2) (.separator :: ((w.map Symbol.ofBool).reverse ++ l))
          (tape pre ++ tail)) := by
      unfold step
      rw [seek_instruction slot off hi]
      cases tape pre ++ tail <;> rfl
    have hr := ih (off+1) (.separator :: ((w.map Symbol.ofBool).reverse ++ l)) (by simp at h ⊢; omega)
    have hall := hs.trans (Reaches.next hsep hr)
    simpa [tape_cons, List.append_assoc, scanConfig, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hall

theorem seek_reaches (pre : List Word) (tail : List Symbol) :
    Reaches (seek pre.length) ⟨0, [], .blank, tape pre ++ tail⟩ (1+(tape pre).length)
      (scanConfig (seek pre.length).program.length ((tape pre).reverse ++ [.blank]) tail) := by
  have hs : step (seek pre.length) ⟨0, [], .blank, tape pre ++ tail⟩ =
      .inr (scanConfig 1 [.blank] (tape pre ++ tail)) := by
    unfold step
    rw [show (seek pre.length).instruction 0 .blank = .move 1 .blank .right by rfl]
    cases tape pre ++ tail <;> rfl
  simpa [seek_states, Nat.add_comm] using
    Reaches.next hs (seek_scan pre.length 0 pre [.blank] tail (by omega))

def carryState : Symbol → Nat
  | .zero => 1 | .one => 2 | .separator => 3 | .blank => 1

theorem grow_carry_instruction (b : Bool) (a : Symbol) (ha : a ≠ .blank) (s : Symbol) :
    (grow b).instruction (carryState a) s =
      match s with
      | .blank => .move 4 a .stay
      | _ => .move (carryState s) a .right := by
  cases a <;> cases s <;> simp_all [carryState, grow, Machine.instruction, Symbol.index]

theorem shift_reaches (b : Bool) (a : Symbol) (xs l : List Symbol)
    (ha : a ≠ .blank) (hx : ∀ s ∈ xs, s ≠ .blank) :
    Reaches (grow b) (scanConfig (carryState a) l xs) (xs.length+1)
      (scanLeftConfig 4 [] ((a :: xs).reverse ++ l)) := by
  induction xs generalizing a l with
  | nil =>
    apply Reaches.next (c' := ⟨4, l, a, []⟩)
    · simp [scanConfig, step, grow_carry_instruction b a ha .blank, moveHead]
    · exact Reaches.refl _
  | cons s xs ih =>
    have hs : step (grow b) (scanConfig (carryState a) l (s :: xs)) =
        .inr (scanConfig (carryState s) (a :: l) xs) := by
      simp only [scanConfig, step, grow_carry_instruction b a ha s]
      cases s <;> simp_all [moveHead, scanConfig] <;> cases xs <;> rfl
    have hr := ih s (a :: l) (hx s (by simp)) (fun c hc => hx c (by simp [hc]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Reaches.next hs hr

theorem grow_reaches (b : Bool) (p : List Symbol) (w : Word) (r : List Symbol)
    (hp : ∀ a ∈ p, a ≠ .blank) (hr : ∀ a ∈ r, a ≠ .blank) :
    Reaches (grow b) (scanConfig 0 (p.reverse ++ [.blank])
      (w.map Symbol.ofBool ++ .separator :: r))
      (p.length + 2*w.length + 2*r.length + 5)
      ⟨5, [], .blank, p ++ (w ++ [b]).map Symbol.ofBool ++ .separator :: r⟩ := by
  let l := (w.map Symbol.ofBool).reverse ++ p.reverse ++ [.blank]
  let out := p ++ (w ++ [b]).map Symbol.ofBool ++ .separator :: r
  have hs := scan_right (grow b) 0 (w.map Symbol.ofBool) (p.reverse ++ [.blank])
    (.separator :: r) (by
      intro a ha
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
      cases c <;> rfl)
  have hi : step (grow b) ⟨0, l, .separator, r⟩ =
      .inr (scanConfig 3 (.ofBool b :: l) r) := by cases r <;> rfl
  have hc := shift_reaches b .separator r (.ofBool b :: l) (by decide) hr
  have hc' : Reaches (grow b) (scanConfig 3 (.ofBool b :: l) r) (r.length+1)
      (scanLeftConfig 4 [] (out.reverse ++ [.blank])) := by
    simpa [carryState, out, l, List.reverse_append, List.map_append, List.append_assoc] using hc
  have hout : ∀ a ∈ out, a ≠ .blank := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hp a h
      · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
        cases c <;> decide
    · rcases List.mem_cons.mp h with h | h
      · subst a; decide
      · exact hr a h
  have hb := scan_left (grow b) 4 out.reverse [] [.blank] (by
    intro a ha
    have ha' := hout a (List.mem_reverse.mp ha)
    cases a <;> simp_all [grow, Machine.instruction, Symbol.index])
  have hend : step (grow b) ⟨4, [], .blank, out⟩ = .inr ⟨5, [], .blank, out⟩ := rfl
  have hb' : Reaches (grow b) (scanLeftConfig 4 [] (out.reverse ++ [.blank])) out.length
      ⟨4, [], .blank, out⟩ := by simpa [scanLeftConfig] using hb
  have hs' : Reaches (grow b) (scanConfig 0 (p.reverse ++ [.blank])
      (w.map Symbol.ofBool ++ .separator :: r)) w.length ⟨0, l, .separator, r⟩ := by
    simpa [l, scanConfig, List.append_assoc] using hs
  have hall := hs'.trans (Reaches.next hi (hc'.trans (hb'.trans (Reaches.next hend (Reaches.refl _)))))
  simpa [out, l, List.append_assoc, Nat.two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hall

theorem push_reaches (pre post : List Word) (w : Word) (b : Bool) :
    Reaches (push pre.length b) (home 0 (pre ++ w :: post))
      (pushTime (pre ++ w :: post))
      (home (push pre.length b).program.length (pre ++ (w ++ [b]) :: post)) := by
  have hs := reaches_append (grow b) (seek_reaches pre (w.map Symbol.ofBool ++ .separator :: tape post))
  have hg := reaches_append_right (seek pre.length)
    (grow_reaches b (tape pre) w (tape post) (tape_nonblank pre) (tape_nonblank post))
  have hg' : Reaches (push pre.length b)
      (scanConfig (seek pre.length).program.length ((tape pre).reverse ++ [.blank])
        (w.map Symbol.ofBool ++ .separator :: tape post))
      ((tape pre).length + 2*w.length + 2*(tape post).length + 5)
      (home (push pre.length b).program.length (pre ++ (w ++ [b]) :: post)) := by
    have hh (q : Nat) (l xs : List Symbol) :
        shiftConfig q (scanConfig 0 l xs) = scanConfig q l xs := by cases xs <;> simp [shiftConfig, scanConfig]
    rw [hh] at hg
    have he : 5 + (seek pre.length).program.length = (push pre.length b).program.length := by
      simp; omega
    simpa only [shiftConfig, he, home, tape_append, tape_cons, push,
      List.map_append, List.map_cons, List.map_nil, List.cons_append, List.append_assoc] using hg
  have hall := hs.trans hg'
  have ht : pushTime (pre ++ w :: post) =
      1 + (tape pre).length + ((tape pre).length + 2*w.length + 2*(tape post).length + 5) := by
    simp [pushTime, tape_append, tape_cons, Nat.two_mul]
    omega
  rw [ht]
  simpa only [home, tape_append, tape_cons, List.append_assoc, push] using hall

def wordTime (count size : Nat) : Nat := count * (2*size + count + 3)
def emissionPolynomial : Polynomial := ⟨3, 2⟩

@[simp] theorem pushWord_states (slot : Nat) (w : Word) :
    (pushWord slot w).program.length = (slot+6)*w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [pushWord, appendMachine, ih, Nat.mul_add, Nat.add_comm]

theorem wordTime_succ (count size : Nat) :
    wordTime (count+1) size = 2*size+4 + wordTime count (size+1) := by
  simp [wordTime, Nat.mul_add, Nat.add_mul]; omega

theorem pushWord_reaches (pre post : List Word) (old w : Word) :
    Reaches (pushWord pre.length w) (home 0 (pre ++ old :: post))
      (wordTime w.length (tape (pre ++ old :: post)).length)
      (home (pushWord pre.length w).program.length (pre ++ (old ++ w) :: post)) := by
  induction w generalizing old with
  | nil => simpa [pushWord, wordTime] using Reaches.refl (home 0 (pre ++ old :: post))
  | cons b w ih =>
    have hp := reaches_append (pushWord pre.length w) (push_reaches pre post old b)
    have hw := reaches_append_right (push pre.length b) (ih (old ++ [b]))
    have hf : (pushWord pre.length (b :: w)).program.length =
        (pushWord pre.length w).program.length + (push pre.length b).program.length := by
      simp only [pushWord, appendMachine, List.length_append, List.length_map]; omega
    have hw' : Reaches (pushWord pre.length (b :: w))
        (home (push pre.length b).program.length (pre ++ (old ++ [b]) :: post))
        (wordTime w.length (tape (pre ++ (old ++ [b]) :: post)).length)
        (home (pushWord pre.length (b :: w)).program.length (pre ++ (old ++ b :: w) :: post)) := by
      rw [hf]
      simpa [home, shiftConfig, pushWord, List.append_assoc] using hw
    have ht : wordTime (b :: w).length (tape (pre ++ old :: post)).length =
        pushTime (pre ++ old :: post) + wordTime w.length
          (tape (pre ++ (old ++ [b]) :: post)).length := by
      rw [List.length_cons, wordTime_succ]
      simp [pushTime, tape_append, tape_cons, Nat.add_assoc]
    rw [ht]
    exact hp.trans hw'

theorem wordTime_polynomial (count size : Nat) :
    wordTime count size ≤ emissionPolynomial.eval (size+count) := by
  have hc : count ≤ size+count+1 := by omega
  have hf : 2*size+count+3 ≤ 3*(size+count+1) := by omega
  have h := Nat.mul_le_mul hc hf
  simpa [wordTime, emissionPolynomial, Polynomial.eval, Nat.pow_two,
    Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using h

structure State where
  regs : List Nat
  out : Word
  deriving Repr

def regWords (regs : List Nat) : List Word := regs.map (fun n => List.replicate n true)
def blocks (x : Word) (st : State) : List Word := x :: regWords st.regs ++ [st.out]
def encode (q : Nat) (x : Word) (st : State) : Config := home q (blocks x st)

/-- Append a static number of ticks to any unary register, retaining input,
other registers, and output. Registers are zero-based after the input block. -/
theorem incr_reaches (x : Word) (pre post : List Nat) (value count : Nat) (out : Word) :
    Reaches (incr pre.length count) (encode 0 x ⟨pre ++ value :: post, out⟩)
      (wordTime count (tape (blocks x ⟨pre ++ value :: post, out⟩)).length)
      (encode (incr pre.length count).program.length x ⟨pre ++ (value+count) :: post, out⟩) := by
  have h := pushWord_reaches (x :: regWords pre) (regWords post ++ [out])
    (List.replicate value true) (List.replicate count true)
  simpa [incr, encode, blocks, regWords, List.replicate_append_replicate, List.append_assoc,
    Nat.add_comm] using h

/-- Append fixed bits to the output block through the same insertion table. -/
theorem emitConst_reaches (x : Word) (st : State) (w : Word) :
    Reaches (emitConst st.regs.length w) (encode 0 x st)
      (wordTime w.length (tape (blocks x st)).length)
      (encode (emitConst st.regs.length w).program.length x ⟨st.regs, st.out ++ w⟩) := by
  have h := pushWord_reaches (x :: regWords st.regs) [] st.out w
  simpa [emitConst, encode, blocks, regWords] using h

/-- The currently certified straight-line register language. Dynamic operations
and loops can extend this compiler without re-proving sequential embedding. -/
inductive Prog where
  | empty
  | increment (slot count : Nat)
  | emit (w : Word)
  | seq (first second : Prog)
  deriving Repr

def WellFormed (registers : Nat) : Prog → Prop
  | .empty => True
  | .increment slot _ => slot < registers
  | .emit _ => True
  | .seq first second => WellFormed registers first ∧ WellFormed registers second

def wellFormedDecidable (k : Nat) : (p : Prog) → Decidable (WellFormed k p)
  | .empty => isTrue trivial
  | .increment slot _ => inferInstanceAs (Decidable (slot < k))
  | .emit _ => isTrue trivial
  | .seq first second => @instDecidableAnd (WellFormed k first) (WellFormed k second)
      (wellFormedDecidable k first) (wellFormedDecidable k second)

instance (k : Nat) (p : Prog) : Decidable (WellFormed k p) := wellFormedDecidable k p

def incrementRegs : Nat → Nat → List Nat → List Nat
  | _, _, [] => []
  | 0, count, value :: rest => (value+count) :: rest
  | slot+1, count, value :: rest => value :: incrementRegs slot count rest

def runProg : Prog → State → State
  | .empty, st => st
  | .increment slot count, st => ⟨incrementRegs slot count st.regs, st.out⟩
  | .emit w, st => ⟨st.regs, st.out ++ w⟩
  | .seq first second, st => runProg second (runProg first st)

def cost (x : Word) : Prog → State → Nat
  | .empty, _ => 0
  | .increment _ count, st => wordTime count (tape (blocks x st)).length
  | .emit w, st => wordTime w.length (tape (blocks x st)).length
  | .seq first second, st => cost x first st + cost x second (runProg first st)

def compile (registers : Nat) : Prog → Machine
  | .empty => ⟨[]⟩
  | .increment slot count => incr slot count
  | .emit w => emitConst registers w
  | .seq first second => appendMachine (compile registers first) (compile registers second)

theorem incrementRegs_length (slot count : Nat) (values : List Nat) :
    (incrementRegs slot count values).length = values.length := by
  induction values generalizing slot with
  | nil => simp [incrementRegs]
  | cons value rest ih => cases slot <;> simp [incrementRegs, ih]

theorem incrementRegs_split (pre post : List Nat) (value count : Nat) :
    incrementRegs pre.length count (pre ++ value :: post) = pre ++ (value+count) :: post := by
  induction pre <;> simp_all [incrementRegs]

theorem register_decomposition (values : List Nat) (slot : Nat) (h : slot < values.length) :
    ∃ pre value post, pre.length = slot ∧ values = pre ++ value :: post := by
  induction values generalizing slot with
  | nil => simp at h
  | cons value rest ih =>
    cases slot with
    | zero => exact ⟨[], value, rest, rfl, rfl⟩
    | succ slot =>
      obtain ⟨pre, v, post, hp, hr⟩ := ih slot (by simpa using h)
      exact ⟨value :: pre, v, post, by simp [hp], by simp [hr]⟩

theorem runProg_regs_length (p : Prog) (st : State) :
    (runProg p st).regs.length = st.regs.length := by
  induction p generalizing st with
  | empty => rfl
  | increment slot count => exact incrementRegs_length slot count st.regs
  | emit w => rfl
  | seq first second ihf ihs =>
    simp only [runProg, ihs, ihf]

theorem increment_state_reaches (x : Word) (st : State) (slot count : Nat)
    (h : slot < st.regs.length) :
    Reaches (incr slot count) (encode 0 x st)
      (wordTime count (tape (blocks x st)).length)
      (encode (incr slot count).program.length x (runProg (.increment slot count) st)) := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot h
  subst values; subst slot
  simpa only [runProg, incrementRegs_split] using incr_reaches x pre post value count out

/-- Every generated table is fixed by the program and register count, with
all tape work accounted for in the shared finite-machine semantics. -/
theorem compile_reaches (x : Word) (k : Nat) (p : Prog) (st : State)
    (hp : WellFormed k p) (hs : st.regs.length = k) :
    Reaches (compile k p) (encode 0 x st) (cost x p st)
      (encode (compile k p).program.length x (runProg p st)) := by
  induction p generalizing st with
  | empty => exact Reaches.refl _
  | increment slot count => exact increment_state_reaches x st slot count (by simpa [WellFormed, hs] using hp)
  | emit w => simpa only [compile, runProg, cost, hs] using emitConst_reaches x st w
  | seq first second ihf ihs =>
    have hf := reaches_append (compile k second) (ihf st hp.1 hs)
    have hs' : (runProg first st).regs.length = k := (runProg_regs_length first st).trans hs
    have hsecond := reaches_append_right (compile k first) (ihs (runProg first st) hp.2 hs')
    have hsecond' : Reaches (compile k (.seq first second))
        (encode (compile k first).program.length x (runProg first st))
        (cost x second (runProg first st))
        (encode (compile k (.seq first second)).program.length x (runProg (.seq first second) st)) := by
      simpa [compile, encode, home, shiftConfig, appendMachine, runProg,
        Nat.add_comm] using hsecond
    exact hf.trans hsecond'

def growth : Prog → Nat
  | .empty => 0
  | .increment _ count => count
  | .emit w => w.length
  | .seq first second => growth first + growth second

theorem tape_regWords_length (values : List Nat) :
    (tape (regWords values)).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa [regWords, tape, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (fun n => value + 1 + n) ih

theorem blocks_length (x : Word) (st : State) :
    (tape (blocks x st)).length = x.length + st.regs.sum + st.regs.length + st.out.length + 2 := by
  simp only [blocks, tape_cons, tape_append, List.length_append, List.length_map,
    List.length_cons, tape_regWords_length]
  simp [tape]; omega

theorem incrementRegs_sum (slot count : Nat) (values : List Nat) (h : slot < values.length) :
    (incrementRegs slot count values).sum = values.sum + count := by
  induction values generalizing slot with
  | nil => simp at h
  | cons value rest ih =>
    cases slot with
    | zero => simp [incrementRegs, Nat.add_assoc, Nat.add_comm]
    | succ slot => simp [incrementRegs, ih slot (by simpa using h), Nat.add_assoc]

theorem runProg_tape_length (x : Word) (k : Nat) (p : Prog) (st : State)
    (hp : WellFormed k p) (hs : st.regs.length = k) :
    (tape (blocks x (runProg p st))).length = (tape (blocks x st)).length + growth p := by
  induction p generalizing st with
  | empty => simp [runProg, growth]
  | increment slot count =>
    have h : slot < st.regs.length := by simpa [WellFormed, hs] using hp
    simp [blocks_length, runProg, growth, incrementRegs_length, incrementRegs_sum slot count st.regs h,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | emit w => simp [blocks_length, runProg, growth, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | seq first second ihf ihs =>
    have hs' : (runProg first st).regs.length = k := (runProg_regs_length first st).trans hs
    simpa [runProg, growth, Nat.add_assoc] using
      (ihs (runProg first st) hp.2 hs').trans (congrArg (fun n => n + growth second) (ihf st hp.1 hs))

theorem wordTime_add (first second size : Nat) :
    wordTime (first+second) size = wordTime first size + wordTime second (size+first) := by
  simp only [wordTime, Nat.two_mul, Nat.mul_add, Nat.add_mul]
  rw [Nat.mul_comm second first]; omega

theorem cost_eq_wordTime (x : Word) (k : Nat) (p : Prog) (st : State)
    (hp : WellFormed k p) (hs : st.regs.length = k) :
    cost x p st = wordTime (growth p) (tape (blocks x st)).length := by
  induction p generalizing st with
  | empty => simp [cost, growth, wordTime]
  | increment slot count => rfl
  | emit w => rfl
  | seq first second ihf ihs =>
    have hs' : (runProg first st).regs.length = k := (runProg_regs_length first st).trans hs
    rw [cost, ihf st hp.1 hs, ihs (runProg first st) hp.2 hs',
      runProg_tape_length x k first st hp.1 hs, growth, wordTime_add]

theorem cost_polynomial (x : Word) (k : Nat) (p : Prog) (st : State)
    (hp : WellFormed k p) (hs : st.regs.length = k) :
    cost x p st ≤ emissionPolynomial.eval ((tape (blocks x st)).length + growth p) := by
  rw [cost_eq_wordTime x k p st hp hs]
  exact wordTime_polynomial _ _


@[simp] theorem pop_states (slot : Nat) : (pop slot).program.length = slot+10 := by
  simp [pop, appendMachine, deleteFirst]
@[simp] theorem clear_states (slot : Nat) : (clear slot).program.length = (pop slot).program.length := by
  simp [clear, retargetMachine]

def deleteCarry (a : Symbol) : Nat :=
  match a with | .zero => 2 | .one => 3 | .separator => 4 | .blank => 2

theorem delete_shift (xs l : List Symbol) (hx : ∀ a ∈ xs, a ≠ .blank) :
    Reaches deleteFirst (scanConfig 1 (.blank :: l) xs) (3*xs.length+2)
      (scanLeftConfig 6 [.blank, .blank] (xs.reverse ++ l)) := by
  induction xs generalizing l with
  | nil =>
    have h1 : step deleteFirst (scanConfig 1 (.blank :: l) []) =
        .inr ⟨7, l, .blank, [.blank]⟩ := rfl
    have h2 : step deleteFirst ⟨7, l, .blank, [.blank]⟩ =
        .inr (scanLeftConfig 6 [.blank, .blank] l) := by cases l <;> rfl
    exact Reaches.next h1 (Reaches.next h2 (Reaches.refl _))
  | cons a xs ih =>
    have ha := hx a (by simp)
    have h1 : step deleteFirst (scanConfig 1 (.blank :: l) (a :: xs)) =
        .inr ⟨deleteCarry a, l, .blank, a :: xs⟩ := by cases a <;> first | contradiction | rfl
    have h2 : step deleteFirst ⟨deleteCarry a, l, .blank, a :: xs⟩ =
        .inr ⟨5, a :: l, a, xs⟩ := by cases a <;> first | contradiction | rfl
    have h3 : step deleteFirst ⟨5, a :: l, a, xs⟩ =
        .inr (scanConfig 1 (.blank :: a :: l) xs) := by
      cases a <;> first | contradiction | (cases xs <;> rfl)
    have h := Reaches.next h1 (Reaches.next h2 (Reaches.next h3
      (ih (a :: l) (fun s hs => hx s (by simp [hs])))))
    simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc] using h

theorem delete_positive (p xs : List Symbol)
    (hp : ∀ a ∈ p, a ≠ .blank) (hx : ∀ a ∈ xs, a ≠ .blank) :
    Reaches deleteFirst (scanConfig 0 (p.reverse ++ [.blank]) (.one :: xs))
      (p.length+4*xs.length+4)
      ⟨9, [], .blank, p ++ xs ++ [.blank, .blank]⟩ := by
  have hstart : step deleteFirst (scanConfig 0 (p.reverse ++ [.blank]) (.one :: xs)) =
      .inr (scanConfig 1 (.blank :: (p.reverse ++ [.blank])) xs) := by cases xs <;> rfl
  have hs := delete_shift xs (p.reverse ++ [.blank]) hx
  have hb := scan_left deleteFirst 6 (p ++ xs).reverse [.blank, .blank] [.blank] (by
    intro a ha
    have ha' : a ≠ .blank := by
      rcases List.mem_append.mp (List.mem_reverse.mp ha) with h | h
      · exact hp a h
      · exact hx a h
    cases a <;> simp_all [deleteFirst, Machine.instruction, Symbol.index])
  have hfinish : step deleteFirst ⟨6, [], .blank, p ++ xs ++ [.blank, .blank]⟩ =
      .inr ⟨9, [], .blank, p ++ xs ++ [.blank, .blank]⟩ := rfl
  have hb' : Reaches deleteFirst
      (scanLeftConfig 6 [.blank, .blank] (xs.reverse ++ (p.reverse ++ [.blank])))
      (p.length+xs.length) ⟨6, [], .blank, p ++ xs ++ [.blank, .blank]⟩ := by
    simpa only [List.length_reverse, List.length_append, List.reverse_reverse,
      List.reverse_append, List.append_assoc, scanLeftConfig, Nat.add_comm] using hb
  rw [show p.length+4*xs.length+4 = ((3*xs.length+2)+(p.length+xs.length+(0+1)))+1 by omega]
  exact Reaches.next hstart (hs.trans (hb'.trans (Reaches.next hfinish (Reaches.refl _))))

theorem delete_empty (p r : List Symbol) (hp : ∀ a ∈ p, a ≠ .blank) :
    Reaches deleteFirst ⟨0, p.reverse ++ [.blank], .separator, r⟩ (p.length+2)
      ⟨10, [], .blank, p ++ .separator :: r⟩ := by
  have hstart : step deleteFirst ⟨0, p.reverse ++ [.blank], .separator, r⟩ =
      .inr (scanLeftConfig 8 (.separator :: r) (p.reverse ++ [.blank])) := by cases p.reverse <;> rfl
  have hb := scan_left deleteFirst 8 p.reverse (.separator :: r) [.blank] (by
    intro a ha
    have hn := hp a (List.mem_reverse.mp ha)
    cases a <;> simp_all [deleteFirst, Machine.instruction, Symbol.index])
  have hf : step deleteFirst ⟨8, [], .blank, p ++ .separator :: r⟩ =
      .inr ⟨10, [], .blank, p ++ .separator :: r⟩ := rfl
  have hb' : Reaches deleteFirst
      (scanLeftConfig 8 (.separator :: r) (p.reverse ++ [.blank])) p.length
      ⟨8, [], .blank, p ++ .separator :: r⟩ := by
    simpa only [List.reverse_reverse, List.length_reverse, scanLeftConfig] using hb
  rw [show p.length+2 = (p.length+1)+1 by omega]
  exact Reaches.next hstart (hb'.trans (Reaches.next hf (Reaches.refl _)))

theorem pop_positive (pre post : List Word) (n : Nat) :
    Reaches (pop pre.length) (home 0 (pre ++ List.replicate (n+1) true :: post))
      (2*(tape pre).length+4*(n+1+(tape post).length)+5)
      ⟨(pop pre.length).program.length, [], .blank,
        tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ := by
  let xs := (List.replicate n true).map Symbol.ofBool ++ .separator :: tape post
  have hs := reaches_append deleteFirst (seek_reaches pre (.one :: xs))
  have hd := reaches_append_right (seek pre.length)
    (delete_positive (tape pre) xs (tape_nonblank pre) (by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        cases b <;> decide
      · rcases List.mem_cons.mp h with h | h
        · subst a; decide
        · exact tape_nonblank post a h))
  have hs' : Reaches (pop pre.length) (home 0 (pre ++ List.replicate (n+1) true :: post))
      (1+(tape pre).length) (scanConfig (seek pre.length).program.length
        ((tape pre).reverse ++ [.blank]) (.one :: xs)) := by
    simpa [pop, home, tape_append, tape_cons, List.replicate_succ, xs, Symbol.ofBool] using hs
  have hd' : Reaches (pop pre.length)
      (scanConfig (seek pre.length).program.length ((tape pre).reverse ++ [.blank]) (.one :: xs))
      ((tape pre).length+4*xs.length+4)
      ⟨(pop pre.length).program.length, [], .blank, tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ := by
    simpa [pop, shiftConfig, scanConfig, xs, tape_append, tape_cons, List.append_assoc,
      appendMachine, seek_states, deleteFirst, Nat.add_comm] using hd
  have ht : xs.length = n+1+(tape post).length := by simp [xs]; omega
  rw [ht] at hd'
  rw [show 2*(tape pre).length+4*(n+1+(tape post).length)+5 =
    (1+(tape pre).length)+((tape pre).length+4*(n+1+(tape post).length)+4) by omega]
  exact hs'.trans hd'

theorem pop_empty (pre post : List Word) :
    Reaches (pop pre.length) (home 0 (pre ++ [] :: post)) (2*(tape pre).length+3)
      (home ((pop pre.length).program.length+1) (pre ++ [] :: post)) := by
  have hs := reaches_append deleteFirst (seek_reaches pre (.separator :: tape post))
  have hd := reaches_append_right (seek pre.length)
    (delete_empty (tape pre) (tape post) (tape_nonblank pre))
  have hs' : Reaches (pop pre.length) (home 0 (pre ++ [] :: post))
      (1+(tape pre).length) ⟨(seek pre.length).program.length,
        (tape pre).reverse ++ [.blank], .separator, tape post⟩ := by
    simpa [pop, home, tape_append, tape_cons, scanConfig] using hs
  have hd' : Reaches (pop pre.length) ⟨(seek pre.length).program.length,
        (tape pre).reverse ++ [.blank], .separator, tape post⟩
      ((tape pre).length+2) (home ((pop pre.length).program.length+1) (pre ++ [] :: post)) := by
    have he : 10+(seek pre.length).program.length = (pop pre.length).program.length+1 := by
      rw [seek_states, pop_states]; omega
    simpa only [shiftConfig, he, pop, home, tape_append, tape_cons, List.map_nil,
      List.nil_append, Nat.zero_add] using hd
  rw [show 2*(tape pre).length+3 = (1+(tape pre).length)+((tape pre).length+2) by omega]
  exact hs'.trans hd'

def clearTime (pre value post : Nat) : Nat := value*(2*pre+4*post+2*value+7)+2*pre+3

theorem clearTime_succ (pre value post : Nat) :
    clearTime pre (value+1) post =
      (2*pre+4*(value+1+post)+5) + clearTime pre value post := by
  simp [clearTime, Nat.mul_add, Nat.add_mul]; omega

theorem clearTarget_inside (slot q : Nat) (hq : q < (pop slot).program.length) :
    clearTarget slot q = q := by unfold clearTarget; rw [ite_eq_left hq]

theorem clearTarget_positive (slot : Nat) :
    clearTarget slot (pop slot).program.length = 0 := by simp [clearTarget]

theorem clearTarget_empty (slot : Nat) :
    clearTarget slot ((pop slot).program.length+1) = (pop slot).program.length := by
  simp [clearTarget]

theorem clear_reaches (pre post : List Word) (n : Nat) :
    ∃ c, Reaches (clear pre.length) (home 0 (pre ++ List.replicate n true :: post))
      (clearTime (tape pre).length n (tape post).length) c ∧
      Similar (home (clear pre.length).program.length (pre ++ [] :: post)) c := by
  induction n with
  | zero =>
    have h := retarget_reaches (pop_empty pre post) (clearTarget pre.length)
      (clearTarget_inside pre.length)
    refine ⟨home (clear pre.length).program.length (pre ++ [] :: post), ?_, ?_⟩
    · change Reaches (clear pre.length)
          (home (clearTarget pre.length 0) (pre ++ [] :: post))
          (2*(tape pre).length+3)
          (home (clearTarget pre.length ((pop pre.length).program.length+1)) (pre ++ [] :: post)) at h
      rw [clearTarget_inside pre.length 0 (by simp), clearTarget_empty] at h
      simpa only [clear_states, clearTime, Nat.zero_mul, Nat.zero_add, List.replicate_zero] using h
    · exact ⟨rfl, rfl, rfl, BlankPad.refl _⟩
  | succ n ih =>
    have h := retarget_reaches (pop_positive pre post n) (clearTarget pre.length)
      (clearTarget_inside pre.length)
    have h' : Reaches (clear pre.length)
        (home 0 (pre ++ List.replicate (n+1) true :: post))
        (2*(tape pre).length+4*(n+1+(tape post).length)+5)
        ⟨0, [], .blank, tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ := by
      change Reaches (clear pre.length)
        (home (clearTarget pre.length 0) (pre ++ List.replicate (n+1) true :: post))
        (2*(tape pre).length+4*(n+1+(tape post).length)+5)
        ⟨clearTarget pre.length (pop pre.length).program.length, [], .blank,
          tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ at h
      rwa [clearTarget_inside pre.length 0 (by simp), clearTarget_positive] at h
    obtain ⟨c, hc, hsim⟩ := ih
    have hp : Similar (home 0 (pre ++ List.replicate n true :: post))
        ⟨0, [], .blank, tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ :=
      ⟨rfl, rfl, rfl, ⟨_, 0, 2, by simp [blanks, home], rfl⟩⟩
    obtain ⟨d, hd, hcd⟩ := reaches_of_similar hc hp
    refine ⟨d, ?_, hsim.trans hcd⟩
    rw [clearTime_succ]
    exact h'.trans hd

def clearPolynomial : Polynomial := ⟨10, 2⟩

theorem clearTime_polynomial (pre value post : Nat) :
    clearTime pre value post ≤ clearPolynomial.eval (pre+value+post+1) := by
  let size := pre+value+post+2
  have h1 : value ≤ size := by omega
  have h2 : 2*pre+4*post+2*value+7 ≤ 7*size := by omega
  have h3 : 2*pre+3 ≤ 3*size*size := by
    have h : 2*pre+3 ≤ 3*size := by omega
    exact Nat.le_trans h (Nat.le_mul_of_pos_right _ (by omega))
  have h := Nat.mul_le_mul h1 h2
  have h' : value*(2*pre+4*post+2*value+7)+2*pre+3 ≤ 10*size*size := by
    have hh := Nat.add_le_add h h3
    have he : size*(7*size)+3*size*size = 10*size*size := by
      simp only [Nat.mul_assoc]
      rw [Nat.mul_left_comm size 7 size]
      omega
    rw [he] at hh
    simpa only [Nat.add_assoc] using hh
  simpa [clearTime, clearPolynomial, Polynomial.eval, Nat.pow_two, size, Nat.mul_assoc,
    Nat.add_assoc] using h'


/-- Clear a scratch register before a compiled block. The table depends only
on static register indices and the program; the cleared value is dynamic. -/
def clearThen (slot registers : Nat) (p : Prog) : Machine :=
  appendMachine (clear (slot+1)) (compile registers p)

theorem clear_then_compile_reaches (x : Word) (pre post : List Nat) (value : Nat)
    (out : Word) (k : Nat) (p : Prog) (hp : WellFormed k p)
    (hk : (pre ++ 0 :: post).length = k) :
    ∃ c, Reaches (clearThen pre.length k p) (encode 0 x ⟨pre ++ value :: post, out⟩)
      (clearTime (tape (x :: regWords pre)).length value
        (tape (regWords post ++ [out])).length + cost x p ⟨pre ++ 0 :: post, out⟩) c ∧
      Similar (encode (clearThen pre.length k p).program.length x
        (runProg p ⟨pre ++ 0 :: post, out⟩)) c := by
  obtain ⟨c, hc, hsim⟩ := clear_reaches (x :: regWords pre) (regWords post ++ [out]) value
  have hstart : Reaches (clear (pre.length+1)) (encode 0 x ⟨pre ++ value :: post, out⟩)
      (clearTime (tape (x :: regWords pre)).length value
        (tape (regWords post ++ [out])).length) c := by
    simpa only [encode, blocks, regWords, List.map_append, List.map_cons,
      List.append_assoc, List.cons_append, List.length_cons, List.length_map] using hc
  have hsim' : Similar (encode (clear (pre.length+1)).program.length x
      ⟨pre ++ 0 :: post, out⟩) c := by
    simpa only [encode, blocks, regWords, List.map_append, List.map_cons,
      List.append_assoc, List.cons_append, List.length_cons, List.length_map, List.replicate_zero] using hsim
  have hr := reaches_append_right (clear (pre.length+1))
    (compile_reaches x k p ⟨pre ++ 0 :: post, out⟩ hp hk)
  have hr' : Reaches (clearThen pre.length k p)
      (encode (clear (pre.length+1)).program.length x ⟨pre ++ 0 :: post, out⟩)
      (cost x p ⟨pre ++ 0 :: post, out⟩)
      (encode (clearThen pre.length k p).program.length x
        (runProg p ⟨pre ++ 0 :: post, out⟩)) := by
    simpa [clearThen, encode, home, shiftConfig, appendMachine, Nat.add_comm] using hr
  obtain ⟨d, hd, he⟩ := reaches_of_similar hr' hsim'
  exact ⟨d, (reaches_append (compile k p) hstart).trans hd, he⟩

theorem clear_then_cost_polynomial (x : Word) (pre post : List Nat) (value : Nat)
    (out : Word) (k : Nat) (p : Prog) (hp : WellFormed k p)
    (hk : (pre ++ 0 :: post).length = k) :
    clearTime (tape (x :: regWords pre)).length value
        (tape (regWords post ++ [out])).length + cost x p ⟨pre ++ 0 :: post, out⟩ ≤
      (polyAdd clearPolynomial emissionPolynomial).eval
        ((tape (blocks x ⟨pre ++ value :: post, out⟩)).length + growth p) := by
  let size := (tape (blocks x ⟨pre ++ value :: post, out⟩)).length
  have hsize : (tape (x :: regWords pre)).length + value +
      (tape (regWords post ++ [out])).length + 1 = size := by
    simp only [size, blocks, regWords, List.map_append, List.map_cons, tape_cons,
      tape_append, List.length_append, List.length_map, List.length_cons, List.length_replicate]
    omega
  have hz : (tape (blocks x ⟨pre ++ 0 :: post, out⟩)).length ≤ size := by
    simp [size, blocks_length]
  have hc := clearTime_polynomial (tape (x :: regWords pre)).length value
    (tape (regWords post ++ [out])).length
  have hclear : clearTime (tape (x :: regWords pre)).length value
      (tape (regWords post ++ [out])).length ≤ clearPolynomial.eval (size + growth p) := by
    apply Nat.le_trans hc
    simp only [clearPolynomial, Polynomial.eval]
    exact Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left (by omega) 2)
  have hemit := cost_polynomial x k p ⟨pre ++ 0 :: post, out⟩ hp hk
  have hemit' : cost x p ⟨pre ++ 0 :: post, out⟩ ≤ emissionPolynomial.eval (size + growth p) := by
    apply Nat.le_trans hemit
    simp only [emissionPolynomial, Polynomial.eval]
    exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega) 2)
  exact Nat.le_trans (Nat.add_le_add hclear hemit') (polyAdd_eval _ _ _)

@[simp] theorem repeatHead_states (slot : Nat) (body : Machine) :
    (repeatHead slot body).program.length = (pop slot).program.length := by
  simp [repeatHead, retargetMachine]

@[simp] theorem repeatBase_states (slot : Nat) (body : Machine) :
    (repeatBase slot body).program.length = (pop slot).program.length + body.program.length + 1 := by
  simp [repeatBase, appendMachine, repeatJump, Nat.add_assoc]

@[simp] theorem repeatMachine_states (slot : Nat) (body : Machine) :
    (repeatMachine slot body).program.length = (pop slot).program.length + body.program.length + 1 := by
  simp [repeatMachine, retargetMachine]

theorem repeatHeadTarget_inside (slot : Nat) (body : Machine) (q : Nat)
    (hq : q < (pop slot).program.length) : repeatHeadTarget slot body q = q := by
  unfold repeatHeadTarget
  rw [ite_eq_left (show q < (pop slot).program.length + 1 by omega)]

theorem repeatTarget_inside (slot : Nat) (body : Machine) (q : Nat)
    (hq : q < (repeatBase slot body).program.length) :
    repeatMachine.clearTargetFor (repeatBase slot body).program.length q = q := by
  unfold repeatMachine.clearTargetFor
  rw [ite_eq_left hq]

theorem repeatHeadTarget_positive (slot : Nat) (body : Machine) :
    repeatHeadTarget slot body (pop slot).program.length = (pop slot).program.length := by
  unfold repeatHeadTarget; rw [ite_eq_left (by omega)]
theorem repeatHeadTarget_empty (slot : Nat) (body : Machine) :
    repeatHeadTarget slot body ((pop slot).program.length+1) = (repeatBase slot body).program.length+1 := by
  simp only [repeatHeadTarget, Nat.lt_irrefl, ite_false, repeatBase_states]
theorem repeatTarget_back (slot : Nat) (body : Machine) :
    repeatMachine.clearTargetFor (repeatBase slot body).program.length
      (repeatBase slot body).program.length = 0 := by simp [repeatMachine.clearTargetFor]
theorem repeatTarget_exit (slot : Nat) (body : Machine) :
    repeatMachine.clearTargetFor (repeatBase slot body).program.length
      ((repeatBase slot body).program.length+1) = (repeatMachine slot body).program.length := by
  unfold repeatMachine.clearTargetFor
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [repeatBase_states, repeatMachine_states]

theorem repeat_empty (pre post : List Word) (body : Machine) :
    Reaches (repeatMachine pre.length body) (home 0 (pre ++ [] :: post))
      (2*(tape pre).length+3)
      (home (repeatMachine pre.length body).program.length (pre ++ [] :: post)) := by
  have h := retarget_reaches (pop_empty pre post) (repeatHeadTarget pre.length body)
    (repeatHeadTarget_inside pre.length body)
  have h' := retarget_reaches (reaches_append (appendMachine body repeatJump) h)
    (repeatMachine.clearTargetFor (repeatBase pre.length body).program.length)
    (repeatTarget_inside pre.length body)
  change Reaches (repeatMachine pre.length body) _ _ _ at h'
  simpa only [retargetConfig, home, repeatHeadTarget_inside pre.length body 0 (by simp),
    repeatHeadTarget_empty, repeatTarget_inside pre.length body 0 (by simp), repeatTarget_exit] using h'

theorem repeat_positive (pre post : List Word) (n : Nat) (body : Machine) :
    ∃ c, Reaches (repeatMachine pre.length body)
      (home 0 (pre ++ List.replicate (n+1) true :: post))
      (2*(tape pre).length+4*(n+1+(tape post).length)+5) c ∧
      Similar (home (pop pre.length).program.length (pre ++ List.replicate n true :: post)) c := by
  have h := retarget_reaches (pop_positive pre post n) (repeatHeadTarget pre.length body)
    (repeatHeadTarget_inside pre.length body)
  have h' := retarget_reaches (reaches_append (appendMachine body repeatJump) h)
    (repeatMachine.clearTargetFor (repeatBase pre.length body).program.length)
    (repeatTarget_inside pre.length body)
  refine ⟨⟨(pop pre.length).program.length, [], .blank,
    tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩, ?_, ?_⟩
  · change Reaches (repeatMachine pre.length body) _ _ _ at h'
    simpa only [retargetConfig, home, repeatHeadTarget_inside pre.length body 0 (by simp),
      repeatHeadTarget_positive, repeatTarget_inside pre.length body 0 (by simp),
      repeatTarget_inside pre.length body (pop pre.length).program.length (by simp only [repeatBase_states]; omega)] using h'
  · exact ⟨rfl, rfl, rfl, ⟨_, 0, 2, by simp [home, blanks], rfl⟩⟩

theorem similar_shiftConfig (off : Nat) (c d : Config) (h : Similar c d) :
    Similar (shiftConfig off c) (shiftConfig off d) :=
  ⟨congrArg (fun q => q + off) h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem similar_retargetConfig (target : Nat → Nat) (c d : Config) (h : Similar c d) :
    Similar (retargetConfig target c) (retargetConfig target d) :=
  ⟨congrArg target h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Embed a home-preserving body and charge the explicit backward jump.
The body may leave arbitrary trailing blank padding. -/
theorem repeat_body_reaches (slot : Nat) (body : Machine) (before after : List Word)
    (t : Nat) (c : Config) (hc : Reaches body (home 0 before) t c)
    (hs : Similar (home body.program.length after) c) :
    ∃ d, Reaches (repeatMachine slot body) (home (pop slot).program.length before)
      (t+1) d ∧ Similar (home 0 after) d := by
  let target := repeatMachine.clearTargetFor (repeatBase slot body).program.length
  have h := reaches_append_right (repeatHead slot body) (reaches_append repeatJump hc)
  have h' := retarget_reaches h target (repeatTarget_inside slot body)
  have hs' := similar_retargetConfig target _ _
    (similar_shiftConfig (repeatHead slot body).program.length _ _ hs)
  have hbody : Reaches (repeatMachine slot body) (home (pop slot).program.length before) t
      (retargetConfig target (shiftConfig (repeatHead slot body).program.length c)) := by
    change Reaches (repeatMachine slot body) _ t _ at h'
    simpa only [retargetConfig, shiftConfig, home, Nat.zero_add, repeatHead_states,
      target, repeatTarget_inside slot body (pop slot).program.length (by simp only [repeatBase_states]; omega)] using h'
  have hsim : Similar (home ((pop slot).program.length + body.program.length) after)
      (retargetConfig target (shiftConfig (repeatHead slot body).program.length c)) := by
    simpa [target, retargetConfig, shiftConfig, home, repeatMachine.clearTargetFor,
      repeatHead_states, Nat.add_comm, Nat.add_assoc] using hs'
  have hjump : Reaches (repeatMachine slot body)
      (home ((pop slot).program.length + body.program.length) after) 1 (home 0 after) := by
    apply Reaches.next (t := 0) _ (Reaches.refl _)
    unfold step repeatMachine
    rw [retarget_instruction]
    have hi : (repeatBase slot body).instruction ((pop slot).program.length + body.program.length) .blank =
        .move (repeatBase slot body).program.length .blank .stay := by
      unfold repeatBase
      rw [show (pop slot).program.length + body.program.length =
        body.program.length + (repeatHead slot body).program.length by simp; omega,
        append_instruction_right]
      rw [show body.program.length = 0 + body.program.length by omega, append_instruction_right]
      simp [repeatJump, Machine.instruction, Symbol.index, shiftInstruction, appendMachine,
        Nat.add_assoc, Nat.add_comm]
    simp only [home] at *
    rw [hi]
    simp only [retargetInstruction, repeatTarget_back, moveHead]
  obtain ⟨d, hd, hsd⟩ := reaches_of_similar hjump hsim
  exact ⟨d, hbody.trans hd, hsd⟩

def registerAt (slot : Nat) (st : State) : Nat := st.regs[slot]?.getD 0
def putRegister (slot value : Nat) (st : State) : State := ⟨st.regs.set slot value, st.out⟩

theorem registerAt_split (pre post : List Nat) (value : Nat) (out : Word) :
    registerAt pre.length ⟨pre ++ value :: post, out⟩ = value := by
  simp [registerAt]

theorem putRegister_split (pre post : List Nat) (old value : Nat) (out : Word) :
    putRegister pre.length value ⟨pre ++ old :: post, out⟩ = ⟨pre ++ value :: post, out⟩ := by
  simp [putRegister]

theorem putRegister_length (slot value : Nat) (st : State) :
    (putRegister slot value st).regs.length = st.regs.length := by simp [putRegister]

theorem registerAt_putRegister (slot value : Nat) (st : State) (h : slot < st.regs.length) :
    registerAt slot (putRegister slot value st) = value := by
  simp [registerAt, putRegister, List.getElem?_set_self h]

/-- Restrict a straight-line body's writes so its loop counter is stable. -/
def ReadOnly (slot : Nat) : Prog → Prop
  | .empty => True
  | .increment dest _ => slot ≠ dest
  | .emit _ => True
  | .seq first second => ReadOnly slot first ∧ ReadOnly slot second

theorem incrementRegs_readOnly (slot dest count : Nat) (values : List Nat)
    (h : slot ≠ dest) :
    (incrementRegs dest count values)[slot]?.getD 0 = values[slot]?.getD 0 := by
  induction values generalizing slot dest with
  | nil => simp [incrementRegs]
  | cons value rest ih =>
    cases slot <;> cases dest <;> simp_all [incrementRegs]

theorem runProg_readOnly (slot : Nat) (p : Prog) (st : State) (h : ReadOnly slot p) :
    registerAt slot (runProg p st) = registerAt slot st := by
  induction p generalizing st with
  | empty => rfl
  | increment dest count => exact incrementRegs_readOnly slot dest count st.regs h
  | emit w => rfl
  | seq first second ihf ihs =>
    exact (ihs _ h.2).trans (ihf _ h.1)

def repeatPrefix (x : Word) (slot : Nat) (st : State) : Nat :=
  (tape (x :: regWords (st.regs.take slot))).length
def repeatSuffix (slot : Nat) (st : State) : Nat :=
  (tape (regWords (st.regs.drop (slot+1)) ++ [st.out])).length

theorem repeatPrefix_split (x : Word) (pre post : List Nat) (value : Nat) (out : Word) :
    repeatPrefix x pre.length ⟨pre ++ value :: post, out⟩ = (tape (x :: regWords pre)).length := by
  simp [repeatPrefix]
theorem repeatSuffix_split (pre post : List Nat) (value : Nat) (out : Word) :
    repeatSuffix pre.length ⟨pre ++ value :: post, out⟩ = (tape (regWords post ++ [out])).length := by
  have hd : pre.drop (pre.length+1) = [] := List.drop_eq_nil_iff.mpr (by omega)
  simp [repeatSuffix, List.drop_append, hd]

def repeatRun (slot : Nat) (p : Prog) : Nat → State → State
  | 0, st => st
  | n+1, st => repeatRun slot p n (runProg p (putRegister slot n st))
def repeatCost (x : Word) (slot : Nat) (p : Prog) : Nat → State → Nat
  | 0, st => 2*repeatPrefix x slot st + 3
  | n+1, st =>
    2*repeatPrefix x slot st + 4*(n+1+repeatSuffix slot st) + 5 +
      cost x p (putRegister slot n st) + 1 +
      repeatCost x slot p n (runProg p (putRegister slot n st))

/-- A unary loop's table is fixed by its body and register index. Its dynamic
number of iterations comes from the tape, and every test, deletion, body step
and backward jump is charged. -/
def loopRun (slot : Nat) (runBody : State → State) : Nat → State → State
  | 0, st => st
  | n+1, st => loopRun slot runBody n (runBody (putRegister slot n st))
def loopCost (x : Word) (slot : Nat) (runBody : State → State)
    (bodyCost : State → Nat) : Nat → State → Nat
  | 0, st => 2*repeatPrefix x slot st + 3
  | n+1, st =>
    2*repeatPrefix x slot st + 4*(n+1+repeatSuffix slot st)+5 +
      bodyCost (putRegister slot n st)+1 +
      loopCost x slot runBody bodyCost n (runBody (putRegister slot n st))

/-- Repeat any checked home-preserving body, including another dynamic loop.
The counter must be retained by the body; all body and controller steps count. -/
theorem loop_reaches (x : Word) (k slot : Nat) (body : Machine)
    (runBody : State → State) (bodyCost : State → Nat)
    (hr : ∀ st, (runBody st).regs.length = st.regs.length)
    (hro : ∀ st, registerAt slot (runBody st) = registerAt slot st)
    (hb : ∀ st, st.regs.length = k → ∃ c,
      Reaches body (encode 0 x st) (bodyCost st) c ∧
      Similar (encode body.program.length x (runBody st)) c)
    (hslot : slot < k) (n : Nat) (st : State)
    (hk : st.regs.length = k) (hn : registerAt slot st = n) :
    ∃ c, Reaches (repeatMachine (slot+1) body) (encode 0 x st)
      (loopCost x slot runBody bodyCost n st) c ∧
      Similar (encode (repeatMachine (slot+1) body).program.length x
        (loopRun slot runBody n st)) c := by
  induction n generalizing st with
  | zero =>
    rcases st with ⟨values, out⟩
    obtain ⟨pre, value, post, hpre, hv⟩ := register_decomposition values slot (by change values.length = k at hk; omega)
    subst values; subst slot
    have hv : value = 0 := by simpa only [registerAt_split] using hn
    subst value
    refine ⟨encode (repeatMachine (pre.length+1) body).program.length x
      ⟨pre ++ 0 :: post, out⟩, ?_, ⟨rfl, rfl, rfl, BlankPad.refl _⟩⟩
    simpa only [loopCost, repeatPrefix_split, encode, blocks, regWords, List.map_append,
      List.map_cons, List.replicate_zero, List.length_cons, List.length_map,
      List.append_assoc, List.cons_append] using
      repeat_empty (x :: regWords pre) (regWords post ++ [out]) body
  | succ n ih =>
    rcases st with ⟨values, out⟩
    obtain ⟨pre, value, post, hpre, hv⟩ := register_decomposition values slot (by change values.length = k at hk; omega)
    subst values; subst slot
    have hv : value = n+1 := by simpa only [registerAt_split] using hn
    subst value
    let lower : State := ⟨pre ++ n :: post, out⟩
    let next := runBody lower
    have hl : lower.regs.length = k := by simpa [lower] using hk
    obtain ⟨c, hc, hsim⟩ := repeat_positive (x :: regWords pre)
      (regWords post ++ [out]) n body
    have hc' : Reaches (repeatMachine (pre.length+1) body)
        (encode 0 x ⟨pre ++ (n+1) :: post, out⟩)
        (2*repeatPrefix x pre.length ⟨pre ++ (n+1) :: post, out⟩ +
          4*(n+1+repeatSuffix pre.length ⟨pre ++ (n+1) :: post, out⟩)+5) c := by
      simpa only [repeatPrefix_split, repeatSuffix_split, encode, blocks, regWords,
        List.map_append, List.map_cons, List.append_assoc, List.cons_append,
        List.length_cons, List.length_map] using hc
    have hsim' : Similar (home (pop (pre.length+1)).program.length (blocks x lower)) c := by
      simpa only [lower, blocks, regWords, List.map_append, List.map_cons,
        List.append_assoc, List.cons_append, List.length_cons, List.length_map] using hsim
    obtain ⟨bc, hbc, hbs⟩ := hb lower hl
    obtain ⟨d, hd, hsd⟩ := repeat_body_reaches (pre.length+1) body
      (blocks x lower) (blocks x next) _ _ hbc hbs
    obtain ⟨e, he, hde⟩ := reaches_of_similar hd hsim'
    have heq : registerAt pre.length next = n := by
      rw [hro lower]; exact registerAt_split pre post n out
    obtain ⟨f, hf, hsf⟩ := ih next ((hr lower).trans hl) heq
    obtain ⟨g, hg, hfg⟩ := reaches_of_similar hf (hsd.trans hde)
    refine ⟨g, ?_, ?_⟩
    · simpa only [loopCost, repeatRun, putRegister_split, Nat.add_assoc,
        lower, next] using hc'.trans (he.trans hg)
    · simpa only [loopRun, putRegister_split, lower, next] using hsf.trans hfg
theorem loopRun_repeat (slot : Nat) (p : Prog) (n : Nat) (st : State) :
    loopRun slot (runProg p) n st = repeatRun slot p n st := by
  induction n generalizing st <;> simp_all [loopRun, repeatRun]
theorem loopCost_repeat (x : Word) (slot : Nat) (p : Prog) (n : Nat) (st : State) :
    loopCost x slot (runProg p) (cost x p) n st = repeatCost x slot p n st := by
  induction n generalizing st <;> simp_all [loopCost, repeatCost]

theorem repeat_compile_reaches (x : Word) (k slot : Nat) (p : Prog)
    (hp : WellFormed k p) (hro : ReadOnly slot p) (hslot : slot < k)
    (n : Nat) (st : State) (hk : st.regs.length = k) (hn : registerAt slot st = n) :
    ∃ c, Reaches (repeatMachine (slot+1) (compile k p)) (encode 0 x st)
      (repeatCost x slot p n st) c ∧
      Similar (encode (repeatMachine (slot+1) (compile k p)).program.length x
        (repeatRun slot p n st)) c := by
  have h := loop_reaches x k slot (compile k p) (runProg p) (cost x p)
    (runProg_regs_length p) (fun st => runProg_readOnly slot p st hro)
    (fun st hk => ⟨_, compile_reaches x k p st hp hk,
      ⟨rfl, rfl, rfl, BlankPad.refl _⟩⟩) hslot n st hk hn
  simpa only [loopRun_repeat, loopCost_repeat] using h

/-- Emit the repository's two true bits per unary unit, using a register on
the tape rather than an input-dependent instruction table. The counter is
consumed; a caller that needs it again must copy it into scratch first. -/
def emitTicks (registers slot : Nat) : Machine :=
  repeatMachine (slot+1) (emitConst registers [true, true])
def ticksTime (pre value post : Nat) : Nat :=
  value * (6*pre + 8*post + 12*value + 12) + 2*pre + 3
def ticksPolynomial : Polynomial := ⟨20, 2⟩

theorem repeatRun_ticks (pre post : List Nat) (n : Nat) (out : Word) :
    repeatRun pre.length (.emit [true, true]) n ⟨pre ++ n :: post, out⟩ =
      ⟨pre ++ 0 :: post, out ++ List.replicate (2*n) true⟩ := by
  induction n generalizing out with
  | zero => simp [repeatRun]
  | succ n ih =>
    simp only [repeatRun, putRegister_split, runProg, ih]
    rw [show 2*(n+1) = 2+2*n by omega, ← List.replicate_append_replicate]
    simp [List.append_assoc]

theorem repeatCost_ticks (x : Word) (pre post : List Nat) (n : Nat) (out : Word) :
    repeatCost x pre.length (.emit [true, true]) n ⟨pre ++ n :: post, out⟩ =
      ticksTime (tape (x :: regWords pre)).length n (tape (regWords post ++ [out])).length := by
  induction n generalizing out with
  | zero => simp [repeatCost, repeatPrefix_split, ticksTime]
  | succ n ih =>
    simp only [repeatCost, repeatPrefix_split, repeatSuffix_split, putRegister_split,
      cost, runProg, ih, List.length_cons, List.length_nil]
    have hsize : (tape (blocks x ⟨pre ++ n :: post, out⟩)).length =
        (tape (x :: regWords pre)).length + n +
          (tape (regWords post ++ [out])).length + 1 := by
      simp only [blocks, regWords, List.map_append, List.map_cons, tape_append, tape_cons,
        List.length_append, List.length_cons, List.length_map, List.length_replicate]
      omega
    have hout : (tape (regWords post ++ [out ++ [true, true]])).length =
        (tape (regWords post ++ [out])).length + 2 := by simp [tape]; omega
    rw [hsize, hout]
    simp [ticksTime, wordTime, Nat.mul_add, Nat.add_mul]; omega

theorem ticksTime_polynomial (pre value post : Nat) :
    ticksTime pre value post ≤ ticksPolynomial.eval (pre+value+post) := by
  let size := pre+value+post+1
  have h1 : value ≤ size := by omega
  have h2 : 6*pre+8*post+12*value+12 ≤ 12*size := by omega
  have h3 : 2*pre+3 ≤ 3*size*size := by
    have hs : 1 ≤ size := by omega
    have hc : 2*pre+3 ≤ 3*size := by omega
    exact Nat.le_trans hc (Nat.le_mul_of_pos_right _ hs)
  have h := Nat.add_le_add (Nat.mul_le_mul h1 h2) h3
  have hh : size*(12*size)+3*size*size ≤ 20*size*size := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm size 12 size]; omega
  simpa [ticksTime, ticksPolynomial, Polynomial.eval, Nat.pow_two, size,
    Nat.add_assoc, Nat.mul_assoc] using Nat.le_trans h hh

theorem emitTicks_reaches (x : Word) (pre post : List Nat) (n : Nat) (out : Word) :
    ∃ c, Reaches (emitTicks (pre ++ n :: post).length pre.length)
      (encode 0 x ⟨pre ++ n :: post, out⟩)
      (ticksTime (tape (x :: regWords pre)).length n (tape (regWords post ++ [out])).length) c ∧
      Similar (encode (emitTicks (pre ++ n :: post).length pre.length).program.length x
        ⟨pre ++ 0 :: post, out ++ List.replicate (2*n) true⟩) c := by
  have h := repeat_compile_reaches x (pre ++ n :: post).length pre.length
    (.emit [true, true]) trivial trivial (by simp) n
    ⟨pre ++ n :: post, out⟩ rfl (registerAt_split pre post n out)
  simpa only [compile, repeatCost_ticks, repeatRun_ticks, emitTicks] using h

theorem compose_home_reaches (first second : Machine) (before middle after : List Word)
    (t u : Nat) (c d : Config) (hc : Reaches first (home 0 before) t c)
    (hs : Similar (home first.program.length middle) c)
    (hd : Reaches second (home 0 middle) u d)
    (he : Similar (home second.program.length after) d) :
    ∃ e, Reaches (appendMachine first second) (home 0 before) (t+u) e ∧
      Similar (home (appendMachine first second).program.length after) e := by
  have h := reaches_append_right first hd
  have h' : Reaches (appendMachine first second) (home first.program.length middle) u
      (shiftConfig first.program.length d) := by simpa only [shiftConfig, home, Nat.zero_add] using h
  obtain ⟨e, hreach, hsim⟩ := reaches_of_similar h' hs
  refine ⟨e, (reaches_append second hc).trans hreach, ?_⟩
  have he' := (similar_shiftConfig first.program.length _ _ he).trans hsim
  simpa [home, shiftConfig, appendMachine, Nat.add_comm] using he'

def emitLiteral (registers slot : Nat) (pos : Bool) : Machine :=
  appendMachine (emitTicks registers slot) (emitConst registers [false, pos])
def literalTime (pre value post : Nat) : Nat :=
  ticksTime pre value post + wordTime 2 (pre+post+2*value+1)
def literalPolynomial : Polynomial := ⟨40, 2⟩

theorem ticks_eq_replicate (n : Nat) : ticks n = List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2+(2*n) by omega, ← List.replicate_append_replicate]
    simp only [ticks, ih]; rfl

theorem literalTime_polynomial (pre value post : Nat) :
    literalTime pre value post ≤ literalPolynomial.eval (pre+value+post) := by
  have ht := ticksTime_polynomial pre value post
  have hw : wordTime 2 (pre+post+2*value+1) ≤ 20*(pre+value+post+1)^2 := by
    let size := pre+value+post+1
    have hf : 2*(pre+post+2*value+1)+5 ≤ 10*size := by omega
    have hh := Nat.mul_le_mul_left 2 hf
    have hs : 1 ≤ size := by omega
    have hb := Nat.mul_le_mul_left 20 (Nat.le_mul_of_pos_right size hs)
    have hc : 2*(10*size) ≤ 20*(size*size) := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb
    simpa only [wordTime, Nat.pow_two, size] using Nat.le_trans hh hc
  have h := Nat.add_le_add ht hw
  change ticksTime pre value post + wordTime 2 (pre+post+2*value+1) ≤
    40*((pre+value+post+1)^2)
  change ticksTime pre value post + wordTime 2 (pre+post+2*value+1) ≤
    20*((pre+value+post+1)^2) + 20*((pre+value+post+1)^2) at h
  omega

/-- Consume the dynamic unary emitter to produce the exact shared literal
encoding, including its delimiter and polarity. -/
theorem emitLiteral_reaches (x : Word) (pre post : List Nat) (n : Nat) (out : Word) (pos : Bool) :
    ∃ c, Reaches (emitLiteral (pre ++ n :: post).length pre.length pos)
      (encode 0 x ⟨pre ++ n :: post, out⟩)
      (literalTime (tape (x :: regWords pre)).length n (tape (regWords post ++ [out])).length) c ∧
      Similar (encode (emitLiteral (pre ++ n :: post).length pre.length pos).program.length x
        ⟨pre ++ 0 :: post, out ++ encodeLit ⟨n, pos⟩⟩) c := by
  let lower : State := ⟨pre ++ 0 :: post, out ++ List.replicate (2*n) true⟩
  obtain ⟨c, hc, hs⟩ := emitTicks_reaches x pre post n out
  have hlen : lower.regs.length = (pre ++ n :: post).length := by simp [lower]
  have h := emitConst_reaches x lower [false, pos]
  rw [hlen] at h
  obtain ⟨d, hd, he⟩ := compose_home_reaches _ _ _ _ _ _ _ _ _ hc hs h
    ⟨rfl, rfl, rfl, BlankPad.refl _⟩
  have hsize : (tape (blocks x lower)).length = (tape (x :: regWords pre)).length +
      (tape (regWords post ++ [out])).length + 2*n+1 := by
    simp only [lower, blocks, regWords, List.map_append, List.map_cons, tape_append, tape_cons,
      List.length_append, List.length_cons, List.length_map, List.length_replicate]
    omega
  refine ⟨d, ?_, ?_⟩
  · simpa [emitLiteral, literalTime, encode, List.length_cons, List.length_nil, hsize] using hd
  · simpa only [emitLiteral, encode, home, lower, encodeLit, ticks_eq_replicate,
      List.append_assoc] using he

/-- Both pop exits join at the same halt state; an empty register remains empty. -/
def decrementTarget (slot q : Nat) : Nat :=
  if q < (pop slot).program.length then q else (pop slot).program.length

def decrementMachine (slot : Nat) : Machine := retargetMachine (pop slot) (decrementTarget slot)
def decrementTime (pre value post : Nat) : Nat :=
  if value = 0 then 2*pre+3 else 2*pre+4*(value+post)+5

@[simp] theorem decrement_states (slot : Nat) :
    (decrementMachine slot).program.length = (pop slot).program.length := by
  simp [decrementMachine, retargetMachine]

theorem decrementTarget_inside (slot q : Nat) (hq : q < (pop slot).program.length) :
    decrementTarget slot q = q := by unfold decrementTarget; rw [ite_eq_left hq]

theorem decrementTime_le_clearTime (pre value post : Nat) :
    decrementTime pre value post ≤ clearTime pre value post := by
  cases value with
  | zero => simp [decrementTime, clearTime]
  | succ n => simp only [decrementTime, Nat.succ_ne_zero, ite_false, clearTime_succ]; omega

theorem decrementTime_polynomial (pre value post : Nat) :
    decrementTime pre value post ≤ clearPolynomial.eval (pre+value+post+1) :=
  Nat.le_trans (decrementTime_le_clearTime pre value post) (clearTime_polynomial pre value post)

theorem decrement_reaches (pre post : List Word) (n : Nat) :
    ∃ c, Reaches (decrementMachine pre.length)
      (home 0 (pre ++ List.replicate n true :: post))
      (decrementTime (tape pre).length n (tape post).length) c ∧
      Similar (home (decrementMachine pre.length).program.length
        (pre ++ List.replicate (n-1) true :: post)) c := by
  cases n with
  | zero =>
    have h := retarget_reaches (pop_empty pre post) (decrementTarget pre.length)
      (decrementTarget_inside pre.length)
    refine ⟨home (decrementMachine pre.length).program.length (pre ++ [] :: post), ?_,
      ⟨rfl, rfl, rfl, BlankPad.refl _⟩⟩
    change Reaches (decrementMachine pre.length)
      (home (decrementTarget pre.length 0) (pre ++ [] :: post)) _
      (home (decrementTarget pre.length ((pop pre.length).program.length+1)) (pre ++ [] :: post)) at h
    simpa [decrementTarget, decrementTime] using h
  | succ n =>
    have h := retarget_reaches (pop_positive pre post n) (decrementTarget pre.length)
      (decrementTarget_inside pre.length)
    refine ⟨⟨(decrementMachine pre.length).program.length, [], .blank,
      tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩, ?_, ?_⟩
    · change Reaches (decrementMachine pre.length)
        (home (decrementTarget pre.length 0) (pre ++ List.replicate (n+1) true :: post)) _
        ⟨decrementTarget pre.length (pop pre.length).program.length, [], .blank,
          tape (pre ++ List.replicate n true :: post) ++ [.blank, .blank]⟩ at h
      simpa [decrementTarget, decrementTime] using h
    · exact ⟨rfl, rfl, rfl, ⟨_, 0, 2, by simp [blanks, home], rfl⟩⟩

/-- A finite register program with destructive counters and nested loops.
All instructions compile through the shared generated register tables. -/
inductive Program where
  | straight (p : Prog)
  | clearRegister (slot : Nat)
  | decrement (slot : Nat)
  | literal (slot : Nat) (pos : Bool)
  | sequence (first second : Program)
  | loop (slot : Nat) (body : Program)
  deriving Repr

def ProgramReadOnly (slot : Nat) : Program → Prop
  | .straight p => ReadOnly slot p
  | .clearRegister dest => slot ≠ dest
  | .decrement dest => slot ≠ dest
  | .literal dest _ => slot ≠ dest
  | .sequence first second => ProgramReadOnly slot first ∧ ProgramReadOnly slot second
  | .loop counter body => slot ≠ counter ∧ ProgramReadOnly slot body

def ProgramWellFormed (registers : Nat) : Program → Prop
  | .straight p => WellFormed registers p
  | .clearRegister slot => slot < registers
  | .decrement slot => slot < registers
  | .literal slot _ => slot < registers
  | .sequence first second => ProgramWellFormed registers first ∧ ProgramWellFormed registers second
  | .loop slot body => slot < registers ∧ ProgramWellFormed registers body ∧ ProgramReadOnly slot body

def readOnlyDecidable (slot : Nat) : (p : Prog) → Decidable (ReadOnly slot p)
  | .empty => isTrue trivial
  | .increment dest _ => inferInstanceAs (Decidable (slot ≠ dest))
  | .emit _ => isTrue trivial
  | .seq first second => @instDecidableAnd _ _ (readOnlyDecidable slot first) (readOnlyDecidable slot second)
instance (slot : Nat) (p : Prog) : Decidable (ReadOnly slot p) := readOnlyDecidable slot p

def programReadOnlyDecidable (slot : Nat) : (p : Program) → Decidable (ProgramReadOnly slot p)
  | .straight p => readOnlyDecidable slot p
  | .clearRegister dest => inferInstanceAs (Decidable (slot ≠ dest))
  | .decrement dest => inferInstanceAs (Decidable (slot ≠ dest))
  | .literal dest _ => inferInstanceAs (Decidable (slot ≠ dest))
  | .sequence first second => @instDecidableAnd _ _
      (programReadOnlyDecidable slot first) (programReadOnlyDecidable slot second)
  | .loop counter body => @instDecidableAnd _ _
      (inferInstanceAs (Decidable (slot ≠ counter))) (programReadOnlyDecidable slot body)
instance (slot : Nat) (p : Program) : Decidable (ProgramReadOnly slot p) := programReadOnlyDecidable slot p

def programWellFormedDecidable (k : Nat) : (p : Program) → Decidable (ProgramWellFormed k p)
  | .straight p => wellFormedDecidable k p
  | .clearRegister slot => inferInstanceAs (Decidable (slot < k))
  | .decrement slot => inferInstanceAs (Decidable (slot < k))
  | .literal slot _ => inferInstanceAs (Decidable (slot < k))
  | .sequence first second => @instDecidableAnd _ _
      (programWellFormedDecidable k first) (programWellFormedDecidable k second)
  | .loop slot body => @instDecidableAnd _ _ (inferInstanceAs (Decidable (slot < k)))
      (@instDecidableAnd _ _ (programWellFormedDecidable k body) (programReadOnlyDecidable slot body))
instance (k : Nat) (p : Program) : Decidable (ProgramWellFormed k p) := programWellFormedDecidable k p

def programRun : Program → State → State
  | .straight p, st => runProg p st
  | .clearRegister slot, st => putRegister slot 0 st
  | .decrement slot, st => putRegister slot (registerAt slot st - 1) st
  | .literal slot pos, st => ⟨(putRegister slot 0 st).regs, st.out ++ encodeLit ⟨registerAt slot st, pos⟩⟩
  | .sequence first second, st => programRun second (programRun first st)
  | .loop slot body, st => loopRun slot (programRun body) (registerAt slot st) st

def programCost (x : Word) : Program → State → Nat
  | .straight p, st => cost x p st
  | .clearRegister slot, st => clearTime (repeatPrefix x slot st) (registerAt slot st) (repeatSuffix slot st)
  | .decrement slot, st => decrementTime (repeatPrefix x slot st) (registerAt slot st) (repeatSuffix slot st)
  | .literal slot _, st => literalTime (repeatPrefix x slot st) (registerAt slot st) (repeatSuffix slot st)
  | .sequence first second, st => programCost x first st + programCost x second (programRun first st)
  | .loop slot body, st => loopCost x slot (programRun body) (programCost x body) (registerAt slot st) st

def compileProgram (k : Nat) : Program → Machine
  | .straight p => compile k p
  | .clearRegister slot => clearThen slot k .empty
  | .decrement slot => decrementMachine (slot+1)
  | .literal slot pos => emitLiteral k slot pos
  | .sequence first second => appendMachine (compileProgram k first) (compileProgram k second)
  | .loop slot body => repeatMachine (slot+1) (compileProgram k body)

theorem registerAt_putRegister_other (slot dest value : Nat) (st : State) (h : slot ≠ dest) :
    registerAt slot (putRegister dest value st) = registerAt slot st := by
  simp [registerAt, putRegister, List.getElem?_set_ne (Ne.symm h)]

theorem loopRun_regs_length (slot : Nat) (runBody : State → State)
    (hr : ∀ st, (runBody st).regs.length = st.regs.length) (n : Nat) (st : State) :
    (loopRun slot runBody n st).regs.length = st.regs.length := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [loopRun, ih, hr, putRegister_length]

theorem loopRun_readOnly (slot counter : Nat) (runBody : State → State)
    (hneq : slot ≠ counter) (hbody : ∀ st, registerAt slot (runBody st) = registerAt slot st)
    (n : Nat) (st : State) : registerAt slot (loopRun counter runBody n st) = registerAt slot st := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [loopRun, ih, hbody, registerAt_putRegister_other slot counter n st hneq]

theorem programRun_regs_length (p : Program) (st : State) :
    (programRun p st).regs.length = st.regs.length := by
  induction p generalizing st with
  | straight p => exact runProg_regs_length p st
  | clearRegister slot => exact putRegister_length slot 0 st
  | decrement slot => exact putRegister_length slot _ st
  | literal slot pos => exact putRegister_length slot 0 st
  | sequence first second ihf ihs => simp only [programRun, ihs, ihf]
  | loop slot body ih => exact loopRun_regs_length slot (programRun body) ih _ st

theorem programRun_readOnly (slot : Nat) (p : Program) (st : State) (h : ProgramReadOnly slot p) :
    registerAt slot (programRun p st) = registerAt slot st := by
  induction p generalizing st with
  | straight p => exact runProg_readOnly slot p st h
  | clearRegister dest => exact registerAt_putRegister_other slot dest 0 st h
  | decrement dest => exact registerAt_putRegister_other slot dest _ st h
  | literal dest pos => exact registerAt_putRegister_other slot dest 0 st h
  | sequence first second ihf ihs => exact (ihs _ h.2).trans (ihf _ h.1)
  | loop counter body ih => exact loopRun_readOnly slot counter (programRun body) h.1 (fun s => ih s h.2) _ st

theorem clear_state_reaches (x : Word) (k slot : Nat) (st : State)
    (hk : st.regs.length = k) (hslot : slot < k) :
    ∃ c, Reaches (compileProgram k (.clearRegister slot)) (encode 0 x st)
      (programCost x (.clearRegister slot) st) c ∧
      Similar (encode (compileProgram k (.clearRegister slot)).program.length x
        (programRun (.clearRegister slot) st)) c := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot (by change values.length = k at hk; omega)
  subst values; subst slot
  have h := clear_then_compile_reaches x pre post value out k .empty trivial (by simpa using hk)
  simpa [compileProgram, programRun, programCost, repeatPrefix_split, repeatSuffix_split,
    registerAt_split, putRegister_split, runProg, cost] using h

theorem literal_state_reaches (x : Word) (k slot : Nat) (pos : Bool) (st : State)
    (hk : st.regs.length = k) (hslot : slot < k) :
    ∃ c, Reaches (compileProgram k (.literal slot pos)) (encode 0 x st)
      (programCost x (.literal slot pos) st) c ∧
      Similar (encode (compileProgram k (.literal slot pos)).program.length x
        (programRun (.literal slot pos) st)) c := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot (by change values.length = k at hk; omega)
  subst values; subst slot
  have h := emitLiteral_reaches x pre post value out pos
  simpa only [compileProgram, programCost, programRun, registerAt_split, putRegister_split,
    repeatPrefix_split, repeatSuffix_split, hk] using h

theorem decrement_state_reaches (x : Word) (k slot : Nat) (st : State)
    (hk : st.regs.length = k) (hslot : slot < k) :
    ∃ c, Reaches (compileProgram k (.decrement slot)) (encode 0 x st)
      (programCost x (.decrement slot) st) c ∧
      Similar (encode (compileProgram k (.decrement slot)).program.length x
        (programRun (.decrement slot) st)) c := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot
    (by change values.length = k at hk; omega)
  subst values; subst slot
  have h := decrement_reaches (x :: regWords pre) (regWords post ++ [out]) value
  simpa [compileProgram, programRun, programCost, repeatPrefix_split, repeatSuffix_split,
    registerAt_split, putRegister_split, encode, blocks, regWords, List.append_assoc] using h

/-- One compiler contract covers sequencing, clearing, exact literal encoding,
and arbitrarily nested dynamic loops. Tables depend only on the program and
register count, while all values and loop bounds are read from the tape. -/
theorem compileProgram_reaches (x : Word) (k : Nat) (p : Program) (st : State)
    (hp : ProgramWellFormed k p) (hk : st.regs.length = k) :
    ∃ c, Reaches (compileProgram k p) (encode 0 x st) (programCost x p st) c ∧
      Similar (encode (compileProgram k p).program.length x (programRun p st)) c := by
  induction p generalizing st with
  | straight p => exact ⟨_, compile_reaches x k p st hp hk, ⟨rfl, rfl, rfl, BlankPad.refl _⟩⟩
  | clearRegister slot => exact clear_state_reaches x k slot st hk hp
  | decrement slot => exact decrement_state_reaches x k slot st hk hp
  | literal slot pos => exact literal_state_reaches x k slot pos st hk hp
  | sequence first second ihf ihs =>
    obtain ⟨c, hc, hs⟩ := ihf st hp.1 hk
    obtain ⟨d, hd, he⟩ := ihs (programRun first st) hp.2 ((programRun_regs_length first st).trans hk)
    simpa only [compileProgram, programRun, programCost, encode] using
      compose_home_reaches _ _ _ _ _ _ _ _ _ hc hs hd he
  | loop slot body ih =>
    exact loop_reaches x k slot (compileProgram k body) (programRun body) (programCost x body)
      (programRun_regs_length body) (fun s => programRun_readOnly slot body s hp.2.2)
      (fun s hs => ih s hp.2.1 hs) hp.1 _ st hk rfl

/-- Copy a dynamic unary source into the destination, restoring the source.
The scratch register is cleared first and is empty on exit. -/
def addToProgram (source dest scratch : Nat) : Program :=
  .sequence (.clearRegister scratch)
    (.sequence (.loop source (.straight (.seq (.increment dest 1) (.increment scratch 1))))
      (.loop scratch (.straight (.increment source 1))))

theorem addToProgram_wellFormed (k source dest scratch : Nat)
    (hs : source < k) (hd : dest < k) (hc : scratch < k)
    (hsd : source ≠ dest) (hsc : source ≠ scratch) :
    ProgramWellFormed k (addToProgram source dest scratch) := by
  simp [addToProgram, ProgramWellFormed, ProgramReadOnly, WellFormed, ReadOnly, hs, hd, hc, hsd, hsc, Ne.symm hsc]

theorem incrementRegs_registerAt (slot count : Nat) (st : State) (h : slot < st.regs.length) :
    registerAt slot (runProg (.increment slot count) st) = registerAt slot st + count := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot h
  subst values; subst slot
  simp only [runProg, incrementRegs_split, registerAt_split]

theorem loopRun_counter_zero (counter : Nat) (runBody : State → State)
    (hr : ∀ st, (runBody st).regs.length = st.regs.length)
    (hbody : ∀ st, registerAt counter (runBody st) = registerAt counter st)
    (n : Nat) (st : State) (hslot : counter < st.regs.length) (hn : registerAt counter st = n) :
    registerAt counter (loopRun counter runBody n st) = 0 := by
  induction n generalizing st with
  | zero => exact hn
  | succ n ih =>
    apply ih
    · simp only [hr, putRegister_length]; exact hslot
    · rw [hbody, registerAt_putRegister counter n st hslot]

theorem loopRun_adds (counter target count : Nat) (runBody : State → State)
    (hneq : target ≠ counter)
    (hr : ∀ st, (runBody st).regs.length = st.regs.length)
    (hbody : ∀ st, target < st.regs.length → registerAt target (runBody st) = registerAt target st + count)
    (n : Nat) (st : State) (htarget : target < st.regs.length) :
    registerAt target (loopRun counter runBody n st) = registerAt target st + n*count := by
  induction n generalizing st with
  | zero => simp [loopRun]
  | succ n ih =>
    have hl : target < (putRegister counter n st).regs.length := by simpa only [putRegister_length] using htarget
    rw [loopRun, ih _ (by simpa only [hr, putRegister_length] using htarget), hbody _ hl,
      registerAt_putRegister_other target counter n st hneq]
    simp only [Nat.succ_mul]; omega

theorem loopRun_out (counter : Nat) (runBody : State → State)
    (hbody : ∀ st, (runBody st).out = st.out) (n : Nat) (st : State) :
    (loopRun counter runBody n st).out = st.out := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [loopRun, ih, hbody, putRegister]

/-- The copy's semantic contract retains every register except destination and
scratch, keeps the input/output, and restores the dynamic source exactly. -/
theorem addToProgram_registers (source dest scratch : Nat) (st : State)
    (hs : source < st.regs.length) (hd : dest < st.regs.length) (hc : scratch < st.regs.length)
    (hsd : source ≠ dest) (hsc : source ≠ scratch) (hdc : dest ≠ scratch) (slot : Nat) :
    registerAt slot (programRun (addToProgram source dest scratch) st) =
      if slot = scratch then 0 else
      if slot = dest then registerAt dest st + registerAt source st else registerAt slot st := by
  let initial := putRegister scratch 0 st
  let body := runProg (.seq (.increment dest 1) (.increment scratch 1))
  let middle := loopRun source body (registerAt source initial) initial
  let restore := runProg (.increment source 1)
  have hbLength : ∀ s, (body s).regs.length = s.regs.length := runProg_regs_length _
  have hrLength : ∀ s, (restore s).regs.length = s.regs.length := runProg_regs_length _
  have hbSource : ∀ s, registerAt source (body s) = registerAt source s :=
    fun s => runProg_readOnly source _ s ⟨hsd, hsc⟩
  have hrScratch : ∀ s, registerAt scratch (restore s) = registerAt scratch s :=
    fun s => runProg_readOnly scratch _ s (Ne.symm hsc)
  have hlen : middle.regs.length = st.regs.length :=
    (loopRun_regs_length source body hbLength _ initial).trans (putRegister_length scratch 0 st)
  have hiSource : registerAt source initial = registerAt source st := registerAt_putRegister_other _ _ _ _ hsc
  have hiScratch : registerAt scratch initial = 0 := registerAt_putRegister _ _ _ hc
  have hmSource : registerAt source middle = 0 :=
    loopRun_counter_zero source body hbLength hbSource _ initial (by simpa [initial, putRegister_length] using hs) rfl
  have hmScratch : registerAt scratch middle = registerAt source st := by
    have h := loopRun_adds source scratch 1 body (Ne.symm hsc) hbLength
      (fun s hl => by
        change registerAt scratch (runProg (.increment scratch 1) (runProg (.increment dest 1) s)) = _
        rw [incrementRegs_registerAt _ _ _ (by simpa only [runProg_regs_length] using hl)]
        rw [runProg_readOnly scratch (.increment dest 1) s (Ne.symm hdc)]) (registerAt source initial) initial
      (by simpa [initial, putRegister_length] using hc)
    simpa only [middle, hiScratch, hiSource, Nat.mul_one, Nat.zero_add] using h
  change registerAt slot (loopRun scratch restore (registerAt scratch middle) middle) = _
  by_cases hslotc : slot = scratch
  · subst slot
    rw [ite_eq_left rfl]
    exact loopRun_counter_zero scratch restore hrLength hrScratch _ middle (by omega) rfl
  · rw [ite_eq_right hslotc]
    by_cases hslotd : slot = dest
    · subst slot
      rw [ite_eq_left rfl, loopRun_readOnly dest scratch restore hdc
        (fun s => runProg_readOnly dest _ s (Ne.symm hsd))]
      have h := loopRun_adds source dest 1 body (Ne.symm hsd) hbLength
        (fun s hl => by
          change registerAt dest (runProg (.increment scratch 1) (runProg (.increment dest 1) s)) = _
          rw [runProg_readOnly dest (.increment scratch 1) _ hdc, incrementRegs_registerAt _ _ _ hl])
        (registerAt source initial) initial (by simpa [initial, putRegister_length] using hd)
      have hiDest : registerAt dest initial = registerAt dest st :=
        registerAt_putRegister_other dest scratch 0 st hdc
      simpa only [middle, hiSource, Nat.mul_one,
        hiDest] using h
    · rw [ite_eq_right hslotd]
      by_cases hslots : slot = source
      · subst slot
        have h := loopRun_adds scratch source 1 restore hsc hrLength
          (fun s hl => incrementRegs_registerAt source 1 s hl) (registerAt scratch middle) middle (by omega)
        simpa only [hmSource, hmScratch, Nat.mul_one, Nat.zero_add] using h
      · rw [loopRun_readOnly slot scratch restore hslotc
          (fun s => runProg_readOnly slot _ s hslots)]
        rw [loopRun_readOnly slot source body hslots
          (fun s => runProg_readOnly slot _ s ⟨hslotd, hslotc⟩)]
        exact registerAt_putRegister_other slot scratch 0 st hslotc

theorem addToProgram_out (source dest scratch : Nat) (st : State) :
    (programRun (addToProgram source dest scratch) st).out = st.out := by
  simp only [addToProgram, programRun]
  rw [loopRun_out scratch (runProg (.increment source 1)) (fun _ => rfl),
    loopRun_out source (runProg (.seq (.increment dest 1) (.increment scratch 1))) (fun _ => rfl)]
  rfl

theorem addToProgram_reaches (x : Word) (k source dest scratch : Nat) (st : State)
    (hk : st.regs.length = k) (hs : source < k) (hd : dest < k) (hc : scratch < k)
    (hsd : source ≠ dest) (hsc : source ≠ scratch) :
    ∃ c, Reaches (compileProgram k (addToProgram source dest scratch)) (encode 0 x st)
      (programCost x (addToProgram source dest scratch) st) c ∧
      Similar (encode (compileProgram k (addToProgram source dest scratch)).program.length x
        (programRun (addToProgram source dest scratch) st)) c :=
  compileProgram_reaches x k _ st (addToProgram_wellFormed k source dest scratch hs hd hc hsd hsc) hk

theorem register_span (x : Word) (slot : Nat) (st : State) (h : slot < st.regs.length) :
    repeatPrefix x slot st + registerAt slot st + repeatSuffix slot st + 1 =
      (tape (blocks x st)).length := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values slot h
  subst values; subst slot
  simp only [repeatPrefix_split, repeatSuffix_split, registerAt_split, blocks,
    regWords, List.map_append, List.map_cons, tape_append, tape_cons,
    List.length_append, List.length_cons, List.length_map, List.length_replicate]
  omega

theorem putRegister_size_le (x : Word) (slot value : Nat) (st : State)
    (hslot : slot < st.regs.length) (hvalue : value ≤ registerAt slot st) :
    (tape (blocks x (putRegister slot value st))).length ≤ (tape (blocks x st)).length := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, old, post, hp, hv⟩ := register_decomposition values slot hslot
  subst values; subst slot
  rw [registerAt_split] at hvalue
  simp only [putRegister_split, blocks_length, List.sum_append, List.sum_cons,
    List.length_append, List.length_cons]
  omega

/-- A straight-line body grows by a fixed amount. An explicit invariant bounds
all intermediate tapes and the complete charged dynamic-loop cost. -/
theorem loopCost_straight_bound (x : Word) (k slot : Nat) (p : Prog)
    (hp : WellFormed k p) (hro : ReadOnly slot p) (hslot : slot < k)
    (n : Nat) (st : State) (hk : st.regs.length = k) (hn : registerAt slot st = n)
    (limit : Nat) (hlimit : (tape (blocks x st)).length + n * growth p ≤ limit) :
    loopCost x slot (runProg p) (cost x p) n st ≤
      (n+1) * (20 * (limit + growth p + 1)^2) := by
  let cap := limit + growth p + 1
  have hcap : 1 ≤ cap := by omega
  have hsq : cap ≤ cap^2 := by
    simpa only [Nat.pow_two] using Nat.le_mul_of_pos_right cap hcap
  induction n generalizing st with
  | zero =>
    have hspan := register_span x slot st (by omega)
    have hpre : repeatPrefix x slot st ≤ limit := by omega
    have hbase : 2*repeatPrefix x slot st+3 ≤ 20*cap := by omega
    have hsq' := Nat.mul_le_mul_left 20 hsq
    simpa only [loopCost, Nat.zero_add, Nat.one_mul, cap] using Nat.le_trans hbase hsq'
  | succ n ih =>
    let lower := putRegister slot n st
    let next := runProg p lower
    have hslot' : slot < st.regs.length := by omega
    have hsize := putRegister_size_le x slot n st hslot' (by omega)
    have hl : lower.regs.length = k := (putRegister_length slot n st).trans hk
    have hnextSize := runProg_tape_length x k p lower hp hl
    have hnextLength : next.regs.length = k := (runProg_regs_length p lower).trans hl
    have hnextN : registerAt slot next = n := by
      rw [runProg_readOnly slot p lower hro, registerAt_putRegister slot n st hslot']
    have hnextLimit : (tape (blocks x next)).length + n*growth p ≤ limit := by
      simp only [Nat.succ_mul] at hlimit
      change (tape (blocks x next)).length = (tape (blocks x lower)).length + growth p at hnextSize
      change (tape (blocks x lower)).length ≤ _ at hsize
      omega
    have htail := ih next hnextLength hnextN hnextLimit
    change loopCost x slot (runProg p) (cost x p) n next ≤ (n+1)*(20*cap^2) at htail
    have hbody := cost_polynomial x k p lower hp hl
    have hbodyCap : cost x p lower ≤ 3*cap^2 := by
      have hsmall : (tape (blocks x lower)).length + growth p + 1 ≤ cap := by
        change (tape (blocks x lower)).length ≤ _ at hsize
        omega
      have h := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hsmall 2)
      exact Nat.le_trans hbody h
    have hspan := register_span x slot st hslot'
    have hcontrol : 2*repeatPrefix x slot st + 4*(n+1+repeatSuffix slot st)+5+1 ≤ 12*cap := by omega
    have hcontroller := Nat.le_trans hcontrol (Nat.mul_le_mul_left 12 hsq)
    have h := Nat.add_le_add (Nat.add_le_add hcontroller hbodyCap) htail
    change 2*repeatPrefix x slot st + 4*(n+1+repeatSuffix slot st)+5 +
      cost x p lower + 1 + loopCost x slot (runProg p) (cost x p) n next ≤
      (n+1+1)*(20*cap^2)
    simp only [Nat.add_mul, Nat.one_mul] at h ⊢
    omega

theorem loopRun_straight_size_le (x : Word) (k slot : Nat) (p : Prog)
    (hp : WellFormed k p) (hro : ReadOnly slot p) (hslot : slot < k)
    (n : Nat) (st : State) (hk : st.regs.length = k) (hn : registerAt slot st = n) :
    (tape (blocks x (loopRun slot (runProg p) n st))).length ≤
      (tape (blocks x st)).length + n * growth p := by
  induction n generalizing st with
  | zero => simp [loopRun]
  | succ n ih =>
    let lower := putRegister slot n st
    let next := runProg p lower
    have hs : slot < st.regs.length := by omega
    have hsize := putRegister_size_le x slot n st hs (by omega)
    have hl : lower.regs.length = k := (putRegister_length slot n st).trans hk
    have hnext := runProg_tape_length x k p lower hp hl
    have hlen : next.regs.length = k := (runProg_regs_length p lower).trans hl
    have hcount : registerAt slot next = n := by
      rw [runProg_readOnly slot p lower hro, registerAt_putRegister slot n st hs]
    have h := ih next hlen hcount
    change (tape (blocks x (loopRun slot (runProg p) n next))).length ≤ _
    change (tape (blocks x lower)).length ≤ _ at hsize
    change (tape (blocks x next)).length = _ at hnext
    simp only [Nat.succ_mul] at *
    omega

def copyPolynomial : Polynomial := ⟨4000, 3⟩

/-- The dynamic transfer and restoration loops have cubic charged cost in the
initial tape length, including the cleared scratch register and output. -/
theorem addToProgram_cost_polynomial (x : Word) (k source dest scratch : Nat) (st : State)
    (hk : st.regs.length = k) (hs : source < k) (hd : dest < k) (hc : scratch < k)
    (hsd : source ≠ dest) (hsc : source ≠ scratch) :
    programCost x (addToProgram source dest scratch) st ≤
      copyPolynomial.eval (tape (blocks x st)).length := by
  let size := (tape (blocks x st)).length
  let initial := putRegister scratch 0 st
  let transfer : Prog := .seq (.increment dest 1) (.increment scratch 1)
  let n := registerAt source initial
  let middle := loopRun source (runProg transfer) n initial
  let restore : Prog := .increment source 1
  let m := registerAt scratch middle
  have hiLength : initial.regs.length = k := (putRegister_length scratch 0 st).trans hk
  have hmLength : middle.regs.length = k :=
    (loopRun_regs_length source _ (runProg_regs_length transfer) n initial).trans hiLength
  have hiSize : (tape (blocks x initial)).length ≤ size :=
    putRegister_size_le x scratch 0 st (by omega) (Nat.zero_le _)
  have hn : n ≤ size := by
    have h := register_span x source initial (by omega)
    omega
  have ht : WellFormed k transfer := ⟨hd, hc⟩
  have htr : ReadOnly source transfer := ⟨hsd, hsc⟩
  have hr : WellFormed k restore := hs
  have hrr : ReadOnly scratch restore := Ne.symm hsc
  have hmSize : (tape (blocks x middle)).length ≤ 3*size := by
    have h := loopRun_straight_size_le x k source transfer ht htr hs n initial hiLength rfl
    change (tape (blocks x middle)).length ≤ _ at h
    simp only [transfer, growth] at h
    omega
  have hm : m ≤ 3*size := by
    have h := register_span x scratch middle (by omega)
    omega
  have hfirst := loopCost_straight_bound x k source transfer ht htr hs n initial hiLength rfl
    (3*size) (by simp only [transfer, growth]; omega)
  have hsecond := loopCost_straight_bound x k scratch restore hr hrr hc m middle hmLength rfl
    (6*size) (by simp only [restore, growth]; omega)
  have hfirstBound : loopCost x source (runProg transfer) (cost x transfer) n initial ≤
      180*(size+1)^3 := by
    simp only [transfer, growth] at hfirst
    have h := Nat.mul_le_mul_right (20*(3*size+2+1)^2) (show n+1 ≤ size+1 by omega)
    have heq : (size+1)*(20*(3*size+2+1)^2) = 180*(size+1)^3 := by
      have he : 3*size+2+1 = 3*(size+1) := by omega
      rw [he]
      rw [Nat.mul_pow]
      change (size+1)*(20*(9*(size+1)^2)) = 180*((size+1)^2*(size+1))
      calc
        _ = (20*9)*((size+1)^2*(size+1)) := by ac_rfl
        _ = _ := rfl
    exact Nat.le_trans hfirst (heq ▸ h)
  have hsecondBound : loopCost x scratch (runProg restore) (cost x restore) m middle ≤
      2160*(size+1)^3 := by
    simp only [restore, growth] at hsecond
    have ha : m+1 ≤ 3*(size+1) := by omega
    have hb : 6*size+1+1 ≤ 6*(size+1) := by omega
    have h := Nat.mul_le_mul ha (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hb 2))
    have heq : (3*(size+1))*(20*(6*(size+1))^2) = 2160*(size+1)^3 := by
      rw [Nat.mul_pow]
      change (3*(size+1))*(20*(36*(size+1)^2)) = 2160*((size+1)^2*(size+1))
      calc
        _ = (3*20*36)*((size+1)^2*(size+1)) := by ac_rfl
        _ = _ := rfl
    exact Nat.le_trans hsecond (heq ▸ h)
  have hclear := clearTime_polynomial (repeatPrefix x scratch st) (registerAt scratch st)
    (repeatSuffix scratch st)
  rw [register_span x scratch st (by omega)] at hclear
  change clearTime _ _ _ ≤ 10*(size+1)^2 at hclear
  have hcube : (size+1)^2 ≤ (size+1)^3 := by
    exact Nat.le_mul_of_pos_right ((size+1)^2) (Nat.succ_pos size)
  have hclearBound := Nat.le_trans hclear (Nat.mul_le_mul_left 10 hcube)
  have h := Nat.add_le_add (Nat.add_le_add hclearBound hfirstBound) hsecondBound
  have htotal : clearTime (repeatPrefix x scratch st) (registerAt scratch st) (repeatSuffix scratch st) +
      loopCost x source (runProg transfer) (cost x transfer) n initial +
      loopCost x scratch (runProg restore) (cost x restore) m middle ≤ 4000*(size+1)^3 :=
    Nat.le_trans (by simpa only [← Nat.add_mul] using h)
      (Nat.mul_le_mul_right ((size+1)^3) (show 2350 ≤ 4000 by decide))
  simpa only [addToProgram, programCost, programRun, transfer, restore, initial,
    n, middle, m, size, copyPolynomial, Polynomial.eval, Nat.add_assoc] using htotal

/-- Reserve two registers beyond the three operands, independently of their values. -/
def subCounter (a b dest : Nat) : Nat := max a (max b dest) + 1
def subScratch (a b dest : Nat) : Nat := subCounter a b dest + 1

def subProgram (a b dest : Nat) : Program :=
  let counter := subCounter a b dest
  let scratch := subScratch a b dest
  .sequence (.clearRegister counter)
    (.sequence (addToProgram b counter scratch)
      (.sequence (.clearRegister dest)
        (.sequence (addToProgram a dest scratch) (.loop counter (.decrement dest)))))

theorem subCounter_wider (a b dest : Nat) :
    a < subCounter a b dest ∧ b < subCounter a b dest ∧ dest < subCounter a b dest := by
  simp only [subCounter]; omega

theorem subProgram_wellFormed (k a b dest : Nat) (hk : subScratch a b dest < k)
    (had : a ≠ dest) : ProgramWellFormed k (subProgram a b dest) := by
  have h := subCounter_wider a b dest
  have hscratch : subScratch a b dest = subCounter a b dest + 1 := rfl
  have h1 := addToProgram_wellFormed k b (subCounter a b dest) (subScratch a b dest)
    (by omega) (by unfold subScratch at hk; omega) hk (by omega) (by unfold subScratch; omega)
  have h2 := addToProgram_wellFormed k a dest (subScratch a b dest)
    (by unfold subScratch at hk; omega) (by unfold subScratch at hk; omega) hk had
    (by unfold subScratch; omega)
  change subCounter a b dest < k ∧ ProgramWellFormed k (addToProgram b (subCounter a b dest) (subScratch a b dest)) ∧
    dest < k ∧ ProgramWellFormed k (addToProgram a dest (subScratch a b dest)) ∧
    subCounter a b dest < k ∧ dest < k ∧ subCounter a b dest ≠ dest
  exact ⟨by omega, h1, by omega, h2, by omega, by omega, by omega⟩

theorem loopRun_decrements (counter target : Nat) (hneq : target ≠ counter)
    (n : Nat) (st : State) (ht : target < st.regs.length) :
    registerAt target (loopRun counter (programRun (.decrement target)) n st) =
      registerAt target st - n := by
  induction n generalizing st with
  | zero => simp [loopRun]
  | succ n ih =>
    rw [loopRun, ih _ (by simpa [programRun, putRegister_length] using ht)]
    change registerAt target (putRegister target
      (registerAt target (putRegister counter n st) - 1) (putRegister counter n st)) - n = _
    rw [registerAt_putRegister _ _ _ (by simpa only [putRegister_length] using ht),
      registerAt_putRegister_other target counter n st hneq, Nat.sub_sub]
    omega

theorem subProgram_registers (a b dest : Nat) (st : State)
    (hk : subScratch a b dest < st.regs.length) (had : a ≠ dest) (slot : Nat) :
    registerAt slot (programRun (subProgram a b dest) st) =
      if slot = subCounter a b dest ∨ slot = subScratch a b dest then 0 else
      if slot = dest then registerAt a st - registerAt b st else registerAt slot st := by
  let counter := subCounter a b dest
  let scratch := subScratch a b dest
  have hwide := subCounter_wider a b dest
  have hac : a < counter := hwide.1
  have hbc : b < counter := hwide.2.1
  have hdc : dest < counter := hwide.2.2
  have hcs : counter < scratch := by dsimp [counter, scratch, subScratch]; omega
  have hc : counter < st.regs.length := by change scratch < st.regs.length at hk; omega
  let initial := putRegister counter 0 st
  let captured := programRun (addToProgram b counter scratch) initial
  let copied := programRun (addToProgram a dest scratch) (putRegister dest 0 captured)
  have hil : initial.regs.length = st.regs.length := putRegister_length _ _ _
  have hcl : captured.regs.length = st.regs.length := (programRun_regs_length _ _).trans hil
  have hdl : copied.regs.length = st.regs.length :=
    (programRun_regs_length _ _).trans ((putRegister_length _ _ _).trans hcl)
  have hcap (i : Nat) : registerAt i captured =
      if i = scratch then 0 else if i = counter then registerAt b st else registerAt i st := by
    have h := addToProgram_registers b counter scratch initial
      (by omega) (by omega) (by change scratch < st.regs.length at hk; omega)
      (by omega) (by omega) (by omega) i
    have hb : registerAt b initial = registerAt b st := registerAt_putRegister_other _ _ _ _ (by omega)
    have hc0 : registerAt counter initial = 0 := registerAt_putRegister _ _ _ hc
    simp only [hb, hc0, Nat.zero_add] at h
    rw [h]
    split <;> try rfl
    split <;> try rfl
    exact registerAt_putRegister_other _ _ _ _ (by assumption)
  have hcopy (i : Nat) : registerAt i copied =
      if i = scratch then 0 else if i = dest then registerAt a st else
      if i = counter then registerAt b st else registerAt i st := by
    have h := addToProgram_registers a dest scratch (putRegister dest 0 captured)
      (by simp only [putRegister_length, hcl]; omega)
      (by simp only [putRegister_length, hcl]; omega)
      (by simp only [putRegister_length, hcl]; exact hk) had (by omega) (by omega) i
    have ha : registerAt a (putRegister dest 0 captured) = registerAt a st := by
      rw [registerAt_putRegister_other _ _ _ _ had, hcap]
      simp only [ite_eq_right (show a ≠ scratch by omega), ite_eq_right (show a ≠ counter by omega)]
    have hd : registerAt dest (putRegister dest 0 captured) = 0 :=
      registerAt_putRegister _ _ _ (by omega)
    change registerAt i copied = _ at h
    rw [h, ha, hd, Nat.zero_add]
    split <;> try rfl
    split <;> try rfl
    rw [registerAt_putRegister_other _ _ _ _ (by assumption), hcap]
    simp only [ite_eq_right (show i ≠ scratch by assumption)]
  have hcc : registerAt counter copied = registerAt b st := by simp [hcopy, show counter ≠ scratch by omega, show counter ≠ dest by omega]
  have hdd : registerAt dest copied = registerAt a st := by simp [hcopy, show dest ≠ scratch by omega]
  change registerAt slot (loopRun counter (programRun (.decrement dest)) (registerAt counter copied) copied) = _
  by_cases hsc : slot = counter
  · subst slot
    simp only [counter, true_or, ite_true]
    exact loopRun_counter_zero counter (programRun (.decrement dest))
      (programRun_regs_length _) (fun s => programRun_readOnly counter _ s (by change counter ≠ dest; omega))
      _ copied (by omega) rfl
  · by_cases hss : slot = scratch
    · subst slot
      rw [loopRun_readOnly scratch counter _ (by omega)
        (fun s => programRun_readOnly scratch _ s (by change scratch ≠ dest; omega))]
      simp [hcopy, scratch]
    · have hneq : ¬(slot = subCounter a b dest ∨ slot = subScratch a b dest) := by
        change ¬(slot = counter ∨ slot = scratch); exact fun h => h.elim hsc hss
      rw [ite_eq_right hneq]
      by_cases hsd : slot = dest
      · subst slot
        rw [ite_eq_left rfl, loopRun_decrements counter dest (by omega) _ copied (by omega), hcc, hdd]
      · rw [ite_eq_right hsd, loopRun_readOnly slot counter _ hsc
          (fun s => programRun_readOnly slot (.decrement dest) s hsd), hcopy]
        simp only [ite_eq_right hss, ite_eq_right hsd, ite_eq_right hsc]

theorem subProgram_out (a b dest : Nat) (st : State) :
    (programRun (subProgram a b dest) st).out = st.out := by
  change (loopRun _ (programRun (.decrement dest)) _ _).out = _
  rw [loopRun_out _ (programRun (.decrement dest)) (fun s => rfl), addToProgram_out]
  change (programRun (addToProgram b (subCounter a b dest) (subScratch a b dest))
    (putRegister (subCounter a b dest) 0 st)).out = st.out
  rw [addToProgram_out]; rfl

theorem subProgram_reaches (x : Word) (k a b dest : Nat) (st : State)
    (hk : st.regs.length = k) (hslots : subScratch a b dest < k)
    (had : a ≠ dest) :
    ∃ c, Reaches (compileProgram k (subProgram a b dest)) (encode 0 x st)
      (programCost x (subProgram a b dest) st) c ∧
      Similar (encode (compileProgram k (subProgram a b dest)).program.length x
        (programRun (subProgram a b dest) st)) c :=
  compileProgram_reaches x k _ st (subProgram_wellFormed k a b dest hslots had) hk

end Issue624.RegisterMachine
