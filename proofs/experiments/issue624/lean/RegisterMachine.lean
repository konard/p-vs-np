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

end Issue624.RegisterMachine
