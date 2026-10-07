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

end Issue624.RegisterMachine
