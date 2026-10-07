import proofs.experiments.issue624.lean.Arithmetic
import proofs.experiments.issue624.lean.Schema

/-!
Input-aware extensions of the charged register compiler.

The existing register language deliberately treats the input block as immutable.
For Cook--Levin generation we need exactly one additional primitive: consume the
leading input bit while storing it as a unary 0/1 register.  The implementation
below reuses the certified register clear/increment tables and the certified
left-shift deletion table.
-/

namespace Issue624.Compiler

open Complexity
open Issue532.Machines
open Issue624.RegisterMachine

/-- A four-state dispatcher.  It normalizes a leading input bit to one.
On zero it exits the combined machine directly; on one it enters a tail
machine at state four.  The original bit is therefore remembered only in the
control state, never in an uncharged meta-level operation. -/
def readNormalizeHead (tailStates : Nat) : Machine := ⟨[
  [.move 1 .blank .right, .halt false, .halt false, .halt false],
  [.halt false, .move 2 .one .left, .move 3 .one .left, .move 2 .separator .left],
  [.move (4 + tailStates) .blank .stay, .halt false, .halt false, .halt false],
  [.move 4 .blank .stay, .halt false, .halt false, .halt false]
]⟩

@[simp] theorem readNormalizeHead_states (tailStates : Nat) :
    (readNormalizeHead tailStates).program.length = 4 := by
  rfl

/-- Read a normalized leading bit.  A one runs one certified unary increment;
a zero jumps over that increment. -/
def readNormalize (dest : Nat) : Machine :=
  appendMachine (readNormalizeHead (incr dest 1).program.length) (incr dest 1)

@[simp] theorem readNormalize_states (dest : Nat) :
    (readNormalize dest).program.length = 4 + (incr dest 1).program.length := by
  simp [readNormalize, appendMachine]

theorem readNormalizeHead_zero (tailStates : Nat) (tail : List Symbol) :
    Reaches (readNormalizeHead tailStates)
      ⟨0, [], .blank, .zero :: tail⟩ 3
      ⟨4 + tailStates, [], .blank, .one :: tail⟩ := by
  exact Reaches.next rfl (Reaches.next rfl (Reaches.next rfl (Reaches.refl _)))

theorem readNormalizeHead_one (tailStates : Nat) (tail : List Symbol) :
    Reaches (readNormalizeHead tailStates)
      ⟨0, [], .blank, .one :: tail⟩ 3
      ⟨4, [], .blank, .one :: tail⟩ := by
  exact Reaches.next rfl (Reaches.next rfl (Reaches.next rfl (Reaches.refl _)))

def readNormalizeTime (b : Bool) (x : Word) (st : State) : Nat :=
  3 + if b then wordTime 1 (tape (blocks (true :: x) st)).length else 0

/-- The dispatcher plus the ordinary unary increment records a leading bit in
a zeroed register, while normalizing that leading tape symbol to one. -/
theorem readNormalize_reaches (b : Bool) (x : Word) (pre post : List Nat) (out : Word) :
    Reaches (readNormalize pre.length)
      (encode 0 (b :: x) ⟨pre ++ 0 :: post, out⟩)
      (readNormalizeTime b x ⟨pre ++ 0 :: post, out⟩)
      (encode (readNormalize pre.length).program.length (true :: x)
        ⟨pre ++ (if b then 1 else 0) :: post, out⟩) := by
  cases b with
  | false =>
      have hh := readNormalizeHead_zero (incr pre.length 1).program.length
        (x.map Symbol.ofBool ++ .separator :: tape (regWords (pre ++ 0 :: post) ++ [out]))
      have h := reaches_append (incr pre.length 1) hh
      rw [readNormalize_states]
      simpa [readNormalize, readNormalizeTime, encode, home, blocks, regWords,
        tape, Symbol.ofBool, List.append_assoc] using h
  | true =>
      have hh := readNormalizeHead_one (incr pre.length 1).program.length
        (x.map Symbol.ofBool ++ .separator :: tape (regWords (pre ++ 0 :: post) ++ [out]))
      have hhead := reaches_append (incr pre.length 1) hh
      have hi := incr_reaches (true :: x) pre post 0 1 out
      have htail := reaches_append_right
        (readNormalizeHead (incr pre.length 1).program.length) hi
      have htail' : Reaches (readNormalize pre.length)
          (encode 4 (true :: x) ⟨pre ++ 0 :: post, out⟩)
          (wordTime 1 (tape (blocks (true :: x) ⟨pre ++ 0 :: post, out⟩)).length)
          (encode (readNormalize pre.length).program.length (true :: x)
            ⟨pre ++ 1 :: post, out⟩) := by
        simpa [readNormalize, encode, home, shiftConfig, appendMachine,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
      have hhead' : Reaches (readNormalize pre.length)
          (encode 0 (true :: x) ⟨pre ++ 0 :: post, out⟩) 3
          (encode 4 (true :: x) ⟨pre ++ 0 :: post, out⟩) := by
        simpa [readNormalize, encode, home, blocks, regWords, tape,
          Symbol.ofBool, List.append_assoc] using hhead
      simpa [readNormalizeTime, Nat.add_assoc] using hhead'.trans htail'

/-- Cost of deleting the now-normalized leading one from the input block. -/
def dropNormalizedTime (x : Word) (st : State) : Nat :=
  4 * (x.length + 1 + (tape (regWords st.regs ++ [st.out])).length) + 5

/-- The existing deletion table works for an arbitrary nonblank tail; unary
registers were only a special case of that stronger table theorem. -/
theorem dropNormalized_reaches (x : Word) (st : State) :
    ∃ c, Reaches (pop 0) (encode 0 (true :: x) st) (dropNormalizedTime x st) c ∧
      Similar (encode (pop 0).program.length x st) c := by
  let xs : List Symbol :=
    x.map Symbol.ofBool ++ .separator :: tape (regWords st.regs ++ [st.out])
  have hs := reaches_append deleteFirst (seek_reaches [] (.one :: xs))
  have hd := reaches_append_right (seek 0)
    (delete_positive [] xs (by simp) (by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
        cases b <;> decide
      · rcases List.mem_cons.mp h with h | h
        · subst a; decide
        · exact tape_nonblank (regWords st.regs ++ [st.out]) a h))
  have hs' : Reaches (pop 0) (encode 0 (true :: x) st) 1
      ⟨(seek 0).program.length, [.blank], .one, xs⟩ := by
    simpa [pop, encode, home, blocks, tape, regWords, Symbol.ofBool, scanConfig, xs] using hs
  have hd' : Reaches (pop 0)
      ⟨(seek 0).program.length, [.blank], .one, xs⟩
      (4 * xs.length + 4)
      ⟨(pop 0).program.length, [], .blank, xs ++ [.blank, .blank]⟩ := by
    simpa [pop, shiftConfig, scanConfig, appendMachine, seek_states,
      deleteFirst, Nat.add_comm, xs] using hd
  refine ⟨⟨(pop 0).program.length, [], .blank, xs ++ [.blank, .blank]⟩, ?_, ?_⟩
  · have hlen : xs.length =
        x.length + 1 + (tape (regWords st.regs ++ [st.out])).length := by
      simp [xs, tape]
      omega
    have hrun := hs'.trans hd'
    have hcost : 1 + (4 * xs.length + 4) = dropNormalizedTime x st := by
      rw [hlen]
      unfold dropNormalizedTime
      omega
    rw [← hcost]
    exact hrun
  · simp only [Similar, encode, home]
    refine ⟨rfl, rfl, rfl, ?_⟩
    refine ⟨tape (blocks x st), 0, 2, by simp [blanks], ?_⟩
    simp [xs, blocks, tape, regWords, blanks]

def bitNat (b : Bool) : Nat := if b then 1 else 0

/-- Semantic effect of consuming a bit. -/
def popBitState (dest : Nat) (b : Bool) (st : State) : State :=
  putRegister dest (bitNat b) st

/-- A compiled input-bit operation for a fixed register file size. -/
def popBit (registers dest : Nat) : Machine :=
  appendMachine (compileProgram registers (.clearRegister dest))
    (appendMachine (readNormalize dest) (pop 0))

def popBitTime (registers dest : Nat) (b : Bool) (x : Word) (st : State) : Nat :=
  let cleared := putRegister dest 0 st
  programCost (b :: x) (.clearRegister dest) st +
    readNormalizeTime b x cleared +
    dropNormalizedTime x (popBitState dest b st)

/-- The complete input primitive is charged and home-preserving up to trailing
blanks.  It consumes exactly one bit and sets exactly the requested register. -/
theorem popBit_reaches (registers dest : Nat) (b : Bool) (x : Word) (st : State)
    (hk : st.regs.length = registers) (hd : dest < registers) :
    ∃ c, Reaches (popBit registers dest) (encode 0 (b :: x) st)
      (popBitTime registers dest b x st) c ∧
      Similar (encode (popBit registers dest).program.length x (popBitState dest b st)) c := by
  rcases st with ⟨values, out⟩
  obtain ⟨pre, value, post, hp, hv⟩ := register_decomposition values dest
    (by change values.length = registers at hk; omega)
  subst values
  subst dest
  have hk' : (pre ++ value :: post).length = registers := by simpa using hk
  obtain ⟨c, hc, hs⟩ := clear_state_reaches (b :: x) registers pre.length
    ⟨pre ++ value :: post, out⟩ hk' (by simpa using hd)
  have hclear :
      programRun (.clearRegister pre.length) ⟨pre ++ value :: post, out⟩ =
        ⟨pre ++ 0 :: post, out⟩ := by
    simp [programRun, putRegister_split]
  rw [hclear] at hs
  have hr := readNormalize_reaches b x pre post out
  have hr' : Reaches (appendMachine (readNormalize pre.length) (pop 0))
      (encode 0 (b :: x) ⟨pre ++ 0 :: post, out⟩)
      (readNormalizeTime b x ⟨pre ++ 0 :: post, out⟩)
      (encode (readNormalize pre.length).program.length (true :: x)
        ⟨pre ++ bitNat b :: post, out⟩) := by
    have := reaches_append (pop 0) hr
    simpa [bitNat] using this
  have hdrop := dropNormalized_reaches x ⟨pre ++ bitNat b :: post, out⟩
  obtain ⟨d, hdreach, hdsim⟩ := hdrop
  have hdrop' := reaches_append_right (readNormalize pre.length) hdreach
  have hdrop'' : Reaches (appendMachine (readNormalize pre.length) (pop 0))
      (encode (readNormalize pre.length).program.length (true :: x)
        ⟨pre ++ bitNat b :: post, out⟩)
      (dropNormalizedTime x ⟨pre ++ bitNat b :: post, out⟩) (shiftConfig
        (readNormalize pre.length).program.length d) := by
    simpa [encode, home, shiftConfig, appendMachine, Nat.add_comm, Nat.add_assoc] using hdrop'
  have hinner := hr'.trans hdrop''
  have hinnerSim : Similar
      (encode (appendMachine (readNormalize pre.length) (pop 0)).program.length x
        ⟨pre ++ bitNat b :: post, out⟩)
      (shiftConfig (readNormalize pre.length).program.length d) := by
    simpa [encode, home, shiftConfig, appendMachine, Nat.add_comm, Nat.add_assoc] using
      similar_shiftConfig (readNormalize pre.length).program.length _ _ hdsim
  have hinnerShift := reaches_append_right
    (compileProgram registers (.clearRegister pre.length)) hinner
  have hinnerShift' : Reaches (popBit registers pre.length)
      (encode (compileProgram registers (.clearRegister pre.length)).program.length
        (b :: x) ⟨pre ++ 0 :: post, out⟩)
      (readNormalizeTime b x ⟨pre ++ 0 :: post, out⟩ +
        dropNormalizedTime x ⟨pre ++ bitNat b :: post, out⟩)
      (shiftConfig (compileProgram registers (.clearRegister pre.length)).program.length
        (shiftConfig (readNormalize pre.length).program.length d)) := by
    simpa [popBit, encode, home, shiftConfig, appendMachine, Nat.add_comm, Nat.add_assoc] using
      hinnerShift
  obtain ⟨e, he, hes⟩ := reaches_of_similar hinnerShift' hs
  refine ⟨e, ?_, ?_⟩
  · have hfirst := reaches_append (appendMachine (readNormalize pre.length) (pop 0)) hc
    have hall := hfirst.trans he
    simpa [popBitTime, popBit, popBitState, bitNat, putRegister_split, hclear,
      Nat.add_assoc] using hall
  · have hshiftSim := similar_shiftConfig
      (compileProgram registers (.clearRegister pre.length)).program.length _ _ hinnerSim
    have := hshiftSim.trans hes
    simpa [popBit, popBitState, bitNat, putRegister_split, encode, home, shiftConfig,
      appendMachine, Nat.add_comm, Nat.add_assoc] using this

end Issue624.Compiler
