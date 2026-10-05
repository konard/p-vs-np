import proofs.experiments.issue532.lean.Machines

/-! A concrete single-tape output primitive. Its finite table erases the input,
returns to the marked origin, emits a fixed word, and restores the head. All
costs below count `Reaches` instructions. This is a primitive for an emitter,
not the input-dependent Cook--Levin reduction. -/
namespace Issue624.ConstantEmitter
open Complexity Issue532.Machines

private def symbols : List Symbol := [.blank, .zero, .one, .separator]
private def fixedRow (q : Nat) (w : Symbol) (d : Direction) : List Instruction :=
  symbols.map (fun _ => .move q w d)
private def keepRow (q : Nat) (d : Direction) : List Instruction :=
  symbols.map (fun a => .move q a d)

private def writeRows (base : Nat) : Word → List (List Instruction)
  | [] => []
  | b :: w => fixedRow (base + 1) (.ofBool b) .right :: writeRows (base + 1) w
private def returnRows (base : Nat) : Nat → List (List Instruction)
  | 0 => []
  | k + 1 => keepRow (base + 1) .left :: returnRows (base + 1) k

private def setupRows : List (List Instruction) :=
  [fixedRow 1 .separator .right,
   [.move 2 .blank .left, .move 1 .blank .right,
    .move 1 .blank .right, .move 1 .blank .right],
   [.move 2 .blank .left, .move 2 .zero .left,
    .move 2 .one .left, .move 3 .separator .stay],
   fixedRow 4 .blank .stay]

def emitter (w : Word) : Machine :=
  ⟨setupRows ++ writeRows 4 w ++ returnRows (4 + w.length) w.length⟩

def emitterPolynomial (w : Word) : Polynomial := ⟨4 + 2 * w.length, 1⟩

private theorem writeRows_length (base : Nat) (w : Word) :
    (writeRows base w).length = w.length := by
  induction w generalizing base <;> simp_all [writeRows]
private theorem returnRows_length (base k : Nat) :
    (returnRows base k).length = k := by
  induction k generalizing base <;> simp_all [returnRows]

theorem emitter_states (w : Word) : (emitter w).program.length = 4 + 2 * w.length := by
  simp [emitter, setupRows, writeRows_length, returnRows_length]; omega

private theorem setupRows_instr (w : Word) (a : Symbol) :
    (emitter w).instruction 0 a = .move 1 .separator .right ∧
    (emitter w).instruction 1 .blank = .move 2 .blank .left ∧
    (emitter w).instruction 2 .blank = .move 2 .blank .left ∧
    (emitter w).instruction 2 .separator = .move 3 .separator .stay ∧
    (emitter w).instruction 3 a = .move 4 .blank .stay := by
  cases a <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem erase_instr (w : Word) (b : Bool) :
    (emitter w).instruction 1 (.ofBool b) = .move 1 .blank .right := by
  cases b <;> rfl

private theorem writeRows_get (base : Nat) (w : Word) (i : Nat) (hi : i < w.length) :
    (writeRows base w)[i]? = some (fixedRow (base + i + 1) (.ofBool (w.getD i false)) .right) := by
  induction w generalizing base i with
  | nil => simp at hi
  | cons b w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [writeRows, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (base + 1) i (by simpa using hi)

private theorem returnRows_get (base k i : Nat) (hi : i < k) :
    (returnRows base k)[i]? = some (keepRow (base + i + 1) .left) := by
  induction k generalizing base i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [returnRows, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (base + 1) i (by omega)

private theorem write_instr (w : Word) (i : Nat) (hi : i < w.length) (a : Symbol) :
    (emitter w).instruction (4 + i) a =
      .move (4 + i + 1) (.ofBool (w.getD i false)) .right := by
  have hrow : (emitter w).program[4 + i]? =
      some (fixedRow (4 + i + 1) (.ofBool (w.getD i false)) .right) := by
    simp only [emitter, List.append_assoc]
    rw [List.getElem?_append_right (by simp [setupRows]), show setupRows.length = 4 by rfl]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simpa [writeRows_length] using hi)]
    exact writeRows_get 4 w i hi
  unfold Machine.instruction
  rw [hrow]
  cases a <;> rfl

private theorem return_instr (w : Word) (i : Nat) (hi : i < w.length) (a : Symbol) :
    (emitter w).instruction (4 + w.length + i) a =
      .move (4 + w.length + i + 1) a .left := by
  have hrow : (emitter w).program[4 + w.length + i]? =
      some (keepRow (4 + w.length + i + 1) .left) := by
    change (setupRows ++ writeRows 4 w ++ returnRows (4 + w.length) w.length)[4 + w.length + i]? = _
    rw [List.getElem?_append_right (by simp [setupRows, writeRows_length]; omega)]
    simp only [List.length_append, show setupRows.length = 4 by rfl, writeRows_length,
      Nat.add_sub_cancel_left]
    exact returnRows_get _ _ _ hi
  unfold Machine.instruction
  rw [hrow]
  cases a <;> rfl

private theorem reaches_trans {m : Machine} {c d e : Config} {t u : Nat}
    (h : Reaches m c t d) (hu : Reaches m d u e) : Reaches m c (t + u) e := by
  induction h with
  | refl => simpa using hu
  | next hs _ ih => simpa [Nat.add_right_comm] using Reaches.next hs (ih hu)

private def cfg (q : Nat) (l : List Symbol) : List Symbol → Config
  | [] => ⟨q, l, .blank, []⟩
  | a :: r => ⟨q, l, a, r⟩

private theorem blanks_snoc (n : Nat) : blanks (n + 1) = blanks n ++ [.blank] := by
  simp [blanks, List.replicate_succ']

private theorem erase_reaches (out : Word) (w : Word) (l : List Symbol) :
    Reaches (emitter out) (cfg 1 l (w.map Symbol.ofBool)) w.length
      (cfg 1 (blanks w.length ++ l) []) := by
  induction w generalizing l with
  | nil => simpa [blanks] using Reaches.refl (cfg 1 l [])
  | cons b w ih =>
    have hs : step (emitter out) (cfg 1 l ((b :: w).map Symbol.ofBool)) =
        .inr (cfg 1 (.blank :: l) (w.map Symbol.ofBool)) := by
      unfold step
      simp only [List.map_cons, cfg, erase_instr, moveHead]
      cases w <;> rfl
    simpa [blanks_snoc, List.append_assoc] using Reaches.next hs (ih (.blank :: l))

private def revCfg (q : Nat) (r : List Symbol) : List Symbol → Config
  | [] => ⟨q, [], .blank, r⟩
  | a :: l => ⟨q, l, a, r⟩

private theorem return_origin (out : Word) (n : Nat) (r : List Symbol) :
    Reaches (emitter out) (revCfg 2 r (blanks n ++ [.separator])) (n + 1)
      ⟨3, [], .separator, blanks n ++ r⟩ := by
  induction n generalizing r with
  | zero =>
    apply Reaches.next (c' := ⟨3, [], .separator, r⟩)
    · simp [revCfg, blanks, step, (setupRows_instr out .blank).2.2.2.1, moveHead]
    · simpa [blanks] using Reaches.refl ⟨3, [], .separator, r⟩
  | succ n ih =>
    have hs : step (emitter out) (revCfg 2 r (blanks (n + 1) ++ [.separator])) =
        .inr (revCfg 2 (.blank :: r) (blanks n ++ [.separator])) := by
      simp only [blanks, List.replicate_succ, List.cons_append, revCfg, step,
        (setupRows_instr out .blank).2.2.1]
      cases n <;> rfl
    simpa [blanks_snoc, List.append_assoc] using Reaches.next hs (ih (.blank :: r))

/-- Finite writing block, with an instruction-table contract. This lemma
counts one charged instruction per output bit. -/
theorem write_block (m : Machine) (base : Nat) (w : Word)
    (h : ∀ i, i < w.length → ∀ a, m.instruction (base + i) a =
      .move (base + i + 1) (.ofBool (w.getD i false)) .right)
    (l : List Symbol) (padding : Nat) :
    Reaches m ⟨base, l, .blank, blanks padding⟩ w.length
      ⟨base + w.length, (w.map Symbol.ofBool).reverse ++ l, .blank,
        blanks (padding - w.length)⟩ := by
  induction w generalizing base l padding with
  | nil => simpa using Reaches.refl ⟨base, l, .blank, blanks padding⟩
  | cons b w ih =>
    have hs : step m ⟨base, l, .blank, blanks padding⟩ =
        .inr ⟨base + 1, .ofBool b :: l, .blank, blanks (padding - 1)⟩ := by
      unfold step
      rw [show base = base + 0 by omega, h 0 (by simp) .blank]
      cases padding <;> rfl
    have ht : ∀ i, i < w.length → ∀ a, m.instruction (base + 1 + i) a =
        .move (base + 1 + i + 1) (.ofBool (w.getD i false)) .right := by
      intro i hi a
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (i + 1) (by simp; omega) a
    have hr := ih (base + 1) ht (.ofBool b :: l) (padding - 1)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.sub_sub,
      Nat.add_left_comm, Nat.add_comm] using Reaches.next hs hr

/-- Restore the head to the original leftmost cell through a finite return
block. The tape content is preserved, and every left move is charged. -/
theorem return_block (m : Machine) (base : Nat) (l : List Symbol) (a : Symbol)
    (r : List Symbol)
    (h : ∀ i, i < l.length → ∀ s, m.instruction (base + i) s =
      .move (base + i + 1) s .left) :
    ∃ d, Reaches m ⟨base, l, a, r⟩ l.length d ∧ d.state = base + l.length ∧
      d.left = [] ∧ d.head :: d.right = l.reverse ++ a :: r := by
  induction l generalizing base a r with
  | nil => exact ⟨⟨base, [], a, r⟩, Reaches.refl _, by simp, rfl, rfl⟩
  | cons b l ih =>
    have hs : step m ⟨base, b :: l, a, r⟩ = .inr ⟨base + 1, l, b, a :: r⟩ := by
      unfold step
      rw [show base = base + 0 by omega, h 0 (by simp) a]
      rfl
    have ht : ∀ i, i < l.length → ∀ s, m.instruction (base + 1 + i) s =
        .move (base + 1 + i + 1) s .left := by
      intro i hi s
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (i + 1) (by simp; omega) s
    obtain ⟨d, hd, hq, hl, hr⟩ := ih (base + 1) b (a :: r) ht
    refine ⟨d, Reaches.next hs hd, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq, hl, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using hr

private theorem prepare (w x : Word) : ∃ n,
    n ≤ x.length ∧ Reaches (emitter w) (initial x) (2 * n + 4)
      ⟨4, [], .blank, blanks (n + 1)⟩ := by
  have hstart (tail : Word) :
      Reaches (emitter w) (cfg 1 [.separator] (tail.map Symbol.ofBool))
        (2 * tail.length + 3) ⟨4, [], .blank, blanks (tail.length + 1)⟩ := by
    have he := erase_reaches w tail [.separator]
    have hs : step (emitter w) (cfg 1 (blanks tail.length ++ [.separator]) []) =
        .inr (revCfg 2 [.blank] (blanks tail.length ++ [.separator])) := by
      simp only [cfg, step, (setupRows_instr w .blank).2.1, moveHead]
      cases tail.length <;> rfl
    have hr := return_origin w tail.length [.blank]
    have hc : step (emitter w) ⟨3, [], .separator, blanks tail.length ++ [.blank]⟩ =
        .inr ⟨4, [], .blank, blanks (tail.length + 1)⟩ := by
      simp [step, (setupRows_instr w .separator).2.2.2.2, moveHead, blanks_snoc]
    have hh := reaches_trans he (Reaches.next hs
      (reaches_trans hr (Reaches.next hc (Reaches.refl _))))
    have ht : tail.length + (tail.length + 1 + (0 + 1) + 1) =
        2 * tail.length + 3 := by omega
    rw [ht] at hh
    exact hh
  cases x with
  | nil =>
    refine ⟨0, by simp, ?_⟩
    have hs : step (emitter w) (initial []) = .inr (cfg 1 [.separator] []) := by
      simp [initial, initialSymbols, step, (setupRows_instr w .blank).1, moveHead, cfg]
    simpa using Reaches.next hs (hstart [])
  | cons b tail =>
    refine ⟨tail.length, by simp, ?_⟩
    have hs : step (emitter w) (initial (b :: tail)) =
        .inr (cfg 1 [.separator] (tail.map Symbol.ofBool)) := by
      simp only [initial, List.map_cons, initialSymbols, step,
        (setupRows_instr w (.ofBool b)).1, moveHead]
      cases tail <;> rfl
    have hh := Reaches.next hs (hstart tail)
    simpa [Nat.add_assoc] using hh

/-- An explicit function machine, including its exact exit state, empty left
tape, output bits, trailing blanks, and a polynomial charged-step bound. -/
theorem emitter_computes (w : Word) :
    Computes (emitter w) (fun _ => w) (emitterPolynomial w) := by
  intro x
  obtain ⟨n, hn, hp⟩ := prepare w x
  have hw := write_block (emitter w) 4 w (write_instr w) [] (n + 1)
  have hreturn : ∀ i, i < (w.map Symbol.ofBool).reverse.length → ∀ s,
      (emitter w).instruction (4 + w.length + i) s =
        .move (4 + w.length + i + 1) s .left := by
    intro i hi s
    exact return_instr w i (by simpa using hi) s
  obtain ⟨d, hd, hq, hl, hr⟩ := return_block (emitter w) (4 + w.length)
    (w.map Symbol.ofBool).reverse .blank (blanks (n + 1 - w.length)) hreturn
  have hw' : Reaches (emitter w) ⟨4, [], .blank, blanks (n + 1)⟩ w.length
      ⟨4 + w.length, (w.map Symbol.ofBool).reverse, .blank,
        blanks (n + 1 - w.length)⟩ := by simpa using hw
  have hd' : Reaches (emitter w)
      ⟨4 + w.length, (w.map Symbol.ofBool).reverse, .blank,
        blanks (n + 1 - w.length)⟩ w.length d := by simpa using hd
  refine ⟨2 * n + 4 + w.length + w.length, d, ?_,
    reaches_trans (reaches_trans hp hw') hd', ?_, hl, n + 1 - w.length + 1, ?_⟩
  · simp only [emitterPolynomial, Polynomial.eval, Nat.pow_one, Nat.mul_add,
      Nat.add_mul, Nat.mul_one]
    have hm := Nat.mul_le_mul_left 2 hn
    omega
  · rw [emitter_states]
    simpa [Nat.add_assoc, Nat.two_mul] using hq
  · simpa [blanks, List.replicate_succ] using hr

end Issue624.ConstantEmitter
