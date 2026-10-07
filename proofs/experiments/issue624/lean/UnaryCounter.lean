import proofs.experiments.issue532.lean.Machines

/-! An input-retaining, finite-table unary counter for the reduction's loops.
The blank cursor advances through input bits. Each iteration moves the next
bit to the cursor, scans to the separator, appends one unary tick, and returns
to the new cursor. The table has nine states for every word and counter value.
The interface is a tape-block contract, with exact charged `Reaches` time. -/
namespace Issue624.UnaryCounter
open Complexity Issue532.Machines

def counter : Machine := ⟨[
  [.move 1 .blank .right, .halt false, .halt false, .halt false],
  [.halt false, .move 2 .blank .left, .move 3 .blank .left, .move 9 .separator .left],
  [.move 4 .zero .right, .halt false, .halt false, .halt false],
  [.move 4 .one .right, .halt false, .halt false, .halt false],
  [.move 5 .blank .right, .halt false, .halt false, .halt false],
  [.halt false, .move 5 .zero .right, .move 5 .one .right, .move 6 .separator .right],
  [.move 7 .one .left, .halt false, .move 6 .one .right, .halt false],
  [.halt false, .halt false, .move 7 .one .left, .move 8 .separator .left],
  [.move 0 .blank .stay, .move 8 .zero .left, .move 8 .one .left, .halt false]]⟩

def ticks (k : Nat) : List Symbol := List.replicate k .one
def cursor (l : List Symbol) (x : Word) (k : Nat) : Config :=
  ⟨0, l, .blank, x.map Symbol.ofBool ++ .separator :: ticks k⟩
def finished (l : List Symbol) (x : Word) (k : Nat) : Config :=
  ⟨9, (x.map Symbol.ofBool).reverse ++ l, .blank,
    .separator :: ticks (k + x.length)⟩
def countTime (n k : Nat) : Nat := n * (2 * (n + k) + 6) + 2
def counterPolynomial : Polynomial := ⟨8, 2⟩

private theorem ticks_reverse (k : Nat) : (ticks k).reverse = ticks k := by
  simp [ticks]
private theorem ticks_snoc (k : Nat) : ticks k ++ [.one] = ticks (k + 1) := by
  simp [ticks, List.replicate_succ']
private theorem ticks_length (k : Nat) : (ticks k).length = k := by simp [ticks]

private theorem scan_input_right (x : Word) (l r : List Symbol) :
    Reaches counter (scanConfig 5 l (x.map Symbol.ofBool ++ r)) x.length
      (scanConfig 5 ((x.map Symbol.ofBool).reverse ++ l) r) := by
  simpa using (scan_right counter 5 (x.map Symbol.ofBool) l r (by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    cases b <;> rfl))
private theorem scan_input_left (x : Word) (l r : List Symbol) :
    Reaches counter (scanLeftConfig 8 r ((x.map Symbol.ofBool).reverse ++ l)) x.length
      (scanLeftConfig 8 (x.map Symbol.ofBool ++ r) l) := by
  simpa using (scan_left counter 8 (x.map Symbol.ofBool).reverse r l (by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    cases b <;> rfl))

private theorem scan_ticks_right (k : Nat) (l : List Symbol) :
    Reaches counter (scanConfig 6 l (ticks k)) k
      ⟨6, ticks k ++ l, .blank, []⟩ := by
  have h := scan_right counter 6 (ticks k) l [] (by
    intro a ha
    have he : a = .one := (by simpa [ticks] using ha : k ≠ 0 ∧ a = .one).2
    subst a
    rfl)
  simpa [ticks, scanConfig] using h
private theorem scan_ticks_left (k : Nat) (l : List Symbol) :
    Reaches counter (scanLeftConfig 7 [.one] (ticks k ++ .separator :: l)) k
      ⟨7, l, .separator, ticks (k + 1)⟩ := by
  have h := scan_left counter 7 (ticks k) [.one] (.separator :: l) (by
    intro a ha
    have he : a = .one := (by simpa [ticks] using ha : k ≠ 0 ∧ a = .one).2
    subst a
    rfl)
  simpa only [ticks_reverse, ticks_snoc, scanLeftConfig, ticks_length] using h

/-- One bit is retained to the left of the cursor and adds one counter tick. -/
theorem counter_cycle (l : List Symbol) (b : Bool) (x : Word) (k : Nat) :
    Reaches counter (cursor l (b :: x) k) (8 + 2 * x.length + 2 * k)
      (cursor (.ofBool b :: l) x (k + 1)) := by
  let p := .ofBool b :: l
  let r := x.map Symbol.ofBool
  let back := r.reverse ++ .blank :: p
  have hstart : Reaches counter (cursor l (b :: x) k) 3
      ⟨4, p, .blank, r ++ .separator :: ticks k⟩ := by
    cases b <;>
      exact Reaches.next rfl (Reaches.next rfl (Reaches.next rfl (Reaches.refl _)))
  have hscan : step counter ⟨4, p, .blank, r ++ .separator :: ticks k⟩ =
      .inr (scanConfig 5 (.blank :: p) (r ++ .separator :: ticks k)) := by
    cases x <;> rfl
  have hr := scan_input_right x (.blank :: p) (.separator :: ticks k)
  have hsep : step counter ⟨5, back, .separator, ticks k⟩ =
      .inr (scanConfig 6 (.separator :: back) (ticks k)) := by
    cases k <;> rfl
  have hi := scan_ticks_right k (.separator :: back)
  have hadd : step counter ⟨6, ticks k ++ .separator :: back, .blank, []⟩ =
      .inr (scanLeftConfig 7 [.one] (ticks k ++ .separator :: back)) := by
    cases k <;> rfl
  have hb := scan_ticks_left k back
  have hreturn : step counter ⟨7, back, .separator, ticks (k + 1)⟩ =
      .inr (scanLeftConfig 8 (.separator :: ticks (k + 1)) (r.reverse ++ .blank :: p)) := by
    change step counter ⟨7, back, .separator, ticks (k + 1)⟩ =
      .inr (scanLeftConfig 8 (.separator :: ticks (k + 1)) back)
    unfold step
    rw [show counter.instruction 7 .separator = .move 8 .separator .left by rfl]
    cases back <;> rfl
  have hl := scan_input_left x (.blank :: p) (.separator :: ticks (k + 1))
  have hend : step counter ⟨8, p, .blank, r ++ .separator :: ticks (k + 1)⟩ =
      .inr (cursor p x (k + 1)) := rfl
  have h := hstart.trans (Reaches.next hscan (hr.trans
    (Reaches.next hsep (hi.trans (Reaches.next hadd (hb.trans
      (Reaches.next hreturn (hl.trans (Reaches.next hend (Reaches.refl _))))))))))
  simpa [r, back, p, Nat.add_assoc, Nat.two_mul, Nat.add_comm, Nat.add_left_comm] using h

/-- The table is fixed, while the retained input and counter are unbounded. -/
theorem counter_reaches (l : List Symbol) (x : Word) (k : Nat) :
    Reaches counter (cursor l x k) (countTime x.length k) (finished l x k) := by
  induction x generalizing l k with
  | nil =>
    simp only [cursor, finished, countTime, List.map_nil, List.length_nil,
      List.reverse_nil, List.nil_append, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    change Reaches counter ⟨0, l, .blank, .separator :: ticks k⟩ 2
      ⟨9, l, .blank, .separator :: ticks k⟩
    exact Reaches.next rfl (Reaches.next rfl (Reaches.refl _))
  | cons b x ih =>
    have ht : 8 + 2 * x.length + 2 * k + countTime x.length (k + 1) =
        countTime (b :: x).length k := by
      simp only [countTime, List.length_cons, Nat.mul_add, Nat.add_mul,
        Nat.mul_one, Nat.one_mul]
      omega
    have h := (counter_cycle l b x k).trans (ih (.ofBool b :: l) (k + 1))
    rw [ht] at h
    simpa [finished, List.reverse_cons, List.append_assoc, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using h

theorem countTime_polynomial (n k : Nat) :
    countTime n k ≤ counterPolynomial.eval (n + k) := by
  have hn : n ≤ n + k + 1 := by omega
  have hb : 2 ≤ (n + k + 1) * 2 := by omega
  have ha : 2 * (n + k) + 6 + 2 ≤ 8 * (n + k + 1) := by omega
  calc
    countTime n k ≤ (n + k + 1) * (2 * (n + k) + 6) + (n + k + 1) * 2 :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hn) hb
    _ = (n + k + 1) * (2 * (n + k) + 6 + 2) := by simp only [Nat.mul_add]
    _ ≤ (n + k + 1) * (8 * (n + k + 1)) := Nat.mul_le_mul_left _ ha
    _ = counterPolynomial.eval (n + k) := by
      simp only [counterPolynomial, Polynomial.eval, Nat.pow_two]
      ac_rfl

/-- Sequencing preserves the charged block contract and exits into the next table. -/
theorem counter_append (next : Machine) (l : List Symbol) (x : Word) (k : Nat) :
    Reaches (appendMachine counter next) (cursor l x k) (countTime x.length k)
      (finished l x k) := reaches_append next (counter_reaches l x k)

/-- Create the cursor and delimiter from the actual input. No input bit is lost. -/
def prepare : Machine := ⟨[
  [.move 4 .separator .left, .move 1 .zero .left, .move 1 .one .left, .halt false],
  [.move 2 .blank .right, .halt false, .halt false, .halt false],
  [.move 3 .separator .left, .move 2 .zero .right, .move 2 .one .right, .halt false],
  [.move 7 .blank .stay, .move 3 .zero .left, .move 3 .one .left, .halt false],
  [.move 5 .blank .stay, .halt false, .halt false, .halt false],
  [.move 6 .blank .stay, .halt false, .halt false, .halt false],
  [.move 7 .blank .stay, .halt false, .halt false, .halt false]]⟩

theorem prepare_reaches (x : Word) :
    Reaches prepare (initial x) (2 * x.length + 4) (shiftConfig 7 (cursor [] x 0)) := by
  cases x with
  | nil =>
    exact Reaches.next rfl (Reaches.next rfl (Reaches.next rfl
      (Reaches.next rfl (Reaches.refl _))))
  | cons b x =>
    let r := (b :: x).map Symbol.ofBool
    have hs : Reaches prepare (initial (b :: x)) 2 (scanConfig 2 [.blank] r) := by
      cases b <;> cases x <;> exact Reaches.next rfl (Reaches.next rfl (Reaches.refl _))
    have hf := scan_right prepare 2 r [.blank] [] (by
      intro a ha
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
      cases c <;> rfl)
    have hf' : Reaches prepare (scanConfig 2 [.blank] r) (b :: x).length
        ⟨2, r.reverse ++ [.blank], .blank, []⟩ := by
      simpa [r, scanConfig] using hf
    have ha : step prepare ⟨2, r.reverse ++ [.blank], .blank, []⟩ =
        .inr (scanLeftConfig 3 [.separator] (r.reverse ++ [.blank])) := by
      unfold step
      rw [show prepare.instruction 2 .blank = .move 3 .separator .left by rfl]
      cases r.reverse ++ [Symbol.blank] <;> rfl
    have hb := scan_left prepare 3 r.reverse [.separator] [.blank] (by
      intro a ha
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
      cases c <;> rfl)
    have hb' : Reaches prepare (scanLeftConfig 3 [.separator] (r.reverse ++ [.blank]))
        (b :: x).length ⟨3, [], .blank, r ++ [.separator]⟩ := by
      simpa [r, scanLeftConfig] using hb
    have hh : step prepare ⟨3, [], .blank, r ++ [.separator]⟩ =
        .inr (shiftConfig 7 (cursor [] (b :: x) 0)) := rfl
    have h := hs.trans (hf'.trans (Reaches.next ha (hb'.trans (Reaches.next hh (Reaches.refl _)))))
    simpa [r, scanConfig, scanLeftConfig, Nat.two_mul, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using h

def countedInput : Machine := appendMachine prepare counter
def inputTime (n : Nat) : Nat := 2 * n + 4 + countTime n 0
def inputPolynomial : Polynomial := ⟨12, 2⟩

/-- From `initial x`, retain exactly `x` and construct its unary length. -/
theorem countedInput_reaches (x : Word) :
    Reaches countedInput (initial x) (inputTime x.length)
      (shiftConfig 7 (finished [] x 0)) := by
  have hp := reaches_append counter (prepare_reaches x)
  have hc := reaches_append_right prepare (counter_reaches [] x 0)
  exact hp.trans hc

theorem inputTime_polynomial (n : Nat) : inputTime n ≤ inputPolynomial.eval n := by
  have hc := countTime_polynomial n 0
  simp only [counterPolynomial, Polynomial.eval, Nat.add_zero] at hc
  have hlinear : 2 * n + 4 ≤ 4 * (n + 1) := by omega
  have hpow : n + 1 ≤ (n + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left (n + 1) (show 1 ≤ n + 1 by omega)
    simpa [Nat.pow_two] using h
  have hfour := Nat.mul_le_mul_left 4 hpow
  simp only [inputTime, inputPolynomial, Polynomial.eval]
  omega

end Issue624.UnaryCounter
