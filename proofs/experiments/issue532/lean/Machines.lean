import proofs.complexity.lean.Complexity

/-!
# Issue #532: machine-level infrastructure shared by the idea files

Every cost statement in the idea files that concerns P versus NP is stated over
the repository's single machine model `proofs/complexity/lean/Complexity.lean`:
a decider is a `Complexity.Machine` and its time is the step count `t` of a
`Complexity.Run`. This file supplies the general facts the idea files need.

* `run_deterministic`: a machine has at most one run from a configuration.
* `PolyDec`, `polyDec_iff_inP`: a polynomial-time machine decider, and its
  equivalence with `Complexity.InP`.
* `Reaches`, `Computes`, `PolyReduces`: function-computing machines and
  polynomial-time many-one reductions.
* `computes_output_length`: a machine's output is at most as long as its input
  plus its running time plus one, so reductions need no separate size bound.
* `compose_run`, `inP_of_promise_reduction`, `inP_of_reduces`: running a
  function machine and then a decider is a run of one composed table (the
  reducer's table followed by the decider's table with shifted state numbers).
  P is closed under reductions, and a machine map into a promise composed with a
  machine that is correct only on the promise decides the whole language.
* `flipMachine`, `inP_complement`, `npEqualsCoNP_of_pEqualsNP`: P is closed
  under complement, so P = NP implies NP = coNP.
* `NPHard`, `NPComplete`, `npComplete_inP_iff`: an NP-complete language is in P
  if and only if P = NP.
* `encMachine_injective`, `diag_not_inP`, `exists_not_inP`,
  `exists_language_not_in_family`: an injective encoding of machines as words,
  a diagonal language outside P, and a Cantor lemma, so statements of the form
  `InP L` are not provable for every `L`.
* `CNF`, `bruteForce_correct`, `encodeCNF`, `decode_encode`, `SAT`, `sat_iff`:
  CNF formulas, the brute-force decider, a lossless binary encoding with a total
  parser, and SAT as a computable `Complexity.Language`.
* `SATInNP`, `SATHard`, `CookLevin`, `inP_sat_iff`: the Cook–Levin theorem
  stated in this model, and "SAT ∈ P ↔ P = NP" under it. The membership half
  `SATInNP` is proved in `SATVerifier.lean` (`SATVerifier.satInNP`) with an
  explicit verifier machine. The hardness half `SATHard` is a known theorem
  that is **not** proved here; every use is an explicit hypothesis named
  `SATHard` or `CookLevin`.
-/

namespace Issue532.Machines

open Complexity

/-! ## Determinism -/

/-- A machine has at most one run from a configuration. -/
theorem run_deterministic {m : Machine} {c : Config} {t t' : Nat} {b b' : Bool}
    (h : Run m c t b) (h' : Run m c t' b') : t = t' ∧ b = b' := by
  induction h generalizing t' with
  | halt hs =>
    cases h' with
    | halt hs' => rw [hs] at hs'; cases hs'; exact ⟨rfl, rfl⟩
    | next hs' _ => rw [hs] at hs'; cases hs'
  | next hs _ ih =>
    cases h' with
    | halt hs' => rw [hs] at hs'; cases hs'
    | next hs' hr' =>
      rw [hs] at hs'
      cases hs'
      obtain ⟨h1, h2⟩ := ih hr'
      exact ⟨by rw [h1], h2⟩

/-! ## Polynomial-time machine deciders -/

/-- `m` decides `L` within the polynomial `p`: on every input it halts within
`p(|x|)` steps with the answer `L x`. -/
def DecidesWithin (m : Machine) (p : Polynomial) (L : Language) : Prop :=
  ∀ x, ∃ t b, t ≤ p.eval x.length ∧ Run m (initial x) t b ∧ b = L x

/-- A polynomial-time machine decider: the decider is a `Complexity.Machine`
and the time is the step count of `Complexity.Run`. -/
def PolyDec (L : Language) : Prop := ∃ (m : Machine) (p : Polynomial), DecidesWithin m p L

theorem inP_of_decidesWithin {m : Machine} {p : Polynomial} {L : Language}
    (h : DecidesWithin m p L) : InP L := by
  refine ⟨⟨L, m, p, fun x => ?_, fun x t b hr => ?_⟩, rfl⟩
  · obtain ⟨t, b, ht, hr, _⟩ := h x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t', b', _, hr', hb'⟩ := h x
    rw [(run_deterministic hr hr').2, hb']

theorem decidesWithin_of_classP (P : ClassP) : DecidesWithin P.machine P.bound P.language := by
  intro x
  obtain ⟨t, b, ht, hr⟩ := P.terminates x
  refine ⟨t, b, ht, hr, ?_⟩
  have := P.correct x t b hr
  cases hb : b <;> cases hL : P.language x <;> simp_all

/-- `PolyDec` is exactly membership in the repository's class P. -/
theorem polyDec_iff_inP (L : Language) : PolyDec L ↔ InP L := by
  constructor
  · rintro ⟨m, p, h⟩
    exact inP_of_decidesWithin h
  · rintro ⟨P, rfl⟩
    exact ⟨P.machine, P.bound, decidesWithin_of_classP P⟩

/-! ## Partial runs -/

/-- `Reaches m c t d`: `t` non-halting steps lead from `c` to `d`. -/
inductive Reaches (m : Machine) : Config → Nat → Config → Prop where
  | refl (c : Config) : Reaches m c 0 c
  | next {c c' d : Config} {t : Nat} :
      step m c = .inr c' → Reaches m c' t d → Reaches m c (t + 1) d

theorem Reaches.run {m : Machine} {c d : Config} {t t' : Nat} {b : Bool}
    (h : Reaches m c t d) (hr : Run m d t' b) : Run m c (t + t') b := by
  induction h with
  | refl => simpa using hr
  | next hs _ ih => rw [Nat.add_right_comm]; exact Run.next hs (ih hr)

theorem Reaches.trans {m : Machine} {c d e : Config} {t u : Nat}
    (h : Reaches m c t d) (hu : Reaches m d u e) : Reaches m c (t + u) e := by
  induction h with
  | refl => simpa using hu
  | next hs _ ih => simpa [Nat.add_right_comm] using Reaches.next hs (ih hu)

/-! ## Tapes that differ only by trailing blanks -/

def blanks (k : Nat) : List Symbol := List.replicate k .blank

/-- A head at the beginning of a list; an empty list scans an implicit blank. -/
def scanConfig (q : Nat) (l : List Symbol) : List Symbol → Config
  | [] => ⟨q, l, .blank, []⟩
  | a :: r => ⟨q, l, a, r⟩

/-- The corresponding view for a scan towards the left. -/
def scanLeftConfig (q : Nat) (r : List Symbol) : List Symbol → Config
  | [] => ⟨q, [], .blank, r⟩
  | a :: l => ⟨q, l, a, r⟩

/-- A looping scan preserves its symbols and charges every right move. -/
theorem scan_right (m : Machine) (q : Nat) (xs l tail : List Symbol)
    (h : ∀ a ∈ xs, m.instruction q a = .move q a .right) :
    Reaches m (scanConfig q l (xs ++ tail)) xs.length
      (scanConfig q (xs.reverse ++ l) tail) := by
  induction xs generalizing l with
  | nil => simpa using Reaches.refl (scanConfig q l tail)
  | cons a xs ih =>
    have hs : step m (scanConfig q l ((a :: xs) ++ tail)) =
        .inr (scanConfig q (a :: l) (xs ++ tail)) := by
      simp only [List.cons_append, scanConfig, step, h a (by simp), moveHead]
      cases xs ++ tail <;> rfl
    have hr := ih (a :: l) (fun s hm => h s (by simp [hm]))
    simpa [List.reverse_cons, List.append_assoc] using Reaches.next hs hr

/-- A looping scan preserves its symbols and charges every left move. -/
theorem scan_left (m : Machine) (q : Nat) (xs r tail : List Symbol)
    (h : ∀ a ∈ xs, m.instruction q a = .move q a .left) :
    Reaches m (scanLeftConfig q r (xs ++ tail)) xs.length
      (scanLeftConfig q (xs.reverse ++ r) tail) := by
  induction xs generalizing r with
  | nil => simpa using Reaches.refl (scanLeftConfig q r tail)
  | cons a xs ih =>
    have hs : step m (scanLeftConfig q r ((a :: xs) ++ tail)) =
        .inr (scanLeftConfig q (a :: r) (xs ++ tail)) := by
      simp only [List.cons_append, scanLeftConfig, step, h a (by simp), moveHead]
      cases xs ++ tail <;> rfl
    have hr := ih (a :: r) (fun s hm => h s (by simp [hm]))
    simpa [List.reverse_cons, List.append_assoc] using Reaches.next hs hr

/-- `r` and `s` agree up to trailing blanks. -/
def BlankPad (r s : List Symbol) : Prop := ∃ u k l, r = u ++ blanks k ∧ s = u ++ blanks l

theorem BlankPad.refl (r : List Symbol) : BlankPad r r :=
  ⟨r, 0, 0, by simp [blanks], by simp [blanks]⟩

theorem BlankPad.symm {r s : List Symbol} (h : BlankPad r s) : BlankPad s r := by
  obtain ⟨u, k, l, hr, hs⟩ := h
  exact ⟨u, l, k, hs, hr⟩

theorem BlankPad.cons {r s : List Symbol} (a : Symbol) (h : BlankPad r s) :
    BlankPad (a :: r) (a :: s) := by
  obtain ⟨u, k, l, hr, hs⟩ := h
  exact ⟨a :: u, k, l, by rw [hr]; rfl, by rw [hs]; rfl⟩

theorem BlankPad.cons_cons {a b : Symbol} {r s : List Symbol} (h : BlankPad (a :: r) (b :: s)) :
    a = b ∧ BlankPad r s := by
  obtain ⟨u, k, l, hr, hs⟩ := h
  cases u with
  | nil =>
    cases k with
    | zero => cases hr
    | succ k =>
      cases l with
      | zero => cases hs
      | succ l =>
        simp only [blanks, List.nil_append, List.replicate_succ, List.cons.injEq] at hr hs
        exact ⟨hr.1.trans hs.1.symm, [], k, l, hr.2, hs.2⟩
  | cons x u =>
    simp only [List.cons_append, List.cons.injEq] at hr hs
    exact ⟨hr.1.trans hs.1.symm, u, k, l, hr.2, hs.2⟩

theorem BlankPad.nil_cons {b : Symbol} {s : List Symbol} (h : BlankPad [] (b :: s)) :
    b = .blank ∧ BlankPad [] s := by
  obtain ⟨u, k, l, hr, hs⟩ := h
  cases u with
  | nil =>
    cases l with
    | zero => cases hs
    | succ l =>
      simp only [blanks, List.nil_append, List.replicate_succ, List.cons.injEq] at hs
      exact ⟨hs.1, [], 0, l, rfl, hs.2⟩
  | cons x u => cases hr

/-- Configurations that differ only by trailing blanks on the right. -/
def Similar (c d : Config) : Prop :=
  c.state = d.state ∧ c.left = d.left ∧ c.head = d.head ∧ BlankPad c.right d.right

theorem Similar.symm {c d : Config} (h : Similar c d) : Similar d c :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem similar_moveHead {c d : Config} (h : Similar c d) (q : Nat) (w : Symbol)
    (dir : Direction) : Similar (moveHead c q w dir) (moveHead d q w dir) := by
  obtain ⟨cs, cl, ch, cr⟩ := c
  obtain ⟨ds, dl, dh, dr⟩ := d
  obtain ⟨_, hl, _, hr⟩ := h
  simp only at hl hr
  subst hl
  cases dir with
  | stay => exact ⟨rfl, rfl, rfl, hr⟩
  | left =>
    cases cl with
    | nil => exact ⟨rfl, rfl, rfl, hr.cons w⟩
    | cons a rest => exact ⟨rfl, rfl, rfl, hr.cons w⟩
  | right =>
    cases cr with
    | nil =>
      cases dr with
      | nil => exact ⟨rfl, rfl, rfl, BlankPad.refl []⟩
      | cons b s =>
        obtain ⟨hb, hs⟩ := hr.nil_cons
        exact ⟨rfl, rfl, hb.symm, hs⟩
    | cons a r =>
      cases dr with
      | nil =>
        obtain ⟨ha, hs⟩ := hr.symm.nil_cons
        exact ⟨rfl, rfl, ha, hs.symm⟩
      | cons b s =>
        obtain ⟨hab, hs⟩ := hr.cons_cons
        exact ⟨rfl, rfl, hab, hs⟩

theorem similar_step {m : Machine} {c d : Config} (h : Similar c d) :
    (∀ b, step m c = .inl b → step m d = .inl b) ∧
      ∀ c', step m c = .inr c' → ∃ d', step m d = .inr d' ∧ Similar c' d' := by
  have hi : m.instruction c.state c.head = m.instruction d.state d.head := by
    rw [h.1, h.2.2.1]
  unfold step
  rw [hi]
  cases m.instruction d.state d.head with
  | halt b => exact ⟨fun _ hb => hb, fun _ hc' => (by cases hc')⟩
  | move q w dir =>
    refine ⟨fun _ hb => (by cases hb), fun c' hc' => ?_⟩
    cases hc'
    exact ⟨_, rfl, similar_moveHead h q w dir⟩

/-- Runs ignore trailing blanks. -/
theorem run_of_similar {m : Machine} {c d : Config} {t : Nat} {b : Bool}
    (hr : Run m c t b) (h : Similar c d) : Run m d t b := by
  induction hr generalizing d with
  | halt hs => exact Run.halt ((similar_step h).1 _ hs)
  | next hs _ ih =>
    obtain ⟨d', hd', hsim⟩ := (similar_step h).2 _ hs
    exact Run.next hd' (ih hsim)

/-! ## Instruction tables: missing rows, shifted tables and concatenation -/

theorem instruction_of_length_le {m : Machine} {q : Nat} (a : Symbol)
    (hq : m.program.length ≤ q) : m.instruction q a = .halt false := by
  unfold Machine.instruction
  rw [List.getElem?_eq_none hq]
  rfl

/-- A non-halting step starts in a state inside the table. -/
theorem state_lt_of_step {m : Machine} {c c' : Config} (h : step m c = .inr c') :
    c.state < m.program.length := by
  apply Nat.lt_of_not_le
  intro hq
  unfold step at h
  rw [instruction_of_length_le c.head hq] at h
  cases h

def shiftInstruction (off : Nat) : Instruction → Instruction
  | .halt b => .halt b
  | .move q w d => .move (q + off) w d

/-- The table of `first` followed by the table of `second` with every state
number increased by `first.program.length`. -/
def appendMachine (first second : Machine) : Machine :=
  ⟨first.program ++ second.program.map (List.map (shiftInstruction first.program.length))⟩

theorem append_instruction_left (first second : Machine) {q : Nat} (a : Symbol)
    (hq : q < first.program.length) :
    (appendMachine first second).instruction q a = first.instruction q a := by
  unfold Machine.instruction appendMachine
  simp only
  rw [List.getElem?_append_left hq]

theorem getD_map_shift (off : Nat) (o : Option Instruction) :
    (o.map (shiftInstruction off)).getD (.halt false) = shiftInstruction off (o.getD (.halt false)) := by
  cases o <;> rfl

theorem append_instruction_right (first second : Machine) (q : Nat) (a : Symbol) :
    (appendMachine first second).instruction (q + first.program.length) a =
      shiftInstruction first.program.length (second.instruction q a) := by
  unfold Machine.instruction appendMachine
  simp only
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel, List.getElem?_map]
  cases second.program[q]? with
  | none => rfl
  | some row =>
    simp only [Option.map_some, Option.bind_some, List.getElem?_map]
    exact getD_map_shift _ _

theorem reaches_append {first : Machine} (second : Machine) {c d : Config} {t : Nat}
    (h : Reaches first c t d) : Reaches (appendMachine first second) c t d := by
  induction h with
  | refl c => exact Reaches.refl c
  | next hs _ ih =>
    refine Reaches.next ?_ ih
    have hlt := state_lt_of_step hs
    unfold step at hs ⊢
    rw [append_instruction_left first second _ hlt]
    exact hs

def shiftConfig (off : Nat) (c : Config) : Config := ⟨c.state + off, c.left, c.head, c.right⟩

theorem moveHead_shift (c : Config) (off q : Nat) (w : Symbol) (dir : Direction) :
    moveHead (shiftConfig off c) (q + off) w dir = shiftConfig off (moveHead c q w dir) := by
  obtain ⟨s, l, h, r⟩ := c
  cases dir <;> cases l <;> cases r <;> rfl

theorem run_append {second : Machine} (first : Machine) {c : Config} {t : Nat} {b : Bool}
    (h : Run second c t b) :
    Run (appendMachine first second) (shiftConfig first.program.length c) t b := by
  induction h with
  | halt hs =>
    apply Run.halt
    unfold step at hs ⊢
    simp only [shiftConfig]
    rw [append_instruction_right]
    cases hins : second.instruction _ _ with
    | halt b' => rw [hins] at hs; exact hs
    | move q w d => rw [hins] at hs; cases hs
  | @next c c' t b hs _ ih =>
    apply Run.next _ ih
    unfold step at hs ⊢
    simp only [shiftConfig]
    rw [append_instruction_right]
    cases hins : second.instruction c.state c.head with
    | halt b' => rw [hins] at hs; cases hs
    | move q w d =>
      rw [hins] at hs
      cases hs
      exact congrArg Sum.inr (moveHead_shift c _ q w d)

/-- Non-halting computations also embed in the shifted second table. -/
theorem reaches_append_right {second : Machine} (first : Machine) {c d : Config} {t : Nat}
    (h : Reaches second c t d) :
    Reaches (appendMachine first second) (shiftConfig first.program.length c) t
      (shiftConfig first.program.length d) := by
  induction h with
  | refl => exact Reaches.refl _
  | @next c c' d t hs _ ih =>
    apply Reaches.next _ ih
    unfold step at hs ⊢
    simp only [shiftConfig]
    rw [append_instruction_right]
    cases hins : second.instruction c.state c.head with
    | halt b => rw [hins] at hs; cases hs
    | move q w dir =>
      rw [hins] at hs
      cases hs
      exact congrArg Sum.inr (moveHead_shift c _ q w dir)

/-! ## Function-computing machines and reductions -/

/-- `m` computes `f` within the polynomial `p`: from `initial x` it reaches,
after at most `p(|x|)` steps, the state `m.program.length` just past its table,
with the head on the leftmost cell and the tape holding `f x` followed by
blanks. -/
def Computes (m : Machine) (f : Word → Word) (p : Polynomial) : Prop :=
  ∀ x, ∃ t c, t ≤ p.eval x.length ∧ Reaches m (initial x) t c ∧
    c.state = m.program.length ∧ c.left = [] ∧
    ∃ k, c.head :: c.right = (f x).map Symbol.ofBool ++ blanks k

/-- Polynomial-time many-one reduction in the machine model: a machine computes
`f` in polynomial time and `L x = L' (f x)`. -/
def PolyReduces (L L' : Language) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p ∧ ∀ x, L x = L' (f x)

/-! ## Tape size grows by at most one cell per step -/

def tapeSize (c : Config) : Nat := c.left.length + 1 + c.right.length

theorem tapeSize_moveHead (c : Config) (q : Nat) (w : Symbol) (dir : Direction) :
    tapeSize (moveHead c q w dir) ≤ tapeSize c + 1 := by
  obtain ⟨s, l, h, r⟩ := c
  cases dir <;> cases l <;> cases r <;> simp [moveHead, tapeSize] <;> omega

theorem tapeSize_reaches {m : Machine} {c d : Config} {t : Nat} (h : Reaches m c t d) :
    tapeSize d ≤ tapeSize c + t := by
  induction h with
  | refl => exact Nat.le_add_right _ _
  | @next c c' d t hs _ ih =>
    have : tapeSize c' ≤ tapeSize c + 1 := by
      unfold step at hs
      cases hins : m.instruction c.state c.head with
      | halt b => rw [hins] at hs; cases hs
      | move q w dir => rw [hins] at hs; cases hs; exact tapeSize_moveHead c q w dir
    omega

theorem tapeSize_initial (x : Word) : tapeSize (initial x) ≤ x.length + 1 := by
  unfold initial
  cases hx : x.map Symbol.ofBool with
  | nil => simp [initialSymbols, tapeSize]
  | cons a rest =>
    have := congrArg List.length hx
    simp only [List.length_map, List.length_cons] at this
    simp [initialSymbols, tapeSize]
    omega

/-- The output of a machine is at most as long as its input plus its running time plus one. -/
theorem computes_output_length {m : Machine} {f : Word → Word} {p : Polynomial}
    (hm : Computes m f p) (x : Word) : (f x).length ≤ x.length + 1 + p.eval x.length := by
  obtain ⟨t, c, ht, hr, _, hl, k, htape⟩ := hm x
  have h1 := tapeSize_reaches hr
  have h2 := tapeSize_initial x
  have h3 := congrArg List.length htape
  simp only [List.length_cons, List.length_append, List.length_map] at h3
  have h4 : tapeSize c = c.right.length + 1 := by simp [tapeSize, hl]; omega
  omega

/-- The output length of a polynomial-time machine is polynomially bounded. -/
theorem computes_output_poly {m : Machine} {f : Word → Word} {p : Polynomial}
    (hm : Computes m f p) : ∃ q : Polynomial, ∀ x, (f x).length ≤ q.eval x.length := by
  have hb : PolynomiallyBounded (fun n => n + 1 + p.eval n) :=
    PolynomiallyBounded.add polynomiallyBounded_succ ⟨p.coefficient, p.degree, fun _ => Nat.le_refl _⟩
  obtain ⟨q, hq⟩ := (polynomiallyBounded_iff_polynomial _).mp hb
  exact ⟨q, fun x => Nat.le_trans (computes_output_length hm x) (hq x.length)⟩

/-- A partial run that ends in the exit state `m.program.length` is unique:
no step is possible from the exit state. -/
theorem reaches_exit_unique {m : Machine} {c d d' : Config} {t t' : Nat}
    (h : Reaches m c t d) (h' : Reaches m c t' d') (hd : d.state = m.program.length)
    (hd' : d'.state = m.program.length) : d = d' := by
  induction h generalizing t' with
  | refl c =>
    cases h' with
    | refl => rfl
    | next hs _ => exact absurd (state_lt_of_step hs) (by omega)
  | next hs _ ih =>
    cases h' with
    | refl => exact absurd (state_lt_of_step hs) (by omega)
    | next hs' hr' =>
      rw [hs] at hs'
      cases hs'
      exact ih hr' hd

theorem map_ofBool_blanks_injective {u v : Word} {k l : Nat}
    (h : u.map Symbol.ofBool ++ blanks k = v.map Symbol.ofBool ++ blanks l) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v =>
      cases k with
      | zero => cases h
      | succ k => cases b <;> cases h
  | cons a u ih =>
    cases v with
    | nil =>
      cases l with
      | zero => cases h
      | succ l => cases a <;> cases h
    | cons b v =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have hab : a = b := by cases a <;> cases b <;> first | rfl | cases h.1
      rw [hab, ih h.2]

/-- A machine computes at most one function. -/
theorem computes_unique {m : Machine} {f g : Word → Word} {p q : Polynomial}
    (hf : Computes m f p) (hg : Computes m g q) : f = g := by
  funext x
  obtain ⟨_, c, _, hc, hcs, _, k, hck⟩ := hf x
  obtain ⟨_, d, _, hd, hds, _, l, hdl⟩ := hg x
  have := reaches_exit_unique hc hd hcs hds
  subst this
  rw [hck] at hdl
  exact map_ofBool_blanks_injective hdl

theorem similar_initial (y : Word) (c : Config) (off : Nat) (hs : c.state = off)
    (hl : c.left = []) (k : Nat) (ht : c.head :: c.right = y.map Symbol.ofBool ++ blanks k) :
    Similar (shiftConfig off (initial y)) c := by
  obtain ⟨cs, cl, ch, cr⟩ := c
  simp only at hs hl ht
  subst hs hl
  unfold initial
  cases hy : y.map Symbol.ofBool with
  | nil =>
    rw [hy, List.nil_append] at ht
    cases k with
    | zero => cases ht
    | succ k =>
      simp only [blanks, List.replicate_succ, List.cons.injEq] at ht
      refine ⟨Nat.zero_add _, rfl, ht.1.symm, [], 0, k, rfl, ht.2⟩
  | cons a rest =>
    rw [hy, List.cons_append, List.cons.injEq] at ht
    exact ⟨Nat.zero_add _, rfl, ht.1.symm, rest, 0, k, by simp [blanks, shiftConfig, initialSymbols], ht.2⟩

theorem polynomial_eval_mono (p : Polynomial) {n n' : Nat} (h : n ≤ n') : p.eval n ≤ p.eval n' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ h) _)

/-- **Composition.** Running a machine for `f` and then a machine `d` on its
output is a run of the table `appendMachine m d` on the original input. -/
theorem compose_run {m d : Machine} {f : Word → Word} {p : Polynomial} (hm : Computes m f p)
    (x : Word) {t : Nat} {b : Bool} (hr : Run d (initial (f x)) t b) :
    ∃ t1, t1 ≤ p.eval x.length ∧ Run (appendMachine m d) (initial x) (t1 + t) b := by
  obtain ⟨t1, c, ht1, hreach, hstate, hleft, k, htape⟩ := hm x
  have hsim := similar_initial (f x) c m.program.length hstate hleft k htape
  exact ⟨t1, ht1, (reaches_append d hreach).run (run_of_similar (run_append m hr) hsim)⟩

/-- The time bound of a composition: `p(n) + p'(q(n))` is polynomially bounded. -/
theorem compose_bound (p p' q : Polynomial) :
    ∃ B : Polynomial, ∀ n, p.eval n + p'.eval (q.eval n) ≤ B.eval n :=
  (polynomiallyBounded_iff_polynomial _).mp
    (PolynomiallyBounded.add ⟨p.coefficient, p.degree, fun _ => Nat.le_refl _⟩
      (PolynomiallyBounded.comp ⟨p'.coefficient, p'.degree, fun _ => Nat.le_refl _⟩
        ⟨q.coefficient, q.degree, fun _ => Nat.le_refl _⟩))

/-- A machine decides `L` within `p` on every word of the promise `Pr`. -/
def DecidesOn (m : Machine) (p : Polynomial) (Pr : Word → Prop) (L : Language) : Prop :=
  ∀ x, Pr x → ∃ t b, t ≤ p.eval x.length ∧ Run m (initial x) t b ∧ b = L x

/-- **Promise composition** (machine construction). A polynomial-time machine map
`f` into the promise `Pr` that preserves the answer, followed by a polynomial-time
machine that is correct only on `Pr`, decides `L` in polynomial time. -/
theorem inP_of_promise_reduction {L M : Language} {Pr : Word → Prop} {m d : Machine}
    {f : Word → Word} {p p' : Polynomial} (hm : Computes m f p) (hinto : ∀ x, Pr (f x))
    (hpres : ∀ x, L x = M (f x)) (hd : DecidesOn d p' Pr M) : InP L := by
  obtain ⟨q, hq⟩ := computes_output_poly hm
  obtain ⟨B, hB⟩ := compose_bound p p' q
  have key : DecidesWithin (appendMachine m d) B L := by
    intro x
    obtain ⟨t2, b, ht2, hrun, hb⟩ := hd (f x) (hinto x)
    obtain ⟨t1, ht1, hrun'⟩ := compose_run hm x hrun
    refine ⟨t1 + t2, b, ?_, hrun', by rw [hb, hpres]⟩
    have := polynomial_eval_mono p' (hq x)
    have := hB x.length
    omega
  exact inP_of_decidesWithin key

/-- **P is closed under polynomial-time reductions** (machine construction). -/
theorem inP_of_reduces {L L' : Language} (hr : PolyReduces L L') (hp : InP L') : InP L := by
  obtain ⟨m, f, p, hm, hf⟩ := hr
  obtain ⟨d, p', hd⟩ := (polyDec_iff_inP L').mpr hp
  exact inP_of_promise_reduction (Pr := fun _ => True) hm (fun _ => trivial) hf
    (fun y _ => hd y)

/-! ## P is closed under complement

`flipMachine m` normalises every row of `m` to all four symbols, sends every
out-of-table target to one extra state, and negates every halting answer, so a
missing instruction (which rejects in `m`) accepts in `flipMachine m`. -/

def flipInstruction (n : Nat) : Instruction → Instruction
  | .halt b => .halt (!b)
  | .move q w dir => .move (min q n) w dir

def flipRow (n : Nat) (row : List Instruction) : List Instruction :=
  (List.range 4).map fun i => flipInstruction n (row.getD i (.halt false))

def flipMachine (m : Machine) : Machine :=
  ⟨m.program.map (flipRow m.program.length) ++ [List.replicate 4 (.halt true)]⟩

theorem symbol_index_lt (a : Symbol) : a.index < 4 := by cases a <;> decide

theorem flip_instruction (m : Machine) (q : Nat) (a : Symbol) :
    (flipMachine m).instruction (min q m.program.length) a =
      flipInstruction m.program.length (m.instruction q a) := by
  have ha := symbol_index_lt a
  unfold Machine.instruction flipMachine
  by_cases hq : q < m.program.length
  · rw [Nat.min_eq_left (Nat.le_of_lt hq)]
    rw [List.getElem?_append_left (by simpa using hq)]
    simp only [List.getElem?_map, List.getElem?_eq_getElem hq, Option.map_some, Option.bind_some]
    simp only [flipRow, List.getElem?_map, List.getElem?_range ha, Option.map_some,
      Option.getD_some, List.getD_eq_getElem?_getD]
  · have hq' : m.program.length ≤ q := Nat.le_of_not_lt hq
    rw [Nat.min_eq_right hq']
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.bind_some,
      List.getElem?_replicate, ha, ite_true, Option.getD_some]
    rw [List.getElem?_eq_none (by omega)]
    rfl

def normState (n : Nat) (c : Config) : Config := ⟨min c.state n, c.left, c.head, c.right⟩

theorem moveHead_normState (n : Nat) (c : Config) (q : Nat) (w : Symbol) (dir : Direction) :
    moveHead (normState n c) (min q n) w dir = normState n (moveHead c q w dir) := by
  obtain ⟨s, l, h, r⟩ := c
  cases dir <;> cases l <;> cases r <;> rfl

theorem step_flip (m : Machine) (c : Config) :
    step (flipMachine m) (normState m.program.length c) =
      match step m c with
      | .inl b => .inl (!b)
      | .inr c' => .inr (normState m.program.length c') := by
  unfold step
  rw [show (normState m.program.length c).state = min c.state m.program.length from rfl,
    show (normState m.program.length c).head = c.head from rfl, flip_instruction]
  cases m.instruction c.state c.head with
  | halt b => rfl
  | move q w dir => simp only [flipInstruction]; rw [moveHead_normState]

theorem run_flip {m : Machine} {c : Config} {t : Nat} {b : Bool} (h : Run m c t b) :
    Run (flipMachine m) (normState m.program.length c) t (!b) := by
  induction h with
  | halt hs => exact Run.halt (by rw [step_flip, hs])
  | next hs _ ih => exact Run.next (by rw [step_flip, hs]) ih

theorem normState_initial (n : Nat) (x : Word) : normState n (initial x) = initial x := by
  unfold initial normState
  cases x.map Symbol.ofBool <;> simp [initialSymbols]

/-- The complement of a language. -/
def complement (L : Language) : Language := fun x => !L x

/-- **P is closed under complement** (machine construction `flipMachine`). -/
theorem inP_complement {L : Language} (h : InP L) : InP (complement L) := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  apply inP_of_decidesWithin (m := flipMachine m) (p := p)
  intro x
  obtain ⟨t, b, ht, hr, hb⟩ := hm x
  refine ⟨t, !b, ht, ?_, by rw [hb]; rfl⟩
  have := run_flip hr
  rwa [normState_initial] at this

theorem complement_complement (L : Language) : complement (complement L) = L := by
  funext x; simp [complement]

/-- coNP in the shared model. -/
def InCoNP (L : Language) : Prop := InNP (complement L)

def NPEqualsCoNP : Prop := ∀ L, InNP L ↔ InCoNP L

/-- P = NP implies NP = coNP (fully proved: `flipMachine` and `ClassP.toNP`). -/
theorem npEqualsCoNP_of_pEqualsNP (h : PEqualsNP) : NPEqualsCoNP := by
  intro L
  constructor
  · intro hL
    exact pSubsetNP _ (inP_complement (h L hL))
  · intro hL
    have := inP_complement (h _ hL)
    rw [complement_complement] at this
    exact pSubsetNP _ this

/-- NP ≠ coNP implies P ≠ NP. -/
theorem pNotEqualsNP_of_npNeCoNP (h : ¬ NPEqualsCoNP) : PNotEqualsNP :=
  fun hp => h (npEqualsCoNP_of_pEqualsNP hp)

/-! ## NP-completeness -/

def NPHard (L : Language) : Prop := ∀ L', InNP L' → PolyReduces L' L

def NPComplete (L : Language) : Prop := InNP L ∧ NPHard L

/-- An NP-complete language is in P if and only if P = NP. -/
theorem npComplete_inP_iff {L : Language} (h : NPComplete L) : InP L ↔ PEqualsNP := by
  constructor
  · intro hL L' hL'
    exact inP_of_reduces (h.2 L' hL') hL
  · intro hPNP
    exact hPNP L h.1

/-! ## Non-vacuity: a language outside P

Machines are encoded injectively as words; the diagonal language rejects the
code of every machine that accepts its own code. -/

/-- Prefix-free encodings: the code of `a` is not a proper prefix of another code. -/
def PrefixFree {α : Type} (e : α → Word) : Prop :=
  ∀ a b r s, e a ++ r = e b ++ s → a = b ∧ r = s

def encNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: encNat n

theorem encNat_prefixFree : PrefixFree encNat := by
  intro a
  induction a with
  | zero =>
    intro b r s h
    cases b with
    | zero => simp only [encNat, List.cons_append, List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h.2⟩
    | succ b => simp [encNat] at h
  | succ a ih =>
    intro b r s h
    cases b with
    | zero => simp [encNat] at h
    | succ b =>
      simp only [encNat, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih b r s h
      exact ⟨by rw [h1], h2⟩

def directionIndex : Direction → Nat
  | .left => 0
  | .right => 1
  | .stay => 2

def encInstruction : Instruction → Word
  | .halt b => [false, b]
  | .move q w d => true :: (encNat q ++ encNat w.index ++ encNat (directionIndex d))

theorem symbol_index_injective {a b : Symbol} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem direction_index_injective {a b : Direction} (h : directionIndex a = directionIndex b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem encInstruction_prefixFree : PrefixFree encInstruction := by
  intro a b r s h
  cases a with
  | halt x =>
    cases b with
    | halt y =>
      simp only [encInstruction, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨by rw [h.1], h.2⟩
    | move q w d => simp [encInstruction] at h
  | move q w d =>
    cases b with
    | halt y => simp [encInstruction] at h
    | move q' w' d' =>
      simp only [encInstruction, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at h
      obtain ⟨hq, h1⟩ := encNat_prefixFree _ _ _ _ h
      obtain ⟨hw, h2⟩ := encNat_prefixFree _ _ _ _ h1
      obtain ⟨hd, h3⟩ := encNat_prefixFree _ _ _ _ h2
      subst hq
      rw [symbol_index_injective hw, direction_index_injective hd]
      exact ⟨rfl, h3⟩

def encList {α : Type} (e : α → Word) : List α → Word
  | [] => [false]
  | a :: l => true :: (e a ++ encList e l)

theorem encList_prefixFree {α : Type} {e : α → Word} (he : PrefixFree e) :
    PrefixFree (encList e) := by
  intro a
  induction a with
  | nil =>
    intro b r s h
    cases b with
    | nil => simp only [encList, List.cons_append, List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h.2⟩
    | cons y l => simp [encList] at h
  | cons x l ih =>
    intro b r s h
    cases b with
    | nil => simp [encList] at h
    | cons y l' =>
      simp only [encList, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨hxy, h⟩ := he _ _ _ _ h
      obtain ⟨hl, h⟩ := ih _ _ _ h
      exact ⟨by rw [hxy, hl], h⟩

/-- The code of a machine: its instruction table, row by row. -/
def encMachine (m : Machine) : Word := encList (encList encInstruction) m.program

theorem encMachine_injective {m m' : Machine} (h : encMachine m = encMachine m') : m = m' := by
  have := (encList_prefixFree (encList_prefixFree encInstruction_prefixFree)) m.program m'.program
    [] [] (by simpa [encMachine] using h)
  cases m; cases m'
  simp only at this
  rw [this.1]

open Classical in
/-- The diagonal language: `w` is in it unless `w` is the code of a machine
that accepts `w`. -/
noncomputable def Diag : Language := fun w =>
  decide (¬ ∃ m : Machine, encMachine m = w ∧ ∃ t, Run m (initial w) t true)

/-- **Diagonalisation.** No machine decides `Diag` (in any time bound). -/
theorem diag_not_inP : ¬ InP Diag := by
  rintro ⟨P, hP⟩
  let w := encMachine P.machine
  obtain ⟨t, b, _, hr⟩ := P.terminates w
  have hc := P.correct w t b hr
  rw [hP] at hc
  cases b with
  | true =>
    have hd : Diag w = true := hc.mpr rfl
    simp only [Diag, decide_eq_true_eq] at hd
    exact hd ⟨P.machine, rfl, t, hr⟩
  | false =>
    have hd : ¬ Diag w = true := fun h => Bool.noConfusion (hc.mp h)
    simp only [Diag, decide_eq_true_eq, Classical.not_not] at hd
    obtain ⟨m, hm, t', hr'⟩ := hd
    have := encMachine_injective hm
    subst this
    exact Bool.noConfusion (run_deterministic hr hr').2

/-- Statements `InP L` (equivalently `PolyDec L`) are not provable for every
language: the machine-level obligations are not vacuous. -/
theorem exists_not_inP : ∃ L : Language, ¬ InP L := ⟨Diag, diag_not_inP⟩

theorem not_forall_polyDec : ¬ ∀ L : Language, PolyDec L :=
  fun h => diag_not_inP ((polyDec_iff_inP Diag).mp (h Diag))

/-- **Cantor's argument over words.** A family of languages indexed by a type
with an injective encoding into words misses some language. Applied to
machine-indexed classes this shows their membership predicates are not
vacuous. -/
theorem exists_language_not_in_family {T : Type} (e : T → Word)
    (he : ∀ a b, e a = e b → a = b) (F : T → Language) : ∃ L : Language, ∀ a, F a ≠ L := by
  classical
  refine ⟨fun w => decide (¬ ∃ a, e a = w ∧ F a w = true), fun a hFa => ?_⟩
  have hw := congrFun hFa (e a)
  cases hF : F a (e a) with
  | true =>
    rw [hF] at hw
    have := (decide_eq_true_iff.mp hw.symm)
    exact this ⟨a, rfl, hF⟩
  | false =>
    rw [hF] at hw
    have hex := Classical.not_not.mp (decide_eq_false_iff_not.mp hw.symm)
    obtain ⟨b, hb, hFb⟩ := hex
    have := he b a hb
    subst this
    rw [hF] at hFb
    cases hFb

/-- Machines paired with explicit polynomials also have an injective encoding. -/
def encMachinePoly (x : Machine × Polynomial) : Word :=
  encMachine x.1 ++ encNat x.2.coefficient ++ encNat x.2.degree

theorem encMachinePoly_injective (x y : Machine × Polynomial)
    (h : encMachinePoly x = encMachinePoly y) : x = y := by
  obtain ⟨m, c, d⟩ := x
  obtain ⟨m', c', d'⟩ := y
  simp only [encMachinePoly, encMachine, List.append_assoc] at h
  obtain ⟨hm, h1⟩ := encList_prefixFree (encList_prefixFree encInstruction_prefixFree) _ _ _ _ h
  obtain ⟨hc, h2⟩ := encNat_prefixFree _ _ _ _ h1
  obtain ⟨hd, _⟩ := encNat_prefixFree _ _ [] [] (by simpa using h2)
  cases m; cases m'
  simp only at hm
  subst hm hc hd
  rfl

/-! ## CNF formulas and SAT as a language

Tokens are bit pairs: `11` is a unary tick of the variable index, `0p` ends a
literal with polarity `p`, `10` ends a clause. The literal `(v, p)` is
`11^v 0p`; a clause is its literals followed by `10`. -/

/-- A literal: variable index and polarity (`pos = true` means `x_var`). -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool := a l.var == l.pos

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a : Assignment, evalCNF a φ = true

/-! ### Brute force over the variables that occur (moved from Idea 01) -/

/-- All variables of `φ` are `< n`. -/
def VarsBelow (n : Nat) (φ : CNF) : Prop := ∀ c ∈ φ, ∀ l ∈ c, l.var < n

theorem evalClause_congr (a b : Assignment) (n : Nat) (c : Clause)
    (hab : ∀ i, i < n → a i = b i) (hc : ∀ l ∈ c, l.var < n) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [evalClause, evalLit]
    rw [hab l.var (hc l (List.mem_cons_self ..)),
      ih (fun l' hl' => hc l' (List.mem_cons_of_mem _ hl'))]

/-- Formulas with variables `< n` only look at the first `n` values. -/
theorem evalCNF_congr (a b : Assignment) (n : Nat) (φ : CNF)
    (hab : ∀ i, i < n → a i = b i) (hφ : VarsBelow n φ) :
    evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [evalCNF]
    rw [evalClause_congr a b n c hab (hφ c (List.mem_cons_self ..)),
      ih (fun c' hc' => hφ c' (List.mem_cons_of_mem _ hc'))]

/-! ## Enumerating all assignments -/

/-- All `2^n` bit vectors of length `n` (bit `0` is the head). -/
def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allAssignments n).map (false :: ·) ++ (allAssignments n).map (true :: ·)

/-- Bit vector to assignment: index `i` ↦ bit `i`, `false` beyond the end. -/
def toAssign : List Bool → Assignment
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v, i + 1 => toAssign v i

/-- The first `n` values of an assignment, as a bit vector. -/
def prefixOf (a : Assignment) : Nat → List Bool
  | 0 => []
  | n + 1 => a 0 :: prefixOf (fun i => a (i + 1)) n

/-- The enumeration contains exactly the vectors of length `n`. -/
theorem mem_allAssignments_iff (n : Nat) (v : List Bool) :
    v ∈ allAssignments n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v => simp [allAssignments]
  | succ n ih =>
    cases v with
    | nil => simp [allAssignments]
    | cons b v =>
      cases b <;> simp [allAssignments, ih]

theorem length_prefixOf (a : Assignment) (n : Nat) : (prefixOf a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [prefixOf, ih]

theorem toAssign_prefixOf (a : Assignment) (n i : Nat) (h : i < n) :
    toAssign (prefixOf a n) i = a i := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => a (j + 1)) i (by omega)

/-! ## The brute-force decider -/

/-- Try every vector of length `n`. -/
def bruteForce (n : Nat) (φ : CNF) : Bool :=
  (allAssignments n).any (fun v => evalCNF (toAssign v) φ)

/-- Soundness: acceptance yields a satisfying assignment. -/
theorem brute_force_sound (n : Nat) (φ : CNF) :
    bruteForce n φ = true → Satisfiable φ := by
  intro h
  obtain ⟨v, _, hv⟩ := List.any_eq_true.mp h
  exact ⟨toAssign v, hv⟩

/-- Completeness: if all variables are `< n`, every satisfiable formula is
accepted, because every assignment agrees on `0, …, n-1` with a listed vector. -/
theorem brute_force_complete (n : Nat) (φ : CNF) (hφ : VarsBelow n φ) :
    Satisfiable φ → bruteForce n φ = true := by
  intro ⟨a, ha⟩
  apply List.any_eq_true.mpr
  refine ⟨prefixOf a n, (mem_allAssignments_iff n _).mpr (length_prefixOf a n), ?_⟩
  rw [evalCNF_congr (toAssign (prefixOf a n)) a n φ
    (fun i hi => toAssign_prefixOf a n i hi) hφ]
  exact ha

/-! ## Number of variables -/

def clauseBound : Clause → Nat
  | [] => 0
  | l :: c => max (l.var + 1) (clauseBound c)

/-- One more than the largest variable index (0 for variable-free formulas). -/
def numVars : CNF → Nat
  | [] => 0
  | c :: φ => max (clauseBound c) (numVars φ)

theorem lt_clauseBound (c : Clause) : ∀ l ∈ c, l.var < clauseBound c := by
  induction c with
  | nil => intro l hl; cases hl
  | cons l c ih =>
    intro l' hl'
    simp only [clauseBound]
    rcases List.mem_cons.mp hl' with h | h
    · subst h; omega
    · have := ih l' h; omega

theorem varsBelow_numVars (φ : CNF) : VarsBelow (numVars φ) φ := by
  induction φ with
  | nil => intro c hc; cases hc
  | cons c φ ih =>
    intro c' hc' l hl
    simp only [numVars]
    rcases List.mem_cons.mp hc' with h | h
    · subst h; have := lt_clauseBound c' l hl; omega
    · have := ih c' h l hl; omega

/-- The uniform decider: brute force over the variables that occur. -/
theorem bruteForce_correct (φ : CNF) :
    bruteForce (numVars φ) φ = true ↔ Satisfiable φ :=
  ⟨brute_force_sound _ φ, brute_force_complete _ φ (varsBelow_numVars φ)⟩

/-! ### The word encoding -/

def ticks : Nat → List Bool
  | 0 => []
  | k + 1 => true :: true :: ticks k

def encodeLit (l : Lit) : List Bool := ticks l.var ++ [false, l.pos]

def encodeClause : Clause → List Bool
  | [] => [true, false]
  | l :: c => encodeLit l ++ encodeClause c

def encodeCNF : CNF → List Bool
  | [] => []
  | c :: φ => encodeClause c ++ encodeCNF φ

/-- The literal encoding charges two bits for every unary variable tick. -/
theorem ticks_length (n : Nat) : (ticks n).length = 2 * n := by
  induction n <;> simp_all [ticks]; omega

theorem encodeLit_length (l : Lit) : (encodeLit l).length = 2 * l.var + 2 := by
  simp [encodeLit, ticks_length]

def decodeAux : List Bool → Nat → Clause → CNF
  | true :: true :: rest, k, cur => decodeAux rest (k + 1) cur
  | false :: p :: rest, k, cur => decodeAux rest 0 (cur ++ [⟨k, p⟩])
  | true :: false :: rest, _, cur => cur :: decodeAux rest 0 []
  | _, _, _ => []

def decode (w : List Bool) : CNF := decodeAux w 0 []

theorem decodeAux_ticks (v : Nat) (r : List Bool) (k : Nat) (cur : Clause) :
    decodeAux (ticks v ++ r) k cur = decodeAux r (k + v) cur := by
  induction v generalizing k with
  | zero => rfl
  | succ v ih =>
    simp only [ticks, List.cons_append, decodeAux]
    rw [ih]; congr 1; omega

theorem decodeAux_clause (c : Clause) (r : List Bool) (cur : Clause) :
    decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 [] := by
  induction c generalizing cur with
  | nil => simp [encodeClause, decodeAux]
  | cons l c ih =>
    simp only [encodeClause, encodeLit, List.append_assoc]
    rw [decodeAux_ticks]
    simp only [List.cons_append, List.nil_append, decodeAux, Nat.zero_add]
    rw [ih]; simp

theorem decode_encode (φ : CNF) : decode (encodeCNF φ) = φ := by
  unfold decode
  induction φ with
  | nil => simp [encodeCNF, decodeAux]
  | cons c φ ih =>
    simp only [encodeCNF]
    rw [decodeAux_clause, ih]; rfl

/-- Distinct formulas have distinct encodings. -/
theorem encode_injective {φ ψ : CNF} (h : encodeCNF φ = encodeCNF ψ) : φ = ψ := by
  rw [← decode_encode φ, h, decode_encode]

/-- SAT as a language of the shared model. Every word denotes a formula through
the total parser `decode` (malformed tails are dropped), so a machine for SAT
never needs a separate well-formedness check; on encodings, `decode` inverts
`encodeCNF` (`decode_encode`). The definition is the exponential brute-force
search, which is computable and correct (`sat_iff`). -/
def SAT : Language := fun w => bruteForce (numVars (decode w)) (decode w)

theorem sat_iff (w : Word) : SAT w = true ↔ Satisfiable (decode w) :=
  bruteForce_correct (decode w)

theorem sat_encode (φ : CNF) : SAT (encodeCNF φ) = true ↔ Satisfiable φ := by
  rw [sat_iff, decode_encode]

/-! ## The Cook–Levin theorem, stated in this model

`CookLevin` is a precise proposition about `Complexity.Machine`, `Complexity.Run`
and the class NP of `Complexity.ClassNP`. It is a known theorem (Cook 1971,
Levin 1973; mechanised for a different machine model by Gäher and Kunze,
ITP 2021). The membership half `SATInNP` is proved in `SATVerifier.lean`
(`SATVerifier.satInNP`, a 45-state verifier that halts within `5(n+1)²`
steps), which imports this file. The hardness half `SATHard` needs the
tableau reduction and is **not proved here**. Idea files that use it take
`SATHard` or `CookLevin` as a named explicit hypothesis. -/

/-- SAT is in NP: a polynomial-time machine verifier for SAT. -/
def SATInNP : Prop := InNP SAT

/-- SAT is NP-hard: every NP language reduces to SAT by a polynomial-time machine. -/
def SATHard : Prop := NPHard SAT

def CookLevin : Prop := NPComplete SAT

theorem cookLevin_iff : CookLevin ↔ SATInNP ∧ SATHard := Iff.rfl

/-- A polynomial-time machine decider for SAT gives P = NP; needs only the
hardness half of Cook–Levin. -/
theorem pEqualsNP_of_inP_sat (hard : SATHard) (h : InP SAT) : PEqualsNP :=
  fun L hL => inP_of_reduces (hard L hL) h

/-- P = NP gives a polynomial-time machine decider for SAT; needs only the
membership half of Cook–Levin. -/
theorem inP_sat_of_pEqualsNP (mem : SATInNP) (h : PEqualsNP) : InP SAT := h SAT mem

/-- Given Cook–Levin, deciding SAT in polynomial time on the shared machine
model is equivalent to P = NP. -/
theorem inP_sat_iff (hCL : CookLevin) : InP SAT ↔ PEqualsNP := npComplete_inP_iff hCL

/-- A decider for `SAT` decides satisfiability on encodings of formulas. -/
theorem inP_sat_on_encodings (h : InP SAT) :
    ∃ (m : Machine) (p : Polynomial), ∀ φ : CNF, ∃ t b,
      t ≤ p.eval (encodeCNF φ).length ∧ Run m (initial (encodeCNF φ)) t b ∧
        (b = true ↔ Satisfiable φ) := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP SAT).mpr h
  refine ⟨m, p, fun φ => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm (encodeCNF φ)
  exact ⟨t, b, ht, hr, by rw [hb]; exact sat_encode φ⟩

end Issue532.Machines
