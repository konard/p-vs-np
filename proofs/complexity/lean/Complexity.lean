/-!
Finite, deterministic single-tape machines for the complexity statements in this
repository. A program is a finite table of instructions. The initial state is
fixed, and only one table instruction is executed per step. In particular,
neither the initial configuration nor the transition function can inspect an
arbitrary language predicate.

The alphabet has a blank and a separator in addition to the two input bits.
The `paired` verifier receives `input ++ [separator] ++ certificate`; the
`ignoreCertificate` verifier runs a decider on the input alone.
-/

namespace Complexity

abbrev Word := List Bool
abbrev Language := Word → Bool

inductive Symbol where
  | blank | zero | one | separator
  deriving DecidableEq, Repr

def Symbol.ofBool : Bool → Symbol
  | false => .zero
  | true => .one

def Symbol.index : Symbol → Nat
  | .blank => 0
  | .zero => 1
  | .one => 2
  | .separator => 3

inductive Direction where
  | left | right | stay
  deriving DecidableEq, Repr

inductive Instruction where
  | halt (answer : Bool)
  | move (nextState : Nat) (write : Symbol) (direction : Direction)
  deriving DecidableEq, Repr

/-- State `q` and scanned symbol `a` select row `q`, column `a`.
    A missing instruction rejects. The table is finite data, not a function. -/
structure Machine where
  program : List (List Instruction)
  deriving Repr

structure Config where
  state : Nat
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving Repr

def initialSymbols : List Symbol → Config
  | [] => ⟨0, [], .blank, []⟩
  | a :: rest => ⟨0, [], a, rest⟩

def initial (input : Word) : Config :=
  initialSymbols (input.map Symbol.ofBool)

def pairedInput (input certificate : Word) : Config :=
  initialSymbols (input.map Symbol.ofBool ++ [.separator] ++ certificate.map Symbol.ofBool)

def Machine.instruction (m : Machine) (q : Nat) (a : Symbol) : Instruction :=
  ((m.program[q]?).bind fun row => row[a.index]?).getD (.halt false)

def moveHead (c : Config) (next : Nat) (write : Symbol) : Direction → Config
  | .stay => ⟨next, c.left, write, c.right⟩
  | .left => match c.left with
      | [] => ⟨next, [], .blank, write :: c.right⟩
      | a :: rest => ⟨next, rest, a, write :: c.right⟩
  | .right => match c.right with
      | [] => ⟨next, write :: c.left, .blank, []⟩
      | a :: rest => ⟨next, write :: c.left, a, rest⟩

/-- One charged machine instruction. `Sum.inl` is a halting answer. -/
def step (m : Machine) (c : Config) : Bool ⊕ Config :=
  match m.instruction c.state c.head with
  | .halt b => .inl b
  | .move next write dir => .inr (moveHead c next write dir)

inductive Run (m : Machine) : Config → Nat → Bool → Prop where
  | halt {c b} : step m c = .inl b → Run m c 1 b
  | next {c c' t b} : step m c = .inr c' → Run m c' t b → Run m c (t + 1) b

/-- An explicit polynomial with a nonzero base at input length zero. -/
structure Polynomial where
  coefficient : Nat
  degree : Nat
  deriving Repr

def Polynomial.eval (p : Polynomial) (n : Nat) : Nat :=
  p.coefficient * (n + 1) ^ p.degree

structure ClassP where
  language : Language
  machine : Machine
  bound : Polynomial
  terminates : ∀ x, ∃ t b, t ≤ bound.eval x.length ∧ Run machine (initial x) t b
  correct : ∀ x t b, Run machine (initial x) t b → (language x = true ↔ b = true)

inductive VerifierProgram where
  | ignoreCertificate (machine : Machine)
  | paired (machine : Machine)

def VerifierProgram.Run (v : VerifierProgram) (x cert : Word)
    (t : Nat) (b : Bool) : Prop :=
  match v with
  | .ignoreCertificate m => Complexity.Run m (initial x) t b
  | .paired m => Complexity.Run m (pairedInput x cert) t b

def VerifierProgram.timeLimit (v : VerifierProgram) (p : Polynomial)
    (x cert : Word) : Nat :=
  match v with
  | .ignoreCertificate _ => p.eval x.length
  | .paired _ => p.eval (x.length + cert.length + 1)

structure ClassNP where
  language : Language
  verifier : VerifierProgram
  timeBound : Polynomial
  certBound : Polynomial
  terminates : ∀ x cert, cert.length ≤ certBound.eval x.length →
    ∃ t b, t ≤ verifier.timeLimit timeBound x cert ∧ verifier.Run x cert t b
  correct : ∀ x, language x = true ↔
    ∃ cert t, cert.length ≤ certBound.eval x.length ∧
      t ≤ verifier.timeLimit timeBound x cert ∧ verifier.Run x cert t true

def InP (language : Language) : Prop :=
  ∃ p : ClassP, p.language = language

def InNP (language : Language) : Prop :=
  ∃ np : ClassNP, np.language = language

def PEqualsNP : Prop := ∀ language, InNP language → InP language
def PNotEqualsNP : Prop := ¬PEqualsNP

/-- The verifier reads no certificate; the empty one witnesses acceptance. -/
def ClassP.toNP (p : ClassP) : ClassNP where
  language := p.language
  verifier := .ignoreCertificate p.machine
  timeBound := p.bound
  certBound := ⟨0, 0⟩
  terminates := by
    intro x cert _
    exact p.terminates x
  correct := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, b, ht, hr⟩ := p.terminates x
      have hb : b = true := (p.correct x t b hr).mp hx
      subst b
      exact ⟨[], t, Nat.zero_le _, ht, hr⟩
    · rintro ⟨cert, t, _, _, hr⟩
      exact (p.correct x t true hr).mpr rfl

theorem pSubsetNP (language : Language) : InP language → InNP language := by
  rintro ⟨p, hp⟩
  exact ⟨p.toNP, hp⟩

end Complexity
