import proofs.complexity.lean.Complexity

/-!
HISTORICAL TOY MODEL: The P/NP class predicates below use separate machine and
runtime semantics. Reductions reuse the shared finite machine representation,
but are not linked to the class predicates. Results in this file do not settle
the Clay P versus NP problem.
-/

/-
  PvsNP.lean - Formal specification and test/check for P vs NP

  This file provides a formal framework for reasoning about the P vs NP problem,
  including definitions of complexity classes and basic verification tests.
-/

namespace PEqNP

/- ## 1. Basic Definitions -/

/-- Binary strings as lists of booleans -/
def BinaryString : Type := List Bool

/-- A decision problem is a predicate on binary strings -/
def DecisionProblem : Type := BinaryString → Prop

/-- Size of input -/
def inputSize (s : BinaryString) : Nat := s.length

/- ## 2. Polynomial Time Complexity -/

/-- A function is polynomial-bounded -/
def IsPolynomial (f : Nat → Nat) : Prop :=
  ∃ (k c : Nat), ∀ n, f n ≤ c * (n ^ k) + c

/-- Constant functions satisfy the polynomial bound. -/
theorem constant_is_poly (c : Nat) : IsPolynomial (fun _ => c) := by
  refine ⟨0, c, ?_⟩
  intro n
  simpa using Nat.le_add_right c c

/-- Linear functions satisfy the polynomial bound. -/
theorem linear_is_poly : IsPolynomial (fun n => n) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simpa using Nat.le_succ n

/-- Quadratic functions satisfy the polynomial bound. -/
theorem quadratic_is_poly : IsPolynomial (fun n => n * n) := by
  refine ⟨2, 1, ?_⟩
  intro n
  simpa [Nat.pow_two] using Nat.le_succ (n * n)

/- ## 3. Deterministic Turing Machine Model -/

/-- Abstract Turing Machine -/
structure TuringMachine where
  states : Nat
  alphabet : Nat
  transition : Nat → Nat → (Nat × Nat × Bool)
  initialState : Nat
  acceptState : Nat
  rejectState : Nat

/-- A configuration has an unbounded tape, a state, and a head position. -/
structure Configuration where
  state : Nat
  tape : Nat → Nat
  head : Nat

/-- The input occupies the first cells; all other cells are blank (zero). -/
def initialConfiguration (M : TuringMachine) (input : BinaryString) : Configuration :=
  { state := M.initialState
    tape := fun i => if input.getD i false then 1 else 0
    head := 0 }

/-- Accepting and rejecting configurations do not take further steps. -/
def step (M : TuringMachine) (c : Configuration) : Configuration :=
  if c.state = M.acceptState ∨ c.state = M.rejectState then c
  else
    let (nextState, symbol, moveRight) := M.transition c.state (c.tape c.head)
    { state := nextState
      tape := fun i => if i = c.head then symbol else c.tape i
      head := if moveRight then c.head + 1 else c.head - 1 }

/-- The configuration after exactly `steps` transitions. -/
def run (M : TuringMachine) (input : BinaryString) : Nat → Configuration
  | 0 => initialConfiguration M input
  | steps + 1 => step M (run M input steps)

/-- A machine accepts an input if it reaches its accepting state. -/
def Accepts (M : TuringMachine) (input : BinaryString) : Prop :=
  ∃ steps, (run M input steps).state = M.acceptState

/-- Time-bounded computation -/
def TMTimeBounded (M : TuringMachine) (time : Nat → Nat) : Prop :=
  ∀ (input : BinaryString),
    ∃ (steps : Nat),
      steps ≤ time (inputSize input) ∧
      ((run M input steps).state = M.acceptState ∨
       (run M input steps).state = M.rejectState)

/- ## 4. Complexity Class P -/

/-- A decision problem L is in P if there exists a polynomial-time
    deterministic Turing machine that decides it -/
def InP (L : DecisionProblem) : Prop :=
  ∃ (M : TuringMachine) (time : Nat → Nat),
    IsPolynomial time ∧
    TMTimeBounded M time ∧
    ∀ (x : BinaryString), L x ↔ Accepts M x

/- ## 5. Complexity Class NP -/

/-- Certificate (witness) for NP problems -/
def Certificate : Type := BinaryString

/-- Polynomial-size certificate -/
def PolyCertificateSize (certSize : Nat → Nat) : Prop :=
  IsPolynomial certSize

/-- Polynomial-time verifier -/
def PolynomialTimeVerifier (V : BinaryString → Certificate → Bool) : Prop :=
  ∃ (time : Nat → Nat),
    IsPolynomial time ∧
    ∀ (x : BinaryString) (c : Certificate), True  -- Abstract time bound

/-- A decision problem L is in NP if there exists a polynomial-time verifier -/
def InNP (L : DecisionProblem) : Prop :=
  ∃ (V : BinaryString → Certificate → Bool) (certSize : Nat → Nat),
    PolyCertificateSize certSize ∧
    PolynomialTimeVerifier V ∧
    ∀ (x : BinaryString),
      L x ↔ ∃ (c : Certificate), inputSize c ≤ certSize (inputSize x) ∧ V x c = true

/- ## 6. The P vs NP Question -/

/-- P is a subset of NP (axiom - proof requires careful construction) -/
axiom P_subseteq_NP : ∀ L, InP L → InNP L

/-- The central question: P = NP? -/
def PEqualsNP : Prop :=
  ∀ L, InNP L → InP L

/-- The alternative: P ≠ NP -/
def PNeqNP : Prop :=
  ∃ L, InNP L ∧ ¬InP L

/-- These are mutually exclusive (classical logic) -/
axiom P_eq_or_neq_NP : PEqualsNP ∨ PNeqNP

/- ## 7. Formal Tests and Checks -/

/-- Test 1: Verify a problem is in P -/
def testInP (L : DecisionProblem) (M : TuringMachine)
            (time : Nat → Nat) (_polyProof : IsPolynomial time) : Prop :=
  TMTimeBounded M time ∧
  ∀ x, L x ↔ Accepts M x

/-- A one-step example checks that the transition reads the input tape. -/
private def firstBitMachine : TuringMachine :=
  { states := 3, alphabet := 2
    transition := fun _ symbol => (if symbol = 1 then 1 else 2, symbol, true)
    initialState := 0, acceptState := 1, rejectState := 2 }

example : (run firstBitMachine [true] 1).state = firstBitMachine.acceptState := by rfl
example : (run firstBitMachine [false] 1).state = firstBitMachine.rejectState := by rfl

/-- Test 2: Verify a problem is in NP -/
def testInNP (L : DecisionProblem)
             (V : BinaryString → Certificate → Bool)
             (certSize : Nat → Nat)
             (_polyCertProof : PolyCertificateSize certSize)
             (_polyVerifierProof : PolynomialTimeVerifier V) : Prop :=
  ∀ x, L x ↔ ∃ c, inputSize c ≤ certSize (inputSize x) ∧ V x c = true

/- A syntax for polynomial bounds, closed under addition, multiplication, and
   substitution. This avoids an unproved closure assumption at composition. -/
inductive PolyBound where
  | constant (c : Nat)
  | input
  | add (p q : PolyBound)
  | mul (p q : PolyBound)
  | compose (p q : PolyBound)

def PolyBound.eval : PolyBound → Nat → Nat
  | .constant c, _ => c
  | .input, n => n
  | .add p q, n => p.eval n + q.eval n
  | .mul p q, n => p.eval n * q.eval n
  | .compose p q, n => p.eval (q.eval n)

theorem PolyBound.eval_mono (p : PolyBound) {n m : Nat} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  induction p generalizing n m with
  | constant _ => exact Nat.le_refl _
  | input => exact h
  | add p q ihp ihq => exact Nat.add_le_add (ihp h) (ihq h)
  | mul p q ihp ihq => exact Nat.mul_le_mul (ihp h) (ihq h)
  | compose p q ihp ihq => exact ihp (ihq h)

/- The output is the contiguous binary prefix of the final tape, beginning at
   its left edge. A blank or separator ends the word. -/
def readOutput : List Complexity.Symbol → BinaryString
  | .zero :: rest => false :: readOutput rest
  | .one :: rest => true :: readOutput rest
  | _ => []

def output (c : Complexity.Config) : BinaryString :=
  readOutput (c.left.reverse ++ c.head :: c.right)

private theorem readOutput_map (x : BinaryString) :
    readOutput (x.map Complexity.Symbol.ofBool) = x := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false =>
      change false :: readOutput (xs.map Complexity.Symbol.ofBool) = false :: xs
      exact congrArg (List.cons false) ih
    | true =>
      change true :: readOutput (xs.map Complexity.Symbol.ofBool) = true :: xs
      exact congrArg (List.cons true) ih

theorem output_initial (x : BinaryString) : output (Complexity.initial x) = x := by
  cases x with
  | nil => rfl
  | cons b xs =>
    cases b with
    | false =>
      change false :: readOutput (xs.map Complexity.Symbol.ofBool) = false :: xs
      exact congrArg (List.cons false) (readOutput_map xs)
    | true =>
      change true :: readOutput (xs.map Complexity.Symbol.ofBool) = true :: xs
      exact congrArg (List.cons true) (readOutput_map xs)

/-- A finite instruction-table machine halts with a final tape. Each step
    charges one instruction, including the halt instruction. -/
inductive OutputRun (m : Complexity.Machine) :
    Complexity.Config → Nat → Complexity.Config → Prop where
  | halt {c b} : Complexity.step m c = .inl b → OutputRun m c 1 c
  | next {c c' out t} : Complexity.step m c = .inr c' →
      OutputRun m c' t out → OutputRun m c (t + 1) out

/-- A reduction program is a finite transducer, a linear-time bitwise NOT,
    or a sequence of two reduction programs. -/
inductive Transducer where
  | machine (m : Complexity.Machine)
  | bitNot
  | compose (first second : Transducer)

/-- A structural scan charges one step per bit and one final step. -/
inductive BitNotRun : BinaryString → Nat → BinaryString → Prop where
  | nil : BitNotRun [] 1 []
  | cons {b xs ys t} : BitNotRun xs t ys → BitNotRun (b :: xs) (t + 1) ((!b) :: ys)

theorem bitNot_runs (x : BinaryString) :
    BitNotRun x (x.length + 1) (x.map Bool.not) := by
  induction x with
  | nil => exact .nil
  | cons _ xs ih => exact .cons ih

/-- Operational semantics: composition runs the second program on the first
    program's output, and charges the sum of their step counts. -/
inductive TransducerRun : Transducer → BinaryString → Nat → BinaryString → Prop where
  | machine {m x t c} : OutputRun m (Complexity.initial x) t c →
      TransducerRun (.machine m) x t (output c)
  | bitNot {x t y} : BitNotRun x t y → TransducerRun .bitNot x t y
  | compose {first second x middle y t₁ t₂} :
      TransducerRun first x t₁ middle → TransducerRun second middle t₂ y →
      TransducerRun (.compose first second) x (t₁ + t₂) y

/-- A function has a concrete program and polynomial bounds for its runtime
    and output length. The program's run must return exactly `f x`. -/
def PolyTimeComputable (f : BinaryString → BinaryString) : Prop :=
  ∃ (program : Transducer) (time size : PolyBound), ∀ x,
    ∃ t y, TransducerRun program x t y ∧
      t ≤ time.eval x.length ∧ y = f x ∧ y.length ≤ size.eval x.length

private def stopMachine : Complexity.Machine := ⟨[]⟩

theorem computable_identity : PolyTimeComputable id := by
  refine ⟨.machine stopMachine, .constant 1, .input, ?_⟩
  intro x
  refine ⟨1, x, ?_, Nat.le_refl _, rfl, Nat.le_refl _⟩
  have hr : OutputRun stopMachine (Complexity.initial x) 1
      (Complexity.initial x) := .halt rfl
  simpa [output_initial] using (TransducerRun.machine hr)

theorem computable_bitNot : PolyTimeComputable (fun x => x.map Bool.not) := by
  refine ⟨.bitNot, .add .input (.constant 1), .input, ?_⟩
  intro x
  refine ⟨x.length + 1, x.map Bool.not, .bitNot (bitNot_runs x),
    Nat.le_refl _, rfl, ?_⟩
  induction x with
  | nil => exact Nat.le_refl _
  | cons _ xs ih => exact Nat.succ_le_succ ih

theorem computable_comp {f g : BinaryString → BinaryString}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) := by
  obtain ⟨first, time₁, size₁, hfirst⟩ := hf
  obtain ⟨second, time₂, size₂, hsecond⟩ := hg
  refine ⟨.compose first second, .add time₁ (.compose time₂ size₁),
    .compose size₂ size₁, ?_⟩
  intro x
  obtain ⟨t₁, middle, hr₁, ht₁, hm, hs₁⟩ := hfirst x
  obtain ⟨t₂, y, hr₂, ht₂, hy, hs₂⟩ := hsecond middle
  refine ⟨t₁ + t₂, y, .compose hr₁ hr₂, ?_, ?_, ?_⟩
  · exact Nat.add_le_add ht₁ (Nat.le_trans ht₂ (time₂.eval_mono hs₁))
  · simpa [Function.comp, hm] using hy
  · exact Nat.le_trans hs₂ (size₂.eval_mono hs₁)

/-- A polynomial-time many-one reduction computes `f` and preserves
    membership after applying it. -/
def PolyTimeReduction (L1 L2 : DecisionProblem) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ x, L1 x ↔ L2 (f x)

theorem reduction_refl (L : DecisionProblem) : PolyTimeReduction L L := by
  exact ⟨id, computable_identity, by intro x; rfl⟩

theorem reduction_trans {L1 L2 L3 : DecisionProblem}
    (h₁ : PolyTimeReduction L1 L2) (h₂ : PolyTimeReduction L2 L3) :
    PolyTimeReduction L1 L3 := by
  obtain ⟨f, hf, hcorrect₁⟩ := h₁
  obtain ⟨g, hg, hcorrect₂⟩ := h₂
  refine ⟨g ∘ f, computable_comp hf hg, ?_⟩
  intro x
  exact (hcorrect₁ x).trans (hcorrect₂ (f x))

/-- The distinct singleton languages are reduced by a one-pass bitwise NOT. -/
theorem singleton_bitNot_reduction :
    PolyTimeReduction (fun x => x = [true]) (fun x => x = [false]) := by
  refine ⟨fun x => x.map Bool.not, computable_bitNot, ?_⟩
  intro x
  cases x with
  | nil => constructor <;> intro h <;> cases h
  | cons b tail =>
    cases b with
    | false =>
      cases tail with
      | nil => constructor <;> intro h <;> cases h
      | cons _ _ => constructor <;> intro h <;> cases h
    | true =>
      cases tail with
      | nil => constructor <;> intro _ <;> rfl
      | cons _ _ => constructor <;> intro h <;> cases h

/-- Test 4: a completeness candidate in the toy P/NP framework. Its NP
    verifier still lacks a machine runtime proof, so this is not standard
    NP-completeness. -/
def IsNPComplete (L : DecisionProblem) : Prop :=
  InNP L ∧
  ∀ L', InNP L' → PolyTimeReduction L' L

/- The NP-completeness implication remains unasserted: InNP still uses an
   unconstrained Boolean verifier, separate from these reduction programs. -/

/- ## 8. Example Problems -/

/-- Boolean formula -/
inductive BoolFormula where
  | var : Nat → BoolFormula
  | not : BoolFormula → BoolFormula
  | and : BoolFormula → BoolFormula → BoolFormula
  | or : BoolFormula → BoolFormula → BoolFormula

/-- Assignment of boolean values to variables -/
def Assignment : Type := Nat → Bool

/-- Evaluate a formula under an assignment -/
def evalFormula (a : Assignment) : BoolFormula → Bool
  | BoolFormula.var n => a n
  | BoolFormula.not f => !(evalFormula a f)
  | BoolFormula.and f1 f2 => evalFormula a f1 && evalFormula a f2
  | BoolFormula.or f1 f2 => evalFormula a f1 || evalFormula a f2

/-- SAT: Does there exist a satisfying assignment? -/
def SAT (f : BoolFormula) : Prop :=
  ∃ (a : Assignment), evalFormula a f = true

/-- TAUT: Is the formula true under all assignments? -/
def TAUT (f : BoolFormula) : Prop :=
  ∀ (a : Assignment), evalFormula a f = true

/- ## 9. Basic Properties (axiomatized) -/

/-- Empty language is in P -/
def emptyLanguage : DecisionProblem := fun _ => False

/-- A machine starting in its reject state decides the empty language. -/
def rejectMachine : TuringMachine :=
  { states := 2, alphabet := 2, transition := fun _ _ => (0, 0, true)
    initialState := 0, acceptState := 1, rejectState := 0 }

theorem empty_in_P : InP emptyLanguage := by
  refine ⟨rejectMachine, fun _ => 0, constant_is_poly 0, ?_, ?_⟩
  · intro input
    exact ⟨0, Nat.le_refl 0, Or.inr rfl⟩
  · intro input
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨steps, h⟩
      have hReject (n : Nat) : (run rejectMachine input n).state = rejectMachine.rejectState := by
        induction n with
        | zero => rfl
        | succ n ih => simp [run, step, ih]
      have hDistinct : rejectMachine.rejectState ≠ rejectMachine.acceptState := by decide
      exact False.elim (hDistinct ((hReject steps).symm.trans h))

/-- Universal language is in P -/
def universalLanguage : DecisionProblem := fun _ => True

/-- A machine starting in its accept state decides the universal language. -/
def acceptMachine : TuringMachine :=
  { states := 2, alphabet := 2, transition := fun _ _ => (0, 0, true)
    initialState := 1, acceptState := 1, rejectState := 0 }

theorem universal_in_P : InP universalLanguage := by
  refine ⟨acceptMachine, fun _ => 0, constant_is_poly 0, ?_, ?_⟩
  · intro input
    exact ⟨0, Nat.le_refl 0, Or.inl rfl⟩
  · intro input
    constructor
    · intro _
      exact ⟨0, rfl⟩
    · intro _
      exact True.intro

/-- P is closed under complement -/
axiom P_closed_under_complement : ∀ L,
    InP L → InP (fun x => ¬L x)

/-- If P = NP, then NP is closed under complement -/
axiom P_eq_NP_implies_NP_closed_complement :
    PEqualsNP → ∀ L, InNP L → InNP (fun x => ¬L x)

/- ## 10. Verification Summary -/

#check InP
#check InNP
#check PEqualsNP
#check PNeqNP
#check P_subseteq_NP
#check IsNPComplete
#check testInP
#check testInNP
#check PolyTimeReduction

#print axioms empty_in_P
#print axioms universal_in_P
#print axioms computable_identity
#print axioms computable_bitNot
#print axioms reduction_trans
#print axioms singleton_bitNot_reduction
#print axioms P_subseteq_NP
#print axioms P_eq_or_neq_NP
#print axioms P_closed_under_complement
#print axioms P_eq_NP_implies_NP_closed_complement

#print "✓ P vs NP formal specification compiled successfully"

end PEqNP
