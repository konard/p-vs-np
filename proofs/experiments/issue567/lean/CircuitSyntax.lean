import proofs.experiments.issue532.lean.Idea41

/-!
The regular grammar of `encCircuit`, checked by a six-state finite machine.
Every paired input halts in exactly `|x| + 1` instructions, including malformed
words. The certificate is left untouched. This is an input-validation slice,
not the circuit evaluator: wire bounds, certificate length and NAND evaluation
are deliberately absent from the recognized language.
-/

namespace Issue567.CircuitSyntax

open Complexity Issue532.Machines Issue532.Circuits Issue532.Idea41

inductive Phase where
  | header | marker | firstWire | secondWire | done | bad
  deriving DecidableEq, Repr

def next : Phase → Bool → Phase
  | .header, true => .header
  | .header, false => .marker
  | .marker, true => .firstWire
  | .marker, false => .done
  | .firstWire, true => .firstWire
  | .firstWire, false => .secondWire
  | .secondWire, true => .secondWire
  | .secondWire, false => .marker
  | .done, _ => .bad
  | .bad, _ => .bad

def syntaxFrom : Phase → Word → Bool
  | q, [] => q == .done
  | q, b :: w => syntaxFrom (next q b) w

def circuitSyntax (w : Word) : Bool := syntaxFrom .header w

/-- The suffix still needed to finish an encoding in each parser phase. -/
def Suffix : Phase → Word → Prop
  | .header, w => ∃ n C, w = encCircuit n C
  | .marker, w => ∃ C, w = encList encGate C
  | .firstWire, w => ∃ i j C, w = encNat i ++ encNat j ++ encList encGate C
  | .secondWire, w => ∃ j C, w = encNat j ++ encList encGate C
  | .done, w => w = []
  | .bad, _ => False

theorem syntaxFrom_sound (q : Phase) (w : Word) :
    syntaxFrom q w = true → Suffix q w := by
  induction w generalizing q with
  | nil =>
      cases q <;> simp [syntaxFrom, Suffix]
  | cons b w ih =>
      intro h
      have hs := ih (next q b) h
      cases q <;> cases b <;> simp only [next, Suffix] at hs ⊢
      · obtain ⟨C, rfl⟩ := hs
        exact ⟨0, C, rfl⟩
      · obtain ⟨n, C, rfl⟩ := hs
        exact ⟨n + 1, C, rfl⟩
      · subst w
        exact ⟨[], rfl⟩
      · obtain ⟨i, j, C, rfl⟩ := hs
        exact ⟨(i, j) :: C, rfl⟩
      · obtain ⟨j, C, rfl⟩ := hs
        exact ⟨0, j, C, rfl⟩
      · obtain ⟨i, j, C, rfl⟩ := hs
        exact ⟨i + 1, j, C, rfl⟩
      · obtain ⟨C, rfl⟩ := hs
        exact ⟨0, C, rfl⟩
      · obtain ⟨j, C, rfl⟩ := hs
        exact ⟨j + 1, C, rfl⟩
      all_goals contradiction

theorem syntaxFrom_nat (q : Phase) (hq : next q true = q) (n : Nat) (r : Word) :
    syntaxFrom q (encNat n ++ r) = syntaxFrom (next q false) r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [encNat, syntaxFrom, hq] using ih

theorem syntaxFrom_list (C : Circuit) :
    syntaxFrom .marker (encList encGate C) = true := by
  induction C with
  | nil => rfl
  | cons g C ih =>
      obtain ⟨i, j⟩ := g
      simp only [encList, encGate, syntaxFrom, next, List.append_assoc]
      rw [syntaxFrom_nat .firstWire rfl]
      simp only [next]
      rw [syntaxFrom_nat .secondWire rfl]
      exact ih

theorem circuitSyntax_encCircuit (n : Nat) (C : Circuit) :
    circuitSyntax (encCircuit n C) = true := by
  unfold circuitSyntax encCircuit
  rw [syntaxFrom_nat .header rfl]
  exact syntaxFrom_list C

theorem circuitSyntax_iff (w : Word) :
    circuitSyntax w = true ↔ ∃ n C, w = encCircuit n C := by
  constructor
  · exact syntaxFrom_sound .header w
  · rintro ⟨n, C, rfl⟩
    exact circuitSyntax_encCircuit n C

theorem circuitSyntax_iff_decCircuit (w : Word) :
    circuitSyntax w = true ↔ ∃ n C, decCircuit w = some (n, C) := by
  rw [circuitSyntax_iff]
  constructor
  · rintro ⟨n, C, rfl⟩
    exact ⟨n, C, decCircuit_encCircuit n C⟩
  · rintro ⟨n, C, hd⟩
    exact ⟨n, C, decCircuit_sound hd⟩

def idx : Phase → Nat
  | .header => 0
  | .marker => 1
  | .firstWire => 2
  | .secondWire => 3
  | .done => 4
  | .bad => 5

def phases : List Phase := [.header, .marker, .firstWire, .secondWire, .done, .bad]

def delta (q : Phase) : Symbol → Instruction
  | .zero => .move (idx (next q false)) .zero .right
  | .one => .move (idx (next q true)) .one .right
  | .separator => .halt (q == .done)
  | .blank => .halt false

def row (q : Phase) : List Instruction :=
  [delta q .blank, delta q .zero, delta q .one, delta q .separator]

def circuitSyntaxMachine : Machine := ⟨phases.map row⟩

theorem instruction (q : Phase) (a : Symbol) :
    circuitSyntaxMachine.instruction (idx q) a = delta q a := by
  have hq : phases[idx q]? = some q := by cases q <;> rfl
  unfold Machine.instruction circuitSyntaxMachine
  simp only [List.getElem?_map, hq, Option.map_some, Option.bind_some]
  cases a <;> rfl

def cfg (q : Phase) (L : List Symbol) : List Symbol → Config
  | [] => ⟨idx q, L, .blank, []⟩
  | a :: R => ⟨idx q, L, a, R⟩

theorem scan_run (q : Phase) (w : Word) (L R : List Symbol) :
    Run circuitSyntaxMachine (cfg q L (w.map Symbol.ofBool ++ .separator :: R))
      (w.length + 1) (syntaxFrom q w) := by
  induction w generalizing q L with
  | nil =>
      apply Run.halt
      simp [step, cfg, instruction, delta, syntaxFrom]
  | cons b w ih =>
      have hs : step circuitSyntaxMachine
          (cfg q L ((b :: w).map Symbol.ofBool ++ .separator :: R)) =
          .inr (cfg (next q b) (Symbol.ofBool b :: L)
            (w.map Symbol.ofBool ++ .separator :: R)) := by
        cases b <;> simp [step, cfg, instruction, delta, Symbol.ofBool, moveHead] <;> rfl
      exact Run.next hs (ih (next q b) (Symbol.ofBool b :: L))

/-- Includes the halting instruction; certificates of any length are allowed. -/
theorem circuitSyntaxMachine_run (x cert : Word) :
    Run circuitSyntaxMachine (pairedInput x cert) (x.length + 1) (circuitSyntax x) := by
  have he : pairedInput x cert =
      cfg .header [] (x.map Symbol.ofBool ++ .separator :: cert.map Symbol.ofBool) := by
    unfold pairedInput
    simp only [List.append_assoc, List.singleton_append]
    cases x <;> rfl
  rw [he]
  exact scan_run .header x [] (cert.map Symbol.ofBool)

def syntaxTimeBound : Polynomial := ⟨1, 1⟩

theorem circuitSyntaxMachine_terminates (x cert : Word) :
    ∃ t b, t ≤ (VerifierProgram.paired circuitSyntaxMachine).timeLimit syntaxTimeBound x cert ∧
      Run circuitSyntaxMachine (pairedInput x cert) t b := by
  refine ⟨x.length + 1, circuitSyntax x, ?_, circuitSyntaxMachine_run x cert⟩
  simp [VerifierProgram.timeLimit, syntaxTimeBound, Polynomial.eval]
  omega

/-- Correctness quantifies over every actual run, not just the exhibited one. -/
theorem circuitSyntaxMachine_correct (x cert : Word) (t : Nat) (b : Bool)
    (hr : Run circuitSyntaxMachine (pairedInput x cert) t b) :
    t = x.length + 1 ∧ b = circuitSyntax x :=
  run_deterministic hr (circuitSyntaxMachine_run x cert)

theorem circuitSyntaxMachine_accepts_iff (x cert : Word) :
    (∃ t, Run circuitSyntaxMachine (pairedInput x cert) t true) ↔
      ∃ n C, x = encCircuit n C := by
  rw [← circuitSyntax_iff]
  constructor
  · rintro ⟨t, hr⟩
    exact (circuitSyntaxMachine_correct x cert t true hr).2.symm
  · intro hx
    exact ⟨x.length + 1, hx ▸ circuitSyntaxMachine_run x cert⟩

end Issue567.CircuitSyntax
