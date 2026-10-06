import proofs.experiments.issue624.lean.CookLevin

set_option maxRecDepth 4096

open Complexity Issue532.Machines Issue624.CookLevin
open Issue624.InitialCNF Issue624.SuccessorCNF Issue624.CertificateCNF

-- These contracts fail to compile before initial wiring is implemented.
example (np : ClassNP) (x : Word) :
    Satisfiable (tableauCNF np x) ↔ np.language x = true := tableauCNF_iff np x
example (np : ClassNP) (x : Word) (h : ∀ w, np.language w = false) :
    ¬Satisfiable (tableauCNF np x) := tableauCNF_rejecting_unsatisfiable np x h
example (np : ClassNP) (x cert : Word) (a : Assignment)
    (h : np.certBound.eval x.length < cert.length)
    (ha : ∀ v, v ≤ 2 * np.certBound.eval x.length →
      a v = Issue624.CertificateCNF.encodeCertificate cert v) :
    evalCNF a (tableauCNF np x) = false := tableauCNF_overlong_rejected np x cert a h ha
example (np : ClassNP) (x : Word) (a : Assignment) (c d : Config) (rest : List Config)
    (h : step (Issue624.VerifierTableau.verifierMachine np.verifier) c ≠ .inr d)
    (hd : decodeTrace np x a = c :: d :: rest) :
    evalCNF a (tableauCNF np x) = false := tableauCNF_wrong_successor_rejected np x a c d rest h hd
example (np : ClassNP) (x : Word) :
    (encodeCNF (tableauCNF np x)).length ≤ (sizePolynomial np).eval x.length :=
  tableauCNF_encoded_size np x

-- A verifier rejects from its prescribed state zero but accepts in state one.
-- The old accepting-prefix fragment accepts that unrelated initial state.
private def startSensitive (answer : Bool) : Machine :=
  ⟨[[.halt answer, .halt answer, .halt answer, .halt answer],
    [.halt true, .halt true, .halt true, .halt true]]⟩
private def startVerifier (paired answer : Bool) : VerifierProgram :=
  if paired then .paired (startSensitive answer) else .ignoreCertificate (startSensitive answer)
private theorem startRun (paired answer : Bool) (x cert : Word) :
    (startVerifier paired answer).Run x cert 1 answer := by
  cases paired <;> change Run (startSensitive answer) _ 1 answer <;> apply Run.halt
  all_goals cases x with
  | nil => rfl
  | cons b rest => cases b <;> rfl
private theorem startTime (paired answer : Bool) (x cert : Word) :
    (startVerifier paired answer).timeLimit ⟨1, 0⟩ x cert = 1 := by cases paired <;> rfl
private def startNP (paired answer : Bool) (bound : Nat) : ClassNP where
  language := fun _ => answer
  verifier := startVerifier paired answer
  certBound := ⟨bound, 0⟩
  timeBound := ⟨1, 0⟩
  terminates := fun x cert _ => ⟨1, answer, by rw [startTime]; exact Nat.le_refl 1, startRun paired answer x cert⟩
  correct := by
    intro x
    constructor
    · intro h
      exact ⟨[], 1, by simp, by rw [startTime]; exact Nat.le_refl 1, h ▸ startRun paired answer x []⟩
    · rintro ⟨cert, t, _, _, hr⟩
      have he := (run_deterministic ((Issue624.VerifierTableau.verifierRun_iff _ _ _ _ _).mp hr)
        ((Issue624.VerifierTableau.verifierRun_iff _ _ _ _ _).mp (startRun paired answer x cert))).2
      exact he.symm

private def wrongState : Config := ⟨1, [.blank], .one,
  [.separator, .zero, .blank, .blank, .blank, .blank]⟩
private def candidate (c : Config) : Assignment :=
  jointAssignment (startNP true false 2) [true] (encodeCertificate [false]) [c]

-- All three fragments are examined on the same assignment, not an empty row.
example : evalCNF (candidate wrongState) (certificateCNF 0 2) = true := by decide
example : evalCNF (candidate wrongState)
    (Issue624.RunCNF.runCNF (startSensitive false) 5 8 1) = true := by decide
example : evalCNF (candidate wrongState) (tableauCNF (startNP true false 2) [true]) = false := by decide
example (paired : Bool) (x : Word) : ¬Satisfiable (tableauCNF (startNP paired false 2) x) :=
  tableauCNF_rejecting_unsatisfiable _ _ (fun _ => rfl)

-- One-hot rows with the wrong head or certificate bit fail initial wiring.
private def wrongHead : Config := ⟨0, [.one, .blank], .separator,
  [.zero, .blank, .blank, .blank, .blank]⟩
private def wrongTape : Config := ⟨0, [.blank], .one,
  [.separator, .one, .blank, .blank, .blank, .blank]⟩
example : evalCNF (candidate wrongHead) (rowCNF 5 2 8) = true := by decide
example : evalCNF (candidate wrongTape) (rowCNF 5 2 8) = true := by decide
example : evalCNF (candidate wrongHead)
    (initialCNF 5 2 1 (sources (startNP true false 2) [true])) = false := by decide
example : evalCNF (candidate wrongTape)
    (initialCNF 5 2 1 (sources (startNP true false 2) [true])) = false := by decide

-- Empty/short/full certificates distinguish blank, zero, and one cells.
example : (windowSources (.paired (startSensitive true)) [] 2 1 6).map
    (Source.eval (encodeCertificate [])) = [.blank, .separator, .blank, .blank, .blank, .blank] := by decide
example : (windowSources (.paired (startSensitive true)) [] 2 1 6).map
    (Source.eval (encodeCertificate [false])) = [.blank, .separator, .zero, .blank, .blank, .blank] := by decide
example : (windowSources (.paired (startSensitive true)) [] 2 1 6).map
    (Source.eval (encodeCertificate [true, false])) = [.blank, .separator, .one, .zero, .blank, .blank] := by decide
example : (windowSources (.ignoreCertificate (startSensitive true)) [] 2 1 6).map
    (Source.eval (encodeCertificate [true, false])) = List.replicate 6 .blank := by decide

private def acceptingModel (paired : Bool) (x cert : Word) (bound : Nat) : Assignment :=
  let np := startNP paired true bound
  let a := encodeCertificate cert
  jointAssignment np x a [initialRow np x a]
example : evalCNF (acceptingModel true [] [] 0) (tableauCNF (startNP true true 0) []) = true := by decide
example : evalCNF (acceptingModel true [] [] 2) (tableauCNF (startNP true true 2) []) = true := by decide
example : evalCNF (acceptingModel true [] [false] 2) (tableauCNF (startNP true true 2) []) = true := by decide
example : evalCNF (acceptingModel true [] [true, false] 2) (tableauCNF (startNP true true 2) []) = true := by decide
example : evalCNF (acceptingModel false [true] [true, false] 2)
    (tableauCNF (startNP false true 2) [true]) = true := by decide
example : decodeCertificate (acceptingModel true [] [false] 2) 0 2 = [false] := by decide
example : decodeTrace (startNP true true 2) [] (acceptingModel true [] [false] 2) =
    [initialRow (startNP true true 2) [] (encodeCertificate [false])] := by rfl

#print axioms tableauCNF_sound
#print axioms tableauCNF_complete
#print axioms tableauCNF_iff
#print axioms tableauCNF_encoded_size
#print axioms tableauCNF_rejecting_unsatisfiable
#print axioms tableauCNF_overlong_rejected
#print axioms tableauCNF_wrong_successor_rejected
