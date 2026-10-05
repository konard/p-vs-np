import proofs.experiments.issue624.lean.CertificateCNF
import proofs.experiments.issue568.lean.Tableau

/-!
Connect the certificate CNF to the existing local trace semantics. Both
verifier constructors are covered, and the acceptance clock uses the decoded
certificate's actual length. `VerifierTableau` is still a semantic predicate:
its transition and accepting constraints have not yet been compiled to CNF.
-/

namespace Issue624.VerifierTableau

open Complexity Issue532.Machines Issue568.Tableau Issue624.CertificateCNF

def verifierMachine : VerifierProgram → Machine
  | .ignoreCertificate m => m
  | .paired m => m

def verifierInitial : VerifierProgram → Word → Word → Config
  | .ignoreCertificate _, x, _ => initial x
  | .paired _, x, cert => pairedInput x cert

theorem verifierRun_iff (v : VerifierProgram) (x cert : Word) (t : Nat) (b : Bool) :
    v.Run x cert t b ↔ Run (verifierMachine v) (verifierInitial v x cert) t b := by
  cases v <;> rfl

/-- The certificate constraints are CNF; the trace constraints reuse #568.
No second trace semantics, padded certificate, or enlarged clock is used. -/
def VerifierTableau (np : ClassNP) (x : Word) (a : Assignment) (trace : List Config) : Prop :=
  let cert := decodeCertificate a 0 (np.certBound.eval x.length)
  evalCNF a (certificateCNF 0 (np.certBound.eval x.length)) = true ∧
  trace.head? = some (verifierInitial np.verifier x cert) ∧
  trace.length ≤ np.verifier.timeLimit np.timeBound x cert ∧
  LocalTrace (verifierMachine np.verifier) true trace

/-- All NP witnesses, including both verifier constructors and all bounded
certificate lengths, are covered by this semantic interface. -/
theorem verifierTableau_iff_language (np : ClassNP) (x : Word) :
    (∃ a trace, VerifierTableau np x a trace) ↔ np.language x = true := by
  constructor
  · rintro ⟨a, trace, _, hhead, hclock, hlocal⟩
    apply (np.correct x).mpr
    exact ⟨decodeCertificate a 0 (np.certBound.eval x.length), trace.length,
      decodeCertificate_length _ _ _, hclock,
      (verifierRun_iff _ _ _ _ _).mpr
        ((localTrace_iff_run _ _ _ true).mp ⟨trace, hhead, rfl, hlocal⟩)⟩
  · intro hx
    obtain ⟨cert, t, hcert, htime, hr⟩ := (np.correct x).mp hx
    obtain ⟨trace, hhead, hlen, hlocal⟩ :=
      (localTrace_iff_run _ _ t true).mpr ((verifierRun_iff _ _ _ _ _).mp hr)
    refine ⟨encodeCertificate cert, trace, ?_⟩
    unfold VerifierTableau
    rw [decode_encodeCertificate cert _ hcert]
    exact ⟨encodeCertificate_models cert _ hcert, hhead, hlen ▸ htime, hlocal⟩

private theorem polynomial_mono (p : Polynomial) {n k : Nat} (h : n ≤ k) :
    p.eval n ≤ p.eval k := by
  exact Nat.mul_le_mul_left p.coefficient
    (Nat.pow_le_pow_left (by omega) p.degree)

/-- A uniform envelope only for sizing the later tableau. Acceptance still
uses the smaller, exact clock in `VerifierTableau`. -/
def maxClock (np : ClassNP) (n : Nat) : Nat :=
  np.timeBound.eval (n + np.certBound.eval n + 1)

def clockPolynomial (np : ClassNP) : Polynomial :=
  ⟨np.timeBound.coefficient * (np.certBound.coefficient + 2) ^ np.timeBound.degree,
    (np.certBound.degree + 1) * np.timeBound.degree⟩

theorem verifierTimeLimit_le (np : ClassNP) (x cert : Word)
    (h : cert.length ≤ np.certBound.eval x.length) :
    np.verifier.timeLimit np.timeBound x cert ≤ maxClock np x.length := by
  cases np.verifier <;> apply polynomial_mono np.timeBound <;> omega

theorem maxClock_polynomial (np : ClassNP) (n : Nat) :
    maxClock np n ≤ (clockPolynomial np).eval n := by
  have hpow : 1 ≤ (n + 1) ^ np.certBound.degree := Nat.one_le_pow _ _ (by omega)
  have hgrowth : n + 1 ≤ (n + 1) ^ (np.certBound.degree + 1) := by
    rw [Nat.pow_succ]
    simpa using Nat.mul_le_mul_right (n + 1) hpow
  have hold : (n + 1) ^ np.certBound.degree ≤
      (n + 1) ^ (np.certBound.degree + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbase : n + np.certBound.eval n + 1 + 1 ≤
      (np.certBound.coefficient + 2) * (n + 1) ^ (np.certBound.degree + 1) := by
    have hc := Nat.mul_le_mul_left np.certBound.coefficient hold
    simp only [Polynomial.eval, Nat.add_mul] at *
    omega
  calc
    maxClock np n ≤ np.timeBound.coefficient *
        ((np.certBound.coefficient + 2) * (n + 1) ^ (np.certBound.degree + 1)) ^
          np.timeBound.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (clockPolynomial np).eval n := by
      simp [clockPolynomial, Polynomial.eval, Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

theorem verifierInitial_span (v : VerifierProgram) (x cert : Word) :
    span (verifierInitial v x cert) ≤ x.length + cert.length + 2 := by
  cases v with
  | ignoreCertificate m =>
    have h := initial_span_le x
    change span (initial x) ≤ _
    omega
  | paired m =>
    cases x <;> simp [verifierInitial, pairedInput, initialSymbols, span] <;> omega

/-- A uniform tape-cell envelope for a model of the semantic interface. -/
theorem verifierTableau_span (np : ClassNP) (x : Word) (a : Assignment) (trace : List Config)
    (h : VerifierTableau np x a trace) (d : Config) (hd : d ∈ trace) :
    span d ≤ x.length + np.certBound.eval x.length + maxClock np x.length + 2 := by
  obtain ⟨_, hhead, htime, hlocal⟩ := h
  have hcert := decodeCertificate_length a 0 (np.certBound.eval x.length)
  have hspan := trace_span_bound _ true trace _ d hhead hlocal hd
  have hinit := verifierInitial_span np.verifier x
    (decodeCertificate a 0 (np.certBound.eval x.length))
  have hclock := verifierTimeLimit_le np x _ hcert
  omega

theorem overlong_not_representable (a : Assignment) (cert : Word) (bound : Nat)
    (h : bound < cert.length) : ¬ Represents a 0 cert bound := by
  intro hr
  have := represents_length hr
  omega

theorem rejecting_verifier_no_tableau (np : ClassNP) (x : Word)
    (h : np.language x = false) : ¬ ∃ a trace, VerifierTableau np x a trace := by
  rw [verifierTableau_iff_language, h]
  decide

/-- Reuse #568's counterexample: accepting at the last configuration does
not excuse an invalid predecessor edge. -/
theorem wrong_successor_not_model (np : ClassNP) (x : Word) (a : Assignment)
    (hm : verifierMachine np.verifier = moveThenAccept) :
    ¬ VerifierTableau np x a [initial [], wrongSuccessor] := by
  intro h
  have hl := h.2.2.2
  rw [hm] at hl
  exact wrong_successor_rejected hl

end Issue624.VerifierTableau
