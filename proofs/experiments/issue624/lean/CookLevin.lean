import proofs.experiments.issue624.lean.InitialCNF

/-! Full bounded-verifier tableau and its model correspondence. The reduction
machine and hardness assembly require separate charged machine proofs. -/
namespace Issue624.CookLevin
open Complexity Issue532.Machines Issue568.Tableau Issue624.LocalCNF
open Issue624.CertificateCNF Issue624.VerifierTableau Issue624.FixedWindow
open Issue624.SuccessorCNF Issue624.InitialCNF

def rowBase (np : ClassNP) (x : Word) : Nat := 2 * np.certBound.eval x.length + 1
def sources (np : ClassNP) (x : Word) : List Source :=
  windowSources np.verifier x (np.certBound.eval x.length)
    (maxClock np x.length) (windowWidth np x.length)
def initialRow (np : ClassNP) (x : Word) (a : Assignment) : Config :=
  fitWindow (verifierInitial np.verifier x (decodeCertificate a 0 (np.certBound.eval x.length)))
    (maxClock np x.length) (windowWidth np x.length)
def tableauCNF (np : ClassNP) (x : Word) : CNF :=
  certificateCNF 0 (np.certBound.eval x.length) ++
    initialCNF (rowBase np x) (verifierMachine np.verifier).program.length
      (maxClock np x.length) (sources np x) ++
    Issue624.RunCNF.runCNF (verifierMachine np.verifier) (rowBase np x)
      (windowWidth np x.length) (maxClock np x.length)
def decodeTrace (np : ClassNP) (x : Word) (a : Assignment) : List Config :=
  Issue624.RunCNF.decodeTrace (verifierMachine np.verifier) (rowBase np x)
    (windowWidth np x.length) (maxClock np x.length) a

@[simp] theorem sources_length (np : ClassNP) (x : Word) :
    (sources np x).length = windowWidth np x.length := by
  apply windowSources_length
  cases np.verifier <;> simp [inputSources, windowWidth] <;> omega

theorem initialRow_span (np : ClassNP) (x : Word) (a : Assignment) :
    span (initialRow np x a) = windowWidth np x.length := by
  apply fitWindow_span
  have hs := verifierInitial_span np.verifier x (decodeCertificate a 0 (np.certBound.eval x.length))
  have hc := decodeCertificate_length a 0 (np.certBound.eval x.length)
  unfold windowWidth
  omega

theorem initialCNF_row (np : ClassNP) (x : Word) (a : Assignment)
    (hf : evalCNF a (certificateCNF 0 (np.certBound.eval x.length)) = true) :
    evalCNF a (initialCNF (rowBase np x) (verifierMachine np.verifier).program.length
      (maxClock np x.length) (sources np x)) = true ↔
      RowRepresents a (rowBase np x) (verifierMachine np.verifier).program.length
        (windowWidth np x.length) (initialRow np x a) := by
  rw [← sources_length np x]
  apply initialCNF_models
  · simp [initialRow_span]
  · cases hv : np.verifier <;> cases x <;> simp [initialRow, fitWindow, verifierInitial, hv, initial, pairedInput, initialSymbols]
  · cases hv : np.verifier <;> cases x <;> simp [initialRow, fitWindow, verifierInitial, hv, initial,
      pairedInput, initialSymbols, blanks]
  · exact (windowSources_eval np x a hf).symm

theorem tableauCNF_unfold (np : ClassNP) (x : Word) (a : Assignment) :
    evalCNF a (tableauCNF np x) = true ↔
      evalCNF a (certificateCNF 0 (np.certBound.eval x.length)) = true ∧
      evalCNF a (initialCNF (rowBase np x) (verifierMachine np.verifier).program.length
        (maxClock np x.length) (sources np x)) = true ∧
      evalCNF a (Issue624.RunCNF.runCNF (verifierMachine np.verifier) (rowBase np x)
        (windowWidth np x.length) (maxClock np x.length)) = true := by
  simp [tableauCNF]

theorem tableauCNF_sound (np : ClassNP) (x : Word) (a : Assignment)
    (hf : evalCNF a (tableauCNF np x) = true) :
    WindowVerifierTableau np x a (decodeTrace np x a) := by
  obtain ⟨hc, hi, hr⟩ := (tableauCNF_unfold np x a).mp hf
  have hrow := (initialCNF_row np x a hc).mp hi
  have hs := Issue624.RunCNF.runCNF_sound _ _ _ _ a hr
  refine ⟨hc, ?_, Issue624.RunCNF.decodeTrace_length _ _ _ _ a, hs.2,
    Issue624.RunCNF.traceRepresents_width _ _ _ _ _ hs.1⟩
  unfold decodeTrace
  cases ht : maxClock np x.length with
  | zero => simp [ht, Issue624.RunCNF.runCNF, evalCNF, evalClause] at hr
  | succ k =>
    simp only [Issue624.RunCNF.decodeTrace]
    split <;> simp [decodeRow_represents _ _ _ _ _ hrow, initialRow, ht]

/-- Certificate slots stay below the row blocks in the joint model. -/
def jointAssignment (np : ClassNP) (x : Word) (a : Assignment) (trace : List Config) : Assignment :=
  fun v => if v < rowBase np x then a v else
    Issue624.RunCNF.traceAssignment (rowBase np x) (verifierMachine np.verifier).program.length
      (windowWidth np x.length) trace v

theorem decodeCertificate_congr (a b : Assignment) (start bound : Nat)
    (he : ∀ v, 2 * start ≤ v → v < 2 * (start + bound) → a v = b v) :
    decodeCertificate a start bound = decodeCertificate b start bound := by
  induction bound generalizing start with
  | zero => rfl
  | succ k ih =>
    have hp := he (2 * start) (by omega) (by omega)
    have hv := he (2 * start + 1) (by omega) (by omega)
    simp only [decodeCertificate, hp, hv]
    split
    · rw [ih (start + 1) (fun v hl hu => he v (by omega) (by omega))]
    · rfl

theorem tableauCNF_complete (np : ClassNP) (x : Word) (a : Assignment) (trace : List Config)
    (ht : WindowVerifierTableau np x a trace) :
    ∃ b, evalCNF b (tableauCNF np x) = true ∧
      decodeCertificate b 0 (np.certBound.eval x.length) =
        decodeCertificate a 0 (np.certBound.eval x.length) ∧ decodeTrace np x b = trace := by
  obtain ⟨hc, hh, hb, hl, hw⟩ := ht
  let b := jointAssignment np x a trace
  have he (v : Nat) (hv : v < rowBase np x) : b v = a v := by simp [b, jointAssignment, hv]
  have hcert : evalCNF b (certificateCNF 0 (np.certBound.eval x.length)) = true := by
    rw [evalCNF_congr b a (rowBase np x) _ he (by simpa [rowBase] using certificateCNF_variables 0 (np.certBound.eval x.length))]; exact hc
  have hd : decodeCertificate b 0 (np.certBound.eval x.length) =
      decodeCertificate a 0 (np.certBound.eval x.length) := by
    apply decodeCertificate_congr
    intro v _ hv
    exact he v (by unfold rowBase; omega)
  have hne : trace ≠ [] := by intro h; subst trace; exact hl
  have hrep := Issue624.RunCNF.traceAssignment_represents (rowBase np x)
    (verifierMachine np.verifier).program.length (windowWidth np x.length) trace hne
    (fun c hc' => ⟨hw c hc', accepting_trace_state_lt _ trace hl c hc'⟩)
  have hjrep : Issue624.RunCNF.TraceRepresents b (rowBase np x)
      (verifierMachine np.verifier).program.length (windowWidth np x.length) trace := by
    apply Issue624.RunCNF.traceRepresents_congr _ b _ _ _ trace _ hrep
    intro v hv; simp [b, jointAssignment, Nat.not_lt.mpr hv]
  have hi : RowRepresents b (rowBase np x) (verifierMachine np.verifier).program.length
      (windowWidth np x.length) (initialRow np x b) := by
    cases trace with
    | nil => exact False.elim (hne rfl)
    | cons c rest =>
      have hh' : c = initialRow np x a := by simpa [initialRow] using hh
      have hid : initialRow np x b = initialRow np x a := by simp [initialRow, hd]
      rw [hid, ← hh']; exact hjrep.1
  refine ⟨b, (tableauCNF_unfold np x b).mpr ⟨hcert, (initialCNF_row np x b hcert).mpr hi,
    Issue624.RunCNF.runCNF_complete _ _ _ _ b trace hjrep hl hb⟩, hd,
    Issue624.RunCNF.decodeTrace_represents _ _ _ _ b trace hjrep hb⟩

theorem tableauCNF_iff (np : ClassNP) (x : Word) :
    Satisfiable (tableauCNF np x) ↔ np.language x = true := by
  constructor
  · rintro ⟨a, hf⟩
    exact (windowVerifierTableau_iff_language np x).mp ⟨a, _, tableauCNF_sound np x a hf⟩
  · intro hx
    obtain ⟨a, trace, ht⟩ := (windowVerifierTableau_iff_language np x).mpr hx
    obtain ⟨b, hb, _⟩ := tableauCNF_complete np x a trace ht
    exact ⟨b, hb⟩

theorem tableauCNF_rejecting_unsatisfiable (np : ClassNP) (x : Word)
    (h : ∀ w, np.language w = false) : ¬Satisfiable (tableauCNF np x) := by
  rw [tableauCNF_iff, h x]; decide

theorem tableauCNF_overlong_rejected (np : ClassNP) (x cert : Word) (a : Assignment)
    (h : np.certBound.eval x.length < cert.length)
    (he : ∀ v, v ≤ 2 * np.certBound.eval x.length → a v = encodeCertificate cert v) :
    evalCNF a (tableauCNF np x) = false := by
  have hc := evalCNF_congr a (encodeCertificate cert) (rowBase np x)
    (certificateCNF 0 (np.certBound.eval x.length))
    (fun v hv => he v (by unfold rowBase at hv; omega)) (by simpa [rowBase] using certificateCNF_variables 0 (np.certBound.eval x.length))
  rw [overlong_rejected cert _ h] at hc
  simp [tableauCNF, hc]

theorem tableauCNF_wrong_successor_rejected (np : ClassNP) (x : Word) (a : Assignment)
    (c d : Config) (rest : List Config)
    (hs : step (verifierMachine np.verifier) c ≠ .inr d)
    (hd : decodeTrace np x a = c :: d :: rest) : evalCNF a (tableauCNF np x) = false := by
  have h := Issue624.RunCNF.runCNF_wrong_successor_rejected _ _ _ _ a c d rest hs hd
  simp [tableauCNF, h]

def offsetPolynomial (np : ClassNP) : Polynomial :=
  polyAdd (polyMul ⟨2, 0⟩ np.certBound) ⟨1, 0⟩
def sizePolynomial (np : ClassNP) : Polynomial :=
  polyAdd (certificatePolynomial np.certBound)
    (polyAdd (initialPolynomial (verifierMachine np.verifier).program.length
      (offsetPolynomial np) (windowPolynomial np))
      (Issue624.RunCNF.runPolynomial (verifierMachine np.verifier)
        (offsetPolynomial np) (windowPolynomial np) (clockPolynomial np)))

theorem encodeCNF_length_append (f g : CNF) :
    (encodeCNF (f ++ g)).length = (encodeCNF f).length + (encodeCNF g).length := by
  induction f with
  | nil => simp [encodeCNF]
  | cons c f ih => simp [encodeCNF, ih, Nat.add_assoc]

theorem tableauCNF_encoded_size (np : ClassNP) (x : Word) :
    (encodeCNF (tableauCNF np x)).length ≤ (sizePolynomial np).eval x.length := by
  have hb : rowBase np x ≤ (offsetPolynomial np).eval x.length := by
    have ha := polyAdd_eval (polyMul ⟨2, 0⟩ np.certBound) ⟨1, 0⟩ x.length
    rw [← polyMul_eval] at ha
    simpa only [offsetPolynomial, rowBase, Polynomial.eval, Nat.pow_zero, Nat.mul_one] using ha
  have hw := windowWidth_polynomial np x.length
  have ht := maxClock_polynomial np x.length
  have hi := initialCNF_polynomial_size (verifierMachine np.verifier).program.length
    (offsetPolynomial np) (windowPolynomial np) x.length (rowBase np x)
    (maxClock np x.length) (np.certBound.eval x.length) (sources np x) hb
    (by simpa using hw) (by simp only [sources_length, windowWidth]; omega) (by unfold rowBase; omega)
    (windowSources_bound _ _ _ _ _)
  have hr := Issue624.RunCNF.runCNF_polynomial_size (verifierMachine np.verifier)
    (offsetPolynomial np) (windowPolynomial np) (clockPolynomial np) x.length
    (rowBase np x) (windowWidth np x.length) (maxClock np x.length) hb hw ht
  have hc := certificateCNF_polynomial_size np.certBound x.length
  have hs := Nat.le_trans (Nat.add_le_add hi hr) (polyAdd_eval _ _ x.length)
  have hall := Nat.le_trans (Nat.add_le_add hc hs) (polyAdd_eval _ _ x.length)
  simpa only [tableauCNF, encodeCNF_length_append, sizePolynomial, Nat.add_assoc] using hall

end Issue624.CookLevin
