import proofs.experiments.issue624.lean.VerifierTableau

/-!
Fixed finite tape windows for the existing `LocalTrace` semantics. The machine
is two-way: moving left when `left = []` creates a new blank cell. Padding on
both sides therefore needs a checked simulation, not an assumed left boundary.
-/
namespace Issue624.FixedWindow

open Complexity Issue532.Machines Issue568.Tableau Issue624.CertificateCNF
open Issue624.VerifierTableau

/-- Equality of tapes up to represented blank padding on both sides. -/
def TapeEquivalent (c d : Config) : Prop :=
  c.state = d.state ∧ c.head = d.head ∧
    BlankPad c.left d.left ∧ BlankPad c.right d.right

theorem TapeEquivalent.symm {c d : Config} (h : TapeEquivalent c d) :
    TapeEquivalent d c := ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem tapeEquivalent_moveHead {c d : Config} (h : TapeEquivalent c d)
    (q : Nat) (w : Symbol) (dir : Direction) :
    TapeEquivalent (moveHead c q w dir) (moveHead d q w dir) := by
  rcases c with ⟨cs, cl, ch, cr⟩
  rcases d with ⟨ds, dl, dh, dr⟩
  obtain ⟨_, _, hl, hr⟩ := h
  cases dir with
  | stay => exact ⟨rfl, rfl, hl, hr⟩
  | left =>
    cases cl with
    | nil =>
      cases dl with
      | nil => exact ⟨rfl, rfl, BlankPad.refl [], hr.cons w⟩
      | cons b s =>
        obtain ⟨hb, hs⟩ := hl.nil_cons
        exact ⟨rfl, hb.symm, hs, hr.cons w⟩
    | cons a r =>
      cases dl with
      | nil =>
        obtain ⟨ha, hs⟩ := hl.symm.nil_cons
        exact ⟨rfl, ha, hs.symm, hr.cons w⟩
      | cons b s =>
        obtain ⟨hab, hs⟩ := hl.cons_cons
        exact ⟨rfl, hab, hs, hr.cons w⟩
  | right =>
    cases cr with
    | nil =>
      cases dr with
      | nil => exact ⟨rfl, rfl, hl.cons w, BlankPad.refl []⟩
      | cons b s =>
        obtain ⟨hb, hs⟩ := hr.nil_cons
        exact ⟨rfl, hb.symm, hl.cons w, hs⟩
    | cons a r =>
      cases dr with
      | nil =>
        obtain ⟨ha, hs⟩ := hr.symm.nil_cons
        exact ⟨rfl, ha, hl.cons w, hs.symm⟩
      | cons b s =>
        obtain ⟨hab, hs⟩ := hr.cons_cons
        exact ⟨rfl, hab, hl.cons w, hs⟩

theorem tapeEquivalent_step {m : Machine} {c d : Config} (h : TapeEquivalent c d) :
    (∀ b, step m c = .inl b → step m d = .inl b) ∧
      ∀ c', step m c = .inr c' → ∃ d', step m d = .inr d' ∧ TapeEquivalent c' d' := by
  have hi : m.instruction c.state c.head = m.instruction d.state d.head := by
    rw [h.1, h.2.1]
  unfold step
  rw [hi]
  cases m.instruction d.state d.head with
  | halt b => exact ⟨fun _ hb => hb, fun _ hc' => by cases hc'⟩
  | move q w dir =>
    refine ⟨(fun _ hb => by cases hb), fun c' hc' => ?_⟩
    cases hc'
    exact ⟨_, rfl, tapeEquivalent_moveHead h q w dir⟩

theorem run_of_tapeEquivalent {m : Machine} {c d : Config} {t : Nat} {b : Bool}
    (hr : Run m c t b) (h : TapeEquivalent c d) : Run m d t b := by
  induction hr generalizing d with
  | halt hs => exact Run.halt ((tapeEquivalent_step h).1 _ hs)
  | next hs _ ih =>
    obtain ⟨d', hd', he⟩ := (tapeEquivalent_step h).2 _ hs
    exact Run.next hd' (ih he)

/-- Put the head at least `margin` cells away from either represented edge.
The width contract is needed only for sizing, never for tape equivalence. -/
def fitWindow (c : Config) (margin width : Nat) : Config :=
  ⟨c.state, c.left ++ blanks margin, c.head,
    c.right ++ blanks (width - span c - margin)⟩

theorem fitWindow_equivalent (c : Config) (margin width : Nat) :
    TapeEquivalent c (fitWindow c margin width) := by
  refine ⟨rfl, rfl, ⟨c.left, 0, margin, ?_, rfl⟩,
    ⟨c.right, 0, width - span c - margin, ?_, rfl⟩⟩ <;> simp [blanks]

theorem run_fitWindow_iff (m : Machine) (c : Config) (t : Nat) (b : Bool)
    (margin width : Nat) : Run m (fitWindow c margin width) t b ↔ Run m c t b :=
  ⟨fun h => run_of_tapeEquivalent h (fitWindow_equivalent c margin width).symm,
    fun h => run_of_tapeEquivalent h (fitWindow_equivalent c margin width)⟩

theorem fitWindow_span (c : Config) (margin width : Nat)
    (h : span c + 2 * margin ≤ width) : span (fitWindow c margin width) = width := by
  simp only [span, fitWindow, List.length_append, blanks, List.length_replicate] at *
  omega

theorem fitWindow_reserve (c : Config) (margin width : Nat)
    (h : span c + 2 * margin ≤ width) :
    margin ≤ (fitWindow c margin width).left.length ∧
    margin ≤ (fitWindow c margin width).right.length := by
  simp only [span, fitWindow, List.length_append, blanks, List.length_replicate] at *
  omega

private theorem run_pos {m : Machine} {c : Config} {t : Nat} {b : Bool}
    (h : Run m c t b) : 0 < t := by cases h <;> omega

private theorem step_window {m : Machine} {c d : Config} {k : Nat}
    (hs : step m c = .inr d) (hl : k + 1 ≤ c.left.length)
    (hr : k + 1 ≤ c.right.length) :
    span d = span c ∧ k ≤ d.left.length ∧ k ≤ d.right.length := by
  rcases c with ⟨q, l, a, r⟩
  cases l with
  | nil => simp at hl
  | cons l ls =>
    cases r with
    | nil => simp at hr
    | cons r rs =>
      unfold step at hs
      cases hi : m.instruction q a with
      | halt b => simp [hi] at hs
      | move next w dir =>
        simp only [hi, Sum.inr.injEq] at hs
        subst d
        cases dir <;> simp_all [moveHead, span] <;> omega

/-- A bounded accepting run admits a `LocalTrace` with a single constant width,
provided its initial tape has enough represented blank reserve on each side. -/
theorem trace_window_of_run {m : Machine} {c : Config} {t : Nat} {b : Bool}
    (h : Run m c t b) (hl : t - 1 ≤ c.left.length) (hr : t - 1 ≤ c.right.length) :
    ∃ trace : List Config, trace.head? = some c ∧ trace.length = t ∧
      LocalTrace m b trace ∧ ∀ d ∈ trace, span d = span c := by
  induction h with
  | @halt c b hs => exact ⟨[c], rfl, rfl, hs, by simp⟩
  | @next c d t b hs hd ih =>
    have hp := run_pos hd
    have hw := step_window hs (k := t - 1) (by omega) (by omega)
    obtain ⟨trace, hhead, hlen, hlocal, hwidth⟩ := ih hw.2.1 hw.2.2
    cases trace with
    | nil => simp at hhead
    | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      refine ⟨c :: d :: rest, rfl, by simp [hlen], ⟨hs, hlocal⟩, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact (hwidth e he).trans hw.1

private theorem accepting_step_state_lt {m : Machine} {c : Config}
    (h : step m c = .inl true) : c.state < m.program.length := by
  apply Nat.lt_of_not_le
  intro hq
  unfold step at h
  rw [instruction_of_length_le c.head hq] at h
  cases h

/-- No accepting trace can enter a missing state, which rejects by default. -/
theorem accepting_trace_state_lt (m : Machine) : ∀ trace : List Config,
    LocalTrace m true trace → ∀ c ∈ trace, c.state < m.program.length := by
  intro trace
  induction trace with
  | nil => intro h; exact False.elim h
  | cons c rest ih =>
    cases rest with
    | nil =>
      intro h d hd
      simp only [List.mem_singleton] at hd
      subst d
      exact accepting_step_state_lt h
    | cons d tail =>
      rintro ⟨hs, ht⟩ e he
      rcases List.mem_cons.mp he with rfl | he
      · exact state_lt_of_step hs
      · exact ih ht e he

def windowWidth (np : ClassNP) (n : Nat) : Nat :=
  n + np.certBound.eval n + 2 * maxClock np n + 3

def windowPolynomial (np : ClassNP) : Polynomial :=
  ⟨np.certBound.coefficient + 2 * (clockPolynomial np).coefficient + 4,
    np.certBound.degree + (clockPolynomial np).degree + 1⟩

theorem windowWidth_polynomial (np : ClassNP) (n : Nat) :
    windowWidth np n ≤ (windowPolynomial np).eval n := by
  let d := np.certBound.degree + (clockPolynomial np).degree + 1
  have hc := Nat.mul_le_mul_left np.certBound.coefficient
    (Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega)
      (show np.certBound.degree ≤ d by dsimp [d]; omega))
  have ht := Nat.mul_le_mul_left (clockPolynomial np).coefficient
    (Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega)
      (show (clockPolynomial np).degree ≤ d by dsimp [d]; omega))
  have hn := Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega)
    (show 1 ≤ d by dsimp [d]; omega)
  simp only [Nat.pow_one] at hn
  have hclock := maxClock_polynomial np n
  change maxClock np n ≤ (clockPolynomial np).coefficient *
    (n + 1) ^ (clockPolynomial np).degree at hclock
  change windowWidth np n ≤ (np.certBound.coefficient +
    2 * (clockPolynomial np).coefficient + 4) * (n + 1) ^ d
  simp only [windowWidth, Polynomial.eval, Nat.add_mul, Nat.mul_assoc]
  omega

/-- A fixed-width representation still using precisely #568's local trace. -/
def WindowVerifierTableau (np : ClassNP) (x : Word) (a : Assignment)
    (trace : List Config) : Prop :=
  let cert := decodeCertificate a 0 (np.certBound.eval x.length)
  let clock := maxClock np x.length
  let width := windowWidth np x.length
  evalCNF a (certificateCNF 0 (np.certBound.eval x.length)) = true ∧
  trace.head? = some (fitWindow (verifierInitial np.verifier x cert) clock width) ∧
  trace.length ≤ clock ∧ LocalTrace (verifierMachine np.verifier) true trace ∧
  ∀ d ∈ trace, span d = width

/-- Complete fixed-window model correspondence for all `ClassNP` witnesses.
This is the finite semantic representation, before compilation into CNF. -/
theorem windowVerifierTableau_iff_language (np : ClassNP) (x : Word) :
    (∃ a trace, WindowVerifierTableau np x a trace) ↔ np.language x = true := by
  constructor
  · rintro ⟨a, trace, _, hhead, _, hlocal, _⟩
    have hc := decodeCertificate_length a 0 (np.certBound.eval x.length)
    have hrun := (localTrace_iff_run _ _ _ true).mp ⟨trace, hhead, rfl, hlocal⟩
    have hrun' := (run_fitWindow_iff _ _ _ _ _ _).mp hrun
    have hv := (verifierRun_iff _ _ _ _ _).mpr hrun'
    exact (np.correct x).mpr ⟨_, trace.length, hc,
      acceptingRun_timeLimit np x _ trace.length hc hv, hv⟩
  · intro hx
    obtain ⟨cert, t, hc, ht, hv⟩ := (np.correct x).mp hx
    have hclock := Nat.le_trans ht (verifierTimeLimit_le np x cert hc)
    have hfit : span (verifierInitial np.verifier x cert) + 2 * maxClock np x.length ≤
        windowWidth np x.length := by
      have hspan := verifierInitial_span np.verifier x cert
      unfold windowWidth
      omega
    have hr := (run_fitWindow_iff _ _ _ _ (maxClock np x.length)
      (windowWidth np x.length)).mpr ((verifierRun_iff _ _ _ _ _).mp hv)
    have hreserve := fitWindow_reserve _ _ _ hfit
    obtain ⟨trace, hhead, hlen, hlocal, hwidth⟩ :=
      trace_window_of_run hr (by omega) (by omega)
    refine ⟨encodeCertificate cert, trace, ?_⟩
    unfold WindowVerifierTableau
    rw [decode_encodeCertificate cert _ hc]
    exact ⟨encodeCertificate_models cert _ hc, hhead, hlen ▸ hclock, hlocal,
      fun d hd => (hwidth d hd).trans (fitWindow_span _ _ _ hfit)⟩

end Issue624.FixedWindow
