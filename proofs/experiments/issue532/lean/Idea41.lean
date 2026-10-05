import proofs.experiments.issue532.lean.Circuits
import proofs.experiments.issue532.lean.Idea16

/-!
# Idea 41: Williams' algorithmic method in the shared model

Williams (2010, 2011) turned faster-than-exhaustive-search satisfiability
algorithms into circuit lower bounds: if the satisfiability of circuits from a
class `C` with `n` inputs and polynomially many gates can be decided in time
`2^n / n^{ω(1)}`, then `NEXP ⊄ C`. For `C = ACC⁰` the algorithm exists, which
gives `NEXP ⊄ ACC⁰` (Williams 2011) and `NQP ⊄ ACC⁰` (Murray–Williams 2018).
For general circuits (`C = P/poly`) the algorithm is an open problem.

This file states the method for general NAND circuits over the shared model:

* `InNTIME`, `InNEXP`, `NEXPSubsetPPoly`: nondeterministic time with `Run`
  step counts and paired certificates (clocked, as in `Complexity.ClassNP`;
  `inNTIME_iff_idea16` shows it is Idea 16's class), the class NEXP, and the
  statement `NEXP ⊆ P/poly` over `Issue532.Circuits`.
* `CircuitSAT`, `encCircuit`, `bruteCircuitSAT_correct`,
  `length_allAssignments`: circuit satisfiability as a language, and the
  exhaustive-search baseline with its `2^n` assignments.
* `FastCircuitSAT`: **the open obligation.** One machine decides
  satisfiability of circuits with `n` inputs and `(n+1)^k` gates within
  `2^n / n^{ω(1)}` `Run` steps.
* `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup`: the three known
  theorems of the proof, stated in the model and used only as explicit
  hypotheses.
* `williams_method`: the implication `FastCircuitSAT → ¬ NEXPSubsetPPoly`
  under those hypotheses. `williams_method_idea16` takes the hierarchy theorem
  in Idea 16's form (`nTimeHierarchy_of_idea16`).
* `lazy_diagonal`, `nTimeHierarchy_of_lazyDiagonal`: the diagonal argument of
  Žák's hierarchy theorem, proved; what remains of `NTimeHierarchy` is a
  simulation statement, `LazyDiagonalSimulation`.
* `fastCircuitSAT_of_pEqualsNP`, `pNotEqualsNP_of_not_fastCircuitSAT`,
  `pNotEqualsNP_of_nexpSubsetPPoly`: the obligation is implied by `P = NP`, so
  refuting it proves `P ≠ NP`, and `NEXP ⊆ P/poly` would also prove `P ≠ NP`.
* `not_forall_inNTIME`: nondeterministic time classes are not everything.
-/

namespace Issue532.Idea41

open Complexity Issue532.Machines Issue532.Circuits

/-! ## Nondeterministic time -/

/-- `m`, started on `x` paired with the certificate `cert`, accepts within
`T` steps. -/
def AcceptsWithin (m : Machine) (T : Nat) (x cert : Word) : Prop :=
  ∃ t, t ≤ T ∧ Run m (pairedInput x cert) t true

/-- `m` is a clocked nondeterministic verifier for `L` with certificate
length and running time at most `c · T(n) + c`: it halts within that bound on
every short certificate, and `x ∈ L` iff it accepts one. The constant `c`
absorbs constant factors and finitely many short inputs. -/
def VerifiesIn (m : Machine) (c : Nat) (T : Nat → Nat) (L : Language) : Prop :=
  (∀ x cert, cert.length ≤ c * T x.length + c →
    ∃ t b, t ≤ c * T x.length + c ∧ Run m (pairedInput x cert) t b) ∧
  ∀ x : Word, L x = true ↔
    ∃ cert : Word, cert.length ≤ c * T x.length + c ∧
      AcceptsWithin m (c * T x.length + c) x cert

/-- The class `NTIME(T)` over `Complexity.Machine`. -/
def InNTIME (T : Nat → Nat) (L : Language) : Prop :=
  ∃ (m : Machine) (c : Nat), VerifiesIn m c T L

/-- This is Idea 16's `NTIME(T)`, the class its hierarchy theorem is stated
for; so the two files use one definition. -/
theorem inNTIME_iff_idea16 (T : Nat → Nat) (L : Language) :
    InNTIME T L ↔ Idea16.InNTIME T L := by
  constructor
  · rintro ⟨m, c, hhalt, hL⟩
    refine ⟨m, c, hhalt, fun x => ?_⟩
    rw [hL x]
    constructor
    · rintro ⟨cert, hc, t, ht, hr⟩
      exact ⟨cert, t, hc, ht, hr⟩
    · rintro ⟨cert, t, hc, ht, hr⟩
      exact ⟨cert, hc, t, ht, hr⟩
  · rintro ⟨m, c, hhalt, hL⟩
    refine ⟨m, c, hhalt, fun x => ?_⟩
    rw [hL x]
    constructor
    · rintro ⟨cert, t, hc, ht, hr⟩
      exact ⟨cert, hc, t, ht, hr⟩
    · rintro ⟨cert, hc, t, ht, hr⟩
      exact ⟨cert, t, hc, ht, hr⟩

/-- The exponential time bound `2^{n^k}`. -/
def expBound (k : Nat) (n : Nat) : Nat := 2 ^ (n ^ k)

/-- The class NEXP. -/
def InNEXP (L : Language) : Prop := ∃ k, InNTIME (expBound k) L

/-- The statement `NEXP ⊆ P/poly` for NAND circuits. Williams' method refutes
it from a fast circuit-satisfiability algorithm. -/
def NEXPSubsetPPoly : Prop := ∀ L : Language, InNEXP L → InPPoly L

/-- `NTIME(2^n) ⊆ NEXP`. -/
theorem inNEXP_of_inNTIME_two_pow {L : Language} (h : InNTIME (fun n => 2 ^ n) L) :
    InNEXP L := by
  obtain ⟨m, c, hhalt, hm⟩ := h
  refine ⟨1, m, c, fun x cert hc => ?_, fun x => ?_⟩
  · simpa [expBound] using hhalt x cert (by simpa [expBound] using hc)
  · simpa [expBound] using hm x

/-! ### Non-vacuity

A time class is a family of languages indexed by a machine and a constant, so
Cantor's argument leaves a language outside it. -/

/-- The language accepted by `m` with constant `c`. -/
noncomputable def acceptedLanguage (m : Machine) (c : Nat) (T : Nat → Nat) : Language :=
  fun x => by
    classical
    exact decide (∃ cert : Word, cert.length ≤ c * T x.length + c ∧
      AcceptsWithin m (c * T x.length + c) x cert)

theorem eq_acceptedLanguage {m : Machine} {c : Nat} {T : Nat → Nat} {L : Language}
    (h : VerifiesIn m c T L) : L = acceptedLanguage m c T := by
  classical
  funext x
  unfold acceptedLanguage
  cases hL : L x with
  | true => exact (decide_eq_true ((h.2 x).mp hL)).symm
  | false =>
    refine (decide_eq_false fun hx => ?_).symm
    have := (h.2 x).mpr hx
    rw [hL] at this
    cases this

/-- No time bound puts every language in `NTIME(T)`. -/
theorem not_forall_inNTIME (T : Nat → Nat) : ¬ ∀ L : Language, InNTIME T L := by
  intro hall
  obtain ⟨L, hL⟩ := exists_language_not_in_family
    (fun x : Machine × Nat => encMachinePoly (x.1, ⟨x.2, 0⟩))
    (fun a b h => by
      have := encMachinePoly_injective _ _ h
      obtain ⟨m, c⟩ := a
      obtain ⟨m', c'⟩ := b
      simp only [Prod.mk.injEq, Polynomial.mk.injEq] at this
      rw [this.1, this.2.1])
    (fun x => acceptedLanguage x.1 x.2 T)
  obtain ⟨m, c, hm⟩ := hall L
  exact hL (m, c) (eq_acceptedLanguage hm).symm

/-! ## Circuit satisfiability as a language -/

/-- A gate `(i, j)` as two unary numbers. -/
def encGate (g : Nat × Nat) : Word := encNat g.1 ++ encNat g.2

theorem encGate_prefixFree : PrefixFree encGate := by
  intro a b r s h
  simp only [encGate, List.append_assoc] at h
  obtain ⟨h1, h⟩ := encNat_prefixFree _ _ _ _ h
  obtain ⟨h2, h⟩ := encNat_prefixFree _ _ _ _ h
  exact ⟨Prod.ext h1 h2, h⟩

/-- A circuit instance: the number of inputs, then the gate list. -/
def encCircuit (n : Nat) (C : Circuit) : Word := encNat n ++ encList encGate C

theorem encCircuit_injective {n n' : Nat} {C C' : Circuit}
    (h : encCircuit n C = encCircuit n' C') : n = n' ∧ C = C' := by
  unfold encCircuit at h
  obtain ⟨hn, h⟩ := encNat_prefixFree _ _ _ _ h
  obtain ⟨hC, _⟩ := encList_prefixFree encGate_prefixFree _ _ [] [] (by simpa using h)
  exact ⟨hn, hC⟩

/-! ### Executable decoding of the exact circuit encoding -/

/-- Read a unary natural, leaving the unconsumed suffix. -/
def decNat : Word → Option (Nat × Word)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => do
      let (n, rest) ← decNat r
      pure (n + 1, rest)

theorem decNat_encNat (n : Nat) (r : Word) :
    decNat (encNat n ++ r) = some (n, r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encNat, decNat, ih]

/-- Read the two unary wire indices of one NAND gate. -/
def decGate (w : Word) : Option ((Nat × Nat) × Word) := do
  let (i, r) ← decNat w
  let (j, rest) ← decNat r
  pure ((i, j), rest)

theorem decGate_encGate (g : Nat × Nat) (r : Word) :
    decGate (encGate g ++ r) = some (g, r) := by
  obtain ⟨i, j⟩ := g
  simp [decGate, encGate, List.append_assoc, decNat_encNat]

/-- The list marker consumes at least one bit per gate, so input length is
enough recursion fuel even if a gate decoder fails to make progress. -/
def decListFuel {α : Type} (d : Word → Option (α × Word)) : Nat → Word →
    Option (List α × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: r => some ([], r)
  | f + 1, true :: r => do
      let (a, r₁) ← d r
      let (l, r₂) ← decListFuel d f r₁
      pure (a :: l, r₂)

def decList {α : Type} (d : Word → Option (α × Word)) (w : Word) :
    Option (List α × Word) := decListFuel d w.length w

theorem length_lt_encList {α : Type} (e : α → Word) (l : List α) :
    l.length < (encList e l).length := by
  induction l with
  | nil => simp [encList]
  | cons a l ih => simp only [encList, List.length_cons, List.length_append]; omega

theorem decListFuel_encList {α : Type} (e : α → Word)
    (d : Word → Option (α × Word))
    (hd : ∀ a r, d (e a ++ r) = some (a, r))
    (l : List α) (r : Word) (fuel : Nat) (hf : l.length < fuel) :
    decListFuel d fuel (encList e l ++ r) = some (l, r) := by
  induction l generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ f => rfl
  | cons a l ih =>
      cases fuel with
      | zero => omega
      | succ f =>
          have hf' : l.length < f := by simp at hf; omega
          simp [decListFuel, encList, List.append_assoc, hd, ih f hf']

theorem decList_encList {α : Type} (e : α → Word)
    (d : Word → Option (α × Word))
    (hd : ∀ a r, d (e a ++ r) = some (a, r))
    (l : List α) (r : Word) :
    decList d (encList e l ++ r) = some (l, r) := by
  unfold decList
  apply decListFuel_encList e d hd
  have h := length_lt_encList e l
  simp only [List.length_append]
  omega

/-- Decode the whole word; the final equality rejects trailing bits as well
as any noncanonical encoding. -/
def decCircuit (w : Word) : Option (Nat × Circuit) := do
  let (n, r) ← decNat w
  let (C, _) ← decList decGate r
  if w = encCircuit n C then some (n, C) else none

theorem decCircuit_encCircuit (n : Nat) (C : Circuit) :
    decCircuit (encCircuit n C) = some (n, C) := by
  have hlist := decList_encList encGate decGate decGate_encGate C []
  simp at hlist
  simp [decCircuit, encCircuit, decNat_encNat, hlist]

theorem decCircuit_sound {w : Word} {n : Nat} {C : Circuit}
    (h : decCircuit w = some (n, C)) : w = encCircuit n C := by
  unfold decCircuit at h
  cases hn : decNat w with
  | none => simp [hn] at h
  | some nr =>
      obtain ⟨n₀, r⟩ := nr
      simp only [hn] at h
      cases hc : decList decGate r with
      | none => simp [hc] at h
      | some cr =>
          obtain ⟨C₀, rest⟩ := cr
          simp [hc] at h
          obtain ⟨heq, rfl, rfl⟩ := h
          exact heq

/-- Check that every gate reads only an earlier wire. This also rejects a
gate on zero inputs before any wire has been produced. -/
def wfFromb : Nat → Circuit → Bool
  | _, [] => true
  | N, (i, j) :: C => decide (i < N) && decide (j < N) && wfFromb (N + 1) C

theorem wfFromb_iff (N : Nat) (C : Circuit) :
    wfFromb N C = true ↔ WFfrom N C := by
  induction C generalizing N with
  | nil => simp [wfFromb, WFfrom]
  | cons g C ih =>
      obtain ⟨i, j⟩ := g
      simp [wfFromb, WFfrom, ih, and_assoc]

/-- Parsing and well-formedness together, with failure on malformed words. -/
def checkCircuit (w : Word) : Bool :=
  match decCircuit w with
  | none => false
  | some (n, C) => wfFromb n C

theorem checkCircuit_iff (w : Word) :
    checkCircuit w = true ↔ ∃ n C, w = encCircuit n C ∧ WF n C := by
  constructor
  · intro h
    cases hd : decCircuit w with
    | none => simp [checkCircuit, hd] at h
    | some nc =>
        obtain ⟨n, C⟩ := nc
        have hw := decCircuit_sound hd
        have hWF : WF n C := (wfFromb_iff n C).mp (by simpa [checkCircuit, hd] using h)
        exact ⟨n, C, hw, hWF⟩
  · rintro ⟨n, C, rfl, hwf⟩
    simpa [checkCircuit, decCircuit_encCircuit] using (wfFromb_iff n C).mpr hwf

/-- The intermediate wire list has exactly one new bit per gate. -/
theorem wires_length (x : Word) (C : Circuit) :
    (wires x C).length = x.length + C.length := Circuits.wires_length x C

/-- Some input of length `n` makes `C` output `true`. -/
def CircuitSatisfiable (n : Nat) (C : Circuit) : Prop :=
  ∃ x : Word, x.length = n ∧ output x C = true

/-- Circuit satisfiability: the word encodes a well-formed satisfiable
circuit. -/
noncomputable def CircuitSAT : Language := fun w => by
  classical
  exact decide (∃ n C, w = encCircuit n C ∧ WF n C ∧ CircuitSatisfiable n C)

theorem circuitSAT_encode (n : Nat) (C : Circuit) :
    CircuitSAT (encCircuit n C) = true ↔ WF n C ∧ CircuitSatisfiable n C := by
  classical
  unfold CircuitSAT
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨n', C', h, hw, hs⟩
    obtain ⟨rfl, rfl⟩ := encCircuit_injective h
    exact ⟨hw, hs⟩
  · rintro ⟨hw, hs⟩
    exact ⟨n, C, rfl, hw, hs⟩

/-- Finite certificate check. The word is decoded exactly, malformed and
forward-wire circuits are rejected, and a certificate must have exactly `n`
bits. `output` is the same NAND evaluator used by `CircuitSatisfiable`. -/
def verifyCircuit (w cert : Word) : Bool :=
  match decCircuit w with
  | none => false
  | some (n, C) => wfFromb n C && decide (cert.length = n) && output cert C

theorem verifyCircuit_spec (w cert : Word) :
    verifyCircuit w cert = true ↔
      ∃ n C, decCircuit w = some (n, C) ∧ WF n C ∧
        cert.length = n ∧ output cert C = true := by
  unfold verifyCircuit
  cases hd : decCircuit w with
  | none => simp
  | some nc =>
      obtain ⟨n, C⟩ := nc
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨⟨hwf, hlen⟩, hout⟩
        exact ⟨n, C, rfl, (wfFromb_iff n C).mp hwf, hlen, hout⟩
      · rintro ⟨n', C', hdec, hwf, hlen, hout⟩
        have heq : (n, C) = (n', C') := Option.some.inj hdec
        cases heq
        exact ⟨⟨(wfFromb_iff n C).mpr hwf, hlen⟩, hout⟩

theorem circuitSAT_iff_verifyCircuit (w : Word) :
    CircuitSAT w = true ↔ ∃ cert, verifyCircuit w cert = true := by
  classical
  unfold CircuitSAT
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨n, C, rfl, hwf, cert, hlen, hout⟩
    exact ⟨cert, (verifyCircuit_spec _ _).mpr
      ⟨n, C, decCircuit_encCircuit n C, hwf, hlen, hout⟩⟩
  · rintro ⟨cert, hcert⟩
    obtain ⟨n, C, hd, hwf, hlen, hout⟩ := (verifyCircuit_spec _ _).mp hcert
    exact ⟨n, C, decCircuit_sound hd, hwf, cert, hlen, hout⟩

/-- Encoded instance size bounds both the declared number of inputs and the
number of gates. No machine runtime bound follows from this statement. -/
theorem decCircuit_data_bounds {w : Word} {n : Nat} {C : Circuit}
    (h : decCircuit w = some (n, C)) :
    n + 1 ≤ w.length ∧ C.length + 1 ≤ w.length := by
  have hw := decCircuit_sound h
  have hc := length_lt_encList encGate C
  have hnat : ∀ k, (encNat k).length = k + 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [encNat, ih]
  rw [hw]
  simp only [encCircuit, List.length_append, hnat n]
  omega

theorem verifyCircuit_cert_bound {w cert : Word}
    (h : verifyCircuit w cert = true) : cert.length ≤ w.length := by
  obtain ⟨n, C, hd, _, hlen, _⟩ := (verifyCircuit_spec w cert).mp h
  have hb := (decCircuit_data_bounds hd).1
  omega

/-- **Known theorem, not mechanised here.** Circuit satisfiability is in NP:
the certificate is a satisfying input and the verifier evaluates the circuit
(Karp 1972; Arora–Barak §6.1). The missing part is the evaluating machine in
this model. -/
def CircuitSATInNP : Prop := InNP CircuitSAT

/-! ## The exhaustive-search baseline -/

theorem length_allAssignments (n : Nat) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allAssignments, List.length_append, List.length_map, ih]
    rw [Nat.pow_succ]
    omega

/-- Exhaustive search: evaluate `C` on all `2^n` inputs. -/
def bruteCircuitSAT (n : Nat) (C : Circuit) : Bool :=
  (allAssignments n).any (fun x => output x C)

theorem bruteCircuitSAT_correct (n : Nat) (C : Circuit) :
    bruteCircuitSAT n C = true ↔ CircuitSatisfiable n C := by
  unfold bruteCircuitSAT CircuitSatisfiable
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, ho⟩
    exact ⟨x, (mem_allAssignments_iff n x).mp hx, ho⟩
  · rintro ⟨x, hx, ho⟩
    exact ⟨x, (mem_allAssignments_iff n x).mpr hx, ho⟩

/-- Exhaustive search evaluates `2^n` circuits of `|C|` gates each. The
method needs a machine that beats this count by a superpolynomial factor. -/
def bruteForceGateEvaluations (n : Nat) (C : Circuit) : Nat :=
  (allAssignments n).length * C.length

theorem bruteForceGateEvaluations_eq (n : Nat) (C : Circuit) :
    bruteForceGateEvaluations n C = 2 ^ n * C.length := by
  rw [bruteForceGateEvaluations, length_allAssignments]

/-! ## The open obligation -/

/-- **Open obligation (Williams 2010).** For every `k` one machine decides
satisfiability of well-formed circuits with `n` inputs and at most `(n+1)^k`
gates in `2^n / n^{ω(1)}` `Run` steps: for every `c`, from some length on,
`t · (n+1)^c ≤ 2^n`. Exhaustive search needs `2^n · |C|` gate evaluations
(`bruteForceGateEvaluations_eq`). -/
def FastCircuitSAT : Prop :=
  ∀ k : Nat, ∃ m : Machine, ∀ c : Nat, ∃ n₀ : Nat, ∀ n : Nat, n₀ ≤ n →
    ∀ C : Circuit, WF n C → C.length ≤ (n + 1) ^ k →
      ∃ t b, t * (n + 1) ^ c ≤ 2 ^ n ∧ Run m (initial (encCircuit n C)) t b ∧
        (b = true ↔ CircuitSatisfiable n C)

/-! ## The known theorems of the proof -/

/-- The truth table of a circuit on `ℓ` inputs, as a word of length `2^ℓ`. -/
def truthTable (ℓ : Nat) (W : Circuit) : Word :=
  (allAssignments ℓ).map (fun y => output y W)

theorem length_truthTable (ℓ : Nat) (W : Circuit) : (truthTable ℓ W).length = 2 ^ ℓ := by
  rw [truthTable, List.length_map, length_allAssignments]

/-- Every NEXP verifier has succinct witnesses: every accepted input has an
accepted certificate that is a prefix of the truth table of a circuit with
polynomially many gates. -/
def SuccinctWitnesses : Prop :=
  ∀ (k : Nat) (m : Machine) (c : Nat) (L : Language), VerifiesIn m c (expBound k) L →
    ∃ d : Nat, ∀ x : Word, L x = true →
      ∃ (ℓ r : Nat) (W : Circuit), W.length ≤ d * (x.length + 1) ^ d ∧ WF ℓ W ∧
        r ≤ c * expBound k x.length + c ∧
        AcceptsWithin m (c * expBound k x.length + c) x ((truthTable ℓ W).take r)

/-- **Known theorem, not mechanised here: the easy-witness lemma**
(Impagliazzo–Kabanets–Wigderson 2002, Theorem 11; Williams 2013, Lemma 3.1).
If `NEXP ⊆ P/poly`, every NEXP verifier has succinct witnesses. -/
def EasyWitnessLemma : Prop := NEXPSubsetPPoly → SuccinctWitnesses

/-- **Known theorem, not mechanised here: the nondeterministic time
hierarchy** (Cook 1973; Seiferas–Fischer–Meyer 1978; Žák 1983). Some language
in `NTIME(2^n)` is outside `NTIME(2^n / (n+1)^c)`. The polynomial gap absorbs
the logarithmic clock overhead of a single-tape simulation.
`nTimeHierarchy_of_lazyDiagonal` proves the diagonal part. -/
def NTimeHierarchy : Prop :=
  ∃ c : Nat, ∃ L : Language, InNTIME (fun n => 2 ^ n) L ∧
    ¬ InNTIME (fun n => 2 ^ n / (n + 1) ^ c) L

/-- **Known theorem, not mechanised here: Williams' speedup** (Williams 2010,
Theorem 1.1 and §3; Williams 2013). A language in `NTIME(2^n)` reduces to
Succinct-3SAT by a quasi-linear Cook–Levin reduction (Tourlakis 2001;
Fortnow–Lipton–van Melkebeek–Viglas 2005). A faster verifier guesses a small
circuit `W` for a satisfying assignment, builds the circuit `D(i)` = "clause
`i` is falsified by `W`", which has `n + O(log n)` inputs and polynomially many
gates, and checks that `D` is unsatisfiable with the fast algorithm. So a fast
circuit-satisfiability algorithm and succinct witnesses put every language of
`NTIME(2^n)` into `NTIME(2^n / (n+1)^c)` for every `c`. -/
def WilliamsSpeedup : Prop :=
  FastCircuitSAT → SuccinctWitnesses →
    ∀ (c : Nat) (L : Language), InNTIME (fun n => 2 ^ n) L →
      InNTIME (fun n => 2 ^ n / (n + 1) ^ c) L

/-! ## The method -/

/-- **Williams' algorithmic method.** A fast circuit-satisfiability algorithm
refutes `NEXP ⊆ P/poly`, given the three known theorems. -/
theorem williams_method (hier : NTimeHierarchy) (ewl : EasyWitnessLemma)
    (speedup : WilliamsSpeedup) (fast : FastCircuitSAT) : ¬ NEXPSubsetPPoly := by
  intro hsub
  obtain ⟨c, L, hL, hnot⟩ := hier
  exact hnot (speedup fast (ewl hsub) c L hL)

/-- The contrapositive: `NEXP ⊆ P/poly` rules out fast circuit
satisfiability. -/
theorem not_fastCircuitSAT_of_nexpSubsetPPoly (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (hsub : NEXPSubsetPPoly) :
    ¬ FastCircuitSAT :=
  fun fast => williams_method hier ewl speedup fast hsub

/-- Idea 16 states the hierarchy theorem for every gap `(n+1)^k` with
`k ≥ 3`; the method needs one gap. -/
theorem nTimeHierarchy_of_idea16 (h : Idea16.NTimeHierarchy) : NTimeHierarchy := by
  obtain ⟨L, hL, hnot⟩ := h 3 (Nat.le_refl 3)
  exact ⟨3, L, (inNTIME_iff_idea16 _ _).mpr hL,
    fun h' => hnot ((inNTIME_iff_idea16 _ _).mp h')⟩

/-- The method with Idea 16's form of the hierarchy theorem. -/
theorem williams_method_idea16 (hier : Idea16.NTimeHierarchy) (ewl : EasyWitnessLemma)
    (speedup : WilliamsSpeedup) (fast : FastCircuitSAT) : ¬ NEXPSubsetPPoly :=
  williams_method (nTimeHierarchy_of_idea16 hier) ewl speedup fast

/-! ## Discharging the diagonal part of the hierarchy theorem

Žák's lazy diagonalisation. The diagonal language `D` copies `L` one step
ahead on the unary inputs `1^l, …, 1^{u-1}` and flips `L(1^l)` at `1^u`. If
`L = D` the copies chain `D(1^l) = D(1^u)`, and the flip gives
`D(1^u) = !D(1^l)`. -/

/-- The unary word `1^n`. -/
def unary (n : Nat) : Word := List.replicate n true

theorem lazy_chain (D L : Language) (l : Nat)
    (hin : ∀ n, l ≤ n → n < l + j → D (unary n) = L (unary (n + 1)))
    (heq : L = D) : D (unary l) = D (unary (l + j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ih (fun n h1 h2 => hin n h1 (by omega))]
    have := hin (l + j) (by omega) (by omega)
    rw [this, heq]
    rfl

/-- **Lazy diagonalisation (Žák 1983).** -/
theorem lazy_diagonal (D L : Language) (l u : Nat) (hlu : l < u)
    (hin : ∀ n, l ≤ n → n < u → D (unary n) = L (unary (n + 1)))
    (hend : D (unary u) = !L (unary l)) : L ≠ D := by
  intro heq
  have hchain := lazy_chain (j := u - l) D L l
    (fun n h1 h2 => hin n h1 (by omega)) heq
  rw [show l + (u - l) = u by omega, hend, heq] at hchain
  cases h : D (unary l) <;> rw [h] at hchain <;> cases hchain

/-- What remains of the hierarchy theorem: a language `D` in `NTIME(T)` that
follows every language of `NTIME(T')` lazily on some interval. Žák's machine
simulates the verifier of the `i`-th language on `1^{n+1}` nondeterministically
inside the interval and decides `L(1^l)` by exhaustive search at the end. -/
def LazyDiagonalSimulation (T T' : Nat → Nat) : Prop :=
  ∃ D : Language, InNTIME T D ∧ ∀ L : Language, InNTIME T' L →
    ∃ l u, l < u ∧ (∀ n, l ≤ n → n < u → D (unary n) = L (unary (n + 1))) ∧
      D (unary u) = !L (unary l)

theorem not_inNTIME_of_lazyDiagonal {T' : Nat → Nat} {D : Language}
    (hD : ∀ L : Language, InNTIME T' L →
      ∃ l u, l < u ∧ (∀ n, l ≤ n → n < u → D (unary n) = L (unary (n + 1))) ∧
        D (unary u) = !L (unary l)) : ¬ InNTIME T' D := by
  intro h
  obtain ⟨l, u, hlu, hin, hend⟩ := hD D h
  exact lazy_diagonal D D l u hlu hin hend rfl

/-- The hierarchy theorem from the simulation statement: the diagonal
argument is proved here. -/
theorem nTimeHierarchy_of_lazyDiagonal (c : Nat)
    (h : LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ c)) :
    NTimeHierarchy := by
  obtain ⟨D, hD, hlazy⟩ := h
  exact ⟨c, D, hD, not_inNTIME_of_lazyDiagonal hlazy⟩

/-- The method with the hierarchy theorem replaced by the simulation
statement. -/
theorem williams_method_lazy (c : Nat)
    (sim : LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ c))
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (fast : FastCircuitSAT) :
    ¬ NEXPSubsetPPoly :=
  williams_method (nTimeHierarchy_of_lazyDiagonal c sim) ewl speedup fast

/-- Idea 16's form of the hierarchy theorem from the simulation statement, one
gap `k ≥ 3` at a time: the diagonal argument is the same. -/
theorem idea16_nTimeHierarchy_of_lazyDiagonal
    (h : ∀ k, 3 ≤ k → LazyDiagonalSimulation (fun n => 2 ^ n) (fun n => 2 ^ n / (n + 1) ^ k)) :
    Idea16.NTimeHierarchy := by
  intro k hk
  obtain ⟨D, hD, hlazy⟩ := h k hk
  exact ⟨D, (inNTIME_iff_idea16 _ _).mp hD,
    fun h' => not_inNTIME_of_lazyDiagonal hlazy ((inNTIME_iff_idea16 _ _).mpr h')⟩

/-! ## The obligation and the separation question

`P = NP` gives a polynomial-time decider for circuit satisfiability, and a
polynomial in the encoding length of a circuit with `(n+1)^k` gates is below
`2^n / (n+1)^c` from some `n` on. So `P = NP` implies the obligation:
refuting `FastCircuitSAT` would prove `P ≠ NP`, and proving it gives
`NEXP ⊄ P/poly` through `williams_method`. -/

/-- `n + 1 ≤ r · 2^{⌊n/r⌋}`. -/
theorem succ_le_mul_two_pow_div (r n : Nat) (hr : 0 < r) : n + 1 ≤ r * 2 ^ (n / r) := by
  have h1 := Nat.div_add_mod n r
  have h2 := Nat.mod_lt n hr
  have h3 : n / r + 1 ≤ 2 ^ (n / r) := Nat.lt_two_pow_self
  calc n + 1 ≤ r * (n / r + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ r * 2 ^ (n / r) := Nat.mul_le_mul_left r h3

/-- A polynomial is below `2^n` from some `n` on. -/
theorem poly_le_two_pow (a e : Nat) : ∃ N, ∀ n, N ≤ n → a * (n + 1) ^ e ≤ 2 ^ n := by
  refine ⟨2 * (a * (2 * e + 2) ^ e), fun n hn => ?_⟩
  have hq : n / (2 * e + 2) * e ≤ n / 2 := by
    have h := Nat.div_mul_le_self n (2 * e + 2)
    have : n / (2 * e + 2) * (2 * e + 2) = 2 * (n / (2 * e + 2) * e) + 2 * (n / (2 * e + 2)) := by
      rw [Nat.mul_add, Nat.mul_left_comm]; omega
    omega
  have hK : a * (2 * e + 2) ^ e ≤ 2 ^ (n / 2) :=
    Nat.le_trans (by omega) (Nat.le_of_lt Nat.lt_two_pow_self)
  calc a * (n + 1) ^ e ≤ a * ((2 * e + 2) * 2 ^ (n / (2 * e + 2))) ^ e :=
        Nat.mul_le_mul_left a
          (Nat.pow_le_pow_left (succ_le_mul_two_pow_div (2 * e + 2) n (by omega)) e)
    _ = a * (2 * e + 2) ^ e * 2 ^ (n / (2 * e + 2) * e) := by
        rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
    _ ≤ 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_le_mul hK (Nat.pow_le_pow_right (by decide) hq)
    _ = 2 ^ (n / 2 + n / 2) := by rw [← Nat.pow_add]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)

theorem length_encNat (i : Nat) : (encNat i).length = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [encNat, ih]

/-- In a well-formed circuit every gate reads a wire below `N + |C|`. -/
theorem wfFrom_bound : ∀ (N : Nat) (C : Circuit), WFfrom N C →
    ∀ g ∈ C, g.1 < N + C.length ∧ g.2 < N + C.length
  | _, [], _, g, hg => by simp at hg
  | N, (i, j) :: C, ⟨hi, hj, hC⟩, g, hg => by
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [List.length_cons]; omega
    · have := wfFrom_bound (N + 1) C hC g hg
      simp only [List.length_cons]; omega

theorem length_encList_gates (B : Nat) : ∀ C : Circuit, (∀ g ∈ C, g.1 < B ∧ g.2 < B) →
    (encList encGate C).length ≤ 1 + C.length * (2 * B + 1)
  | [], _ => by simp [encList]
  | g :: C, h => by
    have hg := h g (by simp)
    have ih := length_encList_gates B C (fun g' hg' => h g' (by simp [hg']))
    simp only [encList, encGate, List.length_cons, List.length_append, length_encNat, Nat.add_mul,
      Nat.one_mul]
    omega

/-- A well-formed circuit with at most `(n+1)^k` gates has an encoding of
polynomial length in `n`. -/
theorem encCircuit_length_le (n k : Nat) (C : Circuit) (hwf : WF n C)
    (hs : C.length ≤ (n + 1) ^ k) :
    (encCircuit n C).length + 1 ≤ 8 * (n + 1) ^ (k + 1 + (k + 1)) := by
  have hE := length_encList_gates (n + C.length) C (wfFrom_bound n C hwf)
  have hn1 : n + 1 ≤ (n + 1) ^ (k + 1) :=
    Nat.le_trans (Nat.le_of_eq (Nat.pow_one _).symm) (Nat.pow_le_pow_right (by omega) (by omega))
  have hC1 : C.length ≤ (n + 1) ^ (k + 1) :=
    Nat.le_trans hs (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Nat.pow_add]
  simp only [encCircuit, List.length_append, length_encNat]
  generalize (n + 1) ^ (k + 1) = Q at hn1 hC1 ⊢
  have hm : C.length * (2 * (n + C.length) + 1) ≤ Q * (4 * Q + 1) :=
    Nat.mul_le_mul hC1 (by omega)
  have hQQ : Q ≤ Q * Q := Nat.le_mul_self Q
  have : Q * (4 * Q + 1) = 4 * (Q * Q) + Q := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  omega

/-- A polynomial-time decider for circuit satisfiability meets the
obligation. -/
theorem fastCircuitSAT_of_inP (h : InP CircuitSAT) : FastCircuitSAT := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP CircuitSAT).mpr h
  intro k
  refine ⟨m, fun c => ?_⟩
  obtain ⟨N, hN⟩ := poly_le_two_pow (p.coefficient * 8 ^ p.degree)
    ((k + 1 + (k + 1)) * p.degree + c)
  refine ⟨N, fun n hn C hwf hsize => ?_⟩
  obtain ⟨t, b, ht, hr, hb⟩ := hm (encCircuit n C)
  refine ⟨t, b, ?_, hr, ?_⟩
  · have hlen := encCircuit_length_le n k C hwf hsize
    calc t * (n + 1) ^ c ≤ p.eval (encCircuit n C).length * (n + 1) ^ c :=
          Nat.mul_le_mul_right _ ht
      _ ≤ p.coefficient * (8 * (n + 1) ^ (k + 1 + (k + 1))) ^ p.degree * (n + 1) ^ c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _))
      _ = p.coefficient * 8 ^ p.degree * (n + 1) ^ ((k + 1 + (k + 1)) * p.degree + c) := by
          rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc,
            Nat.mul_assoc]
      _ ≤ 2 ^ n := hN n hn
  · rw [hb, circuitSAT_encode]
    exact ⟨fun h => h.2, fun h => ⟨hwf, h⟩⟩

/-- `P = NP` implies the obligation. -/
theorem fastCircuitSAT_of_pEqualsNP (mem : CircuitSATInNP) (h : PEqualsNP) : FastCircuitSAT :=
  fastCircuitSAT_of_inP (h CircuitSAT mem)

/-- A polynomial-time SAT decider implies the obligation, given Cook–Levin. -/
theorem fastCircuitSAT_of_inP_sat (hard : SATHard) (mem : CircuitSATInNP) (h : InP SAT) :
    FastCircuitSAT :=
  fastCircuitSAT_of_pEqualsNP mem (pEqualsNP_of_inP_sat hard h)

/-- **Bridge.** Refuting the obligation proves `P ≠ NP`. -/
theorem pNotEqualsNP_of_not_fastCircuitSAT (mem : CircuitSATInNP) (h : ¬ FastCircuitSAT) :
    PNotEqualsNP :=
  fun hEq => h (fastCircuitSAT_of_pEqualsNP mem hEq)

/-- `NEXP ⊆ P/poly` would prove `P ≠ NP`, given the known theorems. -/
theorem pNotEqualsNP_of_nexpSubsetPPoly (mem : CircuitSATInNP) (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (hsub : NEXPSubsetPPoly) :
    PNotEqualsNP :=
  pNotEqualsNP_of_not_fastCircuitSAT mem (not_fastCircuitSAT_of_nexpSubsetPPoly hier ewl speedup hsub)

/-- `P = NP` would refute `NEXP ⊆ P/poly`, given the known theorems. -/
theorem not_nexpSubsetPPoly_of_pEqualsNP (mem : CircuitSATInNP) (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (h : PEqualsNP) :
    ¬ NEXPSubsetPPoly :=
  williams_method hier ewl speedup (fastCircuitSAT_of_pEqualsNP mem h)

end Issue532.Idea41
