import proofs.experiments.issue532.lean.Idea41

/-!
# Issue 10: the Williams route to `NP ⊈ P`, over the shared model

PR #43's first `WilliamsFramework.lean` did not compile and its costs were
free labels. `proofs/experiments/WilliamsFramework.lean` now keeps its path for
regression checks; this file carries the issue 10 target. Every cost below is a number
of `Complexity.Run` steps of a finite-table `Complexity.Machine`. Circuits are
the shared `Issue532.Circuits.Circuit`: a gate list whose length is the size
and whose semantics is `output`. The algorithm-to-lower-bound direction is
Idea 41 (`Issue532.Idea41.williams_method`).

The file proves:

* `NP ⊈ P` is the statement `Complexity.PNotEqualsNP`, and it is equivalent to
  the two classes differing because `P ⊆ NP` is proved (`pSubsetNP`);
* reproductions of the PR #43 defects: free cost labels, sizes unrelated to
  semantics, and the `2^n - n^δ` bound with `δ : Nat`;
* negative tests: no run costs zero steps, no one-step machine decides circuit
  satisfiability, and malformed circuits are rejected;
* the Williams budget `2^n / (n+1)^c` is not polynomial, so the claimed
  circularity (a fast algorithm would already give `P = NP`) fails;
* the diagonal over "polynomially many circuits" fails: on every input some
  three-gate constant circuit agrees with any chosen bit;
* the corrected bridges: `NP ⊄ P/poly` gives `NP ⊈ P` given `P ⊆ P/poly`, and
  Williams gives only `NEXP ⊄ P/poly`.

Nothing here asserts an unproved theorem. Known theorems are hypotheses. The
next ingredient to discharge is `CircuitSATInNP`, the circuit-evaluating
verifier; `satisfying_input_within_certBound` is its certificate-length half.
-/

namespace Issue10.NPNotSubsetP

open Complexity Issue532.Machines Issue532.Circuits Issue532.Idea41

/-! ## The target: `NP ⊈ P` -/

/-- `NP ⊈ P`: some language in NP is not in P. -/
def NPNotSubsetP : Prop := ¬ ∀ L : Language, InNP L → InP L

/-- The shared statement `PNotEqualsNP` is literally `NP ⊈ P`. -/
theorem npNotSubsetP_iff_pNotEqualsNP : NPNotSubsetP ↔ PNotEqualsNP := Iff.rfl

/-- Because `P ⊆ NP` is proved, `NP ⊈ P` says exactly that the classes differ. -/
theorem npNotSubsetP_iff_classes_differ :
    NPNotSubsetP ↔ ¬ ∀ L : Language, InP L ↔ InNP L := by
  constructor
  · intro h heq
    exact h fun L hL => (heq L).2 hL
  · intro h hsub
    exact h fun L => ⟨pSubsetNP L, hsub L⟩

/-- An explicit witness proves `NP ⊈ P`. -/
theorem npNotSubsetP_of_witness {L : Language} (hnp : InNP L) (hp : ¬ InP L) :
    NPNotSubsetP :=
  fun h => hp (h L hnp)

/-- With excluded middle, `NP ⊈ P` gives a witness. -/
theorem witness_of_npNotSubsetP (em : ∀ P : Prop, P ∨ ¬ P) (h : NPNotSubsetP) :
    ∃ L : Language, InNP L ∧ ¬ InP L := by
  cases em (∃ L : Language, InNP L ∧ ¬ InP L) with
  | inl hw => exact hw
  | inr hw =>
    exact absurd (fun L hL => (em (InP L)).elim id fun hp => absurd ⟨L, hL, hp⟩ hw) h

/-! ## Reproducing the PR #43 defects

The PR #43 model, restated with a Boolean predicate for the missing `Set`. -/

namespace Legacy

/-- Size, depth and semantics are independent fields. -/
structure Circuit where
  size : Nat
  depth : Nat
  numInputs : Nat
  compute : (Fin numInputs → Bool) → Bool

def ACC0 (C : Circuit) : Prop := C.depth ≤ 10

def PPoly (C : Circuit) : Prop := ∃ k : Nat, C.size ≤ C.numInputs ^ k

/-- The running time is a free function next to the answer. -/
structure SATAlgorithm where
  solve : Circuit → Bool
  timeComplexity : Nat → Nat

def IsFastSATAlgorithm (alg : SATAlgorithm) : Prop :=
  ∃ δ : Nat, δ > 0 ∧ ∀ n : Nat, alg.timeComplexity n ≤ 2 ^ n - n ^ δ

end Legacy

/-- Any function on any number of inputs is a zero-gate, depth-zero legacy
circuit in both classes: size and depth say nothing about `compute`. -/
theorem legacy_every_function_small (n : Nat) (f : (Fin n → Bool) → Bool) :
    Legacy.ACC0 ⟨0, 0, n, f⟩ ∧ Legacy.PPoly ⟨0, 0, n, f⟩ :=
  ⟨Nat.zero_le _, ⟨0, Nat.zero_le _⟩⟩

/-- Any legacy solver, whatever it computes, is "fast" once its cost label is
set to zero. -/
theorem legacy_zero_cost_is_fast (solve : Legacy.Circuit → Bool) :
    Legacy.IsFastSATAlgorithm ⟨solve, fun _ => 0⟩ :=
  ⟨1, by decide, fun _ => Nat.zero_le _⟩

/-- `2^n - n^δ` is not `2^(n - n^δ)`. -/
theorem legacy_bound_misread : 2 ^ 4 - 4 ^ 1 ≠ 2 ^ (4 - 4 ^ 1) := by decide

/-- With `δ : Nat`, the exponent `n - n^δ` truncates to zero for `δ ≥ 1`. -/
theorem legacy_exponent_collapses (δ n : Nat) (hδ : 1 ≤ δ) : 2 ^ (n - n ^ δ) = 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have h : n + 1 ≤ (n + 1) ^ δ := Nat.le_self_pow (by omega) _
    rw [Nat.sub_eq_zero_of_le h, Nat.pow_zero]

/-- The legacy bound `2^n - n^δ` saves only a polynomial amount. It breaks the
Williams budget `t · (n+1) ≤ 2^n` of `FastCircuitSAT` at `c = 1` on
arbitrarily large lengths. -/
theorem legacy_bound_misses_budget (δ n₀ : Nat) :
    ∃ n, n₀ ≤ n ∧ 2 ^ n < (2 ^ n - n ^ δ) * (n + 1) ^ 1 := by
  obtain ⟨N, hN⟩ := poly_le_two_pow 2 δ
  refine ⟨n₀ + N + 2, by omega, ?_⟩
  have hb := hN (n₀ + N + 2) (by omega)
  have hp : (n₀ + N + 2) ^ δ ≤ (n₀ + N + 2 + 1) ^ δ := Nat.pow_le_pow_left (by omega) δ
  have hpos : 0 < 2 ^ (n₀ + N + 2) := Nat.two_pow_pos _
  rw [Nat.pow_one]
  calc 2 ^ (n₀ + N + 2) < (2 ^ (n₀ + N + 2) - (n₀ + N + 2) ^ δ) * 3 := by omega
    _ ≤ (2 ^ (n₀ + N + 2) - (n₀ + N + 2) ^ δ) * (n₀ + N + 2 + 1) :=
      Nat.mul_le_mul_left _ (by omega)

/-! ## Negative tests for the shared model -/

/-- No run costs zero steps. -/
theorem run_pos {m : Machine} {c : Config} {t : Nat} {b : Bool} (h : Run m c t b) : 0 < t := by
  cases h with
  | halt _ => decide
  | next _ _ => omega

/-- A one-step run is a halting instruction. -/
theorem step_of_run_one {m : Machine} {c : Config} {t : Nat} {b : Bool}
    (h : Run m c t b) (ht : t = 1) : step m c = .inl b := by
  cases h with
  | halt hs => exact hs
  | next _ hr => have := run_pos hr; omega

/-- A halting step reads only the state and the scanned symbol. -/
theorem step_halt_congr {m : Machine} {c c' : Config} {b : Bool}
    (hs : c.state = c'.state) (hh : c.head = c'.head) (h : step m c = .inl b) :
    step m c' = .inl b := by
  unfold step at h ⊢
  rw [← hs, ← hh]
  cases hi : m.instruction c.state c.head with
  | halt b' => rw [hi] at h; exact h
  | move q w d => rw [hi] at h; cases h

/-- The constant-true circuit on one input. -/
def oneTrue : Circuit := [(0, 0), (0, 1)]

/-- The constant-false circuit on one input. -/
def oneFalse : Circuit := [(0, 0), (0, 1), (2, 2)]

theorem wf_oneTrue : WF 1 oneTrue := by simp [WF, WFfrom, oneTrue]

theorem wf_oneFalse : WF 1 oneFalse := by simp [WF, WFfrom, oneFalse]

theorem satisfiable_oneTrue : CircuitSatisfiable 1 oneTrue := ⟨[false], rfl, rfl⟩

theorem unsatisfiable_oneFalse : ¬ CircuitSatisfiable 1 oneFalse := by
  rintro ⟨x, hx, ho⟩
  match x, hx with
  | [false], _ => exact absurd ho (by decide)
  | [true], _ => exact absurd ho (by decide)

/-- No machine decides satisfiability of well-formed circuits in one step:
`oneTrue` and `oneFalse` start with the same state and scanned symbol. -/
theorem no_one_step_circuitSAT (m : Machine) :
    ¬ ∀ n C, WF n C → ∃ b, Run m (initial (encCircuit n C)) 1 b ∧
      (b = true ↔ CircuitSatisfiable n C) := by
  intro h
  obtain ⟨b, hr, hb⟩ := h 1 oneTrue wf_oneTrue
  obtain ⟨b', hr', hb'⟩ := h 1 oneFalse wf_oneFalse
  have hs := step_halt_congr (c := initial (encCircuit 1 oneTrue))
    (c' := initial (encCircuit 1 oneFalse)) rfl rfl
    (step_of_run_one hr rfl)
  rw [step_of_run_one hr' rfl] at hs
  cases hs
  exact unsatisfiable_oneFalse (hb'.1 (hb.2 satisfiable_oneTrue))

/-- A gate that reads a wire that does not exist yet is malformed. -/
theorem malformed_forward_wire : ¬ WF 1 [(0, 1)] := by simp [WF, WFfrom]

/-- A gate on zero inputs is malformed. -/
theorem malformed_no_inputs : ¬ WF 0 [(0, 0)] := by simp [WF, WFfrom]

/-- The malformed circuit `[(0,1)]` outputs `true`, yet `CircuitSAT` rejects it. -/
theorem malformed_rejected :
    CircuitSatisfiable 1 [(0, 1)] ∧ CircuitSAT (encCircuit 1 [(0, 1)]) = false := by
  refine ⟨⟨[false], rfl, rfl⟩, ?_⟩
  cases h : CircuitSAT (encCircuit 1 [(0, 1)]) with
  | false => rfl
  | true => exact absurd ((circuitSAT_encode 1 [(0, 1)]).1 h).1 malformed_forward_wire

/-! ## The Williams budget is not polynomial -/

/-- `2^n / (n+1)^c` is not polynomially bounded. A `FastCircuitSAT` machine
may run in superpolynomial time, so meeting the obligation does not require
`P = NP`; conversely `fastCircuitSAT_of_inP` shows `P`-time is fast enough. -/
theorem williams_budget_not_polynomial (c : Nat) :
    ¬ PolynomiallyBounded (fun n => 2 ^ n / (n + 1) ^ c) := by
  rintro ⟨a, k, h⟩
  obtain ⟨N, hN⟩ := poly_le_two_pow (2 * (a + 1)) (k + c)
  have hq : 0 < (N + 1) ^ c := Nat.pow_pos (by omega)
  have hk : 1 ≤ (N + 1) ^ k := Nat.pow_pos (by omega)
  have hlt : 2 ^ N < (a * (N + 1) ^ k + 1) * (N + 1) ^ c :=
    (Nat.div_lt_iff_lt_mul hq).1 (Nat.lt_succ_of_le (h N))
  have hle : (a * (N + 1) ^ k + 1) * (N + 1) ^ c ≤ (a + 1) * (N + 1) ^ (k + c) := by
    rw [Nat.pow_add, ← Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hb := hN N (Nat.le_refl N)
  rw [Nat.mul_assoc] at hb
  omega

/-! ## The enumeration diagonal fails -/

/-- On every input of positive length, for every bit, a well-formed circuit
with at most three gates outputs that bit. A bit that differs from every
enumerated circuit therefore does not exist once the two constant circuits
are enumerated. -/
theorem constant_circuit_agrees (x : Word) (hx : 0 < x.length) (b : Bool) :
    ∃ C : Circuit, WF x.length C ∧ C.length ≤ 3 ∧ output x C = b := by
  cases b
  · refine ⟨[(0, 0), (0, x.length), (x.length + 1, x.length + 1)], ?_, by simp,
      output_const_false x hx⟩
    simp [WF, WFfrom]; omega
  · refine ⟨[(0, 0), (0, x.length)], ?_, by simp, output_const_true x hx⟩
    simp [WF, WFfrom]; omega

theorem no_bit_differs_from_all_circuits (x : Word) (hx : 0 < x.length) (b : Bool) :
    ¬ ∀ C : Circuit, WF x.length C → C.length ≤ 3 → output x C ≠ b := by
  intro h
  obtain ⟨C, hw, hl, ho⟩ := constant_circuit_agrees x hx b
  exact h C hw hl ho

/-! ## The corrected bridges -/

/-- `NP ⊆ P/poly`. -/
def NPSubsetPPoly : Prop := ∀ L : Language, InNP L → InPPoly L

/-- The PR #43 bridge using the proved inclusion: `NP ⊄ P/poly`
gives `NP ⊈ P` by the theorem `pSubsetPPoly`. -/
theorem npNotSubsetP_of_not_npSubsetPPoly (h : ¬ NPSubsetPPoly) :
    NPNotSubsetP :=
  fun hsub => h fun L hL => pSubsetPPoly L (hsub L hL)

/-- Williams' method, stated for `NEXP`: this is the lower bound it yields,
not `NP ⊄ P/poly`. -/
theorem williams_nexp_lower_bound (hier : NTimeHierarchy) (ewl : EasyWitnessLemma)
    (speedup : WilliamsSpeedup) (fast : FastCircuitSAT) : ¬ NEXPSubsetPPoly :=
  williams_method hier ewl speedup fast

/-- `NEXP ⊄ P/poly` also follows from `P = NP` under the same theorems, so it
cannot by itself give `NP ⊈ P`. -/
theorem nexp_lower_bound_of_pEqualsNP (mem : CircuitSATInNP) (hier : NTimeHierarchy)
    (ewl : EasyWitnessLemma) (speedup : WilliamsSpeedup) (h : PEqualsNP) :
    ¬ NEXPSubsetPPoly :=
  not_nexpSubsetPPoly_of_pEqualsNP mem hier ewl speedup h

/-- The route that does reach `NP ⊈ P`: refute the fast algorithm itself. -/
theorem npNotSubsetP_of_not_fastCircuitSAT (mem : CircuitSATInNP) (h : ¬ FastCircuitSAT) :
    NPNotSubsetP :=
  pNotEqualsNP_of_not_fastCircuitSAT mem h

/-! ## The next ingredient: `CircuitSATInNP`

A verifier for `CircuitSAT` takes a satisfying input as certificate. The
certificate is short: it has `n` bits and the encoding starts with `n + 1`
bits. The remaining part is the evaluating `Machine` and its polynomial
`Run` bound. -/

theorem satisfying_input_within_certBound (n : Nat) (C : Circuit)
    (h : CircuitSatisfiable n C) :
    ∃ x : Word, x.length ≤ Polynomial.eval ⟨1, 1⟩ (encCircuit n C).length ∧
      output x C = true := by
  obtain ⟨x, hx, ho⟩ := h
  refine ⟨x, ?_, ho⟩
  simp only [Polynomial.eval, encCircuit, List.length_append, length_encNat, Nat.pow_one,
    Nat.one_mul]
  omega

end Issue10.NPNotSubsetP
