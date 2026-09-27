import proofs.experiments.issue532.lean.Machines
import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue #532, Idea 39: proof-system scope (lower bounds and p-simulation)

Abstract Cook–Reckhow setting: a proof system over formulas `F` is a relation
`Proves : Proof → F → Prop` with a size function `size : Proof → Nat`.
Polynomials are pairs `⟨c, k⟩` evaluated as `c * (n + 1) ^ k`, as in the
repository's `proofs/complexity` library.

Abstract results (for arbitrary formula and proof types):

* `poly_comp_bound`: `q (p n) ≤ (q.comp p) n` for an explicit polynomial `q.comp p`.
* `lower_bound_transfer_quant`, `superpoly_transfer`: lower bounds transfer
  **downward** along p-simulation. If `S1` p-simulates `S2` and `S1` has a
  superpolynomial lower bound, so does `S2`. The bound for `S2` is computed
  through `q.comp p`.
* `poly_bounded_transfer`: dually, short proofs transfer **upward**.
* `psim_refl`, `psim_trans`: p-simulation is a preorder (with explicit composed
  polynomial).
* `weak_lb_strong_short`: general countermodel. For every tautology predicate with
  formulas of unbounded size, there are two sound and complete systems, `weak`
  and `strong`. `strong` p-simulates `weak`, `weak` has a superpolynomial lower
  bound, and `strong` is polynomially bounded. So a lower bound for a weak system
  (resolution, say) says nothing about stronger systems.
* `SuperpolyAllSystemsFor` (a schema over a class of systems) and
  `optimal_system_reduces`: if a class has a system p-simulating all its
  members, the schema for the class is equivalent to a lower bound for that one
  system.

Machine part (shared model of `Issue532.Machines`):

* `CRSystem L`: a Cook–Reckhow proof system for a language `L` is a
  `Complexity.VerifierProgram` with a polynomial clock, sound and complete for
  `L`; `toSystem` views it as an abstract system over words.
* `TAUT := complement SAT` (the formulas with no satisfying assignment, i.e. the
  negations of tautologies, under the shared CNF encoding).
* The open obligation `AllTautSystemsSuperpolynomial`: every Cook–Reckhow system
  for `TAUT` has a superpolynomial lower bound.
* Proved: a polynomially bounded system puts its language in NP
  (`inNP_of_crPolyBounded`); every language in P has one
  (`crPolyBounded_of_inP`); hence `pNotEqualsNP_of_allTautSystemsSuperpolynomial`
  (from SAT ∈ NP alone). `SATInNP` is proved in `SATVerifier.lean`
  (`SATVerifier.satInNP`), so `pNotEqualsNP_of_allTautSystemsSuperpolynomial'`
  and `npNeCoNP_of_not_inNP_taut'` drop that premise.  With the named known theorem `CookReckhow`
  (obligation ↔ NP ≠ coNP), `pNotEqualsNP_via_cookReckhow` concludes through
  `pNotEqualsNP_of_npNeCoNP`.
* Non-vacuity: the schema `AllCRSystemsSuperpolynomialFor` fails for the
  constant-false language and holds for a language with no Cook–Reckhow system
  at all (Cantor over encoded verifiers).

Verdict: correct tool, insufficient alone. The obligation is equivalent to
`NP ≠ coNP` (Cook–Reckhow 1979; cited as a named hypothesis, not formalized),
which is at least as hard as P ≠ NP.
-/
namespace Issue532.Idea39

/-- Old countermodel: a weak system with no proofs inside a strong system with one. -/
theorem tested :
    ∃ weak strong : Bool → Prop,
      (∀ proof, weak proof → strong proof) ∧
      (∀ proof, ¬ weak proof) ∧ (∃ proof, strong proof) := by
  refine ⟨(fun _ => False), (fun _ => True), ?_, ?_, ?_⟩
  · intro _ impossible
    exact False.elim impossible
  · intro _ impossible
    exact impossible
  · exact ⟨false, True.intro⟩

/-! ## Polynomials -/

/-- A polynomial bound `c * (n + 1) ^ k`. -/
structure Poly where
  c : Nat
  k : Nat

def Poly.eval (p : Poly) (n : Nat) : Nat := p.c * (n + 1) ^ p.k

/-- A polynomial bounding the composition `q ∘ p`. -/
def Poly.comp (q p : Poly) : Poly := ⟨q.c * (p.c + 1) ^ q.k, p.k * q.k⟩

/-- Polynomial bounds are monotone. -/
theorem poly_mono (p : Poly) {m n : Nat} (h : m ≤ n) : p.eval m ≤ p.eval n :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **Composition lemma.** `q (p n) ≤ (q.comp p) n`. -/
theorem poly_comp_bound (q p : Poly) (n : Nat) : q.eval (p.eval n) ≤ (q.comp p).eval n := by
  unfold Poly.eval Poly.comp
  have hx : 1 ≤ (n + 1) ^ p.k := Nat.pow_pos (Nat.succ_pos n)
  have h1 : p.c * (n + 1) ^ p.k + 1 ≤ (p.c + 1) * (n + 1) ^ p.k := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (p.c * (n + 1) ^ p.k + 1) ^ q.k ≤ ((p.c + 1) * (n + 1) ^ p.k) ^ q.k :=
    Nat.pow_le_pow_left h1 _
  rw [Nat.mul_pow, ← Nat.pow_mul] at h2
  calc q.c * (p.c * (n + 1) ^ p.k + 1) ^ q.k
      ≤ q.c * ((p.c + 1) ^ q.k * (n + 1) ^ (p.k * q.k)) := Nat.mul_le_mul_left _ h2
    _ = q.c * (p.c + 1) ^ q.k * (n + 1) ^ (p.k * q.k) := (Nat.mul_assoc _ _ _).symm

/-! ## Proof systems and p-simulation -/

/-- An abstract proof system over formulas `F`. -/
structure System (F : Type) where
  Proof : Type
  Proves : Proof → F → Prop
  size : Proof → Nat

variable {F : Type}

/-- `S1` p-simulates `S2` with bound `q`: every `S2`-proof of `φ` converts to an
`S1`-proof of `φ` of size at most `q (size)`. -/
def PSim (S1 S2 : System F) (q : Poly) : Prop :=
  ∀ π2 φ, S2.Proves π2 φ → ∃ π1, S1.Proves π1 φ ∧ S1.size π1 ≤ q.eval (S2.size π2)

/-- Every `S`-proof of `φs n` has size at least `L n`. -/
def LowerBound (S : System F) (φs : Nat → F) (L : Nat → Nat) : Prop :=
  ∀ n π, S.Proves π (φs n) → L n ≤ S.size π

/-- Every tautology has an `S`-proof of size at most `p (fsize φ)`. -/
def PolyBounded (S : System F) (taut : F → Prop) (fsize : F → Nat) (p : Poly) : Prop :=
  ∀ φ, taut φ → ∃ π, S.Proves π φ ∧ S.size π ≤ p.eval (fsize φ)

/-- Superpolynomial lower bound: for every polynomial some tautology has only
proofs larger than that polynomial of its size. -/
def SuperpolyLB (S : System F) (taut : F → Prop) (fsize : F → Nat) : Prop :=
  ∀ p : Poly, ∃ φ, taut φ ∧ ∀ π, S.Proves π φ → p.eval (fsize φ) < S.size π

/-- A superpolynomial lower bound rules out every polynomial bound. -/
theorem superpoly_not_bounded (S : System F) (taut : F → Prop) (fsize : F → Nat)
    (h : SuperpolyLB S taut fsize) (p : Poly) : ¬ PolyBounded S taut fsize p := by
  intro hb
  obtain ⟨φ, hφ, hbig⟩ := h p
  obtain ⟨π, hπ, hs⟩ := hb φ hφ
  have := hbig π hπ
  omega

/-- **Quantitative transfer.** If `S1` p-simulates `S2` via `q` and every `S1`-proof of
`φs n` has size `≥ L n`, then every `S2`-proof `π2` of `φs n` satisfies
`L n ≤ q (size π2)`. -/
theorem lower_bound_transfer_quant (S1 S2 : System F) (q : Poly) (φs : Nat → F)
    (L : Nat → Nat) (hsim : PSim S1 S2 q) (hlb : LowerBound S1 φs L) :
    ∀ n π2, S2.Proves π2 (φs n) → L n ≤ q.eval (S2.size π2) := by
  intro n π2 h2
  obtain ⟨π1, h1, hs⟩ := hsim π2 (φs n) h2
  exact Nat.le_trans (hlb n π1 h1) hs

/-- **Lower bounds transfer downward.** If `S1` p-simulates `S2` and `S1` has a
superpolynomial lower bound, so does `S2`. For the target polynomial `p` one uses the
`S1` lower bound against `q.comp p`. -/
theorem superpoly_transfer (S1 S2 : System F) (q : Poly) (taut : F → Prop) (fsize : F → Nat)
    (hsim : PSim S1 S2 q) (hlb : SuperpolyLB S1 taut fsize) : SuperpolyLB S2 taut fsize := by
  intro p
  obtain ⟨φ, hφ, hbig⟩ := hlb (q.comp p)
  refine ⟨φ, hφ, fun π2 h2 => ?_⟩
  rcases Nat.lt_or_ge (p.eval (fsize φ)) (S2.size π2) with hlt | hge
  · exact hlt
  · exfalso
    obtain ⟨π1, h1, hs⟩ := hsim π2 φ h2
    have a := hbig π1 h1
    have b := poly_mono q hge
    have c := poly_comp_bound q p (fsize φ)
    omega

/-- **Short proofs transfer upward.** If `S1` p-simulates `S2` via `q` and `S2` is
polynomially bounded by `p`, then `S1` is polynomially bounded by `q.comp p`. -/
theorem poly_bounded_transfer (S1 S2 : System F) (q p : Poly) (taut : F → Prop)
    (fsize : F → Nat) (hsim : PSim S1 S2 q) (hb : PolyBounded S2 taut fsize p) :
    PolyBounded S1 taut fsize (q.comp p) := by
  intro φ hφ
  obtain ⟨π2, h2, hs2⟩ := hb φ hφ
  obtain ⟨π1, h1, hs1⟩ := hsim π2 φ h2
  exact ⟨π1, h1, Nat.le_trans hs1
    (Nat.le_trans (poly_mono q hs2) (poly_comp_bound q p (fsize φ)))⟩

/-- p-simulation is reflexive (bound `n + 1`). -/
theorem psim_refl (S : System F) : PSim S S ⟨1, 1⟩ := by
  intro π φ h
  refine ⟨π, h, ?_⟩
  simp [Poly.eval]

/-- **Transitivity.** If `S1` p-simulates `S2` via `q` and `S2` p-simulates `S3` via `r`,
then `S1` p-simulates `S3` via `q.comp r`. -/
theorem psim_trans (S1 S2 S3 : System F) (q r : Poly)
    (h12 : PSim S1 S2 q) (h23 : PSim S2 S3 r) : PSim S1 S3 (q.comp r) := by
  intro π3 φ h3
  obtain ⟨π2, h2, hs2⟩ := h23 π3 φ h3
  obtain ⟨π1, h1, hs1⟩ := h12 π2 φ h2
  exact ⟨π1, h1, Nat.le_trans hs1
    (Nat.le_trans (poly_mono q hs2) (poly_comp_bound q r (S3.size π3)))⟩

/-! ## Growth: `c * (n + 1) ^ k < 2 ^ n` eventually -/

theorem succ_le_two_pow (q : Nat) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.pow_succ]; omega

theorem lt_two_pow_self (a : Nat) : a < 2 ^ a := by
  have := succ_le_two_pow a
  omega

theorem linear_lt_exp (a q : Nat) (hq : 2 * a + 1 ≤ q) : a * (q + 1) < 2 ^ q := by
  obtain ⟨d, rfl⟩ : ∃ d, q = 2 * a + 1 + d := ⟨q - (2 * a + 1), by omega⟩
  induction d with
  | zero =>
    have h1 : a + 1 ≤ 2 ^ a := succ_le_two_pow a
    have h2 : a < 2 ^ a := lt_two_pow_self a
    have e : 2 ^ (2 * a + 1 + 0) = 2 ^ a * (2 * 2 ^ a) := by
      rw [show 2 * a + 1 + 0 = a + (a + 1) by omega, Nat.pow_add, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ a) 2]
    rw [e, show 2 * a + 1 + 0 + 1 = 2 * (a + 1) by omega]
    have h3 : 2 * (a + 1) ≤ 2 * 2 ^ a := by omega
    have hpos : 0 < 2 * 2 ^ a := by omega
    calc a * (2 * (a + 1)) ≤ a * (2 * 2 ^ a) := Nat.mul_le_mul_left a h3
      _ < 2 ^ a * (2 * 2 ^ a) := Nat.mul_lt_mul_of_pos_right h2 hpos
  | succ d ih =>
    have ih := ih (by omega)
    have ha : a ≤ a * (2 * a + 1 + d + 1) := Nat.le_mul_of_pos_right a (by omega)
    rw [show 2 * a + 1 + (d + 1) = (2 * a + 1 + d) + 1 by omega, Nat.pow_succ,
      Nat.mul_add, Nat.mul_one]
    omega

theorem dyadic_bracket (n : Nat) (hn : 1 ≤ n) : ∃ L, 2 ^ L ≤ n ∧ n < 2 ^ (L + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  induction d with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ d ih =>
    obtain ⟨L, h1, h2⟩ := ih (by omega)
    by_cases h : 1 + (d + 1) < 2 ^ (L + 1)
    · exact ⟨L, by omega, h⟩
    · refine ⟨L + 1, by omega, ?_⟩
      rw [Nat.pow_succ 2 (L + 1)]
      omega

/-- `c * (n + 1) ^ k < 2 ^ n` for all `n ≥ 2 ^ (2 * (c + k) + 1)`. -/
theorem exp_beats_poly (c k : Nat) :
    ∀ n, 2 ^ (2 * (c + k) + 1) ≤ n → c * (n + 1) ^ k < 2 ^ n := by
  intro n hn
  have hn1 : 1 ≤ n := Nat.le_trans (Nat.one_le_two_pow) hn
  obtain ⟨L, hL1, hL2⟩ := dyadic_bracket n hn1
  have hLbig : 2 * (c + k) + 1 ≤ L := by
    rcases Nat.lt_or_ge L (2 * (c + k) + 1) with hlt | hge
    · have : 2 ^ (L + 1) ≤ 2 ^ (2 * (c + k) + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hge
  have hlin : (c + k) * (L + 1) < 2 ^ L := linear_lt_exp (c + k) L hLbig
  have hsum : c + k * (L + 1) < n := by
    have : c + k * (L + 1) ≤ (c + k) * (L + 1) := by
      rw [Nat.add_mul]
      have : c ≤ c * (L + 1) := Nat.le_mul_of_pos_right c (by omega)
      omega
    omega
  have hbase : (n + 1) ^ k ≤ 2 ^ ((L + 1) * k) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by omega) k
  have hc : c < 2 ^ c := lt_two_pow_self c
  have hpos : 0 < 2 ^ ((L + 1) * k) := Nat.two_pow_pos _
  calc c * (n + 1) ^ k ≤ c * 2 ^ ((L + 1) * k) := Nat.mul_le_mul_left c hbase
    _ < 2 ^ c * 2 ^ ((L + 1) * k) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (c + (L + 1) * k) := (Nat.pow_add 2 c _).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)

/-! ## General countermodel: weak lower bounds, strong short proofs -/

/-- A sound and complete system whose proof of `φ` is `φ` itself, at cost `2 ^ fsize φ`. -/
def weakSys (taut : F → Prop) (fsize : F → Nat) : System F :=
  { Proof := F, Proves := fun π φ => π = φ ∧ taut φ, size := fun π => 2 ^ fsize π }

/-- The same proofs at cost `fsize φ`. -/
def strongSys (taut : F → Prop) (fsize : F → Nat) : System F :=
  { Proof := F, Proves := fun π φ => π = φ ∧ taut φ, size := fsize }

/-- Both systems are sound and complete for `taut`. -/
theorem sys_sound_complete (taut : F → Prop) (fsize : F → Nat) (φ : F) :
    (taut φ ↔ ∃ π, (weakSys taut fsize).Proves π φ) ∧
    (taut φ ↔ ∃ π, (strongSys taut fsize).Proves π φ) := by
  constructor
  · exact ⟨fun h => ⟨φ, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  · exact ⟨fun h => ⟨φ, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- **General countermodel.** For every tautology predicate with formulas of unbounded
size there are sound and complete systems `weak` and `strong` such that `strong`
p-simulates `weak` and `weak` has a superpolynomial lower bound, while `strong` is
polynomially bounded and has no superpolynomial lower bound. -/
theorem weak_lb_strong_short (taut : F → Prop) (fsize : F → Nat)
    (hunb : ∀ m, ∃ φ, taut φ ∧ m ≤ fsize φ) :
    SuperpolyLB (weakSys taut fsize) taut fsize ∧
    PolyBounded (strongSys taut fsize) taut fsize ⟨1, 1⟩ ∧
    ¬ SuperpolyLB (strongSys taut fsize) taut fsize ∧
    PSim (strongSys taut fsize) (weakSys taut fsize) ⟨1, 1⟩ := by
  have hb : PolyBounded (strongSys taut fsize) taut fsize ⟨1, 1⟩ := by
    intro φ hφ
    refine ⟨φ, ⟨rfl, hφ⟩, ?_⟩
    simp [strongSys, Poly.eval]
  refine ⟨?_, hb, fun h => superpoly_not_bounded _ taut fsize h ⟨1, 1⟩ hb, ?_⟩
  · intro p
    obtain ⟨φ, hφ, hm⟩ := hunb (2 ^ (2 * (p.c + p.k) + 1))
    refine ⟨φ, hφ, ?_⟩
    rintro π ⟨rfl, _⟩
    exact exp_beats_poly p.c p.k _ hm
  · rintro π φ ⟨rfl, hφ⟩
    refine ⟨π, ⟨rfl, hφ⟩, ?_⟩
    have := lt_two_pow_self (fsize π)
    simp only [strongSys, weakSys, Poly.eval, Nat.pow_one, Nat.one_mul]
    omega

/-! ## The obligation -/

/-- Schema over a class `C` of systems: every system in `C` has a
superpolynomial lower bound.  The machine instance for Cook–Reckhow systems
for `TAUT` is `AllTautSystemsSuperpolynomial` below. -/
def SuperpolyAllSystemsFor (C : System F → Prop) (taut : F → Prop) (fsize : F → Nat) : Prop :=
  ∀ S, C S → SuperpolyLB S taut fsize

/-- **Optimal systems reduce the obligation to one lower bound.** If `S ∈ C` p-simulates
every member of `C`, the obligation for `C` is equivalent to a superpolynomial lower
bound for `S`. -/
theorem optimal_system_reduces (C : System F → Prop) (taut : F → Prop) (fsize : F → Nat)
    (S : System F) (hS : C S) (hopt : ∀ T, C T → ∃ q, PSim S T q) :
    SuperpolyAllSystemsFor C taut fsize ↔ SuperpolyLB S taut fsize := by
  constructor
  · intro h
    exact h S hS
  · intro h T hT
    obtain ⟨q, hq⟩ := hopt T hT
    exact superpoly_transfer S T q taut fsize hq h

/-- A lower bound for one member of `C` does not give the obligation: a polynomially
bounded member refutes it. -/
theorem bounded_member_refutes (C : System F → Prop) (taut : F → Prop) (fsize : F → Nat)
    (S : System F) (hS : C S) (p : Poly) (hb : PolyBounded S taut fsize p) :
    ¬ SuperpolyAllSystemsFor C taut fsize :=
  fun h => superpoly_not_bounded S taut fsize (h S hS) p hb

/-- Check of the composition polynomial at `n = 2`. -/
example : (Poly.eval ⟨2, 1⟩ (Poly.eval ⟨1, 2⟩ 2)) ≤ (Poly.comp ⟨2, 1⟩ ⟨1, 2⟩).eval 2 := by decide

/-! ## Machine part: Cook–Reckhow systems for `TAUT` in the shared model -/

section MachinePart

open Complexity
open Issue532.Machines (SAT SATInNP complement InCoNP NPEqualsCoNP run_deterministic
  inP_of_decidesWithin polyDec_iff_inP inP_complement pNotEqualsNP_of_npNeCoNP
  inP_sat_of_pEqualsNP exists_language_not_in_family encMachine encMachine_injective)

/-- `TAUT` in the shared encoding: the complement of `SAT`.  A CNF word is in
`TAUT` exactly when its formula has no satisfying assignment, i.e. when the
negated formula is a tautology. -/
def TAUT : Language := complement SAT

/-- A Cook–Reckhow proof system for `L` in the shared machine model: a verifier
program that halts within the polynomial `timeBound` (in `|x| + |π| + 1`) on
every (input, proof) pair, accepts only members of `L`, and accepts every
member with some proof. -/
structure CRSystem (L : Language) where
  verifier : VerifierProgram
  timeBound : Polynomial
  halts : ∀ x π, ∃ t b, t ≤ verifier.timeLimit timeBound x π ∧ verifier.Run x π t b
  sound : ∀ x π t, verifier.Run x π t true → L x = true
  complete : ∀ x, L x = true → ∃ π t, verifier.Run x π t true

/-- The abstract system over words carried by a Cook–Reckhow system: proofs
are words, a proof proves `x` when the verifier accepts `(x, π)`, and the size
of a proof is its length. -/
def toSystem {L : Language} (P : CRSystem L) : System Word :=
  { Proof := Word, Proves := fun π x => ∃ t, P.verifier.Run x π t true, size := List.length }

/-- The class of abstract systems coming from Cook–Reckhow systems for `L`. -/
def CRClass (L : Language) : System Word → Prop := fun S => ∃ P : CRSystem L, toSystem P = S

/-- The membership predicate of a language. -/
def memberOf (L : Language) : Word → Prop := fun x => L x = true

/-- Polynomial boundedness of a Cook–Reckhow system (with the abstract
`PolyBounded` of this file, measured in the input length). -/
def CRPolyBounded {L : Language} (P : CRSystem L) : Prop :=
  ∃ p : Poly, PolyBounded (toSystem P) (memberOf L) List.length p

/-- A superpolynomial lower bound is exactly the failure of every polynomial
bound (for every abstract system; classical). -/
theorem superpolyLB_iff_forall_not_polyBounded (S : System F) (taut : F → Prop)
    (fsize : F → Nat) : SuperpolyLB S taut fsize ↔ ∀ p, ¬ PolyBounded S taut fsize p := by
  constructor
  · exact fun h p => superpoly_not_bounded S taut fsize h p
  · intro h p
    apply Classical.byContradiction
    intro hne
    apply h p
    intro φ hφ
    apply Classical.byContradiction
    intro hno
    apply hne
    refine ⟨φ, hφ, fun π hπ => ?_⟩
    apply Classical.byContradiction
    intro hle
    exact hno ⟨π, hπ, Nat.le_of_not_lt hle⟩

/-- Schema over languages: every Cook–Reckhow system for `L` has a
superpolynomial lower bound. -/
def AllCRSystemsSuperpolynomialFor (L : Language) : Prop :=
  ∀ P : CRSystem L, SuperpolyLB (toSystem P) (memberOf L) List.length

/-- **Open obligation (Cook's program).** Every Cook–Reckhow proof system for
`TAUT = complement SAT` (a polynomial-time machine verifier, sound and
complete) has a superpolynomial lower bound: for every polynomial `p` some
member `x` of `TAUT` has only accepted proofs longer than `p |x|`.  With the
named known theorem `CookReckhow` this is equivalent to NP ≠ coNP. -/
def AllTautSystemsSuperpolynomial : Prop :=
  ∀ P : CRSystem (complement SAT),
    SuperpolyLB (toSystem P) (fun x => complement SAT x = true) List.length

theorem allTautSystemsSuperpolynomial_iff_for :
    AllTautSystemsSuperpolynomial ↔ AllCRSystemsSuperpolynomialFor TAUT := Iff.rfl

/-- The obligation is the abstract schema for the class of Cook–Reckhow
systems for `TAUT`. -/
theorem allTautSystemsSuperpolynomial_iff_class :
    AllTautSystemsSuperpolynomial ↔
      SuperpolyAllSystemsFor (CRClass TAUT) (memberOf TAUT) List.length := by
  constructor
  · rintro h S ⟨P, rfl⟩
    exact h P
  · intro h P
    exact h _ ⟨P, rfl⟩

/-- The schema for `L` is the absence of a polynomially bounded system. -/
theorem allCRSystemsSuperpolynomial_iff (L : Language) :
    AllCRSystemsSuperpolynomialFor L ↔ ∀ P : CRSystem L, ¬ CRPolyBounded P := by
  constructor
  · intro h P ⟨p, hp⟩
    exact (superpolyLB_iff_forall_not_polyBounded _ _ _).mp (h P) p hp
  · intro h P
    exact (superpolyLB_iff_forall_not_polyBounded _ _ _).mpr fun p hp => h P ⟨p, hp⟩

/-- **Optimal systems reduce the obligation to one machine lower bound.** If
some Cook–Reckhow system for `TAUT` p-simulates every other, the obligation is
equivalent to a superpolynomial lower bound for that one system. -/
theorem optimal_crSystem_reduces (P : CRSystem TAUT)
    (hopt : ∀ Q : CRSystem TAUT, ∃ q, PSim (toSystem P) (toSystem Q) q) :
    AllTautSystemsSuperpolynomial ↔ SuperpolyLB (toSystem P) (memberOf TAUT) List.length := by
  rw [allTautSystemsSuperpolynomial_iff_class]
  exact optimal_system_reduces _ _ _ _ ⟨P, rfl⟩ (by rintro T ⟨Q, rfl⟩; exact hopt Q)

/-- Verifier runs are deterministic. -/
theorem verifierRun_deterministic {v : VerifierProgram} {x π : Word} {t t' : Nat}
    {b b' : Bool} (h : v.Run x π t b) (h' : v.Run x π t' b') : t = t' ∧ b = b' := by
  cases v with
  | ignoreCertificate m => exact run_deterministic h h'
  | paired m => exact run_deterministic h h'

/-- **A polynomially bounded Cook–Reckhow system puts `L` in NP** (proved: the
proof bound is the certificate bound; the clock and determinism bound the
accepting run). -/
theorem inNP_of_crPolyBounded {L : Language} (P : CRSystem L) (h : CRPolyBounded P) :
    InNP L := by
  obtain ⟨q, hq⟩ := h
  refine ⟨{ language := L, verifier := P.verifier, timeBound := P.timeBound,
            certBound := ⟨q.c, q.k⟩,
            terminates := fun x π _ => P.halts x π,
            correct := fun x => ⟨fun hx => ?_, fun ⟨π, t, _, _, hr⟩ => P.sound x π t hr⟩ }, rfl⟩
  obtain ⟨π, ⟨t, hr⟩, hlen⟩ := hq x hx
  obtain ⟨t', b', ht', hr'⟩ := P.halts x π
  obtain ⟨rfl, _⟩ := verifierRun_deterministic hr hr'
  exact ⟨π, t, hlen, ht', hr⟩

/-- **Every language in P has a polynomially bounded Cook–Reckhow system**
(proved: the decider ignores the proof, and the empty proof suffices). -/
theorem crPolyBounded_of_inP {L : Language} (h : InP L) :
    ∃ P : CRSystem L, CRPolyBounded P := by
  obtain ⟨m, p, hm⟩ := (polyDec_iff_inP L).mpr h
  refine ⟨{ verifier := .ignoreCertificate m, timeBound := p,
            halts := fun x _ => ?_, sound := fun x _ t hr => ?_, complete := fun x hx => ?_ },
          ⟨⟨0, 0⟩, fun x hx => ?_⟩⟩
  · obtain ⟨t, b, ht, hr, _⟩ := hm x
    exact ⟨t, b, ht, hr⟩
  · obtain ⟨t', b', _, hr', hb'⟩ := hm x
    obtain ⟨_, rfl⟩ := run_deterministic hr hr'
    exact hb'.symm
  · obtain ⟨t, b, _, hr, hb⟩ := hm x
    rw [hx] at hb
    subst hb
    exact ⟨[], t, hr⟩
  · obtain ⟨t, b, _, hr, hb⟩ := hm x
    have hx' : L x = true := hx
    rw [hx'] at hb
    subst hb
    exact ⟨[], ⟨t, hr⟩, Nat.zero_le _⟩

/-- A language outside NP satisfies the schema. -/
theorem allCRSystemsSuperpolynomial_of_not_inNP {L : Language} (h : ¬ InNP L) :
    AllCRSystemsSuperpolynomialFor L :=
  (allCRSystemsSuperpolynomial_iff L).mpr fun P hP => h (inNP_of_crPolyBounded P hP)

/-- A language in P violates the schema. -/
theorem not_allCRSystemsSuperpolynomial_of_inP {L : Language} (h : InP L) :
    ¬ AllCRSystemsSuperpolynomialFor L := fun hall => by
  obtain ⟨P, hP⟩ := crPolyBounded_of_inP h
  exact (allCRSystemsSuperpolynomial_iff L).mp hall P hP

/-- `¬ TAUT ∈ NP` gives the obligation (proved). -/
theorem allTautSystemsSuperpolynomial_of_not_inNP (h : ¬ InNP TAUT) :
    AllTautSystemsSuperpolynomial :=
  allCRSystemsSuperpolynomial_of_not_inNP h

/-- The obligation gives `SAT ∉ P` unconditionally (proved). -/
theorem not_inP_sat_of_allTautSystemsSuperpolynomial (h : AllTautSystemsSuperpolynomial) :
    ¬ InP SAT := fun hs =>
  not_allCRSystemsSuperpolynomial_of_inP (inP_complement hs) h

/-- **Conditional theorem (proved).** With SAT ∈ NP (a named Cook–Levin half),
the obligation gives P ≠ NP. -/
theorem pNotEqualsNP_of_allTautSystemsSuperpolynomial (mem : SATInNP)
    (h : AllTautSystemsSuperpolynomial) : PNotEqualsNP := fun hp =>
  not_inP_sat_of_allTautSystemsSuperpolynomial h (inP_sat_of_pEqualsNP mem hp)

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem pNotEqualsNP_of_allTautSystemsSuperpolynomial'
    (h : AllTautSystemsSuperpolynomial) : PNotEqualsNP :=
  pNotEqualsNP_of_allTautSystemsSuperpolynomial SATVerifier.satInNP h

/-- `TAUT ∉ NP` gives NP ≠ coNP, given SAT ∈ NP (proved). -/
theorem npNeCoNP_of_not_inNP_taut (mem : SATInNP) (h : ¬ InNP TAUT) : ¬ NPEqualsCoNP :=
  fun heq => h ((heq SAT).mp mem)

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem npNeCoNP_of_not_inNP_taut' (h : ¬ InNP TAUT) : ¬ NPEqualsCoNP :=
  npNeCoNP_of_not_inNP_taut SATVerifier.satInNP h

/-- Known theorem, not mechanised here: every Cook–Reckhow system for `TAUT`
is superpolynomial iff NP ≠ coNP (S. A. Cook and R. A. Reckhow, "The relative
efficiency of propositional proof systems", J. Symbolic Logic 44(1), 1979,
Theorem 1.5; the machine form uses the NP-completeness of SAT and the closure
of NP under polynomial-time reductions). -/
def CookReckhow : Prop := AllTautSystemsSuperpolynomial ↔ ¬ NPEqualsCoNP

/-- **Conditional theorem (named hypothesis).** The obligation gives NP ≠ coNP. -/
theorem npNeCoNP_of_allTautSystemsSuperpolynomial (hCR : CookReckhow)
    (h : AllTautSystemsSuperpolynomial) : ¬ NPEqualsCoNP := hCR.mp h

/-- **Conditional theorem (named hypothesis).** The obligation gives P ≠ NP
through NP ≠ coNP (`pNotEqualsNP_of_npNeCoNP`). -/
theorem pNotEqualsNP_via_cookReckhow (hCR : CookReckhow)
    (h : AllTautSystemsSuperpolynomial) : PNotEqualsNP :=
  pNotEqualsNP_of_npNeCoNP (npNeCoNP_of_allTautSystemsSuperpolynomial hCR h)

/-- With `CookReckhow`, NP ≠ coNP gives the obligation. -/
theorem allTautSystemsSuperpolynomial_of_npNeCoNP (hCR : CookReckhow)
    (h : ¬ NPEqualsCoNP) : AllTautSystemsSuperpolynomial := hCR.mpr h

/-! ### Non-vacuity -/

/-- The machine with no instructions halts with `false` after one step. -/
theorem emptyMachine_run (x : Word) : Run ⟨[]⟩ (initial x) 1 false := Run.halt rfl

theorem inP_const_false : InP (fun _ => false) :=
  inP_of_decidesWithin (m := ⟨[]⟩) (p := ⟨1, 0⟩)
    (fun x => ⟨1, false, by simp [Polynomial.eval], emptyMachine_run x, rfl⟩)

/-- Non-vacuity, false side: the schema fails for the constant-false language. -/
theorem const_false_not_allSuperpolynomial :
    ¬ AllCRSystemsSuperpolynomialFor (fun _ => false) :=
  not_allCRSystemsSuperpolynomial_of_inP inP_const_false

/-- Injective encoding of verifier programs. -/
def encVerifier : VerifierProgram → Word
  | .ignoreCertificate m => false :: encMachine m
  | .paired m => true :: encMachine m

theorem encVerifier_injective (v w : VerifierProgram) (h : encVerifier v = encVerifier w) :
    v = w := by
  cases v <;> cases w <;> simp only [encVerifier, List.cons.injEq] at h
  · rw [encMachine_injective h.2]
  · cases h.1
  · cases h.1
  · rw [encMachine_injective h.2]

open Classical in
/-- The language of inputs with some accepted proof. -/
noncomputable def verifierLanguage (v : VerifierProgram) : Language :=
  fun x => decide (∃ π t, v.Run x π t true)

theorem verifierLanguage_eq {L : Language} (P : CRSystem L) :
    verifierLanguage P.verifier = L := by
  classical
  funext x
  simp only [verifierLanguage]
  cases hx : L x with
  | true => exact decide_eq_true (P.complete x hx)
  | false =>
    refine decide_eq_false fun ⟨π, t, hr⟩ => ?_
    rw [P.sound x π t hr] at hx
    cases hx

/-- Non-vacuity, true side: some language has no Cook–Reckhow system at all,
so the schema holds for it (Cantor over encoded verifiers). -/
theorem exists_allSuperpolynomial : ∃ L : Language, AllCRSystemsSuperpolynomialFor L := by
  obtain ⟨L, hL⟩ :=
    exists_language_not_in_family encVerifier encVerifier_injective verifierLanguage
  exact ⟨L, fun P => absurd (verifierLanguage_eq P) (hL P.verifier)⟩

/-- The schema is satisfiable and refutable. -/
theorem crSchema_nontrivial :
    (∃ L, AllCRSystemsSuperpolynomialFor L) ∧ (∃ L, ¬ AllCRSystemsSuperpolynomialFor L) :=
  ⟨exists_allSuperpolynomial, ⟨_, const_false_not_allSuperpolynomial⟩⟩

end MachinePart

end Issue532.Idea39
