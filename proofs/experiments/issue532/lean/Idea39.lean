/-!
# Issue #532, Idea 39: proof-system scope (lower bounds and p-simulation)

Abstract Cook–Reckhow setting: a proof system over formulas `F` is a relation
`Proves : Proof → F → Prop` with a size function `size : Proof → Nat`.
Polynomials are pairs `⟨c, k⟩` evaluated as `c * (n + 1) ^ k`, as in the
repository's `proofs/complexity` library.

Main results (all general, for arbitrary formula and proof types):

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
* `SuperpolyAllSystems` (the open obligation) and `optimal_system_reduces`: if a
  class has a system p-simulating all its members, the obligation for the class is
  equivalent to a lower bound for that one system.

Verdict: correct tool, insufficient alone. The Cook–Reckhow theorem (the
obligation for all polynomial-time verifiable systems is equivalent to
`NP ≠ coNP`) is cited, not formalized.
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

/-- **Open obligation.** Every system in the class `C` has a superpolynomial lower bound.
For `C` = Cook–Reckhow systems (polynomial-time checkable, sound and complete for
propositional tautologies) this is equivalent to `NP ≠ coNP` (Cook–Reckhow 1979; not
formalized here). -/
def SuperpolyAllSystems (C : System F → Prop) (taut : F → Prop) (fsize : F → Nat) : Prop :=
  ∀ S, C S → SuperpolyLB S taut fsize

/-- **Optimal systems reduce the obligation to one lower bound.** If `S ∈ C` p-simulates
every member of `C`, the obligation for `C` is equivalent to a superpolynomial lower
bound for `S`. -/
theorem optimal_system_reduces (C : System F → Prop) (taut : F → Prop) (fsize : F → Nat)
    (S : System F) (hS : C S) (hopt : ∀ T, C T → ∃ q, PSim S T q) :
    SuperpolyAllSystems C taut fsize ↔ SuperpolyLB S taut fsize := by
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
    ¬ SuperpolyAllSystems C taut fsize :=
  fun h => superpoly_not_bounded S taut fsize (h S hS) p hb

/-- Check of the composition polynomial at `n = 2`. -/
example : (Poly.eval ⟨2, 1⟩ (Poly.eval ⟨1, 2⟩ 2)) ≤ (Poly.comp ⟨2, 1⟩ ⟨1, 2⟩).eval 2 := by decide

end Issue532.Idea39
