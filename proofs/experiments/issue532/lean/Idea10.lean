import proofs.experiments.issue532.lean.Circuits
import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue #532, Idea 10: monotone lower bounds and transfer to general circuits

We work with Boolean formulas (fan-out-one circuits) over AND, OR, NOT,
literals `lit b` and variables `var i`, evaluated on assignments
`Nat → Bool`. A formula is *monotone* when it contains no NOT (`notFree`).

Proved for all formulas, all assignments, and all `n`:

* `monotone_eval`: monotone formulas compute monotone functions.
* `no_monotone_formula_for_not`, `no_monotone_formula_for_parity`: no
  monotone formula of any size computes `¬x₀`, or parity of `n ≥ 2`
  variables, while `parityCirc_correct` gives general formulas for parity
  of every `n`.
* `monotone_complete`: every monotone function depending on the first `n`
  variables is computed by some monotone formula. So the monotone model is
  exactly the right model for monotone functions; its lower bounds are about
  *size*, not expressibility.
* `doubleRail_correct`, `undual_correct`, `general_iff_double_rail`: general
  formula size equals, up to a factor 2, the monotone formula size of the
  *double-rail* version of the function, which only has to be correct on the
  consistent inputs `(x, ¬x)`. A general superpolynomial lower bound is
  therefore *equivalent* to a monotone lower bound for this partial function,
  and not implied by a monotone lower bound for `f` itself.
* `general_lb_implies_monotone_lb`: the easy direction (general lower bounds
  restrict to monotone ones).

Tie to the shared machine model. The lower-bound shapes are schemas over a
formula family (`GeneralSuperpolyLowerBoundFor`, `MonotoneSuperpolyLowerBoundFor`,
`DoubleRailLowerBoundFor`). They are instantiated on the language
`Issue532.Machines.SAT` through `Issue532.Circuits.slice SAT n`, the Boolean
function that SAT computes on inputs of length `n`:

* `SATFormulaLowerBound` (open obligation): SAT has no polynomial-size
  formulas; `NPNotInPolyFormulas` (open obligation): some language with
  `InNP` has none.
* `npNotInPolyFormulas_of_sat`: with `SATInNP`, the first gives the second.
  This is the honest conclusion (an NC¹-type separation, NP ⊄ poly-size
  formulas). It does **not** give P ≠ NP: that would also need
  `PSubsetPolyFormulas` (every language in P has polynomial-size formulas, a
  P ⊆ NC¹-type statement that is open and widely believed false), as
  `pNotEqualsNP_of_satFormulaLowerBound` makes explicit.
* `npNotInPolyFormulas_of_sat'`, `pNotEqualsNP_of_satFormulaLowerBound'`: the
  same without the `SATInNP` premise, which is proved in `SATVerifier.lean`
  (`SATVerifier.satInNP`). `PSubsetPolyFormulas` remains a premise.
* `sat_slice_not_monotone`, `sat_monotone_lower_bound_trivial`: SAT on words
  is not monotone at length 2, so the monotone lower bound for SAT holds for
  a trivial reason and carries no information; the monotone route has to go
  through the double-rail function (`satFormulaLowerBound_iff_doubleRail`).
* `const_no_general_lower_bound`: the lower-bound shape fails for a constant
  family, so it is not vacuously true.

Verdict: "a monotone lower bound for an NP function gives P ≠ NP" is refuted
in full strength by Tardos (1988): there are monotone functions in P whose
monotone circuit complexity is exponential (not formalized here). The formal
core isolates the exact extra obligation (`SATFormulaLowerBound`), which is
open and faces the natural-proofs barrier.
-/

namespace Issue532.Idea10

open Complexity
open Issue532.Machines (SAT SATInNP)
open Issue532.Circuits (slice)

/-- Boolean formulas; `lit b` is a literal, `var i` reads input `i`. -/
inductive Circ where
  | var : Nat → Circ
  | lit : Bool → Circ
  | conj : Circ → Circ → Circ
  | disj : Circ → Circ → Circ
  | neg : Circ → Circ

open Circ

def eval : Circ → (Nat → Bool) → Bool
  | var i, x => x i
  | lit b, _ => b
  | conj a b, x => eval a x && eval b x
  | disj a b, x => eval a x || eval b x
  | neg a, x => !eval a x

/-- Number of nodes. -/
def size : Circ → Nat
  | var _ => 1
  | lit _ => 1
  | conj a b => size a + size b + 1
  | disj a b => size a + size b + 1
  | neg a => size a + 1

/-- A formula is monotone if it contains no NOT gate. -/
def notFree : Circ → Bool
  | var _ => true
  | lit _ => true
  | conj a b => notFree a && notFree b
  | disj a b => notFree a && notFree b
  | neg _ => false

/-- Boolean order `a ≤ b` (false ≤ true). -/
def leB (a b : Bool) : Bool := !a || b

/-- Pointwise order on assignments. -/
def LeAssign (x y : Nat → Bool) : Prop := ∀ i, leB (x i) (y i) = true

/-- A Boolean function on assignments is monotone. -/
def MonotoneFn (f : (Nat → Bool) → Bool) : Prop := ∀ x y, LeAssign x y → leB (f x) (f y) = true

theorem leB_and (a b c d : Bool) (h1 : leB a c = true) (h2 : leB b d = true) :
    leB (a && b) (c && d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [leB]

theorem leB_or (a b c d : Bool) (h1 : leB a c = true) (h2 : leB b d = true) :
    leB (a || b) (c || d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [leB]

/-- Monotone formulas compute monotone functions (for every formula and all assignments). -/
theorem monotone_eval (c : Circ) (hc : notFree c = true) (x y : Nat → Bool) (hxy : LeAssign x y) :
    leB (eval c x) (eval c y) = true := by
  induction c with
  | var i => exact hxy i
  | lit b => cases b <;> rfl
  | conj a b iha ihb =>
    simp only [notFree, Bool.and_eq_true] at hc
    exact leB_and _ _ _ _ (iha hc.1) (ihb hc.2)
  | disj a b iha ihb =>
    simp only [notFree, Bool.and_eq_true] at hc
    exact leB_or _ _ _ _ (iha hc.1) (ihb hc.2)
  | neg _ _ => simp [notFree] at hc

theorem notFree_computes_monotone (c : Circ) (hc : notFree c = true) : MonotoneFn (eval c) :=
  fun x y h => monotone_eval c hc x y h

/-- Negation of `x₀` is not monotone. -/
theorem neg_not_monotone : ¬ MonotoneFn (fun x => !x 0) := by
  intro h
  have := h (fun _ => false) (fun _ => true) (fun _ => rfl)
  simp [leB] at this

/-- No monotone formula, of any size, computes `¬x₀`. -/
theorem no_monotone_formula_for_not (c : Circ) (hc : notFree c = true) :
    ¬ ∀ x, eval c x = !x 0 := by
  intro h
  apply neg_not_monotone
  intro x y hxy
  have := monotone_eval c hc x y hxy
  rw [h x, h y] at this
  exact this

/-- Parity of the first `n` variables. -/
def parity : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, x => xor (parity n x) (x n)

theorem parity_first (n : Nat) (hn : 1 ≤ n) : parity n (fun i => i == 0) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [parity]
    by_cases h : n = 0
    · subst h; rfl
    · rw [ih (by omega)]
      have : (n == 0) = false := by simp [h]
      rw [this]; rfl

theorem parity_two (n : Nat) (hn : 2 ≤ n) : parity n (fun i => decide (i < 2)) = false := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [parity]
    by_cases h : n = 1
    · subst h; rfl
    · rw [ih (by omega)]
      have : decide (n < 2) = false := by simp; omega
      rw [this]; rfl

/-- Parity of `n ≥ 2` variables is not monotone. -/
theorem parity_not_monotone (n : Nat) (hn : 2 ≤ n) : ¬ MonotoneFn (parity n) := by
  intro h
  have hle : LeAssign (fun i => i == 0) (fun i => decide (i < 2)) := by
    intro i
    by_cases h0 : i = 0
    · subst h0; rfl
    · by_cases h1 : i = 1
      · subst h1; rfl
      · have e1 : (i == 0) = false := by simp [h0]
        simp [leB, e1]
  have := h _ _ hle
  rw [parity_first n (by omega), parity_two n hn] at this
  simp [leB] at this

/-- No monotone formula computes parity of `n ≥ 2` variables. -/
theorem no_monotone_formula_for_parity (n : Nat) (hn : 2 ≤ n) (c : Circ) (hc : notFree c = true) :
    ¬ ∀ x, eval c x = parity n x := by
  intro h
  apply parity_not_monotone n hn
  intro x y hxy
  have := monotone_eval c hc x y hxy
  rw [h x, h y] at this
  exact this

/-- XOR from AND/OR/NOT. -/
def xorC (a b : Circ) : Circ := disj (conj a (neg b)) (conj (neg a) b)

/-- A general formula for parity of the first `n` variables. -/
def parityCirc : Nat → Circ
  | 0 => lit false
  | n + 1 => xorC (parityCirc n) (var n)

/-- General formulas (with NOT) compute parity for every `n`. -/
theorem parityCirc_correct (n : Nat) (x : Nat → Bool) : eval (parityCirc n) x = parity n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parityCirc, parity, xorC, eval, ih]
    cases parity n x <;> cases x n <;> rfl

/-! ### Monotone completeness -/

/-- Update one coordinate of an assignment. -/
def upd (x : Nat → Bool) (k : Nat) (b : Bool) : Nat → Bool := fun i => if i = k then b else x i

/-- `f` only depends on variables `< n`. -/
def DependsOn (f : (Nat → Bool) → Bool) (n : Nat) : Prop :=
  ∀ x y, (∀ i, i < n → x i = y i) → f x = f y

/-- Shannon-style monotone formula: `f = (xₙ ∧ f[xₙ:=1]) ∨ f[xₙ:=0]` for monotone `f`. -/
def build : Nat → ((Nat → Bool) → Bool) → Circ
  | 0, f => lit (f (fun _ => false))
  | n + 1, f => disj (conj (var n) (build n (fun x => f (upd x n true)))) (build n (fun x => f (upd x n false)))

theorem build_notFree : ∀ n f, notFree (build n f) = true := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ n ih => intro f; simp [build, notFree, ih]

theorem upd_le (x y : Nat → Bool) (k : Nat) (b : Bool) (h : LeAssign x y) :
    LeAssign (upd x k b) (upd y k b) := by
  intro i
  simp only [upd]
  by_cases hi : i = k
  · simp [hi, leB]
  · simp [hi]; exact h i

/--
Monotone completeness: every monotone function that depends only on the first
`n` variables is computed by a monotone formula (`build n f`).
-/
theorem monotone_complete : ∀ (n : Nat) (f : (Nat → Bool) → Bool), MonotoneFn f → DependsOn f n →
    ∀ x, eval (build n f) x = f x := by
  intro n
  induction n with
  | zero =>
    intro f _ hd x
    simp only [build, eval]
    exact hd _ _ (fun i hi => by omega)
  | succ n ih =>
    intro f hm hd x
    have hm1 : MonotoneFn (fun x => f (upd x n true)) := fun x y h => hm _ _ (upd_le x y n true h)
    have hm0 : MonotoneFn (fun x => f (upd x n false)) := fun x y h => hm _ _ (upd_le x y n false h)
    have hdb : ∀ b, DependsOn (fun x => f (upd x n b)) n := by
      intro b x y hxy
      apply hd
      intro i hi
      simp only [upd]
      by_cases e : i = n
      · simp [e]
      · simp [e]; exact hxy i (by omega)
    simp only [build, eval]
    rw [ih _ hm1 (hdb true) x, ih _ hm0 (hdb false) x]
    have hsame : ∀ b, x n = b → f (upd x n b) = f x := by
      intro b hb
      apply hd
      intro i _
      simp only [upd]
      by_cases e : i = n
      · simp [e, hb]
      · simp [e]
    cases hxn : x n with
    | true =>
      rw [hsame true hxn]
      have hle : LeAssign (upd x n false) x := by
        intro i
        simp only [upd]
        by_cases e : i = n
        · simp [e, leB]
        · simp [e, leB]
      have := hm _ _ hle
      cases h1 : f x <;> cases h2 : f (upd x n false) <;> simp_all [leB]
    | false =>
      rw [hsame false hxn]
      simp

/-! ### Double rail: general size = monotone size of a partial function -/

/-- Double-rail input: variable `2i` carries `xᵢ`, variable `2i+1` carries `¬xᵢ`. -/
def dual (x : Nat → Bool) : Nat → Bool := fun j => if j % 2 = 0 then x (j / 2) else !x (j / 2)

/-- Push negations to the inputs (De Morgan): returns (formula for `c`, formula for `¬c`). -/
def doubleRail : Circ → Circ × Circ
  | var i => (var (2 * i), var (2 * i + 1))
  | lit b => (lit b, lit (!b))
  | conj a b => (conj (doubleRail a).1 (doubleRail b).1, disj (doubleRail a).2 (doubleRail b).2)
  | disj a b => (disj (doubleRail a).1 (doubleRail b).1, conj (doubleRail a).2 (doubleRail b).2)
  | neg a => ((doubleRail a).2, (doubleRail a).1)

theorem dual_even (x : Nat → Bool) (i : Nat) : dual x (2 * i) = x i := by
  simp only [dual]
  have h1 : 2 * i % 2 = 0 := by omega
  have h2 : 2 * i / 2 = i := by omega
  simp [h1, h2]

theorem dual_odd (x : Nat → Bool) (i : Nat) : dual x (2 * i + 1) = !x i := by
  simp only [dual]
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [h1, h2]

/--
Double rail correctness: both rails are monotone, no larger than `c`, and on
consistent inputs compute `c` and `¬c`.
-/
theorem doubleRail_correct (c : Circ) :
    notFree (doubleRail c).1 = true ∧ notFree (doubleRail c).2 = true ∧
    size (doubleRail c).1 ≤ size c ∧ size (doubleRail c).2 ≤ size c ∧
    ∀ x, eval (doubleRail c).1 (dual x) = eval c x ∧ eval (doubleRail c).2 (dual x) = !eval c x := by
  induction c with
  | var i =>
    refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro x
    exact ⟨dual_even x i, dual_odd x i⟩
  | lit b =>
    refine ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro x; exact ⟨rfl, rfl⟩
  | conj a b iha ihb =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := iha
    obtain ⟨b1, b2, b3, b4, b5⟩ := ihb
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [doubleRail, notFree, a1, b1]
    · simp [doubleRail, notFree, a2, b2]
    · simp only [doubleRail, size]; omega
    · simp only [doubleRail, size]; omega
    · intro x
      simp only [doubleRail, eval, (a5 x).1, (a5 x).2, (b5 x).1, (b5 x).2]
      cases eval a x <;> cases eval b x <;> simp
  | disj a b iha ihb =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := iha
    obtain ⟨b1, b2, b3, b4, b5⟩ := ihb
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [doubleRail, notFree, a1, b1]
    · simp [doubleRail, notFree, a2, b2]
    · simp only [doubleRail, size]; omega
    · simp only [doubleRail, size]; omega
    · intro x
      simp only [doubleRail, eval, (a5 x).1, (a5 x).2, (b5 x).1, (b5 x).2]
      cases eval a x <;> cases eval b x <;> simp
  | neg a iha =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := iha
    refine ⟨a2, a1, ?_, ?_, ?_⟩
    · simp only [doubleRail, size]; omega
    · simp only [doubleRail, size]; omega
    · intro x
      simp only [doubleRail, eval, (a5 x).1, (a5 x).2]
      cases eval a x <;> simp

/-- Replace double-rail inputs by `xᵢ` and `¬xᵢ`. -/
def undual : Circ → Circ
  | var j => if j % 2 = 0 then var (j / 2) else neg (var (j / 2))
  | lit b => lit b
  | conj a b => conj (undual a) (undual b)
  | disj a b => disj (undual a) (undual b)
  | neg a => neg (undual a)

/-- `undual` turns a double-rail formula into a general formula at most twice as large. -/
theorem undual_correct (c : Circ) :
    size (undual c) ≤ 2 * size c ∧ ∀ x, eval (undual c) x = eval c (dual x) := by
  induction c with
  | var j =>
    constructor
    · simp only [undual]
      by_cases h : j % 2 = 0
      · simp [h, size]
      · simp [h, size]
    · intro x
      simp only [undual]
      by_cases h : j % 2 = 0
      · simp [h, eval, dual]
      · simp [h, eval, dual]
  | lit b => exact ⟨by simp [undual, size], fun x => rfl⟩
  | conj a b iha ihb =>
    refine ⟨?_, ?_⟩
    · simp only [undual, size]; omega
    · intro x; simp only [undual, eval, iha.2 x, ihb.2 x]
  | disj a b iha ihb =>
    refine ⟨?_, ?_⟩
    · simp only [undual, size]; omega
    · intro x; simp only [undual, eval, iha.2 x, ihb.2 x]
  | neg a iha =>
    refine ⟨?_, ?_⟩
    · simp only [undual, size]; omega
    · intro x; simp only [undual, eval, iha.2 x]

/-! ### Lower-bound statements -/

/--
Schema: the family `f n` has no general formulas of polynomial size. The family
is a parameter, so this is a schema; its instance for SAT is
`SATFormulaLowerBound`.
-/
def GeneralSuperpolyLowerBoundFor (f : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c d : Nat, ∃ n, ∀ C : Circ, size C ≤ c * n ^ d + c → ∃ x, eval C x ≠ f n x

/-- Schema: a superpolynomial lower bound against monotone formulas only. -/
def MonotoneSuperpolyLowerBoundFor (f : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c d : Nat, ∃ n, ∀ C : Circ, notFree C = true → size C ≤ c * n ^ d + c → ∃ x, eval C x ≠ f n x

/-- Schema: a monotone lower bound for the double-rail partial function
(correct only on inputs `dual x`). -/
def DoubleRailLowerBoundFor (f : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀ c d : Nat, ∃ n, ∀ C : Circ, notFree C = true → size C ≤ c * n ^ d + c → ∃ x, eval C (dual x) ≠ f n x

/-- The easy direction: a general lower bound restricts to monotone formulas. -/
theorem general_lb_implies_monotone_lb (f : Nat → (Nat → Bool) → Bool)
    (h : GeneralSuperpolyLowerBoundFor f) : MonotoneSuperpolyLowerBoundFor f := by
  intro c d
  obtain ⟨n, hn⟩ := h c d
  exact ⟨n, fun C _ hs => hn C hs⟩

/--
Exact reformulation: a general superpolynomial lower bound holds iff a
monotone superpolynomial lower bound holds for the double-rail partial
function. The monotone lower bound needed is for a *partial* function with
negated literals as extra inputs, not for `f` itself.
-/
theorem general_iff_double_rail (f : Nat → (Nat → Bool) → Bool) :
    GeneralSuperpolyLowerBoundFor f ↔ DoubleRailLowerBoundFor f := by
  constructor
  · intro h c d
    obtain ⟨n, hn⟩ := h (2 * c) d
    refine ⟨n, fun C _ hs => ?_⟩
    have hu := undual_correct C
    have hsz : size (undual C) ≤ 2 * c * n ^ d + 2 * c := by
      have : 2 * size C ≤ 2 * (c * n ^ d + c) := Nat.mul_le_mul_left 2 hs
      rw [Nat.mul_assoc]; omega
    obtain ⟨x, hx⟩ := hn (undual C) hsz
    exact ⟨x, by rw [← hu.2 x]; exact hx⟩
  · intro h c d
    obtain ⟨n, hn⟩ := h c d
    refine ⟨n, fun C hs => ?_⟩
    have hd := doubleRail_correct C
    obtain ⟨x, hx⟩ := hn (doubleRail C).1 hd.1 (Nat.le_trans hd.2.2.1 hs)
    exact ⟨x, by rw [← (hd.2.2.2.2 x).1]; exact hx⟩

/-! ### The obligation on the shared machine model -/

/--
**Open obligation.** SAT (the language `Issue532.Machines.SAT` of the shared
machine model) has no polynomial-size formulas: for every `c d` there is a
length `n` at which no formula of size at most `c * n ^ d + c` computes SAT on
the words of length `n` (read from variables `0, …, n - 1`).
-/
def SATFormulaLowerBound : Prop :=
  ∀ c d : Nat, ∃ n, ∀ C : Circ, size C ≤ c * n ^ d + c → ∃ x, eval C x ≠ slice SAT n x

theorem satFormulaLowerBound_iff_for :
    SATFormulaLowerBound ↔ GeneralSuperpolyLowerBoundFor (slice SAT) := Iff.rfl

/--
**Open obligation** (the honest target). Some language with `InNP` has no
polynomial-size formulas.
-/
def NPNotInPolyFormulas : Prop :=
  ∃ L : Language, InNP L ∧
    ∀ c d : Nat, ∃ n, ∀ C : Circ, size C ≤ c * n ^ d + c → ∃ x, eval C x ≠ slice L n x

/-- **Conditional theorem** (honest conclusion). With `SATInNP`, a formula lower
bound for SAT puts NP outside polynomial-size formulas. -/
theorem npNotInPolyFormulas_of_sat (mem : SATInNP) (h : SATFormulaLowerBound) :
    NPNotInPolyFormulas :=
  ⟨SAT, mem, h⟩

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem npNotInPolyFormulas_of_sat' (h : SATFormulaLowerBound) : NPNotInPolyFormulas :=
  npNotInPolyFormulas_of_sat SATVerifier.satInNP h

/--
Not known, and not assumed anywhere: every language in P has polynomial-size
formulas. This is a P ⊆ NC¹-type statement, an open problem that is widely
believed false. It is stated only to show what a formula lower bound would
additionally need in order to give P ≠ NP.
-/
def PSubsetPolyFormulas : Prop :=
  ∀ L : Language, InP L → ∃ c d : Nat, ∀ n, ∃ C : Circ, size C ≤ c * n ^ d + c ∧
    ∀ x, eval C x = slice L n x

/-- The gap, made explicit: a formula lower bound for SAT gives P ≠ NP only
together with the unproved `PSubsetPolyFormulas`. -/
theorem pNotEqualsNP_of_satFormulaLowerBound (mem : SATInNP) (hPF : PSubsetPolyFormulas)
    (h : SATFormulaLowerBound) : PNotEqualsNP := by
  intro hPNP
  obtain ⟨c, d, hc⟩ := hPF SAT (hPNP SAT mem)
  obtain ⟨n, hn⟩ := h c d
  obtain ⟨C, hs, hC⟩ := hc n
  obtain ⟨x, hx⟩ := hn C hs
  exact hx (hC x)

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped.
The unproved `PSubsetPolyFormulas` remains a premise. -/
theorem pNotEqualsNP_of_satFormulaLowerBound' (hPF : PSubsetPolyFormulas)
    (h : SATFormulaLowerBound) : PNotEqualsNP :=
  pNotEqualsNP_of_satFormulaLowerBound SATVerifier.satInNP hPF h

/-- The double-rail reformulation applies to SAT. -/
theorem satFormulaLowerBound_iff_doubleRail :
    SATFormulaLowerBound ↔ DoubleRailLowerBoundFor (slice SAT) :=
  general_iff_double_rail (slice SAT)

/-- SAT on words is not monotone at length 2: `00` encodes the empty formula
(satisfiable) and `10` encodes the empty clause (unsatisfiable). -/
theorem sat_slice_not_monotone : ¬ MonotoneFn (slice SAT 2) := by
  intro h
  have := h (fun _ => false) (fun i => i == 0) (fun _ => rfl)
  have h1 : slice SAT 2 (fun _ => false) = true := by decide
  have h2 : slice SAT 2 (fun i => i == 0) = false := by decide
  rw [h1, h2] at this
  exact absurd this (by decide)

/-- The monotone lower bound for SAT holds for a trivial reason (no monotone
formula computes SAT at length 2), so it says nothing about the size of
formulas for SAT. -/
theorem sat_monotone_lower_bound_trivial : MonotoneSuperpolyLowerBoundFor (slice SAT) := by
  intro c d
  refine ⟨2, fun C hC _ => ?_⟩
  apply Classical.byContradiction
  intro hno
  apply sat_slice_not_monotone
  intro x y hxy
  have heq : ∀ z, eval C z = slice SAT 2 z := fun z =>
    Classical.byContradiction (fun hz => hno ⟨z, hz⟩)
  have := monotone_eval C hC x y hxy
  rw [heq x, heq y] at this
  exact this

/-- Non-vacuity (false side): the lower-bound shape fails for a constant
family, which the one-node formula `lit b` computes at every length. -/
theorem const_no_general_lower_bound (b : Bool) :
    ¬ GeneralSuperpolyLowerBoundFor (fun _ _ => b) := by
  intro h
  obtain ⟨n, hn⟩ := h 1 0
  obtain ⟨x, hx⟩ := hn (lit b) (by simp [size])
  exact hx rfl

end Issue532.Idea10
