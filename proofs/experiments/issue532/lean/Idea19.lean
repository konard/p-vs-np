import proofs.experiments.issue532.lean.Circuits
import proofs.experiments.issue532.lean.SATVerifier

/-!
# Issue #532, Idea 19: advice and nonuniformity

An *advice machine* is a function `M : List α → List Bool → Bool` that is
given, besides the input `x`, an advice string `a x.length` that depends only
on the input length.  This file proves, for arbitrary languages:

* `unary_decided_by_advice`: every unary language `U : Nat → Bool`
  (computable or not) is decided by one fixed trivial machine with one bit
  of advice per length;
* `adviceOf_injective`, `advice_escapes_every_enumeration`,
  `no_enumeration_of_advice_class`: the one-bit-advice class escapes every
  `Nat`-indexed family of languages, in particular the (countable) family of
  languages decided by uniform algorithms, so it contains undecidable
  languages;
* `input_advice_trivializes`: advice that may depend on the whole input
  decides every language, because the advice can be the answer;
* `fixed_machine_advice_limited`: conversely, a fixed machine with at most
  `n` bits of advice at length `n` cannot decide every language on length-`n`
  inputs (a diagonal argument over the `2^n` inputs of length `n`);
* `inPPoly_lengthOnly`, `unaryDiag_not_inP`, `ppoly_not_subset_p`: the same
  phenomenon in the shared model. Every length-only language is in the shared
  `InPPoly`, and a unary diagonal against `Complexity.Machine` is not in `InP`;
* `uniform_in_advice`, `not_in_superclass_not_in_P`,
  `nonuniform_lower_bound_separatesFor` (schema over free classes) and its
  instance `nonuniform_lower_bound_separates`: the only useful direction. If
  P ⊆ P/poly then a language of NP outside P/poly lies outside P.

**Verdict.** Using advice as a route to a uniform polynomial algorithm is
refuted: advice classes contain languages of arbitrary (even undecidable)
complexity, so an advice algorithm carries no uniform information. The
converse direction is developed to the open obligations `SATNotInPPoly`
(`¬ InPPoly SAT`) and `NPNotInPPoly` (NP ⊄ P/poly), stated over the shared
machine and circuit models. Using the proved inclusion `pSubsetPPoly` and
`SATInNP`, they give `PNotEqualsNP`
(`pNotEqualsNP_of_satNotInPPoly`, `pNotEqualsNP_of_npNotInPPoly`). `SATInNP`
is proved in `SATVerifier.lean` (`SATVerifier.satInNP`), so
`npNotInPPoly_of_sat'` and `pNotEqualsNP_of_satNotInPPoly'` drop that premise.
The inclusion is proved in issue #626. Neither lower-bound obligation is proved. Core
Lean only.
-/

namespace Issue532.Idea19

open Complexity Issue532.Machines Issue532.Circuits

/-! ## Advice machines -/

/-- `M` with length-indexed advice `a` decides `L` if it is correct on every
input. -/
def AdviceDecides {α : Type} (M : List α → List Bool → Bool) (a : Nat → List Bool)
    (L : List α → Bool) : Prop :=
  ∀ x, M x (a x.length) = L x

/-- The trivial machine: ignore the input, read the first advice bit. -/
def readAdvice {α : Type} (_x : List α) (adv : List Bool) : Bool := adv.headD false

/-- The unary language on inputs `1^n` (modelled as `List Unit`) given by `U`. -/
def unaryLang (U : Nat → Bool) (x : List Unit) : Bool := U x.length

/-- One bit of advice per length: the answer on `1^n`. -/
def adviceOf (U : Nat → Bool) (n : Nat) : List Bool := [U n]

theorem adviceOf_length (U : Nat → Bool) (n : Nat) : (adviceOf U n).length = 1 := rfl

/-- **Every unary language has one-bit advice.**  No computability assumption
on `U` is made. -/
theorem unary_decided_by_advice (U : Nat → Bool) :
    AdviceDecides readAdvice (adviceOf U) (unaryLang U) := by
  intro x; rfl

/-- Different unary languages receive different advice sequences. -/
theorem adviceOf_injective (U V : Nat → Bool) (h : adviceOf U = adviceOf V) : U = V := by
  funext n
  have := congrFun h n
  simp only [adviceOf, List.cons.injEq] at this
  exact this.1

/-- **The one-bit-advice class escapes every enumeration.**  For every family
`e : Nat → (Nat → Bool)` (for instance, the languages decided by the `i`-th
uniform algorithm) there is a unary language decided by `readAdvice` with
one bit of advice that differs from every member of the family. -/
theorem advice_escapes_every_enumeration (e : Nat → Nat → Bool) :
    ∃ U : Nat → Bool, (∀ i, U ≠ e i) ∧
      AdviceDecides readAdvice (adviceOf U) (unaryLang U) := by
  refine ⟨fun n => !(e n n), fun i h => ?_, unary_decided_by_advice _⟩
  have := congrFun h i
  cases hc : e i i <;> simp [hc] at this

/-- No `Nat`-indexed family contains all unary languages decided by the fixed
machine with one bit of advice. -/
theorem no_enumeration_of_advice_class :
    ¬ ∃ e : Nat → Nat → Bool, ∀ U : Nat → Bool,
      AdviceDecides readAdvice (adviceOf U) (unaryLang U) → ∃ i, e i = U := by
  rintro ⟨e, he⟩
  obtain ⟨U, hU, hdec⟩ := advice_escapes_every_enumeration e
  obtain ⟨i, hi⟩ := he U hdec
  exact hU i hi.symm

/-- **Input-dependent advice trivializes everything.**  If the advice may
depend on the whole input, the machine that outputs its advice decides every
language, with the language itself as advice. -/
theorem input_advice_trivializes {α : Type} (L : α → Bool) :
    ∀ x, (fun (_ : α) (b : Bool) => b) x (L x) = L x := by
  intro x; rfl

/-! ## Limits of a fixed machine with short advice -/

/-- Enumeration of all Boolean strings of length `n`. -/
def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).map (List.cons false) ++ (allVecs n).map (List.cons true)

theorem allVecs_length (n : Nat) : (allVecs n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allVecs, ih, Nat.pow_succ]; omega

theorem mem_allVecs (n : Nat) (v : List Bool) : v ∈ allVecs n ↔ v.length = n := by
  induction n generalizing v with
  | zero =>
    cases v <;> simp [allVecs]
  | succ n ih =>
    cases v with
    | nil => simp [allVecs]
    | cons b w =>
      cases b <;> simp [allVecs, List.mem_map, ih]

/-- Binary value of a string (least significant bit first). -/
def toNat : List Bool → Nat
  | [] => 0
  | b :: x => (if b then 1 else 0) + 2 * toNat x

/-- The length-`n` string encoding `i` (least significant bit first). -/
def fromNat : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, i => (i % 2 == 1) :: fromNat n (i / 2)

theorem fromNat_length (n i : Nat) : (fromNat n i).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [fromNat, ih]

theorem toNat_fromNat (n i : Nat) (h : i < 2 ^ n) : toNat (fromNat n i) = i := by
  induction n generalizing i with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    rw [Nat.pow_succ] at h
    have hi : i / 2 < 2 ^ n := by omega
    simp only [fromNat, toNat, ih _ hi]
    cases hm : (i % 2 == 1)
    · simp at hm; simp; omega
    · simp at hm; simp; omega

/-- `nth A i` is the `i`-th element of `A`, or `[]` if out of range. -/
def nth : List (List Bool) → Nat → List Bool
  | [], _ => []
  | w :: _, 0 => w
  | _ :: A, i + 1 => nth A i

theorem nth_of_mem (A : List (List Bool)) (w : List Bool) (h : w ∈ A) :
    ∃ i, i < A.length ∧ nth A i = w := by
  induction A with
  | nil => simp at h
  | cons u A ih =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨0, by simp, by simp [nth, h]⟩
    · obtain ⟨i, hi, hn⟩ := ih h
      exact ⟨i + 1, by simp; omega, by simp [nth, hn]⟩

/-- **Diagonal limit.**  For every machine `M` and every list `A` of at most
`2^n` advice strings, some language disagrees, on some input of length `n`,
with `M` run on each advice string in `A`. -/
theorem diagonal_against_advice_list (M : List Bool → List Bool → Bool) (n : Nat)
    (A : List (List Bool)) (hA : A.length ≤ 2 ^ n) :
    ∃ L : List Bool → Bool, ∀ w ∈ A, ∃ x, x.length = n ∧ M x w ≠ L x := by
  refine ⟨fun x => !(M x (nth A (toNat x))), fun w hw => ?_⟩
  obtain ⟨i, hi, hn⟩ := nth_of_mem A w hw
  refine ⟨fromNat n i, fromNat_length n i, ?_⟩
  simp only [toNat_fromNat n i (by omega), hn]
  cases M (fromNat n i) w <;> simp

/-- **A fixed machine with at most `n` advice bits cannot decide every
language on length-`n` inputs.**  For every `s ≤ n` there is a language `L`
such that no advice string of length `s` makes `M` correct on all inputs of
length `n`. -/
theorem fixed_machine_advice_limited (M : List Bool → List Bool → Bool) (n s : Nat)
    (hs : s ≤ n) :
    ∃ L : List Bool → Bool, ∀ w : List Bool, w.length = s →
      ∃ x, x.length = n ∧ M x w ≠ L x := by
  have hlen : (allVecs s).length ≤ 2 ^ n := by
    rw [allVecs_length]; exact Nat.pow_le_pow_right (by omega) hs
  obtain ⟨L, hL⟩ := diagonal_against_advice_list M n (allVecs s) hlen
  exact ⟨L, fun w hw => hL w ((mem_allVecs s w).mpr hw)⟩

/-! ## Advice in the shared model: P/poly contains undecidable languages

The advice phenomenon above, restated for the shared classes: every language
that depends only on the input length is in `InPPoly` (one constant circuit per
length), and some such language is not in `InP` (a unary diagonal against the
machine model). So membership in P/poly carries no uniform information. -/

/-- Every language that depends only on the input length is in P/poly: at
length `n` the circuit is the constant `U n`. -/
theorem inPPoly_lengthOnly (U : Nat → Bool) : InPPoly (fun x => U x.length) := by
  refine ⟨⟨3, 0⟩, fun n hn => ?_⟩
  cases hU : U n
  · refine ⟨[(0, 0), (0, n), (n + 1, n + 1)], by simp [Polynomial.eval], ?_, ?_⟩
    · simp [WF, WFfrom]; omega
    · intro x hx; subst hx; show _ = U x.length; rw [hU]; exact output_const_false x hn
  · refine ⟨[(0, 0), (0, n)], by simp [Polynomial.eval], ?_, ?_⟩
    · simp [WF, WFfrom]; omega
    · intro x hx; subst hx; show _ = U x.length; rw [hU]; exact output_const_true x hn

/-- Bijective base-2 numeral of a word; injective. -/
def bijNat : Word → Nat
  | [] => 0
  | b :: w => 2 * bijNat w + (if b then 2 else 1)

theorem bijNat_injective : ∀ v w : Word, bijNat v = bijNat w → v = w
  | [], [] => fun _ => rfl
  | [], b :: w => by cases b <;> simp [bijNat]
  | b :: v, [] => by cases b <;> simp [bijNat]
  | b :: v, c :: w => by
    intro h
    simp only [bijNat] at h
    have hbc : b = c := by
      cases b <;> cases c <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h <;>
        first | rfl | omega
    subst hbc
    have : bijNat v = bijNat w := by
      cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] at h <;> omega
    rw [bijNat_injective v w this]

open Classical in
/-- The unary diagonal: length `n` is accepted unless `n` numbers the code of a
machine that accepts the all-`true` word of length `n`. -/
noncomputable def unaryDiag (n : Nat) : Bool :=
  decide (¬ ∃ m : Machine, bijNat (encMachine m) = n ∧
    ∃ t, Run m (initial (List.replicate n true)) t true)

/-- **No machine decides the unary diagonal**, in any time bound. -/
theorem unaryDiag_not_inP : ¬ InP (fun x => unaryDiag x.length) := by
  rintro ⟨P, hP⟩
  let n := bijNat (encMachine P.machine)
  let w := List.replicate n true
  obtain ⟨t, b, _, hr⟩ := P.terminates w
  have hc := P.correct w t b hr
  rw [hP] at hc
  have hlen : w.length = n := List.length_replicate
  simp only [hlen] at hc
  cases b with
  | true =>
    have hd : unaryDiag n = true := hc.mpr rfl
    simp only [unaryDiag, decide_eq_true_eq] at hd
    exact hd ⟨P.machine, rfl, t, hr⟩
  | false =>
    have hd : ¬ unaryDiag n = true := fun h => Bool.noConfusion (hc.mp h)
    simp only [unaryDiag, decide_eq_true_eq, Classical.not_not] at hd
    obtain ⟨m, hm, t', hr'⟩ := hd
    have := encMachine_injective (bijNat_injective _ _ hm)
    subst this
    exact Bool.noConfusion (run_deterministic hr hr').2

/-- **P/poly is not contained in P** (in the shared model): the unary
diagonal is in P/poly and not in P. Advice buys non-uniformity, not
algorithms. -/
theorem ppoly_not_subset_p : ∃ L : Language, InPPoly L ∧ ¬ InP L :=
  ⟨fun x => unaryDiag x.length, inPPoly_lengthOnly unaryDiag, unaryDiag_not_inP⟩

/-! ## The only useful direction: lower bounds against nonuniform classes -/

/-- Languages over binary strings. -/
abbrev Lang := List Bool → Bool

/-- A uniform decider is an advice machine that ignores empty advice: the
abstract content of P ⊆ P/poly. -/
theorem uniform_in_advice (D : Lang) :
    AdviceDecides (fun x (_ : List Bool) => D x) (fun _ => []) D := by
  intro x; rfl

/-- Schema (the pre-refactor form): some language of a class `NP` lies outside
a class `PPoly`. Both classes are parameters, so the schema is only as strong
as the classes supplied; `NPNotInPPoly` is its instance at the shared `InNP`
and `InPPoly`. -/
def NPNotInPPolyFor (NP PPoly : Lang → Prop) : Prop := ∃ L, NP L ∧ ¬ PPoly L

/-- If `P ⊆ C` and `L ∉ C` then `L ∉ P`. -/
theorem not_in_superclass_not_in_P (P C : Lang → Prop) (hPC : ∀ L, P L → C L)
    (L : Lang) (hL : ¬ C L) : ¬ P L :=
  fun hP => hL (hPC L hP)

/-- Schema version of the conditional separation: if `P ⊆ PPoly` and the
schema holds, then `NP ⊄ P`. -/
theorem nonuniform_lower_bound_separatesFor (P NP PPoly : Lang → Prop)
    (hP : ∀ L, P L → PPoly L) (h : NPNotInPPolyFor NP PPoly) : ¬ (∀ L, NP L → P L) := by
  intro hNP
  obtain ⟨L, hL, hnot⟩ := h
  exact not_in_superclass_not_in_P P PPoly hP L hnot (hNP L hL)

/-! ## The open obligations over the shared model -/

/-- **Open obligation.** SAT (`Issue532.Machines.SAT`) is not in P/poly
(`Issue532.Circuits.InPPoly`). Equivalent to `SuperpolyLowerBound SAT`. -/
def SATNotInPPoly : Prop := ¬ InPPoly SAT

/-- **Open obligation.** NP ⊄ P/poly: some language in the shared `InNP` is
outside the shared `InPPoly`. -/
def NPNotInPPoly : Prop := ∃ L : Language, InNP L ∧ ¬ InPPoly L

theorem npNotInPPoly_iff_for : NPNotInPPoly ↔ NPNotInPPolyFor InNP InPPoly := Iff.rfl

theorem satNotInPPoly_iff_superpoly : SATNotInPPoly ↔ SuperpolyLowerBound SAT :=
  (superpoly_iff_not_inPPoly SAT).symm

/-- The SAT obligation gives the NP obligation, using `SATInNP`. -/
theorem npNotInPPoly_of_sat (mem : SATInNP) (h : SATNotInPPoly) : NPNotInPPoly :=
  ⟨SAT, mem, h⟩

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped. -/
theorem npNotInPPoly_of_sat' (h : SATNotInPPoly) : NPNotInPPoly :=
  npNotInPPoly_of_sat SATVerifier.satInNP h

/-- **Conditional theorem.** Using the proved inclusion `pSubsetPPoly`,
NP ⊄ P/poly gives P ≠ NP. -/
theorem pNotEqualsNP_of_npNotInPPoly (h : NPNotInPPoly) : PNotEqualsNP := by
  intro hEq
  obtain ⟨L, hL, hnot⟩ := h
  exact not_inP_of_not_inPPoly hnot (hEq L hL)

/-- **Conditional theorem (SAT form).** Using `SATInNP` and the proved inclusion, `¬ InPPoly SAT` gives P ≠ NP. -/
theorem pNotEqualsNP_of_satNotInPPoly (mem : SATInNP)
    (h : SATNotInPPoly) : PNotEqualsNP :=
  pNotEqualsNP_of_superpoly_sat mem (satNotInPPoly_iff_superpoly.mp h)

/-- `SATInNP` is proved (`SATVerifier.satInNP`), so the premise is dropped.
The proved inclusion is used internally. -/
theorem pNotEqualsNP_of_satNotInPPoly' (h : SATNotInPPoly) :
    PNotEqualsNP :=
  pNotEqualsNP_of_satNotInPPoly SATVerifier.satInNP h

/-- The schema theorem, instantiated at the shared classes. -/
theorem nonuniform_lower_bound_separates (h : NPNotInPPoly) :
    ¬ (∀ L, InNP L → InP L) :=
  nonuniform_lower_bound_separatesFor InP InNP InPPoly pSubsetPPoly h

/-! ## Non-vacuity -/

/-- The `¬ InPPoly` half is satisfiable (by a counting language not known to
be in NP), and it is not trivial: constant languages are in P/poly. -/
theorem not_inPPoly_nonvacuous : (∃ L, ¬ InPPoly L) ∧ InPPoly (fun _ => true) :=
  ⟨exists_not_inPPoly, inPPoly_const true⟩

/-- `PSubsetPPoly` is not refuted by `ppoly_not_subset_p`: the converse
inclusion fails, which is consistent with P ⊆ P/poly. The obligation needs a
language that is *both* in NP and outside P/poly. -/
theorem ppoly_strictly_bigger_than_p_if :
    (∀ L, InP L → InPPoly L) ∧ ∃ L, InPPoly L ∧ ¬ InP L :=
  ⟨pSubsetPPoly, ppoly_not_subset_p⟩

end Issue532.Idea19
