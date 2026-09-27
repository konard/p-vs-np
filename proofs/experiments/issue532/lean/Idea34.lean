import proofs.complexity.lean.Complexity

/-!
# Issue #532, Idea 34: quantifier order in lower bounds

This file imports the repository's machine model (`Complexity`: finite
single-tape machines, `ClassP`, `ClassNP`, `InP`, `InNP`, `PNotEqualsNP`).

Main results:

* `exists_forall_imp_forall_exists`: `(∃ x, ∀ a, R a x) → ∀ a, ∃ x, R a x`
  holds for every relation.
* `forall_exists_not_imp_exists_forall`: the converse fails for **every** type
  with two distinct elements (countermodel `R a x := a = x`).
* `pNotEqualsNP_iff_exists_hard`: `PNotEqualsNP ↔ ∃ L, InNP L ∧ ¬ InP L`
  (the `←` direction is constructive: `exists_hard_imp_pNotEqualsNP`).
* `not_inP_iff`: `¬ InP L ↔ ∀ p : ClassP, p.language ≠ L` (constructive).
* `pNotEqualsNP_iff_unfolded`: `PNotEqualsNP ↔ ∃ L, InNP L ∧ ∀ p : ClassP,
  ∃ x, p.language x ≠ L x` — every polynomial-time record (machine together
  with its polynomial bound) has its own input on which it is wrong.
* `lookup_agrees`, `no_universal_hard_input`, `no_universal_hard_input_set`:
  in the function model, any finite set of inputs is answered correctly by a
  finite patch of any algorithm; so for a class closed under finite patching
  no finite set of inputs is hard for all algorithms of the class.
* `hard_inputs_unbounded`: for a class closed under finite patching, if every
  algorithm of the class errs somewhere, then every algorithm errs on inputs of
  arbitrarily large length.

Verdict: a correct tool, not a route. It proves that the correct shape of a
P != NP statement is `∀ algorithm, ∃ input`, and that the swapped shape
`∃ input, ∀ algorithm` is false in the function model. No lower bound is
proved here.
-/

namespace Issue532.Idea34

open Complexity

/-! ## (a) Pure quantifier logic -/

/-- **Valid direction.** A single witness good for every `a` is good for each `a`. -/
theorem exists_forall_imp_forall_exists {α β : Type} (R : α → β → Prop) :
    (∃ x, ∀ a, R a x) → ∀ a, ∃ x, R a x := by
  rintro ⟨x, hx⟩ a
  exact ⟨x, hx a⟩

/-- **Invalid direction.** On any type with two distinct elements, the relation
`R a x := a = x` satisfies `∀ a, ∃ x, R a x` but not `∃ x, ∀ a, R a x`. -/
theorem forall_exists_not_imp_exists_forall {α : Type} (a₀ a₁ : α) (hne : a₀ ≠ a₁) :
    ∃ R : α → α → Prop, (∀ a, ∃ x, R a x) ∧ ¬ ∃ x, ∀ a, R a x := by
  refine ⟨fun a x => a = x, fun a => ⟨a, rfl⟩, ?_⟩
  rintro ⟨x, hx⟩
  exact hne ((hx a₀).trans (hx a₁).symm)

/-- Instance used in the dossier: algorithms and inputs are both `Bool`. -/
example : ∃ R : Bool → Bool → Prop, (∀ a, ∃ x, R a x) ∧ ¬ ∃ x, ∀ a, R a x :=
  forall_exists_not_imp_exists_forall false true (by decide)

/-! ## (b) and (c) The quantifier structure of `PNotEqualsNP` -/

/-- **Constructive direction.** An NP language outside P refutes `PEqualsNP`. -/
theorem exists_hard_imp_pNotEqualsNP :
    (∃ L, InNP L ∧ ¬ InP L) → PNotEqualsNP := by
  rintro ⟨L, hNP, hP⟩ hEq
  exact hP (hEq L hNP)

/-- **Classical direction.** `PNotEqualsNP` yields an NP language outside P. -/
theorem pNotEqualsNP_imp_exists_hard :
    PNotEqualsNP → ∃ L, InNP L ∧ ¬ InP L := by
  intro hne
  apply Classical.byContradiction
  intro hno
  apply hne
  intro L hNP
  apply Classical.byContradiction
  intro hP
  exact hno ⟨L, hNP, hP⟩

/-- `PNotEqualsNP ↔ ∃ L, InNP L ∧ ¬ InP L`. -/
theorem pNotEqualsNP_iff_exists_hard :
    PNotEqualsNP ↔ ∃ L, InNP L ∧ ¬ InP L :=
  ⟨pNotEqualsNP_imp_exists_hard, exists_hard_imp_pNotEqualsNP⟩

/-- **Constructive unfolding.** `L ∉ P` means: every `ClassP` record — a machine
together with a polynomial bound and proofs of termination and correctness —
decides some other language. -/
theorem not_inP_iff (L : Language) :
    ¬ InP L ↔ ∀ p : ClassP, p.language ≠ L := by
  constructor
  · intro h p hp
    exact h ⟨p, hp⟩
  · rintro h ⟨p, hp⟩
    exact h p hp

/-- Two languages differ iff they differ on some input (classical). -/
theorem language_ne_iff (L₁ L₂ : Language) : L₁ ≠ L₂ ↔ ∃ x, L₁ x ≠ L₂ x := by
  constructor
  · intro hne
    apply Classical.byContradiction
    intro hno
    apply hne
    funext x
    apply Classical.byContradiction
    intro hx
    exact hno ⟨x, hx⟩
  · rintro ⟨x, hx⟩ heq
    exact hx (heq ▸ rfl)

/-- **Per-algorithm hard inputs.** `L ∉ P` iff every polynomial-time record errs on
some input of its own choosing (`∀ p, ∃ x`, not `∃ x, ∀ p`). -/
theorem not_inP_iff_each_errs (L : Language) :
    ¬ InP L ↔ ∀ p : ClassP, ∃ x, p.language x ≠ L x := by
  rw [not_inP_iff]
  exact forall_congr' fun p => language_ne_iff p.language L

/-- **Full unfolding of `PNotEqualsNP`** with its quantifier order made explicit. -/
theorem pNotEqualsNP_iff_unfolded :
    PNotEqualsNP ↔ ∃ L, InNP L ∧ ∀ p : ClassP, ∃ x, p.language x ≠ L x := by
  rw [pNotEqualsNP_iff_exists_hard]
  constructor
  · rintro ⟨L, h1, h2⟩
    exact ⟨L, h1, (not_inP_iff_each_errs L).mp h2⟩
  · rintro ⟨L, h1, h2⟩
    exact ⟨L, h1, (not_inP_iff_each_errs L).mpr h2⟩

/-! ## Why `∃ input, ∀ algorithm` is false: finite patching -/

/-- Membership test in a finite list of inputs. -/
def memb (x : Word) : List Word → Bool
  | [] => false
  | y :: ys => (x == y) || memb x ys

theorem memb_of_mem {x : Word} {xs : List Word} (h : x ∈ xs) : memb x xs = true := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [memb, Bool.or_eq_true, beq_iff_eq]
    cases h with
    | head => exact Or.inl rfl
    | tail _ h' => exact Or.inr (ih h')

/-- The algorithm `A` patched by a lookup table for `L` on the finite list `xs`. -/
def patch (A L : Word → Bool) (xs : List Word) (x : Word) : Bool :=
  if memb x xs then L x else A x

/-- **Lookup-table lemma.** For every finite list of inputs, the patched algorithm
agrees with `L` on all of them. -/
theorem lookup_agrees (A L : Word → Bool) (xs : List Word) :
    ∀ x, x ∈ xs → patch A L xs x = L x := by
  intro x hx
  simp [patch, memb_of_mem hx]

/-- Outside the patched list, the patched algorithm behaves like `A`. -/
theorem patch_outside (A L : Word → Bool) (xs : List Word) (x : Word)
    (h : memb x xs = false) : patch A L xs x = A x := by
  simp [patch, h]

/-- A class of algorithms is closed under finite patching (true for polynomial time:
a lookup table for finitely many inputs costs only a fixed amount of extra time). -/
def PatchClosed (Alg : (Word → Bool) → Prop) (L : Word → Bool) : Prop :=
  ∀ A xs, Alg A → Alg (patch A L xs)

/-- **No universal hard input.** For a nonempty patch-closed class, no single input is
answered wrongly by every algorithm in the class. -/
theorem no_universal_hard_input (Alg : (Word → Bool) → Prop) (L : Word → Bool)
    (closed : PatchClosed Alg L) (A : Word → Bool) (hA : Alg A) :
    ¬ ∃ x, ∀ B, Alg B → B x ≠ L x := by
  rintro ⟨x, hx⟩
  exact hx (patch A L [x]) (closed A [x] hA) (lookup_agrees A L [x] x (List.mem_singleton.mpr rfl))

/-- **No universal finite hard set.** For a nonempty patch-closed class, no finite list of
inputs contains, for every algorithm of the class, an input where it errs. -/
theorem no_universal_hard_input_set (Alg : (Word → Bool) → Prop) (L : Word → Bool)
    (closed : PatchClosed Alg L) (A : Word → Bool) (hA : Alg A) :
    ¬ ∃ xs : List Word, ∀ B, Alg B → ∃ x, x ∈ xs ∧ B x ≠ L x := by
  rintro ⟨xs, hxs⟩
  obtain ⟨x, hmem, hne⟩ := hxs (patch A L xs) (closed A xs hA)
  exact hne (lookup_agrees A L xs x hmem)

/-- All bit strings of length exactly `n`. -/
def allInputs : Nat → List Word
  | 0 => [[]]
  | n + 1 => (allInputs n).map (List.cons false) ++ (allInputs n).map (List.cons true)

theorem mem_allInputs (x : Word) : x ∈ allInputs x.length := by
  induction x with
  | nil => simp [allInputs]
  | cons b x ih => cases b <;> simp [allInputs, ih]

/-- All bit strings of length `< m`. -/
def inputsBelow : Nat → List Word
  | 0 => []
  | m + 1 => inputsBelow m ++ allInputs m

theorem mem_inputsBelow (x : Word) (m : Nat) (h : x.length < m) : x ∈ inputsBelow m := by
  induction m with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    simp only [inputsBelow, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact Or.inl (ih hlt)
    · right; rw [← heq]; exact mem_allInputs x

/-- **Hard inputs occur at arbitrarily large sizes.** If a patch-closed class contains
no algorithm that is correct everywhere, then every algorithm in it errs on inputs of
every size bound `m` or above. -/
theorem hard_inputs_unbounded (Alg : (Word → Bool) → Prop) (L : Word → Bool)
    (closed : PatchClosed Alg L)
    (noSolver : ∀ B, Alg B → ∃ x, B x ≠ L x) :
    ∀ A, Alg A → ∀ m, ∃ x, m ≤ x.length ∧ A x ≠ L x := by
  intro A hA m
  obtain ⟨x, hx⟩ := noSolver (patch A L (inputsBelow m)) (closed A _ hA)
  refine ⟨x, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hlt
    exact hx (lookup_agrees A L _ x (mem_inputsBelow x m (Nat.lt_of_not_le hlt)))
  · intro hAx
    apply hx
    unfold patch
    cases hm : memb x (inputsBelow m) with
    | false => exact hAx
    | true => rfl

end Issue532.Idea34
