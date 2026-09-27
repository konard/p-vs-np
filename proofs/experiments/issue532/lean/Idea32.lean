/-!
# Issue #532, Idea 32: promise algorithms

**Verdict: developed to an open obligation (conditional theorem proved).**

A *promise algorithm* for a language `L` on a promise `Π` only has to answer
correctly on inputs satisfying `Π`.  Two general facts are proved.

* **Negative (flip at `x`).** For every promise `Π` and every language `L`
  (over a type with decidable equality), if some input `x` lies outside `Π`,
  then there is an algorithm correct on all of `Π` and wrong at `x`
  (`flip_at`).  Consequently, correctness on a promise implies total
  correctness *exactly* when the promise covers every input
  (`promise_total_iff`).
* **Conditional positive.** If a map `f` sends every input into `Π` and
  preserves the answer (`L x = M (f x)`), then any promise solver for `M` on
  `Π` composes with `f` into a total solver for `L` (`promise_reduction_total`),
  with additive cost (`compose_cost`).  The "into the promise" condition is
  also necessary (`composition_works_iff`).

Instantiated to CNF: the Unique-SAT promise `AtMostOneSolution` excludes
`(x0 ∨ x1)` (`not_unique_example`), so some algorithm correct on the promise
calls this satisfiable formula unsatisfiable (`usat_solver_wrong`).  A
different promise makes SAT trivial (`trivial_promise_solver`).  The open
obligation is a deterministic polynomial-time map from all CNFs into the
Unique-SAT promise that preserves satisfiability (`IsolationObligation`); with
a promise solver it would decide SAT (`isolation_solves_sat`).  Such a map
exists trivially once SAT is decidable (`decider_meets_isolation`); whether a
polynomial-time one exists is open.  Nothing here decides P vs NP.
-/

namespace Issue532.Idea32

/-! ## General promise problems -/

/-- `A` decides `L` correctly on every input satisfying the promise `Π`. -/
def CorrectOn {α : Type} (P : α → Prop) (L A : α → Bool) : Prop :=
  ∀ x, P x → A x = L x

/-- Flip at `x`: for any promise and language, an input outside the promise
yields an algorithm that is correct on the whole promise and wrong at `x`. -/
theorem flip_at {α : Type} [DecidableEq α] (P : α → Prop) (L : α → Bool) (x : α)
    (hx : ¬ P x) : ∃ A : α → Bool, CorrectOn P L A ∧ A x ≠ L x := by
  refine ⟨fun y => if y = x then !(L x) else L y, ?_, ?_⟩
  · intro y hy
    have hne : y ≠ x := fun e => hx (e ▸ hy)
    simp [hne]
  · cases L x <;> simp

/-- Promise-correct algorithms need not be total: an input outside the promise
yields a promise-correct algorithm that is not a total solver. -/
theorem promise_correct_not_total {α : Type} [DecidableEq α] (P : α → Prop) (L : α → Bool)
    (h : ∃ x, ¬ P x) : ∃ A : α → Bool, CorrectOn P L A ∧ ¬ ∀ y, A y = L y := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨A, hA, hne⟩ := flip_at P L x hx
  exact ⟨A, hA, fun hall => hne (hall x)⟩

/-- Conditional positive: a map into the promise that preserves the answer turns
any promise solver for `M` into a total solver for `L`. -/
theorem promise_reduction_total {α β : Type} (P : β → Prop) (L : α → Bool) (M : β → Bool)
    (f : α → β) (hinto : ∀ x, P (f x)) (hpres : ∀ x, L x = M (f x))
    (A : β → Bool) (hA : CorrectOn P M A) : ∀ x, A (f x) = L x := by
  intro x
  rw [hA (f x) (hinto x), hpres x]

/-- The "into the promise" condition is exactly what makes the composition work
for *every* promise solver. -/
theorem composition_works_iff {α β : Type} [DecidableEq β] (P : β → Prop) [DecidablePred P]
    (L : α → Bool) (M : β → Bool) (f : α → β) (hpres : ∀ x, L x = M (f x)) :
    (∀ A : β → Bool, CorrectOn P M A → ∀ x, A (f x) = L x) ↔ ∀ x, P (f x) := by
  constructor
  · intro h x
    by_cases hx : P (f x)
    · exact hx
    obtain ⟨A, hA, hne⟩ := flip_at P M (f x) hx
    exact absurd ((h A hA x).trans (hpres x)) hne
  · intro hinto A hA
    exact promise_reduction_total P L M f hinto hpres A hA

/-- Special case `f = id`: correctness on a promise is total correctness for
every algorithm exactly when the promise covers all inputs. -/
theorem promise_total_iff {α : Type} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    (L : α → Bool) :
    (∀ A : α → Bool, CorrectOn P L A → ∀ x, A x = L x) ↔ ∀ x, P x :=
  composition_works_iff P L L (fun x => x) (fun _ => rfl)

/-- Cost of the composition: with abstract step counts and sizes, the composed
solver costs at most `p n + r (q n)` when `f` costs `≤ p n`, maps size `n` to size
`≤ q n`, and the promise solver costs `≤ r m` on size `m` with `r` monotone. -/
theorem compose_cost {α β : Type} (sizeA : α → Nat) (sizeB : β → Nat) (f : α → β)
    (costF : α → Nat) (costA : β → Nat) (p q r : Nat → Nat)
    (hF : ∀ x, costF x ≤ p (sizeA x)) (hS : ∀ x, sizeB (f x) ≤ q (sizeA x))
    (hA : ∀ y, costA y ≤ r (sizeB y)) (hr : ∀ m m', m ≤ m' → r m ≤ r m') (x : α) :
    costF x + costA (f x) ≤ p (sizeA x) + r (q (sizeA x)) :=
  Nat.add_le_add (hF x) (Nat.le_trans (hA (f x)) (hr _ _ (hS x)))

/-! ## CNF core -/

structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

abbrev Clause := List Lit
abbrev CNF := List Clause
abbrev Assignment := Nat → Bool

def evalLit (a : Assignment) (l : Lit) : Bool :=
  if l.pos then a l.var else !(a l.var)

def evalClause (a : Assignment) : Clause → Bool
  | [] => false
  | l :: c => evalLit a l || evalClause a c

def evalCNF (a : Assignment) : CNF → Bool
  | [] => true
  | c :: φ => evalClause a c && evalCNF a φ

def Satisfiable (φ : CNF) : Prop := ∃ a, evalCNF a φ = true

def clauseVars (c : Clause) : List Nat := c.map Lit.var

def vars : CNF → List Nat
  | [] => []
  | c :: φ => clauseVars c ++ vars φ

/-! ## The Unique-SAT promise -/

/-- The Unique-SAT promise: any two satisfying assignments agree on the
variables of `φ` (so `φ` is unsatisfiable or has exactly one solution). -/
def AtMostOneSolution (φ : CNF) : Prop :=
  ∀ a b, evalCNF a φ = true → evalCNF b φ = true → ∀ v, v ∈ vars φ → a v = b v

/-- The formula `x0 ∨ x1`. -/
def twoWay : CNF := [[⟨0, true⟩, ⟨1, true⟩]]

theorem twoWay_satisfiable : Satisfiable twoWay :=
  ⟨fun _ => true, rfl⟩

/-- `x0 ∨ x1` has two solutions differing on `x1`, so it violates the promise. -/
theorem not_unique_example : ¬ AtMostOneSolution twoWay := by
  intro h
  have := h (fun _ => true) (fun v => v == 0) rfl rfl 1 (by decide)
  exact Bool.noConfusion this

/-- The single-literal formula `x0` satisfies the promise. -/
theorem unique_example : AtMostOneSolution [[⟨0, true⟩]] := by
  intro a b ha hb v hv
  simp [evalCNF, evalClause, evalLit] at ha hb
  simp only [vars, clauseVars, List.map_cons, List.map_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  subst hv
  rw [ha, hb]

/-- `flip_at` instantiated to Unique-SAT: for any SAT decider `sat`, some
algorithm correct on the whole promise answers "unsatisfiable" on the
satisfiable formula `x0 ∨ x1`. -/
theorem usat_solver_wrong (sat : CNF → Bool) (hsat : ∀ φ, sat φ = true ↔ Satisfiable φ) :
    ∃ A : CNF → Bool, CorrectOn AtMostOneSolution sat A ∧
      A twoWay = false ∧ Satisfiable twoWay := by
  obtain ⟨A, hA, hne⟩ := flip_at AtMostOneSolution sat twoWay not_unique_example
  have hs : sat twoWay = true := (hsat twoWay).2 twoWay_satisfiable
  refine ⟨A, hA, ?_, twoWay_satisfiable⟩
  cases h : A twoWay
  · rfl
  · exact absurd (h.trans hs.symm) hne

/-! ## A promise that makes SAT trivial -/

def hasEmpty : CNF → Bool
  | [] => false
  | c :: φ => c.isEmpty || hasEmpty φ

theorem hasEmpty_unsat (φ : CNF) (h : hasEmpty φ = true) : ¬ Satisfiable φ := by
  intro ⟨a, ha⟩
  induction φ with
  | nil => exact Bool.noConfusion h
  | cons c φ ih =>
    simp only [evalCNF, Bool.and_eq_true] at ha
    simp only [hasEmpty, Bool.or_eq_true] at h
    cases h with
    | inl hc =>
      cases c with
      | nil => exact Bool.noConfusion ha.1
      | cons _ _ => exact Bool.noConfusion hc
    | inr hφ => exact ih hφ ha.2

/-- Promise: satisfiable, or containing the empty clause. -/
def EmptyPromise (φ : CNF) : Prop := Satisfiable φ ∨ hasEmpty φ = true

/-- On this promise, the linear-time test "no empty clause" decides SAT:
promise problems can be much easier than the total problem. -/
theorem trivial_promise_solver (sat : CNF → Bool) (hsat : ∀ φ, sat φ = true ↔ Satisfiable φ) :
    CorrectOn EmptyPromise sat (fun φ => !(hasEmpty φ)) := by
  intro φ hφ
  cases he : hasEmpty φ with
  | true =>
    have hn : ¬ Satisfiable φ := hasEmpty_unsat φ he
    cases hs : sat φ with
    | false => show (!hasEmpty φ) = false; rw [he]; rfl
    | true => exact absurd ((hsat φ).1 hs) hn
  | false =>
    have hS : Satisfiable φ := by
      cases hφ with
      | inl h => exact h
      | inr h => rw [he] at h; exact Bool.noConfusion h
    show (!hasEmpty φ) = sat φ
    rw [he, (hsat φ).2 hS]; rfl

/-- The same trivial solver is wrong outside the promise, e.g. on `x0 ∧ ¬x0`. -/
theorem trivial_solver_wrong (sat : CNF → Bool) (hsat : ∀ φ, sat φ = true ↔ Satisfiable φ) :
    (fun φ => !(hasEmpty φ)) [[⟨0, true⟩], [⟨0, false⟩]] ≠ sat [[⟨0, true⟩], [⟨0, false⟩]] := by
  intro h
  have hs : Satisfiable [[⟨0, true⟩], [⟨0, false⟩]] := (hsat _).1 (h.symm.trans rfl)
  obtain ⟨a, ha⟩ := hs
  simp only [evalCNF, evalClause, evalLit, Bool.or_false, Bool.and_true] at ha
  cases h0 : a 0 <;> rw [h0] at ha <;> exact Bool.noConfusion ha

/-! ## The open obligation -/

/-- The obligation: a map in the class `PolyTime` from all CNFs into the
Unique-SAT promise that preserves satisfiability (a deterministic isolation). -/
def IsolationObligation (PolyTime : (CNF → CNF) → Prop) : Prop :=
  ∃ f : CNF → CNF, PolyTime f ∧ (∀ φ, AtMostOneSolution (f φ)) ∧
    ∀ φ, Satisfiable φ ↔ Satisfiable (f φ)

/-- Conditional theorem: the obligation plus any promise solver for Unique-SAT
gives a total SAT solver `A ∘ f` with `f` in the class `PolyTime`. -/
theorem isolation_solves_sat (PolyTime : (CNF → CNF) → Prop) (h : IsolationObligation PolyTime)
    (A : CNF → Bool) (hA : ∀ φ, AtMostOneSolution φ → (A φ = true ↔ Satisfiable φ)) :
    ∃ f : CNF → CNF, PolyTime f ∧ ∀ φ, A (f φ) = true ↔ Satisfiable φ := by
  obtain ⟨f, hf, hinto, hpres⟩ := h
  exact ⟨f, hf, fun φ => (hA (f φ) (hinto φ)).trans (hpres φ).symm⟩

/-- The map used when a SAT decider is already available: the empty formula
(one solution modulo no variables) or the empty clause (no solution). -/
def isolate (sat : CNF → Bool) (φ : CNF) : CNF := if sat φ then [] else [[]]

/-- A SAT decider meets the correctness part of the obligation trivially via
`isolate`, so the obligation is only as hard as its time bound. -/
theorem decider_meets_isolation (sat : CNF → Bool) (hsat : ∀ φ, sat φ = true ↔ Satisfiable φ) :
    (∀ φ, AtMostOneSolution (isolate sat φ)) ∧
      ∀ φ, Satisfiable φ ↔ Satisfiable (isolate sat φ) := by
  constructor
  · intro φ a b ha _ v hv
    unfold isolate at ha hv
    cases hs : sat φ with
    | true => rw [hs] at hv; exact absurd hv List.not_mem_nil
    | false => rw [hs] at ha; exact Bool.noConfusion ha
  · intro φ
    unfold isolate
    cases hs : sat φ with
    | true =>
      exact ⟨fun _ => ⟨fun _ => true, rfl⟩, fun _ => (hsat φ).1 hs⟩
    | false =>
      constructor
      · intro hS
        rw [(hsat φ).2 hS] at hs
        exact Bool.noConfusion hs
      · intro ⟨a, ha⟩
        exact Bool.noConfusion ha

end Issue532.Idea32
