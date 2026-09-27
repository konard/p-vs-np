import proofs.experiments.issue532.lean.Machines

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
different promise makes SAT trivial (`trivial_promise_solver`).

`IsolationObligationFor PolyTime` is a generic schema with a free class
`PolyTime` of maps; with a free class it is met by the decider-based map
`isolate` (`decider_meets_isolation`), so it only carries content once
`PolyTime` is fixed.  The open obligations are stated over the shared machine
model (`Complexity.Machine`, time = step count of `Complexity.Run`, words
decoded to CNFs by `Issue532.Machines.decode`):

* `IsolationObligation`: a polynomial-time machine map `g` on words (in the
  sense of `Issue532.Machines.Computes`) with every `g w` in the Unique-SAT
  promise and `SAT w = SAT (g w)`.  This is a *deterministic* isolation;
  Valiant–Vazirani gives only a randomized one.
* `PromiseSolver`: a polynomial-time machine correct for SAT on the Unique-SAT
  promise (`Issue532.Machines.DecidesOn`).

`isolation_promise_inP` and `isolation_route_gives_pEqualsNP` prove
`IsolationObligation → PromiseSolver → InP SAT` (and `PEqualsNP` given
`SATHard`); `isolationObligation_of_schema` and
`schema_of_isolationObligation` relate the machine obligation to the schema
instantiated with machine-computable maps; `not_forall_promise_class` shows
deciding on the promise is not trivial.  Nothing here decides P vs NP.
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

/-! ## The isolation schema -/

/-- Generic schema (a free class `PolyTime` of maps, not a machine model): a map
in `PolyTime` from all CNFs into the Unique-SAT promise that preserves
satisfiability (a deterministic isolation).  With a free `PolyTime` it is met
by `isolate` (see `decider_meets_isolation`); the machine instance is
`IsolationObligation` below. -/
def IsolationObligationFor (PolyTime : (CNF → CNF) → Prop) : Prop :=
  ∃ f : CNF → CNF, PolyTime f ∧ (∀ φ, AtMostOneSolution (f φ)) ∧
    ∀ φ, Satisfiable φ ↔ Satisfiable (f φ)

/-- Conditional theorem for the schema: it plus any promise solver for
Unique-SAT gives a total SAT solver `A ∘ f` with `f` in the class `PolyTime`. -/
theorem isolation_solves_sat (PolyTime : (CNF → CNF) → Prop) (h : IsolationObligationFor PolyTime)
    (A : CNF → Bool) (hA : ∀ φ, AtMostOneSolution φ → (A φ = true ↔ Satisfiable φ)) :
    ∃ f : CNF → CNF, PolyTime f ∧ ∀ φ, A (f φ) = true ↔ Satisfiable φ := by
  obtain ⟨f, hf, hinto, hpres⟩ := h
  exact ⟨f, hf, fun φ => (hA (f φ) (hinto φ)).trans (hpres φ).symm⟩

/-- The map used when a SAT decider is already available: the empty formula
(one solution modulo no variables) or the empty clause (no solution). -/
def isolate (sat : CNF → Bool) (φ : CNF) : CNF := if sat φ then [] else [[]]

/-- A SAT decider meets the correctness part of the schema trivially via
`isolate`.  This is why `IsolationObligationFor PolyTime` is vacuous for a free
`PolyTime` (any class containing `isolate sat` meets it): the content of the
obligation is entirely in the time bound, which `IsolationObligation` fixes to
machine step counts. -/
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

/-! ## The obligations over the shared machine model -/

open Complexity
open Issue532.Machines (SAT decode encodeCNF Computes DecidesOn DecidesWithin
  inP_of_promise_reduction polyDec_iff_inP pEqualsNP_of_inP_sat SATHard sat_iff sat_encode
  run_deterministic exists_language_not_in_family encMachine encMachine_injective)

/-! ### Translation between this file's CNF and the shared CNF -/

def ofLit (l : Machines.Lit) : Lit := ⟨l.var, l.pos⟩
def toLit (l : Lit) : Machines.Lit := ⟨l.var, l.pos⟩

/-- A shared-layer CNF read as a CNF of this file. -/
def ofM (φ : Machines.CNF) : CNF := φ.map (fun c => c.map ofLit)
/-- A CNF of this file read as a shared-layer CNF. -/
def toM (φ : CNF) : Machines.CNF := φ.map (fun c => c.map toLit)

theorem ofClause_toClause (c : Clause) : (c.map toLit).map ofLit = c := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [List.map_cons, ih]; rfl

theorem ofM_toM (φ : CNF) : ofM (toM φ) = φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [ofM, toM, List.map_cons] at *
    rw [ofClause_toClause, ih]

theorem evalLit_ofLit (a : Assignment) (l : Machines.Lit) :
    evalLit a (ofLit l) = Machines.evalLit a l := by
  obtain ⟨v, b⟩ := l
  simp only [evalLit, ofLit, Machines.evalLit]
  cases a v <;> cases b <;> rfl

theorem evalClause_ofM (a : Assignment) (c : Machines.Clause) :
    evalClause a (c.map ofLit) = Machines.evalClause a c := by
  induction c with
  | nil => rfl
  | cons l c ih => simp only [List.map_cons, evalClause, Machines.evalClause, evalLit_ofLit, ih]

theorem evalCNF_ofM (a : Assignment) (φ : Machines.CNF) :
    evalCNF a (ofM φ) = Machines.evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [ofM, List.map_cons, evalCNF, Machines.evalCNF, evalClause_ofM] at *
    rw [ih]

theorem satisfiable_ofM (φ : Machines.CNF) : Satisfiable (ofM φ) ↔ Machines.Satisfiable φ := by
  simp only [Satisfiable, Machines.Satisfiable, evalCNF_ofM]

/-- The shared `SAT` language, read through this file's CNF semantics. -/
theorem sat_iff_ofM (w : Word) : SAT w = true ↔ Satisfiable (ofM (decode w)) :=
  (sat_iff w).trans (satisfiable_ofM _).symm

/-! ### The promise, the obligations and the conditional theorems -/

/-- The Unique-SAT promise on words: the decoded formula has at most one
solution. -/
def UniquePromise (w : Word) : Prop := AtMostOneSolution (ofM (decode w))

/-- **Open obligation** (deterministic isolation).  A polynomial-time machine map
`g` on words (`Computes m g p`: the step count of the machine's run is at most
`p.eval |w|`) that sends every word into the Unique-SAT promise and preserves
`SAT`.  Valiant–Vazirani (1986) gives only a *randomized* map with this
property (success probability `Ω(1/n)`, and only for satisfiable inputs); the
obligation asks for a deterministic one. -/
def IsolationObligation : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    (∀ w, UniquePromise (g w)) ∧ ∀ w, SAT w = SAT (g w)

/-- **Open obligation** (Unique-SAT solver).  A polynomial-time machine that
decides `SAT` correctly on every word in the Unique-SAT promise. -/
def PromiseSolver : Prop :=
  ∃ (d : Machine) (p : Polynomial), DecidesOn d p UniquePromise SAT

/-- **Conditional theorem.**  Deterministic isolation plus a Unique-SAT promise
solver puts SAT in P (machine composition `inP_of_promise_reduction`). -/
theorem isolation_promise_inP (hI : IsolationObligation) (hS : PromiseSolver) : InP SAT := by
  obtain ⟨m, g, p, hm, hinto, hpres⟩ := hI
  obtain ⟨d, q, hd⟩ := hS
  exact inP_of_promise_reduction hm hinto hpres hd

/-- **Conditional theorem.**  With NP-hardness of SAT (`SATHard`, a named
hypothesis: the hard half of Cook–Levin), the two obligations give P = NP. -/
theorem isolation_route_gives_pEqualsNP (hard : SATHard) (hI : IsolationObligation)
    (hS : PromiseSolver) : PEqualsNP :=
  pEqualsNP_of_inP_sat hard (isolation_promise_inP hI hS)

/-- A total polynomial-time SAT decider is in particular a promise solver. -/
theorem promiseSolver_of_inP (h : InP SAT) : PromiseSolver := by
  obtain ⟨m, p, hd⟩ := (polyDec_iff_inP SAT).2 h
  exact ⟨m, p, fun x _ => hd x⟩

/-- Under deterministic isolation, the promise problem is exactly as hard as SAT. -/
theorem promiseSolver_iff_inP (hI : IsolationObligation) : PromiseSolver ↔ InP SAT :=
  ⟨isolation_promise_inP hI, promiseSolver_of_inP⟩

/-! ### The machine obligation is the schema with machine-computable maps -/

/-- `f` is realised on words by a polynomial-time machine: some machine map `g`
satisfies `decode (g w) = f (decode w)` (read through `ofM`) on every word. -/
def RealizedOnWords (f : CNF → CNF) : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ w, ofM (decode (g w)) = f (ofM (decode w))

/-- `f` is realised on encodings by a polynomial-time machine: some machine map
`g` satisfies `decode (g (encodeCNF φ)) = f φ` (read through `ofM`/`toM`). -/
def RealizedOnEncodings (f : CNF → CNF) : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ φ, ofM (decode (g (encodeCNF (toM φ)))) = f φ

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The schema instantiated with maps realised by machines on words gives the
machine obligation. -/
theorem isolationObligation_of_schema (h : IsolationObligationFor RealizedOnWords) :
    IsolationObligation := by
  obtain ⟨f, ⟨m, g, p, hm, hg⟩, hinto, hpres⟩ := h
  refine ⟨m, g, p, hm, fun w => ?_, fun w => bool_eq_of_iff ?_⟩
  · show AtMostOneSolution (ofM (decode (g w)))
    rw [hg]; exact hinto _
  · rw [sat_iff_ofM, sat_iff_ofM, hg]
    exact hpres _

/-- The machine obligation gives the schema instantiated with maps realised by
machines on encodings. -/
theorem schema_of_isolationObligation (h : IsolationObligation) :
    IsolationObligationFor RealizedOnEncodings := by
  obtain ⟨m, g, p, hm, hinto, hpres⟩ := h
  refine ⟨fun φ => ofM (decode (g (encodeCNF (toM φ)))), ⟨m, g, p, hm, fun _ => rfl⟩,
    fun φ => hinto _, fun φ => ?_⟩
  have h1 : Satisfiable φ ↔ SAT (encodeCNF (toM φ)) = true := by
    rw [sat_encode, ← satisfiable_ofM, ofM_toM]
  rw [h1, hpres, sat_iff_ofM]

/-! ### Non-vacuity: deciding on the promise is not trivial -/

/-- Pad a word into pairs `false, b`; such words decode to the empty formula. -/
def pad : Word → Word
  | [] => []
  | b :: w => false :: b :: pad w

def unpad : Word → Word
  | _ :: b :: r => b :: unpad r
  | _ => []

theorem unpad_pad (w : Word) : unpad (pad w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [pad, unpad, ih]

theorem decodeAux_pad (w : Word) (k : Nat) (cur : Machines.Clause) :
    Machines.decodeAux (pad w) k cur = [] := by
  induction w generalizing k cur with
  | nil => simp [pad, Machines.decodeAux]
  | cons b w ih => simp only [pad, Machines.decodeAux, ih]

/-- Every padded word lies in the Unique-SAT promise. -/
theorem uniquePromise_pad (w : Word) : UniquePromise (pad w) := by
  intro a b _ _ v hv
  simp only [decode, Machines.decode, decodeAux_pad, ofM, List.map_nil, vars] at hv
  exact absurd hv List.not_mem_nil

open Classical in
/-- **Non-vacuity.**  Not every language is decided on the Unique-SAT promise by
a machine (in any polynomial time bound): the promise contains all padded words,
and a diagonal language over them escapes every machine. -/
theorem not_forall_promise_class :
    ¬ ∀ L : Language, ∃ (d : Machine) (p : Polynomial), DecidesOn d p UniquePromise L := by
  intro hall
  obtain ⟨L0, hL0⟩ := exists_language_not_in_family encMachine
    (fun _ _ h => encMachine_injective h)
    (fun m w => decide (∃ t, Run m (initial (pad w)) t true))
  obtain ⟨d, p, hd⟩ := hall (fun w => L0 (unpad w))
  apply hL0 d
  funext w
  obtain ⟨t, b, _, hr, hb⟩ := hd (pad w) (uniquePromise_pad w)
  simp only [unpad_pad] at hb
  subst hb
  cases hL : L0 w with
  | true => rw [hL] at hr; exact decide_eq_true ⟨t, hr⟩
  | false =>
    rw [hL] at hr
    exact decide_eq_false (fun ⟨t', hr'⟩ => Bool.noConfusion (run_deterministic hr hr').2)

end Issue532.Idea32
