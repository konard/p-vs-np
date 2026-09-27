import proofs.experiments.issue532.lean.Machines

/-!
# Issue #532, Idea 26: separator consistency

Verdict: **refuted as a route (general theorem)** — separator-based
decomposition is exact only if *all* `2^|S|` separator states are tracked,
and no summary with fewer states is sound in general.

For a CNF written as `A ++ B` whose shared variables lie in a list `S`
(the *separator*), this file proves, for all `A`, `B`, `S`:

* `separator_sat_iff` — `A ++ B` is satisfiable iff some separator state
  `σ ∈ allBool |S|` (a Boolean vector indexed by `S`) is simultaneously
  realised by a model of `A` and by a model of `B`;
* `length_allBool`, `mem_allBool` — the enumeration of separator states has
  exactly `2^|S|` entries and contains every Boolean vector of length `|S|`;
* `separate_not_joint` — for every variable `x`, `[[x]]` and `[[¬x]]` are
  separately satisfiable but their union is not (so separator *agreement*
  cannot be dropped, already for `|S| = 1`);
* `equality_gadget` / `compatible_states_units` — for every duplicate-free
  separator `S` and all states `σ, τ` of length `|S|`, the unit-clause
  formulas `units S σ` and `units S τ` are each satisfiable, `units S σ` is
  compatible with exactly the one state `σ`, and the union is satisfiable iff
  `σ = τ`;
* `summary_must_be_injective` — hence any procedure that compresses the
  `A`-side state to a summary and decides the union from the summary and the
  `B`-side state must use a summary that is injective on all `2^|S|` states.

Consequently the separator method costs `2^|S| · (cost A + cost B)` in the
worst case; it is polynomial only when separators have logarithmic size, which
fails for expander-based hard formulas (linear separators).
See `../ideas/Idea26.md`.

Cost layer, in the shared machine model (`Machines`): `SepTree r φ` is a
recursive separator decomposition of `φ` with a total separator budget `r`
along every branch (so the primal graph has treewidth at most `2r`), and
`SepPromise k w` asks for it with `r = k * log₂ (|w|+1)`.  The named known
theorem `LogSeparatorSATInP` (separator-state dynamic programming is
polynomial on that promise) is a hypothesis, not mechanised.  The open
obligation `SATSeparatorReduction` asks for a `Complexity.Machine` mapping every
SAT instance, within a polynomial number of steps, to an equisatisfiable
instance with such a decomposition; `pEqualsNP_of_separatorReduction` derives
`PEqualsNP` from it, and `not_forall_separatorReduction` is the non-vacuity
check.
-/

namespace Issue532.Idea26

/-! ## CNF core (same as Idea 25) -/

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

theorem evalCNF_append (a : Assignment) (φ ψ : CNF) :
    evalCNF a (φ ++ ψ) = (evalCNF a φ && evalCNF a ψ) := by
  induction φ with
  | nil => simp [evalCNF]
  | cons c φ ih => simp [evalCNF, ih, Bool.and_assoc]

theorem evalClause_congr (a b : Assignment) (c : Clause)
    (h : ∀ v, v ∈ clauseVars c → a v = b v) : evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    have hl : a l.var = b l.var := h l.var (by simp [clauseVars])
    have hc : ∀ v, v ∈ clauseVars c → a v = b v := by
      intro v hv
      apply h v
      simp only [clauseVars, List.map_cons, List.mem_cons]
      exact Or.inr hv
    simp only [evalClause, evalLit, hl, ih hc]

theorem eval_congr (a b : Assignment) (φ : CNF)
    (h : ∀ v, v ∈ vars φ → a v = b v) : evalCNF a φ = evalCNF b φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have hc : ∀ v, v ∈ clauseVars c → a v = b v :=
      fun v hv => h v (by simp only [vars, List.mem_append]; exact Or.inl hv)
    have hφ : ∀ v, v ∈ vars φ → a v = b v :=
      fun v hv => h v (by simp only [vars, List.mem_append]; exact Or.inr hv)
    simp only [evalCNF, evalClause_congr a b c hc, ih hφ]

/-! ## Separator states -/

/-- All Boolean vectors of length `n`, `false`-first. -/
def allBool : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBool n).map (false :: ·) ++ (allBool n).map (true :: ·)

/-- The enumeration of separator states has exactly `2^n` entries. -/
theorem length_allBool (n : Nat) : (allBool n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allBool, ih, Nat.pow_succ]; omega

/-- The enumeration contains exactly the vectors of length `n`. -/
theorem mem_allBool (n : Nat) (σ : List Bool) : σ ∈ allBool n ↔ σ.length = n := by
  induction n generalizing σ with
  | zero =>
    cases σ with
    | nil => simp [allBool]
    | cons b σ => simp [allBool]
  | succ n ih =>
    cases σ with
    | nil => simp [allBool]
    | cons b σ =>
      cases b <;> simp [allBool, ih]

/-- The separator state of an assignment: its values on `S`. -/
def restrict (S : List Nat) (a : Assignment) : List Bool := S.map a

theorem restrict_length (S : List Nat) (a : Assignment) : (restrict S a).length = S.length := by
  simp [restrict]

theorem restrict_eq_agree (S : List Nat) (a b : Assignment)
    (h : restrict S a = restrict S b) : ∀ v, v ∈ S → a v = b v := by
  induction S with
  | nil => intro v hv; cases hv
  | cons s S ih =>
    simp only [restrict, List.map_cons, List.cons.injEq] at h
    intro v hv
    rcases List.mem_cons.mp hv with hv | hv
    · subst hv; exact h.1
    · exact ih h.2 v hv

/-- **Separator theorem.** If every variable shared by `A` and `B` lies in `S`,
then `A ++ B` is satisfiable iff some separator state `σ` (one of the
`2^|S|` entries of `allBool |S|`) is realised both by a model of `A` and by a
model of `B`. -/
theorem separator_sat_iff (A B : CNF) (S : List Nat)
    (hS : ∀ v, v ∈ vars A → v ∈ vars B → v ∈ S) :
    Satisfiable (A ++ B) ↔
      ∃ σ, σ ∈ allBool S.length ∧
        (∃ a, restrict S a = σ ∧ evalCNF a A = true) ∧
        (∃ b, restrict S b = σ ∧ evalCNF b B = true) := by
  constructor
  · rintro ⟨a, ha⟩
    rw [evalCNF_append, Bool.and_eq_true] at ha
    exact ⟨restrict S a, (mem_allBool _ _).mpr (restrict_length S a),
      ⟨a, rfl, ha.1⟩, ⟨a, rfl, ha.2⟩⟩
  · rintro ⟨σ, _, ⟨a, haσ, ha⟩, ⟨b, hbσ, hb⟩⟩
    have agree : ∀ v, v ∈ S → a v = b v :=
      restrict_eq_agree S a b (haσ.trans hbσ.symm)
    let c : Assignment := fun v => if v ∈ vars A then a v else b v
    refine ⟨c, ?_⟩
    have hcA : evalCNF c A = evalCNF a A :=
      eval_congr c a A (fun v hv => by simp [c, hv])
    have hcB : evalCNF c B = evalCNF b B := by
      apply eval_congr c b B
      intro v hv
      by_cases hvA : v ∈ vars A
      · simp only [c, hvA, ite_true]; exact agree v (hS v hvA hv)
      · simp [c, hvA]
    rw [evalCNF_append, hcA, hcB, ha, hb]
    rfl

/-! ## Separator agreement cannot be dropped -/

/-- **Countermodel family, `|S| = 1`.** For every variable `x`, `[[x]]` and
`[[¬x]]` are separately satisfiable but their union is not. -/
theorem separate_not_joint (x : Nat) :
    Satisfiable [[⟨x, true⟩]] ∧ Satisfiable [[⟨x, false⟩]] ∧
      ¬ Satisfiable ([[⟨x, true⟩]] ++ [[⟨x, false⟩]]) := by
  refine ⟨⟨fun _ => true, rfl⟩, ⟨fun _ => false, rfl⟩, ?_⟩
  rintro ⟨a, ha⟩
  cases h : a x <;> simp [evalCNF, evalClause, evalLit, h] at ha

/-! ## All `2^|S|` states are needed: the equality gadget -/

/-- Unit clauses fixing the variables of `S` to the values `σ`. -/
def units : List Nat → List Bool → CNF
  | s :: S, b :: σ => [⟨s, b⟩] :: units S σ
  | _, _ => []

theorem evalLit_unit (a : Assignment) (s : Nat) (b : Bool) :
    evalLit a ⟨s, b⟩ = true ↔ a s = b := by
  cases b <;> cases h : a s <;> simp [evalLit, h]

theorem units_eval (a : Assignment) (S : List Nat) (σ : List Bool)
    (hlen : σ.length = S.length) :
    evalCNF a (units S σ) = true ↔ restrict S a = σ := by
  induction S generalizing σ with
  | nil =>
    cases σ with
    | nil => simp [units, evalCNF, restrict]
    | cons b σ => simp at hlen
  | cons s S ih =>
    cases σ with
    | nil => simp at hlen
    | cons b σ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [units, evalCNF, evalClause, Bool.or_false, Bool.and_eq_true,
        evalLit_unit, ih σ hlen, restrict, List.map_cons, List.cons.injEq]

/-- Every state is realisable when the separator is duplicate-free. -/
theorem realizable (S : List Nat) (hS : S.Nodup) (σ : List Bool)
    (hlen : σ.length = S.length) : ∃ a, restrict S a = σ := by
  induction S generalizing σ with
  | nil =>
    cases σ with
    | nil => exact ⟨fun _ => false, rfl⟩
    | cons b σ => simp at hlen
  | cons s S ih =>
    cases σ with
    | nil => simp at hlen
    | cons b σ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hs : s ∉ S := (List.nodup_cons.mp hS).1
      obtain ⟨a, ha⟩ := ih (List.nodup_cons.mp hS).2 σ hlen
      refine ⟨fun v => if v = s then b else a v, ?_⟩
      simp only [restrict, List.map_cons, List.cons.injEq]
      refine ⟨by simp, ?_⟩
      rw [← ha]
      apply List.map_congr_left
      intro v hv
      have : v ≠ s := fun e => hs (e ▸ hv)
      simp [this]

/-- **Compatibility sets are singletons.** The formula `units S σ` is
compatible with the separator state `τ` iff `τ = σ`. -/
theorem compatible_states_units (S : List Nat) (hS : S.Nodup) (σ τ : List Bool)
    (hσ : σ.length = S.length) :
    (∃ a, restrict S a = τ ∧ evalCNF a (units S σ) = true) ↔ τ = σ := by
  constructor
  · rintro ⟨a, haτ, ha⟩
    rw [← haτ]
    exact (units_eval a S σ hσ).mp ha
  · intro h
    subst h
    obtain ⟨a, ha⟩ := realizable S hS τ hσ
    exact ⟨a, ha, (units_eval a S τ hσ).mpr ha⟩

/-- **Equality gadget.** For duplicate-free `S` and states `σ, τ` of length
`|S|`: both sides are satisfiable, yet the union is satisfiable iff `σ = τ`.
Any separator summary of the left side that identifies two different states
therefore answers some instance wrongly; all `2^|S|` states are needed. -/
theorem equality_gadget (S : List Nat) (hS : S.Nodup) (σ τ : List Bool)
    (hσ : σ.length = S.length) (hτ : τ.length = S.length) :
    Satisfiable (units S σ) ∧ Satisfiable (units S τ) ∧
      (Satisfiable (units S σ ++ units S τ) ↔ σ = τ) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := realizable S hS σ hσ
    exact ⟨a, (units_eval a S σ hσ).mpr ha⟩
  · obtain ⟨a, ha⟩ := realizable S hS τ hτ
    exact ⟨a, (units_eval a S τ hτ).mpr ha⟩
  · constructor
    · rintro ⟨a, ha⟩
      rw [evalCNF_append, Bool.and_eq_true] at ha
      exact ((units_eval a S σ hσ).mp ha.1).symm.trans ((units_eval a S τ hτ).mp ha.2)
    · intro h
      subst h
      obtain ⟨a, ha⟩ := realizable S hS σ hσ
      refine ⟨a, ?_⟩
      rw [evalCNF_append, (units_eval a S σ hσ).mpr ha]
      rfl

/-- **No lossy summary.** Suppose a procedure compresses the `A`-side state
`σ` to a summary `summ σ` and then decides `units S σ ++ units S τ` from the
summary and `τ` alone, via `D`.  If `D` is correct on all pairs of states of
length `|S|`, then `summ` is injective on those states, i.e. it must
distinguish all `2^|S|` of them. -/
theorem summary_must_be_injective {β : Type} (S : List Nat) (hS : S.Nodup)
    (summ : List Bool → β) (D : β → List Bool → Bool)
    (hD : ∀ σ τ, σ.length = S.length → τ.length = S.length →
      (D (summ σ) τ = true ↔ Satisfiable (units S σ ++ units S τ)))
    (σ τ : List Bool) (hσ : σ.length = S.length) (hτ : τ.length = S.length)
    (hsum : summ σ = summ τ) : σ = τ := by
  have h1 : D (summ σ) σ = true := (hD σ σ hσ hσ).mpr ((equality_gadget S hS σ σ hσ hσ).2.2.mpr rfl)
  rw [hsum] at h1
  exact ((equality_gadget S hS τ σ hτ hσ).2.2.mp ((hD τ σ hτ hσ).mp h1)).symm


/-! ## The one-level schema -/

/-- Schema for (Sep), one level, over a caller-supplied class `PolyTime` of maps
and a bound `w`: a map in `PolyTime` sending every CNF to an equisatisfiable
split `A ++ B` whose shared variables lie in a separator `S` of length at most
`w |φ|`.  `PolyTime` is a free parameter, so the schema carries no running-time
content; the machine version is `SATSeparatorReduction` below. -/
def SeparatorObligationFor (PolyTime : (CNF → CNF × CNF × List Nat) → Prop) (w : Nat → Nat) :
    Prop :=
  ∃ f : CNF → CNF × CNF × List Nat, PolyTime f ∧ ∀ φ,
    (∀ v, v ∈ vars (f φ).1 → v ∈ vars (f φ).2.1 → v ∈ (f φ).2.2) ∧
    (f φ).2.2.length ≤ w φ.length ∧
    (Satisfiable φ ↔ Satisfiable ((f φ).1 ++ (f φ).2.1))

/-- Conditional theorem: under the schema, satisfiability of every CNF is
decided by the `2 ^ w(|φ|)` separator states. -/
theorem separator_obligation_states (PolyTime : (CNF → CNF × CNF × List Nat) → Prop)
    (w : Nat → Nat) (h : SeparatorObligationFor PolyTime w) :
    ∃ f : CNF → CNF × CNF × List Nat, PolyTime f ∧ ∀ φ,
      (f φ).2.2.length ≤ w φ.length ∧
      (Satisfiable φ ↔ ∃ σ, σ ∈ allBool (f φ).2.2.length ∧
        (∃ a, restrict (f φ).2.2 a = σ ∧ evalCNF a (f φ).1 = true) ∧
        (∃ b, restrict (f φ).2.2 b = σ ∧ evalCNF b (f φ).2.1 = true)) := by
  obtain ⟨f, hf, hall⟩ := h
  refine ⟨f, hf, fun φ => ?_⟩
  obtain ⟨hS, hw, hp⟩ := hall φ
  exact ⟨hw, hp.trans (separator_sat_iff _ _ _ hS)⟩

/-! ## Recursive separator decompositions -/

/-- `SepTree r φ`: `φ` is either a leaf with at most `r` variable occurrences, or
a concatenation `A ++ B` whose shared variables lie in a separator `S` with
`|S| ≤ r`, both halves decomposed recursively with the remaining budget
`r - |S|`.  Along every branch the separators add up to at most `r`, so taking
as bag of a node the variables of its formula that lie in the separators on its
path (plus the leaf variables at leaves) gives a tree decomposition of the
primal graph of width below `2r`. -/
inductive SepTree : Nat → CNF → Prop
  | leaf {r : Nat} {φ : CNF} : (vars φ).length ≤ r → SepTree r φ
  | split {r : Nat} {A B : CNF} (S : List Nat) :
      (∀ v, v ∈ vars A → v ∈ vars B → v ∈ S) → S.length ≤ r →
      SepTree (r - S.length) A → SepTree (r - S.length) B → SepTree r (A ++ B)

/-- A separator tree exposes, at its root, either a small leaf or one exact
separator step with at most `2^r` states (`separator_sat_iff`). -/
theorem sepTree_root {r : Nat} {φ : CNF} (h : SepTree r φ) :
    (vars φ).length ≤ r ∨
      ∃ (A B : CNF) (S : List Nat), φ = A ++ B ∧ S.length ≤ r ∧
        (Satisfiable φ ↔ ∃ σ, σ ∈ allBool S.length ∧
          (∃ a, restrict S a = σ ∧ evalCNF a A = true) ∧
          (∃ b, restrict S b = σ ∧ evalCNF b B = true)) := by
  cases h with
  | leaf hl => exact Or.inl hl
  | split S hS hlen _ _ => exact Or.inr ⟨_, _, S, rfl, hlen, separator_sat_iff _ _ S hS⟩

/-- A separator tree with budget `r` also has every larger budget. -/
theorem sepTree_mono {r φ} (h : SepTree r φ) : ∀ {r'}, r ≤ r' → SepTree r' φ := by
  induction h with
  | leaf hl => exact fun hr => SepTree.leaf (Nat.le_trans hl hr)
  | split S hS hlen _ _ ihA ihB =>
    intro r' hr
    exact SepTree.split S hS (Nat.le_trans hlen hr) (ihA (by omega)) (ihB (by omega))

/-! ## The machine model -/

open Complexity

/-- A CNF of the shared machine model, read in this file's syntax. -/
def ofM (φ : Machines.CNF) : CNF := φ.map (List.map fun l => ⟨l.var, l.pos⟩)

theorem evalClause_ofM (a : Assignment) (C : Machines.Clause) :
    evalClause a (C.map fun l => (⟨l.var, l.pos⟩ : Lit)) = Machines.evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [List.map_cons, evalClause, Machines.evalClause, ih, evalLit, Machines.evalLit]
    cases l.pos <;> cases a l.var <;> rfl

theorem evalCNF_ofM (a : Assignment) (φ : Machines.CNF) :
    evalCNF a (ofM φ) = Machines.evalCNF a φ := by
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    simp only [ofM, List.map_cons, evalCNF, Machines.evalCNF] at ih ⊢
    rw [evalClause_ofM, ih]

/-- The shared language `SAT` is satisfiability in this file's syntax. -/
theorem sat_ofM (w : Word) : Machines.SAT w = true ↔ Satisfiable (ofM (Machines.decode w)) := by
  rw [Machines.sat_iff]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [evalCNF_ofM]; exact ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← evalCNF_ofM]; exact ha⟩

/-- The word `w` encodes a CNF with a separator tree of budget
`k * log₂ (|w|+1)` (logarithmic treewidth). -/
def SepPromise (k : Nat) (w : Word) : Prop :=
  SepTree (k * Nat.log2 (w.length + 1)) (ofM (Machines.decode w))

/-- **Known theorem, not mechanised here.** For each fixed `k`, SAT is decided in
polynomial time on the promise `SepPromise k`.  The promise gives primal
treewidth below `2k·log₂(|w|+1)` (see `SepTree`); a tree decomposition of width
`O(k log |w|)` is found in time `2^{O(k log |w|)}·poly = poly` (Robertson–
Seymour, Graph Minors XIII, JCTB 63, 1995; Bodlaender, Drange, Dregi, Fomin,
Lokshtanov, Pilipczuk, SIAM J. Comput. 45(2), 2016), and dynamic programming
over the separator states of the bags decides satisfiability in time
`2^{O(tw)}·poly` (Alekhnovich–Razborov, FOCS 2002; Samer–Szeider, J. Discrete
Algorithms 8(1), 2010).  What is not mechanised is the `Complexity.Machine`
carrying this out. -/
def LogSeparatorSATInP : Prop :=
  ∀ k, ∃ (d : Machine) (p : Polynomial), Machines.DecidesOn d p (SepPromise k) Machines.SAT

/-- A polynomial-time machine reduction of `L` to SAT instances with a
logarithmic separator tree. -/
def SeparatorReduction (L : Language) (k : Nat) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
    ∀ x, SepPromise k (f x) ∧ L x = Machines.SAT (f x)

/-- **Open obligation** ((Sep) with recursion, in the machine model).  For some
`k`, a `Complexity.Machine` maps every word `x`, within a polynomial number of
`Run` steps, to a word `f x` with `SAT x = SAT (f x)` whose CNF has a separator
tree with budget `k * log₂ (|f x|+1)`. -/
def SATSeparatorReduction : Prop := ∃ k, SeparatorReduction Machines.SAT k

/-- Transfer: a separator reduction and the separator-state decider put `L` in P. -/
theorem inP_of_separatorReduction {L : Language} {k : Nat} (hS : LogSeparatorSATInP)
    (h : SeparatorReduction L k) : InP L := by
  obtain ⟨m, f, p, hm, hf⟩ := h
  obtain ⟨d, p', hd⟩ := hS k
  exact Machines.inP_of_promise_reduction hm (fun x => (hf x).1) (fun x => (hf x).2) hd

/-- **Conditional theorem.** The open obligation and the known separator-state
decider put SAT in P. -/
theorem inP_sat_of_separatorReduction (hS : LogSeparatorSATInP)
    (h : SATSeparatorReduction) : InP Machines.SAT := by
  obtain ⟨k, hk⟩ := h
  exact inP_of_separatorReduction hS hk

/-- **Conditional theorem.** With the hardness half of Cook–Levin, the open
obligation gives P = NP. -/
theorem pEqualsNP_of_separatorReduction (hard : Machines.SATHard)
    (hS : LogSeparatorSATInP) (h : SATSeparatorReduction) : PEqualsNP :=
  Machines.pEqualsNP_of_inP_sat hard (inP_sat_of_separatorReduction hS h)

/-- Machine analogue of `separator_obligation_states`: under the obligation,
every reduced instance is a small leaf or splits exactly over at most
`2^(k log₂(|f x|+1))` separator states, and `SAT x` is its satisfiability. -/
theorem separatorReduction_states (h : SATSeparatorReduction) :
    ∃ (k : Nat) (m : Machine) (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧
      ∀ x, (Machines.SAT x = true ↔ Satisfiable (ofM (Machines.decode (f x)))) ∧
        ((vars (ofM (Machines.decode (f x)))).length ≤ k * Nat.log2 ((f x).length + 1) ∨
          ∃ (A B : CNF) (S : List Nat), ofM (Machines.decode (f x)) = A ++ B ∧
            S.length ≤ k * Nat.log2 ((f x).length + 1) ∧
            (Satisfiable (A ++ B) ↔ ∃ σ, σ ∈ allBool S.length ∧
              (∃ a, restrict S a = σ ∧ evalCNF a A = true) ∧
              (∃ b, restrict S b = σ ∧ evalCNF b B = true))) := by
  obtain ⟨k, m, f, p, hm, hf⟩ := h
  refine ⟨k, m, f, p, hm, fun x => ⟨by rw [(hf x).2, sat_ofM], ?_⟩⟩
  rcases sepTree_root (hf x).1 with hl | ⟨A, B, S, he, hl, hs⟩
  · exact Or.inl hl
  · exact Or.inr ⟨A, B, S, he, hl, he ▸ hs⟩

/-- The language obtained by running the machine `m` as a reduction into `M`. -/
noncomputable def viaMachine (M : Language) (m : Machine) : Language :=
  fun x => @decide (∃ (f : Word → Word) (p : Polynomial), Machines.Computes m f p ∧ M (f x) = true)
    (Classical.propDecidable _)

theorem viaMachine_eq {M : Language} {m : Machine} {f : Word → Word} {p : Polynomial}
    (hm : Machines.Computes m f p) : viaMachine M m = fun x => M (f x) := by
  funext x
  unfold viaMachine
  cases h : M (f x) with
  | true => exact @decide_eq_true _ (Classical.propDecidable _) ⟨f, p, hm, h⟩
  | false =>
    apply @decide_eq_false _ (Classical.propDecidable _)
    rintro ⟨g, q, hg, hgx⟩
    rw [← Machines.computes_unique hm hg, h] at hgx
    cases hgx

/-- **Cantor over machines.** For every target language `M` some language has no
machine map `f` with `L x = M (f x)`. -/
theorem exists_not_reducible (M : Language) :
    ∃ L : Language, ∀ (m : Machine) (f : Word → Word) (p : Polynomial),
      Machines.Computes m f p → ∃ x, L x ≠ M (f x) := by
  obtain ⟨L, hL⟩ := Machines.exists_language_not_in_family Machines.encMachine
    (fun _ _ h => Machines.encMachine_injective h) (viaMachine M)
  refine ⟨L, fun m f p hm => Classical.byContradiction fun hno => hL m ?_⟩
  rw [viaMachine_eq hm]
  funext x
  exact Classical.byContradiction fun hx => hno ⟨x, fun h => hx h.symm⟩

/-- **Non-vacuity.** For every `k`, some language has no separator reduction, so
`SeparatorReduction Machines.SAT k` is a statement about SAT. -/
theorem not_forall_separatorReduction (k : Nat) :
    ¬ ∀ L : Language, SeparatorReduction L k := by
  intro h
  obtain ⟨L, hL⟩ := exists_not_reducible Machines.SAT
  obtain ⟨m, f, p, hm, hf⟩ := h L
  obtain ⟨x, hx⟩ := hL m f p hm
  exact hx (hf x).2

end Issue532.Idea26
