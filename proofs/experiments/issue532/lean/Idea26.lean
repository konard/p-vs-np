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


/-! ## The open obligation -/

/-- The open obligation (Sep), one level: a map in the class `PolyTime` sending
every CNF to an equisatisfiable split `A ++ B` whose shared variables lie in a
separator `S` of length at most `w |φ|`. -/
def SeparatorObligation (PolyTime : (CNF → CNF × CNF × List Nat) → Prop) (w : Nat → Nat) :
    Prop :=
  ∃ f : CNF → CNF × CNF × List Nat, PolyTime f ∧ ∀ φ,
    (∀ v, v ∈ vars (f φ).1 → v ∈ vars (f φ).2.1 → v ∈ (f φ).2.2) ∧
    (f φ).2.2.length ≤ w φ.length ∧
    (Satisfiable φ ↔ Satisfiable ((f φ).1 ++ (f φ).2.1))

/-- Conditional theorem: under the obligation, satisfiability of every CNF is
decided by the `2 ^ w(|φ|)` separator states. -/
theorem separator_obligation_states (PolyTime : (CNF → CNF × CNF × List Nat) → Prop)
    (w : Nat → Nat) (h : SeparatorObligation PolyTime w) :
    ∃ f : CNF → CNF × CNF × List Nat, PolyTime f ∧ ∀ φ,
      (f φ).2.2.length ≤ w φ.length ∧
      (Satisfiable φ ↔ ∃ σ, σ ∈ allBool (f φ).2.2.length ∧
        (∃ a, restrict (f φ).2.2 a = σ ∧ evalCNF a (f φ).1 = true) ∧
        (∃ b, restrict (f φ).2.2 b = σ ∧ evalCNF b (f φ).2.1 = true)) := by
  obtain ⟨f, hf, hall⟩ := h
  refine ⟨f, hf, fun φ => ?_⟩
  obtain ⟨hS, hw, hp⟩ := hall φ
  exact ⟨hw, hp.trans (separator_sat_iff _ _ _ hS)⟩

end Issue532.Idea26
