/-!
# Issue #532, Idea 36: exact relaxation and rounding

Relax an integer program to a fractional one, solve the relaxation, round.

Model: half-unit vertex cover. A fractional vertex assignment `x : Nat → Nat`
counts in halves (`0, 1, 2` mean `0, 1/2, 1`); it is a fractional cover of an
edge list if `x u + x v ≥ 2` on every edge. The LP value in halves is
`halfSum vs x = Σ_{v ∈ vs} x v`.

Main results:

* `round_is_cover`: threshold rounding `R(v) := (x v ≥ 1)` of any fractional
  cover is a vertex cover.
* `round_cost_le`: `|R| ≤ halfSum vs x`, i.e. `cost(R) ≤ 2 · LP`.
* `round_two_approx`: rounding an optimal fractional cover gives a cover of
  size at most twice every integral cover.
* `complete_graph_gap`, `no_exact_rounding`: on the complete graph with `n`
  vertices the all-halves assignment is a fractional cover of LP value `n/2`,
  while every vertex cover has at least `n - 1` vertices; for `n ≥ 3` no
  rounding can be exact for this relaxation.
* `exact_rounding_optimal`, `exact_rounding_decides`: in general, an exact
  rounding of a relaxation produces optimal solutions and so decides the
  decision version. `ExactRoundingObligation` records the open obligation.
* `tested`: the conditional witness-transfer lemma (a sound rounding map turns a
  relaxed witness into a discrete witness).
-/

namespace Issue532.Idea36

/-! ## Conditional witness transfer -/

/-- **Witness transfer.** A rounding map that is sound on relaxed solutions turns
any relaxed witness into a discrete witness. -/
theorem tested {Discrete Relaxed : Type}
    (feasible : Discrete → Prop) (relaxed : Relaxed → Prop)
    (round : Relaxed → Discrete)
    (soundRound : ∀ y, relaxed y → feasible (round y)) :
    (∃ y, relaxed y) → ∃ x, feasible x := by
  rintro ⟨y, hy⟩
  exact ⟨round y, soundRound y hy⟩

/-! ## Half-unit vertex cover -/

/-- A fractional cover in half units: every edge has total weight at least `2` (one unit). -/
def FracCover (edges : List (Nat × Nat)) (x : Nat → Nat) : Prop :=
  ∀ e ∈ edges, 2 ≤ x e.1 + x e.2

/-- An integral vertex cover given by its indicator function. -/
def IsCover (edges : List (Nat × Nat)) (C : Nat → Bool) : Prop :=
  ∀ e ∈ edges, C e.1 = true ∨ C e.2 = true

/-- Threshold rounding: keep every vertex with weight at least one half. -/
def round (x : Nat → Nat) (v : Nat) : Bool := decide (1 ≤ x v)

/-- Number of chosen vertices among the vertex list `vs`. -/
def cost (vs : List Nat) (C : Nat → Bool) : Nat := (vs.filter C).length

/-- LP value in half units. -/
def halfSum (vs : List Nat) (x : Nat → Nat) : Nat := (vs.map x).sum

/-- **Rounding is feasible.** Threshold rounding of a fractional cover is a vertex cover. -/
theorem round_is_cover (edges : List (Nat × Nat)) (x : Nat → Nat)
    (h : FracCover edges x) : IsCover edges (round x) := by
  intro e he
  have hsum := h e he
  by_cases h1 : 1 ≤ x e.1
  · exact Or.inl (by simp [round, h1])
  · exact Or.inr (by simp [round]; omega)

/-- **Rounding costs at most twice the LP.** `|R| ≤ Σ x` in half units. -/
theorem round_cost_le (vs : List Nat) (x : Nat → Nat) :
    cost vs (round x) ≤ halfSum vs x := by
  induction vs with
  | nil => simp [cost, halfSum]
  | cons v vs ih =>
    simp only [cost, halfSum] at ih
    by_cases h : 1 ≤ x v
    · simp [cost, halfSum, round, h]
      omega
    · simp [cost, halfSum, round, h]
      omega

/-- An integral cover viewed as a fractional one (weight `2` = one unit on chosen vertices). -/
def toFrac (C : Nat → Bool) (v : Nat) : Nat := if C v then 2 else 0

theorem toFrac_cover (edges : List (Nat × Nat)) (C : Nat → Bool)
    (h : IsCover edges C) : FracCover edges (toFrac C) := by
  intro e he
  rcases h e he with h1 | h1 <;> simp [toFrac, h1] <;> split <;> omega

theorem halfSum_toFrac (vs : List Nat) (C : Nat → Bool) :
    halfSum vs (toFrac C) = 2 * cost vs C := by
  induction vs with
  | nil => simp [halfSum, cost]
  | cons v vs ih =>
    simp only [halfSum, cost] at ih
    cases hv : C v <;> simp [halfSum, cost, toFrac, hv, ih] <;> omega

/-- **Factor-2 approximation.** If `x` is an optimal fractional cover, the rounded
set is a vertex cover no larger than twice any vertex cover. -/
theorem round_two_approx (vs : List Nat) (edges : List (Nat × Nat)) (x : Nat → Nat)
    (hx : FracCover edges x)
    (hopt : ∀ y, FracCover edges y → halfSum vs x ≤ halfSum vs y)
    (C : Nat → Bool) (hC : IsCover edges C) :
    IsCover edges (round x) ∧ cost vs (round x) ≤ 2 * cost vs C := by
  refine ⟨round_is_cover edges x hx, ?_⟩
  have h1 := round_cost_le vs x
  have h2 := hopt (toFrac C) (toFrac_cover edges C hC)
  rw [halfSum_toFrac] at h2
  omega

/-! ## Integrality gap on complete graphs -/

/-- All edges `(v, w)` with `v` before `w` in the list. -/
def completeEdges : List Nat → List (Nat × Nat)
  | [] => []
  | v :: vs => vs.map (fun w => (v, w)) ++ completeEdges vs

theorem cost_all_true (vs : List Nat) (C : Nat → Bool) (h : ∀ w ∈ vs, C w = true) :
    cost vs C = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hv : C v = true := h v (List.mem_cons_self ..)
    have ih' := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [cost] at ih'
    simp [cost, hv, ih']

/-- **Integral lower bound on complete graphs.** Every vertex cover of the complete
graph on `vs` misses at most one vertex. -/
theorem complete_cover_cost (vs : List Nat) (C : Nat → Bool)
    (hC : IsCover (completeEdges vs) C) : vs.length ≤ cost vs C + 1 := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hrest : IsCover (completeEdges vs) C := fun e he =>
      hC e (by simp only [completeEdges, List.mem_append]; exact Or.inr he)
    have ih' := ih hrest
    simp only [cost] at ih'
    cases hv : C v with
    | true =>
      simp [cost, hv]
      omega
    | false =>
      have hall : ∀ w ∈ vs, C w = true := by
        intro w hw
        have hmem : (v, w) ∈ completeEdges (v :: vs) := by
          simp only [completeEdges, List.mem_append, List.mem_map]
          exact Or.inl ⟨w, hw, rfl⟩
        rcases hC _ hmem with h | h
        · simp [hv] at h
        · exact h
      have := cost_all_true vs C hall
      simp only [cost] at this
      simp [cost, hv, this]

theorem halfSum_one (vs : List Nat) : halfSum vs (fun _ => 1) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [halfSum] at ih
    simp [halfSum, ih]
    omega

/-- **Integrality gap.** On the complete graph with `n` vertices, the all-halves
assignment is a fractional cover of value `n/2` (that is, `n` in half units), while
every vertex cover has at least `n - 1` vertices. -/
theorem complete_graph_gap (vs : List Nat) :
    FracCover (completeEdges vs) (fun _ => 1) ∧
    halfSum vs (fun _ => 1) = vs.length ∧
    ∀ C, IsCover (completeEdges vs) C → vs.length ≤ cost vs C + 1 :=
  ⟨fun _ _ => Nat.le_refl 2, halfSum_one vs, complete_cover_cost vs⟩

/-- **No exact rounding for this relaxation.** For `n ≥ 3` there is a fractional cover
whose LP value is strictly below the value of every integral cover. -/
theorem no_exact_rounding (vs : List Nat) (h3 : 3 ≤ vs.length) :
    ∃ x, FracCover (completeEdges vs) x ∧
      ∀ C, IsCover (completeEdges vs) C → halfSum vs x < 2 * cost vs C := by
  refine ⟨fun _ => 1, fun _ _ => Nat.le_refl 2, ?_⟩
  intro C hC
  have h1 := complete_cover_cost vs C hC
  rw [halfSum_one]
  omega

/-! ## Exact rounding in general -/

/-- `lp` is a relaxation bound: it never exceeds the cost of a feasible solution. -/
def Relaxation {Inst Sol : Type} (feasible : Inst → Sol → Prop) (cost : Inst → Sol → Nat)
    (lp : Inst → Nat) : Prop :=
  ∀ I s, feasible I s → lp I ≤ cost I s

/-- An exact rounding: it always returns a feasible solution whose cost equals the LP bound. -/
def ExactRounding {Inst Sol : Type} (feasible : Inst → Sol → Prop) (cost : Inst → Sol → Nat)
    (lp : Inst → Nat) (rnd : Inst → Sol) : Prop :=
  ∀ I, feasible I (rnd I) ∧ cost I (rnd I) ≤ lp I

/-- **Exact rounding gives optimal solutions.** -/
theorem exact_rounding_optimal {Inst Sol : Type} (feasible : Inst → Sol → Prop)
    (cost : Inst → Sol → Nat) (lp : Inst → Nat) (rnd : Inst → Sol)
    (hrel : Relaxation feasible cost lp) (hex : ExactRounding feasible cost lp rnd) :
    ∀ I s, feasible I s → cost I (rnd I) ≤ cost I s :=
  fun I s hs => Nat.le_trans (hex I).2 (hrel I s hs)

/-- **Exact rounding decides the decision version** `∃ s, feasible I s ∧ cost I s ≤ k`. -/
theorem exact_rounding_decides {Inst Sol : Type} (feasible : Inst → Sol → Prop)
    (cost : Inst → Sol → Nat) (lp : Inst → Nat) (rnd : Inst → Sol)
    (hrel : Relaxation feasible cost lp) (hex : ExactRounding feasible cost lp rnd) :
    ∀ I k, (∃ s, feasible I s ∧ cost I s ≤ k) ↔ cost I (rnd I) ≤ k := by
  intro I k
  constructor
  · rintro ⟨s, hs, hk⟩
    exact Nat.le_trans (exact_rounding_optimal feasible cost lp rnd hrel hex I s hs) hk
  · intro hk
    exact ⟨rnd I, (hex I).1, hk⟩

/-- **Open obligation.** A relaxation of an NP-hard integer program together with a
polynomial-time exact rounding. By `exact_rounding_decides`, meeting it for an NP-hard
problem (with `PolyTime` the real polynomial-time predicate) would give P = NP. -/
def ExactRoundingObligation {Inst Sol : Type} (PolyTime : (Inst → Sol) → Prop)
    (feasible : Inst → Sol → Prop) (cost : Inst → Sol → Nat) (lp : Inst → Nat) : Prop :=
  Relaxation feasible cost lp ∧ ∃ rnd, PolyTime rnd ∧ ExactRounding feasible cost lp rnd

/-- Triangle check: LP value `3/2` (3 halves) against integral optimum `2`. -/
example : halfSum [0, 1, 2] (fun _ => 1) = 3 ∧ cost [0, 1, 2] (round (fun _ => 1)) = 3 := by
  decide

end Issue532.Idea36
