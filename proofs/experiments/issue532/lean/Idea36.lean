import proofs.experiments.issue532.lean.Machines

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
  decision version. `ExactRoundingObligationFor` is the generic schema (free
  `PolyTime`, `feasible`, `cost`, `lp`).
* Over the shared machine model (`Complexity.Machine`, time = step count of
  `Complexity.Run`), vertex-cover instances are words (`budgetOf`, `edgesOf`,
  `verticesOf`; a certificate cover is read by `coverOf`). The open obligation
  `ExactRoundingObligation` asks for a polynomial-time machine map that keeps
  the instance and appends an optimal vertex cover.
  `exactRoundingObligation_iff_schema` shows it is exactly the schema
  instantiated with machine-computed roundings and some relaxation bound.
  `exactRounding_inP` and `exactRounding_gives_pEqualsNP` turn it into
  `InP VC` and `PEqualsNP` under the named known theorems `CoverCheckInP` and
  `VCHard`.

Verdict: correct tool, insufficient alone. Exact rounding is impossible for
the half-integral relaxation (`no_exact_rounding`); for any relaxation it is
equivalent to computing optimal covers, which is the open obligation above.
Nothing here proves or refutes P = NP.
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

/-- Generic schema (free `PolyTime`, `feasible`, `cost` and `lp`, not a machine
model): a relaxation bound together with an exact rounding in the class
`PolyTime`. By `exact_rounding_decides`, meeting it for an NP-hard problem with
`PolyTime` the real polynomial-time class would give P = NP; the machine
instance for vertex cover is `ExactRoundingObligation` below. -/
def ExactRoundingObligationFor {Inst Sol : Type} (PolyTime : (Inst → Sol) → Prop)
    (feasible : Inst → Sol → Prop) (cost : Inst → Sol → Nat) (lp : Inst → Nat) : Prop :=
  Relaxation feasible cost lp ∧ ∃ rnd, PolyTime rnd ∧ ExactRounding feasible cost lp rnd

/-- Triangle check: LP value `3/2` (3 halves) against integral optimum `2`. -/
example : halfSum [0, 1, 2] (fun _ => 1) = 3 ∧ cost [0, 1, 2] (round (fun _ => 1)) = 3 := by
  decide

/-! ## Vertex cover on the shared machine model

A word is read as a list of unary numbers (`true^k false` is `k`). The list
`k, e, a₁, b₁, …, a_e, b_e, c₀, c₁, …` is the instance "is there a vertex cover
of the edges `(a₁, b₁), …, (a_e, b_e)` with at most `k` vertices", and the
trailing numbers `c₀, c₁, …` (if any) are a candidate cover: vertex `v` is
chosen iff `c_v ≠ 0`. The vertices are `0, …, vbound - 1`, where `vbound`
exceeds every endpoint. -/

open Complexity
open Issue532.Machines (Computes PolyReduces NPHard inP_of_reduces exists_not_inP)

def natsAux : Word → Nat → List Nat
  | [], _ => []
  | true :: r, k => natsAux r (k + 1)
  | false :: r, k => k :: natsAux r 0

/-- The unary numbers of a word. -/
def nats (w : Word) : List Nat := natsAux w 0

/-- Encode a list of numbers in unary. -/
def encNats : List Nat → Word
  | [] => []
  | k :: r => List.replicate k true ++ false :: encNats r

def toPairs : List Nat → List (Nat × Nat)
  | a :: b :: r => (a, b) :: toPairs r
  | _ => []

/-- One more than the largest endpoint. -/
def vbound : List (Nat × Nat) → Nat
  | [] => 0
  | e :: r => max (max (e.1 + 1) (e.2 + 1)) (vbound r)

/-- The budget `k` of the instance. -/
def budgetOf (w : Word) : Nat := (nats w).headD 0

/-- The edges of the instance. -/
def edgesOf (w : Word) : List (Nat × Nat) :=
  toPairs (((nats w).drop 2).take (2 * (nats w).getD 1 0))

/-- The vertices `0, …, vbound - 1` of the instance. -/
def verticesOf (w : Word) : List Nat := List.range (vbound (edgesOf w))

/-- The candidate cover carried after the instance. -/
def coverOf (w : Word) (v : Nat) : Bool :=
  ((nats w).drop (2 + 2 * (nats w).getD 1 0)).getD v 0 != 0

/-- The triangle with budget `2`, and the cover `{1, 2}` appended. -/
example : budgetOf (encNats [2, 3, 0, 1, 1, 2, 0, 2]) = 2 ∧
    edgesOf (encNats [2, 3, 0, 1, 1, 2, 0, 2]) = [(0, 1), (1, 2), (0, 2)] ∧
    verticesOf (encNats [2, 3, 0, 1, 1, 2, 0, 2]) = [0, 1, 2] ∧
    (coverOf (encNats [2, 3, 0, 1, 1, 2, 0, 2, 0, 1, 1]) 0,
      coverOf (encNats [2, 3, 0, 1, 1, 2, 0, 2, 0, 1, 1]) 1,
      coverOf (encNats [2, 3, 0, 1, 1, 2, 0, 2, 0, 1, 1]) 2) = (false, true, true) := by
  decide

open Classical in
/-- The vertex-cover language: the instance has a cover within its budget. -/
noncomputable def VC : Language := fun w =>
  decide (∃ C, IsCover (edgesOf w) C ∧ cost (verticesOf w) C ≤ budgetOf w)

open Classical in
/-- The certificate check: the appended candidate is a cover within the budget. -/
noncomputable def CoverCheck : Language := fun u =>
  decide (IsCover (edgesOf u) (coverOf u) ∧ cost (verticesOf u) (coverOf u) ≤ budgetOf u)

/-- **Known theorem, not mechanised here.** Checking a proposed vertex cover
against the budget takes polynomial time: this is the certificate check that
puts vertex cover in NP (R. M. Karp, "Reducibility among combinatorial
problems", 1972; Garey–Johnson, *Computers and Intractability*, 1979, §3.1).
With unary numbers the check is a linear scan per edge. -/
def CoverCheckInP : Prop := InP CoverCheck

/-- **Known theorem, not mechanised here.** Vertex cover is NP-hard (Karp 1972,
via SAT ≤ 3-SAT ≤ CLIQUE ≤ VERTEX COVER; Garey–Johnson 1979, Theorem 3.3). The
unary encoding above is polynomially related to the standard one, since vertex
names and the budget are at most the number of vertices. -/
def VCHard : Prop := NPHard VC

/-- `C` is a minimum vertex cover of `edges` on the vertex list `vs`. -/
def OptimalCover (edges : List (Nat × Nat)) (vs : List Nat) (C : Nat → Bool) : Prop :=
  IsCover edges C ∧ ∀ C', IsCover edges C' → cost vs C ≤ cost vs C'

/-- **Open obligation** (exact rounding for vertex cover, machine model). A
polynomial-time machine map `g` (`Computes m g p`: the step count of the run is
at most `p.eval |w|`) that keeps the instance of `w` and appends an optimal
vertex cover. By `exactRoundingObligation_iff_schema` this is exactly an exact
rounding, computed by a machine, of some relaxation bound. -/
def ExactRoundingObligation : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ w, budgetOf (g w) = budgetOf w ∧ edgesOf (g w) = edgesOf w ∧
      OptimalCover (edgesOf w) (verticesOf w) (coverOf (g w))

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **Conditional theorem.** The obligation reduces vertex cover to the
certificate check by a polynomial-time machine. -/
theorem exactRounding_reduces (h : ExactRoundingObligation) : PolyReduces VC CoverCheck := by
  obtain ⟨m, g, p, hm, hg⟩ := h
  refine ⟨m, g, p, hm, fun w => bool_eq_of_iff ?_⟩
  obtain ⟨hb, he, hcov, hopt⟩ := hg w
  have hv : verticesOf (g w) = verticesOf w := by simp only [verticesOf, he]
  simp only [VC, CoverCheck, decide_eq_true_eq, hb, he, hv]
  constructor
  · rintro ⟨C, hC, hk⟩
    exact ⟨hcov, Nat.le_trans (hopt C hC) hk⟩
  · rintro ⟨hC, hk⟩
    exact ⟨_, hC, hk⟩

/-- **Conditional theorem.** The obligation and the certificate check put vertex
cover in P. -/
theorem exactRounding_inP (h : ExactRoundingObligation) (hc : CoverCheckInP) : InP VC :=
  inP_of_reduces (exactRounding_reduces h) hc

/-- **Conditional theorem.** With NP-hardness of vertex cover, the obligation
gives P = NP. -/
theorem exactRounding_gives_pEqualsNP (hard : VCHard) (hc : CoverCheckInP)
    (h : ExactRoundingObligation) : PEqualsNP :=
  fun L hL => inP_of_reduces (hard L hL) (exactRounding_inP h hc)

/-- **Non-vacuity** (of the reduction the obligation provides). Given the
certificate check, not every language reduces to it: otherwise every language
would be in P, contradicting `exists_not_inP`. -/
theorem not_forall_reduces_coverCheck (hc : CoverCheckInP) :
    ¬ ∀ L : Language, PolyReduces L CoverCheck := by
  intro hall
  obtain ⟨L, hL⟩ := exists_not_inP
  exact hL (inP_of_reduces (hall L) hc)

/-! ### The machine obligation is the schema with machine-computed roundings -/

/-- Feasibility and cost of vertex cover on word instances. -/
def vcFeasible (w : Word) (C : Nat → Bool) : Prop := IsCover (edgesOf w) C
def vcCost (w : Word) (C : Nat → Bool) : Nat := cost (verticesOf w) C

/-- A rounding computed by a polynomial-time machine: the machine keeps the
instance and appends the rounded cover. -/
def MachineRounding (rnd : Word → Nat → Bool) : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ w, budgetOf (g w) = budgetOf w ∧ edgesOf (g w) = edgesOf w ∧ rnd w = coverOf (g w)

/-- **Instantiation.** The machine obligation holds exactly when, for some
relaxation bound `lp`, the schema `ExactRoundingObligationFor` holds with
machine-computed roundings. -/
theorem exactRoundingObligation_iff_schema :
    ExactRoundingObligation ↔
      ∃ lp : Word → Nat, ExactRoundingObligationFor MachineRounding vcFeasible vcCost lp := by
  constructor
  · rintro ⟨m, g, p, hm, hg⟩
    refine ⟨fun w => vcCost w (coverOf (g w)), fun w C hC => (hg w).2.2.2 C hC,
      fun w => coverOf (g w), ⟨m, g, p, hm, fun w => ⟨(hg w).1, (hg w).2.1, rfl⟩⟩,
      fun w => ⟨(hg w).2.2.1, Nat.le_refl _⟩⟩
  · rintro ⟨lp, hrel, rnd, ⟨m, g, p, hm, hg⟩, hex⟩
    refine ⟨m, g, p, hm, fun w => ⟨(hg w).1, (hg w).2.1, ?_, fun C hC => ?_⟩⟩
    · have := (hex w).1
      rw [(hg w).2.2] at this
      exact this
    · have := exact_rounding_optimal vcFeasible vcCost lp rnd hrel hex w C hC
      rw [(hg w).2.2] at this
      exact this

end Issue532.Idea36
