# Idea 36 — Exact relaxation and rounding

**Verdict:** Correct tool, insufficient alone (general theorem proved)

The plan is to relax an NP-hard integer program to a linear program, which is
solvable in polynomial time, and then round the fractional optimum to an
integer optimum. For vertex cover, the files prove that threshold rounding of
any half-unit fractional cover is a cover of cost at most twice the LP value,
which is a correct factor-2 tool. They also prove that the complete graph `K_n` has
an integrality gap: it has a fractional cover of value `n/2`, while every
integral cover has at least `n - 1` vertices, so for `n ≥ 3` no rounding of
this relaxation can be exact. In general, an exact rounding of any relaxation
returns optimal solutions. Over the shared machine model, the open obligation
`ExactRoundingObligation` asks for a polynomial-time `Complexity.Machine` map
that appends an optimal vertex cover to every word-encoded instance. With the
named known theorems `CoverCheckInP` (the certificate check is in P) and
`VCHard` (Karp 1972) it gives `InP VC` and `PEqualsNP`.

## 1. The idea at full strength

Integer programs encode NP-complete problems: vertex cover, independent set,
3-SAT (as 0/1 feasibility), and so on. Linear programs are solvable in
polynomial time (Khachiyan's ellipsoid method, Karmarkar's interior point
method). The hope is:

1. Write an NP-complete problem as an integer program.
2. Solve the LP relaxation in polynomial time.
3. Round the fractional optimum to an integral solution **of the same value**.

If step 3 were always possible in polynomial time, the problem would be in P,
and so P = NP. The idea is a natural reading of issue #532, Part I, item 1,
where the problem is reformulated as optimization over a continuous object. The
question is whether the continuous object can be "discretised back" without
loss.

## 2. Precise mathematical formulation

**Half-unit vertex cover.** Vertices are natural numbers. A graph is a vertex
list `vs` and an edge list `edges : List (Nat × Nat)`.

- A fractional assignment `x : Nat → Nat` is counted in halves, so `0, 1, 2`
  mean `0, 1/2, 1`.
- `FracCover edges x` means `x u + x v ≥ 2` for every edge `(u, v)`, that is,
  total weight at least one unit.
- `IsCover edges C` means that `C : Nat → Bool` picks an endpoint of every edge.
- `round x v := (x v ≥ 1)` is threshold rounding at one half.
- `cost vs C` is the number of picked vertices in `vs`, and
  `halfSum vs x = Σ_{v ∈ vs} x v` is the LP value in halves, so LP value
  `= halfSum / 2`.
- `completeEdges vs` is the edge list of the complete graph on `vs`.

**General relaxation.**

- `Relaxation feasible cost lp := ∀ I s, feasible I s → lp I ≤ cost I s`.
- `ExactRounding feasible cost lp rnd := ∀ I, feasible I (rnd I) ∧ cost I (rnd I) ≤ lp I`.
- `ExactRoundingObligationFor PolyTime feasible cost lp` is the generic
  **schema**: a relaxation together with a rounding that is in `PolyTime` and
  exact. `PolyTime`, `feasible`, `cost` and `lp` are parameters, so the schema
  is not itself an open problem.

**Vertex cover on the shared machine model.** Words, machines and runs come
from `proofs/complexity/lean/Complexity.lean`, and `Computes m g p` (the
machine outputs `g w` within `p.eval |w|` steps of its `Run`) from
`proofs/experiments/issue532/lean/Machines.lean`.

- A word is read as a list of unary numbers (`nats`, `true^k false` is `k`).
  The list `k, e, a₁, b₁, …, a_e, b_e, c₀, c₁, …` is the instance with budget
  `budgetOf w = k` and edges `edgesOf w = [(a₁, b₁), …, (a_e, b_e)]`. The
  vertices `verticesOf w` are `0, …, vbound - 1`, where `vbound` exceeds every
  endpoint. The trailing numbers are a candidate cover `coverOf w`: vertex `v`
  is chosen iff `c_v ≠ 0`.
- `VC w` holds iff some cover of `edgesOf w` has at most `budgetOf w` vertices.
  `CoverCheck u` holds iff `coverOf u` is a cover of `edgesOf u` within
  `budgetOf u`.
- `OptimalCover edges vs C` says `C` is a cover of minimum cost.
- Named known theorems (true, not mechanised here):
  `CoverCheckInP : Prop := InP CoverCheck` (the certificate check of vertex
  cover ∈ NP) and `VCHard : Prop := NPHard VC` (Karp 1972).
- The open obligation:

```lean
def ExactRoundingObligation : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ w, budgetOf (g w) = budgetOf w ∧ edgesOf (g w) = edgesOf w ∧
      OptimalCover (edgesOf w) (verticesOf w) (coverOf (g w))
```

- `MachineRounding rnd` says `rnd` is computed by such a machine map, with
  `vcFeasible` and `vcCost` the vertex-cover feasibility and cost on words.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | small illustration kept from an earlier round (a one-line logical step, not a main result): a sound rounding map turns a relaxed witness into a discrete witness | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `round_is_cover` | threshold rounding of any fractional cover is a vertex cover | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `round_cost_le` | `|round x| ≤ halfSum vs x`, i.e. cost at most twice the LP value | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `toFrac_cover` | an integral cover, weighted `2` on chosen vertices, is a fractional cover | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `halfSum_toFrac` | its LP value in halves is `2 · cost` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `round_two_approx` | rounding a fractional cover that is optimal among half-unit assignments gives a cover of size `≤ 2 ·` any cover | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `cost_all_true` | if every vertex is chosen, the cost is the number of vertices | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `complete_cover_cost` | every vertex cover of the complete graph on `n` vertices has `≥ n - 1` vertices | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `halfSum_one` | the all-halves assignment has LP value `n/2` (`n` halves) | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `complete_graph_gap` | on `K_n`: the fractional cover has value `n/2`, while integral covers have value `≥ n - 1` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `no_exact_rounding` | for `n ≥ 3`, some fractional cover of `K_n` is strictly cheaper than every integral cover | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exact_rounding_optimal` | an exact rounding of a relaxation returns optimal solutions | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exact_rounding_decides` | an exact rounding decides `∃ s, feasible I s ∧ cost I s ≤ k` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exactRounding_reduces` | `ExactRoundingObligation → PolyReduces VC CoverCheck` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exactRounding_inP` | `ExactRoundingObligation → CoverCheckInP → InP VC` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exactRounding_gives_pEqualsNP` | `VCHard → CoverCheckInP → ExactRoundingObligation → PEqualsNP` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `not_forall_reduces_coverCheck` | non-vacuity: given `CoverCheckInP`, not every language reduces to `CoverCheck` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |
| `exactRoundingObligation_iff_schema` | `ExactRoundingObligation ↔ ∃ lp, ExactRoundingObligationFor MachineRounding vcFeasible vcCost lp` | [Lean](../lean/Idea36.lean) | [Rocq](../rocq/Idea36.v) |

The definitions `FracCover`, `IsCover`, `round`, `cost`, `halfSum`,
`completeEdges`, `Relaxation` and `ExactRounding` are present in both files
under the same names. The schema is `ExactRoundingObligationFor` in Lean (the
intended Rocq name is the same). The machine-model part (the word encoding,
`VC`, `CoverCheck`, `CoverCheckInP`, `VCHard`, `ExactRoundingObligation` and
the last five rows) is proved in Lean only so far; the intended Rocq names are
the same. The combinatorial proofs are constructive; `VC` and `CoverCheck` are
classical `decide`s, and the non-vacuity theorem uses the classical diagonal
language of the shared layer. A `decide` example checks the encoding on the
triangle.
The theorems are stated for arbitrary graphs, arbitrary fractional covers, and
arbitrary instance and solution types.

## 4. Complete argument

**Rounding is feasible.** Let `(u, v)` be an edge with `x u + x v ≥ 2`. If
`x u ≥ 1`, then `u` is rounded in. Otherwise `x u = 0`, so `x v ≥ 2 ≥ 1` and
`v` is rounded in (`round_is_cover`).

**Rounding costs at most twice the LP.** Every rounded vertex has `x v ≥ 1`,
that is, weight at least one half. It contributes `1` to `cost` and at least
`1` to `halfSum`. Summing over `vs` gives `cost vs (round x) ≤ halfSum vs x`,
which is twice the LP value (`round_cost_le`).

**Factor 2.** Any integral cover `C` gives the fractional cover `toFrac C`, of
value `2 · cost vs C` halves (`toFrac_cover`, `halfSum_toFrac`). If `x` is an
optimal fractional cover, then `halfSum vs x ≤ 2 · cost vs C`. Together with the
previous step, `cost(round x) ≤ 2 · cost(C)` (`round_two_approx`).

**The gap.** On the complete graph over `vs` with `|vs| = n`, the constant
assignment `1` (one half everywhere) covers every edge, since `1 + 1 = 2`. Its
value is `n` halves (`halfSum_one`). Suppose a vertex cover `C` leaves out a
vertex `v`. Every edge `(v, w)` must then be covered by `w`, so `C` contains
all other vertices. By induction along the list, `n ≤ cost + 1`
(`complete_cover_cost`). For `n ≥ 3` this gives `2 · cost ≥ 2n - 2 > n`. So the
fractional optimum is strictly below the integral optimum (`no_exact_rounding`).
This is the same `K_n` gap as in Idea 11: LP value `n/2`, integral value
`n - 1`. (Only the inequalities above are formalized; that these values are
exactly the LP and integral optima of `K_n` is standard but not formalized.)
The ratio `2(n - 1)/n` tends to `2`. The factor-2 analysis above is
therefore tight **for this relaxation**, and no rounding scheme can be exact on
it.

**Exact rounding in general.** If `lp` is a relaxation bound and `rnd` is
feasible with `cost (rnd I) ≤ lp I`, then for every feasible `s`,
`cost (rnd I) ≤ lp I ≤ cost s`. So `rnd I` is optimal
(`exact_rounding_optimal`), and `cost (rnd I) ≤ k` decides whether a solution
of cost `≤ k` exists (`exact_rounding_decides`).

**The machine obligation.** On words, suppose a machine map `g` keeps the
instance and appends an optimal cover. If `VC w` holds, some cover of cost
`≤ k` exists, so the optimal appended cover also has cost `≤ k` and
`CoverCheck (g w)` holds. Conversely, the appended cover is itself a witness.
So `VC w = CoverCheck (g w)`, and `g` is a polynomial-time reduction
(`exactRounding_reduces`). With `CoverCheckInP`, `inP_of_reduces` gives
`InP VC` (`exactRounding_inP`). With `VCHard`, every NP language reduces to
`VC`, so P = NP (`exactRounding_gives_pEqualsNP`). The obligation is exactly
exact rounding on machines (`exactRoundingObligation_iff_schema`). An exact
rounding of any relaxation bound `lp` is optimal by `exact_rounding_optimal`.
Conversely, an optimal machine output is an exact rounding for `lp` equal to
its own cost, which is a relaxation bound by optimality. Time is the step count
of the machine's `Run` throughout; no running-time claim is left informal.

**Witness transfer.** `tested` is a small illustration kept from an earlier
round, a one-line logical step rather than a main result. It isolates what a
rounding needs to transfer **feasibility**: soundness on every relaxed solution. It says nothing about
cost, and so nothing about optimality.

## 5. Known results and literature

- R. M. Karp, "Reducibility among combinatorial problems", 1972. Vertex cover
  is NP-complete. Not formalized.
- L. G. Khachiyan, "A polynomial algorithm in linear programming", *Soviet
  Math. Doklady* 20, 1979. Linear programming is in P. Not formalized.
- G. L. Nemhauser and L. E. Trotter, "Vertex packings: structural properties
  and algorithms", *Mathematical Programming* 8, 1975. The vertex cover LP has
  half-integral optimal vertices, which is why the half-unit model here loses
  nothing. Not formalized.
- A. J. Hoffman and J. B. Kruskal, 1956: totally unimodular constraint matrices
  have integral LP vertices. For such matrices (for example bipartite vertex
  cover) rounding **is** exact, and the problems are in P. Not formalized.
- I. Dinur and S. Safra, "On the hardness of approximating minimum vertex
  cover", *Annals of Mathematics* 162(1), 2005. Approximating vertex cover
  within a factor of about 1.36 is NP-hard. Not formalized.
- S. Khot and O. Regev, "Vertex cover might be hard to approximate to within
  2 − ε", *Journal of Computer and System Sciences* 74(3), 2008. Under the
  Unique Games Conjecture, the factor 2 proved here is optimal for polynomial
  algorithms. Not formalized.

## 6. How far the idea can be pushed toward P vs NP

**At full potential**, the idea proves the open obligation over the shared
machine model:

```lean
def ExactRoundingObligation : Prop :=
  ∃ (m : Machine) (g : Word → Word) (p : Polynomial), Computes m g p ∧
    ∀ w, budgetOf (g w) = budgetOf w ∧ edgesOf (g w) = edgesOf w ∧
      OptimalCover (edgesOf w) (verticesOf w) (coverOf (g w))

theorem exactRounding_inP (h : ExactRoundingObligation) (hc : CoverCheckInP) : InP VC
theorem exactRounding_gives_pEqualsNP (hard : VCHard) (hc : CoverCheckInP)
    (h : ExactRoundingObligation) : PEqualsNP
```

The route needs two named hypotheses, both known theorems that are not
mechanised here: `CoverCheckInP` (checking a candidate cover is polynomial) and
`VCHard` (vertex cover is NP-hard, Karp 1972). By
`exactRoundingObligation_iff_schema`, the obligation is exactly the generic
schema `ExactRoundingObligationFor` with machine-computed roundings and some
relaxation bound. So "a polynomial relaxation plus a polynomial exact rounding"
is equivalent in strength to computing optimal vertex covers in polynomial
time. There is no slack. Non-vacuity: given `CoverCheckInP`, not every
language reduces to `CoverCheck` (`not_forall_reduces_coverCheck`), so the
reduction the obligation provides is a genuine property of `VC`.

**What blocks the obvious relaxations.** The natural LP for vertex cover has
integrality gap tending to 2 (`complete_graph_gap`), so exact rounding is
impossible for it (`no_exact_rounding`). A stronger relaxation (more
constraints, lift-and-project hierarchies, SDP) must close the gap on all
instances while staying polynomial-size. Unconditionally, Dinur–Safra rule out
polynomial approximation below about 1.36 unless P = NP. So any polynomial
relaxation with integrality gap below that factor would itself yield P = NP.
Showing that polynomial relaxations have such gaps for NP-hard problems is a
lower-bound question about relaxation size. For exact LP formulations of some
NP-hard polytopes (TSP, cut polytope) such lower bounds are known: S. Fiorini,
S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential lower bounds
for polytopes in combinatorial optimization", *STOC 2012* and *J. ACM* 62(2),
2015 (not formalized). They rule out polynomial-size exact LPs for those
polytopes, whatever the complexity of the rounding. Idea 11 treats relaxations
more broadly.

**What the idea does give.** A correct factor-2 algorithm
(`round_two_approx`), and an audit criterion: exactness holds exactly when the
relaxation is tight, which is a structural property to be proved (total
unimodularity, half-integrality plus a combinatorial argument, and so on). It
cannot be assumed.

**Caveats.** `CoverCheckInP` and `VCHard` are named hypotheses, not mechanised
theorems. Linear programming in P and the literature of section 5 are cited,
not formalized. The machine-model part is so far only in Lean; `Idea36.v` has
the combinatorics and the schema.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 3 (confusing LP/SDP relaxations with exact integer solutions):** the
  gap on `K_n` is a machine-checked counterexample to "the LP optimum equals the
  integer optimum".
- **Family 5 (solving an easier or approximate problem):** a factor-2 rounding
  (`round_two_approx`) solves the approximation problem, not the decision
  problem.
- **Family 18 (contradicting known results):** a claimed polynomial rounding
  with ratio better than 1.36 for vertex cover would contradict Dinur–Safra
  unless P = NP.
- **Family 17 (encoding size):** a relaxation with exponentially many
  constraints is not a polynomial-time LP without a separation oracle.

Audit rule: for a claimed exact rounding, check the proof of the inequality
`cost(round x) ≤ LP(x)` on the complete graph (or on the problem's own gap
instance). If the proof uses a property that `K_n` lacks, the claim is
restricted to a special class.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea36.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea36.v
rm -f proofs/experiments/issue532/rocq/Idea36.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea36.aux
```

Both commands print nothing on success.
