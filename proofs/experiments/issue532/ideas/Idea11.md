# Idea 11 — LP relaxation exactness (vertex cover integrality gap)

**Verdict:** Refuted in full strength (published theorem) + formal core. The shortcut "relax the integer program to an LP, solve it in polynomial time, and read off the exact answer" is refuted by a general theorem: for every `n ≥ 3` the vertex cover LP is not exact on the complete graph `Kₙ` (`not_LPExact_complete`), and on `K_{2q}` the integrality gap is at least `2 − 1/q`, which tends to 2 (`gap_family`); together with `frac_lower_complete` and `complete_cover_exact` it is exactly `2 − 1/q` over half-integral fractional covers (which lose nothing by the cited, unformalized Nemhauser–Trotter theorem). The strongest version, an exact polynomial-size LP (via extra variables) for the TSP, cut or stable set polytope, is refuted by Fiorini–Massar–Pokutta–Tiwary–de Wolf (2012/2015), and Rothvoss (2014) shows that such LP-size lower bounds hold even for problems in P, so they are statements about LPs, not about P vs NP. What LPs do give is proved here too: threshold rounding is a 2-approximation on every graph (`rounding_two_approx`).

## 1. The idea at full strength

Row 11 of the research log and family 3 of
[`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md) describe a route
used by several claimed P = NP proofs. At full strength:

1. Write an NP-hard problem (vertex cover, SAT, TSP) as an integer linear
   program.
2. Drop integrality and solve the LP in polynomial time (Khachiyan 1979).
3. Claim that the LP optimum equals the integer optimum, or that a
   polynomial rounding step recovers an optimal integer solution.
4. Stronger form: add polynomially many extra variables and constraints so
   that the LP polytope *projects exactly* onto the convex hull of integer
   solutions (an extended formulation). Then linear programming solves
   the NP-hard problem exactly, which would give P = NP.

Steps 3 and 4 are the claims under test.

## 2. Precise mathematical formulation

**Graphs.** A graph on vertices `0, …, n−1` is `adj : ℕ → ℕ → Bool`; the
complete graph is `complete u v = (u ≠ v)`.

**Half-integral fractional covers.** To stay in `ℕ` values are counted in
half units: `x : ℕ → ℕ` with `x i ≤ 2` (meaning `0, 1/2, 1`) and
`x u + x v ≥ 2` on every edge (`FracCover n adj x`). The LP value is
`sumTo x n / 2`, where `sumTo x n = x 0 + … + x(n−1)`. Restricting to
half-integral values loses nothing for vertex cover: the LP has a
half-integral optimal solution (Nemhauser–Trotter 1975; not formalized).

**Integral covers.** `s : ℕ → Bool` with `s u ∨ s v` on every edge
(`IntCover n adj s`); cost `card s n`.

**Exactness.** `LPExact n adj`: every fractional cover `x` is matched by an
integral cover `s` with `2 · card s n ≤ sumTo x n`, i.e. integer optimum
≤ LP value. (The converse inequality always holds.)

**Rounding.** `round x i = (x i ≥ 1)`: keep every vertex of value `≥ 1/2`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `sumTo_le` | Pointwise `x ≤ y` on `[0, n)` implies `sumTo x n ≤ sumTo y n`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `sumTo_const_le` | If `c ≤ x i` for all `i < n` then `c · n ≤ sumTo x n`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `sumTo_except` | If `c ≤ x i` for all `i < n` except one `u < n`, then `c · (n − 1) ≤ sumTo x n`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `card_all` | If every vertex `< n` is chosen then `card s n = n`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `half_feasible_complete` | For every `n`, all-`1/2` is a fractional cover of `Kₙ` of value `n/2`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `exists_zero_or_all_pos` | Either some `u < n` has `x u = 0`, or all `x i ≥ 1` for `i < n`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `frac_lower_complete` | For `n ≥ 2`, every half-integral fractional cover of `Kₙ` has value `≥ n/2`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `complete_cover_large` | For every `n`, every integral cover of `Kₙ` has `≥ n − 1` vertices. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `card_nonzero` | The set `{1, …, n}` has `n` elements below `n + 1`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `complete_cover_exact` | For `n ≥ 1`, `{1, …, n−1}` covers `Kₙ` with `n − 1` vertices. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `gap_family` | For every `q ≥ 1`: on `K_{2q}` all-`1/2` is a fractional cover of value `q`, and every integral cover has `≥ 2q − 1` vertices (so the gap is at least `2 − 1/q`). | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `LPExact` | Definition: the relaxation is exact on a graph. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `not_LPExact_complete` | For every `n ≥ 3`, the vertex cover LP is not exact on `Kₙ`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `round` | Definition: threshold rounding at `1/2`. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |
| `rounding_two_approx` | On every graph, rounding a fractional cover gives an integral cover of cost `≤ 2 ·` LP value. | [Lean](../lean/Idea11.lean) | [Rocq](../rocq/Idea11.v) |

No theorem in either file proves or refutes P = NP.

## 4. Complete argument

**LP side (`half_feasible_complete`, `frac_lower_complete`).** On `Kₙ`
every pair is an edge, so all-`1/2` is feasible with value `n/2`. For the
lower bound, either some vertex `u` has value `0` — then every other vertex
has value `1` (its edge to `u` must be covered), so the value is
`≥ n − 1 ≥ n/2` for `n ≥ 2` (`sumTo_except` with `c = 2`) — or every vertex
has value `≥ 1/2` and the total is `≥ n/2` (`sumTo_const_le` with `c = 1`).
So the half-integral LP optimum of `Kₙ` is exactly `n/2`.

**Integral side (`complete_cover_large`, `complete_cover_exact`).**
Induction on `n`. Restricting a cover of `K_{n+1}` gives a cover of `Kₙ`.
If vertex `n` is chosen, the count grows by one. If it is not chosen, every
edge `{i, n}` with `i < n` forces `i` to be chosen, so all `n` earlier
vertices are chosen (`card_all`). Either way `card ≥ n`. The set
`{1, …, n−1}` shows the bound is attained.

**Gap (`gap_family`, `not_LPExact_complete`).** On `K_{2q}` the LP value is
`q` and the integer optimum is `2q − 1`, so the ratio is `2 − 1/q`. For
`n ≥ 3`, exactness would give an integral cover with `2(n − 1) ≤ 2 · card ≤ n`,
i.e. `n ≤ 2`, a contradiction. This holds for every such `n`, not only for
a sample.

**Rounding (`rounding_two_approx`).** If `x u + x v ≥ 2` then `x u ≥ 1` or
`x v ≥ 1`, so the rounded set covers every edge. Each rounded vertex has
`x i ≥ 1` half unit, so `card (round x) n ≤ sumTo x n = 2 ·` LP value
(`sumTo_le`). Together with the gap family the factor 2 is asymptotically
tight *against the LP value*: no rounding scheme can certify better than
`2 − 1/q` from this LP alone.

## 5. Known results and literature

* L. G. Khachiyan, "A polynomial algorithm in linear programming", Doklady
  Akademii Nauk SSSR 244(5), 1979. LPs are solvable in polynomial time.
* G. L. Nemhauser and L. E. Trotter, "Vertex packings: structural
  properties and algorithms", Mathematical Programming 8, 1975. The vertex
  cover LP has half-integral optimal solutions.
* D. S. Hochbaum, "Approximation algorithms for the set covering and
  vertex cover problems", SIAM J. Comput. 11(3), 1982. LP rounding gives a
  2-approximation (the statement of `rounding_two_approx`).
* M. Yannakakis, "Expressing combinatorial optimization problems by linear
  programs", JCSS 43(3), 1991 (STOC 1988). Symmetric extended formulations
  of the TSP and matching polytopes need exponential size.
* S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Linear
  vs. semidefinite extended formulations: exponential separation and strong
  lower bounds", STOC 2012; journal version "Exponential lower bounds for
  polytopes in combinatorial optimization", JACM 62(2), 2015. The TSP, cut
  and stable set polytopes have exponential extension complexity, with no
  symmetry assumption.
* T. Rothvoss, "The matching polytope has exponential extension
  complexity", STOC 2014 (JACM 64(6), 2017). Matching is in P, yet its
  polytope needs exponential-size LPs: LP size lower bounds are not
  complexity lower bounds.
* A. Bazzi, S. Fiorini, S. Pokutta and O. Svensson, "No small linear
  program approximates vertex cover within a factor 2 − ε", FOCS 2015.
  The `K_{2q}` gap above extends to every polynomial-size LP.
* I. Dinur and S. Safra, "On the hardness of approximating minimum vertex
  cover", Annals of Mathematics 162(1), 2005: approximating vertex cover
  within 1.36 is NP-hard. S. Khot and O. Regev, "Vertex cover might be hard
  to approximate to within 2 − ε", JCSS 74(3), 2008: `2 − ε` is hard under
  the Unique Games Conjecture.

## 6. How far the idea can be pushed toward P vs NP

* **Refuted (formal, general):** automatic exactness of the natural LP. The
  gap is not an artefact of small cases; it holds for every `n ≥ 3` and
  approaches 2.
* **Refuted (published):** exact polynomial-size LP formulations, even with
  extra variables, for the TSP, cut and stable set polytopes (FMPTW), and
  polynomial-size LPs approximating vertex cover better than `2 − ε`
  (Bazzi–Fiorini–Pokutta–Svensson).
* **Does not touch P vs NP:** Rothvoss' theorem shows that extension
  complexity can be exponential for a problem in P. Hence an exponential LP
  lower bound for an NP-hard problem is not evidence for P ≠ NP, and it does
  not rule out a polynomial algorithm that is not an LP of this form.
* **What survives:** LP relaxations are correct tools for approximation
  (`rounding_two_approx`). Beating factor 2 for vertex cover in polynomial
  time would refute the Unique Games Conjecture, and beating 1.36 would
  prove P = NP (Dinur–Safra); neither is an LP question.

An attempt following this route must supply either an integrality theorem
for its specific polytope (and then face the extension complexity bounds)
or a rounding procedure with a proof of exactness on all instances;
`not_LPExact_complete` is the minimal counterexample it must survive.

## 7. Failure modes this idea catches

* **LP/SDP relaxation confused with the integer problem** (family 3 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): the relaxed
  optimum `n/2` is not the integer optimum `n − 1`.
* **Easier or approximate problem solved instead** (family 5): rounding
  solves vertex cover within factor 2, not exactly.
* **Heuristic evidence as proof** (family 8): an LP that happens to return
  integral solutions on test graphs (for example bipartite ones) says
  nothing about `Kₙ`.
* **Structure theorem from one algorithm class** (family 20): extended
  formulation lower bounds rule out LPs, not algorithms.

Audit rule: any "solve the LP relaxation" step must be accompanied by a
proof that the LP is integral on the instance class used, and the class must
still be NP-hard.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea11.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea11.v
```

Both commands print nothing on success. Remove the generated
`Idea11.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
