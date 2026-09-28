# Idea 04 — Local (pairwise / k-wise) consistency to global satisfiability

**Verdict:** Refuted in full strength (published theorem) + formal core

For every `n`, the XOR cycle `x_0 ≠ x_1 ≠ … ≠ x_{n−1} ≠ x_0` is satisfiable iff
`n` is even. Every subsystem that misses one of its constraints is satisfiable.
So for every `k`, the odd cycle of length `2k+1` passes every check on at most
`k` constraints and is still unsatisfiable. All of this is machine-checked. The
stronger, propagation-based version of the idea (bounded-width / `k`-consistency
algorithms) is refuted for SAT by published theorems: Tseitin formulas need
large resolution width, and 3-SAT does not have bounded width. That part is not
formalized here.

## 1. The idea at full strength

Ambitious version (direction P = NP): satisfiability is a *global* property,
but maybe it is always witnessed *locally*. If some fixed `k` exists such that
"every group of `k` constraints is consistent" (or a propagation procedure that
only ever looks at `k` variables at a time) implies global satisfiability, then
SAT is decidable in time `n^{O(k)}`, i.e. in polynomial time.

Source in issue #532: Part I item 1 ("Restricting geometry, connectivity, or
structure collapses hardness", "Hardness arises from **combinatorial
freedom**"), Part I item 2 ("It assumes locality, fixed neighborhoods … Search
for new invariants"), and Part II Phase 4 ("Encode proof templates …
local optimization arguments … Attempt formal proofs → record exact failure
points"). The failure point recorded here is the odd cycle: every piece is fine
and the whole is not.

## 2. Precise mathematical formulation

* **Systems.** A system is `sys : List (Nat × Nat)`. The pair `(i, j)` is the
  constraint `x_i ≠ x_j` over Boolean variables. `Solves x sys :⇔ ∀ p ∈ sys,
  x p.1 ≠ x p.2`, and `SatSys sys :⇔ ∃ x, Solves x sys`.
* **XOR cycle.** `cycle n = [(i, (i+1) mod n) | i < n]`.
* **Subsystems.** `S` is a subsystem of `sys` if every element of `S` belongs to
  `sys` (duplicates and reordering allowed).
* **`k`-local consistency.** `LocallyConsistent k sys :⇔` every subsystem with
  at most `k` constraints is satisfiable.
* **CNF view.** `sysCNF` turns each `(i, j)` into the 2-clauses
  `(x_i ∨ x_j) ∧ (¬x_i ∨ ¬x_j)`.
* **The claim the route needs.** `∃ k, ∀ sys, LocallyConsistent k sys → SatSys sys`
  (for the full idea: the same with CNF formulas and a stronger, propagating
  notion of consistency).

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `mem_cycle` | `p ∈ cycle n ↔ ∃ i < n, p = (i, (i+1) mod n)`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `cycle_even_sat` | `n mod 2 = 0 → SatSys (cycle n)` (alternating assignment). | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `solution_alternates` | If `x` solves `cycle n`, then for `i < n`: `x i = x 0 ↔ i mod 2 = 0`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `cycle_odd_unsat` | `n mod 2 = 1 → ¬SatSys (cycle n)`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `cycle_sat_iff` | `SatSys (cycle n) ↔ n mod 2 = 0`, for every `n`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `path_sat` | For `j < n` there is `x` satisfying every cycle constraint except the one at position `j`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `missing_constraint_sat` | Every subsystem of `cycle n` that misses some constraint of `cycle n` is satisfiable. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `short_subsystem_misses`, `short_subsystem_sat` | A subsystem with fewer than `n` constraints misses one (pigeonhole) and is therefore satisfiable. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `odd_cycle_locally_consistent` | For odd `n`: `LocallyConsistent (n−1) (cycle n) ∧ ¬SatSys (cycle n)`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `local_consistency_insufficient` | `∀ k, ∃ sys, LocallyConsistent k sys ∧ ¬SatSys sys`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `no_local_to_global` | `∀ k, ¬(∀ sys, LocallyConsistent k sys → SatSys sys)`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `sysCNF_iff` | For every assignment `x`: `evalCNF x (sysCNF sys) = true ↔ Solves x sys`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |
| `cycleCNF_sat_iff` | `Satisfiable (sysCNF (cycle n)) ↔ n mod 2 = 0`. | [Idea04.lean](../lean/Idea04.lean) | [Idea04.v](../rocq/Idea04.v) |

Not machine-checked: the statements about propagation-based consistency,
resolution width, bounded width, and the CSP dichotomy in Section 5.

## 4. Complete argument

**Even cycles.** Put `x_i = [i is odd]`. For `i + 1 < n` the constraint compares
consecutive parities, which differ. For `i = n − 1` it compares `x_{n−1}` with
`x_0 = false`, and `n − 1` is odd because `n` is even.

**Odd cycles.** Let `x` solve `cycle n`. For `i + 1 < n` the constraint at `i`
is `x_i ≠ x_{i+1}`. Two Booleans that differ from a common third are equal, so
by induction `x_i = x_0` exactly when `i` is even (`solution_alternates`). For
odd `n`, `n − 1` is even, so `x_{n−1} = x_0`. But the wrap-around constraint
at `n − 1` is `x_{n−1} ≠ x_0`, a contradiction.

**Removing one constraint.** For even `n` the full solution works. For odd `n`
and a removed position `j`, take `x_i = par(i)` for `i ≤ j` and
`x_i = par(i+1)` for `i > j`. Constraints below `j` compare `par(i)`,
`par(i+1)`. Constraints above `j` compare `par(i+1)`, `par(i+2)`. The
wrap-around (if `j ≠ n−1`) compares `x_{n−1} = par(n) = true` with
`x_0 = par(0) = false`. All differ. The only constraint that may fail is the one
at `j`, which was removed.

**Pigeonhole.** The first components of the cycle's constraints are
`0, 1, …, n−1`, all distinct. If a subsystem `S` contained every cycle
constraint, then `range n ⊆ map fst S`, so `n ≤ |S|`. Hence every `S` with
`|S| < n` misses a constraint and is satisfiable.

**Local consistency fails for every `k`.** Take `n = 2k+1`. The cycle is
`2k`-locally consistent, hence `k`-locally consistent, and unsatisfiable.

Worked example (`k = 3`, `n = 7`): the 7 constraints
`x0≠x1, x1≠x2, …, x5≠x6, x6≠x0` have no solution, but all
`C(7,3) + C(7,2) + 7 = 63` subsystems of 1 to 3 distinct constraints are
satisfiable. So are all `2^7 − 1 = 127` proper sub-*sets*.

**Why the formal core does not settle the full idea.** The notion
`LocallyConsistent` checks pieces *independently*. Propagation algorithms
(arc/path consistency, `(k, l)`-consistency, resolution of bounded width) chain
local deductions. On these 2-CNF instances, chaining `x_0 ≠ x_1`, `x_1 ≠ x_2` into
`x_0 = x_2` and so on refutes the odd cycle. Indeed 2-SAT is in P. The full
refutation of propagation needs different instances (Section 5): Tseitin
formulas and linear equations mod 2. On those, even propagation with `k`
variables fails unless `k` grows linearly with `n`.

## 5. Known results and literature

* G. S. Tseitin, "On the complexity of derivation in propositional calculus",
  in *Studies in Constructive Mathematics and Mathematical Logic, Part 2*,
  1968 (English translation 1970). Introduced the parity (XOR) formulas on
  graphs, of which the odd cycle is the simplest case. (Not formalized.)
* A. Urquhart, "Hard examples for resolution", *J. ACM* 34(1), 1987. Tseitin
  formulas on expander graphs need exponential-size resolution refutations.
  (Not formalized.)
* E. Ben-Sasson and A. Wigderson, "Short proofs are narrow — resolution made
  simple", *J. ACM* 48(2), 2001. Resolution width lower bounds, in particular
  linear width for Tseitin formulas on expanders. (Not formalized.)
* A. Atserias and V. Dalmau, "A combinatorial characterization of resolution
  width", *J. Computer and System Sciences* 74(3), 2008. `k`-consistency
  refutes a CNF iff it has a resolution refutation of width about `k`. With
  Ben-Sasson–Wigderson this shows that no fixed-`k` consistency algorithm
  refutes all unsatisfiable 3-CNFs. (Not formalized.)
* T. Feder and M. Y. Vardi, "The computational structure of monotone monadic
  SNP and constraint satisfaction: a study through Datalog and group theory",
  *SIAM J. Computing* 28(1), 1998. Defined bounded width and showed that
  linear equations over finite groups (e.g. mod 2) do not have bounded width.
  (Not formalized.)
* L. Barto and M. Kozik, "Constraint satisfaction problems solvable by local
  consistency methods", *J. ACM* 61(1), 2014. A CSP template has bounded width
  iff it cannot "count" (cannot simulate linear equations). (Not formalized.)
* A. Bulatov, "A dichotomy theorem for nonuniform CSPs", FOCS 2017, and
  D. Zhuk, "A proof of the CSP dichotomy conjecture", FOCS 2017 / *J. ACM*
  67(5), 2020. Every finite-template CSP is in P or NP-complete. The
  polynomial algorithms combine local consistency with Gaussian-elimination-like
  steps, not local consistency alone. (Not formalized.)
* B. Aspvall, M. F. Plass, R. E. Tarjan, "A linear-time algorithm for testing
  the truth of certain quantified Boolean formulas", *Information Processing
  Letters* 8(3), 1979. 2-SAT in linear time via the implication graph, which
  handles the odd-cycle family. (Not formalized.)

## 6. How far the idea can be pushed toward P vs NP

At full potential the idea gives *exactly* the bounded-width CSPs: for those,
`k`-consistency decides satisfiability in polynomial time (Barto–Kozik). This
is a real positive frontier, and it is fully characterized.

**Remaining obligation.** For SAT itself none remains, since the route is
refuted: 3-SAT can express linear equations mod 2 (Tseitin), and those have
unbounded width. So no fixed `k` works for 3-SAT. This is an *unconditional*
theorem (it does not assume P ≠ NP). For a *new* consistency notion, the
obligation would be "a polynomial-time local rule that is complete for
unsatisfiable 3-CNFs". Any such rule whose soundness is witnessed by bounded-width
resolution is ruled out by Ben-Sasson–Wigderson + Atserias–Dalmau. A rule of
unbounded power is no longer "local", and the obligation becomes Idea 01's
`PolySATDecider` (equivalent to P = NP). No Lean `def` is introduced for it,
since the bounded version is refuted and the unbounded version is Idea 01.

**Barriers.** The proof-complexity lower bounds above are the relevant
barriers. Local consistency *is* bounded-width resolution, so it inherits their
lower bounds. Algebraic methods (Gaussian elimination) escape the XOR
counterexamples but are defeated by other encodings. Combining them with local
consistency is exactly what the dichotomy algorithms do, and those algorithms
only cover polynomial-time templates.

## 7. Failure modes this idea catches

* **Local-to-global inference**
  ([error family 6](../../../attempts/COMMON_ERRORS.md#6-replacing-global-consistency-with-local-or-greedy-consistency)):
  "every small part is satisfiable, hence the whole is" is refuted by
  `no_local_to_global` for every size bound.
* **Solving a special case**
  ([family 5](../../../attempts/COMMON_ERRORS.md#5-solving-an-easier-special-approximate-or-different-problem)):
  a method that handles these 2-CNF cycles (e.g. 2-SAT propagation) has solved
  an easy problem. It must be tested on Tseitin/XOR families, where
  propagation fails.
* **Heuristic evidence**
  ([family 8](../../../attempts/COMMON_ERRORS.md#8-treating-heuristics-experiments-or-probability-as-proof)):
  random testing of subsystems of size `≤ k` on `cycle (2k+1)` never finds an
  inconsistency, although the system is unsatisfiable.
* **Barrier-limited techniques**
  ([family 14](../../../attempts/COMMON_ERRORS.md#14-ignoring-known-barriers-or-using-a-barrier-limited-technique)):
  a polynomial SAT algorithm that is secretly a bounded-width consistency
  procedure contradicts the published width lower bounds.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea04.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea04.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea04.{vo,vok,vos,glob}` and
`.Idea04.aux` files.
