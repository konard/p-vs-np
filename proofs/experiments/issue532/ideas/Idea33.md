# Idea 33 — Average-case to worst-case transfer

**Verdict:** Refuted as a route (general theorem)

An algorithm can be correct on all but a vanishing fraction of the inputs of
every length and still be wrong in the worst case at every length. The Lean and
Rocq files prove this for **every** language `L` and **every** input length `n`:
the algorithm `flipOne L` errs on exactly one of the `2^n` inputs of length `n`.
The full-strength version, a worst-case-to-average-case reduction for an
NP-complete problem, is open. Known results show that the natural
(non-adaptive) forms of such reductions would collapse the polynomial
hierarchy. We state the missing step as an explicit schema
(`WorstToAverageObligationFor`), not as an assumption, and give its instance
in the shared machine model (`WorstToAverage`). With polynomial-time machines
and the uniform distribution, the transfer for SAT together with an
average-case decider gives `InP SAT`. Failure of the transfer for SAT gives
`PNotEqualsNP`.

## 1. The idea at full strength

The hope is: "an algorithm that solves SAT on almost all inputs, or on random
inputs, can be turned into an algorithm that solves SAT on all inputs." Two
directions are attempted:

- **Toward P = NP:** find a heuristic that succeeds on random or typical
  instances, then argue that worst-case instances are rare or can be avoided.
  From that, conclude that SAT is in P.
- **Toward P != NP:** prove that SAT is hard on average for some distribution.
  Worst-case hardness would follow, and the argument would sometimes be read as
  going in the other direction too.

In issue #532 this is the "average-case complexity" training ground of Part II,
Phase 6 ("Target achievable separations ... average-case complexity"). It also
touches Part I, item 2 ("Failure of known heuristics ≠ impossibility of all
methods"). The hidden inference is *"small average error ⇒ zero worst-case
error"*. This is the exact point that fails.

## 2. Precise mathematical formulation

- Inputs are bit strings `List Bool`. A language is `L : List Bool → Bool`. An
  algorithm is `A : List Bool → Bool`. Here only correctness matters, so there is
  no cost model.
- The uniform sample space at length `n` is the explicit list `allInputs n` of
  all `2^n` strings of length `n` (proved complete and duplicate-free).
- `count p l` is the length of `l.filter p`.
- The error count at length `n` is
  `count (fun x => A x != L x) (allInputs n)`. The error fraction is this count
  divided by `2^n`.
- `AvgCorrect A L δ` holds when the error count is at most `δ n` for every `n`.
  `WorstCorrect A L` holds when `A x = L x` for all `x`.
- The inference under test is `AvgCorrect A L δ → WorstCorrect A L` for a
  "small" `δ`, for example `δ n = 1` (error fraction `2^{-n}`).
- The full-strength claim is a **worst-case-to-average-case reduction**. Given
  an NP-complete `L`, a class `Efficient` (polynomial time) and a budget
  `δ n = 2^n / poly(n)`, it asks for an efficient `A` with `AvgCorrect A L δ`
  to yield an efficient `B` with `WorstCorrect B L`. In the files this is
  the schema `WorstToAverageObligationFor Efficient L δ`. It quantifies over a
  free class `Efficient`, so it is a schema, not an open obligation.
- **Machine instance (shared model `Complexity`, `Issue532.Machines`).**
  `machineAnswer m p x` is the answer "machine `m` accepts `x` within
  `p(|x|)` steps".
  `AvgPolyDec L δ := ∃ m p, (∀ x, ∃ t b, t ≤ p(|x|) ∧ Run m (initial x) t b) ∧ AvgCorrect (machineAnswer m p) L δ`
  is a clocked machine that errs on at most `δ n` inputs of each length.
  `WorstToAverage L δ := AvgPolyDec L δ → InP L`. The distribution is uniform
  on the bit strings of each length. Under the shared CNF encoding most words
  decode to formulas with an empty clause, so this is not the
  samplable-distribution statement of the literature.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `allInputs_length` | `allInputs n` has exactly `2^n` elements | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `mem_allInputs` | every string `x` is in `allInputs x.length` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `length_of_mem_allInputs` | every member of `allInputs n` has length `n` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `allInputs_nodup` | `allInputs n` has no duplicates | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `count_isZeros` | exactly one string of length `n` is all-false | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `flipOne_errors` | for all `L, n`: `flipOne L` errs on exactly 1 input of length `n` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `flipOne_agreements` | for all `L, n`: `flipOne L` is correct on exactly `2^n - 1` inputs of length `n` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `flipOne_error_vanishes` | for all `L, k` and all `n ≥ k`: (error count) · `k ≤ 2^n` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `flipOne_worst_case_wrong` | for all `L, n`: some `x` of length `n` has `flipOne L x ≠ L x` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `average_case_does_not_imply_worst_case` | for every `L` there is an `A` with `2^n - 1` agreements and 1 error at every `n`, wrong at every length | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `worst_implies_avg` | worst-case correct ⇒ average-case correct for any budget | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `avg_zero_implies_worst` | a budget of zero errors at every length ⇒ worst-case correct | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `WorstToAverageObligationFor` (def) | the abstract schema, as a `Prop` over a free class `Efficient`; never assumed | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `obligation_not_automatic` | for every `L` there is a class `Efficient` with `¬ WorstToAverageObligationFor Efficient L (fun _ => 1)` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `obligation_transfers` | the schema plus an efficient average-case solver yields an efficient worst-case solver | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `AvgPolyDec`, `WorstToAverage` (defs) | machine instance: clocked polynomial-time machine with at most `δ n` errors per length; the transfer `AvgPolyDec L δ → InP L` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `avgPolyDec_of_inP`, `inP_of_avgPolyDec_zero`, `avgPolyDec_zero_iff` | `InP L` gives `AvgPolyDec L δ` for every `δ`; `AvgPolyDec L 0 ↔ InP L` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `worstToAverage_of_inP`, `worstToAverage_zero` | the transfer holds for languages in P, and for budget zero for every language | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `inP_sat_of_worstToAverage` | `WorstToAverage SAT δ → AvgPolyDec SAT δ → InP SAT` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `pEqualsNP_of_worstToAverage` | with `SATHard`, the same data give `PEqualsNP` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `worstToAverage_sat_of_pEqualsNP` | with `SATInNP`, `PEqualsNP` gives `WorstToAverage SAT δ` for every `δ` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `pNotEqualsNP_of_not_worstToAverage` | with `SATInNP`, `¬ WorstToAverage SAT δ` gives `PNotEqualsNP` | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `exists_language_far_from_family` | for an injective code of a family of languages, some language differs from each member on both one-bit extensions of its code | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |
| `exists_not_avgPolyDec`, `worstToAverage_nontrivial` | non-vacuity: some language has no machine average-case decider with budget one | [Lean](../lean/Idea33.lean) | [Rocq](../rocq/Idea33.v) |

The intended Rocq names are the Lean names; the Rocq file still has the
pre-machine version (old name `WorstToAverageObligation`, no machine part).

In Lean the Boolean tests are `A x != L x` and `A x == L x`. In Rocq they are
`negb (Bool.eqb (A x) (L x))` and `Bool.eqb (A x) (L x)`.

## 4. Complete argument

**Enumeration.** `allInputs 0 = [[]]`, and `allInputs (n+1)` puts `false`
in front of every string in `allInputs n`, followed by `true` in front of every
string. By induction the length is `2^n + 2^n = 2^(n+1)`. Each member has
length `n`. Every string `b :: x` lies in the `b`-half of
`allInputs (|x|+1)`. The two halves are duplicate-free, because `cons b` is
injective, and disjoint, because their heads differ. So `allInputs n` is exactly
the uniform sample space of size `2^n`.

**Counting the all-false string.** `isZeros x` holds when every bit of `x` is
`false`. For `n = 0` the count is 1. For `n + 1`, the `false`-half contributes
`count isZeros (allInputs n) = 1`, because `isZeros (false :: y) = isZeros y`.
The `true`-half contributes 0. So the count is always 1.

**The counterexample algorithm.** `flipOne L x := if isZeros x then !L x else L x`.
A case split on `isZeros x` and `L x` gives `(flipOne L x != L x) = isZeros x`.
So the error count at length `n` equals `count isZeros (allInputs n) = 1`
(`flipOne_errors`). The agreement and disagreement counts partition the list
(`count_add_count_not`), so the agreement count is `2^n - 1`
(`flipOne_agreements`). For example, at `n = 3` the algorithm is right on 7 of
8 inputs. At `n = 20` it is right on 1,048,575 of 1,048,576 inputs.

**Vanishing error.** `k < 2^k ≤ 2^n` whenever `k ≤ n`, so `1 · k ≤ 2^n`
(`flipOne_error_vanishes`). The error fraction is therefore at most `1/k` from
length `k` on, for every `k`.

**Worst-case failure.** At length `n`, the input `zeros n` (all-false) has
`flipOne L (zeros n) = !L (zeros n) ≠ L (zeros n)`
(`flipOne_worst_case_wrong`).

**Why this refutes the route.** The theorem holds for every `L`, including
SAT or any NP-complete language. It also holds at every length, so it is not a
finite-size artifact. The error budget is the smallest nonzero one, so no
average-case error bound `δ n ≥ 1` implies worst-case correctness by itself.
Only `δ = 0` works (`avg_zero_implies_worst`), and that is just worst-case
correctness. Any argument of the form "my algorithm fails on a negligible
fraction of inputs, so it decides `L`" is therefore invalid unless it adds a
further ingredient.

**The obligation is not automatic.** Let `Efficient A := ∃ x, A x ≠ L x`, the
class of algorithms that are not exactly `L`. Then `flipOne L` is in the class
and has at most one error per length, so the hypothesis of
`WorstToAverageObligationFor Efficient L (fun _ => 1)` holds. The conclusion
would need a `B` in the class with `B x = L x` for all `x`, which contradicts
membership. So `obligation_not_automatic` shows that the obligation can hold
only because of specific properties of `L` and of the algorithm class.
Counting alone cannot establish it. `obligation_transfers` records that once
the obligation is proved, it yields the worst-case solver.

**Machine instance.** With a clocked machine, `machineAnswer m p` agrees
with the machine's output on every input (`machineAnswer_eq`). So budget zero
is exactly P (`avgPolyDec_zero_iff`), and every language in P satisfies the
transfer. For SAT: if the transfer holds and an average-case decider exists,
then SAT is in P (`inP_sat_of_worstToAverage`), and with SAT NP-hard, P = NP
(`pEqualsNP_of_worstToAverage`). If P = NP, then SAT is in P and the
transfer holds for every budget (`worstToAverage_sat_of_pEqualsNP`).
Contrapositively, a failure of the transfer for SAT at any budget proves
P ≠ NP (`pNotEqualsNP_of_not_worstToAverage`). The hypothesis
`AvgPolyDec L 1` is not automatic: machines paired with polynomials have an
injective encoding, and a language that flips the answer of each machine on
both one-bit extensions of its own code gives every clocked machine at least
two errors at that length (`exists_language_far_from_family`,
`two_le_count`, `exists_not_avgPolyDec`).

## 5. Known results and literature

- L. A. Levin, "Average case complete problems", *SIAM Journal on Computing*
  15(1), 1986. Defines distributional NP and average-case completeness.
- R. Impagliazzo, "A personal view of average-case complexity", *Proc. 10th
  IEEE Structure in Complexity Theory Conference*, 1995. The "five worlds"
  (Algorithmica, Heuristica, Pessiland, Minicrypt, Cryptomania). "Heuristica" is
  the world where NP is hard in the worst case but easy on average. It is not
  known to be excluded, so the counterexample above has a complexity-theoretic
  analogue that cannot currently be ruled out.
- J. Feigenbaum and L. Fortnow, "Random-self-reducibility of complete sets",
  *SIAM Journal on Computing* 22(5), 1993. If an NP-complete set is
  (non-adaptively) random-self-reducible, then coNP ⊆ NP/poly, and the
  polynomial hierarchy collapses.
- A. Bogdanov and L. Trevisan, "On worst-case to average-case reductions for NP
  problems", *SIAM Journal on Computing* 36(4), 2006 (FOCS 2003). A non-adaptive
  worst-case-to-average-case reduction from an NP-complete problem to a
  distributional problem in NP (samplable distribution, inverse-polynomial error)
  implies coNP ⊆ NP/poly.
- A. Bogdanov and L. Trevisan, "Average-Case Complexity", *Foundations and
  Trends in Theoretical Computer Science* 2(1), 2006. Survey.
- M. Ajtai, "Generating hard instances of lattice problems", *STOC 1996*. A
  worst-case-to-average-case reduction for approximate lattice problems. The
  approximation factors involved are not known to be NP-hard, so this does not
  bear on NP-complete problems.
- The permanent is random-self-reducible (Lipton, 1991), which gives
  worst-case-to-average-case reductions for #P-complete problems. This shows
  that such reductions exist for problems believed to lie above NP. No such
  reduction is known for NP-complete problems.

None of these results is formalized here. The files formalize the counting
counterexample, the abstract schema, and its instance for machines of the
shared model under the uniform distribution on words.

## 6. How far the idea can be pushed toward P vs NP

**At full potential.** A worst-case-to-average-case reduction for SAT under
some samplable distribution would let average-case hardness results (for example
from cryptographic assumptions) imply worst-case hardness. In the other
direction, it would turn an average-case heuristic into a worst-case algorithm.
In either direction it links the two regimes. It does **not** by itself decide
P vs NP: it would still need an average-case algorithm (for P = NP) or an
average-case lower bound (for P != NP).

**Exact remaining statement.** The schema `WorstToAverageObligationFor` with
`L` = SAT, `Efficient` = deterministic polynomial time, and `δ n = 2^n / p(n)`
for a polynomial `p`, together with a matching distribution. For the uniform
distribution on words its machine instance is `WorstToAverage SAT δ`, and the
files prove `WorstToAverage SAT δ → AvgPolyDec SAT δ → InP SAT` and
`¬ WorstToAverage SAT δ → PNotEqualsNP` (given `SATInNP`). This instance is
deliberately **not** labelled an open obligation. Under the shared CNF
encoding most words of each length decode to formulas containing the empty
clause, so SAT is plausibly easy on average under the uniform distribution
(this is not proved here). Then `WorstToAverage SAT δ` would be about as
hard as `InP SAT` itself, and would not be the samplable-distribution
statement of the literature. With a samplable distribution, the formal
`allInputs` count would become a weighted count.

**Barriers.**
- *Non-adaptive reductions*: Feigenbaum–Fortnow and Bogdanov–Trevisan show that
  such a reduction for an NP-complete problem implies coNP ⊆ NP/poly. That
  collapse is believed false, so, unless coNP ⊆ NP/poly, any successful
  reduction must be adaptive or use a non-black-box argument.
- *Counting*: `obligation_not_automatic` shows that no argument using only
  error counts can work. The proof must exploit the algebraic or combinatorial
  structure of the problem (as random self-reducibility does for the permanent).
- *Heuristica*: the absence of a proof that Heuristica is impossible means that
  nobody currently knows how to exclude "NP easy on average, hard in the worst
  case".

**Strength relative to P vs NP.** The obligation is neither known to imply nor
known to follow from P != NP. If P = NP, the obligation holds trivially: take
`B` to be the polynomial SAT algorithm. So refuting it would prove P != NP, and
proving it outright is not easier than excluding Heuristica. It is a separate
open problem, orthogonal to the separation itself.

## 7. Failure modes this idea catches

- **Family 8 (heuristics, experiments, or probability as proof)** in
  [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md): claims that an algorithm
  "works on all tested / random instances" are exactly `AvgCorrect` with a small
  budget. `average_case_does_not_imply_worst_case` shows this never implies
  `WorstCorrect` without a further argument.
- **Family 5 (solving an easier or different problem)**: average-case solvability
  is a different problem from worst-case solvability.
- **Family 12 (smuggling the conclusion)**: an attempt that assumes "hard
  instances are rare, hence avoidable" assumes a worst-case-to-average-case
  reduction, which is `WorstToAverageObligationFor` (machine instance
  `WorstToAverage`).
- Audit rule: for any claimed transfer, ask for the class `Efficient`, the
  distribution, the error budget, and a proof that uses more than counting. By
  `obligation_not_automatic`, a proof that uses only counting is invalid.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea33.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea33.v
rm -f proofs/experiments/issue532/rocq/Idea33.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea33.aux
```

Both commands print nothing on success.
