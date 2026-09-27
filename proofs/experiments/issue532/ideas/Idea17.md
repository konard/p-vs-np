# Idea 17 — Enumeration accounting: exponential versus polynomial

**Verdict:** Refuted as a route (general theorem)

The accounting of exhaustive search is proved exactly and for every length.
The enumeration of length-`n` Boolean vectors has exactly `2^n` entries, with
no duplicates and none missing. Every polynomial `c * (n+1)^k` is eventually
smaller than `2^n`, with an explicit threshold. So exhaustive enumeration is
refuted, in general and formally, as a polynomial-time method. The files also
prove that the idea cannot be run in the other direction. An exponential
enumeration count is not a lower bound for the problem, because another
algorithm may avoid enumeration entirely. The real lower-bound statement,
`AllAlgorithmsSuperpolynomial`, is only defined here. It is equivalent to
P != NP when instantiated with polynomial-time machines for SAT.

## 1. The idea at full strength

The idea has two readings, one for each direction of the problem.

* **Toward P = NP.** "Enumerate candidate certificates and check each one; if
  the enumeration were organised cleverly enough, it would be polynomial."
  This matches Part I item 7 of issue #532: "Repeated failure patterns can be
  formalized and eliminated". The hidden-exponential-work pattern is one such
  failure.
* **Toward P != NP.** "SAT on `n` variables has `2^n` candidate assignments,
  and `2^n` beats every polynomial, therefore SAT is not in P." This is the
  most common argument in the repository's attempt catalogue
  (COMMON_ERRORS family 1, "Assuming a lower bound instead of proving it").

Phase 4 of the issue plan ("Encode proof templates ... counting arguments ...
Attempt formal proofs → record exact failure points") asks for exactly this
pair: prove the counting correctly, then record where the inference to a
complexity-class statement fails.

## 2. Precise mathematical formulation

* **Candidates.** `allVecs n : List (List Bool)`, defined by
  `allVecs 0 = [[]]` and
  `allVecs (n+1) = map (cons false) (allVecs n) ++ map (cons true) (allVecs n)`.
* **Brute force.** `bruteForce f n = (allVecs n).any f` for any predicate
  `f : List Bool → Bool`.
* **Cost model.** `searchCost f l` is the number of candidates examined by a
  left-to-right scan that stops at the first success. The unit of cost is one
  predicate evaluation. The cost of evaluating `f` itself is not counted, so
  every lower bound stated with this cost is also a lower bound for any finer
  cost model that charges at least one step per evaluation.
* **Polynomials.** `polyEval c k n = c * (n+1)^k`. This is the
  repository's `Complexity.Polynomial.eval` in
  `proofs/complexity/lean/Complexity.lean` (coefficient `c`, degree `k`),
  copied locally so the file needs no imports. Every polynomial with
  non-negative integer coefficients is bounded above by one of this form.
* **Claims needed by the idea at full strength.**
  1. (P = NP reading) For some polynomial, the enumeration has at most
     `polyEval c k n` entries for all `n`. This is refuted.
  2. (P != NP reading) "Enumeration costs `2^n`" implies "every algorithm
     costs super-polynomially". This inference is invalid. The correct
     statement is `AllAlgorithmsSuperpolynomial M`, which quantifies over
     all correct algorithms `A` in a model `M`:
     `∀ A, correct A → ∀ c k N, ∃ n ≥ N, polyEval c k n < cost A n`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `allVecs_length` | For all `n`, `allVecs n` has length `2^n`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `mem_allVecs` | For all `n, v`: `v ∈ allVecs n` iff `v.length = n`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `allVecs_nodup` | For all `n`, `allVecs n` has no duplicates. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `bruteForce_correct` | For all `f, n`: `bruteForce f n = true` iff some length-`n` vector satisfies `f`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `searchCost_all_false` | If no element of `l` satisfies `f`, the scan examines `length l` candidates. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `searchCost_no_witness` | If no length-`n` vector satisfies `f`, the scan of `allVecs n` examines exactly `2^n` candidates. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `succ_le_two_pow`, `lt_two_pow_self` | `q+1 ≤ 2^q` and `a < 2^a` for all naturals. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `linear_lt_exp` | For all `a, q` with `q ≥ 2a+1`: `a*(q+1) < 2^q`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `dyadic_bracket` | Every `n ≥ 1` has an `L` with `2^L ≤ n < 2^(L+1)`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `exp_beats_poly` | For all `c, k` and all `n ≥ 2^(2(c+k)+1)`: `c*(n+1)^k < 2^n`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `exists_threshold` | For all `c, k` there is `N` with `c*(n+1)^k < 2^n` for every `n ≥ N`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `enumeration_not_polynomial` | For all `c, k` there is `N` such that for all `n ≥ N`, both the enumeration length and the worst-case scan cost exceed `c*(n+1)^k`. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `enumeration_cost_is_not_problem_cost` | For all `n`, the scan cost of the always-false predicate is `2^n`, yet brute force returns the same answer as the constant `false` procedure. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `AllAlgorithmsSuperpolynomial` (def) | Open obligation: every correct algorithm of the model exceeds every polynomial at arbitrarily large lengths. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `superpolynomial_excludes_poly` | If the obligation holds for a model, no correct algorithm of it is polynomially bounded. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |
| `one_slow_algorithm_is_not_a_lower_bound` | In a model with a `2^n` algorithm and a cost-1 algorithm, the first exceeds every polynomial infinitely often, yet the obligation fails. | [Idea17.lean](../lean/Idea17.lean) | [Idea17.v](../rocq/Idea17.v) |

No theorem in either file concerns a Turing machine. The cost functions are
explicit counts in the models described in Section 2.

## 4. Complete argument

**Enumeration.** Induction on `n`. For `n = 0` the list is `[[]]`: length
`1 = 2^0`, no duplicates, and the only vector of length 0 is `[]`. For `n+1`,
the length is `2^n + 2^n = 2^(n+1)`. A vector of length `n+1` has the form
`b :: w` with `|w| = n`. By induction `w ∈ allVecs n`, so `b :: w` lies in
the `false` half or the `true` half. There are no duplicates because each
half is the image of a duplicate-free list under the injective map `cons b`,
and the two halves differ in their first bit.

**Brute force.** `List.any` is true iff some member satisfies `f`, and
membership is exactly "has length `n`". If no member satisfies `f`, the scan
never stops early, so it examines `length l` candidates. With
`l = allVecs n` that number is `2^n`.

**Growth theorem.** The proof uses integer arithmetic only.

1. `q + 1 ≤ 2^q` by induction, so `a < 2^a`.
2. *Linear versus exponential.* At `q = 2a+1`,
   `a(2a+2) = a·2(a+1) ≤ a·2·2^a < 2^a·2·2^a = 2^(2a+1)`.
   For the step `q → q+1` we have `a ≤ a(q+1) < 2^q`, hence
   `a(q+2) = a(q+1) + a < 2^q + 2^q = 2^(q+1)`.
3. *Dyadic bracket.* Every `n ≥ 1` satisfies `2^L ≤ n < 2^(L+1)` for some
   `L`. This follows by induction on `n`: either `n+1` stays below
   `2^(L+1)`, or it equals `2^(L+1)` and `L` increases by one.
4. *Main bound.* Let `n ≥ 2^(2(c+k)+1)` and bracket `n` by `L`. Then
   `L ≥ 2(c+k)+1`, since otherwise `n < 2^(L+1) ≤ 2^(2(c+k)+1)`. Step 2
   with `a = c+k` gives `(c+k)(L+1) < 2^L ≤ n`, so `c + k(L+1) < n`. Next,
   `n+1 ≤ 2^(L+1)`, which gives `(n+1)^k ≤ 2^((L+1)k)`. Finally
   `c·(n+1)^k ≤ c·2^((L+1)k) < 2^c·2^((L+1)k) = 2^(c+(L+1)k) ≤ 2^n`.

*Worked numbers.* For `c = 1, k = 2` the proved threshold is `2^7 = 128`.
At `n = 128`: `(129)^2 = 16641` and `2^128 ≈ 3.4·10^38`. The true crossover
is much earlier: `(n+1)^2 < 2^n` already holds from `n = 6` (`49 < 64`).
The theorem does not claim its threshold is optimal.

**Why the P != NP reading fails.**
`enumeration_cost_is_not_problem_cost` gives an explicit example. For the
always-false predicate, the scan costs `2^n` at every length, yet the
question "is there a witness?" has the constant answer `false`, which a
one-step procedure gives. `one_slow_algorithm_is_not_a_lower_bound`
packages the same point in the abstract model: one super-polynomial algorithm
coexists with a constant-cost correct algorithm, so the universal statement
fails. A lower bound needs `∀ algorithms`, not `∃ a slow algorithm`.

**Why the P = NP reading fails.** `enumeration_not_polynomial` shows the
enumeration outgrows every polynomial `c*(n+1)^k`. Any claimed polynomial
bound on an algorithm that examines all candidates is therefore false for
every sufficiently large `n`, not just for one tested `n`. Since every
integer polynomial is dominated by one of this form, the statement covers all
polynomials.

## 5. Known results and literature

* J. Hartmanis and R. E. Stearns, "On the computational complexity of
  algorithms", *Transactions of the AMS* 117 (1965). Time hierarchy
  theorems. These give genuine lower bounds for *some* problems, but only by
  diagonalization, not by counting candidates.
* S. A. Cook, "The complexity of theorem-proving procedures", *STOC* 1971.
  NP-completeness of SAT. It makes "SAT needs super-polynomial time"
  equivalent to P != NP.
* U. Schöning, "A probabilistic algorithm for k-SAT and constraint
  satisfaction problems", *FOCS* 1999. Solves 3-SAT in about `(4/3)^n`
  expected time. This shows concretely that `2^n` enumeration is not the
  cost of 3-SAT.
* R. Paturi, P. Pudlák, M. Saks, F. Zane, "An improved exponential-time
  algorithm for k-SAT", *Journal of the ACM* 52(3) (2005). The PPSZ
  algorithm, again strictly better than `2^n`.
* R. Impagliazzo and R. Paturi, "On the complexity of k-SAT", *Journal of
  Computer and System Sciences* 62(2) (2001). The Exponential Time
  Hypothesis. It is a conjecture, not a theorem, and it is strictly stronger
  than P != NP.
* T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question",
  *SIAM Journal on Computing* 4(4) (1975). Oracles relative to which P = NP
  and P != NP.

None of these results is formalized in the two files. Only the elementary
counting and growth facts of Section 3 are machine-checked.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** The idea yields an exact, formal refutation of every
  algorithm whose cost is at least the number of candidates it examines,
  whenever it examines them all. The same growth theorem is reused in Idea 20
  to show that polynomially many processors cannot hide `2^n` work.
* **Remaining obligation.** `AllAlgorithmsSuperpolynomial M`, with `M` the
  class of deterministic polynomial-time machines deciding SAT under a fixed
  encoding (for example `Complexity.ClassP` in
  `proofs/complexity/lean/Complexity.lean`), is exactly the statement
  "SAT ∉ P", which by the Cook–Levin theorem is equivalent to P != NP. The
  obligation is therefore equivalent to the original problem, not weaker.
* **Barriers.** A proof that argues "every algorithm must in effect enumerate"
  must control arbitrary algorithms.
  * Arguments that only use the input/output behaviour of a subroutine
    relativize. Baker–Gill–Solovay shows they cannot settle P vs NP.
  * Counting over candidates is a property of the search space, not of the
    algorithm. Schöning and PPSZ show that the search space size is not the
    complexity even for k-SAT.
  * ETH-style statements (`2^(δn)` for 3-SAT) are conjectures. Assuming
    them is COMMON_ERRORS family 12 (smuggling the conclusion).

## 7. Failure modes this idea catches

* **Family 1 (assumed lower bound).** Any attempt that derives "not in P"
  from "the natural search examines `2^n` candidates" is refuted by
  `enumeration_cost_is_not_problem_cost` and
  `one_slow_algorithm_is_not_a_lower_bound`. An auditor should ask where the
  proof quantifies over *all* algorithms.
* **Family 2 (hidden exponential work).** If a claimed polynomial algorithm
  materialises all assignments, all subsets, or all paths, then
  `enumeration_not_polynomial` together with `allVecs_nodup` shows that its
  running time exceeds every polynomial from an explicit length onwards.
* **Family 7 (counting mistakes).** `allVecs_length` and `mem_allVecs` give
  the exact count. Attempts that count "`n^2` cases" for a search over subsets
  can be checked against it.
* **Family 20 (one algorithm class).** Failure of enumeration-based methods
  is a statement about one class of algorithms. `twoAlgModel` is a
  machine-checked instance of the gap.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea17.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea17.v
rm -f proofs/experiments/issue532/rocq/Idea17.vo proofs/experiments/issue532/rocq/Idea17.vok \
      proofs/experiments/issue532/rocq/Idea17.vos proofs/experiments/issue532/rocq/Idea17.glob \
      proofs/experiments/issue532/rocq/.Idea17.aux
```

Both commands print nothing on success.
