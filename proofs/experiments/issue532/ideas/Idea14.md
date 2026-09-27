# Idea 14 — Randomized search

**Verdict:** Developed to an open obligation (conditional theorem proved). Randomness is a legitimate resource with correct general laws. One-sided error amplifies exponentially with repetition (`rp_amplification`, proved by exact counting of seed tuples), and a one-sided algorithm with polynomially many seeds is derandomized in polynomial time by enumeration (`polySeedRP_implies_poly`). Random search does not reach P = NP by itself. Observing success on test seeds gives no error bound (`observed_success_no_guarantee`), and the route needs two open statements, recorded as definitions and never assumed: SAT has a polynomial randomized decider (`NPinRP`), and its seeds can be compressed to logarithmic length (`SeedCompression`). Their conjunction yields a deterministic polynomial decider (`rp_sat_with_seed_compression`). Caveat: the cost classes use an abstract model in which the declared time `T` is not tied to executing the algorithm (Section 2), so as formalized `PolyDec`, `NPinRP` and `SeedCompression` are satisfiable for every language (for example `T = 0` and a single seed); the formal content is the counting and the conditional bookkeeping, and the open statements are open only when read in a real machine model, which is not formalized here.

## 1. The idea at full strength

Attempts in this family run a randomized local search, random restarts, a
random walk or an evolutionary heuristic on SAT or another NP-complete
problem. They observe that it finds solutions on all tested instances in
polynomial time, and conclude that NP problems are "efficiently solvable",
hence P = NP.

At full strength the idea is the following. If SAT had a polynomial-time
randomized algorithm with bounded one-sided error (NP ⊆ RP), then

1. amplification would make the error exponentially small, and
2. a derandomization step would turn the algorithm into a deterministic
   polynomial-time one, giving P = NP.

The dossier makes steps 1 and 2 precise, proves what is provable in general,
and isolates the two open statements.

## 2. Precise mathematical formulation

A randomized algorithm on input `x` is a Boolean function `A x : ℕ → Bool`
of a seed `i < s x`, with all seeds equally likely. Probabilities are
counts divided by `s x`, so all statements are about counts in `ℕ`.

* `cnt s P` is the number of `i < s` with `P i`.
* `countT s k Q` is the number of lists `t` of length `k` over `[0, s)`
  with `Q t`. It is defined by enumerating the first entry and recursing, so
  it is an honest count of the `s^k` independent seed tuples.
* **One-sided error:** `OneSided L A s :≡ ∀ x, 0 < s x`, no false accepts
  (`L x = false → ∀ i, A x i = false`), and at most half of the seeds reject
  a yes-instance (`L x = true → 2 · cnt (s x) (¬A x) ≤ s x`).
* **Repetition:** on a tuple `t` of `k` seeds, accept iff some run accepts
  (`t.any (A x)`).
* **Enumeration:** `anySeed s f` is the OR of `f 0, …, f (s−1)`.
* **Cost classes** (abstract cost model with declared time `T`, as in
  [Idea 12](Idea12.md)):
  * `RPDecider sz L` has `2^(r x)` seeds with `r x`, `T x` polynomial in
    `sz x`.
  * `PolySeedRP sz L` has `s x` seeds with `s x`, `T x` polynomial.
  * `PolyDec sz L` is a deterministic decider with polynomial time.
  * Caveat: `T` (and the time of `PolyDec`) is a declared number, not the
    running time of an execution, and nothing links it to `A`. In this
    abstract model all three classes contain every language (take one seed,
    `A x i = L x`, `T = 0`; not stated as a theorem). They express the
    intended classes only when instantiated with a real machine model.
* **Open obligations:**
  * `NPinRP sz SAT :≡ RPDecider sz SAT`.
  * `SeedCompression sz SAT :≡ RPDecider sz SAT → PolySeedRP sz SAT`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `countT_true` | There are exactly `s^k` seed tuples of length `k`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `countT_all` | Exactly `(cnt s P)^k` tuples consist only of seeds satisfying `P`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `amplification_count` | `2b ≤ s ⇒ b^k · 2^k ≤ s^k`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `rp_amplification` | If at most half the seeds reject wrongly, at most `s^k/2^k` tuples make all `k` runs reject. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `observed_success_no_guarantee` | For every list `obs` of tested seeds and every `s`, some `A` succeeds on all of `obs` but fails on at least `s − |obs|` seeds. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `one_sided_amplified` | For a `OneSided` algorithm: repetition never accepts a no-instance, and on yes-instances the all-fail tuples are at most `s^k/2^k`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `enumeration_decides` | Trying all seeds decides `L` exactly for a `OneSided` algorithm. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `poly_seeds_derandomize` | With `s x ≤ e(n+1)^k` seeds and `T x ≤ c(n+1)^d` per run, enumeration costs `≤ e·c·(n+1)^(k+d)`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `polySeedRP_implies_poly` | `PolySeedRP sz L ⇒ PolyDec sz L`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `rp_sat_with_seed_compression` | `NPinRP sz L ∧ SeedCompression sz L ⇒ PolyDec sz L`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |

`NPinRP` and `SeedCompression` are `def ... : Prop` in Lean and
`Definition ... : Prop` in Rocq. They are never assumed. No theorem in
either file proves or refutes P = NP.

## 4. Complete argument

**Counting tuples.** `countT s (k+1) Q = Σ_{i<s} countT s k (t ↦ Q (i :: t))`.
For `Q = all P`, the inner count is `countT s k (all P)` when `P i` holds and
`countT s k (const false) = 0` otherwise. So the sum is
`cnt s P · countT s k (all P)`, and induction gives `(cnt s P)^k`
(`countT_all`). The same computation with `Q = const true` gives `s^k`.

**Amplification.** All `k` runs reject on tuple `t` iff every seed in `t` is
bad: `¬(t.any A) = t.all (¬A)`. Hence the number of failing tuples is
`b^k` with `b = cnt s (¬A)`. If `2b ≤ s`, then `(2b)^k ≤ s^k`, i.e.
`b^k · 2^k ≤ s^k`. The failure probability is at most `2^−k`, and `k`
repetitions cost `k` times the single-run time. No-instances are never
accepted, because every run rejects.

**Observed success.** Given tested seeds `obs`, let `A i = [i ∈ obs]`. It
succeeds on every tested seed. At most `|obs|` seeds below `s` are in `obs`
(`cnt_memB_le`, by induction on `obs`, using that each value is counted at
most once), so at least `s − |obs|` seeds fail. With `s = 2^r` seeds and
polynomially many tests, the failure fraction can be `1 − poly/2^r`.
Experiments on sampled seeds therefore bound nothing without a proof about
the algorithm on all seeds, and the same holds for sampled instances.

**Derandomization by enumeration.** On a no-instance every seed rejects, so
`anySeed = false`. On a yes-instance, if `anySeed = false` then
`cnt s A = 0`, so `cnt s (¬A) = s` by `cnt_compl`. With `2 cnt s (¬A) ≤ s`
this forces `s = 0`, contradicting `0 < s`. Enumeration costs
`s x · T x ≤ e(n+1)^k · c(n+1)^d = e c (n+1)^(k+d)`.

**Where it stops.** A polynomial-time randomized algorithm reads a
polynomial number `r` of random bits, so it has `2^r` seeds. Enumeration
then costs `2^r · T`, which is exponential. Polynomial cost requires
`s x` polynomial, i.e. seed length `O(log n)`: that is `SeedCompression`.
The classical route to it is a pseudorandom generator stretching `O(log n)`
truly random bits into `r` bits that fool the algorithm. Such generators are
known to exist under circuit lower bounds (Nisan–Wigderson; Impagliazzo–
Wigderson), which are themselves open. And before any of this, `NPinRP` for
SAT is open and widely believed false.

## 5. Known results and literature

* J. Gill, "Computational complexity of probabilistic Turing machines",
  SIAM J. Comput. 6(4), 1977. Probabilistic complexity classes, including
  BPP.
* L. Adleman, "Two theorems on random polynomial time", FOCS 1978. RP ⊆
  P/poly: a fixed advice string of good seeds works for every input of a
  given length. The same amplification-and-union-bound counting gives BPP ⊆
  P/poly.
* R. M. Karp and R. J. Lipton, "Some connections between nonuniform and
  uniform complexity classes", STOC 1980. If NP ⊆ P/poly, the polynomial
  hierarchy collapses to its second level. With BPP ⊆ P/poly this gives:
  NP ⊆ BPP collapses PH.
* K.-I. Ko, "Some observations on the probabilistic algorithms and NP-hard
  problems", Information Processing Letters 14(1), 1982. NP ⊆ BPP implies
  NP = RP, which is why the one-sided model here loses nothing essential.
* N. Nisan and A. Wigderson, "Hardness vs randomness", JCSS 49(2), 1994;
  R. Impagliazzo and A. Wigderson, "P = BPP if E requires exponential
  circuits: derandomizing the XOR lemma", STOC 1997. Seed compression
  (hence BPP = P) follows from circuit lower bounds.
* V. Kabanets and R. Impagliazzo, "Derandomizing polynomial identity tests
  means proving circuit lower bounds", Computational Complexity 13, 2004.
  Derandomizing polynomial identity testing would itself imply circuit lower
  bounds, so derandomization and lower bounds are tied in both directions.
* M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of
  Mathematics 160(2), 2004. A problem long known to have efficient
  randomized algorithms was derandomized unconditionally, by a
  problem-specific argument.
* U. Schöning, "A probabilistic algorithm for k-SAT and constraint
  satisfaction problems", FOCS 1999. Randomized walk for 3-SAT with expected
  time about `(4/3)^n` up to polynomial factors: randomization improves the
  exponent but remains exponential.

## 6. How far the idea can be pushed toward P vs NP

* **Proved (general):** exact seed-tuple counting, exponential one-sided
  amplification, correctness and cost of derandomization by enumeration, and
  the conditional theorem `rp_sat_with_seed_compression`.
* **Refuted (general):** "success on the tested seeds or instances implies a
  guarantee" (`observed_success_no_guarantee`).
* **Exact remaining obligation:**
  1. `NPinRP sz SAT`: a polynomial-time one-sided randomized algorithm for
     SAT. This is open and, by Karp–Lipton and Adleman, would collapse the
     polynomial hierarchy to its second level.
  2. `SeedCompression sz SAT`: logarithmic seed length. This is open in
     general and known to be tied to circuit lower bounds.

  Both are needed. `rp_sat_with_seed_compression` shows they suffice. Note
  that (1) alone is the statement NP = RP (since RP ⊆ NP, and SAT is
  NP-complete by the cited Cook–Levin theorem). It is open and widely
  believed false, but it is not known to imply P = NP.
* **For P ≠ NP** randomized search gives no route: a failing heuristic
  says nothing about all algorithms (see [Idea 12](Idea12.md) on why
  hardness has to be proved, not observed).

## 7. Failure modes this idea catches

* **Heuristics/probability** (family 8 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): empirical
  success rates on test seeds or random instances are not worst-case bounds
  (`observed_success_no_guarantee`).
* **Nondeterminism/randomness/quantum** (family 9): replacing P by RP or BPP
  changes the question. The step back to P is `SeedCompression`.
* **Hidden exponential work** (family 2): derandomizing by trying all
  `2^r` seeds is exponential unless `r = O(log n)`
  (`poly_seeds_derandomize`).
* **Easier/different problem** (family 5): average-case success on random
  instances is not worst-case solvability.
* **Uniformity** (family 16): Adleman's fixed good seeds give circuits
  (P/poly), not a uniform algorithm.

Audit rule: a randomized claim must state its error model (one- or
two-sided), prove the error bound for every input and all seeds, and state
separately how the randomness is removed.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea14.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea14.v
```

Both commands print nothing on success. Remove the generated
`Idea14.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
