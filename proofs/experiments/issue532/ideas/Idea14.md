# Idea 14 — Randomized search

**Verdict:** Developed to an open obligation (conditional theorem proved). Randomness is a legitimate resource with correct general laws. One-sided error amplifies exponentially with repetition (`rp_amplification`, proved by exact counting of seed tuples). A one-sided algorithm with polynomially many seeds is derandomized by enumeration (`enumeration_decides`, `poly_seeds_derandomize`, and on machines `logSeed_enumeration`). Random search does not reach P = NP by itself. Observing success on test seeds gives no error bound (`observed_success_no_guarantee`). The route needs two open statements about the shared machine model, recorded as definitions and never assumed: SAT has a polynomial-time one-sided randomised machine (`NPinRP : InRP SAT`), and its random strings can be compressed to logarithmic length (`SeedCompression SAT`). Together with the named known theorem `SeedEnumeration`, they yield a polynomial-time machine decider for SAT (`rp_sat_with_seed_compression`) and, with SAT's NP-hardness, P = NP (`rp_route_gives_pEqualsNP`). Time is the step count of `Complexity.Run`. The obligations are not vacuous: `InRP` fails for some language (`not_forall_inRP`).

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
* **Machine model.** Words, machines, `Run`, `pairedInput`, `InP`,
  `PEqualsNP` come from `proofs/complexity/lean/Complexity.lean`, and `SAT`,
  `PolyDec`, `SATHard` from `proofs/experiments/issue532/lean/Machines.lean`.
  A randomised machine runs on `pairedInput x r` for a random string `r`, and
  its time is the step count of `Run`.
  * `seedWord ℓ i` is the `i`-th binary string of length `ℓ`; by
    `seedWord_surjective`, seeds `i < 2^ℓ` enumerate every string of length
    `ℓ`.
  * `HaltsWithin m p ℓ`: on every `x` and every seed `i`, `m` halts on
    `pairedInput x (seedWord (ℓ |x|) i)` within `p.eval (|x| + ℓ |x| + 1)`
    steps.
  * `seedAccepts m ℓ x i` says seed `i` makes `m` accept `x`.
  * `RPMachine m p R L :≡ HaltsWithin m p R.eval ∧
    OneSided L (seedAccepts m R.eval) (x ↦ 2^(R.eval |x|))`: random strings of
    polynomial length `R`, no false accepts, at most half the strings reject a
    yes-instance. `InRP L :≡ ∃ m p R, RPMachine m p R L`.
  * `logSeed k n = k · ⌊log₂(n+1)⌋`, with `2^(logSeed k n) ≤ (n+1)^k`
    (`two_pow_logSeed`). `PolySeedMachine m p k L` is `RPMachine` with random
    strings of length `logSeed k`, and `PolySeedRP L :≡ ∃ m p k,
    PolySeedMachine m p k L`.
  * The random-string length is always an explicit polynomial or
    `logSeed k`, never an arbitrary function of the input length (which would
    smuggle in advice).
* **Open obligations:**

```lean
def NPinRP : Prop := InRP SAT
def SeedCompression (L : Language) : Prop := InRP L → PolySeedRP L
```

* **Named known theorem, not mechanised here:**
  `SeedEnumeration : Prop := ∀ L, PolySeedRP L → InP L`. Its mathematics is
  proved (`logSeed_enumeration`: trying all at most `(n+1)^k` seeds, each run
  halting within `p`, gives the right answer). The missing part is the
  single-tape machine that enumerates the seeds and simulates `m`, which is
  the standard derandomization-by-enumeration argument (Gill 1977).

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
| `seedWord_surjective` | Seeds `i < 2^ℓ` enumerate every random string of length `ℓ`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `two_pow_logSeed` | `2^(k·⌊log₂(n+1)⌋) ≤ (n+1)^k`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `logSeed_enumeration` | For a `PolySeedMachine`: enumerating all seeds decides `L`, there are at most `(n+1)^k` seeds, and each run halts within `p`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `rp_sat_with_seed_compression` | `NPinRP → SeedCompression SAT → SeedEnumeration → PolyDec SAT`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `rp_route_gives_pEqualsNP` | `NPinRP → SeedCompression SAT → SeedEnumeration → SATHard → PEqualsNP`. | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |
| `not_forall_inRP` | Non-vacuity: `InRP` fails for some language (diagonalisation against `rpLanguage`). | [Lean](../lean/Idea14.lean) | [Rocq](../rocq/Idea14.v) |

`NPinRP` and `SeedCompression` are `def ... : Prop` over the shared machine
model and are never assumed. `SeedEnumeration` is a named hypothesis, not an
axiom. No theorem in either file proves or refutes P = NP. The counting rows
are in both files under the same names. The machine-model rows (`seedWord`,
`HaltsWithin`, `RPMachine`, `InRP`, `PolySeedMachine`, `logSeed_enumeration`,
`rp_sat_with_seed_compression`, `rp_route_gives_pEqualsNP`,
`not_forall_inRP`) are Lean-only for now. The intended Rocq names are the same;
`Idea14.v` still has the earlier abstract-cost version, including
`polySeedRP_implies_poly`.

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

**On machines.** For a `PolySeedMachine m p k L`, `seedAccepts` is
`OneSided`, so enumeration over the `2^(logSeed k |x|) ≤ (|x|+1)^k` seeds
decides `L`, and each of these runs halts within `p` steps
(`logSeed_enumeration`). Packaging this as one machine is `SeedEnumeration`.
Given it, `NPinRP` and `SeedCompression SAT` give `InP SAT`, hence
`PolyDec SAT` by `polyDec_iff_inP`, and with `SATHard`, P = NP.

**Non-vacuity.** The language decided by a one-sided machine is determined by
the pair `(m, R)` (`rpLanguage`, by `enumeration_decides`). Since machine and
polynomial pairs have an injective encoding into words, a diagonal language
differs from every `rpLanguage`, so it is not in `InRP` (`not_forall_inRP`).
So `NPinRP` is a real statement about SAT.

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
  amplification, correctness and cost of derandomization by enumeration
  (abstractly and, via `logSeed_enumeration`, for machines with logarithmic
  seeds), and the conditional theorems `rp_sat_with_seed_compression` and
  `rp_route_gives_pEqualsNP`.
* **Refuted (general):** "success on the tested seeds or instances implies a
  guarantee" (`observed_success_no_guarantee`).
* **Exact remaining obligation** (over the shared machine model, time = `Run`
  step count):
  1. `NPinRP : InRP SAT`: a polynomial-time one-sided randomised machine for
     SAT. This is open and, by Karp–Lipton and Adleman, would collapse the
     polynomial hierarchy to its second level.
  2. `SeedCompression SAT : InRP SAT → PolySeedRP SAT`: logarithmic
     random-string length. This is open in general and known to be tied to
     circuit lower bounds.

  Both are needed. `rp_sat_with_seed_compression` shows they suffice,
  together with the named known theorem `SeedEnumeration` and, for
  `PEqualsNP`, `SATHard` (Cook–Levin). Note that (1) alone is the statement
  NP = RP (since RP ⊆ NP, and SAT is NP-complete by the cited Cook–Levin
  theorem). It is open and widely believed false, but it is not known to imply
  P = NP. `not_forall_inRP` shows `InRP` is a genuine restriction.
* **For P ≠ NP** randomized search gives no route: a failing heuristic
  says nothing about all algorithms (see [Idea 12](Idea12.md) on why
  hardness has to be proved, not observed).
* **Caveats.** `SeedEnumeration` (the enumerating machine) and `SATHard` are
  named hypotheses, not mechanised; both are standard theorems. The
  machine-model part is Lean-only so far; `Idea14.v` keeps the earlier
  abstract-cost version, where the declared time is not tied to execution.

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
