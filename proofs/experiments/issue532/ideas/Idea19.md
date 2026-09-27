# Idea 19 — Advice and nonuniformity

**Verdict:** Refuted as a route (general theorem)

Letting the solver receive advice (a hint that depends on the input length,
or on the input itself) is refuted as a route to a uniform polynomial SAT
algorithm. A single trivial machine with one advice bit per length decides
every unary language, including undecidable ones. Advice that depends on the
whole input decides every language. So the existence of an advice algorithm
carries no uniform algorithmic information. The opposite direction, a lower
bound against advice (NP ⊄ P/poly), would separate P from NP. It is recorded
as the open obligation `NPNotInPPoly`, and the conditional separation is
proved.

## 1. The idea at full strength

Issue #532 Phase 5 ("Iterate alternative models") lists "Non-uniform advice"
among the assumptions to change deliberately, and Phase 1 asks for a formal
definition of P/poly. Part I item 4 ("Lookup tables vs generalization") treats
the related claim that "The shortest program is just a map". A per-length
lookup table is exactly an advice string. At full strength the idea reads:

> If a polynomial-time machine, given a short hint for each input length,
> decides SAT, then SAT is easy. So look for the hint and treat it as part of
> the algorithm (toward P = NP). Conversely, show that no short hint suffices
> for SAT (toward P != NP).

The first reading claims that *SAT ∈ P/poly, or an advice-assisted algorithm
for SAT, yields SAT ∈ P*. The second reading claims *SAT ∉ P/poly*.

## 2. Precise mathematical formulation

* An advice machine is `M : List α → List Bool → Bool`. An advice sequence is
  `a : Nat → List Bool`. `M` with `a` decides `L` when
  `∀ x, M x (a x.length) = L x` (`AdviceDecides`).
* Unary languages are functions `U : Nat → Bool`, read on inputs
  `x : List Unit` as `U x.length`. `readAdvice` returns the first advice bit.
  `adviceOf U n = [U n]`.
* P/poly (Karp–Lipton) is the class of languages decided by a
  polynomial-time machine with advice of polynomial length. It contains P,
  since the advice can be empty.
* The open obligation is `NPNotInPPoly NP PPoly := ∃ L, NP L ∧ ¬ PPoly L`.
  The classes are abstract predicates on languages. With the standard
  classes this is the open statement NP ⊄ P/poly.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `unary_decided_by_advice` | For every `U : Nat → Bool`, `readAdvice` with advice `[U n]` decides the unary language of `U`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `adviceOf_length` | The advice has exactly one bit per length. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `adviceOf_injective` | Distinct languages receive distinct advice sequences. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `advice_escapes_every_enumeration` | For every family `e : Nat → Nat → Bool` there is a unary `U` with one-bit advice that differs from every `e i`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `no_enumeration_of_advice_class` | No `Nat`-indexed family contains every language of the one-bit-advice class. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `input_advice_trivializes` | With input-dependent advice, the machine "output the advice" decides every language. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `toNat_fromNat`, `fromNat_length` | Binary encoding of `i < 2^n` as a length-`n` string is invertible. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `diagonal_against_advice_list` | For any `M` and any list of at most `2^n` advice strings, some language defeats `M` on length `n` under every one of them. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `fixed_machine_advice_limited` | A fixed `M` with advice of length `s ≤ n` cannot decide every language on inputs of length `n`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `uniform_in_advice` | Every uniform decider is an advice machine with empty advice (abstract P ⊆ P/poly). | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `NPNotInPPoly` (def) | Open obligation: some NP language lies outside the advice class. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `not_in_superclass_not_in_P` | `P ⊆ C` and `L ∉ C` imply `L ∉ P`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `nonuniform_lower_bound_separates` | `P ⊆ PPoly` and `NPNotInPPoly NP PPoly` imply `¬ (NP ⊆ P)`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |

Differences between the two files:

* Rocq has no function extensionality in the core. So
  `advice_escapes_every_enumeration`, `adviceOf_injective` and
  `no_enumeration_of_advice_class` are stated pointwise in Rocq, for example
  `∃ n, U n ≠ e i n` instead of `U ≠ e i`. The pointwise form is at least as
  strong.
* Lean uses `funext`, which is a theorem in Lean 4 core, not an axiom
  declaration.

## 4. Complete argument

**Advice decides everything unary.** Given `U`, put `a n := [U n]`. On input
`1^n` the machine reads its advice bit and outputs `U n`. Correctness is
definitional, and no property of `U` (computability, complexity) is used.

**Diagonal escape.** Let `e : Nat → (Nat → Bool)` be any family. For
example, `e i` may be the unary language decided by the `i`-th Turing
machine. Such a family exists because Turing machines can be enumerated, but
the machine model itself is not formalized here. Define
`U n := ¬ e n n`. Then `U i ≠ e i i` for each `i`, so `U ≠ e i`. By the
previous paragraph `U` has one-bit advice. So the class of one-bit-advice
languages is not contained in any countable class, and in particular it
contains undecidable languages. An advice algorithm for SAT therefore
implies nothing about a uniform algorithm. The advice sequence may itself be
uncomputable, and the class it lives in contains uncomputable languages.

**Input-dependent advice.** If the hint may depend on `x` itself, set the
hint to `L x`. Then "output the hint" is correct for every `L`. This is the
precise sense in which "the answer as a hint" is circular.

**Fixed machines with short advice are limited.** Fix `M` and `n`, and let
`A` be a list of at most `2^n` advice strings. Index inputs of length `n` by
their binary value `toNat x < 2^n`, which is invertible by `fromNat`. Define
`L x := ¬ M x (A[toNat x])`. For `w = A[i]`, the input `x = fromNat n i`
satisfies `M x w ≠ L x`. Taking `A` to be all strings of length `s ≤ n`
(`2^s ≤ 2^n` of them) gives `fixed_machine_advice_limited`. This is the
formal core of Shannon's counting argument: most Boolean functions on `n`
inputs need exponentially many advice bits, or exponential circuit size,
for any fixed evaluator.

*Worked example.* Take `n = 1`, `s = 1`, and `M x w := w.head`. Then
`A = allVecs 1 = [[false],[true]]` and `L [false] = ¬ M [false] [false] =
true`, `L [true] = ¬ M [true] [true] = false`. Advice `[false]` fails on
input `[false]`, and advice `[true]` fails on input `[true]`.

**Conditional separation.** Assume `P ⊆ PPoly` and `L ∈ NP \ PPoly`. If
`NP ⊆ P`, then `L ∈ P ⊆ PPoly`, which is a contradiction.

## 5. Known results and literature

* R. M. Karp and R. J. Lipton, "Some connections between nonuniform and
  uniform complexity classes", *STOC* 1980. This paper introduced advice
  classes such as P/poly. The Karp–Lipton theorem states that NP ⊆ P/poly
  implies the polynomial hierarchy collapses to Σ₂ᵖ. The fact that P/poly
  contains undecidable unary languages is standard folklore; its core is the
  diagonal argument formalized here.
* L. Adleman, "Two theorems on random polynomial time", *FOCS* 1978.
  Proves RP ⊆ P/poly. The same amplification argument gives BPP ⊆ P/poly.
* C. E. Shannon, "The synthesis of two-terminal switching circuits", *Bell
  System Technical Journal* 28 (1949). Most Boolean functions of `n`
  variables require circuits of size about `2^n / n`.
* Nonuniform lower bounds that are known are much weaker than the
  obligation. The best explicit general circuit lower bounds are linear, a
  small constant times `n`.

What is **not** formalized:

* Turing machines, polynomial time, and the actual classes P, NP and P/poly.
* The Karp–Lipton collapse and Adleman's theorem.
* The counting version of Shannon's bound. Only the diagonal form for a
  fixed evaluator is proved.

## 6. How far the idea can be pushed toward P vs NP

* **As an upper-bound route (P = NP): refuted.** An advice algorithm is not
  an algorithm. The class it certifies membership in contains languages
  outside every countable family (`advice_escapes_every_enumeration`).
  Turning an advice algorithm into a uniform one needs a uniform procedure
  that *computes the advice* in polynomial time, which is the original
  problem again. If that procedure exists the advice is unnecessary.
* **As a lower-bound route (P ≠ NP): developed to an open obligation.**
  `NPNotInPPoly` together with `P ⊆ P/poly` gives P ≠ NP
  (`nonuniform_lower_bound_separates`). The obligation is strictly stronger
  than P ≠ NP as far as is known. It is implied by, but not known to be
  equivalent to, superpolynomial circuit lower bounds for SAT.
* **Barriers.** Circuit lower bounds for NP face the natural proofs barrier
  (Razborov–Rudich, *JCSS* 1997, assuming pseudorandom functions) and
  relativization (Baker–Gill–Solovay 1975) where applicable. See Ideas
  33–40 for barrier formalizations.

## 7. Failure modes this idea catches

* **Hidden advice or a precomputed table** (family 12, circular reasoning:
  the hint contains the answer). A "polynomial algorithm" that uses a lookup table
  indexed by input length, or a hint that depends on the input, is an advice
  algorithm. `input_advice_trivializes` and `unary_decided_by_advice` show
  that such algorithms exist for every language.
* **Nonuniform vs uniform confusion** (family 16). A family of polynomial-size circuits,
  one per `n`, does not give a polynomial-time algorithm unless the family
  is uniformly generated.
* **Counting fallacies** (family 7). An argument that "there are too few short programs
  to solve SAT" proves nothing without a fixed evaluator. With the evaluator
  fixed, `fixed_machine_advice_limited` shows exactly what counting gives:
  hardness of *some* language, not of SAT specifically.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea19.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea19.v
rm -f proofs/experiments/issue532/rocq/Idea19.vo proofs/experiments/issue532/rocq/Idea19.vok \
      proofs/experiments/issue532/rocq/Idea19.vos proofs/experiments/issue532/rocq/Idea19.glob \
      proofs/experiments/issue532/rocq/.Idea19.aux
```

Both commands print nothing on success.
