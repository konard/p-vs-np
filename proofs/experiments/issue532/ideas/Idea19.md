# Idea 19 — Advice and nonuniformity

**Verdict:** Refuted as a route (general theorem)

Letting the solver receive advice (a hint that depends on the input length,
or on the input itself) is refuted as a route to a uniform polynomial SAT
algorithm. A single trivial machine with one advice bit per length decides
every unary language, including undecidable ones. The formal statement is that
the class escapes every `Nat`-indexed family; the step to undecidability uses
an enumeration of Turing machines, which is not formalized. Advice that depends on the
whole input decides every language. So the existence of an advice algorithm
carries no uniform algorithmic information. The opposite direction, a lower
bound against advice (NP ⊄ P/poly), would separate P from NP. It is recorded
on the shared machine and circuit model as the open obligations
`SATNotInPPoly` (`¬ InPPoly SAT`) and `NPNotInPPoly`
(`∃ L, InNP L ∧ ¬ InPPoly L`), and the conditional separations
`pNotEqualsNP_of_satNotInPPoly` and `pNotEqualsNP_of_npNotInPPoly` are proved
from the named known theorem `PSubsetPPoly`. In the same model, P/poly is
proved not to be contained in P (`ppoly_not_subset_p`).

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
* The schema is `NPNotInPPolyFor NP PPoly := ∃ L, NP L ∧ ¬ PPoly L`, with
  the classes as parameters (renamed from `NPNotInPPoly`).
* **Shared model.** `InPPoly L` (from `Circuits.lean`): some polynomial `p`
  bounds, at every positive length `n`, the gate count of a well-formed
  circuit deciding `L` on the words of length `n`. `PSubsetPPoly` (P ⊆ P/poly)
  is a named known theorem there.
* **Open obligations.** `SATNotInPPoly := ¬ InPPoly SAT` with
  `SAT = Issue532.Machines.SAT`, and
  `NPNotInPPoly := ∃ L, InNP L ∧ ¬ InPPoly L` (NP ⊄ P/poly).

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
| `NPNotInPPolyFor` (def) | Schema (renamed from `NPNotInPPoly`; Rocq: same name): some language of the class `NP` lies outside the class `PPoly`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `not_in_superclass_not_in_P` | `P ⊆ C` and `L ∉ C` imply `L ∉ P`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `nonuniform_lower_bound_separatesFor` | Schema form (renamed from `nonuniform_lower_bound_separates`): `P ⊆ PPoly` and `NPNotInPPolyFor NP PPoly` imply `¬ (NP ⊆ P)`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `inPPoly_lengthOnly` | Every language depending only on the input length is in `InPPoly`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `bijNat_injective` | The bijective base-2 numeral of a word is injective. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `unaryDiag_not_inP` | No machine of the shared model decides the unary diagonal. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `ppoly_not_subset_p` | `∃ L, InPPoly L ∧ ¬ InP L`: P/poly is not contained in P. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `SATNotInPPoly` (def) | Open obligation: `¬ InPPoly SAT`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `NPNotInPPoly` (def) | Open obligation: `∃ L, InNP L ∧ ¬ InPPoly L`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `npNotInPPoly_iff_for` | `NPNotInPPoly ↔ NPNotInPPolyFor InNP InPPoly`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `satNotInPPoly_iff_superpoly` | `SATNotInPPoly ↔ SuperpolyLowerBound SAT`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `npNotInPPoly_of_sat` | `SATInNP → SATNotInPPoly → NPNotInPPoly`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `pNotEqualsNP_of_npNotInPPoly` | Conditional: `PSubsetPPoly → NPNotInPPoly → PNotEqualsNP`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `pNotEqualsNP_of_satNotInPPoly` | Conditional: `SATInNP → PSubsetPPoly → SATNotInPPoly → PNotEqualsNP`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `nonuniform_lower_bound_separates` | The schema theorem at the shared classes: `PSubsetPPoly → NPNotInPPoly → PNotEqualsNP`. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `not_inPPoly_nonvacuous` | Non-vacuity: some language is outside `InPPoly` (counting), and constant languages are inside. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |
| `ppoly_strictly_bigger_than_p_if` | With `PSubsetPPoly`, P is strictly contained in P/poly. | [Idea19.lean](../lean/Idea19.lean) | [Idea19.v](../rocq/Idea19.v) |

Differences between the two files:

* Rocq has no function extensionality in the core. So
  `advice_escapes_every_enumeration`, `adviceOf_injective` and
  `no_enumeration_of_advice_class` are stated pointwise in Rocq, for example
  `∃ n, U n ≠ e i n` instead of `U ≠ e i`. The pointwise form is at least as
  strong for these two escape statements. For `adviceOf_injective` both the
  hypothesis and the conclusion are pointwise
  (`∀ n, adviceOf U n = adviceOf V n → ∀ n, U n = V n`), which is the natural
  form without function extensionality.
* Lean uses `funext`, which is a theorem in Lean 4 core, not an axiom
  declaration.
* `unaryDiag` is a different, computable language in Rocq. Lean defines it
  noncomputably as "no machine with code `n` accepts `1^n` in any number of
  steps", which is undecidable, so no computable definition can be
  equivalent to it. Rocq decodes `n` to a word with `bijWord n n` (the
  Rocq-only inverse of `bijNat`, see `bijWord_bijNat`), decodes that word to
  a (machine, polynomial) pair with `decMachinePoly`, and flips the output
  of the step-bounded `clockedLanguage` on `1^n`. `unaryDiag_not_inP` and
  `ppoly_not_subset_p` have the Lean statements. `bijNat_injective` is
  proved through `bijWord_bijNat` and `length_le_bijNat`.
* `satNotInPPoly_iff_superpoly` takes an extra premise
  `(forall P : Prop, P \/ ~ P)`, because the shared
  `superpoly_iff_not_inPPoly` in `Circuits.v` needs it for the direction
  `¬ InPPoly L → SuperpolyLowerBound L`. It is a premise, not an axiom.
* `pNotEqualsNP_of_satNotInPPoly` has the Lean statement and is proved
  directly from `not_inP_of_not_inPPoly` and `inP_sat_of_pEqualsNP`, without
  excluded middle.

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
(`2^s ≤ 2^n` of them) gives `fixed_machine_advice_limited`. This is a
diagonal analogue of Shannon's counting argument, and much weaker. It shows
only that `n` advice bits do not let a fixed evaluator decide every language
on length `n`. Counting (not formalized) shows more: there are `2^(2^n)`
functions but at most `2^s` advice strings, so most Boolean functions on `n`
inputs need about `2^n` advice bits for a fixed evaluator, and circuits of
size about `2^n / n`.

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
  `NPNotInPPoly` (or `SATNotInPPoly`, with `SATInNP`) together with the named
  known theorem `PSubsetPPoly` gives P ≠ NP
  (`pNotEqualsNP_of_npNotInPPoly`, `pNotEqualsNP_of_satNotInPPoly`). The obligation implies P ≠ NP (with
  the standard classes, where P ⊆ P/poly), and the converse implication is
  not known. By the NP-completeness of SAT (Cook–Levin, cited, not
  formalized) and closure of P/poly under polynomial-time reductions, it is
  equivalent to SAT having no polynomial-size circuit family.
* **Barriers.** Circuit lower bounds for NP face the natural proofs barrier
  (Razborov–Rudich, *JCSS* 1997, assuming pseudorandom functions) and
  relativization (Baker–Gill–Solovay 1975) where applicable. Ideas 16 and
  38 formalize parts of the relativization barrier. The natural proofs
  barrier is only cited, here and in Idea 30.
* **Non-vacuity and caveats.** `¬ InPPoly L` is satisfiable (by Shannon
  counting in `Circuits.lean`, for a language not known to be in NP) and
  fails for constant languages (`not_inPPoly_nonvacuous`). `InPPoly` only
  constrains positive lengths: with length 0 included, a fixed-length
  circuit convention made `SAT` vacuously outside P/poly (the empty circuit
  outputs `false` on the empty word, which encodes a satisfiable formula);
  `Circuits.lean` now quantifies over `0 < n`. `PSubsetPPoly` is a named
  hypothesis, not proved here.

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
  fixed, `fixed_machine_advice_limited` shows what the diagonal form gives:
  hardness of *some* language, not of SAT specifically.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea19.lean
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Circuits.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea19.v
for f in proofs/complexity/rocq/Complexity proofs/experiments/issue532/rocq/Machines \
         proofs/experiments/issue532/rocq/Circuits proofs/experiments/issue532/rocq/Idea19; do
  rm -f "$f.vo" "$f.vok" "$f.vos" "$f.glob" "$(dirname "$f")/.$(basename "$f").aux"
done
```

The compile commands print nothing on success.
