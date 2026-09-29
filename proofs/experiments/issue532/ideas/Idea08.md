# Idea 08 — Program induction and generalization from finite examples

**Verdict:** Refuted as a route (general theorem)

A finite set of examples does not determine a function. For every consistent
sample and every unseen input, two consistent total functions disagree there
(`two_consistent_extensions`). On `k` unseen inputs, all `2^k` labellings are
consistent (`all_patterns_consistent`). The lookup table always fits
(`lookup_consistent`), so fitting is never the hard part: the hard part is
choosing among the fits. Generalization becomes possible only for a restricted
hypothesis class. Consistent elimination then identifies the target once the
inputs separate the class (`elimination_identifies`), but the computational cost
moves to finding a consistent hypothesis, which is NP-hard for natural classes.

## 1. The idea at full strength

Ambitious version: infer the program (or the SAT-solving rule, or the
structure of the witnesses) from finitely many solved examples. Then run the
inferred program on new instances. If the induction step were sound and
efficient, the learned program would decide the problem everywhere. A variant
aimed at P ≠ NP says that "shortest-program induction is NP-hard, therefore
solving NP-hard problems requires it".

Source in issue #532: Part I item 3 ("Finding the shortest program is
undecidable … When restricted to finite observed data … decidable but NP-hard
(via generalization/compression) … ✖ We don't know optimal generalization
principles"), Part I item 4 ("The shortest program is just a map … Lookup
tables are not shortest in general. Generalization is compression. Compression
is hypothesis search. Hypothesis search is NP-hard"), and Part II Phase 3
("Program induction from finite examples — MDL-style formulations"). The
failure points recorded here are `two_consistent_extensions` (data alone
cannot decide) and `no_separation_unrestricted` (no finite sample identifies a
function from the class of all functions).

## 2. Precise mathematical formulation

* **Sample.** `S : List (ℕ × Bool)` (input, label). `Consistent f S :⇔ ∀ p ∈ S, f p.1 = p.2`.
  `SampleConsistent S :⇔ ∃ f, Consistent f S`. `inputs S = S.map fst`.
* **Extensions.** `ext f0 U m` overwrites `f0` on the list of points `U` with
  the bits `m`, position by position.
* **Lookup table.** `lookup S y` returns the label of the first example with
  input `y`, and `false` if there is none.
* **Restricted class.** A finite list `H` of hypotheses `ℕ → Bool`.
  `labelWith t xs` labels inputs `xs` by the target `t`. `survivors H S`
  filters `H` by consistency with `S`. `Separates xs H :⇔` any two members of
  `H` that agree on `xs` agree everywhere.
* **The claim the route needs.** A procedure that, from a finite sample of a
  target `t`, outputs a program equal to `t` on *all* inputs, for every target
  in the intended class, and does so in polynomial time.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `two_consistent_extensions` | If `SampleConsistent S` and `x ∉ inputs S`, then `∃ f g, Consistent f S ∧ Consistent g S ∧ f x ≠ g x`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `ext_outside` | `y ∉ U → ext f0 U m y = f0 y`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `ext_pattern` | If `U` has no duplicates and `|m| = |U|`, then `U.map (ext f0 U m) = m`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `all_patterns_consistent` | If `SampleConsistent S`, `U` has no duplicates, `U` is disjoint from `inputs S`, and `|m| = |U|`, then `∃ f, Consistent f S ∧ U.map f = m`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `length_allStrings` | `|allStrings n| = 2^n`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `mem_allStrings_iff` | `v ∈ allStrings n ↔ |v| = n`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `realised_patterns` | Under the hypotheses of `all_patterns_consistent`, `|allStrings |U|| = 2^|U|`, and every `m ∈ allStrings |U|` is `U.map f` for some `f` consistent with `S`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `lookup_consistent` | `SampleConsistent S → Consistent (lookup S) S`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `mem_survivors` | `h ∈ survivors H (labelWith t xs) ↔ h ∈ H ∧ ∀ x ∈ xs, h x = t x`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `elimination_identifies` | If `t ∈ H` and `Separates xs H`, then `t ∈ survivors H (labelWith t xs)` and every survivor `h` satisfies `∀ y, h y = t y`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |
| `no_separation_unrestricted` | If `x ∉ xs`, then for every `f0` there are `f, g` with `∀ y ∈ xs, f y = g y` and `f x ≠ g x`. | [Idea08.lean](../lean/Idea08.lean) | [Idea08.v](../rocq/Idea08.v) |

Not machine-checked: the PAC bounds, the NP-hardness results and the other
literature in Section 5. The spec's counting form "exactly `2^(N−m)`
consistent functions on an `N`-point domain with `m` distinct sample points" is
covered only in part by `realised_patterns` with `U` equal to the `N − m`
unsampled points. It shows that each of the `2^(N−m)` entries of
`allStrings (N−m)` (all bit strings of that length, by `mem_allStrings_iff`) is
the restriction to `U` of some function consistent with `S`. That these entries
are pairwise distinct, and the matching upper bound (a consistent restriction
is determined by its values on `U`), are immediate but are not stated as
theorems. So the exact count is not itself machine-checked.

## 4. Complete argument

**Two extensions.** Take any `f0` consistent with `S`. Let `f = f0` with `x ↦
true`, and `g = f0` with `x ↦ false`. Every example input differs from `x`, so
`f`, `g` agree with `f0` on all inputs of `S`, and `f x = true ≠ false = g x`.

**All patterns.** `ext f0 U m` sets the `i`-th point of `U` to the `i`-th bit
of `m`. Since `U` has no duplicates, the value at `U[i]` is not overwritten by
a later entry, so `U.map (ext f0 U m) = m` (induction on `U`). Outside `U` the
function equals `f0`, and the sample inputs are outside `U`, so consistency
is inherited from `f0`. As `m` ranges over the `2^k` strings of length
`k = |U|`, the restrictions to `U` range over all `2^k` patterns.

Worked example: `S = [(0, true), (1, false)]`, `U = [2, 3, 4]`. There are 8
consistent functions with pairwise different behaviour on `{2, 3, 4}`, one for
each of the 8 patterns. Any rule that picks one of them ("simplest",
"shortest", "smoothest") adds an assumption that is not in the data.

**Lookup table.** Induction on `S`. For the head `(a, b)`, `lookup` returns
`b`. For a later example `p` with `p.1 = a`, consistency of the sample (a
single `f0` fits both) forces `p.2 = f0 a = b`. Otherwise `lookup` recurses.
So memorisation always fits, and its size grows with the data. This is the
issue's point that "the shortest program is just a map" when nothing further is
assumed.

**Elimination.** Survivors are exactly the members of `H` that agree with `t`
on `xs` (`mem_survivors`). Separation turns agreement on `xs` into agreement
everywhere. For the class of all functions, `no_separation_unrestricted`
shows that no finite `xs` separates. So identification from finite data
*requires* a restricted class, and the restriction is the real content.

## 5. Known results and literature

* E. M. Gold, "Language identification in the limit", *Information and
  Control* 10(5), 1967. Identification from examples depends on the class,
  and some natural classes are not identifiable. (Not formalized.)
* E. M. Gold, "Complexity of automaton identification from given data",
  *Information and Control* 37(3), 1978. Finding a minimum DFA consistent with
  given examples is NP-hard. This is the "decidable but NP-hard" regime of
  Part I item 3. (Not formalized.)
* L. G. Valiant, "A theory of the learnable", *Communications of the ACM*
  27(11), 1984. Introduces PAC learning. (Not formalized.)
* A. Blumer, A. Ehrenfeucht, D. Haussler, M. K. Warmuth, "Occam's razor",
  *Information Processing Letters* 24(6), 1987. A consistent hypothesis from
  a finite class `H`, found from `O((ln|H| + ln(1/δ))/ε)` examples,
  generalizes with high probability. Short consistent hypotheses (compression)
  imply learning. (Not formalized. `elimination_identifies` is the exact,
  noise-free, distribution-free analogue.)
* L. Pitt and L. G. Valiant, "Computational limitations on learning from
  examples", *J. ACM* 35(4), 1988. Properly learning 3-term DNF is NP-hard
  (it cannot be done in polynomial time unless RP = NP), even though
  3-term DNF is learnable with a larger hypothesis class (3-CNF). (Not
  formalized.)
* D. H. Wolpert, "The lack of a priori distinctions between learning
  algorithms", *Neural Computation* 8(7), 1996 (no-free-lunch). Averaged
  uniformly over all targets, every learner has the same off-sample error.
  This is the probabilistic counterpart of `all_patterns_consistent`. (Not
  formalized.)

## 6. How far the idea can be pushed toward P vs NP

**At full potential.** With a finite class `H` and separating inputs,
consistent elimination is exact (`elimination_identifies`). With `H` given
succinctly (programs of size `≤ s`, circuits, DFAs), Occam's razor gives
sample efficiency. The computational step is then "find some `h ∈ H`
consistent with the data". For natural succinct classes that step is NP-hard
(Gold 1978; Pitt–Valiant 1988). So program induction does not *solve* NP
problems. It *contains* an NP search as a subroutine, matching the issue's
chain "Compression is hypothesis search. Hypothesis search is NP-hard."

**Remaining obligation.** The unrestricted route is refuted outright. No
finite sample determines the function (`two_consistent_extensions`), so no
`def` obligation is introduced for it. For the restricted route, the obligation
is a polynomial-time consistent-hypothesis finder for a class rich enough to
contain a SAT decider. For classes whose consistency problem is NP-hard (minimum
DFAs, Gold 1978; 3-term DNF, Pitt–Valiant 1988), such a finder would decide an
NP-hard problem in polynomial time and hence, by those cited reductions and
Cook–Levin (none formalized), give Idea 01's `PolySATDecider`. The P ≠ NP direction is not available here either: "shortest
consistent program is NP-hard to find" says nothing about whether *other*
algorithms can decide SAT, because a decider need not be learned from examples.

**Barriers.** Distribution-free lower bounds on sample complexity
(VC-dimension) and the NP-hardness of proper learning mean that both the
information side and the computation side are limited. Neither kind of limit
separates P from NP.

## 7. Failure modes this idea catches

* **Local-to-global inference**
  ([error family 6](../../../attempts/COMMON_ERRORS.md#6-replacing-global-consistency-with-local-or-greedy-consistency)):
  agreement on sampled inputs does not imply agreement everywhere
  (`no_separation_unrestricted`).
* **Heuristics and experiments treated as proof**
  ([family 8](../../../attempts/COMMON_ERRORS.md#8-treating-heuristics-experiments-or-probability-as-proof)):
  a rule that works on all tested instances has only been checked on a sample,
  and `all_patterns_consistent` shows the untested instances are unconstrained.
* **Verification versus search**
  ([family 15](../../../attempts/COMMON_ERRORS.md#15-confusing-verification-search-construction-and-certificates)):
  some hypothesis always fits the data (`lookup_consistent`), and checking a
  given hypothesis against a finite sample is a direct evaluation. Finding a
  *small* one is the hard search problem (informal; see Section 5).
* **Different problem**
  ([family 5](../../../attempts/COMMON_ERRORS.md#5-solving-an-easier-special-approximate-or-different-problem)):
  success in PAC learning (approximately correct, with high probability, on a
  distribution) is not exact worst-case decision.
* **Provability vs computability**
  ([family 10](../../../attempts/COMMON_ERRORS.md#10-confusing-provability-computability-decidability-and-complexity)):
  shortest-program induction is undecidable in general and NP-hard on finite
  data. These are different statements and should not be conflated.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea08.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea08.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea08.{vo,vok,vos,glob}` and
`.Idea08.aux` files.
