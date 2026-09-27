# Idea 15 — Circuit depth versus size

**Verdict:** Correct tool, insufficient alone (general theorem proved). Size and depth are different resources, and the exact relation between them for formulas is proved in general: `depth < size < 2^(depth+1)` and `leaves ≤ 2^depth` (`size_le_pow_depth`, `leaves_le_pow_depth`, `depth_lt_size`). Both extremes are attained, even by formulas for the same function with the same size (`same_function_different_depth`). Depth lower bounds are the right tool for separations below P, and a superpolynomial formula-size lower bound implies a superlogarithmic depth lower bound (`sizeLB_implies_depthLB`). Even the open obligation `DepthLB` for an explicit NP family would only give NP ⊄ NC¹, a statement not known to imply, or to follow from, P ≠ NP.

## 1. The idea at full strength

Some attempts argue about the "depth" of a computation: SAT "needs
sequential steps", so any circuit for it is deep, so it is hard; or,
conversely, a shallow (parallel) algorithm is exhibited and claimed to be
efficient. Others conflate the two measures: a formula is shown to have
large depth and this is taken as a size lower bound, or a formula is
balanced and claimed to become small.

At full strength the idea is to use depth lower bounds, which are
equivalent to formula-size lower bounds by Spira's theorem and to
communication complexity by Karchmer–Wigderson, as a route to lower bounds
for NP. The dossier fixes the exact relations between the measures, shows
that they are tight, and states precisely what a depth lower bound would
and would not give.

## 2. Precise mathematical formulation

A formula is a tree `F ::= var i | neg F | conj F F | disj F F`, evaluated
under an assignment `ρ : ℕ → Bool`.

* `size`: number of nodes (leaves and gates).
* `leaves`: number of variable occurrences.
* `depth`: length of the longest root-to-leaf path. Variables have depth 0,
  and each gate adds 1 to the maximum depth of its children.
* `chain n = (((x₀ ∧ x₁) ∧ x₂) ∧ ⋯) ∧ xₙ`.
* `bal d i` is the balanced AND tree over the `2^d` variables
  `x_{i·2^d}, …, x_{(i+1)·2^d − 1}`.
* `andRange a m ρ = ρ a ∧ ⋯ ∧ ρ (a + m − 1)`.
* A formula `f` *computes* `g : (ℕ → Bool) → Bool` if
  `eval ρ f = g ρ` for all `ρ`.

**Open obligations (definitions, never assumed).** Let
`fam : ℕ → (ℕ → Bool) → Bool` be a family, with `fam n` a function of `n`
variables.

* `FormulaSizeLB fam :≡ ∀ c, ∃ n, ∀ f, Computes f (fam n) → 2^(c·(log₂ n + 1)) ≤ size f`.
  This says superpolynomial formula size.
* `DepthLB fam :≡ ∀ c, ∃ n, ∀ f, Computes f (fam n) → c·(log₂ n + 1) ≤ depth f`.
  This says superlogarithmic depth.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `size_le_pow_depth` | Every formula satisfies `size + 1 ≤ 2^(depth + 1)`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `leaves_le_pow_depth` | Every formula satisfies `leaves ≤ 2^depth`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `depth_lt_size` | Every formula satisfies `depth < size`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `chain_size` | `size (chain n) = 2n + 1`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `chain_depth` | `depth (chain n) = n`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `eval_chain` | `chain n` computes `x₀ ∧ ⋯ ∧ xₙ`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `bal_size` | `size (bal d i) + 1 = 2^(d+1)`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `bal_depth` | `depth (bal d i) = d`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `eval_bal` | `bal d i` computes the AND of its `2^d` variables. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `same_function_different_depth` | For every `d`, `chain (2^d − 1)` and `bal d 0` compute the same function with the same size, with depths `2^d − 1` and `d`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |
| `sizeLB_implies_depthLB` | `FormulaSizeLB fam ⇒ DepthLB fam`. | [Lean](../lean/Idea15.lean) | [Rocq](../rocq/Idea15.v) |

`FormulaSizeLB` and `DepthLB` are `def ... : Prop` in Lean and
`Definition ... : Prop` in Rocq. They are never assumed. No theorem in
either file proves or refutes P = NP.

## 4. Complete argument

**Upper bound on size from depth.** By induction:

* A variable has `size + 1 = 2 = 2^1`.
* For `neg g`, `size + 1 = size g + 2 ≤ 2^(depth g + 1) + 1 ≤ 2^(depth g + 2)`.
* For a binary gate with `m = max(depth g, depth h)`,
  `size + 1 = (size g + 1) + (size h + 1) ≤ 2^(depth g+1) + 2^(depth h+1) ≤ 2 · 2^(m+1) = 2^(m+2)`.

The leaf bound is the same computation without the `+1`. Both are tight by
`bal_size`. Since every internal node increases depth by at most one along
some path, `depth < size`, which is tight by `chain_size` and `chain_depth`
(`size = 2·depth + 1` for the binary chain; a chain of negations gives
`size = depth + 1`).

So for every formula,
`log₂(size + 1) − 1 ≤ depth ≤ size − 1`, and both ends are reached.

**Same function, different depth.** Using
`andRange a (m + n) = andRange a m ∧ andRange (a + m) n`, the left and right
subtrees of `bal (d+1) i` cover the ranges starting at `2i·2^d` and
`(2i+1)·2^d = 2i·2^d + 2^d`. Together these form the range starting at
`i·2^(d+1)` of length `2^(d+1)`. Hence `bal d 0` computes the AND of
`x₀,…,x_{2^d−1}`, as does `chain (2^d − 1)` (`eval_chain`). Both have
`2^(d+1) − 1` nodes, but depths `d` and `2^d − 1`. Equal size does not
determine depth, and a function is not "inherently sequential" just because
one formula for it is deep.

**From size lower bounds to depth lower bounds.** If `2^(c(log₂ n + 1)) ≤ size f`
and `size f + 1 ≤ 2^(depth f + 1)`, then `c(log₂ n + 1) < depth f + 1`, so
`c(log₂ n + 1) ≤ depth f`. The converse (small size ⇒ small depth) is
Spira's balancing theorem, which is not formalized here. With it the two
obligations are equivalent up to constants. Also, a circuit (DAG) of depth
`d` (fan-in 2) unfolds into a formula of depth `d`, hence of size
`< 2^(d+1)`, so depth lower bounds for circuits and for formulas coincide
(circuits are not formalized here; this remark is informal).

**Why this is insufficient alone.** Polynomial-size formulas correspond to
non-uniform NC¹ (depth `O(log n)`, fan-in 2). A superlogarithmic depth
lower bound for an explicit NP family shows NP ⊄ NC¹. P ≠ NP would need a
lower bound against *all* polynomial-time algorithms, not only against
logarithmic-depth ones. The known implications go: NP ⊄ P/poly ⇒ P ≠ NP,
and NP ⊄ P/poly ⇒ NP ⊄ NC¹ (since NC¹ ⊆ P/poly). No implication between
NP ⊄ NC¹ and P ≠ NP is known in either direction. Even this weaker target
is far beyond current techniques.

## 5. Known results and literature

* P. M. Spira, "On time-hardware complexity tradeoffs for Boolean
  functions", Proc. 4th Hawaii International Symposium on System Sciences,
  1971. Every formula of size `s` is equivalent to one of depth
  `O(log s)`.
* R. P. Brent, "The parallel evaluation of general arithmetic expressions",
  JACM 21(2), 1974. The analogous balancing for arithmetic expressions.
* V. M. Khrapchenko, "A method of determining lower bounds for the
  complexity of Π-schemes", Mat. Zametki 10(1), 1971. Parity of `n`
  variables needs de Morgan formulas of size `Ω(n²)`.
* J. Håstad, "The shrinkage exponent of de Morgan formulas is 2", SIAM J.
  Comput. 27(1), 1998. An explicit function (Andreev's) needs de Morgan
  formulas of size `n^(3−o(1))`. By `leaves_le_pow_depth` this gives only
  depth `(3 − o(1)) log₂ n`, still logarithmic.
* M. Karchmer and A. Wigderson, "Monotone circuits for connectivity require
  super-logarithmic depth", SIAM J. Discrete Math. 3(2), 1990. Formula
  depth equals the communication complexity of the associated
  Karchmer–Wigderson game. Monotone st-connectivity needs monotone depth
  `Ω(log² n)`.
* M. Karchmer, R. Raz and A. Wigderson, "Super-logarithmic depth lower
  bounds via the direct sum in communication complexity", Computational
  Complexity 5(3/4), 1995. Their (KRW) conjecture on composition would
  imply P ⊄ NC¹. It is open.
* R. Raz and P. McKenzie, "Separation of the monotone NC hierarchy",
  Combinatorica 19(3), 1999. Monotone depth hierarchy results. As with
  [Idea 10](Idea10.md), these do not transfer to general circuits.

## 6. How far the idea can be pushed toward P vs NP

* **Proved (general):** the tight inequalities
  `log₂(size+1) − 1 ≤ depth ≤ size − 1` and `leaves ≤ 2^depth` for all
  formulas; tight families; same-function/same-size/different-depth
  examples for all `d`; size lower bounds imply depth lower bounds.
* **Refuted (general):** "a deep formula for `g` shows that `g` needs depth"
  and "equal size implies equal depth" (`same_function_different_depth`).
* **Exact remaining obligation:** `DepthLB fam` (equivalently, via Spira,
  `FormulaSizeLB fam`; only the direction `FormulaSizeLB ⇒ DepthLB` is
  formalized) for an explicit family `fam` in NP. This is open. The
  best known explicit bound is about `3 log₂ n`. Even if proved, the result
  would be NP ⊄ NC¹, not P ≠ NP. P ≠ NP by circuit methods needs lower
  bounds against polynomial-size circuits of unbounded depth
  (`NP ⊄ P/poly`), a stronger statement than a formula lower bound.
* **Barrier:** natural-proofs arguments (Razborov–Rudich; see
  [Idea 10](Idea10.md)) apply to formula lower bounds as well, under
  standard cryptographic assumptions.

## 7. Failure modes this idea catches

* **Assumed lower bound** (family 1 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): exhibiting one
  deep formula (or one sequential algorithm) for a problem and claiming
  that every formula is deep (`same_function_different_depth`).
* **Structure theorem from one algorithm class** (family 20): lower bounds
  against shallow circuits or formulas are not lower bounds against all
  polynomial-time algorithms.
* **Nonstandard definitions** (family 11): mixing up size, depth and number
  of leaves. The dossier fixes all three and proves how they relate.
* **Encoding size** (family 17): unfolding a circuit into a formula can
  blow up size exponentially in depth (`size_le_pow_depth` is tight).
* **Barriers** (family 14): formula lower bound arguments that are
  "natural" face the Razborov–Rudich barrier.

Audit rule: a depth or size claim must say whether it is about formulas or
circuits, give the measure precisely, and quantify over *all* formulas
computing the function.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea15.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea15.v
```

Both commands print nothing on success. Remove the generated
`Idea15.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
