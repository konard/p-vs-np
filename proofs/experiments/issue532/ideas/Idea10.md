# Idea 10 — Restricted (monotone) circuit lower bounds and transfer to general circuits

**Verdict:** Refuted in full strength (published theorem) + formal core — superpolynomial and even exponential lower bounds for *monotone* circuits are known (Razborov 1985; Alon–Boppana 1987), but they do not transfer to general circuits: Tardos (1988) gives a monotone function computable in polynomial time whose monotone circuit complexity is exponential, so a monotone lower bound for an NP function cannot by itself give P ≠ NP. The formal core proves, for all formulas and all `n`, that monotone formulas compute exactly the monotone functions (`monotone_eval`, `monotone_complete`), that NOT and parity have no monotone formulas of any size, and that a general superpolynomial lower bound is *equivalent* to a monotone lower bound for the double-rail partial function (`general_iff_double_rail`), not to a monotone lower bound for `f` itself. The remaining obligation `GeneralSuperpolyLowerBound` is open; as formalized it is a *formula* lower bound (which for an NP family would separate NP from non-uniform NC¹), and only its circuit analogue, which is not formalized, would give P ≠ NP.

## 1. The idea at full strength

Issue #532, Part II, Phase 1 asks for models such as "Boolean circuits (size
+ depth)", and Phase 2 lists "Known lower bounds for restricted circuits"
next to the barriers. The idea at full strength, aimed at **P ≠ NP**:

1. Choose a restricted model where lower bounds are provable. Monotone
   circuits (AND/OR only) are the most successful example: superpolynomial
   lower bounds are known for CLIQUE, an NP-complete monotone function.
2. Prove a superpolynomial lower bound for an NP function in that model.
3. Transfer the bound to general circuits (AND/OR/NOT) by removing or
   simulating the negations, so that NP ⊄ P/poly and therefore P ≠ NP.

Step 3 is the whole question. This dossier proves exactly how much of the
transfer holds and names the missing statement.

## 2. Precise mathematical formulation

**Formulas.** `Circ ::= var i | lit b | conj a b | disj a b | neg a`,
evaluated on assignments `x : ℕ → Bool`. `size` counts nodes. A formula is
*monotone* when `notFree c = true` (it has no `neg`). The formal files use
formulas (fan-out one). For circuits (DAGs) the same constructions can be
applied gate by gate (the double-rail translation then at most doubles the
size); this circuit version is an informal remark and is not formalized.

**Order.** `leB a b = ¬a ∨ b` is the order `false ≤ true`; `LeAssign x y`
is the pointwise order; `MonotoneFn f` means `x ≤ y → f x ≤ f y`.

**Parity.** `parity n x = x₀ ⊕ … ⊕ x_{n−1}`.

**Double rail.** `dual x` is the assignment on `2n` variables with
`dual x (2i) = xᵢ` and `dual x (2i+1) = ¬xᵢ`. `doubleRail c` pushes
negations to the inputs (De Morgan) and returns a pair of monotone formulas
for `c` and `¬c` over the double-rail variables. `undual` substitutes
`xᵢ`, `¬xᵢ` back.

**Lower-bound statements** for a family `f n : (ℕ → Bool) → Bool`:

* `GeneralSuperpolyLowerBound f`: for all `c, d` there is `n` such that
  every formula `C` with `size C ≤ c·n^d + c` differs from `f n` somewhere.
* `MonotoneSuperpolyLowerBound f`: the same, but only for monotone `C`.
* `DoubleRailLowerBound f`: the same for monotone `C` that only need to be
  correct on the consistent inputs `dual x`.

**Claim to be refuted.** "`MonotoneSuperpolyLowerBound f` for an NP family
`f` implies `GeneralSuperpolyLowerBound f`." The published refutations cited
below are for the circuit analogues of these definitions (monotone versus
general circuit size); the formal files do not prove this refutation.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `leB_and` | AND is monotone in both arguments. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `leB_or` | OR is monotone in both arguments. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `monotone_eval` | Every NOT-free formula is monotone: `x ≤ y → eval c x ≤ eval c y`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `notFree_computes_monotone` | `eval c` is a monotone function for NOT-free `c`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `neg_not_monotone` | `x ↦ ¬x₀` is not monotone. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `no_monotone_formula_for_not` | No monotone formula, of any size, computes `¬x₀`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `parity_first` | For `n ≥ 1`, parity of the assignment `[i = 0]` is `true`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `parity_two` | For `n ≥ 2`, parity of the assignment `[i < 2]` is `false`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `parity_not_monotone` | For every `n ≥ 2`, parity of `n` variables is not monotone. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `no_monotone_formula_for_parity` | For every `n ≥ 2`, no monotone formula computes parity of `n` variables. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `parityCirc_correct` | For every `n`, the general formula `parityCirc n` computes parity. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `build_notFree` | The Shannon formula `build n f` is monotone. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `upd_le` | Updating one coordinate preserves the pointwise order. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `monotone_complete` | Every monotone `f` depending on the first `n` variables is computed by the monotone formula `build n f`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `dual_even` | `dual x (2i) = xᵢ`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `dual_odd` | `dual x (2i+1) = ¬xᵢ`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `doubleRail_correct` | For every formula `c`, both rails are monotone, have size `≤ size c`, and compute `c` and `¬c` on every `dual x`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `undual_correct` | For every formula `c`, `undual c` has size `≤ 2·size c` and `eval (undual c) x = eval c (dual x)`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `GeneralSuperpolyLowerBound` | Definition of the open obligation (a `Prop`, never assumed). | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `MonotoneSuperpolyLowerBound` | Definition: superpolynomial lower bound against monotone formulas. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `DoubleRailLowerBound` | Definition: monotone lower bound for the double-rail partial function. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `general_lb_implies_monotone_lb` | A general lower bound implies the monotone one (the easy direction). | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |
| `general_iff_double_rail` | For every family `f`: `GeneralSuperpolyLowerBound f ↔ DoubleRailLowerBound f`. | [Lean](../lean/Idea10.lean) | [Rocq](../rocq/Idea10.v) |

No theorem in either file proves or refutes P = NP, and no circuit lower
bound for an explicit NP function is claimed.

## 4. Complete argument

**Monotonicity (`monotone_eval`).** Induction on the formula. Variables are
monotone by hypothesis, literals are constant, and `leB_and`/`leB_or` show
that AND and OR preserve the order. The `neg` case cannot occur because the
formula is NOT-free.

**What monotone formulas cannot do.** If a monotone formula computed `¬x₀`,
then `¬x₀` would be monotone; but the all-false assignment is below the
all-true one while `¬x₀` goes from `true` to `false` (`neg_not_monotone`).
For parity with `n ≥ 2`, compare `[i = 0]` (parity `1`) with `[i < 2]`
(parity `0`): the first is pointwise below the second (`parity_first`,
`parity_two`, `parity_not_monotone`). These are *expressibility* failures,
valid for formulas of every size, and general formulas compute both
functions (`parityCirc_correct`; this recursive formula duplicates
subformulas and is not size-optimal, but parity has general circuits of
linear size, built from `n − 1` constant-size XOR gadgets).

**What monotone formulas can do (`monotone_complete`).** For monotone `f`
depending on the first `n + 1` variables, the Shannon expansion
`f = (xₙ ∧ f[xₙ:=1]) ∨ f[xₙ:=0]` is valid: if `xₙ = 0` the first disjunct is
false and the second equals `f x`; if `xₙ = 1` the first disjunct equals
`f x` and the second is `≤ f x` by monotonicity. Both restrictions are
monotone and depend on `n` variables, so induction applies. Hence the
monotone model computes every monotone function; the only question is size.
This is why monotone lower bounds are *size* lower bounds and can be
compared with general size.

**Negations to the leaves (`doubleRail_correct`).** Define the pair
`(p c, q c)` by `p (var i) = var 2i`, `q (var i) = var (2i+1)`,
`p (conj a b) = conj (p a) (p b)`, `q (conj a b) = disj (q a) (q b)`,
dually for `disj`, `p (lit b) = lit b`, `q (lit b) = lit ¬b`, and
`(p (neg a), q (neg a)) = (q a, p a)`. By induction, both are NOT-free,
each has at most `size c` nodes (the `neg` node is dropped), and on
`dual x` they compute `c x` and `¬c x` (De Morgan in each case).

**Back to general formulas (`undual_correct`).** Replacing `var 2i` by
`var i` and `var (2i+1)` by `neg (var i)` at most doubles the size and
satisfies `eval (undual c) x = eval c (dual x)`.

**Exact reformulation (`general_iff_double_rail`).**
(⇒) Given `c, d`, apply the general bound with constant `2c`: any monotone
`C` of size `≤ c·n^d + c` correct on all `dual x` would give `undual C` of
size `≤ 2c·n^d + 2c` correct on all `x`, contradicting the bound.
(⇐) Given a general `C` of size `≤ c·n^d + c`, the first rail of
`doubleRail C` is monotone, not larger, and agrees with `C` on every
`dual x`; the double-rail lower bound gives an `x` where it, hence `C`,
is wrong. The constants are uniform, so polynomial bounds match exactly.

**Why the transfer from `f` itself fails.** `DoubleRailLowerBound f` asks
for a lower bound on monotone formulas that are only required to be
correct on the *consistent* inputs `dual x`, and they may use the negated
literals as free inputs. A monotone lower bound for `f` constrains monotone
formulas that must be correct on *every* input and see only positive
literals. For monotone `f` the latter class is contained in the former (a
monotone formula for `f`, renamed `i ↦ 2i`, is correct on all `dual x`), so
`DoubleRailLowerBound f` implies the monotone bound for `f`; the converse
is exactly what fails in general. Tardos (1988) exhibits a monotone
function in P (so its double-rail *circuit* complexity is polynomial, by the
circuit analogue of `doubleRail_correct`, which is not formalized) whose
monotone circuit complexity is exponential;
Razborov's perfect-matching bound (1985) already gives a superpolynomial
gap for a function in P. So "monotone lower bound ⇒ general lower bound" is
false as a general principle; any successful transfer must use a property
of the specific function that these counterexamples lack.

## 5. Known results and literature

* A. A. Razborov, "Lower bounds on the monotone complexity of some Boolean
  functions", Doklady Akademii Nauk SSSR 281(4), 1985 (English: Soviet
  Math. Doklady 31, 1985). Superpolynomial monotone lower bound for CLIQUE.
* A. A. Razborov, "Lower bounds on monotone complexity of the logical
  permanent", Matematicheskie Zametki 37(6), 1985 (English: Mathematical
  Notes 37, 1985). Superpolynomial monotone lower bound for bipartite
  perfect matching, a problem in P: the first superpolynomial monotone
  versus general gap.
* N. Alon and R. B. Boppana, "The monotone circuit complexity of Boolean
  functions", Combinatorica 7(1), 1987. Exponential monotone lower bounds
  for CLIQUE.
* É. Tardos, "The gap between monotone and non-monotone circuit complexity
  is exponential", Combinatorica 8(1), 1988. A monotone function computable
  in polynomial time with exponential monotone circuit complexity.
* A. A. Razborov, "On the method of approximations", STOC 1989. Limits of
  the approximation method (the technique behind the monotone bounds) for
  general circuits.
* M. Karchmer and A. Wigderson, "Monotone circuits for connectivity require
  super-logarithmic depth", SIAM J. Discrete Math. 3(2), 1990; R. Raz and
  A. Wigderson, "Monotone circuits for matching require linear depth",
  JACM 39(3), 1992. Monotone *depth* lower bounds, again with no transfer
  to general depth.
* A. A. Razborov and S. Rudich, "Natural proofs", JCSS 55(1), 1997. Under
  standard cryptographic assumptions, "natural" proof strategies cannot
  prove superpolynomial general circuit lower bounds.
* M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, "A better-than-3n
  lower bound for the circuit complexity of an explicit function", FOCS
  2016: `(3 + 1/86)n − o(n)`. J. Li and T. Yang, STOC 2022: `3.1n − o(n)`.
  These are the best known general lower bounds for explicit functions,
  and they are only linear.
* A. A. Markov (1958) showed that `⌈log₂(n+1)⌉` negations suffice for any
  function of `n` variables, so "few negations" does not restrict the
  function class either.

## 6. How far the idea can be pushed toward P vs NP

* **Proved:** the monotone model is complete for monotone functions and
  exactly as strong as the general model *on the double-rail partial
  function* (for formulas). Consequently, the missing statement is a
  general lower bound for an NP family `f`; in the formal (formula) setting
  this is `GeneralSuperpolyLowerBound f`, and
  `general_iff_double_rail` restates it without negations, as a monotone
  bound for a partial function.
* **Refuted (published):** that a monotone circuit lower bound for `f`
  implies a general circuit lower bound (Tardos 1988; also Razborov's
  matching bound). Not formalized.
* **Open:** `GeneralSuperpolyLowerBound f` for an NP family `f`. For
  circuits (rather than formulas) this would give NP ⊄ P/poly and hence
  P ≠ NP; the formula version formalized here would only give that NP
  has no polynomial-size formulas, which is not known to imply P ≠ NP.
  The known general circuit bounds for explicit functions are linear (§5).
* **Barrier:** Razborov–Rudich (1997) natural proofs apply to general
  circuit lower bound strategies, and Razborov (1989) showed that the
  method of approximations behind the monotone bounds has strong limits for
  general circuits. A route through the double-rail
  reformulation must exploit that correctness is only required on
  consistent inputs; the approximation method does not use this.

Precise obligation for a follow-up: prove `GeneralSuperpolyLowerBound f`
(or `DoubleRailLowerBound f`, which is equivalent) for a family `f` in NP,
in its circuit form if the goal is P ≠ NP, and explain which of the barriers
the argument avoids.

## 7. Failure modes this idea catches

* **Restricted-model lower bound presented as general** (family 20 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md), structure
  theorem from one algorithm class): a lower bound against monotone
  formulas says nothing about formulas with NOT; `no_monotone_formula_for_parity`
  is an unconditional "lower bound" for a function with linear-size general
  circuits.
* **Solving a different problem** (family 5): the monotone complexity of
  `f` is a different quantity from the monotone complexity of the
  double-rail partial function; `general_iff_double_rail` shows which one
  matters.
* **Assumed lower bound** (family 1): an attempt that "transfers" a monotone
  bound usually assumes that negations can be removed cheaply; they can
  (`doubleRail_correct`), but only at the price of changing the function.
* **Barriers** (family 14): any argument that reaches
  `GeneralSuperpolyLowerBound` must say how it avoids natural proofs.
* **Uniform vs non-uniform** (family 16): circuit lower bounds are
  non-uniform; P ≠ NP follows from a superpolynomial circuit lower bound for
  an NP family, but the converse is not known.

Audit rule: any attempt that uses a restricted-model lower bound must state
the transfer theorem it relies on and check it against
`general_iff_double_rail` and Tardos' counterexample.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea10.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea10.v
```

Both commands print nothing on success. Remove the generated
`Idea10.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
