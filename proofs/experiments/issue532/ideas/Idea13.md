# Idea 13 — Approximation to exactness

**Verdict:** Developed to an open obligation (conditional theorem proved). For integer-valued objectives, an approximation becomes exact only once its error drops below one unit: a `(1 + 1/q)`-approximation is exact whenever `OPT < q` (`approx_exact_nat`, `approx_exact_max`). The bound is sharp (`threshold_sharp`), and any constant ratio such as 2 leaves room for non-optimal answers (`ratio_two_not_exact`). A fully polynomial approximation scheme is therefore exact in polynomial time whenever the optimum is polynomially bounded (`fptas_poly_bounded_exact`), and a good enough ratio decides gap problems (`polyApprox_decides_gap`). The open obligation is `PolyApprox opt num den`, stated over the shared machine model: a `Complexity.Machine` computes (`Computes`, time = step count of `Run`) a word whose value `wordValue` approximates `opt` within ratio `num/den`. Beyond a published NP-hardness threshold it would imply P = NP by the cited PCP gap reductions (not formalized), and this dossier does not discharge it. `PolyApprox` is not vacuous: for every ratio, some problem has no polynomial-time machine approximation (`not_forall_polyApprox`). Caveat: the step from the gap decider of `polyApprox_decides_gap` to `InP SAT` goes through PCP gap reductions that are cited, not mechanised.

## 1. The idea at full strength

Attempts in this family argue:

1. An NP-hard optimisation problem (vertex cover, TSP, MAX-SAT, knapsack)
   has a polynomial-time approximation algorithm with ratio `c`.
2. Since `c` can be made close to 1, or the heuristic "always finds the
   optimum on tests", the algorithm is in fact exact.
3. Exact optimisation of an NP-hard problem in polynomial time gives P = NP.

At full strength the idea is correct in one precise situation: if the
objective is an integer and the relative error times `OPT` is below 1, the
approximate value equals the optimum. The question is when this situation
can be reached in polynomial time.

## 2. Precise mathematical formulation

Instances have type `α`, with size `sz : α → ℕ` and integer optimum
`opt : α → ℕ`. Ratios are written multiplicatively so that everything stays
in `ℕ`.

* **Minimisation, ratio `1 + 1/q`:** `OPT ≤ A` and `A · q ≤ OPT · (q + 1)`.
* **Maximisation, ratio `q/(q+1)`:** `A ≤ OPT` and `OPT · q ≤ A · (q + 1)`.
* **Ratio `num/den` (minimisation):** `OPT ≤ A` and `A · den ≤ OPT · num`.
* **Approximation scheme:** `S : ℕ → α → ℕ`, where `S q` has ratio
  `1 + 1/q`, with running time `T q x`. It is *fully polynomial* (an
  FPTAS) if `T q x ≤ c · (sz x + q + 1)^d`.
* **Gap promise problem:** each instance satisfies `opt x ≤ a` or
  `a · num < opt x · den`; the task is to decide which.
* **Machine model.** Words, machines, `Run`, `Polynomial` come from
  `proofs/complexity/lean/Complexity.lean`, and `Computes m f p` (machine `m`
  outputs `f x` within `p.eval |x|` steps of its `Run`) from
  `proofs/experiments/issue532/lean/Machines.lean`. Instances are words, and
  a machine's output word `y` is read as the number `wordValue y` (binary,
  least significant bit first).
* **Open obligation:**

```lean
def PolyApprox (opt : Word → Nat) (num den : Nat) : Prop :=
  ∃ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p ∧
    ∀ x, opt x ≤ wordValue (f x) ∧ wordValue (f x) * den ≤ opt x * num
```

  The time is the step count of the machine's run, so `PolyApprox` cannot be
  satisfied by declaring a running time.
* **Non-vacuity helpers:** `optOf L num x` is `1` on members of `L` and
  `num + 1` on non-members; `thresholdLanguage num m` is the language read off
  the output of `m` by the test `wordValue ≤ num`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `approx_exact_nat` | `OPT ≤ A`, `A·q ≤ OPT·(q+1)`, `OPT < q` ⇒ `A = OPT` (minimisation). | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `approx_exact_max` | `A ≤ OPT`, `OPT·q ≤ A·(q+1)`, `OPT ≤ q` ⇒ `A = OPT` (maximisation). | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `threshold_sharp` | For every `q`, with `OPT = q` the value `q + 1` is `(1+1/q)`-approximate and not optimal. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `ratio_two_not_exact` | For every `OPT ≥ 1` there is a 2-approximate value different from `OPT`. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `scheme_exact_below_bound` | A scheme run with `q = B x > opt x` returns `opt x`. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `fptas_poly_bounded_exact` | FPTAS + `B x ≤ e(sz x+1)^k` ⇒ exact in time `≤ c(e+1)^d (sz x+1)^((k+1)d)`. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `approx_decides_gap` | A ratio-`num/den` algorithm decides every gap promise problem with gap above `num/den`. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `polyApprox_decides_gap` | `PolyApprox opt num den` ⇒ a machine `m` with `Computes m f p` whose output answers every gap promise problem with gap above `num/den` by the test `wordValue (f x) · den ≤ a · num`. | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |
| `not_forall_polyApprox` | Non-vacuity: for `den ≥ 1`, `PolyApprox opt num den` fails for some `opt` (diagonalisation against `thresholdLanguage`). | [Lean](../lean/Idea13.lean) | [Rocq](../rocq/Idea13.v) |

`PolyApprox` is a `def ... : Prop` over the shared machine model. It is never
assumed as an axiom. No theorem in either file proves or refutes P = NP. The
arithmetic rows are in both files under the same names. The machine-model
statements (`wordValue`, `PolyApprox`, `polyApprox_decides_gap`, `optOf`,
`thresholdLanguage`, `not_forall_polyApprox`) are Lean-only for now. The
intended Rocq names are the same; `Idea13.v` still has the earlier
abstract-cost `PolyApprox`.

## 4. Complete argument

**Exactness below one unit (`approx_exact_nat`).** Suppose `OPT ≤ A`,
`A q ≤ OPT (q + 1)` and `OPT < q`. If `A ≥ OPT + 1`, then
`(OPT + 1) q ≤ A q ≤ OPT q + OPT`, so `q ≤ OPT`, contradicting `OPT < q`.
Hence `A = OPT`. In words, the additive error `A − OPT ≤ OPT/q` is an
integer strictly below 1.

**Maximisation (`approx_exact_max`).** If `A ≤ OPT − 1`, then
`OPT q ≤ A (q + 1) ≤ (OPT − 1)(q + 1) = OPT q + OPT − q − 1`, so
`OPT ≥ q + 1`, contradicting `OPT ≤ q`.

**Sharpness.** With `OPT = q` and `A = q + 1`:
`A q = (q + 1) q = OPT (q + 1)`, so the ratio condition holds with
equality, yet `A ≠ OPT` (`threshold_sharp`). For ratio 2, `A = 2·OPT` is
admissible and differs from `OPT` whenever `OPT ≥ 1`
(`ratio_two_not_exact`). So no constant ratio `c > 1` implies exactness on
instances with large optimum. "The ratio is close to 1" gives no guarantee
of exactness unless it is tied to the size of `OPT`.

**Approximation schemes (`scheme_exact_below_bound`,
`fptas_poly_bounded_exact`).** Given a bound `B x > opt x`, run the scheme
with `q = B x`; the first lemma gives exactness. If the scheme is fully
polynomial, `T (B x) x ≤ c (sz x + B x + 1)^d`. If `B x ≤ e (sz x + 1)^k`,
then using `(sz x + 1) ≤ (sz x + 1)^(k+1)` and
`(sz x + 1)^k ≤ (sz x + 1)^(k+1)`,
`sz x + B x + 1 ≤ (e + 1)(sz x + 1)^(k+1)`, and raising to the `d`-th power
gives the stated bound. This is the Garey–Johnson argument: a strongly
NP-hard problem (NP-hard even when numbers are polynomially bounded, so that
`OPT` is polynomially bounded) has no FPTAS unless P = NP. For weakly
NP-hard problems such as knapsack, `OPT` can be exponential in the input
length. The same construction then only gives a pseudo-polynomial algorithm,
which is why the knapsack FPTAS does not prove P = NP.

**Gap problems (`approx_decides_gap`).** Suppose each instance satisfies
`opt x ≤ a` or `a·num < opt x·den`, and `opt ≤ A ≤ opt·num/den`. If
`opt x ≤ a`, then `A x·den ≤ opt x·num ≤ a·num`. Otherwise
`A x·den ≥ opt x·den > a·num`. So the test `A x·den ≤ a·num` decides the
promise problem. `polyApprox_decides_gap` lifts this to machines: the
machine of `PolyApprox` computes `f` within its polynomial, and the single
comparison on `wordValue (f x)` answers the promise problem. The
PCP theorem and its refinements produce polynomial reductions from SAT to
exactly such gap problems. A polynomial-time approximation with a ratio
better than the gap would therefore decide SAT, which is the sense in which
inapproximability results are conditional on P ≠ NP. The dossier formalizes
the minimisation direction; the maximisation direction (used for MAX-3SAT)
is symmetric and is not formalized here.

**Non-vacuity (`not_forall_polyApprox`).** Suppose every `opt` had a
ratio-`num/den` machine approximation with `den ≥ 1`. Take a language `L`
that differs from `thresholdLanguage num m` for every machine `m`; it exists
by diagonalisation, since machines have an injective encoding into words. For
`optOf L num`, the approximation `A` satisfies `A ≤ num` on members
(`A · den ≤ num` and `A ≤ A · den`) and `A ≥ num + 1` on non-members. So
`L` is `thresholdLanguage num m` for the approximating machine `m` (the
computed function is unique, `computes_unique`), a contradiction.

## 5. Known results and literature

* M. R. Garey and D. S. Johnson, "'Strong' NP-completeness results:
  motivation, examples, and implications", JACM 25(3), 1978. A strongly
  NP-hard problem with polynomially bounded integer objective has no FPTAS
  unless P = NP. This is the argument behind `fptas_poly_bounded_exact`.
* O. H. Ibarra and C. E. Kim, "Fast approximation algorithms for the
  knapsack and sum of subset problems", JACM 22(4), 1975. An FPTAS for
  knapsack, a weakly NP-hard problem. So an FPTAS alone does not yield a
  polynomial-time exact algorithm unless P = NP.
* S. Arora and S. Safra, "Probabilistic checking of proofs: a new
  characterization of NP", JACM 45(1), 1998; S. Arora, C. Lund, R. Motwani,
  M. Sudan and M. Szegedy, "Proof verification and the hardness of
  approximation problems", JACM 45(3), 1998. The PCP theorem: MAX-3SAT has
  no PTAS unless P = NP.
* J. Håstad, "Some optimal inapproximability results", JACM 48(4), 2001.
  For every `ε > 0`, approximating MAX-E3SAT within `7/8 + ε` is NP-hard,
  while a uniformly random assignment already achieves `7/8` in expectation.
* I. Dinur and S. Safra, "On the hardness of approximating minimum vertex
  cover", Annals of Mathematics 162(1), 2005. Vertex cover within a factor
  of about 1.36 is NP-hard.
* I. Dinur, "The PCP theorem by gap amplification", JACM 54(3), 2007. A
  combinatorial proof of the PCP theorem.

## 6. How far the idea can be pushed toward P vs NP

* **Proved (general):** exactness from approximation below one integer unit;
  sharpness of that bound; the polynomial-time exact algorithm from an FPTAS
  on polynomially bounded objectives; gap decision from approximation.
* **Refuted (general):** "a constant-ratio (or near-1 ratio) approximation is
  exact". The countermodels hold for every optimum value.
* **Exact remaining obligation:** a proof of P = NP along this route requires
  `PolyApprox opt num den` (over the shared machine model, time = `Run` step
  count) for some NP-hard problem `opt` and a ratio `num/den` strictly
  better than a published NP-hardness threshold (for example, below
  Dinur–Safra's constant for vertex cover). By `polyApprox_decides_gap` it
  gives a polynomial-time machine answering the corresponding gap problem.
  Together with the published gap reduction from SAT (cited, not
  mechanised), it would give a polynomial decider for SAT. Alternatively: an
  FPTAS for a strongly NP-hard problem. Nothing proved here brings either
  statement closer: by the cited results each would imply P = NP.
  `not_forall_polyApprox` shows that `PolyApprox` is a genuine restriction on
  `opt`, not a consequence of the definitions.
* **Caveats.** The last step, from a gap decider to `InP SAT`, uses the PCP
  gap reductions, which are cited and not mechanised, so no conditional
  theorem to `InP SAT` is stated here. The FPTAS results
  (`fptas_poly_bounded_exact`) are arithmetic about a given time bound `T`;
  they are not tied to a machine. The machine-model part is Lean-only so far.
* **For P ≠ NP** the route gives nothing directly. Inapproximability
  theorems are themselves conditional on P ≠ NP.

## 7. Failure modes this idea catches

* **Easier/different problem** (family 5 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): solving the
  approximate version and claiming the exact one (`ratio_two_not_exact`,
  `threshold_sharp`).
* **Heuristics/probability** (family 8): "the approximation was optimal on
  all tests". The countermodels show that a ratio guarantee does not bound
  the number of non-optimal instances.
* **Encoding size** (family 17): an FPTAS whose `q` must be of order `OPT`
  runs in time polynomial in `OPT`, i.e. pseudo-polynomial. This is
  polynomial only when `OPT` is polynomially bounded in the bit length
  (`fptas_poly_bounded_exact`).
* **LP/SDP relaxation** (family 3): relaxations give ratio guarantees, not
  exactness. See also [Idea 11](Idea11.md).
* **False statements** (family 18): claims of approximation ratios below
  Håstad's or Dinur–Safra's thresholds would, by those theorems, imply
  P = NP, and must be checked against them first.

Audit rule: any claim that approximation yields exactness must exhibit the
bound `OPT < q` (or the gap) and show that the resulting `q` is polynomial
in the bit length of the input.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea13.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea13.v
```

Both commands print nothing on success. Remove the generated
`Idea13.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
