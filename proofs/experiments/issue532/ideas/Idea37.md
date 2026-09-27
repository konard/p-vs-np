# Idea 37 — Parameterized structure

**Verdict:** Developed to an open obligation (conditional theorem proved)

A fixed-parameter tractable (FPT) algorithm runs in time `f(k) · n^c` for a
structural parameter `k`. The files prove that such a bound is polynomial
whenever `f(k)` is polynomially bounded in `n`, in particular when `2^k ≤ n`.
When the parameter is as large as the input, the same bound `2^n · n^c` exceeds
every polynomial. The route to P = NP is therefore reduced to one precise open
obligation: an FPT algorithm for an NP-complete problem whose parameter is
logarithmic on **all** instances.

## 1. The idea at full strength

Many NP-complete problems are easy when a structural parameter is small. Vertex
cover of size `k` can be decided in time about `2^k · n`, and SAT on formulas
of treewidth `k` in time about `2^k · poly(n)`. The idea at full strength:

1. Find a parameter `k(I)` of instances of an NP-complete problem.
2. Give an FPT algorithm with running time `f(k) · |I|^c`.
3. Show that `f(k(I))` is polynomial in `|I|` on **every** instance.

Steps 1–3 would give a polynomial-time algorithm for an NP-complete problem, and
so P = NP. This is the "structure" direction of issue #532, Part I, item 2:
exploit hidden structure of instances rather than worst-case search.

## 2. Precise mathematical formulation

- `FPTBound time size param f c := ∀ I, time I ≤ f (param I) · (size I)^c`.
- `LogBoundedParam size param b := ∀ I, 2^(param I) ≤ (size I)^b`, which says
  the parameter is at most `b · log₂(size)`.
- `LogParamFPTObligation Correct time size` says there is an algorithm `A` with
  `Correct A`, an FPT bound with `f k = 2^k`, and a parameter that is
  logarithmically bounded on every instance.
- Polynomials are in the repository's form `c · (n+1)^d` (see
  `Polynomial.eval` in `proofs/complexity`).

The abstract predicates `Correct` and `time` stand for "decides the
NP-complete language" and "step count of the machine". The theorems hold for
every instantiation.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | a monotone cost is bounded when the parameter is bounded | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_param_bound_poly` | `f k ≤ n^a` implies `f k · n^c ≤ n^(a+c)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_log_param_poly` | `2^k ≤ n` implies `2^k · n^c ≤ n^(c+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `linear_lt_exp` | `a · (q+1) < 2^q` for `q ≥ 2a+1` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `dyadic_bracket` | every `n ≥ 1` has `L` with `2^L ≤ n < 2^(L+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `exp_beats_poly` | `c · (n+1)^d < 2^n` for all `n ≥ 2^(2(c+d)+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `exists_threshold` | for all `c, d` there is `N` with `c · (n+1)^d < 2^n` for all `n ≥ N` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `poly_lt_two_pow` | for all `c, d` there is `n` with `c · (n+1)^d < 2^n` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_full_param_not_poly` | for all `a, d, c` there is `n` with `a · (n+1)^d < 2^n · n^c` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_log_param_polytime` | an FPT bound `2^k · n^c` with `2^k ≤ n^b` gives `time ≤ n^(b+c)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `obligation_gives_poly_time` | `LogParamFPTObligation` yields a correct algorithm with a polynomial bound | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |

The definitions `FPTBound`, `LogBoundedParam` and `LogParamFPTObligation` are
present in both files. All proofs are constructive.

## 4. Complete argument

**(a) Small parameters.** If `f(k) ≤ n^a`, multiplying by `n^c` gives
`f(k) · n^c ≤ n^a · n^c = n^(a+c)` (`fpt_param_bound_poly`). For `f(k) = 2^k`
and `2^k ≤ n`, that is `k ≤ log₂ n`, the bound is `n^(c+1)`
(`fpt_log_param_poly`). More generally, `2^k ≤ n^b`, that is `k ≤ b log₂ n`,
gives `n^(b+c)`. Hence an algorithm with an FPT bound and a logarithmic
parameter on every instance runs in polynomial time (`fpt_log_param_polytime`,
`obligation_gives_poly_time`).

**(b) Large parameters.** First, linear against exponential:
`a (q+1) < 2^q` once `q ≥ 2a + 1`, by induction on `q`, where the base case
uses `a + 1 ≤ 2^a` (`linear_lt_exp`). For `n ≥ 2^(2(c+d)+1)`, pick the dyadic
bracket `2^L ≤ n < 2^(L+1)` (`dyadic_bracket`). Then `L ≥ 2(c+d)+1`, so
`c + d(L+1) < n`, and

    c · (n+1)^d ≤ c · 2^((L+1)d) < 2^c · 2^((L+1)d) = 2^(c + (L+1)d) ≤ 2^n

(`exp_beats_poly`). For every polynomial `a (n+1)^d` there is therefore an `n`
where `2^n · n^c ≥ 2^n > a (n+1)^d` (`fpt_full_param_not_poly`). An FPT
algorithm whose parameter can be as large as the input is not a polynomial
algorithm, whatever `c` is.

**(c) The gap between (a) and (b).** Either the parameter is logarithmic on
every instance, and then the problem is in P, or it is not, and then the FPT
bound gives nothing better than exponential time on the bad instances. For an
NP-complete problem the first alternative is exactly
`LogParamFPTObligation`, and it implies P = NP. There is no intermediate
conclusion. Restricting to instances with small parameter defines a
**different** problem, which is typically in P and not NP-complete unless
P = NP.

## 5. Known results and literature

- R. G. Downey and M. R. Fellows, "Fixed-parameter tractability and
  completeness I: basic results", *SIAM Journal on Computing* 24(4), 1995. This
  paper defines FPT and the W-hierarchy. Problems such as clique, parameterized
  by solution size, are W[1]-hard and believed not to be FPT. Not formalized.
- B. Courcelle, "The monadic second-order logic of graphs I", *Information and
  Computation* 85, 1990. MSO-definable graph properties are decidable in linear
  time on graphs of bounded treewidth, which covers SAT of bounded
  (primal) treewidth. Not formalized.
- R. Impagliazzo and R. Paturi, "On the complexity of k-SAT", *JCSS* 62(2),
  2001, formulates the Exponential Time Hypothesis (ETH). R. Impagliazzo,
  R. Paturi and F. Zane, "Which problems have strongly exponential
  complexity?", *JCSS* 63(4), 2001, proves the sparsification lemma. Under ETH,
  3-SAT has no `2^o(n)` algorithm in the number of variables `n`, so no
  parameter that is `o(n)` on all instances admits a `2^k · poly` algorithm.
  Not formalized.
- Vertex cover of size `k` is solvable in time `O(2^k · n)` by the bounded
  search tree (standard; see Downey–Fellows, *Parameterized Complexity*,
  Springer, 1999). By (a), it is in P on instances with `k ≤ log₂ n`. That
  restricted problem is in P and is not NP-complete unless P = NP. Not
  formalized.

## 6. How far the idea can be pushed toward P vs NP

**At full potential**, the idea proves `LogParamFPTObligation` for an
NP-complete problem. By `obligation_gives_poly_time`, this is a polynomial-time
algorithm for that problem, so the obligation is equivalent to P = NP (the
converse is trivial: with a polynomial algorithm take `param = 0`). The
formalization makes the needed hypothesis explicit and checks that nothing
weaker suffices from the FPT bound alone (`fpt_full_param_not_poly`).

**Why the obligation is hard.** Under ETH (Impagliazzo–Paturi–Zane), no
NP-complete problem admits a parameter with both properties, since that would
give a subexponential algorithm for 3-SAT. So the obligation is at least as
hard as refuting ETH. Parameters that are small on "typical" or "structured"
instances (treewidth, backdoor size) are not small on all instances. A padding
trick, which pads an instance with `k` variables to length `2^k`, makes any
parameter logarithmic but needs an exponential-size reduction. That is not a
polynomial reduction.

**What is gained.** A correct and fully general accounting of when
parameterized algorithms yield polynomial time. It is useful for auditing
claims of the form "SAT is FPT in parameter X, and X is small".

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 17 (encoding-size, bit-complexity, or parameter mistakes):** treating
  `2^k · n^c` as polynomial without proving `k = O(log n)` on every instance.
  `fpt_full_param_not_poly` shows that it is not polynomial when `k = n`.
- **Family 5 (solving an easier or special problem):** an algorithm for the
  small-parameter subclass solves a restricted problem, not the NP-complete one.
- **Family 2 (hiding exponential work):** the factor `f(k)` is the exponential
  work. It moves into the parameter, it does not disappear.
- **Family 20 (structure theorem from one class):** "all hard instances have
  small parameter" is a claim about all instances and must be proved.

Audit rule: for an FPT-based claim, write down `f`, the parameter, and a proof
that `f(param I) ≤ size(I)^b` for every instance `I`. Without the last item,
the claim is only a parameterized result.

## 8. Reproduction

From the repository root:

```bash
lake env lean proofs/experiments/issue532/lean/Idea37.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea37.v
rm -f proofs/experiments/issue532/rocq/Idea37.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea37.aux
```

Both commands print nothing on success.
