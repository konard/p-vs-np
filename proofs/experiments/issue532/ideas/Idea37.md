# Idea 37 — Parameterized structure

**Verdict:** Developed to an open obligation (conditional theorem proved)

A fixed-parameter tractable (FPT) algorithm runs in time `f(k) · n^c` for a
structural parameter `k`. The files prove that such a bound is polynomial
whenever `f(k)` is polynomially bounded in `n`, in particular when `2^k ≤ n`.
When the parameter is as large as the input, the same bound `2^n · n^c` exceeds
every polynomial at some (in fact all large) `n`, so it no longer certifies
polynomial time. The route to P = NP is therefore reduced to one precise open
obligation over the shared machine model, `LogParamFPTObligation`: a
`Complexity.Machine` decides `SAT` within `2^(param x) · (|x|+1)^c` `Run` steps
for a parameter with `2^(param x) ≤ (|x|+1)^b` on **every** word. It gives
`InP SAT`, and with `SATHard` it gives `PEqualsNP`.

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

Arithmetic core (all instance types):

- `FPTBound time size param f c := ∀ I, time I ≤ f (param I) · (size I)^c`.
- `LogBoundedParam size param b := ∀ I, 2^(param I) ≤ (size I)^b`, which says
  the parameter is at most `b · log₂(size)`.
- `LogParamFPTObligationFor Correct time size` is the generic **schema**: an
  algorithm `A` with `Correct A`, an FPT bound with `f k = 2^k`, and a parameter
  that is logarithmically bounded on every instance. `Correct` and `time` are
  parameters, so the schema is not itself an open problem.

Shared machine model (`proofs/complexity/lean/Complexity.lean`,
`proofs/experiments/issue532/lean/Machines.lean`): instances are words
`x : Word`, a decider is a `Machine`, its time on `x` is the step count `t` of
`Run m (initial x) t v`, and polynomials are `Polynomial.eval p n =
coefficient · (n+1)^degree`. The size of `x` is `|x| + 1`.

```lean
def LogParamFPT (L : Language) : Prop :=
  ∃ (m : Machine) (param : Word → Nat) (c b : Nat),
    (∀ x, 2 ^ param x ≤ (x.length + 1) ^ b) ∧
    ∀ x, ∃ t v, t ≤ 2 ^ param x * (x.length + 1) ^ c ∧ Run m (initial x) t v ∧ v = L x

def LogParamFPTObligation : Prop := LogParamFPT SAT
```

`SAT` is the shared language `Issue532.Machines.SAT` (a word is decoded to a
CNF). `steps m x` is the step count of the unique halting run of `m` on `x`,
and `MachineDecides L m` says that run answers `L x`; these instantiate the
schema.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `tested` | small illustration kept from an earlier round (a one-line monotonicity step, not a main result): a monotone cost is bounded when the parameter is bounded | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_param_bound_poly` | `f k ≤ n^a` implies `f k · n^c ≤ n^(a+c)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_log_param_poly` | `2^k ≤ n` implies `2^k · n^c ≤ n^(c+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `linear_lt_exp` | `a · (q+1) < 2^q` for `q ≥ 2a+1` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `dyadic_bracket` | every `n ≥ 1` has `L` with `2^L ≤ n < 2^(L+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `exp_beats_poly` | `c · (n+1)^d < 2^n` for all `n ≥ 2^(2(c+d)+1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `exists_threshold` | for all `c, d` there is `N` with `c · (n+1)^d < 2^n` for all `n ≥ N` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `poly_lt_two_pow` | for all `c, d` there is `n` with `c · (n+1)^d < 2^n` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_full_param_not_poly` | for all `a, d, c` there is `n` with `a · (n+1)^d < 2^n · n^c` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `fpt_log_param_polytime` | an FPT bound `2^k · n^c` with `2^k ≤ n^b` gives `time ≤ n^(b+c)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `obligation_gives_poly_time` | the schema `LogParamFPTObligationFor` yields a correct algorithm with a polynomial bound | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `logParamFPT_inP` | `LogParamFPT L → InP L`: the step bound is at most the polynomial `(x.length + 1)^(b+c)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `logParam_obligation_inP` | `LogParamFPTObligation → InP SAT` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `logParam_route_gives_pEqualsNP` | `SATHard → LogParamFPTObligation → PEqualsNP` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `not_forall_logParamFPT` | non-vacuity: `LogParamFPT L` fails for some language `L` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `steps_eq` | the step count `steps m x` is the length of any halting run of `m` on `x` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |
| `logParamFPT_iff_schema` | `LogParamFPT L ↔ LogParamFPTObligationFor (MachineDecides L) steps (fun x => x.length + 1)` | [Lean](../lean/Idea37.lean) | [Rocq](../rocq/Idea37.v) |

The arithmetic rows are proved in both files. The machine-model rows (from
`logParamFPT_inP` on) are proved in Lean only so far; the intended Rocq names
are the same, with the schema named `LogParamFPTObligationFor` as in Lean.
The arithmetic proofs are constructive. `steps` uses classical choice, and
`not_forall_logParamFPT` uses the classical diagonal language of the shared
layer.

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
where `2^n · n^c ≥ 2^n > a (n+1)^d` (`fpt_full_param_not_poly`). So for an FPT
algorithm whose parameter can be as large as the input, the FPT bound gives no
polynomial guarantee, whatever `c` is. (This is a statement about the bound,
not a lower bound on the running time of any particular algorithm.)

**(c) The gap between (a) and (b).** Either the parameter is logarithmic on
every instance, and then the problem is in P, or it is not, and then the FPT
bound gives nothing better than exponential time on the bad instances. For SAT the
first alternative is exactly `LogParamFPTObligation`. It gives `InP SAT`
(`logParam_obligation_inP`, via `inP_of_decidesWithin` with the polynomial
`1 · (n+1)^(b+c)`), and with the named hypothesis `SATHard` it gives P = NP. There is no intermediate
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
  time on graphs of bounded treewidth (given a tree decomposition, which
  Bodlaender's algorithm supplies in linear time for fixed width). Encoding a
  CNF as a relational structure, this covers SAT of bounded primal or
  incidence treewidth. Not formalized.
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

**At full potential**, the idea proves the open obligation

```lean
def LogParamFPTObligation : Prop := LogParamFPT SAT

theorem logParam_obligation_inP (h : LogParamFPTObligation) : InP SAT
theorem logParam_route_gives_pEqualsNP (hard : SATHard) (h : LogParamFPTObligation) :
    PEqualsNP
```

The time is the step count of a `Run` of a `Complexity.Machine`, so the
obligation cannot be met by choosing a convenient cost function. The step from
`InP SAT` to `PEqualsNP` needs the named hypothesis `SATHard` (NP-hardness of
`SAT`, the hard half of Cook–Levin), stated in `Machines.lean` and not
mechanised. `logParamFPT_iff_schema` shows that `LogParamFPT L` is exactly the
generic schema `LogParamFPTObligationFor` instantiated with machines, their
step count `steps` and the size `|x| + 1`. `not_forall_logParamFPT` shows that
`LogParamFPT` is not a consequence of the definitions: it fails for the
diagonal language. The formalization also checks that nothing weaker suffices
from the FPT bound alone (`fpt_full_param_not_poly`).

The converse, `InP SAT → LogParamFPTObligation`, is not claimed. A machine with
time bound `a · (n+1)^d` meets the FPT form only if the constant `a` can be
absorbed. At `|x| = 0` the bound `2^(param x) · 1` with `2^(param x) ≤ 1` forces
one step. In the informal sense (up to constant factors) the two statements are
equivalent: take `param = 0`.

**Why the obligation is hard.** Under ETH (Impagliazzo–Paturi), no
NP-complete problem admits a parameter with both properties, since that would
give a polynomial-time, hence subexponential, algorithm for 3-SAT. So the
obligation is at least as hard as refuting ETH. Parameters that are small on
"typical" or "structured" instances (treewidth, backdoor size) are not small on
all instances. A padding trick, which pads an instance with `k` variables to
length `2^k`, makes any parameter logarithmic but needs an exponential-size
reduction. That is not a polynomial reduction.

**What is gained.** A correct and fully general accounting of when
parameterized algorithms yield polynomial time. It is useful for auditing
claims of the form "SAT is FPT in parameter X, and X is small".

**Caveats.** `SATHard` is a named hypothesis, not a mechanised theorem. ETH and
the parameterized results of section 5 are cited, not formalized. The
machine-model part is so far only in Lean; `Idea37.v` has the arithmetic and
the schema.

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
