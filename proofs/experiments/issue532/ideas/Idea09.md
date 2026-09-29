# Idea 09 — Description length versus running time (and Levin universal search)

**Verdict:** Refuted as a route (general theorem) — the inference "the shortest program for a task is also the fastest" is false for every target `v ↦ v + k` with `k ≥ 6` in an explicit loop language with honest size and cost semantics (`shortest_is_never_fastest`). The meta-algorithmic half of the idea is developed to full strength as Levin universal search: it is sound, complete, and within a fixed factor `8 · 2^i` of any witness-producing program `i` (`levin_search_bound`). Whether that search is polynomial for SAT is exactly the open obligation `SATWitnessMachine`, stated in the shared machine model (one `Complexity.Machine` outputs a satisfying assignment of every satisfiable encoded formula within a polynomial number of `Reaches` steps). It is proved to imply `InP SAT` and, with `SATHard`, `PEqualsNP`; the composition step `WitnessCheckInP` and `SATHard` are explicit hypotheses (known theorems, not mechanised). The converse holds by search-to-decision self-reducibility (cited, not formalized); nothing here decides the obligation.

## 1. The idea at full strength

Issue #532, Part I item 5 ("Shortest program ⇒ shortest runtime") reframes
the textbook remark "shortest description does not imply fastest execution"
as model-dependent: "This separation relies on allowing reuse, loops, and
iteration ... We don't know whether alternative models collapse this gap."
Part I item 8 ("Meta-algorithms and 'shortest solver of solvers'") adds the
hope that a meta-search over programs can "progressively carve the space".

The most ambitious version of the idea, aimed at **P = NP**, reads:

1. Among all SAT solvers, pick the one with the shortest description (or
   search programs in order of description length).
2. Argue that the shortest correct solver is also (nearly) the fastest one,
   so that a search ordered by length finds an efficient solver.
3. Conclude that SAT has a polynomial-time algorithm if a short one exists,
   and read off its running time from its description length.

A second variant, aimed at **P ≠ NP**, argues the converse: if every short
program is slow then SAT has no fast program.

Both variants need a quantitative link between description length and time.
This dossier shows that no monotone link exists even in a tiny language, and
that the best meta-algorithm one can hope for (Levin search) moves the whole
difficulty into a single statement equivalent to P = NP.

## 2. Precise mathematical formulation

**Loop language.** `Prog ::= inc | seq p q | loop k b` with `k ∈ ℕ`.

* Size (description length): `size inc = 1`, `size (seq p q) = size p + size q`,
  `size (loop k b) = bits k + 1 + size b`, where `bits k` is the binary length
  of `k` (`bits 0 = bits 1 = 1`; Lean defines it recursively, Rocq as
  `1 + Nat.log2 k`; both satisfy `k < 2^(bits k) ≤ 2k` for `k ≥ 1`). Loop
  counters are therefore charged honestly in binary, not as one free symbol.
* Semantics `run p v = (value, steps)`: `inc` adds one in one step; `seq`
  composes and adds step counts; `loop k b` runs `b` exactly `k` times, with
  one bookkeeping step per iteration and one exit step, so `loop 0 b` costs 1.
* `gain p` and `cost p` are the closed forms: `gain (loop k b) = k · gain b`,
  `cost (loop k b) = k · (cost b + 1) + 1`.

**Claim to be refuted ("shortest ⇒ fastest").** For a target function `f`,
if `p` has minimum size among programs computing `f`, then `p` has minimum
cost among them. Weaker monotone forms: `size p ≤ size q → cost p ≤ cost q`
for programs computing the same function (and the converse).

**Levin search (abstract model).** Programs are indexed by `i ∈ ℕ`.
`runs i t : Option W` is the output of program `i` when run for `t` steps
from scratch (restart semantics), assumed monotone in `t`
(`MonotoneRuns`). A verifier `V : W → Bool` checks candidate witnesses. Phase
`j` runs programs `i = 0, ..., j` for `2^(j−i)` steps each and returns the
first verified output; `search J` returns the first successful phase `≤ J`.
Work is the total number of simulated steps (`phaseWork`, `totalWork`);
verifier calls and simulation overhead are not charged (see §6).

**Schema.** `PolyTimeWitnessProgramExistsFor sz runs V`: there are a fixed
program index `i` and constants `c, d` such that on every satisfiable
instance `x` program `i` outputs a verified witness within `c·sz(x)^d + c`
steps. Since `runs` is a parameter, the schema says nothing until `runs` is
fixed; with an oracle for `runs` it holds trivially. It is therefore not the
obligation.

**Machine model.** Words are `List Bool`; a machine is a
`Complexity.Machine` and its running time is the `Reaches`/`Run` step count
of the shared layer (`Machines.lean`). `Computes m f p` says `m` leaves `f x`
on its tape within `p(|x|)` steps. The SAT verifier is
`satCheck x w = evalCNF (toAssign w) (decode x)`, and
`SAT x = true ↔ ∃ w, satCheck x w = true` (`sat_iff_exists_witness`).
For Levin search over machines, `OutputsWithin m x t w` says `m` exits on `x`
with output `w` within `t` steps, and `machineRuns e i x t` is that output for
the `i`-th machine of an enumeration `e` (well defined by
`outputsWithin_unique`).

**Open obligation.** `SATWitnessMachine := PolyWitnessMachine satCheck`, i.e.

```lean
∃ (m : Machine) (f : Word → Word) (p : Polynomial), Computes m f p ∧
  ∀ x, (∃ w, satCheck x w = true) → satCheck x (f x) = true
```

**Known theorem used as a hypothesis.** `WitnessCheckInP`: for every
`Computes m f p`, the language `x ↦ satCheck x (f x)` is in P (closure of P
under composition with polynomial-time functions; single-tape simulation,
Sipser Theorem 7.8). It is true but not mechanised here, and it appears only
as a named hypothesis.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `bits_spec` | For `n ≥ 1`: `n < 2^(bits n) ≤ 2n`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `run_eq` | Every program maps `v` to `v + gain p` in exactly `cost p` steps. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `cost_ge_gain` | For every program, `gain p ≤ cost p`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `time_optimal_is_loop_free` | If `cost p = gain p` then `p` contains no loop. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `loopFree_size_eq_cost` | For loop-free `p`: `size p = cost p` and `size p = gain p`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `fastest_programs_have_size_k` | If `gain p = k` and `cost p = k` then `size p = k`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `unroll_spec` | `unroll m` (m+1 increments) has gain, cost and size all `m + 1`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `loop_inc_size` | `loop k inc` has gain `k`, cost `2k + 1`, size `bits k + 2`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `loop_inc_exponential_gap` | For `k ≥ 1`: `2^(size (loop k inc)) ≤ 4 · cost (loop k inc)`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `loop_inc_short` | For `k ≥ 6`: `size (loop k inc) < k`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `shortest_is_never_fastest` | For `k ≥ 6` and every `q` with `gain q = k` and `size q ≤ size (loop k inc)`: `cost (unroll (k−1)) < cost q`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `shorter_not_implies_faster` | Not every pair of same-function programs with `size p ≤ size q` has `cost p ≤ cost q`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `faster_not_implies_shorter` | Not every pair of same-function programs with `cost p ≤ cost q` has `size p ≤ size q`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `padding_longer_and_slower` | For every `k`, padding `loop k inc` with `loop 0 inc` gives a same-function program that is longer and slower. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `search_sound` | Every witness returned by Levin search is accepted by `V`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `levin_finds` | If `runs` is monotone, `runs i t = some w`, `V w = true` and `t ≤ 2^L`, then `search (i + L)` returns some verified witness. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `phaseWork_eq` | Phase `j` simulates exactly `2^(j+1) − 1` steps. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `totalWork_lt` | `totalWork J + 1 < 2^(J+2)`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `exists_ceil_log` | For `t ≥ 1` there is `L` with `t ≤ 2^L < 2t`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `levin_search_bound` | Under monotonicity, if program `i` outputs a verified witness within `t ≥ 1` steps, some `search J` returns a verified witness and `totalWork J < 8 · 2^i · t`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `PolyTimeWitnessProgramExistsFor` | Schema (abstract `runs`, not the obligation): one fixed program index finds verified witnesses in `c·sz(x)^d + c` steps. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `levin_poly_for` | If the schema holds (and runs are monotone), there are `K, c, d` such that Levin search finds a verified witness on every satisfiable `x` with `totalWork J < K · (c·sz(x)^d + c + 1)`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `sat_iff_exists_witness` | `SAT x = true ↔ ∃ w, satCheck x w = true`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `SATWitnessMachine` | Open obligation: one machine computes (`Computes m f p`) a satisfying assignment `f x` of every satisfiable `x`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `WitnessCheckInP` | Known theorem, not mechanised (hypothesis only): `Computes m f p → InP (fun x => satCheck x (f x))`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `inP_sat_of_witnessMachine` | `WitnessCheckInP → SATWitnessMachine → InP SAT`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `pEqualsNP_of_witnessMachine` | `WitnessCheckInP → SATHard → SATWitnessMachine → PEqualsNP`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `not_forall_polyWitnessMachine` | Non-vacuity: `¬ ∀ V, PolyWitnessMachine V` (Cantor over machine encodings). | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `outputsWithin_unique` | A machine's output within any time bound is unique. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `machineRuns_monotone` | Machine runs `machineRuns e · x` are monotone, so Levin's schema applies to them. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |
| `levin_sat_of_witnessMachine` | Under `SATWitnessMachine`, for every enumeration `e` listing all machines, there are `K` and a polynomial `p` with: on every `x` with `SAT x = true`, Levin search over `machineRuns e` returns a satisfying assignment with `totalWork J < K · (p(|x|) + 1)`. | [Lean](../lean/Idea09.lean) | [Rocq](../rocq/Idea09.v) |

Rocq-specific difference: Lean reads machine outputs with classical choice;
Rocq's `machineRuns` is computable (step-bounded `exitWithin` and
`readOutput`), `outputsWithin_unique`, `machineRuns_eq` and `machineRuns_spec`
take explicit arguments, and `not_forall_polyWitnessMachine` is a direct
diagonal over clocked machine/polynomial codes (`outputsTrue`, `witnessDiag`)
instead of the Cantor family lemma. The Rocq file is fully constructive.

No theorem in either file proves or refutes P = NP.

## 4. Complete argument

### 4.1 Closed form of the semantics

By induction on `p` (`run_eq`): `inc` maps `v ↦ v + 1` in 1 step; for
`seq p q` the values add and the costs add; for `loop k b`, a separate
induction on `k` (`iter_eq`) shows that iterating a map `v ↦ (v + g, c)`
`k` times yields `(v + k·g, k·(c+1) + 1)`. So every program computes a
translation `v ↦ v + gain p` and its step count does not depend on `v`.

### 4.2 Time is at least the output increment

`cost_ge_gain`: `inc` has gain 1 and cost 1; sequencing adds both; a loop
has gain `k·gain b ≤ k·(cost b + 1) < k·(cost b + 1) + 1`. Hence **no
program for `v ↦ v + k` runs in fewer than `k` steps**, and `unroll (k−1)`
attains `k` exactly (`unroll_spec`): the time-optimal cost is exactly `k`.

### 4.3 Time-optimal programs are long

`time_optimal_is_loop_free`: if `cost p = gain p`, then `p` has no loop.
For `seq`, both components satisfy `gain ≤ cost`, so equality of the sums
forces equality in each and induction applies; for a loop, the strict
inequality of §4.2 makes `cost = gain` impossible. `loopFree_size_eq_cost`:
in a loop-free program every `inc` contributes 1 to size, cost and gain.
Together (`fastest_programs_have_size_k`): **every fastest program for
`v ↦ v + k` has size exactly `k`.**

### 4.4 Short programs exist and are slow

`loop k inc` has size `bits k + 2` and cost `2k + 1` (`loop_inc_size`). Using
`2^(bits k) ≤ 2k` and `2m + 4 < 2^m` for `m ≥ 4` (`small_lt_pow`), we get
`bits k + 2 < k` for every `k ≥ 6` (`loop_inc_short`). Concretely:

| `k` | `size (loop k inc)` | `cost (loop k inc)` | fastest cost | fastest size |
| --- | --- | --- | --- | --- |
| 6 | 5 | 13 | 6 | 6 |
| 16 | 7 | 33 | 16 | 16 |
| 1024 | 13 | 2049 | 1024 | 1024 |

`loop_inc_exponential_gap` makes the growth explicit: for `k ≥ 1`,
`2^size ≤ 4·cost`, i.e. the running time of a short program can be
exponential in its length.

### 4.5 The refutation

`shortest_is_never_fastest`: fix `k ≥ 6` and any `q` with `gain q = k` and
`size q ≤ size (loop k inc) < k`. If `cost q = k`, then §4.3 gives
`size q = k`, a contradiction; since `cost q ≥ k` by §4.2, `cost q > k =
cost (unroll (k−1))`. A minimum-size program for `v ↦ v + k` has size at most
`size (loop k inc)`, so **no minimum-size program is time-optimal, for
every `k ≥ 6`.** This is a statement about the true minimum over all programs,
obtained without computing that minimum.

`shorter_not_implies_faster` and `faster_not_implies_shorter` instantiate the
family at `k = 6` to refute both monotone laws, and
`padding_longer_and_slower` shows that "longer" is not a proxy for "faster"
either. `loopFree_size_eq_cost` confirms the issue's remark: in the
loop-free fragment size and time coincide, so the separation is caused
precisely by iteration.

### 4.6 Levin universal search

*Soundness* (`search_sound`): each phase only returns outputs that passed
`check V`. *Completeness* (`levin_finds`): if `runs i t = some w`, `V w =
true` and `t ≤ 2^L`, then in phase `j = i + L` program `i` receives budget
`2^(j−i) = 2^L ≥ t`, so by monotonicity it outputs `w`, which passes the check;
`phaseAux_finds` shows the phase returns some verified witness (possibly
from a smaller index), and `search_mono` propagates success to `search (i+L)`.

*Work* (`phaseWork_eq`, `totalWork_lt`): phase `j` costs
`Σ_{i≤j} 2^(j−i) = 2^(j+1) − 1`, and summing over `j ≤ J` gives
`2^(J+2) − J − 3 < 2^(J+2)`. With `L` chosen by `exists_ceil_log`
(`t ≤ 2^L < 2t`), the total is below `2^(i+L+2) = 4·2^i·2^L < 8·2^i·t`
(`levin_search_bound`). Example: if program `i = 10` outputs a witness in
`t = 1000` steps, then `L = 10`, success by phase 20, and total simulated
work is below `2^22 ≈ 4.2·10^6 < 8·1024·1000 ≈ 8.2·10^6`.

*Schema theorem* (`levin_poly_for`): if one fixed program `i` is polynomial
on all satisfiable instances, then Levin search is polynomial on satisfiable
instances, measured in simulated steps, with factor `K = 8·2^i`, and it does
not need to know `i`, `c`, or `d`.

### 4.7 The obligation in the machine model

*Witnesses.* `sat_iff_exists_witness`: if `a` satisfies `decode x`, then so
does `toAssign (prefixOf a n)` for `n = numVars (decode x)`, because the
formula only reads variables below `n` (`evalCNF_congr`, `varsBelow_numVars`,
`toAssign_prefixOf`); conversely a witness `w` gives the assignment
`toAssign w`.

*Conditional theorems.* Under `SATWitnessMachine` take `m, f, p`. For every
`x`, `SAT x = satCheck x (f x)`: if `SAT x` then `f x` is a witness; if
`satCheck x (f x)` then `SAT x`. So `SAT` equals the language
`x ↦ satCheck x (f x)`, which is in P by the hypothesis `WitnessCheckInP`
(`inP_sat_of_witnessMachine`). With `SATHard`, `pEqualsNP_of_inP_sat` gives
`PEqualsNP` (`pEqualsNP_of_witnessMachine`).

*Non-vacuity.* `not_forall_polyWitnessMachine`: for the verifier
`V x w = (w == [L x])` every `x` has a witness, so a witness machine for `V`
computes `x ↦ [L x]`. By `computes_unique` the machine then determines `L`
(`outputsTrue m = L`). Cantor's argument over machine encodings
(`exists_language_not_in_family encMachine`) yields an `L` determined by no
machine, so some verifier has no witness machine.

*Levin over machines.* A run that exits is unique (`reaches_exit_unique`,
`map_ofBool_blanks_injective`), so `OutputsWithin m x t w` determines `w`
(`outputsWithin_unique`), `machineRuns e` is well defined and monotone in `t`
(`machineRuns_monotone`). If `e i = m` and `m` computes `f` within `p`, then
`machineRuns e i x (p(|x|) + 1) = some (f x)`, and `levin_search_bound` gives
total simulated work below `8·2^i·(p(|x|) + 1)` on every satisfiable `x`
(`levin_sat_of_witnessMachine`).

## 5. Known results and literature

* L. A. Levin, "Universal sequential search problems", *Problemy Peredachi
  Informatsii* 9(3), 1973 (English translation in *Problems of Information
  Transmission*). Introduces universal search: an explicit algorithm for
  NP search problems that is optimal up to a multiplicative factor
  depending on the competing program. The abstract core of this bound is
  formalized here (restart semantics, `levin_search_bound`); Levin's
  machine-level version is not.
* M. Blum, "A machine-independent theory of the complexity of recursive
  functions", *Journal of the ACM* 14(2), 1967. The speed-up theorem: some
  computable functions have no fastest program at all, so "the fastest
  program" need not exist. Not formalized here.
* M. Hutter, "The fastest and shortest algorithm for all well-defined
  problems", *International Journal of Foundations of Computer Science*
  13(3), 2002. A refinement of Levin search with provably-correct
  speed-up proofs; it has a huge additive constant and does not decide
  P versus NP. Not formalized here.
* M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*, Springer (3rd ed., 2008). Background on description length,
  Levin's time-bounded complexity `Kt`, and universal search. Not formalized.
* S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. Standard source for search-to-decision
  reduction for SAT, which makes the obligation equivalent to P = NP. Not
  formalized here.

## 6. How far the idea can be pushed toward P vs NP

**What the idea gives at full potential.** Levin search is an explicit,
fully specified algorithm `U` for SAT search such that, for every SAT
search algorithm `A` with index `i_A` and running time `T_A`, `U` runs in
time `O(2^{i_A} · T_A(n))` plus verification and simulation overhead
(polynomial per call). Consequently:

* If P = NP, then `U` (a program we can write down today) finds satisfying
  assignments in polynomial time on every satisfiable input — we would not need to find the algorithm, only the
  proof of its running time.
* "The fastest SAT search algorithm is known up to a fixed factor" is a
  true statement, but the factor `2^{i_A}` may be astronomically large, and
  the bound says nothing about whether any `T_A` is polynomial.

**Exact remaining obligation.** `SATWitnessMachine` (Lean `def`): some
`Complexity.Machine` computes, within a polynomial bound on its `Reaches`
step count, a satisfying assignment of every satisfiable encoded formula.
Proved: it implies `InP SAT` given the composition theorem `WitnessCheckInP`
(`inP_sat_of_witnessMachine`), and `PEqualsNP` given also `SATHard`
(`pEqualsNP_of_witnessMachine`); both are true, cited, not mechanised, and
used only as named hypotheses. The converse (P = NP gives a witness machine)
holds by search-to-decision self-reducibility and is cited, not formalized.
So the obligation is **equivalent to P = NP** and not weaker than the
original problem. The conditional theorems show that Levin search loses
nothing beyond a fixed factor, not that the obligation is easier.
`not_forall_polyWitnessMachine` shows that the witness-machine property is
not satisfied by every verifier, so the obligation is not vacuous. The
abstract schema `PolyTimeWitnessProgramExistsFor` is kept only as the
interface of the Levin search theorems; it is not the obligation.

**Decision versus search.** Levin search does not halt on unsatisfiable
formulas. To obtain a decider one must additionally know the polynomial
bound (and the index `i`), then reject after that many steps. Proving such a
bound is again the obligation.

**Barriers.** The P = NP direction of this route is not limited by the
lower-bound barriers (relativization, natural proofs, algebrization concern
proofs of P ≠ NP), but it is limited by the fact that it contains no
information about SAT: universal search is a relativizing construction and
works identically relative to any oracle, including oracles where P ≠ NP
(Baker–Gill–Solovay 1975). So universal search cannot by itself establish a
polynomial bound. For the P ≠ NP variant ("every short program is slow"),
`shortest_is_never_fastest` shows that description length does not bound
time from below in general, and a proof that every program for SAT is slow
is precisely a superpolynomial lower bound, subject to all known barriers.

**Model dependence.** The issue asks whether alternative models collapse
the gap. In the loop-free fragment they do (`loopFree_size_eq_cost`), but
such a model cannot express polynomial-time algorithms on unbounded input
sizes with fixed-size programs; as soon as iteration is allowed, the
exponential gap `loop_inc_exponential_gap` appears. Blum's speed-up theorem
shows that in general models even the existence of a fastest program fails.

## 7. Failure modes this idea catches

* **Hidden exponential work** (family 2 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): a short loop can
  hide exponential time (`loop_inc_exponential_gap`). An attempt that
  argues "the algorithm has a short description, hence is efficient" is
  refuted by this family.
* **Encoding-size mistakes** (family 17): charging a loop counter as one
  symbol instead of `bits k` changes size claims; this file charges binary
  length explicitly.
* **Confusing verification and search** (family 15): Levin search turns a
  verifier into a search procedure, but its running time depends on an
  unknown program; possessing a verifier does not give a polynomial
  algorithm.
* **Structure theorem from one algorithm class** (family 20): the refutation
  shows that optimising one resource (length) says nothing about another
  (time) across all programs.
* **Circular reasoning** (family 12): a proof that "Levin search is
  polynomial" must prove `SATWitnessMachine`, i.e. P = NP; an
  attempt that assumes it has assumed the conclusion.

Audit rule: any argument that infers time bounds from description length
must state a theorem of the form of `shortest_is_never_fastest` for its own
model and explain why its model avoids it.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea09.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea09.v
```

Both commands print nothing on success. Remove the generated
`Idea09.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
