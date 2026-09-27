# Idea 22 — Decision-to-search self-reduction

**Verdict:** Correct tool, insufficient alone (general theorem proved)

SAT is self-reducible. From any exact decision procedure, fixing the
variables one at a time gives a satisfying assignment of every satisfiable
CNF, with exactly one decider call per variable. The files prove this for
every CNF and every decider. The Lean file also proves the polynomial cost
transfer in the shared machine model: a `Complexity.Machine` deciding `SAT`
within a polynomial number of `Run` steps drives the self-reduction to a
witness with total `Run` step count of all questions polynomial in the
encoding length (`decision_to_search`). So finding a witness is no harder
than deciding, and, with the NP-hardness of SAT (`SATHard`, a named
hypothesis: Cook–Levin, not mechanised), P = NP is equivalent to
polynomial-time SAT search. The tool does not produce a fast decider. The
remaining obligation `ExactPolyDecider := PolyDec SAT` is exactly SAT ∈ P.

## 1. The idea at full strength

Issue #532 Part I item 8 ("Meta-algorithms and 'shortest solver of
solvers'") and Part I item 5 ("'Shortest program ⇒ shortest runtime'")
suggest turning knowledge about a problem into an efficient procedure.
Phase 1 asks to formalize the baseline world, including "Complexity
classes". The research log records the core observation that a "decision
guides search". At full strength the idea reads:

> The yes/no answer of a decider tells us, variable by variable, which way
> to go. So the hard part of SAT is only the yes/no question. Search, and
> the witnesses that NP is about, add no difficulty. Therefore it is enough
> to find a fast decider, perhaps a non-constructive or "meta" one (toward
> P = NP). Conversely, a lower bound for search is a lower bound for
> decision (toward P ≠ NP).

The precise claims are:

* the self-reduction is correct;
* its overhead is polynomial;
* hence P = NP iff SAT search is in polynomial time.

## 2. Precise mathematical formulation

* The SAT core is the same as in Idea 21: literals `⟨var, pos⟩`, clauses,
  CNFs, `evalCNF`, and `Satisfiable φ := ∃ a, evalCNF a φ = true`.
  `restrict v b φ` drops the clauses satisfied by `v := b` and deletes the
  remaining literals on `v`. `setVar a v b` updates `a` at `v`.
* `size φ` is the number of literal occurrences plus the number of
  clauses. `varsOf φ` lists the variable occurrences of `φ`, so its length
  is at most `size φ`.
* `Decides dec := ∀ ψ, dec ψ = true ↔ Satisfiable ψ` is exact correctness
  on every CNF.
* `search dec vs φ` handles `vs = v :: vs'` as follows. It sets
  `b := dec (restrict v true φ)`, recurses on `restrict v b φ`, and returns
  `setVar r.1 v b` together with the number of calls plus one. At
  `vs = []` it returns the all-false assignment and 0 calls.
* `searchCost dec cost vs φ` is the sum of `cost ψ` over the queries `ψ`
  that `search` actually asks.
* Schema (abstract cost): for `Cost : (CNF → Bool) → CNF → Nat`,
  `ExactPolyDeciderFor Cost := ∃ dec c k, Decides dec ∧ ∀ ψ, Cost dec ψ ≤ c (size ψ + 1)^k`
  and `PolySearchFor Cost`. These are only interfaces for the cost
  arithmetic; they are not the obligation.
* **Machine model.** Words are `List Bool`; deciders are
  `Complexity.Machine`s and their cost is the `Run` step count of the shared
  layer (`Machines.lean`). A CNF `φ` of this file is translated literal by
  literal to the shared layer (`toM`, `evalCNF_toM`) and encoded as the word
  `enc φ := Machines.encodeCNF (toM φ)`, of length `encLen φ`; then
  `SAT (enc φ) = true ↔ Satisfiable φ` (`sat_enc`). For a machine `m`,
  `machineDec m x` is its answer on `x` and `runTime m x` its (unique) `Run`
  step count.
* **Open obligation.** `ExactPolyDecider := PolyDec SAT`, i.e.
  `∃ (m : Machine) (p : Polynomial), DecidesWithin m p SAT`: one machine
  halts on every word `x` within `p(|x|)` steps with the answer `SAT x`.
  This is `InP SAT`.
* **Machine search.** `PolySearch` states that some machine `m` halts within
  a polynomial on every input and, for every CNF `φ`, the self-reduction
  driven by `ψ ↦ machineDec m (enc ψ)` returns a satisfying assignment if `φ`
  is satisfiable, while the total `Run` step count
  `searchCost (…) (fun ψ => runTime m (enc ψ)) (varsOf φ) φ` of all
  questions is at most `q(encLen φ)` for a polynomial `q`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `eval_restrict`, `sat_split` | Restriction is evaluation under `setVar`. `φ` is satisfiable iff one of its two restrictions on `v` is. These are copied from Idea 21. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `size_restrict_le` | `size (restrict v b φ) ≤ size φ`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `varsOf_spec`, `varsOf_length_le` | All variables of `φ` are in `varsOf φ`, and its length is at most `size φ`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `search_correct` | For all `dec` with `Decides dec`, all `vs`, and all `φ` with `VarsIn φ vs` that are satisfiable, the returned assignment satisfies `φ`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `search_calls` | For all `dec vs φ`, the number of decider calls is exactly `length vs`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `search_decides` | With `Decides dec` and `VarsIn φ vs`: the output satisfies `φ` iff `φ` is satisfiable. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `fullSearch_correct`, `fullSearch_calls_le` | Searching over `varsOf φ` is correct and makes at most `size φ` calls. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `search_gives_decider` | Any procedure that returns a satisfying assignment of every satisfiable CNF yields an exact decider (evaluate its output). | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `searchCost_le` | If every query costs at most `c (size ψ + 1)^k`, the search costs at most `length vs · c (size φ + 1)^k`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `searchCost_le_measure` | The same bound for any size measure `μ` that restriction does not increase and any monotone bound `B`: total cost `≤ length vs · B (μ φ)`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `decision_to_search_for` | Schema: `ExactPolyDeciderFor Cost → PolySearchFor Cost` for every abstract cost model (total query cost at most `c (size φ + 1)^(k+1)`). | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `satDec_correct` | The splitting decider of Idea 21 on `varsOf φ` is an exact decider, unconditionally. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `unconditional_search` | With `satDec`, the self-reduction finds a satisfying assignment of every satisfiable CNF. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `evalCNF_toM`, `sat_enc` | The translation to the shared layer preserves evaluation, and `SAT (enc φ) = true ↔ Satisfiable φ`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `encLen_restrict_le`, `size_le_encLen` | Restriction never lengthens the encoding, and `size φ ≤ encLen φ`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `machineDec_eq`, `runTime_eq` | If `Run m (initial x) t b`, then `machineDec m x = b` and `runTime m x = t`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `decides_of_decidesWithin` | A machine with `DecidesWithin m p SAT` gives an exact decider `ψ ↦ machineDec m (enc ψ)` of this file's CNFs. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `ExactPolyDecider` | Open obligation: `PolyDec SAT` (one machine decides `SAT` within a polynomial number of `Run` steps). | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `decision_to_search` | `ExactPolyDecider → PolySearch`: the machine-driven self-reduction is correct on every satisfiable CNF, and the total `Run` step count of its questions is at most `size φ · p(encLen φ) ≤ q(encLen φ)`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `inP_sat_of_exactPolyDecider` | `ExactPolyDecider → InP SAT`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `pEqualsNP_of_exactPolyDecider` | `SATHard → ExactPolyDecider → PEqualsNP`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `exists_not_polyDec` | Non-vacuity: some language has no polynomial-time machine decider. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |

The machine-model rows (from `evalCNF_toM` on) are in the Lean file; the Rocq
file still states the earlier cost-model version and has not been ported yet.
Rocq uses `fst`/`snd` where Lean uses `.1`/`.2`.

## 4. Complete argument

**Correctness** (induction on `vs`, for all `φ` at once).

* If `vs = []`, then `VarsIn φ []` means `φ` has no literals. A
  satisfiable such `φ` is satisfied by the all-false assignment
  (`sat_no_vars`).
* If `vs = v :: vs'`, let `b = dec (restrict v true φ)`. First show that
  `restrict v b φ` is satisfiable.
  * If `b = true`, this follows from `Decides dec`.
  * If `b = false`, then `restrict v true φ` is unsatisfiable, again by
    `Decides dec`. Since `φ` is satisfiable, `sat_split` leaves only
    `restrict v false φ`.
* The variables of `restrict v b φ` lie in `vs'` (`restrict_vars`). So the
  induction hypothesis gives an assignment `r` satisfying it. By
  `eval_restrict`, `setVar r v b` satisfies `φ`.

Duplicates in `vs` do no harm. The proof never needs `vs` to be duplicate
free.

**Call count.** Each step makes one call and recurses once, so the count is
`length vs`. For `vs = varsOf φ` this is at most `size φ`.

**Cost.** Restriction does not increase size, and `c (n+1)^k` is monotone
in `n`. So every query in the run costs at most `c (size φ + 1)^k`, and
there are `length vs` of them. With `length (varsOf φ) ≤ size φ` and
`n · c (n+1)^k ≤ c (n+1)^(k+1)`, the total is at most
`c (size φ + 1)^(k+1)`. The cost of computing the restrictions, which is
linear in `size φ` per step, is not counted in `searchCost`. In any
reasonable machine model it adds `O(size φ^2)`.

**Cost in the machine model.** Let `m` decide `SAT` within `p`. Each question
`ψ` is answered by the run of `m` on `enc ψ`; its answer is `SAT (enc ψ)`, so
`ψ ↦ machineDec m (enc ψ)` is an exact decider (`decides_of_decidesWithin`),
and its step count is `runTime m (enc ψ) ≤ p(encLen ψ)` (`runTime_eq`, using
`run_deterministic`). Every question is a restriction of `φ` and restriction
only deletes literals and clauses, so `encLen ψ ≤ encLen φ`
(`encLen_restrict_le`). There are at most `size φ ≤ encLen φ` questions
(`size_le_encLen`: every literal and every clause end marker takes at least
two bits). By `searchCost_le_measure` the total `Run` step count is at most
`encLen φ · p(encLen φ) ≤ q(encLen φ)` with `q` of degree one higher
(`decision_to_search`).

*Worked example.* Take `φ = (x₀ ∨ x₁) ∧ (¬x₀)` with `vs = [0, 1]`.

* `restrict 0 true φ` contains the empty clause (from `¬x₀`), so the
  decider says false and `x₀ := false`.
* `restrict 0 false φ = [[x₁]]`, and `restrict 1 true` of it is `[]`,
  which is satisfiable, so `x₁ := true`.
* Two calls were made, and `(x₀, x₁) = (false, true)` satisfies `φ`.

If the decider answers in `(s+1)^2` steps on size `s`, the search costs at
most `2 · (5+1)^2 = 72` query steps, since `size φ = 5`.

**Converse.** If `S` returns a satisfying assignment of every satisfiable
CNF, then "evaluate `S φ` on `φ`" decides SAT exactly
(`search_gives_decider`). Evaluation is linear time, so polynomial search
gives polynomial decision.

**Why this is insufficient alone.** `satDec_correct` exhibits an exact
decider outright, but it has exponential cost (Idea 21, `leaves_eq`). The
obligation is therefore stated about machines and their `Run` step counts,
where it is `InP SAT` (`inP_sat_of_exactPolyDecider`) and, with `SATHard`,
gives `PEqualsNP` (`pEqualsNP_of_exactPolyDecider`). Polynomial-time machine
decidability is a real restriction (`exists_not_polyDec`). The
self-reduction moves the difficulty from search to decision but does not
reduce it.

## 5. Known results and literature

* S. A. Cook, "The complexity of theorem-proving procedures", *STOC* 1971,
  and L. Levin (1973). SAT is NP-complete, so SAT ∈ P iff P = NP.
* The self-reducibility of SAT and the equivalence of search and decision
  for NP-complete problems are standard textbook facts. See for example
  S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press (2009).
* M. Bellare and S. Goldwasser, "The complexity of decision versus
  search", *SIAM Journal on Computing* 23(1) (1994). This paper shows that,
  if deterministic and nondeterministic doubly exponential time differ,
  some NP language has a search problem that does not reduce to its
  decision problem. The reduction proved here is specific to
  self-reducible problems such as SAT.

What is **not** formalized:

* The cost of the search's own bookkeeping (computing restrictions) as a
  machine: `PolySearch` bounds the `Run` steps of the questions only; a single
  machine running the whole search would add a polynomial overhead.
* Cook–Levin. Its NP-hardness half appears only as the named hypothesis
  `SATHard` of `pEqualsNP_of_exactPolyDecider`.
* The Bellare–Goldwasser separation.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** `decision_to_search` (in the shared machine model) and
  `search_gives_decider`, combined with Cook–Levin (the hypothesis
  `SATHard`, not mechanised), show that P = NP iff SAT search is in
  polynomial time. The reduction costs one
  decider call per variable, with polynomial overhead. This is as strong as
  it gets. Any polynomial SAT decider, even one found non-constructively,
  can be turned into a polynomial witness finder once it is written down.
  Levin's universal search even gives an explicit witness finder that runs
  in polynomial time on satisfiable inputs if P = NP, although it need not
  halt quickly on unsatisfiable inputs.
* **Remaining obligation.** `ExactPolyDecider := PolyDec SAT`, a statement
  about `Complexity.Machine` deciders and `Run` step counts. It is `InP SAT`
  (`inP_sat_of_exactPolyDecider`) and gives `PEqualsNP` under `SATHard`
  (`pEqualsNP_of_exactPolyDecider`); the converse holds under `SATInNP`
  (`inP_sat_of_pEqualsNP` in the shared layer). It is neither weaker nor
  stronger than P = NP, and the self-reduction adds nothing toward proving
  it.
* **Toward P ≠ NP.** By the converse, a superpolynomial lower bound for
  SAT search gives one for SAT decision. Again this is only a
  reformulation: it is P ≠ NP itself.
* **Barriers.** Self-reducibility relativizes. The same argument works
  relative to any oracle. So it cannot, by itself, resolve P vs NP
  (Baker–Gill–Solovay, *SIAM J. Comput.* 1975).

## 7. Failure modes this idea catches

* **Family 15 (verification, search, construction, certificates).** Claims
  that "deciding SAT fast still leaves finding solutions hard", or the
  reverse, are false for SAT (`decision_to_search`,
  `search_gives_decider`). Claims of this kind for general NP relations
  need care (Bellare–Goldwasser).
* **Family 12 (circular reasoning).** A "polynomial decider" whose cost is
  measured in a model that charges nothing for the hard step. The schema
  `ExactPolyDeciderFor` holds for the cost model that charges nothing, which
  is why the obligation is stated with `Run` step counts instead.
* **Family 2 (hiding exponential work).** A search procedure that calls a
  subroutine that is itself exponential, such as `satDec`. The call count
  is polynomial, but the cost is not.
* **Family 17 (parameter mistakes).** Counting calls (`length vs`) instead
  of total cost. `searchCost_le` makes the per-call bound explicit.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea22.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea22.v
rm -f proofs/experiments/issue532/rocq/Idea22.vo proofs/experiments/issue532/rocq/Idea22.vok \
      proofs/experiments/issue532/rocq/Idea22.vos proofs/experiments/issue532/rocq/Idea22.glob \
      proofs/experiments/issue532/rocq/.Idea22.aux
```

Both commands print nothing on success.
