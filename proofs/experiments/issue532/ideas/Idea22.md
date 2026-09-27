# Idea 22 — Decision-to-search self-reduction

**Verdict:** Correct tool, insufficient alone (general theorem proved)

SAT is self-reducible. From any exact decision procedure, fixing the
variables one at a time gives a satisfying assignment of every satisfiable
CNF, with exactly one decider call per variable. The files prove this for
every CNF and every decider. They also prove the polynomial cost transfer:
a polynomially bounded decider gives polynomially bounded search. So finding
a witness is no harder than deciding, and P = NP is equivalent to
polynomial-time SAT search. The tool does not produce a fast decider. The
remaining obligation `ExactPolyDecider` is exactly the P = NP direction.

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
* A cost model `Cost : (CNF → Bool) → CNF → Nat` gives the cost of running
  a decider on an input. The open obligation is
  `ExactPolyDecider Cost := ∃ dec c k, Decides dec ∧ ∀ ψ, Cost dec ψ ≤ c (size ψ + 1)^k`.
  With an honest cost model, such as Turing machine steps on a standard
  encoding, this is SAT ∈ P, which is equivalent to P = NP by Cook–Levin.

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
| `ExactPolyDecider` (def) | Open obligation: an exact decider of polynomially bounded cost in the given cost model. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `decision_to_search` | `ExactPolyDecider Cost → PolySearch Cost`. The search is correct on every satisfiable CNF and its total query cost is at most `c (size φ + 1)^(k+1)`. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `satDec_correct` | The splitting decider of Idea 21 on `varsOf φ` is an exact decider, unconditionally. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `zero_cost_trivial` | In the cost model that charges 0, `ExactPolyDecider` holds. So the obligation has content only for an honest cost model. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |
| `unconditional_search` | With `satDec`, the self-reduction finds a satisfying assignment of every satisfiable CNF. | [Idea22.lean](../lean/Idea22.lean) | [Idea22.v](../rocq/Idea22.v) |

The two files state the same theorems. Rocq uses `fst`/`snd` where Lean
uses `.1`/`.2`.

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
decider outright, but it has exponential cost (Idea 21, `leaves_eq`).
`zero_cost_trivial` shows that if cost is not tied to a machine, the
obligation is trivially "satisfied". This is exactly the family 12
situation: the whole difficulty is hidden in the choice of cost model. The
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
  search", *SIAM Journal on Computing* 23(1) (1994). This paper shows that
  search does not reduce to decision for all NP languages under
  cryptographic assumptions. The reduction proved here is specific to
  self-reducible problems such as SAT.

What is **not** formalized:

* Turing machines or any concrete cost model.
* Cook–Levin, and hence the equivalence of `ExactPolyDecider` (for an
  honest model) with P = NP.
* The Bellare–Goldwasser separation.

## 6. How far the idea can be pushed toward P vs NP

* **Full potential.** `decision_to_search` and `search_gives_decider` show
  that P = NP iff SAT search is in polynomial time. The reduction costs one
  decider call per variable, with polynomial overhead. This is as strong as
  it gets. Any polynomial SAT decider, even one found non-constructively,
  can be turned into a polynomial witness finder once it is written down.
  With Levin's universal search even the "written down" step disappears.
* **Remaining obligation.** `ExactPolyDecider Cost` for an honest cost
  model. This is SAT ∈ P, which is equivalent to P = NP. It is neither
  weaker nor stronger, and the self-reduction adds nothing toward proving
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
  measured in a model that charges nothing for the hard step. By
  `zero_cost_trivial` such a model makes the obligation trivially true.
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
