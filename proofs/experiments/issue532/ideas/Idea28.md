# Idea 28 — Definitional extensions (Tseitin transformation)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Introducing a fresh variable `y` with the definition `y ↔ (x ∧ z)` (or `¬x`, or `x ∨ z`) preserves satisfiability. Applied once per gate, this is the Tseitin transformation, and the files prove it correct for every propositional formula: it is equisatisfiable, has at most `3 · #gates + 1` clauses, at most 3 literals per clause, and exactly one new variable per gate. It is a *hardness-preserving* reduction (formula/circuit-SAT ≤ 3-SAT), so it cannot make instances easier. Adding definitions inside proofs gives extended resolution, and superpolynomial lower bounds for it are a famous open problem, stated here as the obligation `ERSuperpolyLowerBound`.

## 1. The idea at full strength

The hope in the direction **P = NP**: auxiliary variables change the "geometry" of a formula. A well-chosen set of definitions might expose structure (small width, few conflicts, a short refutation) that a simple solver then exploits. Research-log item 28 phrases the obligation as "show that the extended encoding makes exact solving polynomial, including encoding and decoding cost".

The hope in the direction **P ≠ NP** (via NP ≠ coNP): show that even with arbitrary definitions, some unsatisfiable formulas have no short refutation. This would be a lower bound for extended resolution / Extended Frege.

Issue #532 places this at Part I, item 5 ("Model choice matters": definitions are "reuse" in the proof model) and at Part I, item 6 ("Different physical models ... may change invariants"). Part II, Phase 1 asks to formalize "Boolean circuits (size + depth)" and prove equivalences "explicitly, not by folklore". The circuit-to-CNF equivalence proved here is exactly such a folklore step.

## 2. Precise mathematical formulation

Formulas are `Formula ::= var i | neg f | conj f g | disj f g`, with `eval a f`, `gates f` (number of `neg/conj/disj` nodes) and `bound f` (1 + largest input index). CNFs are as in Ideas 25–27.

`tseitin f n` returns `(out, cls, next)`. The fresh variables are `n, n+1, …`, one per gate, allocated after the children. `out` carries the value of `f`, `cls` are the gate clauses, and `next` is the first unused variable. The gate clauses are:

| gate | clauses |
| --- | --- |
| `y ↔ ¬x` | `(y ∨ x)`, `(¬y ∨ ¬x)` |
| `y ↔ x ∧ z` | `(¬y ∨ x)`, `(¬y ∨ z)`, `(y ∨ ¬x ∨ ¬z)` |
| `y ↔ x ∨ z` | `(y ∨ ¬x)`, `(y ∨ ¬z)`, `(¬y ∨ x ∨ z)` |

`tseitinCNF f = cls (tseitin f (bound f)) ++ [[out]]`.

Extended resolution (`ERDerives φ π`) starts from `π = φ` and repeatedly adds either:

* a resolvent (with weakening) of two present clauses on a variable `v`; or
* the three extension clauses `defGate y l₁ l₂` for `y ↔ (l₁ ∧ l₂)`, where `l₁, l₂` are literals and `y` occurs nowhere yet and differs from their variables.

A refutation is a derivation containing `[]`. Its length is `π.length`, and `size φ` counts clauses plus literal occurrences.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `negGate_iff`, `andGate_iff`, `orGate_iff` | The gate clauses hold iff `y` equals the gate value | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `define_and_sat_iff` | For every CNF `φ` and fresh `y` (`y ∉ vars φ`, `y ≠ x, z`): `Sat (φ ++ andGate y x z) ↔ Sat φ` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `Formula.eval_congr` (Rocq `formula_eval_congr`) | Formula evaluation depends only on variables `< bound f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_next` | `next (tseitin f n) = n + gates f` — exactly one fresh variable per gate | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_length` | `|cls (tseitin f n)| ≤ 3 · gates f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_width` | Every gate clause has at most 3 literals | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_sound` | Any model of the gate clauses gives `out` the value `eval b f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_scope` | If `bound f ≤ n`: `out < next` and all clause variables are `< next` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `extend_below` | The canonical extension leaves variables `< n` unchanged | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `extend_correct` | The canonical extension satisfies the gate clauses and `out ↦ eval a f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitin_equisat` | `Satisfiable (tseitinCNF f) ↔ ∃ a, eval a f = true`, for every `f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitinCNF_length` | `|tseitinCNF f| ≤ 3 · gates f + 1` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitinCNF_width` | `tseitinCNF f` is a 3-CNF | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `tseitinCNF_vars` | All variables of `tseitinCNF f` are `< bound f + gates f` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `transfer` | A decider correct on all 3-CNFs, composed with `tseitinCNF`, decides formula-SAT | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `defGate_iff`, `er_sat`, `er_sound` | Extended resolution is sound: a derivation containing `[]` refutes `φ` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `ERSuperpolyLowerBound` (def) | The open obligation: unsatisfiable family, no ER refutation of length `≤ c · (size+1)^k` for any `c, k` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `obligation_excludes_poly_bound` | A witness of the obligation rules out every fixed polynomial bound on refutation length | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |

No axioms are used, and there is no `sorry`/`Admitted`. In Rocq the `ERDerives` constructors are named `er_start`, `er_res`, `er_ext`.

## 4. Complete argument

**Soundness (`tseitin_sound`).** By induction on `f`. For `neg f`, the clauses contain `negGate y (out f)` and, by `negGate_iff`, `b y = ¬ b (out f)`. The induction hypothesis gives `b (out f) = eval b f`. `conj` and `disj` are the same with `andGate_iff` and `orGate_iff`. So a model `b` of `tseitinCNF f` has `b out = true` (from the unit clause) and `b out = eval b f`, hence `eval b f = true`.

**Completeness (`extend_correct`).** Given `a`, the assignment `extend f n a` sets each gate variable, in allocation order, to the value of its subformula under `a`. The bookkeeping uses three invariants, each proved by induction:

1. `next = n + gates f` (`tseitin_next`), so later gates get strictly larger variables.
2. When `bound f ≤ n`, `out` and all variables in `cls` lie below `next` (`tseitin_scope`).
3. `extend f n a` agrees with `a` below `n` (`extend_below`).

For `conj f g`, let `r = tseitin f n`, `s = tseitin g r.next`, `b₁ = extend f n a`, `b₂ = extend g r.next b₁`, and `b = b₂[s.next := eval a f ∧ eval a g]`.

* By (3), `b₂` agrees with `b₁` below `r.next`, which contains every variable of `r.cls` and `r.out` by (2).
* By (3) again, `b₁` agrees with `a` below `n ≥ bound g`, so `eval b₁ g = eval a g` (`Formula.eval_congr`).
* The final update at `s.next` does not touch anything below `s.next`, by (1) and (2).

Hence `b` satisfies `r.cls`, `s.cls` and the gate clause, and `b s.next = eval a (conj f g)` (`extend_binary`).

**Size.** Each gate adds at most 3 clauses and exactly one variable, and each clause has at most 3 literals. With the output unit this gives `≤ 3·gates + 1` clauses (`tseitinCNF_length`), all of width ≤ 3 (`tseitinCNF_width`), over the variables `< bound f + gates f` (`tseitinCNF_vars`).

**Transfer.** If `D` decides satisfiability of every CNF of width ≤ 3, then `D ∘ tseitinCNF` decides satisfiability of every formula (`transfer`). This is the direction "3-SAT is at least as hard as formula-SAT". It does *not* go the other way. Nothing about `tseitinCNF f` is easier than `f`: it is the standard hardness reduction.

**Single definition (`define_and_sat_iff`).** Forward: drop the extra clauses. Backward: extend the model by `y := a x ∧ a z`; `φ` is unchanged because `y ∉ vars φ`. The same argument, with literals `l₁, l₂`, gives the extension step of `er_sat`. The resolution step is sound by case analysis on `b v`: the satisfying literal of the clause that is not killed by `b v` survives into the resolvent.

**Worked numbers.** `(x₀ ∧ x₁) ∨ ¬x₂` has 3 gates, so it gets fresh variables 3, 4, 5 and at most 3 + 2 + 3 + 1 = 9 clauses. A circuit with 10⁶ gates yields at most 3,000,001 clauses of width ≤ 3.

**Why this is insufficient alone.** As a P = NP route, the extended encoding must make solving easier, but `transfer` shows it is a many-one reduction *into* 3-SAT. Solving the image in polynomial time is exactly as hard as solving formula-SAT, which is NP-complete. Definitions can help specific proofs. Cook (1976) gave polynomial-size extended-resolution proofs of the pigeonhole principle, which is exponentially hard for resolution by Haken (Idea 27). But finding good definitions is itself the search problem.

## 5. Known results and literature

* G. S. Tseitin, "On the complexity of derivation in propositional calculus", in *Studies in Constructive Mathematics and Mathematical Logic*, Part II, 1968 (English translation 1970). Introduces the extension rule and the definitional CNF encoding, and proves lower bounds for regular resolution.
* S. A. Cook, "The complexity of theorem-proving procedures", STOC 1971; R. M. Karp, "Reducibility among combinatorial problems", 1972. SAT and 3-SAT are NP-complete. The Tseitin encoding is the usual circuit-SAT ≤ 3-SAT step.
* S. A. Cook, "A short proof of the pigeon hole principle using extended resolution", *SIGACT News* 8(4), 1976.
* S. A. Cook and R. A. Reckhow, "The relative efficiency of propositional proof systems", *Journal of Symbolic Logic* 44(1), 1979. NP = coNP iff some propositional proof system is polynomially bounded. They also show that extended resolution and Extended Frege are polynomially equivalent.
* A. Haken, "The intractability of resolution", *Theoretical Computer Science* 39, 1985. Contrast with Cook 1976.
* J. Krajíček and P. Pudlák, "Some consequences of cryptographical conjectures for S¹₂ and EF", *Information and Computation* 140, 1998. Under cryptographic assumptions, Extended Frege lacks feasible interpolation, so the standard route to lower bounds for weaker systems does not apply.
* J. Krajíček, *Bounded Arithmetic, Propositional Logic, and Complexity Theory*, Cambridge University Press, 1995. Superpolynomial lower bounds for Frege and Extended Frege are open.

None of these theorems are formalized here. The files formalize the Tseitin transformation (with correctness, size and width), the definition-extension lemma, a definition of extended resolution with its soundness, and the lower-bound obligation as a `Prop`.

## 6. How far the idea can be pushed toward P vs NP

**Toward P = NP.** The route requires a polynomial-time procedure that, given `φ`, finds definitions making `φ` solvable or refutable in polynomial time. For unsatisfiable `φ`, the output would be a short ER refutation. Such a procedure would make ER polynomially bounded, and by Cook–Reckhow that implies NP = coNP. This is not known to follow from P = NP alone. Conversely, P = NP gives short refutations in *some* proof system, not necessarily ER. The route is therefore at least as strong as proving that ER is polynomially bounded, and it is blocked by any ER lower bound.

**Toward P ≠ NP.** The open obligation is

```
def ERSuperpolyLowerBound (family : Nat → CNF) : Prop :=
  (∀ n, ¬ Satisfiable (family n)) ∧
  ∀ c k, ∃ n, ∀ π, ERDerives (family n) π → [] ∈ π →
    c * (size (family n) + 1) ^ k < π.length
```

* NP ≠ coNP implies that such a family exists (Cook–Reckhow, contrapositive).
* Its existence would **not** by itself imply NP ≠ coNP or P ≠ NP: it is a lower bound for one proof system.
* No such family is known. Extended Frege is the strongest system of the Cook–Reckhow program in common use, and even for Frege no superpolynomial lower bound is known.

Barriers:

* The known lower-bound techniques for weaker systems (feasible interpolation, width, restrictions) either do not apply to EF or are blocked by cryptographic assumptions (Krajíček–Pudlák).
* EF corresponds to reasoning in the bounded arithmetic `S¹₂`/`PV`, so a lower bound requires independence results for weak arithmetic. Those are themselves open.

## 7. Failure modes this idea catches

* **Reductions in the wrong direction** (error family 4 in [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md)). `transfer` shows that Tseitin maps *into* 3-SAT. Claiming that an encoding "simplifies" a problem because it has width 3 confuses hardness preservation with easiness.
* **Non-fresh definitions** (error family 4). `define_and_sat_iff` needs `y ∉ vars φ`, `y ≠ x`, `y ≠ z`. Reusing a variable breaks equisatisfiability. For example, defining `y := x ∧ z` when `φ` already forces `y = true` and `x = false` makes the result unsatisfiable.
* **Encoding-size mistakes** (error family 17). The encoding is linear (`≤ 3·gates + 1` clauses), but only because each gate gets its own variable. Distributing `∨` over `∧` instead can be exponential.
* **Proof-system lower bounds mistaken for P ≠ NP** (error family 5, a different problem). Resolution lower bounds (Idea 27) do not carry over to ER, and ER lower bounds would not prove P ≠ NP.
* **Folklore reliance** (error family 11). The size and freshness bookkeeping is proved, not assumed.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea28.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea28.v
```

Both commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
