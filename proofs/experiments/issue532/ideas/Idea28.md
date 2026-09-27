# Idea 28 — Definitional extensions (Tseitin transformation)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

Introducing a fresh variable `y` with the definition `y ↔ (x ∧ z)` (or `¬x`, or `x ∨ z`) preserves satisfiability. Applied once per gate, this is the Tseitin transformation, and the files prove it correct for every propositional formula: it is equisatisfiable, has at most `3 · #gates + 1` clauses, at most 3 literals per clause, and exactly one new variable per gate. It is a *hardness-preserving* reduction (formula/circuit-SAT ≤ 3-SAT), so it cannot make instances easier. Adding definitions inside proofs gives extended resolution, and superpolynomial lower bounds for it are a famous open problem. It is stated here as the open obligation `ERNotPolyBounded` over the shared machine language `Issue532.Machines.SAT`: extended resolution is not polynomially bounded on the CNFs that SAT rejects. The files prove that this obligation implies the same lower bound for resolution (`resNotPolyBounded_of_er`), and that NP ≠ coNP implies the obligation given the Cook–Reckhow theorem as a named hypothesis (`erNotPolyBounded_of_npNeCoNP`). The obligation is not known to imply NP ≠ coNP or P ≠ NP, so no conditional theorem to `PNotEqualsNP` is claimed.

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

**Tie to the shared machine model.** `toMachineCNF` translates these CNFs into `Issue532.Machines.CNF` and preserves satisfiability (`satisfiable_toMachine`). `satWord φ` is the encoded word, and `sat_satWord` gives `SAT (satWord φ) = true ↔ Satisfiable φ`.

**Schemas** (parameterised shapes, not obligations):

* `ERSuperpolyLowerBoundFor family`: `family` is unsatisfiable, and for every `c, k` some member has no ER refutation of length `≤ c · (size + 1)^k`.
* `NotPolyBoundedFor D`: the refutation system `D` is not polynomially bounded on the CNFs that SAT rejects.

**Open obligation** (fixed, no free parameters):

```
def ERNotPolyBounded : Prop :=
  ∀ c k : Nat, ∃ φ : CNF, SAT (satWord φ) = false ∧
    ∀ π, ERDerives φ π → [] ∈ π → c * (size φ + 1) ^ k < π.length
```

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
| `ERSuperpolyLowerBoundFor` (def) | Schema: unsatisfiable family, no ER refutation of length `≤ c · (size+1)^k` for any `c, k` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `obligation_excludes_poly_bound` | A witness of the obligation rules out every fixed polynomial bound on refutation length | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `toMachineCNF`, `satisfiable_toMachine` | Translation into `Issue532.Machines.CNF` preserves satisfiability | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `satWord`, `sat_satWord`, `sat_satWord_false` | `SAT (satWord φ) = true ↔ Satisfiable φ` (and the `false` form) | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `NotPolyBoundedFor` (def) | Schema: a refutation system `D` is not polynomially bounded on the CNFs that SAT rejects | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `ERNotPolyBounded` (def) | Open obligation: extended resolution is not polynomially bounded on the CNFs that `SAT` rejects | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `erNotPolyBounded_iff_for` | `ERNotPolyBounded ↔ NotPolyBoundedFor ERDerives` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `ERPolyBounded` (def), `erNotPolyBounded_iff` | `ERNotPolyBounded ↔ ¬ ERPolyBounded` (Rocq: given excluded middle; the forward direction without it is `erNotPolyBounded_not_polyBounded`) | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `erNotPolyBounded_iff_family` | The obligation holds iff some family meets `ERSuperpolyLowerBoundFor` (Rocq: given a choice principle; the backward direction without it is `erNotPolyBounded_of_family`) | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `ResDerives`, `erDerives_of_res` | Resolution derivations are extended-resolution derivations | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `ResNotPolyBounded` (def) | Resolution is not polynomially bounded (known, Haken 1985; not mechanised) | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `resNotPolyBounded_of_er` | Conditional theorem: `ERNotPolyBounded → ResNotPolyBounded` (the honest conclusion) | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `CookReckhowER` (def) | Named known theorem (Cook–Reckhow 1979): `¬ NPEqualsCoNP → ERNotPolyBounded` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `erNotPolyBounded_of_npNeCoNP` | Given `CookReckhowER`, NP ≠ coNP implies the obligation | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `contra`, `sat_contra` | `x₀ ∧ ¬x₀` is rejected by `SAT` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `noRules_notPolyBounded` | Non-vacuity: the schema `NotPolyBoundedFor` holds for the system with no rules | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `oneStep_not_notPolyBounded` | Non-vacuity: the schema fails for a system deriving `[]` in one step | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |
| `emptyClause_not_superpoly` | Non-vacuity: `ERSuperpolyLowerBoundFor` fails for the family `fun _ => [[]]` | [Idea28.lean](../lean/Idea28.lean) | [Idea28.v](../rocq/Idea28.v) |

No axioms are used, and there is no `sorry`/`Admitted`.

Rocq-specific differences:

- Constructor names: the `ERDerives` constructors are `er_start`, `er_res` and `er_ext`, and the `ResDerives` constructors are `res_start` and `res_res`.
- Shadowed CNF syntax: the file keeps its own CNF syntax, which shadows the syntax of `Machines.v`. The machine versions are written qualified, for example `Machines.evalCNF`.
- `erNotPolyBounded_iff`: Lean proves the backward direction with `Classical.byContradiction`. In Rocq the theorem instead takes excluded middle `(forall P : Prop, P \/ ~ P)` as an explicit premise.
- `erNotPolyBounded_iff_family`: Lean builds the family with `Classical.choose`. In Rocq the theorem instead takes an explicit premise: a choice principle for `nat`-indexed families of CNFs, `forall P : nat -> CNF -> Prop, (forall n, exists phi, P n phi) -> exists f, forall n, P n (f n)`.
- Directions without premises: for both theorems above, the direction that needs no premise is also proved on its own, as `erNotPolyBounded_not_polyBounded` and `erNotPolyBounded_of_family`.
- `sat_contra`: proved by `vm_compute` instead of `decide`.

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
* S. A. Cook and R. A. Reckhow, "The relative efficiency of propositional proof systems", *Journal of Symbolic Logic* 44(1), 1979. NP = coNP iff some propositional proof system is polynomially bounded. This paper also introduces Extended Frege. Extended resolution and Extended Frege are polynomially equivalent (see Krajíček 1995 below).
* A. Haken, "The intractability of resolution", *Theoretical Computer Science* 39, 1985. Contrast with Cook 1976.
* J. Krajíček and P. Pudlák, "Some consequences of cryptographical conjectures for S¹₂ and EF", *Information and Computation* 140, 1998. Under cryptographic assumptions, Extended Frege lacks feasible interpolation, so the standard route to lower bounds for weaker systems does not apply.
* J. Krajíček, *Bounded Arithmetic, Propositional Logic, and Complexity Theory*, Cambridge University Press, 1995. Superpolynomial lower bounds for Frege and Extended Frege are open.

None of these theorems are formalized here. The files formalize the Tseitin transformation (with correctness, size and width), the definition-extension lemma, a definition of extended resolution with its soundness, and the lower-bound obligation as a `Prop`.

## 6. How far the idea can be pushed toward P vs NP

**Toward P = NP.** The route requires a polynomial-time procedure that, given `φ`, finds definitions making `φ` solvable or refutable in polynomial time. For unsatisfiable `φ`, the output would be a short ER refutation. Such a procedure would make ER polynomially bounded, and by Cook–Reckhow that implies NP = coNP. This is not known to follow from P = NP alone. Conversely, P = NP gives short refutations in *some* proof system, not necessarily ER. The route is therefore at least as strong as proving that ER is polynomially bounded, and it is blocked by any ER lower bound.

**Toward P ≠ NP.** The open obligation is

```
def ERNotPolyBounded : Prop :=
  ∀ c k : Nat, ∃ φ : CNF, SAT (satWord φ) = false ∧
    ∀ π, ERDerives φ π → [] ∈ π → c * (size φ + 1) ^ k < π.length
```

Here `SAT` is `Issue532.Machines.SAT` and `satWord` is the machine encoding of the CNF. The formal results are:

* `erNotPolyBounded_iff_family`: the obligation is equivalent to the existence of a family meeting the schema `ERSuperpolyLowerBoundFor`.
* `resNotPolyBounded_of_er`: the obligation implies the same statement for resolution. This is the honest conclusion. A lower bound for one proof system transfers only to the systems that it simulates.
* `erNotPolyBounded_of_npNeCoNP`: given the named known theorem `CookReckhowER` (Cook–Reckhow 1979), NP ≠ coNP implies the obligation.
* The converse is not known. The obligation would **not** by itself imply NP ≠ coNP or P ≠ NP, because it is a lower bound for one proof system. For this reason the file proves no conditional theorem to `PNotEqualsNP`.
* Non-vacuity: `noRules_notPolyBounded` shows that `NotPolyBoundedFor` holds for a trivial system, and `oneStep_not_notPolyBounded` shows that it fails for an unsound one. `emptyClause_not_superpoly` shows that the family schema fails for the empty-clause family.
* No witness of the obligation is known. Extended Frege is the strongest system of the Cook–Reckhow program in common use, and even for Frege no superpolynomial lower bound is known.

Barriers:

* The known lower-bound techniques for weaker systems (feasible interpolation, width, restrictions) either do not apply to EF or are blocked by cryptographic assumptions (Krajíček–Pudlák).
* EF corresponds to reasoning in the bounded arithmetic `PV` (equivalently, for the relevant statements, `S¹₂`): statements provable there have polynomial-size EF proofs of their propositional translations. So an EF lower bound for such translations would yield independence results for these weak theories, and those are themselves open.

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
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Machines.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea28.v
```

All commands print nothing on success. Remove the generated Rocq artifacts (`.vo`, `.vok`, `.vos`, `.glob`, `.aux`) afterwards.
