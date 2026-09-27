# Idea 01 — Exact SAT algorithm (brute force as the baseline for a uniform SAT decider)

**Verdict:** Developed to an open obligation (conditional theorem proved)

The uniform brute-force decider for CNF-SAT is proved sound and complete for
every formula, and its cost is proved to be exactly `2^n` formula evaluations
on every unsatisfiable formula with `n` variables, so brute force is refuted as
a polynomial-time algorithm by a general theorem. The route "find a uniform
polynomial-time SAT decider" is stated in the repository's shared machine
model as the open obligation `PolySATDecider := InP SAT`, where `SAT` is the
language of encoded satisfiable CNFs. The conditional theorems proved are:
`PolySATDecider → PEqualsNP` under the named hypothesis `SATHard`,
`PolySATDecider ↔ PEqualsNP` under `CookLevin`, and any machine that meets the
obligation computes exactly the brute-force answer on every formula. The
Cook–Levin theorem is not mechanised; it enters only as these hypotheses.

## 1. The idea at full strength

The most ambitious form of the idea is the direct P = NP route. Write one
algorithm `A` that takes any CNF formula `φ`, halts after at most `p(|φ|)`
steps for a fixed polynomial `p`, and outputs `true` exactly when `φ` is
satisfiable. Since CNF-SAT is NP-complete, such an `A` would give P = NP.

In issue #532 the idea comes from Part I item 1 ("Hardness arises from
**combinatorial freedom**", "Restricting geometry, connectivity, or structure
collapses hardness") and Part II Phase 1 ("Formalize the baseline world
(ground truth)", "Complexity classes … with explicit encodings, explicit
resource bounds"). Brute force is the ground truth. Any faster algorithm must
agree with it on every input, and any claimed polynomial algorithm must be
compared with its `2^n` cost.

## 2. Precise mathematical formulation

* **Syntax.** A literal is a pair `(var : Nat, pos : Bool)`. A clause is a list
  of literals, and a CNF is a list of clauses.
* **Semantics.** An assignment is `a : Nat → Bool`. `evalLit a (v,p) = (a v == p)`.
  A clause is true iff some literal is true (the empty clause is false). A CNF
  is true iff every clause is true (the empty CNF is true).
  `Satisfiable φ :⇔ ∃ a, evalCNF a φ = true`.
* **Variables.** `VarsBelow n φ :⇔` every variable index in `φ` is `< n`.
  `numVars φ` = 1 + the largest variable index (0 if there is none).
* **Enumeration.** `allAssignments 0 = [[]]` and
  `allAssignments (n+1) = map (false :: ·) (allAssignments n) ++ map (true :: ·) (allAssignments n)`.
  `toAssign v i` is bit `i` of `v`, and `false` past the end.
* **Brute force.** `bruteForce n φ = any v ∈ allAssignments n, evalCNF (toAssign v) φ`.
* **Cost of brute force.** `bruteForceCost n φ` is the number of formula
  evaluations made by the left-to-right search. The search stops at the first
  satisfying vector.
* **Input encoding.** `encodeCNF` uses two-bit tokens: `11` is a unary tick of
  the variable index, `0p` ends a literal with polarity `p`, and `10` ends a
  clause. Unary variable indices are harmless for NP-completeness, since
  variables can be renamed to `0 … m−1` in polynomial time. They also make
  `numVars φ ≤ |encodeCNF φ|` hold.
* **Machine model.** The shared model of
  `proofs/complexity/lean/Complexity.lean` and
  `proofs/experiments/issue532/lean/Machines.lean`. A deterministic
  single-tape machine has a finite instruction table
  (`List (List Instruction)`). One instruction is executed per step.
  `Run M c t b` means that from configuration `c`, `M` halts after `t` steps
  with answer `b`. Polynomials are `c·(n+1)^d`. `InP L` holds when one machine
  decides `L` on every word within one polynomial bound (`polyDec_iff_inP`
  restates it with `DecidesWithin`). The CNF syntax, `bruteForce`,
  `encodeCNF`/`decode` and the language
  `SAT w := bruteForce (numVars (decode w)) (decode w)` are defined in that
  shared layer, with `sat_encode : SAT (encodeCNF φ) = true ↔ Satisfiable φ`.
* **The open claim needed for P = NP.**

  ```lean
  def PolySATDecider : Prop := InP SAT
  ```

  Unfolded, a single machine and a single polynomial must decide `SAT` on
  every input word within the bound. On encodings of formulas this is
  `∃ M p, ∀ φ, ∃ t b, t ≤ p.eval |encodeCNF φ| ∧ Run M (initial (encodeCNF φ)) t b ∧
  (b = true ↔ Satisfiable φ)` (`inP_sat_on_encodings`).
* **Known theorems used only as named hypotheses** (shared layer, not
  mechanised): `SATInNP := InNP SAT`, `SATHard := NPHard SAT` (every NP
  language `PolyReduces` to `SAT`), and `CookLevin := SATInNP ∧ SATHard`.

Why a machine model is needed: core Lean functions have no running time.
`fun φ => bruteForce (numVars φ) φ` is already a correct Lean function
`CNF → Bool`. The statement "there is a correct Lean function" is therefore
true and says nothing about efficiency. Any honest efficiency claim has to name
a cost model with unit-cost steps of bounded power, as the finite table does.
`polySATDecider_not_trivial` checks that the predicate `InP` of the
obligation is not satisfied by every language.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `evalCNF_congr` | If `a` and `b` agree below `n` and `VarsBelow n φ`, then `evalCNF a φ = evalCNF b φ`. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `length_allAssignments` | `(allAssignments n).length = 2^n` for all `n`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `mem_allAssignments_iff` | `v ∈ allAssignments n ↔ v.length = n`. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `nodup_allAssignments` | `allAssignments n` has no repetitions. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `brute_force_sound` | `bruteForce n φ = true → Satisfiable φ`, for all `n`, `φ`. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `brute_force_complete` | `VarsBelow n φ → Satisfiable φ → bruteForce n φ = true`. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `bruteForce_correct` | `bruteForce (numVars φ) φ = true ↔ Satisfiable φ` for every CNF. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `bruteForceCost_le` | `bruteForceCost n φ ≤ 2^n`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `bruteForceCost_unsat` | `¬Satisfiable φ → bruteForceCost n φ = 2^n` (for every `n`). | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `hardFamily_unsat` | `hardFamily n = [x0] ∧ [¬x0] ∧ ⋀_{i<n}(x_i ∨ ¬x_i)` is unsatisfiable for every `n`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `hardFamily_cost` | For `n ≥ 1`: `numVars (hardFamily n) = n`, it is unsatisfiable, and brute force spends exactly `2^n` evaluations on it. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `decode_encode`, `encode_injective` | `decode (encodeCNF φ) = φ`, so the encoding is injective. | [Machines.lean](../lean/Machines.lean) | [Idea01.v](../rocq/Idea01.v) |
| `numVars_le_encodingLength` | `numVars φ ≤ (encodeCNF φ).length`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `bruteForceCost_le_exp_size` | `bruteForceCost (numVars φ) φ ≤ 2^{(encodeCNF φ).length}`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `PolySATDecider` (definition) | The open obligation of Section 2, `InP SAT`. It is not proved and not assumed. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `polySATDecider_iff_polyDec` | `PolySATDecider ↔ PolyDec SAT` (explicit machine and polynomial). | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |
| `pEqualsNP_of_polySATDecider` | `SATHard → PolySATDecider → PEqualsNP`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |
| `polySATDecider_of_pEqualsNP` | `SATInNP → PEqualsNP → PolySATDecider`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |
| `polySATDecider_iff` | `CookLevin → (PolySATDecider ↔ PEqualsNP)`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |
| `pNotEqualsNP_of_not_polySATDecider` | `SATInNP → ¬PolySATDecider → PNotEqualsNP`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |
| `polySAT_agrees_with_bruteForce` | `PolySATDecider →` there are `M` and `p` such that for every `φ` the machine halts within `p(|enc φ|)` steps with answer `bruteForce (numVars φ) φ`. | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) |
| `polySATDecider_not_trivial` | Non-vacuity: `¬ ∀ L : Language, InP L` (the shared diagonal language `Diag` is not in P). | [Idea01.lean](../lean/Idea01.lean) | [Idea01.v](../rocq/Idea01.v) (planned, same name) |

Rows whose Lean link is `Machines.lean` are proved once in the shared layer
and used here; `Idea01.lean` imports it.

Not machine-checked: the Cook–Levin theorem (it appears only as the named
hypotheses `SATHard`, `SATInNP`, `CookLevin`), any lower bound for machines
other than brute force, and the running time of brute force on the machine
model. The cost proved here counts formula evaluations, not machine steps.
The Rocq file still states the obligation over its own copy of the machine
model; porting it to the shared Rocq layer is pending.

## 4. Complete argument

**Enumeration.** By induction on `n`: `allAssignments 0 = [[]]` has one element.
The list for `n+1` is two images of the list for `n`, so its length is
`2·2^n = 2^{n+1}`. A vector `b :: v` lies in the list for `n+1` iff `v` lies in
the list for `n`. Induction on `n` then gives `v ∈ allAssignments n ↔ |v| = n`.
There are no duplicates because `cons b` is injective and the two halves differ
in their head bit.

**Soundness.** If some listed `v` satisfies `φ`, then `toAssign v` is a
satisfying assignment.

**Completeness.** Let `a` satisfy `φ` and let all variables of `φ` be `< n`.
Let `prefixOf a n = [a 0, …, a (n−1)]`. It has length `n`, so it is listed, and
`toAssign (prefixOf a n) i = a i` for `i < n`. By `evalCNF_congr` (proved by
induction over clauses and literals), `φ` takes the same value under both
assignments, so the listed vector satisfies `φ`. Since `VarsBelow (numVars φ) φ`
always holds, `bruteForce (numVars φ)` is a *uniform* decider for all CNFs.

**Cost.** `searchCount` adds 1 for each vector it evaluates and stops at the
first success. So it is at most the list length (`2^n`). If no vector
satisfies `φ`, which happens exactly when `φ` is unsatisfiable, every vector is
evaluated and the count is exactly `2^n`. `hardFamily n` is unsatisfiable
because of the clauses `x0` and `¬x0`. It mentions exactly the variables
`0 … n−1` through the tautologies `x_i ∨ ¬x_i`, and `numVars` of the family is
`max(1, n) = n`. Worked numbers: for `n = 20`, brute force evaluates `φ` on
`1 048 576` assignments. For `n = 100` it needs about `1.27·10^30`. The
encoding of `hardFamily n` has length `Θ(n²)` (unary indices), so this is
`2^{Θ(√N)}` in the input length `N`. It is still super-polynomial, and the
general upper bound is `2^N` (`bruteForceCost_le_exp_size`).

**Encoding.** Decoding reads two-bit tokens. The lemma
`decodeAux (ticks v ++ r) k cur = decodeAux r (k+v) cur` and the clause lemma
`decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 []` give
`decode ∘ encodeCNF = id`. Injectivity is needed for the obligation to be
well-posed. If two formulas with different satisfiability had the same
encoding, `PolySATDecider` would be false for a trivial reason.

**Conditional theorems.** `PolySATDecider` is `InP SAT`. If `SAT` is
NP-hard (`SATHard`), every NP language `PolyReduces` to `SAT`, and P is closed
under machine reductions (`inP_of_reduces`, proved in the shared layer by
concatenating the two instruction tables), so every NP language is in P:
`pEqualsNP_of_polySATDecider`. Conversely, if `SAT ∈ NP` (`SATInNP`) and
P = NP, then `SAT ∈ P`. Together, under `CookLevin`, `PolySATDecider ↔ PEqualsNP`
(`polySATDecider_iff`). Now suppose `M` and `p` witness the obligation. For a
formula `φ` let `b` be the machine's answer on `encodeCNF φ`. Then
`b = true ↔ Satisfiable φ ↔ bruteForce (numVars φ) φ = true`, so the two
Booleans are equal (`polySAT_agrees_with_bruteForce`). The machine therefore
reproduces the exponential reference answer within a polynomial budget. This
is the exact shape of any P = NP proof through SAT.

**Non-vacuity.** The obligation is not a consequence of the definitions: the
shared diagonal language `Diag` is not in P (`diag_not_inP`), so `InP` is not
satisfied by every language (`polySATDecider_not_trivial`).

**Why this does not refute the route.** The cost theorems concern brute
force, not all algorithms. No lower bound for arbitrary machines is proved,
and none is known (see Section 6).

## 5. Known results and literature

* S. A. Cook, "The complexity of theorem-proving procedures", *Proc. 3rd ACM
  STOC*, 1971. SAT is NP-complete. (Not formalized here.)
* L. A. Levin, "Universal sequential search problems", *Problemy Peredachi
  Informatsii* 9(3), 1973. Independent NP-completeness, and *universal search*:
  an explicit algorithm that finds satisfying assignments of satisfiable
  formulas within a constant factor (plus verification overhead) of any other
  algorithm's time. (Not formalized.)
* B. Monien and E. Speckenmeyer, "Solving satisfiability in less than 2^n
  steps", *Discrete Applied Mathematics* 10, 1985. Among the first algorithms
  for k-SAT that beat `2^n`. (Not formalized.)
* R. Paturi, P. Pudlák, M. Saks, F. Zane, "An improved exponential-time
  algorithm for k-SAT", FOCS 1998; *J. ACM* 52(3), 2005 (PPSZ). (Not formalized.)
* U. Schöning, "A probabilistic algorithm for k-SAT and constraint
  satisfaction problems", FOCS 1999. A randomized `(4/3)^n·poly(n)` algorithm
  for 3-SAT and `(2(k−1)/k)^n·poly(n)` for k-SAT. (Not formalized.)
* R. Impagliazzo and R. Paturi, "On the complexity of k-SAT", *J. Computer and
  System Sciences* 62(2), 2001. This paper introduced the Exponential Time
  Hypothesis (3-SAT needs time `2^{δn}` for some `δ > 0`), and it is also the
  source of the strong version (SETH: the k-SAT exponent tends to 1; the name
  SETH was fixed in later work of Calabro, Impagliazzo and Paturi). Both are
  conjectures, and each implies P ≠ NP. (Not formalized.)

All of these improve the base of the exponent. None gives a polynomial
algorithm, and none proves that no polynomial algorithm exists.

## 6. How far the idea can be pushed toward P vs NP

At full potential the idea gives the following, all proved:

1. a uniform, correct, total decider for all CNFs (`bruteForce_correct`);
2. an exact cost profile: `2^n` evaluations on every unsatisfiable input
   (`bruteForceCost_unsat`) and at most `2^{input length}` in general;
3. a well-posed statement of the goal in the shared machine model,
   `PolySATDecider := InP SAT`, with a lossless encoding (`decode_encode`);
4. the connection to the separation question: `pEqualsNP_of_polySATDecider`
   (hypothesis `SATHard`), `polySATDecider_iff` (hypothesis `CookLevin`),
   `pNotEqualsNP_of_not_polySATDecider` (hypothesis `SATInNP`);
5. the reduction of any positive solution to "reproduce `bruteForce` in
   polynomially many machine steps" (`polySAT_agrees_with_bruteForce`).

**Remaining obligation:** `PolySATDecider : Prop := InP SAT` (Lean and Rocq
name). The route from it to `PEqualsNP` needs `SATHard`, which is not
mechanised here; with `CookLevin` it is *equivalent* to P = NP, and its
negation is equivalent to P ≠ NP. So the obligation is exactly as hard as the
original problem. It is not an easier intermediate step.

**Barriers and evidence.**

* To *prove* `PolySATDecider` one must give an algorithm. No barrier theorem
  rules this out. The evidence against it is empirical and conjectural: decades
  of algorithm design have only improved the exponent's base (Section 5), and
  ETH/SETH, if true, imply that no subexponential algorithm exists.
* To *refute* `PolySATDecider` (i.e., prove P ≠ NP) one must show a lower bound
  for *all* machines. The relativization (Baker–Gill–Solovay 1975), natural
  proofs (Razborov–Rudich 1997), and algebrization (Aaronson–Wigderson 2009)
  barriers apply to that direction. The cost theorems in this file do not help
  there, because they concern one specific algorithm.
* Levin's universal search shows that if any polynomial-time algorithm finds
  satisfying assignments, then an explicit algorithm is already known that finds
  them in polynomial time on every *satisfiable* input. Universal search alone
  does not certify unsatisfiable inputs within a known bound. What is missing
  is the *proof* of a polynomial bound, not the search procedure itself.

## 7. Failure modes this idea catches

* **Hidden exponential work** ([error family 2](../../../attempts/COMMON_ERRORS.md#2-hiding-exponential-work-in-a-claimed-polynomial-algorithm)):
  a claimed polynomial algorithm that, when unfolded, iterates over
  `allAssignments n` or an equivalent set runs in `2^n` time on unsatisfiable
  inputs (`bruteForceCost_unsat`, `hardFamily_cost`).
* **Incorrectness on some input.** By `polySAT_agrees_with_bruteForce`, a
  claimed fast decider can be tested against `bruteForce` on small formulas. Any
  disagreement refutes the claim. `hardFamily n` gives unsatisfiable test cases
  of every size.
* **Cost-free functions.** A proof that "there is a Lean/Rocq function deciding
  SAT" proves nothing about P vs NP (brute force is one). This is
  [error family 11](../../../attempts/COMMON_ERRORS.md#11-using-undefined-nonstandard-or-incompatible-formal-definitions)
  (nonstandard definitions) and family 17 (encoding-size mistakes). Size must
  be measured on a fixed encoding such as `encodeCNF`.
* **Measuring cost in the wrong parameter** (family 17). Cost in `n` (variables)
  and cost in input length differ polynomially (`numVars_le_encodingLength`).
  An argument that confuses them, for example one using exponentially large
  variable indices, is caught by fixing the encoding.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea01.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea01.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea01.{vo,vok,vos,glob}` and
`.Idea01.aux` files.
