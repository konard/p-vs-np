# Idea 03 — Verifier formalization for CNF-SAT (the NP side)

**Verdict:** Correct tool, insufficient alone (general theorem proved)

For every CNF formula, a certificate verifier is proved sound and complete, with
certificates of length `numVars φ` (never longer than the input). Its cost is
exactly `size φ` literal evaluations (at most half the input length), for every
certificate. This is the verifier half of "CNF-SAT ∈ NP", proved in general,
with cost counted in literal evaluations rather than Turing-machine steps.
It shows that nothing about P vs NP is hidden in *checking*. The whole
difficulty is the quantifier `∃ cert` (and, for unsatisfiability, `∀ cert` over
`2^n` certificates, which costs exactly `2^n · size φ` to check exhaustively).
Removing that quantifier in polynomial time is Idea 01's open obligation
`PolySATDecider`.

## 1. The idea at full strength

Ambitious version: formalize NP precisely through verifiers, as Part II Phase 1
of issue #532 asks ("Complexity classes — Formal definitions of: P, NP, coNP …
All with: explicit encodings, explicit resource bounds"). Then use the verifier
as a lever. If the verifier is simple enough (linear time, local checks), one
might hope that its structure can be "inverted" to find certificates quickly
(towards P = NP), or that its simplicity can be used to show that certificates
cannot be found quickly (towards P ≠ NP).

Part I item 3 ("Undecidability appears only when **universal correctness** ('for
all inputs') is required … ✔ We know which quantifiers introduce
undecidability") and the meta-conclusion ("a quantifier mismatch") point to the
same place. The verifier removes every quantifier except one, the quantifier
over certificates. This file isolates that quantifier exactly.

## 2. Precise mathematical formulation

* **CNF syntax and semantics** are as in Idea 01: `Lit = (var, pos)`,
  `evalClause`, `evalCNF`, `Satisfiable φ :⇔ ∃ a, evalCNF a φ = true`, and
  `VarsBelow n φ`.
* **Certificates** are bit vectors `cert : List Bool`, with `toAssign cert i` =
  bit `i` (`false` past the end).
* **Verifier.** `verify φ cert := evalCNF (toAssign cert) φ`.
* **Input size.** `encodeCNF` is Idea 01's lossless two-bit-token encoding
  (unary variable indices). `size φ` is the number of literal occurrences.
* **Cost model.** The verifier is instrumented to return a pair
  `(answer, number of literal evaluations)`:
  * `verifyRun` evaluates every literal once (no short-circuit);
  * `verifyRunSC` stops a clause at its first true literal and the formula at
    its first false clause.

  The unit of cost is one literal evaluation, i.e. one lookup of a certificate
  bit and one comparison. This is a *counted* cost, not machine steps. A
  Turing-machine verifier would need an additional polynomial overhead for
  moving the head to bit `var`. That overhead is not formalized here.
* **The NP-style claim.**
  `Satisfiable φ ↔ ∃ cert, |cert| = numVars φ ∧ verify φ cert = true`, with
  `numVars φ ≤ |encodeCNF φ|` and cost `size φ ≤ |encodeCNF φ| / 2`.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `verify_sound` | `verify φ cert = true → Satisfiable φ`, for all `φ`, `cert`. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `verify_complete` | `VarsBelow n φ → Satisfiable φ → ∃ cert, cert.length = n ∧ verify φ cert = true`. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `sat_iff_exists_cert` | `Satisfiable φ ↔ ∃ cert, cert.length = numVars φ ∧ verify φ cert = true`, for every CNF. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `numVars_le_encodingLength`, `cert_length_le_encoding` | A certificate of length `numVars φ` is at most as long as `encodeCNF φ`. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `verifyRun_result`, `verify_cost_eq` | The instrumented verifier returns `verify φ cert` and makes exactly `size φ` literal evaluations, for every certificate. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `verifyRunSC_result`, `verifyRunSC_cost_le` | The short-circuit verifier returns `verify φ cert` and makes at most `size φ` literal evaluations. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `size_le_encodingLength` | `2 · size φ ≤ (encodeCNF φ).length`. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `verify_cost_le_encoding` | `2 · cost ≤ (encodeCNF φ).length`: verification is linear in the input length. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `unsat_iff_all_rejected` | `VarsBelow n φ → (¬Satisfiable φ ↔ ∀ cert ∈ allAssignments n, verify φ cert = false)`. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `total_verification_cost` | Verifying every certificate of length `n` costs exactly `2^n · size φ` literal evaluations. | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |
| `decode_encode`, `encode_injective` | The input encoding is lossless (reused from Idea 01). | [Idea03.lean](../lean/Idea03.lean) | [Idea03.v](../rocq/Idea03.v) |

Not machine-checked: a Turing-machine implementation of the verifier and its
step count, the definition of the class NP over languages, and NP-completeness
of SAT (Cook–Levin).

## 4. Complete argument

**Soundness** is immediate. If `evalCNF (toAssign cert) φ = true`, then
`toAssign cert` is a satisfying assignment.

**Completeness.** Let `a` satisfy `φ` with `VarsBelow n φ`. The certificate
`prefixOf a n = [a 0, …, a (n−1)]` has length `n`, and `toAssign` of it agrees
with `a` below `n`. A formula on variables `< n` has the same value under
assignments that agree below `n` (`evalCNF_congr`, by induction on clauses and
literals). Hence `verify φ (prefixOf a n) = true`. Taking `n = numVars φ`
(`varsBelow_numVars`) gives the NP characterization `sat_iff_exists_cert`.

**Certificate length.** `numVars φ = 1 + max var`. Each literal with variable
`v` is encoded by `2v + 2` bits, so `numVars φ ≤ |encodeCNF φ|`
(`numVars_le_encodingLength`).

**Cost.** `clauseRun` returns `(evalClause, length c)` by induction on the
clause, and `cnfRun` returns `(evalCNF, Σ |c|) = (evalCNF, size φ)`. The cost
does not depend on the certificate at all. The short-circuit version returns
the same Boolean (case analysis on the first literal or clause value) and a
count bounded by the full count. Every literal occupies at least two bits
(`[false, pos]` plus `2v` tick bits), so `2 · size φ ≤ |encodeCNF φ|`.

Worked example. `φ = (x0 ∨ ¬x1) ∧ (x1 ∨ x2) ∧ (¬x0 ∨ ¬x2)` has `size φ = 6` and
`numVars φ = 3`. Its encoding has length
`(2+4+2) + (4+6+2) + (2+6+2) = 30` bits (literal `x_v` or `¬x_v` takes
`2v + 2` bits, and each clause ends with 2 bits). Verifying the certificate
`[true, true, false]` costs exactly 6 literal evaluations and accepts.

**Exhaustive checking.** By `unsat_iff_all_rejected`, `¬Satisfiable φ` is the
statement "all `2^n` certificates are rejected". Verifying all of them costs
`Σ_{v} size φ = 2^n · size φ` (`total_verification_cost`, by induction on the
list and `length_allAssignments`). For `n = 40` and `size φ = 400`, that is
`2^40 · 400 ≈ 4.4·10^14` literal evaluations, while a single verification costs
400.

**Why this is insufficient alone.** The theorems make NP-membership of SAT
fully explicit. They say nothing about how to *find* a certificate or rule them
all out faster than exhaustively. Idea 02 shows that treating the verifier as a
black box cannot beat `2^n`. Beating `2^n` polynomially requires using the
verifier's input `φ` as text, which is the open problem.

## 5. Known results and literature

* S. A. Cook, "The complexity of theorem-proving procedures", *Proc. 3rd ACM
  STOC*, 1971. Introduces polynomial-time reducibility and proves that every
  language accepted by a nondeterministic polynomial-time machine reduces to
  SAT, i.e. SAT is NP-complete. (Not formalized here.)
* L. A. Levin, "Universal sequential search problems", *Problemy Peredachi
  Informatsii* 9(3), 1973. Search problems defined by polynomially checkable
  relations. (Not formalized.)
* R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
  Computer Computations*, Plenum, 1972. 21 NP-complete problems, each with a
  simple verifier. (Not formalized.)
* The verifier characterization of NP (languages with polynomially bounded,
  polynomial-time checkable certificates) is textbook material, e.g.
  S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, Chapter 2. (Not formalized.)

## 6. How far the idea can be pushed toward P vs NP

At full potential the idea yields the complete, explicit NP side for SAT:

1. soundness and completeness of the verifier for every CNF;
2. certificate length `≤ |input|`;
3. verification cost `= size φ ≤ |input|/2` literal evaluations, independent of
   the certificate.

**Remaining obligation.** There is no open obligation on the verifier side.
The idea is finished. The obligation it exposes is to remove the certificate
quantifier in polynomial time, i.e. Idea 01's `PolySATDecider`, equivalent to
P = NP by Cook–Levin. For the co-side, a short certificate of
unsatisfiability for every unsatisfiable formula (a polynomially bounded proof
system) is equivalent to NP = coNP (Cook–Reckhow 1979, *J. Symbolic Logic* 44).
`unsat_iff_all_rejected` shows that the naive coNP certificate is the full list
of `2^n` rejections.

**Barriers.** Simple verifiers do not help separate the classes. Every NP
language has a verifier of this simple form, including NP-complete ones, so any
argument that uses only "the verifier is simple" applies equally to easy
problems like 2-SAT (whose verifier is the same `verify` restricted to 2-clauses)
and cannot distinguish them. Relativization applies as well: verification
relative to an oracle is just as easy, and Baker–Gill–Solovay oracles exist in
both directions.

## 7. Failure modes this idea catches

* **Verification confused with search**
  ([error family 15](../../../attempts/COMMON_ERRORS.md#15-confusing-verification-search-construction-and-certificates)):
  an argument of the form "checking is linear, so solving is polynomial" is
  contradicted by the gap between `verify_cost_eq` (`size φ`) and
  `total_verification_cost` (`2^n · size φ`). Only the latter is achieved by
  the naive method.
* **Certificate-size and encoding mistakes**
  ([family 17](../../../attempts/COMMON_ERRORS.md#17-encoding-size-bit-complexity-or-parameter-mistakes)):
  certificates and costs are bounded in terms of the explicit encoding
  (`cert_length_le_encoding`, `verify_cost_le_encoding`), so a claim that
  measures size in an incompatible parameter can be checked against these.
* **Nonstandard definitions of NP**
  ([family 11](../../../attempts/COMMON_ERRORS.md#11-using-undefined-nonstandard-or-incompatible-formal-definitions)):
  `sat_iff_exists_cert` is the standard verifier definition. Any attempt must
  state SAT in an equivalent form, and a "certificate" of exponential length or
  a verifier with unbounded cost does not qualify.
* **Hidden exponential work**
  ([family 2](../../../attempts/COMMON_ERRORS.md#2-hiding-exponential-work-in-a-claimed-polynomial-algorithm)):
  "verify each candidate" over `allAssignments n` costs exactly
  `2^n · size φ`.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea03.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea03.v
```

Both commands produce no output on success. Afterwards delete the generated
`proofs/experiments/issue532/rocq/Idea03.{vo,vok,vos,glob}` and
`.Idea03.aux` files.
