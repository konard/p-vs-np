# Idea 34 — Quantifier order in lower bounds

**Verdict:** Correct tool, insufficient alone (general theorem proved)

A proof of P != NP must have the quantifier shape "there is an NP language such
that **for every** polynomial-time machine **there exists** an input on which
the machine is wrong". The swapped shape, "there is one input (or one finite
set of inputs) on which **every** algorithm is wrong", is false for any class of
algorithms closed under finite patching. The files prove this against the
repository's own machine model (`proofs/complexity`). They also prove that
hard inputs for such a class must occur at arbitrarily large sizes. No lower
bound is proved. The idea is an auditing tool that removes a common logical
error.

## 1. The idea at full strength

The hope is that one can prove P != NP by exhibiting **hard instances**: a
family of SAT formulas that "no algorithm can solve quickly". The most ambitious
reading is: "there is an explicit input (or input family) that defeats every
polynomial-time algorithm". From this, P != NP would follow.

Issue #532, Part I, item 3 says "We know which quantifiers introduce
undecidability ... Quantifier control is key". The meta-conclusion lists "a
quantifier mismatch" as a typical source of false impossibility. Part II,
Phase 4 asks to "encode proof templates ... record exact failure points". This
idea makes the quantifier structure of a lower bound explicit and machine-checks
which order is correct.

## 2. Precise mathematical formulation

From `proofs/complexity/lean/Complexity.lean` (Rocq: `proofs/complexity/rocq/Complexity.v`):

- `Word = List Bool`, `Language = Word → Bool`.
- `ClassP` is a record: a language, a finite instruction-table `Machine`, a
  polynomial `bound` (`c·(n+1)^k`), and proofs that the machine halts within
  the bound on every input and answers correctly.
- `InP L := ∃ p : ClassP, p.language = L`, and `InNP L` is defined similarly
  with verifiers.
- `PEqualsNP := ∀ L, InNP L → InP L` and `PNotEqualsNP := ¬ PEqualsNP`.

The correct unfolded shape (proved as `pNotEqualsNP_iff_unfolded`) is

    PNotEqualsNP ↔ ∃ L, InNP L ∧ ∀ p : ClassP, ∃ x, p.language x ≠ L x.

The input `x` is chosen **after** the record `p` (machine and polynomial) and
may depend on it. The erroneous shape is `∃ x, ∀ p, ...`, or
`∃ finite set xs, ∀ p, ∃ x ∈ xs, ...`.

For the function-level analysis, an algorithm class is a predicate
`Alg : (Word → Bool) → Prop`. `patch A L xs` answers `L x` on the finite
list `xs` and `A x` elsewhere. `PatchClosed Alg L` says that `Alg` is closed
under this patching. Polynomial-time machines have this property: a lookup
table for finitely many inputs adds a bounded amount of time. That fact about
`ClassP` is **not** formalized here, because building the patched instruction
table is a separate engineering task.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `exists_forall_imp_forall_exists` | for every relation `R`: `(∃ x, ∀ a, R a x) → ∀ a, ∃ x, R a x` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `forall_exists_not_imp_exists_forall` | on any type with `a₀ ≠ a₁` there is `R` with `∀ a, ∃ x, R a x` and `¬ ∃ x, ∀ a, R a x` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `exists_hard_imp_pNotEqualsNP` | `(∃ L, InNP L ∧ ¬ InP L) → PNotEqualsNP` (constructive) | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `pNotEqualsNP_imp_exists_hard` | `PNotEqualsNP → ∃ L, InNP L ∧ ¬ InP L` (classical) | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `pNotEqualsNP_iff_exists_hard` | `PNotEqualsNP ↔ ∃ L, InNP L ∧ ¬ InP L` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `not_inP_iff` | `¬ InP L ↔ ∀ p : ClassP, p.language ≠ L` (constructive) | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `language_ne_iff` | `L₁ ≠ L₂ ↔ ∃ x, L₁ x ≠ L₂ x` (classical plus function extensionality) | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `not_inP_iff_each_errs` | `¬ InP L ↔ ∀ p : ClassP, ∃ x, p.language x ≠ L x` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `pNotEqualsNP_iff_unfolded` | `PNotEqualsNP ↔ ∃ L, InNP L ∧ ∀ p : ClassP, ∃ x, p.language x ≠ L x` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `lookup_agrees` | for every finite list `xs`: `patch A L xs` agrees with `L` on every `x ∈ xs` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `patch_outside` | outside `xs`, `patch A L xs` equals `A` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `no_universal_hard_input` | for a nonempty patch-closed class: `¬ ∃ x, ∀ B ∈ Alg, B x ≠ L x` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `no_universal_hard_input_set` | for a nonempty patch-closed class: no finite list `xs` contains an error of every `B ∈ Alg` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `mem_inputsBelow` | every word of length `< m` is in the explicit list `inputsBelow m` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |
| `hard_inputs_unbounded` | patch-closed class, no member correct everywhere ⇒ every member errs on some input of length `≥ m`, for every `m` | [Lean](../lean/Idea34.lean) | [Rocq](../rocq/Idea34.v) |

Logical dependencies: in both provers, `pNotEqualsNP_imp_exists_hard`,
`pNotEqualsNP_iff_exists_hard`, `language_ne_iff`, `not_inP_iff_each_errs`,
`pNotEqualsNP_iff_unfolded` and `hard_inputs_unbounded` use classical logic.
In Rocq this is `Classical_Prop.NNPP`, and `language_ne_iff` also uses
`FunctionalExtensionality`. In Lean it is `Classical.byContradiction` and
`funext`. All other theorems are constructive.

## 4. Complete argument

**(a) Quantifier logic.** If one `x` satisfies `R a x` for all `a`, it serves
as the witness for each `a`. For the converse, take any `a₀ ≠ a₁` and
`R a x := (a = x)`. Each `a` has the witness `x = a`. A single `x` with
`a = x` for all `a` would give `a₀ = x = a₁`. In lower-bound language, with
`a` an algorithm and `x` an input, this says: "every algorithm has an input on
which it fails" does not imply "some input makes every algorithm fail".

**(b) P != NP as an existence statement.** `PNotEqualsNP` is `¬ ∀ L, InNP L → InP L`.
If `L ∈ NP \ P` exists, then `PEqualsNP` would put it in P, a contradiction.
This direction is constructive. Conversely, assume `PNotEqualsNP` and suppose
no such `L` exists. Then for each `L ∈ NP`, `¬ InP L` is contradictory, so
`InP L` holds by double-negation elimination. This proves `PEqualsNP`, a
contradiction. This direction needs classical logic twice.

**(c) Unfolding `¬ InP L`.** `InP L` is `∃ p : ClassP, p.language = L`, so its
negation is `∀ p, p.language ≠ L`. With function extensionality and classical
logic, `p.language ≠ L` is `∃ x, p.language x ≠ L x`. So a P != NP proof must
produce, for **each** record `p`, meaning each machine together with each
polynomial clock and each proof of its correctness for the language it decides,
an input `x` where that machine's language differs from `L`. The input `x`
depends on `p`.

**Why the swapped order is false.** Fix any algorithm `A` in a class closed
under finite patching and any finite list `xs` of candidate hard inputs. The
patched algorithm `patch A L xs` is also in the class and answers `L` correctly
on every element of `xs` (`lookup_agrees`). So no finite set of inputs can be
hard for every member (`no_universal_hard_input_set`). The one-input case is
`no_universal_hard_input`. For example, let `L` be SAT and `xs` any list of
1000 formulas. The algorithm "look the formula up in a 1000-entry table, else
answer `false`" is correct on all of them. It is polynomial-time, with an
additive cost that is bounded independently of the input length.

**Hard inputs must be unbounded in size.** Suppose the class contains no
algorithm that is correct everywhere, and suppose `A` in the class were correct
on all inputs of length `≥ m`. Patch `A` on the finite list `inputsBelow m`
of all `2^0 + ... + 2^(m-1)` words of length `< m`. The result lies in the class
and is correct everywhere, a contradiction. So `A` errs at some length `≥ m`, for
every `m` (`hard_inputs_unbounded`). This is the formal reason why "a hard
instance of size 10^6" says nothing about P vs NP. Lower bounds are statements
about infinitely many sizes, and the hard input for each algorithm moves with
the algorithm.

## 5. Known results and literature

- S. Cook, "The complexity of theorem-proving procedures", *STOC 1971*; and R.
  Karp, "Reducibility among combinatorial problems", 1972. These are the standard
  definitions of NP-completeness that the `∃ L ∈ NP` quantifier ranges over.
- The standard textbook formulation of P != NP as "for every polynomial-time
  machine M there are inputs on which M errs on SAT" is found, for example, in
  S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
- Finite modifications: every finite variant of a language in P is in P. This
  is standard textbook material and is the reason `PatchClosed` holds for P. It
  is not formalized for the `Machine` model here.
- Adversary and diagonalization arguments (for example the time hierarchy
  theorem of Hartmanis and Stearns, "On the computational complexity of
  algorithms", *Trans. AMS* 117, 1965) have exactly the `∀ machine ∃ input`
  shape. They construct the hard input from the machine's description.

None of the cited results is formalized here, beyond the logical skeleton and
the function-level patching argument.

## 6. How far the idea can be pushed toward P vs NP

**At full potential** the idea is a correct normal form. Any proof of P != NP in
the repository's model must establish

    ∃ L, InNP L ∧ ∀ p : ClassP, ∃ x, p.language x ≠ L x

and, by `hard_inputs_unbounded` applied to any patch-closed class (such as
polynomial time), the witnesses `x` must be available at arbitrarily large
lengths. The remaining obligation is `PNotEqualsNP` itself. This idea does not
reduce it. It only rules out proof shapes that cannot work:

- `∃ x, ∀ p, ...` is refuted by `no_universal_hard_input`.
- `∃ finite xs, ∀ p, ∃ x ∈ xs, ...` is refuted by `no_universal_hard_input_set`.
- "hard at one size" is refuted by `hard_inputs_unbounded`.

**Barriers.** The `∀ p ∃ x` shape is what diagonalization provides, and
diagonalization relativizes (Baker–Gill–Solovay; see Idea 38). The input
`x` cannot be chosen uniformly for all algorithms, so "hard distribution"
arguments must quantify over algorithms first as well (see Idea 33).

**Strength.** The obligation is literally equivalent to P != NP
(`pNotEqualsNP_iff_unfolded`), so nothing is gained or lost in strength. The
contribution is the precise quantifier shape.

## 7. Failure modes this idea catches

In [COMMON_ERRORS](../../../attempts/COMMON_ERRORS.md):

- **Family 12 (circular reasoning / smuggling the conclusion):** "these
  instances are hard for every algorithm" assumes `∃ x ∀ p`, which is false for
  patch-closed classes.
- **Family 13 (misusing diagonalization):** a diagonal construction yields
  `∀ p ∃ x`. Reading it as a fixed hard input swaps quantifiers.
- **Family 14 (barriers):** the `∀ p ∃ x` shape alone gives no
  nonrelativizing leverage.
- **Family 16 (uniformity / finite-size):** a lower bound at one input size, or
  on one benchmark list, is refuted as a P != NP argument by
  `no_universal_hard_input_set` and `hard_inputs_unbounded`.
- **Family 20 (one algorithm class):** showing that algorithms of a special form
  fail is a statement `∀ p ∈ special, ∃ x`, not `∀ p : ClassP, ∃ x`.

Audit rule: rewrite the claimed lower bound in prenex form and compare it with
`pNotEqualsNP_iff_unfolded`. If an input is quantified before the algorithm, or
the hard inputs have bounded size, the argument is invalid.

## 8. Reproduction

From the repository root (the shared model must be built first):

```bash
lake build proofs.complexity.lean.Complexity   # only if not yet built
lake env lean proofs/experiments/issue532/lean/Idea34.lean
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea34.v
rm -f proofs/experiments/issue532/rocq/Idea34.{vo,vok,vos,glob} proofs/experiments/issue532/rocq/.Idea34.aux
```

The Idea34 commands print nothing on success.
