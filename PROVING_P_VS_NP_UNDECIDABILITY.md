# Investigating P vs NP independence: a research roadmap

**Navigation:** [Repository root](README.md) · [Independence strategies](P_VS_NP_INDEPENDENCE_STRATEGIES.md) · [Issue 7 investigation](experiments/issue7_undecidability_attempt.md) · [Conditional independence schema](proofs/p_vs_np_undecidable/README.md)

## Scope and logical target

The question here is **independence from a specified formal theory**. It is distinct from the truth of P = NP in the standard natural numbers and from algorithmic undecidability. No result in this repository establishes either P = NP, P ≠ NP, or their independence from ZFC.

Fix the **object theory** `T = ZFC`, with a chosen recursive coding of its language, axioms, and first-order proofs. Let `φ` be the exact ZFC translation of the clocked-SAT sentence below. Define the syntactic provability predicate

```text
Pr_T(n) := ∃ p Proof_T(p,n),
Ind_T(φ) := ¬Pr_T(⌜φ⌝) ∧ ¬Pr_T(⌜¬φ⌝).
```

`Proof_T(p,n)` means that `p` codes a valid finite `T` proof of the formula with Gödel number `n`. A proof assistant formalization must implement that coding; an arbitrary `Theory.proves` parameter does not instantiate ZFC. The current [independence schema](proofs/p_vs_np_undecidable/README.md) deliberately leaves this relation abstract.

Our working **metatheory** is ordinary classical mathematics strong enough to reason about syntax, first-order completeness, and models, for example ZFC. Any claim that a model of ZFC exists must explicitly assume `Con(ZFC)` or another sufficient relative consistency hypothesis; ZFC cannot establish its own consistency if it is consistent. By the deduction and completeness theorems, `Ind_T(φ)` corresponds to consistency of both `T + φ` and `T + ¬φ`, and then to models of each extension, when those theorems and the relevant consistency assumptions are available in the metatheory. The two models need not be transitive or related by forcing. A claim that a `T` proof gives **standard arithmetic truth** additionally needs soundness for the relevant sentence; consistency alone is insufficient. A proof assistant's kernel checks a formal derivation relative to its definitions, axioms, and trusted implementation. It does not independently certify that the formal sentence captures the intended complexity classes.

## The arithmetic statement and quantifiers

Use deterministic Turing-machine code `e`, polynomial clock code `k`, and input code `x`. Let `R(e,k,x)` be the computable predicate saying that `e` halts within its clock on `x` and returns the correct answer to SAT. For each finite `x`, SAT can be checked by exhaustive search; machine simulation under a fixed clock is finite. In the standard natural numbers, the intended formulas are:

```text
P = NP  ⇔  ∃ e,k ∀ input x, R(e,k,x)              (Σ⁰₂ form)
P ≠ NP  ⇔  ∀ e,k ∃ input x, ¬R(e,k,x)             (Π⁰₂ form)
```

The equivalence to P = NP uses SAT's NP completeness, including Cook–Levin hardness, and must be proved for the **chosen machine model** before using the formula as a formal replacement. These are upper bounds in the arithmetical hierarchy, not completeness claims. The same SAT language must defeat **every** polynomial-time candidate in the second line. Allowing the NP language to vary with the machine gives a different and much weaker assertion.

## What forcing and proof search actually say

For a transitive ground model `M` of set theory and its ordinary set-forcing extension `M[G]`, arithmetic truth is preserved because the natural numbers and finite computations are the same. In particular, forcing invariance gives `M ⊨ φ` exactly when `M[G] ⊨ φ`, provided `φ` is correctly represented by the arithmetic sentence above. This rules out a truth-changing forcing construction over that ground model. **Independence and provability remain open**: forcing invariance does not establish `Pr_T(⌜φ⌝)` or `Pr_T(⌜¬φ⌝)`. The models supplied by completeness for a possible independence result need not be a ground-model/forcing-extension pair. A generic oracle can change a relativized complexity question without becoming an ordinary finite SAT-deciding program.

The standard model has a definite truth value for `φ`, and classical excluded middle proves `φ ∨ ¬φ`. Neither fact supplies a `T` proof of a branch. The metamathematical statement `Ind_T(φ)` also has a classical truth value in a fixed metatheory, but no theorem here gives a decision algorithm or guarantees a proof of either answer in that metatheory. To disprove independence it would suffice to exhibit a genuine `T` proof of `φ` or `¬φ`. Showing that one class of model constructions fails would not suffice. To prove independence, establish both nonprovability claims, or both relative consistency claims, with all hypotheses exposed.

Automated tools can enumerate candidate proofs and use a proof assistant to check those that they find. Search may run forever when there is no proof in the chosen calculus. Proof checking certifies the encoded theorem relative to the imported assumptions and semantics; it cannot turn a placeholder predicate or a `sorry` into the intended ZFC result. The [issue 7 Lean experiments](experiments/issue7_undecidability_attempt.md) illustrate excluded middle and conditional forcing invariance only; they do not formalize ZFC, forcing, or the full SAT equivalence.

## Current formal foundation

The repository already defines encoded CNF `SAT` on a shared machine model in [Lean Machines](proofs/experiments/issue532/lean/Machines.lean) and [Rocq Machines](proofs/experiments/issue532/rocq/Machines.v). Paired [Lean SATVerifier](proofs/experiments/issue532/lean/SATVerifier.lean) and [Rocq SATVerifier](proofs/experiments/issue532/rocq/SATVerifier.v) prove `satInNP : SATInNP` using explicit verifier machines. The models state `SATHard` and `CookLevin`; **SATHard remains an unfinished formal proof obligation**. Theorems connecting `InP SAT` to `PEqualsNP` are conditional on that hardness premise (or on `CookLevin`). Reuse these files, and keep the premise visible until it is proved. A fresh SAT definition with an admission would lose this established result.

The [conditional independence schema](proofs/p_vs_np_undecidable/README.md) has a syntactic negation and an abstract proof relation, but no ZFC proof predicate. A concrete independence theorem needs an encoding of `T` and a verified bridge from the shared machine statement to the ZFC sentence `φ`. The bridge must specify how strings, machines, polynomial clocks, and computations are represented in set theory. Compilation of a schematic theorem is not evidence that those bridges are complete.

## Research phases and reviewable deliverables

These phases are logical dependencies rather than promised dates. Each deliverable should state a precise proposition, its dependencies, and whether it is proved or only conditional. For new formal results in the shared model, provide corresponding Lean and Rocq statements and identify any asymmetric implementation gap.

### 1. Audit definitions and references

- Fix the object sentence `φ`, proof calculus for `T`, Gödel coding, and intended standard interpretation in a short design note.
- Compare the existing machine, SAT, and independence definitions with [the corrected issue 7 analysis](experiments/issue7_undecidability_attempt.md) and [strategy catalog](P_VS_NP_INDEPENDENCE_STRATEGIES.md).
- Record separately which statements concern standard arithmetic truth, model-relative truth, `T` provability, and metatheoretic provability.

**Exit condition:** A reviewer can trace every claim to a definition or a cited theorem and can see every imported assumption.

### 2. Complete the SAT bridge in the shared model

- Reuse `Machines.SAT` and the proved `SATVerifier.satInNP` in both Lean and Rocq.
- Prove the hardness half `SATHard` for the actual machine and reduction definitions, or retain it explicitly as a hypothesis.
- Establish the clocked-decider equivalence with `PEqualsNP` only after its polynomial bounds, encodings, and Cook–Levin dependencies are discharged.

**Exit condition:** The two prover files state matching theorems; an assumption audit distinguishes proved results from conditional corollaries.

### 3. Develop the bounded-arithmetic branch precisely

For an explicitly chosen language and `BASIC` axioms, `S₂¹` uses **Σᵇ₁-PIND** (polynomial or length induction), while `T₂¹` uses **Σᵇ₁-IND** (ordinary successor induction). Here PIND steps from the value at `⌊x/2⌋` to the value at `x`; IND steps from `x` to `x+1`. These are different axiom or inference schemas. Buss gives the definitions in his [bounded-arithmetic thesis](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/BAthesis/Buss_Thesis.pdf) and discusses their proof-theoretic strength in his [survey](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/index.html).

- Encode these schemas and verify a small representative derivation in each theory before asserting any relationship to a complexity class.
- Formulate a specific nonprovability or proof-length conjecture with an exact formula and theory. Proving a separation between `S₂¹` and `T₂¹`, or an independence result for P vs NP, remains a research obligation; no such result follows merely from their definitions.

**Exit condition:** The formal schemas match Buss's definitions and all claimed implications have proofs or labeled hypotheses.

### 4. Analyze nonstandard models

- Define how internal natural numbers, finite strings, machine codes, and clocks are interpreted in a nonstandard model of `T`.
- Check which arithmetic absoluteness argument applies to each pair of models. Ordinary forcing extensions of a transitive ground model are a restricted case.
- If a model construction is proposed, identify the exact consistency assumption that supplies the model and the sentence it satisfies.

**Exit condition:** A model argument states satisfaction of `φ` or `¬φ` and does not infer syntactic provability from shared truth alone.

### 5. Study proof complexity and barriers

- State the proof system, formula family, size measure, and explicit lower-bound target.
- Treat relativization, natural proofs, and algebrization as limits on particular techniques. None by itself proves unprovability in `T`.
- Relate any lower bound to `Ind_T(φ)` only through a separate, proved metatheorem.

**Exit condition:** Every lower-bound claim has a formal quantifier structure and a cited or proved transfer theorem.

### 6. Test a genuine independence route

- Formulate the proposed theorem as `Ind_T(φ)`, or as `Con(T + φ) ∧ Con(T + ¬φ)` in a named metatheory.
- Give a construction or syntactic argument for **both** sides, with the consistency and soundness requirements spelled out.
- Check whether the construction is blocked by arithmetic invariance; if so, record that restriction without inferring ZFC provability.

**Exit condition:** A formal derivation proves the exact metatheorem with its assumptions, or the attempted route is recorded as unresolved. There is no guaranteed endpoint.

## First concrete task

Start from [Lean Machines](proofs/experiments/issue532/lean/Machines.lean) and [Rocq Machines](proofs/experiments/issue532/rocq/Machines.v). Read their `SAT`, `SATHard`, `CookLevin`, and `inP_sat_iff` definitions, then inspect the two `SATVerifier.satInNP` proofs. Write paired Lean and Rocq statements of the clocked-SAT equivalence, listing `SATHard` explicitly wherever it is still needed. Prove a small encoding or clock lemma in each prover, with no new admissions, and record the remaining Cook–Levin hardness obligation. This gives a checkable intermediate result without implying that independence is settled.

**Status:** done in [issue7/](proofs/experiments/issue7/README.md). The paired [Lean ClockedSAT](proofs/experiments/issue7/lean/ClockedSAT.lean) and [Rocq ClockedSAT](proofs/experiments/issue7/rocq/ClockedSAT.v) files prove the clock lemma `runFor_iff`. They prove that the Σ⁰₂ form `∃ m p, ∀ x, clockCheck m p x = true` is `InP SAT` with no premise, and that it is equivalent to `PEqualsNP` given `SATHard`. Its negation is the Π⁰₂ form `∀ m p, ∃ x, clockCheck m p x = false`. `per_machine_form_holds` proves that the per-machine quantifier order holds outright, so it cannot express P ≠ NP. `SATHard` remains unproved in the shared model, and independence remains open. The next tasks are to prove `SATHard` for `Complexity.Machine`, to code machines and clocks as natural numbers, and to translate the sentence into ZFC with a concrete `Proof_T`.

## Possible outcomes and reporting

A direct `T` proof of either side would refute `Ind_T(φ)`. A metatheoretic proof of both nonprovability claims, under stated assumptions, would establish the corresponding conditional independence result. A result about a weaker theory, a restricted proof system, or one forcing family must keep that scope in its title and conclusion. An infrastructure result can be useful even if no independence claim follows. No probability percentages, publication outcomes, or completion dates are justified by the present evidence.

## Primary references

- Scott Aaronson, [*P ?= NP*, §3.1 and footnote 24](https://www.scottaaronson.com/papers/pnp.pdf), on arithmetic statements and set-theoretic independence.
- Samuel R. Buss, [*Bounded Arithmetic*](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/BAthesis/Buss_Thesis.pdf), for `S₂¹` and `T₂¹` induction schemas.
- Samuel R. Buss, [*Bounded Arithmetic and Propositional Proof Complexity*](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/marktoberdorf95/index.html), for bounded-arithmetic proof strength and proof complexity.
