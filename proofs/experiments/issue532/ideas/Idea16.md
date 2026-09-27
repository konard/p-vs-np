# Idea 16 — Diagonalization

**Verdict:** Refuted in full strength (published theorem) + formal core. Diagonalization is the correct tool for hierarchy theorems, and its abstract form is proved in general (`diag_ne`, `hierarchy_abstract`, `hierarchy_strict`). The formal core is that the argument uses only the enumeration/simulation interface, so it holds verbatim in every oracle world (`diag_relativizes`, `hierarchy_relativizes`, `diagTech_relativizing`). A relativizing technique cannot prove a statement that fails in some world (`relativizing_cannot_prove`, `diagonalization_cannot_prove`). Baker, Gill and Solovay (1975) give oracles `A` and `B` with `P^A = NP^A` and `P^B ≠ NP^B`, so pure diagonalization settles P vs NP in neither direction. The query-complexity heart of their oracle `B` is also proved (`oracle_adversary`).

## 1. The idea at full strength

Diagonalization separates classes. The halting problem is undecidable,
`TIME(n) ⊊ TIME(n³)`, `P ⊊ EXP`, `NP ⊊ NEXP`. The natural hope is to
enumerate all polynomial-time machines `M₁, M₂, …` and build an NP language
that disagrees with `Mᵢ` on some input, for every `i`. That would prove
P ≠ NP. The full-strength idea is "some diagonal construction, possibly
elaborate, with an NP machine playing the universal simulator, separates
P from NP."

This dossier proves the abstract diagonal and hierarchy arguments in
general, formalizes what it means for them to relativize, and records why
the Baker–Gill–Solovay theorem rules the idea out as a stand-alone method.

## 2. Precise mathematical formulation

* A language is `L : ℕ → Bool`. An enumeration is `e : ℕ → ℕ → Bool`, with
  `e i` the `i`-th language. The diagonal is `diag e n = ¬ e n n`.
* `Enumerates e C`: every `e i` is in `C`, and every `L ∈ C` equals some
  `e i`. `C` is the abstraction of "languages decided in time `t`".
* `OneQuery u L`: there are `a : ℕ → ℕ` and `g : Bool → Bool` with
  `L x = g (u (a x) x)`. This abstracts "decidable by a machine that runs
  the universal simulator once", i.e. in somewhat more time.
* An oracle world is `O : ℕ → Bool`. A statement about worlds is
  `S : World → Prop`. `Relativizes S :≡ ∀ O, S O`.
* A technique `T : (World → Prop) → Prop` is the set of world-statements it
  establishes. `Relativizing T :≡ ∀ S, T S → Relativizes S`.
* `DiagTech` is pure diagonalization: statements that, world by world, are
  equivalent to the diagonal conclusion or the hierarchy conclusion for some
  oracle-extended enumeration `eO`, `uO`, `CO`.
* Query algorithms are decision trees `QT ::= leaf b | query q t f` run
  against an oracle. `qdepth` is the worst-case number of queries. The BGS
  test language is
  `testLang O n := ∃ y < 2^n, O (2^n + y)`, where `2^n + y` codes the
  length-`n` string `y`.

**Open obligation (definition, never assumed).**
`NonRelativizingIngredient T real S :≡ (∀ S', T S' → S' real) ∧ T S ∧ ¬ Relativizing T`.
This asks for a technique that is sound in the real world, proves `S`, and
does not relativize. With `S O := "P^O ≠ NP^O"` and `real` the empty
oracle, it describes what any proof of P ≠ NP must contain. The
relativized classes P^O and NP^O are not formalized here.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `diag_ne` | For every enumeration `e` and every `i`, `diag e ≠ e i`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `no_enumeration_of_all` | No enumeration lists all languages. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `hierarchy_abstract` | If `e` enumerates `C` and `u i x = e i x`, then `x ↦ ¬u x x` is `OneQuery u` and not in `C`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `hierarchy_strict` | Under the same hypotheses, `C ⊆ OneQuery u` and the inclusion is strict. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `no_relativizing_proof` | If `S` fails in some world, `S` does not relativize. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `neither_relativizes` | If `S` fails in world `A` and holds in world `B`, neither `S` nor `¬S` relativizes. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diag_relativizes` | The diagonal theorem holds in every world, for every oracle-extended enumeration. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `hierarchy_relativizes` | The hierarchy theorem holds in every world. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diagTech_relativizing` | Pure diagonalization (`DiagTech`) is a relativizing technique. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `relativizing_cannot_prove` | A relativizing technique cannot prove a statement that fails in some world. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diagonalization_cannot_prove` | `DiagTech` proves no statement that fails in some world. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `ingredient_necessary` | Any technique proving a world-dependent statement is non-relativizing. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `path_length` | A run queries at most `qdepth t` points. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `run_agree` | Oracles agreeing on the queried points give the same output. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `anyB_iff` | The bounded disjunction `anyB p m` is true iff some `y < m` has `p y`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `testLang_one_certificate` | `testLang O n` holds iff some certificate `y < 2^n` has `O (2^n + y)`, so one query verifies it (the NP side). | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `exists_unqueried` | A list of length `< m` misses some point of `a, …, a + m − 1`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `oracle_adversary` | Every decision tree with `qdepth t < 2^n` computes `testLang · n` wrongly on some oracle. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |

`NonRelativizingIngredient` is a `def ... : Prop` in Lean and a
`Definition ... : Prop` in Rocq. It is never assumed. The Rocq file does not
import `FunctionalExtensionality` or any other axiom. No theorem in either
file proves or refutes P = NP.

## 4. Complete argument

**Diagonal.** If `diag e = e i`, evaluating both sides at `i` gives
`¬ e i i = e i i`, which is impossible for a Boolean.

**Hierarchy.** Let `D x = ¬ u x x`. `D` is `OneQuery u` with `a = id` and
`g = ¬`. If `D ∈ C`, then `D = e i` for some `i`. At input `i` this gives
`e i i = ¬ u i i = ¬ e i i`, a contradiction. Every `e i` is `OneQuery u`
(`a = const i`, `g = id`), so `C ⊊ OneQuery u`. The concrete hierarchy
theorems instantiate `C` as `TIME(t)`, `e` as a clocked enumeration of
machines, and `u` as a universal machine whose simulation overhead gives the
larger bound.

**Relativization.** Nothing in either proof inspects what `e` or `u` are,
beyond the interface `u i x = e i x`. Given an oracle `O` and the
oracle-machine enumeration `e_O`, `u_O`, the same proof goes through
(`diag_relativizes`, `hierarchy_relativizes`). This is the formal content of
"diagonalization relativizes". `DiagTech` collects exactly the statements
obtained this way, and `diagTech_relativizing` proves that each holds in
every world.

**The barrier.** Let `S O := "P^O ≠ NP^O"`. Baker–Gill–Solovay prove that
there is a world `A` with `¬ S A` and a world `B` with `S B`. By
`neither_relativizes`, neither `S` nor `¬ S` holds in all worlds. By
`relativizing_cannot_prove`, no relativizing technique, pure
diagonalization included, proves either one. A proof of P ≠ NP (or P = NP)
must therefore use a property of real machines that fails for some oracle
machines. This is `NonRelativizingIngredient`, and `ingredient_necessary`
shows that it cannot be avoided.

**Why the B side holds (the formalized core).** A deterministic machine
running in time `p(n) < 2^n` is, on input `1^n`, a decision tree over the
oracle with fewer than `2^n` queries. (This translation from machines to
decision trees is informal, since machines are not formalized; the formal
statement is about decision trees.) `oracle_adversary` runs it against
the empty oracle `O₀`:

* If it accepts, `O₀` is a counterexample, because `testLang O₀ n` is false.
* If it rejects, it has queried fewer than `2^n` points, so some string
  `2^n + y` was never queried (`exists_unqueried`). Put only that string
  into `O₁`. By `run_agree` the run is unchanged, so it still rejects, but
  `testLang O₁ n` is true.

An NP machine decides `testLang` with one guessed query
(`testLang_one_certificate`). BGS interleave this adversary step with an
enumeration of all polynomial-time oracle machines, choosing fresh lengths
`n` so that the stages do not interfere. That interleaving is not
formalized here.

**The A side (not formalized).** For a PSPACE-complete oracle `A`,
`NP^A ⊆ NPSPACE = PSPACE ⊆ P^A`, so `P^A = NP^A`.

## 5. Known results and literature

* A. M. Turing, "On computable numbers, with an application to the
  Entscheidungsproblem", Proc. London Math. Soc. (2) 42, 1936. The diagonal
  argument for undecidability.
* J. Hartmanis and R. E. Stearns, "On the computational complexity of
  algorithms", Trans. AMS 117, 1965. The deterministic time hierarchy
  theorem by clocked diagonalization.
* S. A. Cook, "A hierarchy for nondeterministic time complexity", JCSS
  7(4), 1973. The nondeterministic time hierarchy.
* T. Baker, J. Gill and R. Solovay, "Relativizations of the P =? NP
  question", SIAM J. Comput. 4(4), 1975. Oracles `A`, `B` with
  `P^A = NP^A` and `P^B ≠ NP^B`.
* R. E. Ladner, "On the structure of polynomial time reducibility", JACM
  22(1), 1975. If P ≠ NP, there are NP-intermediate languages. Its proof is
  a delayed diagonalization and also relativizes. It shows what
  diagonalization can do inside NP, assuming P ≠ NP.
* C. H. Bennett and J. Gill, "Relative to a random oracle A,
  P^A ≠ NP^A ≠ co-NP^A with probability 1", SIAM J. Comput. 10(1), 1981.
* A. Shamir, "IP = PSPACE", JACM 39(4), 1992. A non-relativizing result
  (there are oracles relative to which IP ≠ PSPACE). This shows that
  non-relativizing techniques exist, via arithmetization.
* A. A. Razborov and S. Rudich, "Natural proofs", JCSS 55(1), 1997, and
  S. Aaronson and A. Wigderson, "Algebrization: a new barrier in complexity
  theory", ACM TOCT 1(1), 2009. The further barriers that the known
  non-relativizing techniques run into.

## 6. How far the idea can be pushed toward P vs NP

* **Proved (general):** the diagonal and abstract hierarchy theorems for
  arbitrary enumerations and simulators; that both relativize; that
  relativizing techniques cannot prove world-dependent statements; and the
  adversary lower bound (fewer than `2^n` queries are not enough) behind
  the separating oracle.
* **Refuted (published, BGS):** any proof of P ≠ NP or of P = NP that
  relativizes, in particular pure diagonalization over machine
  enumerations with simulation.
* **What diagonalization does give:** `P ⊊ EXP`, `NP ⊊ NEXP`, and (Ladner)
  intermediate problems conditional on P ≠ NP. None of these compares P
  with NP, because the separated classes differ in the *same* resource by
  more than the simulation overhead. For P vs NP no universal simulator of
  one class inside the other with small overhead is known. Having one would
  already mean `NP ⊆ P`.
* **Exact remaining obligation:** `NonRelativizingIngredient` for
  `S O := "P^O ≠ NP^O"`. Known non-relativizing techniques
  (arithmetization, as in IP = PSPACE) are blocked for P vs NP by
  algebrization, and circuit-based ones by natural proofs.
* **Scope of the model:** "relativizes" is modelled as "holds in every
  world" for statements built from oracle-extended enumerations. Real
  relativization is a property of proofs, a meta-level notion. The model
  captures the logical core used in the barrier argument: a proof that
  applies to every world cannot establish a world-dependent statement.

## 7. Failure modes this idea catches

* **Misusing diagonalization** (family 13 in
  [`COMMON_ERRORS.md`](../../../attempts/COMMON_ERRORS.md)): a diagonal
  argument over polynomial-time machines that never uses a
  non-relativizing property is refuted by BGS
  (`diagonalization_cannot_prove`).
* **Ignoring known barriers** (family 14): the relativization barrier is
  made explicit (`relativizing_cannot_prove`, `neither_relativizes`).
* **Confusing computability with complexity** (family 10): the halting
  problem diagonal (`diag_ne`) proves undecidability. It gives no
  polynomial-time lower bound for a decidable NP problem.
* **Different problem** (family 5): hierarchy theorems separate classes
  with more of the same resource (`hierarchy_strict`). They do not compare
  deterministic and nondeterministic polynomial time.
* **Structure theorem from one algorithm class** (family 20): the
  adversary bound (`oracle_adversary`) is about query algorithms against
  arbitrary oracles, not about real machines on concrete inputs.

Audit rule: for any diagonal argument, ask "does this still work if every
machine has access to an oracle?" If yes, the argument cannot settle
P vs NP.

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea16.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea16.v
```

Both commands print nothing on success. Remove the generated
`Idea16.vo`, `.vok`, `.vos`, `.glob` and `.aux` files afterwards.
