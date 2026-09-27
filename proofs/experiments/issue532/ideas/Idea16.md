# Idea 16 — Diagonalization

**Verdict:** Refuted in full strength (published theorem) + formal core. Diagonalization is the correct tool for hierarchy theorems, and its abstract form is proved in general (`diag_ne`, `hierarchy_abstract`, `hierarchy_strict`). The formal core is that the argument uses only the enumeration/simulation interface, so it holds verbatim in every oracle world (`diag_relativizes`, `hierarchy_relativizes`, `diagTech_relativizing`). A relativizing technique cannot prove a statement that fails in some world (`relativizing_cannot_prove`, `diagonalization_cannot_prove`). Baker, Gill and Solovay (1975) give oracles `A` and `B` with `P^A = NP^A` and `P^B ≠ NP^B`, so pure diagonalization settles P vs NP in neither direction. The query-complexity heart of their oracle `B` is also proved (`oracle_adversary`). In the shared machine model the files define oracle machines and `P^A`, `NP^A` (`InPO`, `InNPO`, `PEqualsNPO`), prove that a constant oracle gives back `InP`, `InNP` and `PEqualsNP` (`pEqualsNPO_const_iff`), state BGS as the named known theorems `BGSCollapse` and `BGSSeparation` (`bgs_no_uniform_answer`), and prove the diagonal half of the deterministic time hierarchy for machines (`diagWithin_not_decidedWithin`), unrelativized and relative to every oracle.

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

**Generic schema (definition, never assumed).**
`NonRelativizingIngredientFor T real S :≡ (∀ S', T S' → S' real) ∧ T S ∧ ¬ Relativizing T`.
This asks for a technique that is sound in the real world, proves `S`, and
does not relativize. It is a schema over a free technique `T`, not an open
obligation: the verdict is a barrier, and the machine part below states the
barrier itself in the shared model.

**Machine part (shared model `Complexity.Machine`, `Issue532.Machines`).**

* An oracle is a language `A : Oracle := Language`. An oracle machine
  `OMachine` has the instructions of `Complexity.Instruction` plus
  `query yes no`, which reads the bits from the head rightwards
  (`queryWord`) and jumps to `yes` if `A` holds of them, else to `no`.
  `ORun A m c t b` is the run relation, with the same step count as
  `Complexity.Run`.
* `ODecidesWithin A m p L`, `InPO A L` (P^A), `InNPO A L` (NP^A, with an
  `OVerifier` on `pairedInput x cert` and the bounds of `ClassNP`) and
  `PEqualsNPO A := ∀ L, InNPO A L → InPO A L`.
* Known theorem (Baker–Gill–Solovay 1975), as named hypotheses:
  `BGSCollapse := ∃ A, PEqualsNPO A` and
  `BGSSeparation := ∃ B, ¬ PEqualsNPO B`.
* Time hierarchy in the machine model. `AcceptsWithin m p w` is
  `∃ t ≤ p(|w|), Run m (initial w) t true`, and
  `DiagWithin p` is the diagonal language over `encMachine`:
  `w ∈ DiagWithin p ↔ ¬ ∃ m, encMachine m = w ∧ AcceptsWithin m p w`.
  * `TimeHierarchy := ∀ p, ∃ L, InP L ∧ ¬ ∃ m, DecidesWithin m p L`.
  * `UniversalSimulation := ∀ p, InP (DiagWithin p)` (known theorem,
    Hartmanis–Stearns 1965 with the Hennie–Stearns simulation).
  * The relativized versions are `DiagWithinO`, `TimeHierarchyO A` and
    `UniversalSimulationO`.
* Time classes with a linear-constant slack:
  `InDTIME T L := ∃ m c, ∀ x, ∃ t b, t ≤ c·T(|x|) + c ∧ Run m (initial x) t b ∧ b = L x`
  and `InNTIME T L` (a verifier on `pairedInput x cert` with certificates and
  running time at most `c·T(|x|) + c`).
  `NTimeHierarchyGap T₁ T₂ := ∃ L, InNTIME T₂ L ∧ ¬ InNTIME T₁ L` and
  `NTimeHierarchy := ∀ k ≥ 3, NTimeHierarchyGap (n ↦ 2^n / (n+1)^k) (n ↦ 2^n)`
  (known theorem: Cook 1973, Seiferas–Fischer–Meyer 1978, Žák 1983).

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
| `NonRelativizingIngredientFor` (def) | Schema over a free technique: sound in the real world, proves `S`, not relativizing. Never assumed. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `orun_deterministic` | Oracle-machine runs are deterministic. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `orun_lift_iff` | An ordinary machine, lifted, runs identically against every oracle. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `run_lower_iff` | Against the constant oracle `b`, an oracle machine runs like the ordinary machine `lowerMachine b m`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `inPO_of_inP`, `inNPO_of_inNP`, `inNPO_of_inPO` | P ⊆ P^A, NP ⊆ NP^A and P^A ⊆ NP^A for every oracle. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `inPO_const_iff`, `inNPO_const_iff`, `pEqualsNPO_const_iff` | For a constant oracle: `InPO ↔ InP`, `InNPO ↔ InNP`, `PEqualsNPO ↔ PEqualsNP`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `pEqualsNP_of_all_oracles`, `pNotEqualsNP_of_all_oracles` | An answer that holds for every oracle holds for the real classes. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `BGSCollapse`, `BGSSeparation` (defs) | Known theorem (BGS 1975), named hypotheses: some oracle with `P^A = NP^A`, some with `P^B ≠ NP^B`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `bgs_no_uniform_answer` | Under BGS, neither `∀ A, PEqualsNPO A` nor `∀ A, ¬ PEqualsNPO A`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diagonal_core` | For an injective code `e` and any acceptance relation, the diagonal language `diagLang e Acc` is not the acceptance set of any `m`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diagWithin_not_decidedWithin` | No machine decides `DiagWithin p` within `p` steps (diagonal half of the time hierarchy, proved). | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `UniversalSimulation`, `TimeHierarchy` (defs) | Known theorem: `DiagWithin p ∈ P`; the hierarchy `∀ p, ∃ L ∈ P` not decided within `p`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `timeHierarchy_of_universalSimulation` | `UniversalSimulation → TimeHierarchy`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `no_uniform_bound_of_timeHierarchy` | Under `TimeHierarchy`, no single polynomial bounds all of P. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `encOMachine_injective` | Oracle machines have an injective prefix-free encoding. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `diagWithinO_not_decidedWithin` | For every oracle `A`, no oracle machine decides `DiagWithinO A p` within `p` (the diagonal relativizes, in the machine model). | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `TimeHierarchyO`, `UniversalSimulationO` (defs) | Relativized hierarchy; known theorem: universal simulation relative to every oracle. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `timeHierarchyO_of_universalSimulationO` | `UniversalSimulationO → ∀ A, TimeHierarchyO A`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `InDTIME`, `InNTIME`, `NTimeHierarchyGap`, `NTimeHierarchy` (defs) | Deterministic and nondeterministic time classes; the nondeterministic time hierarchy as a known theorem. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |
| `exists_not_inDTIME`, `exists_not_inNTIME` | Non-vacuity: for every `T` some language is outside `DTIME(T)` and outside `NTIME(T)`. | [Lean](../lean/Idea16.lean) | [Rocq](../rocq/Idea16.v) |

`NonRelativizingIngredientFor`, `BGSCollapse`, `BGSSeparation`,
`UniversalSimulation`, `UniversalSimulationO` and `NTimeHierarchy` are
`def ... : Prop`. The last five are known theorems, not mechanised here; they
appear only as explicit hypotheses. The intended Rocq names equal the Lean
names; the Rocq file still has the pre-machine version. The Rocq file does not
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
machines. This is the schema `NonRelativizingIngredientFor`, and
`ingredient_necessary` shows that it cannot be avoided.

**The barrier in the machine model.** Oracle machines are
`Complexity.Machine` with one extra instruction. With a constant oracle the
query is a fixed jump, so `lowerMachine b m` runs identically
(`run_lower_iff`), and `P^A`, `NP^A` and `P^A = NP^A` collapse to `InP`,
`InNP` and `PEqualsNP` (`pEqualsNPO_const_iff`). Hence an answer proved for
every oracle is an answer for the real classes
(`pEqualsNP_of_all_oracles`, `pNotEqualsNP_of_all_oracles`), and under
the named BGS hypotheses no answer holds for every oracle
(`bgs_no_uniform_answer`).

**Time hierarchy in the machine model.** Encode machines by the injective
prefix-free `encMachine`. The diagonal language `DiagWithin p` accepts `w`
iff `w` is not the code of a machine that accepts `w` within `p(|w|)` steps.
If `m` decided it within `p`, then at `w = encMachine m` acceptance within
`p` would coincide with the diagonal's answer, which is its negation
(`diagonal_core`, `diagWithin_not_decidedWithin`). Membership of
`DiagWithin p` in P needs a clocked universal machine; that is the known
theorem `UniversalSimulation`, and `timeHierarchy_of_universalSimulation`
gives `TimeHierarchy`. The same proof, with `encOMachine`, works relative to
every oracle (`diagWithinO_not_decidedWithin`). This is the machine-model
form of "diagonalization relativizes".

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
* F. C. Hennie and R. E. Stearns, "Two-tape simulation of multitape Turing
  machines", J. ACM 13(4), 1966. The `O(T log T)` universal simulation.
* S. A. Cook, "A hierarchy for nondeterministic time complexity", JCSS
  7(4), 1973. The nondeterministic time hierarchy.
* J. I. Seiferas, M. J. Fischer and A. R. Meyer, "Separating
  nondeterministic time complexity classes", J. ACM 25(1), 1978, and
  S. Žák, "A Turing machine time hierarchy", TCS 21(3), 1983. The
  nondeterministic hierarchy for all time-constructible `T₁(n+1) = o(T₂(n))`.
  These results are for multitape machines; the one-tape model here pays an
  `O(|M|·T)`-type simulation overhead, which is why `NTimeHierarchy` keeps
  a gap of `(n+1)^k` with `k ≥ 3` between `2^n / (n+1)^k` and `2^n`.
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
* **Machine-level barrier:** with `P^A`, `NP^A` defined for machines
  (`InPO`, `InNPO`), a proof that works for every oracle settles the real
  question (`pEqualsNP_of_all_oracles`, `pNotEqualsNP_of_all_oracles`), and
  BGS (`BGSCollapse`, `BGSSeparation`, named hypotheses) rules out both
  answers for every oracle (`bgs_no_uniform_answer`). There is no open
  obligation here: what a proof would have to add is the schema
  `NonRelativizingIngredientFor` for `S O := "P^O ≠ NP^O"`, which is a
  requirement on techniques, not a statement about machines. Known non-relativizing techniques
  (arithmetization, as in IP = PSPACE) are blocked for P vs NP by
  algebrization, and circuit-based ones by natural proofs.
* **Scope of the model:** "relativizes" is modelled as "holds in every
  world" for statements built from oracle-extended enumerations. Real
  relativization is a property of proofs, a meta-level notion. The model
  captures the logical core used in the barrier argument: a proof that
  applies to every world cannot establish a world-dependent statement. The
  machine part makes the worlds concrete (oracle machines of the shared
  model); the BGS construction itself and universal simulation are not
  mechanised, and the translation from polynomial-time oracle machines to
  decision trees used by `oracle_adversary` is informal.

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
