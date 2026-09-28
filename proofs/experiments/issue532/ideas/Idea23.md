# Idea 23 — Resolution-based SAT reasoning

**Verdict:** Developed to an open obligation (conditional theorem proved)

Resolution with weakening is sound and complete for unsatisfiability. The
files prove, for every CNF, that a CNF is unsatisfiable iff the empty
clause is derivable. As a route to polynomial SAT algorithms, resolution is
refuted by a published theorem: Haken (1985) proved that the pigeonhole
formulas need exponentially large resolution refutations (cited, not
formalized). The general version, Cook's program of proving
superpolynomial lower bounds for every propositional proof system, is
developed to the open obligation `NoPolyBoundedUNSATProofSystem`: UNSAT
(`complement SAT` in the shared machine model) has no polynomially bounded
proof system whose verifier is a polynomial-time machine. The files prove
that it implies `¬ InP SAT`, that with SAT ∈ NP it implies `PNotEqualsNP`,
and that with the named known theorems (Cook–Reckhow, Cook–Levin, closure
of NP under reductions) it is equivalent to NP ≠ coNP
(`noPolyBounded_iff_npNeCoNP`). SAT ∈ NP (`SATInNP`) is proved in
`SATVerifier` (`SATVerifier.satInNP`), so the primed versions drop that
premise: the obligation implies `PNotEqualsNP` with no other premise
(`pNotEqualsNP_of_noPolyBounded'`), and the equivalence needs only
`SATHard`, `CookReckhowNP` and `NPClosedUnderReductions`
(`noPolyBounded_iff_npNeCoNP'`). The abstract schema
`NoPolyBoundedProofSystemFor Efficient`, with a free efficiency predicate,
is kept for the abstract results.

## 1. The idea at full strength

Issue #532 Phase 4 ("Systematic elimination of proof strategies") asks to
"Attempt formal proofs → record exact failure points" so that each failure
becomes "Any proof of type X must overcome lemma Y". Part I item 7 says
that "Repeated failure patterns can be formalized and eliminated". The
research log records the core step of resolution: from `P ∨ R` and
`¬P ∨ S` infer `R ∨ S`. The idea has two directions at full strength:

> (toward P = NP) Resolution is a complete, purely syntactic procedure. A
> clever enough resolution strategy refutes every unsatisfiable CNF in
> polynomially many steps, so UNSAT and hence SAT is easy.
>
> (toward P ≠ NP) Prove that every sound and complete proof system needs
> superpolynomially long proofs for some unsatisfiable formulas. By
> Cook–Reckhow this is NP ≠ coNP, which implies P ≠ NP.

## 2. Precise mathematical formulation

* The SAT core is the same as in Idea 21: literals `⟨var, pos⟩`, clauses,
  CNFs, `restrict`, `sat_split`, `VarsIn`, `varsOf` and `size`.
* `Derives φ C` is the least relation closed under three rules.
  * **Axiom:** `C ∈ φ`.
  * **Resolution:** from `⟨v,true⟩ :: C₁` and `⟨v,false⟩ :: C₂`, derive
    `C₁ ++ C₂`.
  * **Weakening:** from `C`, derive any `D` containing every literal of
    `C`. Weakening includes reordering and duplicating literals.
* A proof system for UNSAT (Cook–Reckhow) is modelled as a
  `ProofSystem`. It has a verifier `verify : List Bool → CNF → Bool` that
  is sound (`verify π φ = true → ¬ Satisfiable φ`) and complete (every
  unsatisfiable `φ` has some accepted `π`).
  * Cook and Reckhow also require `verify` to run in polynomial time. In
    the abstract part that requirement is an explicit parameter
    `Efficient`; the machine part below makes it concrete.
* `PolyBounded P` means there are `c, k` such that every unsatisfiable `φ`
  has an accepted proof of length at most `c (size φ + 1)^k`.
* The abstract schema is
  `NoPolyBoundedProofSystemFor Efficient := ∀ P, Efficient P → ¬ PolyBounded P`.
  It quantifies over a free predicate `Efficient`, so it is a schema, not
  an open obligation.

**Machine part (shared model `Complexity`, `Issue532.Machines`).**

* A machine proof system for a language `L` is a `MachineProofSystem L`:
  a `VerifierProgram` together with a polynomial `timeBound` such that
  * `halts : ∀ x π, ∃ t b, t ≤ verifier.timeLimit timeBound x π ∧ verifier.Run x π t b`,
  * `sound : ∀ x π t, verifier.Run x π t true → L x = true`,
  * `complete : ∀ x, L x = true → ∃ π t, verifier.Run x π t true`.
* `P.PolyBounded := ∃ q : Polynomial, ∀ x, L x = true → ∃ π t, |π| ≤ q(|x|) ∧ P.verifier.Run x π t true`.
* `NoPolyBoundedMachineProofSystem L := ∀ P : MachineProofSystem L, ¬ P.PolyBounded`.
* **Open obligation:**
  `NoPolyBoundedUNSATProofSystem := NoPolyBoundedMachineProofSystem (complement SAT)`.
* Known theorems, named hypotheses (never assumed as axioms), except
  `SATInNP`, which is proved (see the last item):
  * `CookReckhowNP := ∀ L, InNP L → ∃ P : MachineProofSystem L, P.PolyBounded`
    (Cook–Reckhow 1979);
  * `NPClosedUnderReductions := ∀ L L', PolyReduces L L' → InNP L' → InNP L`
    (Karp 1972);
  * `SATHard` (the hardness half of Cook–Levin, from the shared layer);
  * `SATInNP` (the membership half of Cook–Levin, from the shared layer) is
    not a hypothesis: it is proved in `SATVerifier.lean` / `SATVerifier.v`
    (`SATVerifier.satInNP`). The unprimed theorems still take it as a
    premise; the primed ones do not.

## 3. What is machine-checked

| Theorem | Informal statement | Lean | Rocq |
| --- | --- | --- | --- |
| `derives_sound` | If `Derives φ C` and `a` satisfies `φ`, then `a` satisfies `C`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `empty_derivable_unsat` | `Derives φ [] → ¬ Satisfiable φ`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `mem_restrict_full`, `clauseHas_false`, `mem_removeVar_of` | Structure of restricted clauses: each comes from a clause without the literal `v = b`, whose literals on `v` are all `v = !b`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `lift` | `Derives (restrict v b φ) D → Derives φ (⟨v, !b⟩ :: D)`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `resolution_complete` | For all `vs φ`, if `VarsIn φ vs` and `φ` is unsatisfiable, then `Derives φ []`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `unsat_iff_derives_empty` | For every CNF: `¬ Satisfiable φ ↔ Derives φ []`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `bounded_certificate` | A polynomially bounded proof system gives `c, k` with `¬ Satisfiable φ ↔ ∃ π, |π| ≤ c (size φ + 1)^k ∧ verify π φ`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `fromDecider`, `fromDecider_bounded` | From an exact decider, the system "accept any proof iff the decider says UNSAT" is sound, complete, and bounded (empty proofs suffice). | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `NoPolyBoundedProofSystemFor` (def) | Schema: no proof system in the class `Efficient` is polynomially bounded. Never assumed. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `unrestricted_obligation_false` | Without an efficiency requirement the obligation is false (use `fromDecider` with the exponential splitting decider `satDec`). | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `lower_bound_excludes_efficient_decider` | If systems built from efficient exact deciders are efficient, then `NoPolyBoundedProofSystemFor Efficient` implies that no exact decider is efficient. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `MachineProofSystem` (structure) | Cook–Reckhow proof system in the machine model: polynomially clocked verifier, sound and complete; `PolyBounded` asks for polynomially short accepted proofs. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `inNP_of_polyBounded` | A polynomially bounded machine proof system for `L` gives `InNP L`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `proofSystem_of_inP` | Every `L ∈ P` has a polynomially bounded machine proof system (empty proofs). | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `NoPolyBoundedMachineProofSystem`, `NoPolyBoundedUNSATProofSystem` (defs) | Open obligation: `complement SAT` has no polynomially bounded machine proof system. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `not_noPolyBounded_of_inP`, `noPolyBounded_of_not_inNP` | The property fails for languages in P and holds for languages outside NP. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `encVerifier_injective`, `verifierLanguage_eq` | Verifier programs have an injective encoding; a proof system's verifier determines its language. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `exists_noPolyBounded` | Non-vacuity: some language has no polynomially bounded machine proof system. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `not_inP_sat_of_noPolyBounded` | `NoPolyBoundedUNSATProofSystem → ¬ InP SAT`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `pNotEqualsNP_of_noPolyBounded` | `SATInNP → NoPolyBoundedUNSATProofSystem → PNotEqualsNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `pNotEqualsNP_of_noPolyBounded'` | `NoPolyBoundedUNSATProofSystem → PNotEqualsNP`, with no `SATInNP` premise (`SATInNP` is proved: `SATVerifier.satInNP`). | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `CookReckhowNP`, `NPClosedUnderReductions` (defs) | Known theorems, not mechanised here: every NP language has a polynomially bounded machine proof system; NP is closed under reductions. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `polyReduces_complement` | A reduction from `L` to `L'` is one from `complement L` to `complement L'`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `npNeCoNP_of_noPolyBounded`, `pNotEqualsNP_via_coNP` | With `SATInNP` and `CookReckhowNP`, the obligation gives `¬ NPEqualsCoNP`, hence `PNotEqualsNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `npNeCoNP_of_noPolyBounded'`, `pNotEqualsNP_via_coNP'` | With `CookReckhowNP` alone (the `SATInNP` premise is dropped, since `SATVerifier.satInNP` proves it), the obligation gives `¬ NPEqualsCoNP`, hence `PNotEqualsNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `npEqualsCoNP_of_polyBounded` | With `SATHard` and `NPClosedUnderReductions`, a polynomially bounded system for `complement SAT` gives `NPEqualsCoNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `noPolyBounded_iff_npNeCoNP` | Under the four named hypotheses, `NoPolyBoundedUNSATProofSystem ↔ ¬ NPEqualsCoNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |
| `noPolyBounded_iff_npNeCoNP'` | Under `SATHard`, `CookReckhowNP` and `NPClosedUnderReductions` (the `SATInNP` premise is dropped, since `SATVerifier.satInNP` proves it), `NoPolyBoundedUNSATProofSystem ↔ ¬ NPEqualsCoNP`. | [Idea23.lean](../lean/Idea23.lean) | [Idea23.v](../rocq/Idea23.v) |

The Rocq names are the Lean names, with these Rocq-specific differences:

* The Rocq constructors are `d_ax`, `d_res` and `d_weak`, where Lean has
  `Derives.ax`, `Derives.res` and `Derives.weak`. The proof-system fields
  are `verify`, `ps_sound` and `ps_complete`, where Lean has `verify`,
  `sound` and `complete`.
* The fields of `MachineProofSystem` are `verifier`, `timeBound`, `halts`,
  `mps_sound` and `mps_complete`. Lean's `MachineProofSystem.PolyBounded`
  is `MachinePolyBounded` in Rocq, because `PolyBounded` is already the
  abstract notion.
* Lean's `verifierLanguage v` is `noncomputable`: it decides the unbounded
  search `∃ π t, v.Run x π t true` with classical logic. The Rocq
  `verifierLanguage v p q` is computable. It searches the proofs of length
  at most `q(|x|)` (`wordsUpTo`) and runs each with the step-bounded
  interpreter `runFor` for `timeLimit v p x π` steps. So Rocq's
  `verifierLanguage_eq` has an extra premise, that `q` bounds the proofs of
  the system, and it is stated pointwise, without function extensionality.
* Lean proves `exists_noPolyBounded` with the Cantor lemma
  `exists_language_not_in_family` over `encVerifier`. Rocq proves the same
  statement by a direct pointwise diagonal, `noProofSystemLanguage`, over
  encoded triples of verifier, clock and proof bound (`encVerifierBounds`,
  with the computable decoder `decVerifierBounds`).
* The Rocq file does not import classical logic or any other axiom.

## 4. Complete argument

**Soundness.** The proof is by induction on the derivation.

* Axioms are true under any `a` that satisfies `φ`.
* For resolution, suppose `a` satisfies `⟨v,true⟩ :: C₁` and
  `⟨v,false⟩ :: C₂`. The two literals on `v` cannot both be true. So one
  of the premises is satisfied inside `C₁` or `C₂`, and hence `C₁ ++ C₂`
  is true.
* Weakening keeps a true literal.

The empty clause is false under every assignment, so deriving it refutes
`φ`.

**Lifting.** Let `D` be derived from `ψ = restrict v b φ`. The proof is by
induction on the derivation.

* *Axiom.* `D = removeVar v C` for some `C ∈ φ` that does not contain
  `v = b`. Every literal of `C` either is on another variable, and so is
  kept in `D`, or is the literal `v = !b`. So `C ⊆ ⟨v,!b⟩ :: D`, and
  weakening from the axiom `C` gives the claim.
* *Resolution on `w`.* By induction we have `⟨v,!b⟩ :: ⟨w,true⟩ :: C₁`
  and `⟨v,!b⟩ :: ⟨w,false⟩ :: C₂`. Reorder both by weakening, resolve on
  `w`, and weaken the result to `⟨v,!b⟩ :: (C₁ ++ C₂)`.
* *Weakening.* Add the extra literal to both sides.

**Completeness.** The proof is by induction on the list `vs` that contains
the variables of `φ`.

* If `vs = []`, every clause of `φ` is empty. An unsatisfiable `φ` is
  non-empty, since `[]` is satisfiable, so `[] ∈ φ` is an axiom.
* If `vs = v :: vs'`, both restrictions are unsatisfiable (`sat_split`)
  and have their variables in `vs'` (`restrict_vars`). By induction both
  derive `[]`. Lifting gives `Derives φ [¬v]` from `restrict v true φ` and
  `Derives φ [v]` from `restrict v false φ`. Resolving them gives `[]`.

The derivation built this way mirrors the splitting tree of Idea 21. Its
tree size can be as large as `2^|vs|`.

*Worked example.* For the four clauses `x∨y, x∨¬y, ¬x∨y, ¬x∨¬y`:

* resolving `x∨y` with `x∨¬y` on `y` gives `x∨x`, which weakens to `x`;
* resolving `¬x∨y` with `¬x∨¬y` gives `¬x`;
* resolving `x` with `¬x` gives the empty clause.

That is three resolution steps. In the formal system, where the pivot
literal must come first, each step is preceded by weakening steps that
reorder the literals.

**Proof systems.** If `P` is polynomially bounded, then UNSAT is exactly
the set of formulas having an accepted proof of length at most
`c (size + 1)^k` (`bounded_certificate`). When `verify` is polynomial time,
this places UNSAT in NP. Because UNSAT is coNP-complete, it gives
NP = coNP. The Cook–Reckhow theorem is this direction together with its
converse: NP = coNP implies that a polynomially bounded proof system
exists.

Conversely, an exact decider yields a proof system with empty proofs
(`fromDecider_bounded`). So if a polynomial-time exact decider existed,
and the verifier "run the decider" counts as efficient, the obligation
would fail. This is `lower_bound_excludes_efficient_decider` read
contrapositively. Without any efficiency requirement the obligation is
simply false (`unrestricted_obligation_false`). This is why the
efficiency parameter is essential and cannot be dropped.

**Machine part.** In the shared model the efficiency requirement is a
polynomial clock on a `VerifierProgram`. If `P` is polynomially bounded,
the proof bound `q` is a certificate bound, and the clock together with the
determinism of runs bounds the accepting run, so `L ∈ NP`
(`inNP_of_polyBounded`). Conversely a polynomial-time decider for `L`
gives a system that ignores the proof (`proofSystem_of_inP`). Applied to
`complement SAT`: if SAT were in P, then UNSAT would be in P and would have
a system with empty proofs, so the obligation implies `¬ InP SAT`
(`not_inP_sat_of_noPolyBounded`), and with SAT ∈ NP it implies P ≠ NP
(`pNotEqualsNP_of_noPolyBounded`). With Cook–Reckhow, a bounded system
exists for every NP language, so the obligation puts UNSAT outside NP and
gives NP ≠ coNP (`npNeCoNP_of_noPolyBounded`). Conversely, a bounded system
for UNSAT puts UNSAT in NP; since every coNP language reduces to UNSAT
(complement of the Cook–Levin reduction, `polyReduces_complement`) and NP
is closed under reductions, coNP ⊆ NP and so NP = coNP
(`npEqualsCoNP_of_polyBounded`). The statement is not vacuous: by Cantor's
argument over encoded verifiers, some language has no machine proof system
at all (`exists_noPolyBounded`).

## 5. Known results and literature

* J. A. Robinson, "A machine-oriented logic based on the resolution
  principle", *Journal of the ACM* 12(1) (1965).
* S. A. Cook and R. A. Reckhow, "The relative efficiency of propositional
  proof systems", *Journal of Symbolic Logic* 44(1) (1979). A
  polynomially bounded proof system exists iff NP = coNP.
* A. Haken, "The intractability of resolution", *Theoretical Computer
  Science* 39 (1985). Resolution refutations of the pigeonhole formulas
  `PHP^{n+1}_n` have size `2^{Ω(n)}`.
* A. Urquhart, "Hard examples for resolution", *Journal of the ACM* 34(1)
  (1987). Tseitin formulas on expanders.
* V. Chvátal and E. Szemerédi, "Many hard examples for resolution",
  *Journal of the ACM* 35(4) (1988). Random 3-CNF.
* E. Ben-Sasson and A. Wigderson, "Short proofs are narrow — resolution
  made simple", *Journal of the ACM* 48(2) (2001). This is the size–width
  relation, which gives uniform proofs of the lower bounds above.

What is **not** formalized:

* Proof size for resolution. Only derivability is modelled; there is no
  size-indexed derivation relation.
* All the lower bounds listed above.
* The encoding of resolution as a Cook–Reckhow proof system on bit
  strings.
* The meaning of `Efficient` in the abstract part. The machine part fixes
  it as a polynomial clock on a verifier of the shared model, but the link
  between the abstract CNF type and the bit-string CNF encoding of `SAT` is
  not formalized.
* The Cook–Reckhow direction "NP ⊆ bounded proof systems"
  (`CookReckhowNP`), closure of NP under reductions
  (`NPClosedUnderReductions`) and the hardness half of Cook–Levin
  (`SATHard`). These are named hypotheses. The membership half (`SATInNP`)
  is proved in `SATVerifier` (`SATVerifier.satInNP`). The direction "bounded system ⇒
  NP" is proved (`inNP_of_polyBounded`).

## 6. How far the idea can be pushed toward P vs NP

* **Toward P = NP: refuted.** Every resolution-based algorithm produces a
  resolution refutation on unsatisfiable inputs. This includes DPLL and
  CDCL (see Idea 21). Haken's theorem makes every such algorithm
  exponential on the pigeonhole formulas. This is a published
  unconditional theorem, about this algorithm family only.
* **Toward P ≠ NP: developed to an open obligation.**
  **Exact remaining obligation:** `NoPolyBoundedUNSATProofSystem`, that is,
  `∀ P : MachineProofSystem (complement SAT), ¬ P.PolyBounded`. The files
  prove `NoPolyBoundedUNSATProofSystem → ¬ InP SAT`, and, since `SATInNP`
  is proved in `SATVerifier`, `NoPolyBoundedUNSATProofSystem → PNotEqualsNP`
  with no other premise (`pNotEqualsNP_of_noPolyBounded'`). With the named
  hypotheses `SATHard`, `CookReckhowNP` and `NPClosedUnderReductions` it is
  equivalent to `¬ NPEqualsCoNP` (`noPolyBounded_iff_npNeCoNP'`; the
  unprimed `noPolyBounded_iff_npNeCoNP` also takes `SATInNP`). This is stronger than P ≠ NP as far as
  is known, because P = NP implies NP = coNP but the converse is open.
  `lower_bound_excludes_efficient_decider` is the abstract skeleton of
  "NP ≠ coNP implies P ≠ NP".
* **Where the program stands.** Superpolynomial lower bounds are known for
  resolution, cutting planes, bounded-depth Frege and several algebraic
  systems. No superpolynomial lower bound is known for Frege or extended
  Frege systems.
* **Barriers.** Lower bounds for strong proof systems face obstacles
  analogous to those for circuits. Known lower-bound methods for a proof
  system often rest on circuit lower bounds for a corresponding circuit
  class (feasible interpolation, restriction methods). Feasible
  interpolation is known to fail for extended Frege and for Frege under
  cryptographic assumptions (Krajíček–Pudlák 1998; Bonet–Pitassi–Raz
  2000). Lower bounds for Frege and extended Frege are widely expected to
  be at least as hard as circuit lower bounds for classes such as `NC¹`
  and `P/poly`, but this is a heuristic analogy, not a proved barrier
  theorem. Relativization is not the relevant barrier here.

## 7. Failure modes this idea catches

* **Family 20 (structure theorem from one class).** Exponential lower bounds
  for resolution do not show that SAT needs exponential time. They show it
  only for resolution-based algorithms.
* **Family 14 (ignoring barriers).** A claimed lower bound for all proof
  systems must at least exceed the known resolution and bounded-depth
  Frege techniques.
* **Family 15 (verification vs certificates).** "UNSAT has no short
  certificates" is a statement about all efficient verifiers.
  `unrestricted_obligation_false` shows that without the efficiency
  requirement it is false.
* **Family 1 (assuming a lower bound).** Stating "no proof system is
  polynomially bounded" as a hypothesis and deriving P ≠ NP from it proves
  nothing new. Here it is only the `def` `NoPolyBoundedUNSATProofSystem`
(and the schema `NoPolyBoundedProofSystemFor`), never assumed; the proved
statements are the conditionals out of it.

See [COMMON_ERRORS.md](../../../attempts/COMMON_ERRORS.md).

## 8. Reproduction

From the repository root:

```sh
lake env lean proofs/experiments/issue532/lean/Idea23.lean
rocq compile -Q . '' proofs/experiments/issue532/rocq/Idea23.v
rm -f proofs/experiments/issue532/rocq/Idea23.vo proofs/experiments/issue532/rocq/Idea23.vok \
      proofs/experiments/issue532/rocq/Idea23.vos proofs/experiments/issue532/rocq/Idea23.glob \
      proofs/experiments/issue532/rocq/.Idea23.aux
```

Both commands print nothing on success.
