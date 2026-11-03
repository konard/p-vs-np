# The formal statement of P vs NP in this repository

This file states the problem from the Clay statement down to the formal
target and the acceptance criterion. It follows the seven items of
[#628](https://github.com/konard/p-vs-np/issues/628). Every declaration it
names on `main` is listed in the claims block at the end, and every
`file:line` written next to a declaration name is checked by
`python3 scripts/check_formal_statement.py` (see
[Checked claims](#checked-claims)). Names that exist only in an unmerged PR or
in another repository are marked as such and are not checked.

**Status: the repository has not proved P = NP or P ≠ NP.** No theorem in
`scripts/proof_status.json` has type `PEqualsNP` or `PNotEqualsNP` without a
hypothesis. (Checked on 2026-11-03 by reading the signatures of the 78 Lean
entries. The row `no-unconditional-target` of CLAIMS.md checks it with
`scripts/check_claims.py`; `scripts/check_formal_statement.py` does not.)

The list of unproved premises is in [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md).
This file does not repeat it.

## Statement-only summary

The target, copied from the Lean definitions in source order. Each comment
line gives the source lines of the code lines below it. The script checks
that the code lines occur in `Complexity.lean` in this order and that each
group starts and ends at the lines its comment gives. Lines between the
groups are omitted.

<!-- verbatim-from: proofs/complexity/lean/Complexity.lean -->
```lean
-- proofs/complexity/lean/Complexity.lean:92-93 the only notion of polynomial
def Polynomial.eval (p : Polynomial) (n : Nat) : Nat :=
  p.coefficient * (n + 1) ^ p.degree
-- :181 ClassP: one machine, one bound, every input
  terminates : ∀ x, ∃ t b, t ≤ bound.eval x.length ∧ Run machine (initial x) t b
-- :207-209 ClassNP: a short certificate, checked in polynomial time
  correct : ∀ x, language x = true ↔
    ∃ cert t, cert.length ≤ certBound.eval x.length ∧
      t ≤ verifier.timeLimit timeBound x cert ∧ verifier.Run x cert t true
-- :211-218 the target
def InP (language : Language) : Prop :=
  ∃ p : ClassP, p.language = language
def InNP (language : Language) : Prop :=
  ∃ np : ClassNP, np.language = language
def PEqualsNP : Prop := ∀ language, InNP language → InP language
def PNotEqualsNP : Prop := ¬PEqualsNP
```

## 1. The question

The Clay Mathematics Institute statement is in [pvsnp.pdf](pvsnp.pdf)
(S. Cook, "The P versus NP problem"). It asks whether every language whose
members have short certificates that can be checked in polynomial time can
also be decided in polynomial time.

The formal target is the same proposition in three provers:

| prover | file | declarations |
| --- | --- | --- |
| Lean | `proofs/complexity/lean/Complexity.lean` | `PEqualsNP` (`proofs/complexity/lean/Complexity.lean:217`), `PNotEqualsNP` (`proofs/complexity/lean/Complexity.lean:218`) |
| Rocq | `proofs/complexity/rocq/Complexity.v` | `PEqualsNP` (`proofs/complexity/rocq/Complexity.v:204`), `PNotEqualsNP` (`proofs/complexity/rocq/Complexity.v:205`) |
| Agda | `proofs/complexity/agda/Complexity.agda` | `PEqualsNP` (`proofs/complexity/agda/Complexity.agda:193`), `PNotEqualsNP` (`proofs/complexity/agda/Complexity.agda:196`) |

`PEqualsNP` is stated as the inclusion NP ⊆ P. The other inclusion is
proved: `pSubsetNP` (`proofs/complexity/lean/Complexity.lean:240`), with
twins `pSubsetNP` (`proofs/complexity/rocq/Complexity.v:225`) and
`pSubsetNP` (`proofs/complexity/agda/Complexity.agda:226`). It uses
`ClassP.toNP` (`proofs/complexity/lean/Complexity.lean:221`), a verifier
that ignores the certificate. So the target is equivalent to equality of the
classes: `npSubsetP_iff_classes_equal`
(`proofs/experiments/issue8/lean/NPSubsetP.lean:49`) proves
`NPSubsetP ↔ ∀ L, InP L ↔ InNP L`, and `npSubsetP_iff_pEqualsNP`
(`proofs/experiments/issue8/lean/NPSubsetP.lean:46`) identifies `NPSubsetP`
with `PEqualsNP`. In Agda the definitions live in `Set` (propositions as
types).

The SAT language used by every bridge is `SAT`
(`proofs/experiments/issue532/lean/Machines.lean:1004`), with Rocq twin
`SAT` (`proofs/experiments/issue532/rocq/Machines.v:1276`). It is proved to
be in NP: `satInNP` (`proofs/experiments/issue532/lean/SATVerifier.lean:816`),
twin `satInNP` (`proofs/experiments/issue532/rocq/SATVerifier.v:855`).

## 2. Modeling choices

Each choice is a decision. A reader must accept all of them for
`PEqualsNP` to mean the Clay question. All are in
`proofs/complexity/lean/Complexity.lean` unless stated otherwise.

1. **Words are lists of bits; a language is a total Boolean function.**
   `Word` (`proofs/complexity/lean/Complexity.lean:15`) is `List Bool`;
   `Language` (`proofs/complexity/lean/Complexity.lean:16`) is
   `Word → Bool`.
   *Why it matters:* every language has a definite answer on every word, so
   the only open question is the cost of computing it. openai/math uses
   `List Bool → Prop` instead (see section 3). The two agree on decidable
   languages, and every language in P or NP is decidable.
2. **One tape, four symbols.** `Symbol`
   (`proofs/complexity/lean/Complexity.lean:18`) is blank, zero, one,
   separator.
   *Why it matters:* the alphabet is finite and fixed. A machine whose tape
   alphabet may be infinite can pack unbounded data into one cell, and then
   step counts no longer measure work. openai/math adds exactly this guard to
   Mathlib's `TM2ComputableInPolyTime`: `FiniteAlphabet M := ∀ k, Finite (M.Γ k)`
   (openai/math at commit `4eaee87`,
   [`lean/ComparatorChallenges/VertexCover.lean:112`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/VertexCover.lean#L112)). The audit
   in PR #639 (unmerged) records the Mathlib gap it closes: otherwise only the
   input alphabet must be finite. Here finiteness holds by construction. The
   single tape costs at most a polynomial factor against multi-tape machines,
   but that equivalence is not mechanized (section 3).
3. **A finite instruction table; a missing row rejects.** `Machine`
   (`proofs/complexity/lean/Complexity.lean:43`) is a `List (List Instruction)`.
   `Machine.instruction` (`proofs/complexity/lean/Complexity.lean:64`)
   returns `.halt false` when the row is missing.
   *Why it matters:* a machine is finite data. It cannot be an arbitrary Lean
   function, which could hide the language itself in the transition rule.
   That loophole made most early obligations vacuous (section 7).
4. **Halting is charged one step.** `Run`
   (`proofs/complexity/lean/Complexity.lean:82`) is an inductive relation
   with an exact step count, and its `halt` case has count 1. `step`
   (`proofs/complexity/lean/Complexity.lean:77`) executes one table entry.
   *Why it matters:* no run takes zero time, and the count is the number of
   table entries executed. Time bounds are statements about `Run`, not about
   Lean evaluation.
5. **Polynomials are `c·(n+1)^k`.** `Polynomial.eval`
   (`proofs/complexity/lean/Complexity.lean:92`).
   *Why it matters:* the `+1` makes the bound nonzero at input length 0 when
   `c ≥ 1`. `PolynomiallyBounded`
   (`proofs/complexity/lean/Complexity.lean:96`) is defined by this form,
   and `polynomiallyBounded_iff_polynomial`
   (`proofs/complexity/lean/Complexity.lean:99`) restates it with a
   `Polynomial`. That the form matches the textbook notion (every polynomial
   with natural coefficients is bounded by some `c·(n+1)^k`) is a standard
   fact that is not stated in Lean.
6. **P needs one machine and one bound for all inputs.** `ClassP`
   (`proofs/complexity/lean/Complexity.lean:177`): every input terminates
   within `bound.eval |x|` steps, and every run gives the right answer.
   *Why it matters:* the bound comes before the input. Per-input or
   per-length machines do not count (see `per_machine_form_holds` in section 7).
7. **NP uses a verifier program on a paired input.** `VerifierProgram`
   (`proofs/complexity/lean/Complexity.lean:184`) has two constructors:
   `ignoreCertificate` and `paired`. The paired verifier reads
   `pairedInput` (`proofs/complexity/lean/Complexity.lean:61`), that is
   `input ++ [separator] ++ certificate`. `VerifierProgram.timeLimit`
   (`proofs/complexity/lean/Complexity.lean:194`) is `p.eval |x|` for
   `ignoreCertificate` and `p.eval (|x| + |cert| + 1)` for `paired`.
   `ClassNP` (`proofs/complexity/lean/Complexity.lean:200`)
   bounds the certificate by a polynomial in `|x|`.
   *Why it matters:* the separator lets the machine find the certificate.
   The certificate bound makes the total time polynomial in `|x|`. The
   `ignoreCertificate` constructor makes P ⊆ NP immediate.
8. **SAT is brute force over a total decoder.** `SAT`
   (`proofs/experiments/issue532/lean/Machines.lean:1004`) is
   `bruteForce (numVars (decode w)) (decode w)`. `decode`
   (`proofs/experiments/issue532/lean/Machines.lean:967`) maps every word to
   some CNF, dropping malformed tails. `bruteForce`
   (`proofs/experiments/issue532/lean/Machines.lean:888`) is the
   specification, proved correct by `sat_iff`
   (`proofs/experiments/issue532/lean/Machines.lean:1006`; compiled on
   `main`, not certified).
   *Why it matters:* SAT is a language on all words, with no separate
   "invalid input" case. The exponential definition is a specification, not
   a proposed algorithm.
9. **CNF encoding with unary variable indices.** `encodeCNF`
   (`proofs/experiments/issue532/lean/Machines.lean:957`) writes each
   literal as `ticks var ++ [false, pos]` and ends each clause with
   `[true, false]`. `decode_encode`
   (`proofs/experiments/issue532/lean/Machines.lean:987`) proves the
   round trip (compiled on `main`, not certified).
   *Why it matters:* the encoding length is polynomial in the formula size
   with unary indices. Changing the encoding changes concrete degrees. That P
   and NP do not depend on the encoding is a known fact that is not
   mechanized (section 3).
10. **Reductions are machine-computed.** `Computes`
    (`proofs/experiments/issue532/lean/Machines.lean:318`) and `PolyReduces`
    (`proofs/experiments/issue532/lean/Machines.lean:325`) require a
    `Machine` with a polynomial `Run` bound. `NPHard`
    (`proofs/experiments/issue532/lean/Machines.lean:600`) and `NPComplete`
    (`proofs/experiments/issue532/lean/Machines.lean:602`) use them.
    *Why it matters:* a reduction that is only a Lean function would make
    hardness trivial. `SATHard` is stated with these reductions.

## 3. Known theorems not mechanized

### In this repository

Each item below is a standard theorem that relates this model to the
textbook one. Each is *not mechanized* on `main`. The full list of named
hypotheses, with dependents and status, is
[proofs/HYPOTHESES.md](proofs/HYPOTHESES.md), tracked in
[#629](https://github.com/konard/p-vs-np/issues/629).

- **Polynomial equivalence with multi-tape and RAM models.** *Not
  mechanized,* and assumed. It is not yet named as a definition; it has a
  row with a proposed name, `ModelEquivalence`, in
  [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md). It matters for any port of
  a published algorithm or lower bound whose cost is stated for another
  model.
- **Invariance of P and NP under the choice of encoding.** *Not
  mechanized,* and assumed. Not named as a definition either; its row has
  the proposed name `EncodingInvariance`.
- **Cook–Levin hardness.** `SATHard`
  (`proofs/experiments/issue532/lean/Machines.lean:1027`), Rocq twin
  `SATHard` (`proofs/experiments/issue532/rocq/Machines.v:1300`). *Not
  mechanized.* Tracked in [#624](https://github.com/konard/p-vs-np/issues/624).
  The first slice is on `main`: `boundedAccept_iff_run`
  (`proofs/experiments/issue568/lean/Tableau.lean:145`). PR #630 (open, not
  draft, merge blocked) adds `tableauCNF_iff` and
  `tableauCNF_encoded_size`, but not `SATHard`. (On 2026-11-03, 4 of its 8
  CI checks failed.)
- **P ⊆ P/poly.** `PSubsetPPoly`
  (`proofs/experiments/issue532/lean/Circuits.lean:109`). *Not mechanized
  on `main`.* Tracked in [#626](https://github.com/konard/p-vs-np/issues/626).
  PR #632 (open, CI passing, unmerged) proves it as `pSubsetPPoly`.
- **NP is closed under polynomial reductions.** `NPClosedUnderReductions`
  (`proofs/experiments/issue532/lean/Idea23.lean:683`). *Not mechanized.*
- **CircuitSAT is in NP.** `CircuitSATInNP`
  (`proofs/experiments/issue532/lean/Idea41.lean:405`). *Not mechanized on
  `main`.* Tracked in [#625](https://github.com/konard/p-vs-np/issues/625).
  PR #631 (open, CI passing, unmerged) proves it as `circuitSATInNP`.

### Outside this repository

Other formalizations of P and NP exist. None of their theorems transfers to
this repository by name, because each uses a different machine model. Using
one would be common-error family 11 ("Using undefined, nonstandard, or
incompatible formal definitions", `proofs/attempts/COMMON_ERRORS.md`). A
transfer needs a mechanized simulation between the models.

- **openai/math** (Lean, Mathlib). Machines are
  `Turing.TM2ComputableInPolyTime` with `FiniteAlphabet`. Languages are
  `List Bool → Prop`. `PEqualsNP := ClassP = ClassNP`
  ([`lean/ComparatorChallenges/BinPackingGap.lean:326`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/BinPackingGap.lean#L326)
  in that repository, at commit `4eaee87`).
- **Gäher and Kunze** (Coq, ITP 2021). Cook–Levin for the call-by-value
  λ-calculus L. Mentioned in `proofs/experiments/issue568/README.md`, which
  notes the different setup.
- **Isabelle AFP `Cook_Levin`** (Balbach, 2023). Cook–Levin for multi-tape
  Turing machines.
- **anthropics/formal-math, `eth/`** (Lean, Mathlib). `Turing.TM2` machines.
  The audit in PR #639 (unmerged) records that the bridge from TM2 to a word
  RAM is given in prose, not in Lean.

**The October 2026 ETH claims.** On 26 and 27 October 2026, openai/math
(family 378) and anthropics/formal-math (`eth/`) each claimed a
deterministic `2^{O_k(n·polyloglog n/√log n)}` k-SAT algorithm whose
correctness and running time are checked in Lean, each in its own model. If
correct, such an algorithm refutes the Exponential Time Hypothesis. For
openai/math that step is argued in prose (its Lean code does not define
ETH); anthropics/formal-math defines ETH over Mathlib `FinTM2` and proves
`MainResults.ethIsFalse` with the standard axioms, in its own model. These claims
are recent and not peer-reviewed. For the openai/math claim, a review group
of Impagliazzo, Paturi and Williams was announced (source: the PR #639 case
study, unmerged).
They do not settle P vs NP. ETH implies P ≠ NP (PR #639 proves
`pNotEqualsNP_of_eth` in the shared model; unmerged), so ETH is at least as
strong as P ≠ NP; whether it is strictly stronger is unknown. A refutation
of ETH removes one sufficient condition for P ≠ NP and proves neither answer.

## 4. What counts as solved

The rule, verbatim from item 4 of #628:

> A theorem of `Complexity.PEqualsNP` or `Complexity.PNotEqualsNP` in both
> Lean and Rocq, listed in `scripts/proof_status.json`, with assumption
> reports showing only `propext`, `Classical.choice`, `Quot.sound` (Lean) and
> at most `Classical_Prop.classic` (Rocq); no explicit theorem hypotheses;
> plus the model-fidelity theorems of item 3 or an explicit statement that
> they remain assumed. State that a theorem with a `SATHard`-style argument is
> conditional, not a solution.

So a theorem with a `SATHard`-style argument is conditional, not a solution.
For example `pEqualsNP_of_inP_sat`
(`proofs/experiments/issue532/lean/Machines.lean:1035`) is certified, but it
takes `SATHard` as an argument, and `Print Assumptions` cannot see that.

The disjunction `P_vs_NP_is_decidable`
(`proofs/p_vs_np_decidable/lean/PvsNPDecidable.lean:18`), Rocq twin
`P_vs_NP_is_decidable` (`proofs/p_vs_np_decidable/rocq/PvsNPDecidable.v:9`),
is certified. It is excluded middle. It decides nothing.

The close criterion of #567 and #568 is the same rule applied to one side,
in checkable form: a theorem in both Lean and Rocq, listed in
`scripts/proof_status.json`, whose type is exactly `Complexity.PNotEqualsNP`
(for #567) or `Complexity.PEqualsNP` (for #568) with no arguments. The PR
shows this by the `#check` (Lean) and `Check` (Rocq) output of the theorem,
and by `#print axioms` / `Print Assumptions` output that lists only the
allowed axioms above.

## 5. The result graph

Each row is a theorem that compiles on `main`. It connects a statement to
the target or to another statement. The premise column lists the named
hypotheses it takes. `certified` says whether `scripts/proof_status.json`
lists the Lean theorem; a compiled theorem that is not listed has no
assumption report. Status is the status of the premises.

| edge (from → to) | theorem | file:line | premise | certified | status |
| --- | --- | --- | --- | --- | --- |
| `InP SAT` → `PEqualsNP` | `pEqualsNP_of_inP_sat` | `proofs/experiments/issue532/lean/Machines.lean:1035` | `SATHard` | yes | premise open; PR #630 unmerged |
| `PEqualsNP` → `InP SAT` | `inP_sat_of_pEqualsNP'` | `proofs/experiments/issue532/lean/SATVerifier.lean:819` | none (uses `satInNP`) | yes | unconditional |
| `InP SAT` ↔ `PEqualsNP` | `inP_sat_iff_of_hard` | `proofs/experiments/issue532/lean/SATVerifier.lean:826` | `SATHard` | yes | premise open; PR #630 unmerged |
| `∀ m p, ∃ x, clockCheck m p x = false` → `PNotEqualsNP` | `pNotEqualsNP_of_pi2` | `proofs/experiments/issue7/lean/ClockedSAT.lean:177` | none (uses `satInNP` inside) | yes | unconditional |
| `PNotEqualsNP` → `∀ m p, ∃ x, clockCheck m p x = false` | `pi2_of_pNotEqualsNP` | `proofs/experiments/issue7/lean/ClockedSAT.lean:182` | `SATHard` | yes | premise open; PR #630 unmerged |
| `SuperpolyLowerBound SAT` (that is, `¬ InPPoly SAT`) → `PNotEqualsNP` | `pNotEqualsNP_of_superpoly_sat` | `proofs/experiments/issue532/lean/Circuits.lean:118` | `SATInNP`, `PSubsetPPoly` | no | `SATInNP` discharged on main; `PSubsetPPoly` discharged in PR #632 (unmerged) |
| `¬ NPSubsetPPoly` → `NPNotSubsetP` | `npNotSubsetP_of_not_npSubsetPPoly` | `proofs/experiments/issue10/lean/NPNotSubsetP.lean:255` | `PSubsetPPoly` | yes | discharged in PR #632 (unmerged) |
| `¬ FastCircuitSAT` → `PNotEqualsNP` | `pNotEqualsNP_of_not_fastCircuitSAT` | `proofs/experiments/issue532/lean/Idea41.lean:717` | `CircuitSATInNP` | no | discharged in PR #631 (unmerged) |
| `FastCircuitSAT` → `¬ NEXPSubsetPPoly` | `williams_method` | `proofs/experiments/issue532/lean/Idea41.lean:504` | `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup` | no | all open |
| `NEXPSubsetPPoly` → `PNotEqualsNP` | `pNotEqualsNP_of_nexpSubsetPPoly` | `proofs/experiments/issue532/lean/Idea41.lean:722` | `CircuitSATInNP`, `NTimeHierarchy`, `EasyWitnessLemma`, `WilliamsSpeedup` | no | one in PR #631, three open |
| `LazyDiagonalSimulation` → `NTimeHierarchy` | `nTimeHierarchy_of_lazyDiagonal` | `proofs/experiments/issue532/lean/Idea41.lean:579` | none (the source is itself open) | no | `LazyDiagonalSimulation` open |
| `Nonempty Candidate` ↔ `PEqualsNP` | `candidate_iff_pEqualsNP` | `proofs/experiments/issue609/lean/PEqualsNPAttempt.lean:46` | `SATHard` | yes | premise open; PR #630 unmerged |

The same graph as a picture. Labels on arrows are premises. `[open]`,
`[PR #N]` and `[main]` give their status.

```
                 SATHard [open, PR #630]
   InP SAT  ----------------------------------->  PEqualsNP
            <-----------------------------------
                 none (satInNP [main])

   (forall m p, exists x, clockCheck m p x = false)
            ------------- none ------------------>  PNotEqualsNP
            <------------ SATHard [open] ---------

   SuperpolyLowerBound SAT
            ---- PSubsetPPoly [PR #632] ---------->  PNotEqualsNP

   not FastCircuitSAT
            ---- CircuitSATInNP [PR #631] -------->  PNotEqualsNP
                                                         ^
   not NEXPSubsetPPoly <---- NTimeHierarchy [open] ----  |
           ^                 EasyWitnessLemma [open]     |
           |                 WilliamsSpeedup [open]      |
     FastCircuitSAT                                      |
                                                         |
   NEXPSubsetPPoly ---- CircuitSATInNP + the three ------+

   LazyDiagonalSimulation [open] ---- none ---->  NTimeHierarchy
```

Reading the graph:

- The Π⁰₂ edge to `PNotEqualsNP` needs no premise. Its source is a
  statement about every machine and every clock. It is as hard as the target.
- Once #624, #625 and #626 are done, the edges into the target have no
  bridge premise left, except the Williams route. What remains on every edge
  is the open source statement itself (for example `InP SAT`, or a circuit
  lower bound for SAT).
- More conditional edges, one per idea, are listed in the dependents column
  of [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md).

## 6. The two tracks and the frontier

Both tracks share one model, one SAT and one set of bridges.

**NP ⊆ P track, [#568](https://github.com/konard/p-vs-np/issues/568)
(open).** Target `PEqualsNP`. Milestones, as listed in #568:

1. [#624](https://github.com/konard/p-vs-np/issues/624): prove `SATHard`.
   Slice 1 is on `main` (`localTrace_iff_run`
   (`proofs/experiments/issue568/lean/Tableau.lean:131`),
   `boundedAccept_iff_run`, `bounded_initial_span`
   (`proofs/experiments/issue568/lean/Tableau.lean:86`)). PR #630
   (unmerged) adds part of slices 2 to 4. It does not prove `SATHard`.
2. Milestone B: DPLL as a `Complexity.Machine` with a proved `Run` bound.
   The functional version exists: `dpll_correct`
   (`proofs/experiments/issue8/lean/NPSubsetP.lean:290`) and `dpllSAT_calls_le`
   (`proofs/experiments/issue8/lean/NPSubsetP.lean:404`), which bounds the
   calls by `2^(len w + 1)`. There is no machine version yet.
3. Milestone C: one falsifiable improvement. Not started, according to the
   latest status comment on #568.

Frontier: a `Complexity.Machine` that decides `SAT` within a polynomial
bound (`PolySATDecider`, an open obligation), plus `SATHard`.

**NP ⊈ P track, [#567](https://github.com/konard/p-vs-np/issues/567)
(open).** Target `PNotEqualsNP`. Milestones, as listed in #567:

1. [#625](https://github.com/konard/p-vs-np/issues/625): `CircuitSATInNP`.
   PR #631, unmerged.
2. [#626](https://github.com/konard/p-vs-np/issues/626): `PSubsetPPoly`.
   PR #632, unmerged.
3. N3: all-size, scope-correct results from candidate failures. One scoped
   result exists: `coarseKey_not_satisfiability_complete`
   (`proofs/experiments/issue567/lean/ResidualKey.lean:81`).

Frontier: a superpolynomial lower bound for an NP language against
machines (`SATMachinesSuperpolynomial`) or against circuits
(`SATNotInPPoly`, `ExplicitNPLowerBound`), or the Williams ingredients
together with `¬ FastCircuitSAT`. All are open.

The close rule for both issues is in section 4. Milestone PRs use "Refs #567"
or "Refs #568", not "Fixes".

## 7. Proved wrong: do not retry

- [proofs/attempts/COMMON_ERRORS.md](proofs/attempts/COMMON_ERRORS.md)
  groups the errors of past published attempts into 20 families. Read the
  families before proposing a route. Family 11 (incompatible formal
  definitions) applies to any import from another model.
- [proofs/experiments/issue532/RESEARCH_LOG.md](proofs/experiments/issue532/RESEARCH_LOG.md)
  gives each of the 41 ideas one of four verdicts: "Refuted as a route
  (general theorem)" (15 ideas), "Refuted in full strength (published
  theorem) + formal core" (6), "Developed to an open obligation (conditional
  theorem proved)" (9), and "Correct tool, insufficient alone (general
  theorem proved)" (11). Do not retry an idea in the first two classes
  without a new ingredient that its refutation does not cover.
- [experiments/issue532_vacuity/REPORT.md](experiments/issue532_vacuity/REPORT.md):
  before the shared machine model, "Of the 30 ideas that define an
  obligation, 25 are vacuous as stated." A new obligation must use
  `Complexity.Machine` and `Run`, or it may be vacuous in the same way.

Specific results that close a door, all compiled on `main` (certified
unless marked):

- `per_machine_form_holds`
  (`proofs/experiments/issue7/lean/ClockedSAT.lean:211`): for every machine
  and clock there is an NP language that the machine does not decide in
  time. The language depends on the machine, so this does not give
  P ≠ NP. The quantifier order matters.
- `rejectAll_defeated` (`proofs/experiments/issue7/lean/ClockedSAT.lean:244`):
  one instance of the Π⁰₂ statement, for one machine. Checking machines one
  at a time does not prove the Π⁰₂ statement.
- `calls_bound_not_polynomial`
  (`proofs/experiments/issue8/lean/NPSubsetP.lean:409`): the proved DPLL call
  bound is not polynomial. Its docstring says it is not a lower bound for SAT.
- `coarseKey_not_satisfiability_complete`
  (`proofs/experiments/issue567/lean/ResidualKey.lean:81`): an answer cache
  keyed only by (number of variables, number of clauses, encoded length) is
  unsound.
- `bgs_no_uniform_answer` (`proofs/experiments/issue532/lean/Idea16.lean:582`;
  not certified): given the oracle results of Baker, Gill and Solovay (the
  named hypotheses `BGSCollapse` and `BGSSeparation`), neither answer to
  P vs NP holds relative to every oracle, so no argument that holds
  relative to every oracle settles P vs NP. `separation_refutes_uniform`
  (`proofs/experiments/issue609/lean/KnownBarriers.lean:40`) is a separate,
  abstract schema over any oracle type and any pair of classes: a separating
  oracle at which a technique applies refutes a uniform proof of equality by
  that technique. It does not mention BGS, and the BGS theorem does not use
  it.
- `diag_not_inP` (`proofs/experiments/issue532/lean/Machines.lean:719`; not
  certified): no machine decides `Diag`
  (`proofs/experiments/issue532/lean/Machines.lean:715`) in any time bound.
  Plain diagonalization of this kind leaves the decidable world, so it says
  nothing about languages in NP.

## Checked claims

Run from the repository root:

```bash
python3 -I scripts/check_formal_statement.py
python3 -I scripts/check_formal_statement.py --write-lines   # refresh line numbers
python3 -I scripts/check_formal_statement.py --strict        # warnings fail too
```

The script uses only the Python standard library and reads source text; it
builds nothing. CI runs it with its tests in the `detect-changes` job of
`.github/workflows/verification.yml` (added 2026-11-03, not yet pushed). It
checks:

- every `path::Name` line of the claims block below: the file exists and
  declares `Name`;
- every location written as a declaration name followed by
  `(path:line)`, and every table row with a name cell followed by a
  `path:line` cell: the line declares that name. A drift of up to three lines
  is a warning; more is a failure;
- the summary box: its code lines occur in `Complexity.lean` in the same
  order, and each group starts and ends at the lines its comment gives;
- the result graph: the named hypotheses in the theorem's signature, outside
  the edge cell, are exactly those of the premise column, and `certified`
  agrees with `scripts/proof_status.json`;
- prose: a sentence that locates a theorem and calls it "certified", or
  "proved" without "not certified", needs a `scripts/proof_status.json`
  entry for it;
- the table of [proofs/HYPOTHESES.md](proofs/HYPOTHESES.md): columns,
  classes, status values, that each row names a Prop definition, the
  dependents column, and that every marked hypothesis under `proofs/` has a
  row there (details in [scripts/README.md](scripts/README.md)).

It does not check prose otherwise: PR and issue states, counts, verdicts,
the wording of statements, and quotations were checked by hand on
2026-11-03 and can go stale. Premises are found by reading signature text,
not by Lean, so a premise hidden behind another definition is not seen.

```claims
# The target (section 1)
proofs/complexity/lean/Complexity.lean::Word
proofs/complexity/lean/Complexity.lean::Language
proofs/complexity/lean/Complexity.lean::Symbol
proofs/complexity/lean/Complexity.lean::Machine
proofs/complexity/lean/Complexity.lean::Machine.instruction
proofs/complexity/lean/Complexity.lean::step
proofs/complexity/lean/Complexity.lean::Run
proofs/complexity/lean/Complexity.lean::Polynomial
proofs/complexity/lean/Complexity.lean::Polynomial.eval
proofs/complexity/lean/Complexity.lean::PolynomiallyBounded
proofs/complexity/lean/Complexity.lean::polynomiallyBounded_iff_polynomial
proofs/complexity/lean/Complexity.lean::pairedInput
proofs/complexity/lean/Complexity.lean::ClassP
proofs/complexity/lean/Complexity.lean::VerifierProgram
proofs/complexity/lean/Complexity.lean::VerifierProgram.timeLimit
proofs/complexity/lean/Complexity.lean::ClassNP
proofs/complexity/lean/Complexity.lean::InP
proofs/complexity/lean/Complexity.lean::InNP
proofs/complexity/lean/Complexity.lean::PEqualsNP
proofs/complexity/lean/Complexity.lean::PNotEqualsNP
proofs/complexity/lean/Complexity.lean::ClassP.toNP
proofs/complexity/lean/Complexity.lean::pSubsetNP
proofs/complexity/rocq/Complexity.v::Machine
proofs/complexity/rocq/Complexity.v::Run
proofs/complexity/rocq/Complexity.v::ClassP
proofs/complexity/rocq/Complexity.v::ClassNP
proofs/complexity/rocq/Complexity.v::InP
proofs/complexity/rocq/Complexity.v::InNP
proofs/complexity/rocq/Complexity.v::PEqualsNP
proofs/complexity/rocq/Complexity.v::PNotEqualsNP
proofs/complexity/rocq/Complexity.v::pSubsetNP
proofs/complexity/agda/Complexity.agda::InP
proofs/complexity/agda/Complexity.agda::InNP
proofs/complexity/agda/Complexity.agda::PEqualsNP
proofs/complexity/agda/Complexity.agda::PNotEqualsNP
proofs/complexity/agda/Complexity.agda::pSubsetNP
proofs/experiments/issue8/lean/NPSubsetP.lean::NPSubsetP
proofs/experiments/issue8/lean/NPSubsetP.lean::npSubsetP_iff_pEqualsNP
proofs/experiments/issue8/lean/NPSubsetP.lean::npSubsetP_iff_classes_equal
# SAT and reductions (section 2)
proofs/experiments/issue532/lean/Machines.lean::Computes
proofs/experiments/issue532/lean/Machines.lean::PolyReduces
proofs/experiments/issue532/lean/Machines.lean::NPHard
proofs/experiments/issue532/lean/Machines.lean::NPComplete
proofs/experiments/issue532/lean/Machines.lean::bruteForce
proofs/experiments/issue532/lean/Machines.lean::encodeCNF
proofs/experiments/issue532/lean/Machines.lean::decode
proofs/experiments/issue532/lean/Machines.lean::decode_encode
proofs/experiments/issue532/lean/Machines.lean::SAT
proofs/experiments/issue532/lean/Machines.lean::sat_iff
proofs/experiments/issue532/rocq/Machines.v::encodeCNF
proofs/experiments/issue532/rocq/Machines.v::SAT
proofs/experiments/issue532/lean/SATVerifier.lean::satInNP
proofs/experiments/issue532/rocq/SATVerifier.v::satInNP
# Named hypotheses (section 3)
proofs/experiments/issue532/lean/Machines.lean::SATInNP
proofs/experiments/issue532/lean/Machines.lean::SATHard
proofs/experiments/issue532/lean/Machines.lean::CookLevin
proofs/experiments/issue532/rocq/Machines.v::SATInNP
proofs/experiments/issue532/rocq/Machines.v::SATHard
proofs/experiments/issue532/rocq/Machines.v::CookLevin
proofs/experiments/issue532/lean/Circuits.lean::PSubsetPPoly
proofs/experiments/issue532/rocq/Circuits.v::PSubsetPPoly
proofs/experiments/issue532/lean/Idea23.lean::NPClosedUnderReductions
proofs/experiments/issue532/rocq/Idea23.v::NPClosedUnderReductions
proofs/experiments/issue532/lean/Idea41.lean::CircuitSATInNP
proofs/experiments/issue532/rocq/Idea41.v::CircuitSATInNP
proofs/experiments/issue532/lean/Idea41.lean::FastCircuitSAT
proofs/experiments/issue532/lean/Idea41.lean::NTimeHierarchy
proofs/experiments/issue532/lean/Idea41.lean::EasyWitnessLemma
proofs/experiments/issue532/lean/Idea41.lean::WilliamsSpeedup
proofs/experiments/issue532/lean/Idea41.lean::LazyDiagonalSimulation
proofs/experiments/issue532/lean/Idea41.lean::NEXPSubsetPPoly
proofs/experiments/issue532/lean/Circuits.lean::InPPoly
proofs/experiments/issue532/lean/Circuits.lean::SuperpolyLowerBound
proofs/experiments/issue568/lean/Tableau.lean::localTrace_iff_run
proofs/experiments/issue568/lean/Tableau.lean::boundedAccept_iff_run
proofs/experiments/issue568/lean/Tableau.lean::bounded_initial_span
proofs/experiments/issue568/rocq/Tableau.v::boundedAccept_iff_run
# What counts as solved (section 4)
proofs/p_vs_np_decidable/lean/PvsNPDecidable.lean::P_vs_NP_is_decidable
proofs/p_vs_np_decidable/rocq/PvsNPDecidable.v::P_vs_NP_is_decidable
# Result graph (section 5)
proofs/experiments/issue532/lean/Machines.lean::pEqualsNP_of_inP_sat
proofs/experiments/issue532/rocq/Machines.v::pEqualsNP_of_inP_sat
proofs/experiments/issue532/lean/SATVerifier.lean::inP_sat_of_pEqualsNP'
proofs/experiments/issue532/lean/SATVerifier.lean::inP_sat_iff_of_hard
proofs/experiments/issue532/rocq/SATVerifier.v::inP_sat_iff_of_hard
proofs/experiments/issue7/lean/ClockedSAT.lean::clockCheck
proofs/experiments/issue7/lean/ClockedSAT.lean::pNotEqualsNP_of_pi2
proofs/experiments/issue7/rocq/ClockedSAT.v::pNotEqualsNP_of_pi2
proofs/experiments/issue7/lean/ClockedSAT.lean::pi2_of_pNotEqualsNP
proofs/experiments/issue532/lean/Circuits.lean::pNotEqualsNP_of_superpoly_sat
proofs/experiments/issue532/rocq/Circuits.v::pNotEqualsNP_of_superpoly_sat
proofs/experiments/issue10/lean/NPNotSubsetP.lean::NPNotSubsetP
proofs/experiments/issue10/lean/NPNotSubsetP.lean::NPSubsetPPoly
proofs/experiments/issue10/lean/NPNotSubsetP.lean::npNotSubsetP_of_not_npSubsetPPoly
proofs/experiments/issue10/rocq/NPNotSubsetP.v::npNotSubsetP_of_not_npSubsetPPoly
proofs/experiments/issue532/lean/Idea41.lean::pNotEqualsNP_of_not_fastCircuitSAT
proofs/experiments/issue532/rocq/Idea41.v::pNotEqualsNP_of_not_fastCircuitSAT
proofs/experiments/issue532/lean/Idea41.lean::williams_method
proofs/experiments/issue532/rocq/Idea41.v::williams_method
proofs/experiments/issue532/lean/Idea41.lean::pNotEqualsNP_of_nexpSubsetPPoly
proofs/experiments/issue532/rocq/Idea41.v::pNotEqualsNP_of_nexpSubsetPPoly
proofs/experiments/issue532/lean/Idea41.lean::nTimeHierarchy_of_lazyDiagonal
proofs/experiments/issue532/rocq/Idea41.v::nTimeHierarchy_of_lazyDiagonal
proofs/experiments/issue609/lean/PEqualsNPAttempt.lean::Candidate
proofs/experiments/issue609/lean/PEqualsNPAttempt.lean::candidate_iff_pEqualsNP
proofs/experiments/issue609/rocq/PEqualsNPAttempt.v::candidate_iff_pEqualsNP
# Tracks and frontier (section 6)
proofs/experiments/issue8/lean/NPSubsetP.lean::dpll_correct
proofs/experiments/issue8/rocq/NPSubsetP.v::dpll_correct
proofs/experiments/issue8/lean/NPSubsetP.lean::dpllSAT_calls_le
proofs/experiments/issue532/lean/Idea01.lean::PolySATDecider
proofs/experiments/issue532/lean/Idea17.lean::SATMachinesSuperpolynomial
proofs/experiments/issue532/lean/Idea19.lean::SATNotInPPoly
proofs/experiments/issue532/lean/Idea30.lean::ExplicitNPLowerBound
proofs/experiments/issue567/lean/ResidualKey.lean::coarseKey_not_satisfiability_complete
proofs/experiments/issue567/rocq/ResidualKey.v::coarseKey_not_satisfiability_complete
# Proved wrong (section 7)
proofs/experiments/issue7/lean/ClockedSAT.lean::per_machine_form_holds
proofs/experiments/issue7/lean/ClockedSAT.lean::rejectAll_defeated
proofs/experiments/issue8/lean/NPSubsetP.lean::calls_bound_not_polynomial
proofs/experiments/issue532/lean/Idea16.lean::BGSCollapse
proofs/experiments/issue532/lean/Idea16.lean::BGSSeparation
proofs/experiments/issue532/lean/Idea16.lean::bgs_no_uniform_answer
proofs/experiments/issue609/lean/KnownBarriers.lean::separation_refutes_uniform
proofs/experiments/issue532/lean/Machines.lean::Diag
proofs/experiments/issue532/lean/Machines.lean::diag_not_inP
```
