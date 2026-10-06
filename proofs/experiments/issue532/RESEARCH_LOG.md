# Issue 532: forty-one fully developed ideas toward P vs NP

This log records forty research directions suggested by
[issue #532](https://github.com/konard/p-vs-np/issues/532), and a forty-first
(Williams' algorithmic method) added in review. Each idea has three parts:

- a **dossier** `ideas/IdeaNN.md`, which states the idea at full strength,
  formulates it precisely, lists the machine-checked theorems, gives the
  complete argument, surveys the literature, pushes the idea as far as it goes
  toward P vs NP, and records the failure modes it catches;
- an independent **Lean 4** file `lean/IdeaNN.lean` (core Lean, no Mathlib);
- an independent **Rocq** file `rocq/IdeaNN.v` (standard library only).

Every theorem is general: it is stated for all formulas, all input lengths,
all algorithms in the stated model, and so on, not for one hand-picked
instance. No file uses `sorry`, `admit`, `Admitted`, a new axiom, a
`Parameter`, or a theorem whose conclusion is `True`. Open problems appear
only as **definitions** of propositions (for example `PolySATDecider` or
`ExplicitNPLowerBound`). They are never assumed as axioms.

An earlier revision stated these propositions with free cost functions or free
complexity classes, so several of them were provable in one line and the
conditional theorems that took them as hypotheses said nothing about P vs NP.
Every open obligation is now stated over the repository's single machine model
([`Complexity.lean`](../../complexity/lean/Complexity.lean)): a decider or
reduction is a `Complexity.Machine`, its time is the step count of
`Complexity.Run`, and the bound is a `Complexity.Polynomial`. The checker
enforces this, each file proves that its obligation is not provable for every
language (`not_forall_*`), and the review's trivialising proofs are kept as a
regression that must fail (see [the shared model](#the-shared-model)).

**Nothing here proves P = NP or P ≠ NP.** Each idea ends in one of four
verdicts:

| Verdict | Meaning | Ideas |
| --- | --- | --- |
| Refuted as a route (general theorem) | A theorem proved in both provers shows that the idea, used as a route to a polynomial SAT algorithm or to a separation, cannot work in general. | 02, 05, 06, 07, 08, 09, 17, 18, 19, 20, 26, 27, 31, 33, 35 |
| Refuted in full strength (published theorem) + formal core | The strongest version is refuted by a published theorem (cited). Its combinatorial core is machine-checked. | 04, 10, 11, 16, 21, 38 |
| Developed to an open obligation (conditional theorem proved) | The idea is correct as far as it goes. What remains is stated as one precise proposition, and the files prove what would follow from it. | 01, 13, 14, 23, 30, 32, 37, 39, 41 |
| Correct tool, insufficient alone (general theorem proved) | The tool is proved correct in general and is needed by any solution, but by itself it cannot decide P vs NP. The files prove why. | 03, 12, 15, 22, 24, 25, 28, 29, 34, 36, 40 |

## The forty-one ideas

| No. | Idea (dossier, Lean, Rocq) | Verdict | Principal machine-checked result | What remains, or why the route fails |
| --- | --- | --- | --- | --- |
| 01 | [Exact SAT algorithm](ideas/Idea01.md) ([Lean](lean/Idea01.lean), [Rocq](rocq/Idea01.v)) | Open obligation | A uniform brute-force CNF decider is sound and complete. It costs exactly `2^n` evaluations on unsatisfiable formulas. | `PolySATDecider := InP SAT` for the shared `SAT` language. `PolySATDecider ↔ PEqualsNP` is proved under the named hypothesis `SATHard` alone, because `SATInNP` is proved in `SATVerifier`. Any machine meeting the obligation agrees with brute force (proved). |
| 02 | [Certificate search](ideas/Idea02.md) ([Lean](lean/Idea02.lean), [Rocq](rocq/Idea02.v)) | Refuted as a route | An adaptive black-box search that only evaluates candidate certificates needs `2^n` trials, even on CNF inputs. The bound is tight. | A fast algorithm must use the text of the formula. That is the whole problem. |
| 03 | [Verifier formalization](ideas/Idea03.md) ([Lean](lean/Idea03.lean), [Rocq](rocq/Idea03.v)) | Correct tool | A CNF verifier is sound and complete. Certificates are no longer than the input, and verification costs exactly `size φ`. | Verification is easy. The difficulty is the quantifier `∃ cert`, which is Idea 01's obligation. |
| 04 | [Local to global consistency](ideas/Idea04.md) ([Lean](lean/Idea04.lean), [Rocq](rocq/Idea04.v)) | Refuted in full strength | An XOR cycle is satisfiable iff its length is even. Every proper subsystem of an odd cycle is satisfiable. | Bounded-width and `k`-consistency fail for 3-SAT and Tseitin formulas (cited). |
| 05 | [Greedy optimization](ideas/Idea05.md) ([Lean](lean/Idea05.lean), [Rocq](rocq/Idea05.v)) | Refuted as a route | The greedy ratio is unbounded: for every `r` there is an instance with ratio above `r`. Greedy is exact when continuations are uniform or the decisions are independent. | Exactness needs the absence of interaction between choices, which NP-hard problems lack. |
| 06 | [Local search and potentials](ideas/Idea06.md) ([Lean](lean/Idea06.lean), [Rocq](rocq/Idea06.v)) | Refuted as a route | For every flip radius `k`, some satisfiable CNF has a non-global local minimum. An exact neighbourhood always exists, and with one local search decides SAT. | `ExactLocalSearch`: a polynomial-time machine that finds a local minimum of an exact neighbourhood. With `CNFEvalInP` (named) it gives `InP SAT`; the neighbourhood part is free, so the obligation is computing a minimum-cost assignment. |
| 07 | [Lossless compression](ideas/Idea07.md) ([Lean](lean/Idea07.lean), [Rocq](rocq/Idea07.v)) | Refuted as a route | Pigeonhole: no injective encoder shortens every `n`-bit string. Incompressible strings exist for every decoder. | Compression helps only on structured families, and finding that structure is the problem. |
| 08 | [Generalization from examples](ideas/Idea08.md) ([Lean](lean/Idea08.lean), [Rocq](rocq/Idea08.v)) | Refuted as a route | Every finite sample has two consistent extensions, and all `2^k` labellings of `k` unseen points are consistent. | Needs a restricted hypothesis class, and consistent learning is NP-hard for natural classes. |
| 09 | [Shortest vs fastest program; Levin search](ideas/Idea09.md) ([Lean](lean/Idea09.lean), [Rocq](rocq/Idea09.v)) | Refuted as a route | In an explicit loop language the shortest program is never the fastest (`shortest_is_never_fastest`). Levin search is within a factor `8·2^i` of program `i`. | `SATWitnessMachine`: one machine outputs a satisfying assignment of every satisfiable formula in polynomially many steps. It gives `InP SAT` (with the named `WitnessCheckInP`), and with `SATHard` it gives P = NP. |
| 10 | [Monotone circuit lower bounds](ideas/Idea10.md) ([Lean](lean/Idea10.lean), [Rocq](rocq/Idea10.v)) | Refuted in full strength | Monotone formulas compute exactly the monotone functions. Negation and parity have no monotone formula. The double-rail translation is proved. | Razborov and Alon–Boppana bounds do not transfer: Tardos (1988) is cited. |
| 11 | [LP relaxation exactness](ideas/Idea11.md) ([Lean](lean/Idea11.lean), [Rocq](rocq/Idea11.v)) | Refuted in full strength | The vertex-cover LP is not exact on `K_n` for any `n ≥ 3`. The gap on `K_{2q}` is `2 − 1/q`. | Extended-formulation lower bounds (Fiorini et al., Rothvoss) are cited. |
| 12 | [Reduction verification](ideas/Idea12.md) ([Lean](lean/Idea12.lean), [Rocq](rocq/Idea12.v)) | Correct tool | Reductions compose. Deciders pull back and hardness pushes forward, with explicit polynomials. Constant maps and yes-preservation alone are invalid. | Reductions only move hardness around. They do not create a fast algorithm. |
| 13 | [Approximation to exactness](ideas/Idea13.md) ([Lean](lean/Idea13.lean), [Rocq](rocq/Idea13.v)) | Open obligation | A `(1+1/q)`-approximation is exact when `OPT < q`, and the threshold is sharp. An FPTAS is exact on polynomially bounded optima. Gap problems are decided by good ratios. | `PolyApprox` beyond the known PCP inapproximability thresholds. |
| 14 | [Randomized search](ideas/Idea14.md) ([Lean](lean/Idea14.lean), [Rocq](rocq/Idea14.v)) | Open obligation | One-sided error amplifies exactly, by counting seed tuples. Polynomially many seeds derandomize by enumeration. Observed success gives no guarantee. | `NPinRP` and `SeedCompression`, both open. |
| 15 | [Circuit depth vs size](ideas/Idea15.md) ([Lean](lean/Idea15.lean), [Rocq](rocq/Idea15.v)) | Correct tool | For formulas, `depth < size < 2^(depth+1)`. Both extremes occur for the same function. A size lower bound implies a depth lower bound. | Depth bounds give NP ⊄ NC¹. That is not known to imply P ≠ NP. |
| 16 | [Diagonalization](ideas/Idea16.md) ([Lean](lean/Idea16.lean), [Rocq](rocq/Idea16.v)) | Refuted in full strength | An abstract hierarchy theorem holds in every oracle world. A relativizing technique cannot prove a statement that fails in some world. There is an oracle adversary for `2^n` queries. | Baker–Gill–Solovay, stated over oracle machines (`InPO`, `InNPO`) as the named theorems `BGSCollapse` and `BGSSeparation`: some non-relativizing ingredient (`NonRelativizingIngredientFor`) is required. The time classes `InNTIME` and `NTimeHierarchy` are shared with Idea 41. |
| 17 | [Enumeration accounting](ideas/Idea17.md) ([Lean](lean/Idea17.lean), [Rocq](rocq/Idea17.v)) | Refuted as a route | There are exactly `2^n` assignments with no duplicates. `c(n+1)^k < 2^n` beyond an explicit threshold. One slow algorithm is not a lower bound. | `SATMachinesSuperpolynomial`, proved equivalent to `¬ InP SAT` (`allMachinesSuperpolynomial_iff_not_inP`), so it is P ≠ NP itself. With `SATInNP` (proved) it gives `PNotEqualsNP`. |
| 18 | [Structural restrictions](ideas/Idea18.md) ([Lean](lean/Idea18.lean), [Rocq](rocq/Idea18.v)) | Refuted as a route | 1-valid, 0-valid and unit CNF are decided correctly. No satisfiability-preserving map, even an uncomputable one, sends all CNFs into a trivial class. | `UnitReduction`: a polynomial-time machine reduction of SAT into unit CNF. With `UnitSATInP` (named) it gives `InP SAT`. The size-only schema `PolySizeReductionIntoFor` already holds via a non-constructive map (`unit_size_reduction_exists`). By Schaefer (cited), unless P = NP the class must itself be NP-complete. |
| 19 | [Advice and nonuniformity](ideas/Idea19.md) ([Lean](lean/Idea19.lean), [Rocq](rocq/Idea19.v)) | Refuted as a route | One advice bit per length decides every unary language. Advice classes escape every enumeration of uniform machines. | The opposite direction, `SATNotInPPoly` / `NPNotInPPoly`, would separate P from NP. It gives `PNotEqualsNP` from the named `PSubsetPPoly` (proved conditional). |
| 20 | [Parallel and physical cost](ideas/Idea20.md) ([Lean](lean/Idea20.lean), [Rocq](rocq/Idea20.v)) | Refuted as a route | `W ≤ p · rounds` and span bounds (Brent) hold, so `2^n` work does not fit in polynomially many rounds and processors. | `PhysicalResourceHonestyFor` is a physical postulate, not a theorem. For machines of the shared model it is proved (`physicalResourceHonesty_machine`). |
| 21 | [DPLL branching](ideas/Idea21.md) ([Lean](lean/Idea21.lean), [Rocq](rocq/Idea21.v)) | Refuted in full strength | The split rule holds. Split and DPLL solvers are correct. The split tree has exactly `2^|vs|` leaves, and pruning never increases this. | Resolution lower bounds (Haken 1985, cited) apply to every DPLL/CDCL run. |
| 22 | [Decision to search](ideas/Idea22.md) ([Lean](lean/Idea22.lean), [Rocq](rocq/Idea22.v)) | Correct tool | Self-reduction finds a witness with exactly one decider call per variable. The polynomial cost transfers. | `ExactPolyDecider`, which is P = NP. |
| 23 | [Resolution](ideas/Idea23.md) ([Lean](lean/Idea23.lean), [Rocq](rocq/Idea23.v)) | Open obligation | Resolution with weakening is sound and refutation-complete: unsatisfiable iff the empty clause is derivable. | `NoPolyBoundedUNSATProofSystem` over machine verifiers. It gives `¬ InP SAT` and `PNotEqualsNP`, and is equivalent to NP ≠ coNP under named known theorems (`noPolyBounded_iff_npNeCoNP`). Haken's bound (cited) handles resolution only. |
| 24 | [Unit propagation](ideas/Idea24.md) ([Lean](lean/Idea24.lean), [Rocq](rocq/Idea24.v)) | Correct tool | Unit propagation is sound and equisatisfiable. It is incomplete on the family `sq x y ++ ψ`. Horn-SAT is decided in full. | Complete only on tractable fragments. |
| 25 | [Decomposable constraints](ideas/Idea25.md) ([Lean](lean/Idea25.lean), [Rocq](rocq/Idea25.v)) | Correct tool | Variable-disjoint components are solved independently and their witnesses merged. The chain family is connected for every `n`. | Hard families are connected with linear treewidth. |
| 26 | [Separator consistency](ideas/Idea26.md) ([Lean](lean/Idea26.lean), [Rocq](rocq/Idea26.v)) | Refuted as a route | The exact separator theorem is proved. Separately satisfiable sides can disagree. By the equality gadget, all `2^|S|` states must be distinguished. | Linear separators force `2^{Ω(n)}` states for this method. |
| 27 | [Variable elimination](ideas/Idea27.md) ([Lean](lean/Idea27.lean), [Rocq](rocq/Idea27.v)) | Refuted as a route | The Davis–Putnam elimination theorem holds with the exact size law `rest + pos·neg`. A `p + q → p·q` blow-up family is given. | It is a form of resolution, so Haken's bound (cited) applies to every order. |
| 28 | [Tseitin extensions](ideas/Idea28.md) ([Lean](lean/Idea28.lean), [Rocq](rocq/Idea28.v)) | Correct tool | Tseitin is equisatisfiable for every formula, with at most `3·#gates + 1` clauses of width at most 3. | It preserves hardness. `ERNotPolyBounded` (extended resolution is not polynomially bounded on UNSAT) is open. It follows from NP ≠ coNP under Cook–Reckhow (named), and is not known to give P ≠ NP. |
| 29 | [Reduction chains](ideas/Idea29.md) ([Lean](lean/Idea29.lean), [Rocq](rocq/Idea29.v)) | Correct tool | Machine reductions compose (`polyReduces_trans`). P transfers backwards along chains and NP-hardness forwards. `reducesToP_iff_inP` is proved. | "Reduce SAT to something easy" is the same as SAT being easy (`satReducesToP_iff_inP_sat`). |
| 30 | [Unrestricted circuit lower bounds](ideas/Idea30.md) ([Lean](lean/Idea30.lean), [Rocq](rocq/Idea30.v)) | Open obligation | Lower-bound transfer holds. By Shannon counting, some `n`-bit function has no NAND circuit with `g` gates when `(g+1)((n+g)²)^g < 2^(2^n)`. | `ExplicitNPLowerBound`, which faces the natural-proofs, relativization and algebrization barriers. |
| 31 | [Length-wise advice](ideas/Idea31.md) ([Lean](lean/Idea31.lean), [Rocq](rocq/Idea31.v)) | Refuted as a route | Truth-table trees compute every function with exactly `2^n` leaves. Parity needs `2^n` leaves. Advice escapes every uniform enumeration. | `UniformSATAdvice`: polynomial-time machines that produce and use the advice. It gives `InP SAT`, so it amounts to a uniform algorithm. |
| 32 | [Promise algorithms](ideas/Idea32.md) ([Lean](lean/Idea32.lean), [Rocq](rocq/Idea32.v)) | Open obligation | A promise solver is total iff the promise covers every input; otherwise some promise-correct solver errs outside it. A promise-preserving reduction into the promise yields a total solver at additive cost, and the "into" condition is necessary. | `IsolationObligation`: a deterministic polynomial map into Unique-SAT. Only a randomized one is known (Valiant–Vazirani, cited). |
| 33 | [Average vs worst case](ideas/Idea33.md) ([Lean](lean/Idea33.lean), [Rocq](rocq/Idea33.v)) | Refuted as a route | For every language and length, `flipOne L` errs on exactly one of the `2^n` inputs. | `WorstToAverage` for SAT. With an average-case machine decider it gives `InP SAT`, and its failure gives `PNotEqualsNP`. Non-adaptive forms collapse PH (Bogdanov–Trevisan, cited). |
| 34 | [Quantifier order](ideas/Idea34.md) ([Lean](lean/Idea34.lean), [Rocq](rocq/Idea34.v)) | Correct tool | `PNotEqualsNP ↔ ∃ L ∈ NP, ¬ InP L`, over the repository's `Complexity` model. `∃∀` does not follow from `∀∃`. Hard inputs must occur at unbounded sizes. | An auditing tool. It proves no lower bound. |
| 35 | [Solution-set compression](ideas/Idea35.md) ([Lean](lean/Idea35.lean), [Rocq](rocq/Idea35.v)) | Refuted as a route | Any exact representation of `n`-variable functions uses at least `2^n` bits on some function. Fewer than `2^b` tables have codes shorter than `b`. | On CNF-definable functions it is as hard as SAT. |
| 36 | [Relaxation and rounding](ideas/Idea36.md) ([Lean](lean/Idea36.lean), [Rocq](rocq/Idea36.v)) | Correct tool | Threshold rounding gives a cover of cost at most `2·LP`. `K_n` has LP value `n/2` against an integral value `n − 1`. | Exact polynomial rounding for an NP-hard problem would decide it. |
| 37 | [Parameterized structure](ideas/Idea37.md) ([Lean](lean/Idea37.lean), [Rocq](rocq/Idea37.v)) | Open obligation | `f(k)·n^c` is polynomial when `2^k ≤ n`. With `k = n` it beats every polynomial. | `LogParamFPTObligation`: a logarithmic parameter on all instances of an NP-complete problem. |
| 38 | [Relativization audit](ideas/Idea38.md) ([Lean](lean/Idea38.lean), [Rocq](rocq/Idea38.v)) | Refuted in full strength | A decision tree of depth `< N` cannot decide OR on `N` oracle bits, while one nondeterministic query does. A relativizing method settles nothing that is oracle-dependent. | Baker–Gill–Solovay (cited). |
| 39 | [Proof-system scope](ideas/Idea39.md) ([Lean](lean/Idea39.lean), [Rocq](rocq/Idea39.v)) | Open obligation | Lower bounds transfer down along p-simulation with a composed polynomial. p-simulation is a preorder. A weak lower bound is compatible with strong short proofs. | `AllTautSystemsSuperpolynomial`: every Cook–Reckhow system `CRSystem` for TAUT, over machine verifiers, has a superpolynomial lower bound (Cook–Reckhow's program). |
| 40 | [Size-uniform invariants](ideas/Idea40.md) ([Lean](lean/Idea40.lean), [Rocq](rocq/Idea40.v)) | Correct tool | Additive recurrences are polynomial. Doubling recurrences are at least `2^n` and beat every polynomial. | `SATMachineSelfReduction`, which gives `InP SAT` (with the named `IterationClosure`) and restates P = NP. |
| 41 | [Williams' algorithmic method](ideas/Idea41.md) ([Lean](lean/Idea41.lean), [Rocq](rocq/Idea41.v)) | Open obligation | `williams_method`: in the shared model, a Circuit-SAT algorithm faster than `2^n/n^ω(1)` (`FastCircuitSAT`, over `Run`) together with three known theorems taken as explicit hypotheses (the nondeterministic time hierarchy, the easy-witness lemma, and the speedup step `WilliamsSpeedup`) refutes NEXP ⊆ P/poly. The hierarchy is derived from a lazy-diagonalisation lemma (`lazy_diagonal`, proved) plus a universal simulator (`LazyDiagonalSimulation`, an explicit hypothesis). The class `NTIME(T)` is Idea 16's (`inNTIME_iff_idea16`), and Idea 16's `NTimeHierarchy` discharges the hierarchy hypothesis (`williams_method_idea16`); that statement is itself a named known theorem, so one hypothesis is shared, not removed. P = NP gives `FastCircuitSAT` (proved, given `CircuitSATInNP`), so a refutation of `FastCircuitSAT` gives P ≠ NP. | `FastCircuitSAT` for general circuits is open; NEXP ⊄ P/poly is not known to give P ≠ NP. This is the only route here that turns a modest algorithmic gain into an unconditional lower bound (Williams 2011, Murray–Williams 2018, cited). |

## The shared model

All cost statements that concern P vs NP use one machine model, so that the
obligations of different ideas are propositions about the same objects as
`Complexity.PEqualsNP`.

- [`Complexity.lean`](../../complexity/lean/Complexity.lean) and
  [`Complexity.v`](../../complexity/rocq/Complexity.v) (pre-existing):
  single-tape machines given by a finite instruction table, `Run m c t b` (the
  machine halts from configuration `c` after exactly `t` steps with answer
  `b`), `Polynomial`, `InP`, `InNP`, `PEqualsNP`.
- [`lean/Machines.lean`](lean/Machines.lean) and
  [`rocq/Machines.v`](rocq/Machines.v) (new):
  - `PolyDec` with `polyDec_iff_inP`;
  - function-computing machines `Computes`, polynomial-time many-one
    reductions `PolyReduces`, machine composition (`compose_run`), closure of
    P under reductions (`inP_of_reduces`), under promise reductions
    (`inP_of_promise_reduction`) and under complement (`inP_complement`);
  - `NPHard`, `NPComplete`, `npComplete_inP_iff`;
  - an injective encoding of machines and a diagonal language outside P
    (`diag_not_inP`, `exists_language_not_in_family`), used by every idea to
    prove that its obligation is not provable for every language;
  - CNF formulas, a lossless binary encoding with a total parser
    (`decode_encode`), and `SAT` as a `Complexity.Language`;
  - Cook–Levin stated in this model: `SATInNP`, `SATHard`, `CookLevin`, and
    `inP_sat_iff : CookLevin → (InP SAT ↔ PEqualsNP)`.
- [`lean/Circuits.lean`](lean/Circuits.lean) and
  [`rocq/Circuits.v`](rocq/Circuits.v) (new): NAND circuits over the same
  `Word`, `InPPoly`, `SuperpolyLowerBound ↔ ¬ InPPoly`, and Shannon counting.
  A circuit family is only required to be correct for `0 < n`, because a
  NAND circuit with no inputs has no gate to read.
- [`lean/SATVerifier.lean`](lean/SATVerifier.lean) and
  [`rocq/SATVerifier.v`](rocq/SATVerifier.v) (new): the membership half of
  Cook–Levin, `SATVerifier.satInNP : SATInNP`, proved with an explicit
  45-state verifier machine, a running-time polynomial `⟨5, 2⟩` and a
  certificate bound `⟨1, 1⟩`.

The hardness half `SATHard` (and so `CookLevin`) is a known theorem that these
files do **not** prove. Every use of it is an explicit named hypothesis.
`SATInNP` is no longer a hypothesis anywhere a theorem needs it: Idea 01 uses
`SATVerifier.satInNP` directly, and Ideas 10, 15, 17, 19, 23, 29, 30, 33 and
39 keep their `SATInNP`-parametrised theorems and add primed corollaries that
discharge it. The same holds for the other known theorems used by single ideas
(for example `PSubsetPPoly`, the easy-witness lemma, or polynomial-time
evaluation of a CNF under an assignment): each is a `def … : Prop` with a
"Known theorem, not mechanised here" comment, never an axiom.

The checker enforces the model. A definition whose comment calls it an "open
obligation" must be in a file that imports `Machines`, must mention a
machine-model name (`Run`, `Computes`, `PolyDec`, `InP`, …) directly or
through definitions of the same file, and may not quantify over a free cost
function or bind a free predicate. Importing `SATVerifier` counts as importing
the model, since it imports `Machines`; in Rocq a plain `Require` (without
`Import`, used where names clash, for example Idea 41's `Idea16.InNTIME`)
counts too. The earlier free-cost definitions remain in
some files as schemas named `…For`, with a theorem that instantiates each
schema with the machine model.

The review of this pull request gave four one-line proofs that the old
obligations of Ideas 13, 14, 32 and 37 hold for every problem, and a
follow-up audit gave such proofs for 24 ideas. They are kept in
[`experiments/issue532_vacuity`](../../../experiments/issue532_vacuity/REPORT.md),
and `check.py` there requires every one of them to fail against the current
files.

## How the issue's questions map to the ideas

The issue asks two groups of questions. The first group is conceptual; the
second is a phased research plan. Each question is answered by the dossiers
listed.

| Issue section | Question in the issue | Answered by |
| --- | --- | --- |
| Part I.1 | Can TSP or shortest-path intuition lead to a fast exact algorithm? | 05, 06, 11, 18, 37 |
| Part I.2 | Do heuristics that work in practice generalize? | 05, 06, 13, 14 |
| Part I.3 | Is finding the shortest program undecidable, and does it matter? | 08, 09 |
| Part I.4 | Lookup tables versus generalization | 07, 08, 19, 31, 35 |
| Part I.5 | Is the shortest program also the fastest? | 09 |
| Part I.6 | Circuits, depth, parallelism and physics | 10, 15, 20, 30 |
| Part I.7 | What does NP-hardness transfer? | 12, 18, 29 |
| Part I.8 | Meta-algorithms that search for algorithms | 01, 09 (Levin search), 22 |
| Part I.9 | What Lean and Rocq can and cannot check | 03, 34, 40 |
| Part II Phase 1 | Formal foundations | 03, 15, 20, 34 |
| Part II Phase 2 | Barrier audit | 10, 16, 30, 38, 39 |
| Part II Phase 3 | Compression and description length | 07, 08, 09, 30, 35 |
| Part II Phase 4 | Proof templates | 05, 06, 07, 16, 30, 35 |
| Part II Phase 5 | Alternative computational models | 14, 19, 20, 31, 32, 33 |
| Part II Phase 6 | Positive frontier (tractable cases) | 15, 18, 32, 33 |
| Part II Phase 7 | Research log | this file |

## What the forty-one ideas show together

1. **Every positive route reduces to one formal proposition, `InP SAT`.**
   Each of Ideas 01, 06, 09, 12, 18, 22, 25, 26, 29, 31, 35 and 40 states its
   obligation over the shared model and proves `obligation → InP SAT`
   (`inP_sat_of_…`), in some cases with a named known theorem as an extra
   premise (for example polynomial-time evaluation of a CNF under an
   assignment). Ideas 01, 29 and 35 prove the converse as well. Ideas 14, 32,
   36 and 37 prove `obligation → PEqualsNP` directly under `SATHard` (or its
   vertex-cover analogue). Under Cook–Levin, `inP_sat_iff` then identifies
   `InP SAT` with `PEqualsNP`. These are theorems in both provers, not a
   prose claim, so none of these routes is a new way around the problem.
2. **Every negative route reduces to explicit lower bounds.** Ideas 17, 19, 23,
   28, 30 and 39 each reduce to a superpolynomial lower bound against *all*
   algorithms, all circuits, or all proof systems; 23 and 39 state it over
   machine verifiers and prove what it gives (`¬ InP SAT`, and NP ≠ coNP
   under named known theorems). Ideas 10, 16, 21, 23 and 38
   show why the restricted versions that are known do not transfer.
3. **Shortcuts that look plausible are refuted in general.** Ideas 02, 04,
   05, 07, 08, 11, 18, 24, 26, 27, 31, 33 and 35 are refuted by theorems that
   hold for every size, not by single counterexamples.
4. **The barriers are real and formalized in their combinatorial core.**
   Relativization (16, 38) and monotone non-transfer (10) are proved in their
   abstract form. The natural-proofs and algebrization barriers are cited in
   ideas 30 and 38.
5. **One route connects the two families.** Idea 41 (Williams' algorithmic
   method) turns a Circuit-SAT algorithm that beats brute force by a
   super-polynomial factor into the lower bound NEXP ⊄ P/poly
   (`williams_method`), with the hierarchy and easy-witness theorems as
   explicit hypotheses. It is non-relativizing and not a natural proof, so it
   is not ruled out by the barrier audits of Ideas 16, 30 and 38. It also
   explains why the gap between `2^n` and `2^n/poly(n)` in Ideas 01, 02 and 21
   matters. NEXP ⊄ P/poly is not known to imply P ≠ NP.

## Failed attempts used as filters

The repository's [common-errors index](../../attempts/COMMON_ERRORS.md)
catalogues earlier attempts. Each dossier's section 7 lists the error families
it catches. For example:

- ideas 17 and 34 catch "one slow algorithm is a lower bound" and swapped
  quantifiers;
- ideas 12, 18 and 29 catch invalid or direction-reversed reductions;
- ideas 05, 06, 13 and 14 catch "works on tests, therefore always";
- ideas 07 and 35 catch compression that loses information;
- ideas 10, 16 and 38 catch lower bounds that do not transfer.

## Reproduction

From the repository root:

```sh
# Structure, verdicts, section-3 tables, forbidden tokens, and links
python3 experiments/issue532/check_dossiers.py
python3 -m unittest discover -s experiments/issue532 -p 'test_*.py' -v

# Lean: all 41 idea files and the shared files are part of the `proofs` library
lake build

# Rocq: the same order as .github/workflows/verification.yml
rocq compile -Q . '' proofs/complexity/rocq/Complexity.v
for file in Machines Circuits SATVerifier Idea16; do
  rocq compile -Q . '' "proofs/experiments/issue532/rocq/$file.v" || exit 1
done
for file in proofs/experiments/issue532/rocq/Idea*.v; do
  rocq compile -Q . '' "$file" || exit 1
done

# The review's trivialising proofs must all fail against the current files
python3 experiments/issue532_vacuity/check.py
```

The `Assumptions.v` files in `experiments/issue532_satverifier/`,
`experiments/issue532_idea41/` and `experiments/issue532_primes/` print the
assumptions of the main theorems (compile them after the files above); all
are closed under the global context.

Each file can also be checked on its own with
`lake env lean proofs/experiments/issue532/lean/IdeaNN.lean`. The one exception
is Idea 34, which needs `lake build proofs.complexity.lean.Complexity` first.

## Verification log

Issue 625 direct evaluator experiment (2026-10-06). An 83-state candidate
table now preserves certificates during length checking, performs unary
wire lookups, and appends NAND results. The Python suite compares 3,174
bounded pairs against the finite specification. Lean and Rocq kernel-check
fourteen concrete runs of that same table against `verifyCircuit` and prove
soundness and completeness of its bounded interpreter for arbitrary machines.
These finite checks do not prove the candidate's universal invariants or its
polynomial runtime. Unconditional `circuitSATInNP`, manifest registration,
and premise removal remain blocked; both completion jobs still fail. Details
and the exact remaining obligations are in
[`experiments/issue625`](../../../experiments/issue625/README.md).

Issue 625 completion enforcement (2026-10-06). Review identified that the
workflow could pass while `circuitSATInNP` was absent because only the syntax
slice and conditional assembly were checked. Mandatory Lean and Rocq jobs now
compile unconditional membership and all six bridges without membership
parameters, require manifest registration, and audit the required import
closures and theorem assumptions with fixed limits. The required verification
summary rejects either job failing or being skipped. Probe sources and logs
are retained as CI artifacts. The gate currently fails in both provers for
missing membership and retained premises. This is CI enforcement, not a new
known theorem mechanized: the universal evaluator and polynomial `Run` proofs
remain missing, and issue 625 remains unresolved.

Issue 625 input-validation slice (2026-10-05). A six-state circuit syntax
machine now recognizes exactly `encCircuit` on the paired input model, with
an exact `|x| + 1` instruction count, including the halt. Lean and Rocq prove
the same recognition, decoder equivalence, termination and run-correctness
statements. The syntax results are known theorems mechanized, not NP
membership. A forward wire has valid syntax, and the new regression makes
that distinction explicit. The paired NP-record assembly theorem still takes
the full evaluating machine's polynomial run theorem as a parameter.
The unconditional `circuitSATInNP` target remains absent in both provers;
the `mem` parameters in Idea 41 and issue 10 remain in place. Details and
reproduction are in [`experiments/issue625`](../../../experiments/issue625/README.md).

Fourth round (2026-09-27, after the review). Every open obligation was moved
onto the shared machine model, `SATInNP` was proved, and Idea 41 was added and
connected to Idea 16.

- `python3 experiments/issue532/check_dossiers.py` reports all 41 dossiers
  complete, and the checker's 7 unit tests pass.
- `python3 experiments/issue532_vacuity/check.py` reports that every
  trivialising proof of the review and of the audit (24 idea files plus the
  review's four proofs, original and retargeted) is rejected.
- `lake build` (Lean 4.34.1) completed with 237 jobs, with no warnings from
  the issue 532 files.
- Every Rocq file compiled in the order above, with no output, under both
  Rocq 9.2 (local) and the `rocq/rocq-prover:9.0` image used in CI.
- Rocq's `Print Assumptions` reports the SATVerifier theorem, the six main
  Idea 41 theorems and the 19 `SATInNP`-free corollaries of Ideas 10, 15, 17,
  19, 23, 29, 30, 33 and 39 as closed under the global context
  (`experiments/issue532_satverifier`, `experiments/issue532_idea41`,
  `experiments/issue532_primes`); in Lean, `#print axioms` shows only
  `propext`, `Classical.choice` and `Quot.sound` for the corollaries.
- In total there are about 21,000 lines of Lean with 1,390 theorems, 22,100
  lines of Rocq with 1,540 theorems and lemmas (44 files each, counting the
  shared `Machines`, `Circuits` and `SATVerifier` and the idea files), and
  9,800 lines of dossiers.

Third round (2026-09-27). Every idea was rewritten from a toy check into a
full dossier with general theorems.

- `python3 experiments/issue532/check_dossiers.py` reports all 40 dossiers
  complete, and the checker's unit tests pass.
- `lake build` (Lean 4.34.1) completed with 233 jobs. All 40 idea files built
  without warnings.
- Every Rocq file compiled with no output under both Rocq 9.2 (local) and the
  `rocq/rocq-prover:9.0` image used in CI.
- In total there are about 13,200 lines of Lean with 823 theorems, 11,900
  lines of Rocq with 869 theorems and lemmas, and 7,500 lines of dossiers.
- The earlier toy generators (`generate.py`, `more_cases.py`) were removed.
  They would overwrite the developed files.

The first two rounds (2026-09-26) introduced the forty directions as small
paired checks. Their results survive as special cases inside the general
theorems of this round.

## Research context

The official [P versus NP problem description](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf)
sets the asymptotic target. The [relativization result](https://doi.org/10.1137/0204037),
[natural proofs](https://www1.karlin.mff.cuni.cz/~krajicek/rr.pdf) and the
[algebrization barrier](https://eccc.weizmann.ac.il/eccc-reports/2008/TR08-005/Paper.pdf)
constrain the lower-bound routes (ideas 10, 16, 30, 38). The
[resolution width–size tradeoff](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf)
and [extended-formulation lower bounds](https://arxiv.org/abs/1111.0837)
bound the proof-system and relaxation routes (ideas 21, 23, 27, 11, 36). Each
dossier's section 5 cites the literature it relies on and says which results
are formalized and which are only cited.
