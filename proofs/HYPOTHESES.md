# Named hypotheses

A named hypothesis is a proposition defined once (`def … : Prop` in Lean,
`Definition … : Prop` in Rocq) and passed to a theorem as an explicit
argument. It is never an axiom. For this reason `#print axioms` (Lean) and
`Print Assumptions` (Rocq) cannot see it: a theorem such as
`pEqualsNP_of_inP_sat (hard : SATHard) (h : InP SAT) : PEqualsNP` reports
only the global axioms, while its real dependency on `SATHard` sits in its
type. This file is the list of every such hypothesis on `main`. It is the
manifest requested in [#629](https://github.com/konard/p-vs-np/issues/629).
The problem statement and the result graph are in
[../FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md).

Unless a cell starts with `proofs/`, file paths are relative to
`proofs/experiments/issue532/`. Line numbers are checked by
`python3 scripts/check_formal_statement.py`.

<!-- path-base: proofs/experiments/issue532/ -->

Classes:

- `bridge`: a standard theorem that links the shared machine model to the
  textbook classes (Cook–Levin, P ⊆ P/poly, closure under reductions).
- `P-membership`: a known polynomial-time algorithm, still to be written as a
  `Complexity.Machine` with a polynomial `Run` bound.
- `simulation`: universal simulation, time hierarchies, and simulations
  between machine models or encodings.
- `deep`: a published theorem whose proof is long (oracles, proof
  complexity, the Williams method). Cite it; mechanize it only with a plan.
- `obligation`: not a known theorem but an open statement. Most rows are
  the statement that one idea reduces P vs NP to; a proof of any of them
  would be a major result. Two rows, `PSubsetPolyFormulas` and
  `PSubsetLogDepth`, are believed false. They are stated only to show what a
  formula lower bound would still need.

The dependents column lists Lean theorems whose signature takes the
hypothesis as an argument (`(h : H)`, `H →` or `(h : ¬ H)`), found by a
search of `theorem`/`lemma` signatures under `proofs/`, excluding
`proofs/attempts/`. A theorem whose type only states the hypothesis (`… : H`
or `H ↔ …`) is not a dependent. When more than five theorems use it, the
list ends in "…" and gives the total. `scripts/check_formal_statement.py`
recomputes the list from the signature text and fails on a difference.

| name | class | lean (file:line) | rocq (file:line) | statement (one line) | reference | dependents | status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `SATInNP` | bridge | `lean/Machines.lean:1024` | `rocq/Machines.v:1296` | `InNP SAT` | Cook 1971; proved here as `satInNP` (`lean/SATVerifier.lean:816`) | `pNotEqualsNP_of_superpoly_sat`, `polySATDecider_of_pEqualsNP`, `pNotEqualsNP_of_not_polySATDecider`, `npNotInPolyFormulas_of_sat`, `pNotEqualsNP_of_satFormulaLowerBound`, … (23 total) | discharged on main |
| `SATHard` | bridge | `lean/Machines.lean:1027` | `rocq/Machines.v:1300` | `NPHard SAT` (every NP language reduces to SAT by a `PolyReduces` machine) | Cook 1971; Levin 1973; tracked in #624 | `pEqualsNP_of_inP_sat`, `inP_sat_iff_of_hard`, `candidate_iff_pEqualsNP`, `clockedSAT_iff_pEqualsNP`, `npSubsetP_iff_inP_sat`, … (33 total) | in progress (PR #630, unmerged) |
| `CookLevin` | bridge | `lean/Machines.lean:1029` | `rocq/Machines.v:1302` | `NPComplete SAT`; equivalent to `SATHard` by `cookLevin_iff_satHard` | Cook 1971; Levin 1973; tracked in #624 | `inP_sat_iff`, `polySATDecider_iff`, `satMachinesSuperpolynomial_iff_pNotEqualsNP`, `satReducesToP_iff_pEqualsNP` | in progress (PR #630, unmerged) |
| `CircuitSATInNP` | bridge | `lean/Idea41.lean:405` | `rocq/Idea41.v:473` | `InNP CircuitSAT` | Karp 1972; Arora–Barak §6.1; tracked in #625 | `fastCircuitSAT_of_pEqualsNP`, `fastCircuitSAT_of_inP_sat`, `pNotEqualsNP_of_not_fastCircuitSAT`, `pNotEqualsNP_of_nexpSubsetPPoly`, `nexp_lower_bound_of_pEqualsNP`, … (7 total) | discharged in PR #631 (unmerged) |
| `PSubsetPPoly` | bridge | `lean/Circuits.lean:109` | `rocq/Circuits.v:154` | `∀ L, InP L → InPPoly L` | Savage 1972; Pippenger–Fischer 1979; Arora–Barak Thm 6.6; tracked in #626 | `not_inP_of_not_inPPoly`, `pNotEqualsNP_of_superpoly_sat`, `pNotEqualsNP_of_superpoly`, `pNotEqualsNP_of_npNotInPPoly`, `npNotSubsetP_of_not_npSubsetPPoly`, … (15 total) | discharged in PR #632 (unmerged) |
| `NPClosedUnderReductions` | bridge | `lean/Idea23.lean:683` | `rocq/Idea23.v:721` | `∀ L L', PolyReduces L L' → InNP L' → InNP L` | Karp 1972; Arora–Barak §2.2 | `npEqualsCoNP_of_polyBounded`, `noPolyBounded_iff_npNeCoNP`, `noPolyBounded_iff_npNeCoNP'` | open |
| `CookReckhowNP` | bridge | `lean/Idea23.lean:677` | `rocq/Idea23.v:716` | every `InNP` language has a polynomially bounded machine proof system | Cook–Reckhow 1979 | `npNeCoNP_of_noPolyBounded`, `npNeCoNP_of_noPolyBounded'`, `pNotEqualsNP_via_coNP`, `pNotEqualsNP_via_coNP'`, `noPolyBounded_iff_npNeCoNP`, … (6 total) | open |
| `CNFEvalInP` | P-membership | `lean/Idea06.lean:669` | `rocq/Idea06.v:656` | `InP EvalLang` (CNF evaluation under a given assignment) | Cook 1971; Arora–Barak Ch. 2 | `inP_of_localSearchSolves`, `inP_sat_of_exactLocalSearch`, `pEqualsNP_of_exactLocalSearch` | open |
| `WitnessCheckInP` | P-membership | `lean/Idea09.lean:625` | `rocq/Idea09.v:510` | for every `Computes m f p`, `InP (fun x => satCheck x (f x))` | Sipser Thm 7.8 | `inP_sat_of_witnessMachine`, `pEqualsNP_of_witnessMachine` | open |
| `UnitSATInP` | P-membership | `lean/Idea18.lean:384` | `rocq/Idea18.v:358` | `SATInPOn IsUnitCNF` (SAT restricted to unit CNFs is in P) | Dowling–Gallier 1984; Aspvall–Plass–Tarjan 1979 | `inP_sat_of_unitReduction`, `pEqualsNP_of_unitReduction` | open |
| `CoverCheckInP` | P-membership | `lean/Idea36.lean:320` | `rocq/Idea36.v:352` | `InP CoverCheck` (checking a vertex cover against a budget) | Karp 1972; Garey–Johnson §3.1 | `exactRounding_inP`, `exactRounding_gives_pEqualsNP`, `not_forall_reduces_coverCheck` | open |
| `IterationClosure` | P-membership | `lean/Idea40.lean:394` | `rocq/Idea40.v:400` | a length-nonincreasing machine map iterated `len x` times is again machine-computable in polynomial time | Sipser Thm 7.8 | `inP_of_machineSelfReduction`, `inP_sat_of_machineSelfReduction`, `pEqualsNP_of_machineSelfReduction` | open |
| `SeedEnumeration` | P-membership | `lean/Idea14.lean:344` | `rocq/Idea14.v:342` | `∀ L, PolySeedRP L → InP L` (enumerate all logarithmic seeds) | folklore (seed enumeration) | `rp_sat_with_seed_compression`, `rp_route_gives_pEqualsNP` | open |
| `SmallComponentSATInP` | P-membership | `lean/Idea25.lean:333` | `rocq/Idea25.v:321` | for each `k`, a polynomial machine decides `SAT` on CNFs with components of size at most `k·log` | Hopcroft–Tarjan 1973; Samer–Szeider 2010 | `inP_of_componentReduction`, `inP_sat_of_componentReduction`, `pEqualsNP_of_componentReduction` | open |
| `LogSeparatorSATInP` | P-membership | `lean/Idea26.lean:408` | `rocq/Idea26.v:412` | for each `k`, a polynomial machine decides `SAT` on CNFs with a separator tree of budget `k·log` | Robertson–Seymour; Bodlaender et al. 2016; Alekhnovich–Razborov 2002 | `inP_of_separatorReduction`, `inP_sat_of_separatorReduction`, `pEqualsNP_of_separatorReduction` | open |
| `UniversalSimulation` | simulation | `lean/Idea16.lean:641` | `rocq/Idea16.v:689` | `∀ p, InP (DiagWithin p)` (clocked universal machine in P) | Hartmanis–Stearns 1965; Hennie–Stearns 1966 | `timeHierarchy_of_universalSimulation` | open |
| `UniversalSimulationO` | simulation | `lean/Idea16.lean:726` | `rocq/Idea16.v:847` | `∀ A p, InPO A (DiagWithinO A p)` (oracle version) | Hartmanis–Stearns 1965; Hennie–Stearns 1966 | `timeHierarchyO_of_universalSimulationO` | open |
| `TimeHierarchy` | simulation | `lean/Idea16.lean:645` | `rocq/Idea16.v:693` | `∀ p, ∃ L, InP L ∧ ¬ ∃ m, DecidesWithin m p L`; follows from `UniversalSimulation` by `timeHierarchy_of_universalSimulation` | Hartmanis–Stearns 1965 | `no_uniform_bound_of_timeHierarchy` | open |
| `LazyDiagonalSimulation` | simulation | `lean/Idea41.lean:564` | `rocq/Idea41.v:603` | `LazyDiagonalSimulation T T'`: one `NTIME(T)` language lazily disagrees with every `NTIME(T')` language | Žák 1983 | `nTimeHierarchy_of_lazyDiagonal`, `williams_method_lazy`, `idea16_nTimeHierarchy_of_lazyDiagonal` | open |
| `ModelEquivalence` | simulation | not defined | not defined | proposed name; not yet a definition: the single-tape `Complexity.Machine` model and multi-tape Turing machines and word RAMs simulate each other with polynomial time overhead, so P and NP are the same in all three | Hartmanis–Stearns 1965; Hennie–Stearns 1966; Cook–Reckhow 1973 (time-bounded RAMs) | none (assumed informally by every port of a result stated for another model) | open |
| `EncodingInvariance` | simulation | not defined | not defined | proposed name; not yet a definition: `InP` and `InNP` do not change under any polynomial-time computable, polynomially bounded change of the encoding of instances | folklore; Arora–Barak Ch. 1 | none (assumed informally by `encodeCNF` and every other encoding) | open |
| `NTimeHierarchy` (Idea16) | simulation | `lean/Idea16.lean:762` | `rocq/Idea16.v:894` | `∀ k ≥ 3, NTimeHierarchyGap (2^n/(n+1)^k) (2^n)` | Cook 1973; Seiferas–Fischer–Meyer 1978; Žák 1983 | `nTimeHierarchy_of_idea16`, `williams_method_idea16` | open |
| `NTimeHierarchy` (Idea41) | simulation | `lean/Idea41.lean:482` | `rocq/Idea41.v:519` | `∃ c L, InNTIME (2^n) L ∧ ¬ InNTIME (2^n/(n+1)^c) L` | Cook 1973; Seiferas–Fischer–Meyer 1978; Žák 1983 | `williams_method`, `not_fastCircuitSAT_of_nexpSubsetPPoly`, `pNotEqualsNP_of_nexpSubsetPPoly`, `williams_nexp_lower_bound`, `nexp_lower_bound_of_pEqualsNP`, … (6 total) | open |
| `EasyWitnessLemma` | deep | `lean/Idea41.lean:475` | `rocq/Idea41.v:513` | `NEXPSubsetPPoly → SuccinctWitnesses` | Impagliazzo–Kabanets–Wigderson 2002; Williams 2013 | `williams_method`, `not_fastCircuitSAT_of_nexpSubsetPPoly`, `williams_method_idea16`, `williams_method_lazy`, `williams_nexp_lower_bound`, … (8 total) | open |
| `WilliamsSpeedup` | deep | `lean/Idea41.lean:495` | `rocq/Idea41.v:529` | `FastCircuitSAT → SuccinctWitnesses → ∀ c L, InNTIME (2^n) L → InNTIME (2^n/(n+1)^c) L` | Williams 2010, 2013 | `williams_method`, `not_fastCircuitSAT_of_nexpSubsetPPoly`, `williams_method_idea16`, `williams_method_lazy`, `williams_nexp_lower_bound`, … (8 total) | open |
| `BGSCollapse` | deep | `lean/Idea16.lean:574` | `rocq/Idea16.v:597` | `∃ A, PEqualsNPO A` | Baker–Gill–Solovay 1975 | `bgs_no_uniform_answer`, `machineRelativizing_cannot_settle` | open |
| `BGSSeparation` | deep | `lean/Idea16.lean:578` | `rocq/Idea16.v:602` | `∃ B, ¬ PEqualsNPO B` | Baker–Gill–Solovay 1975 | `bgs_no_uniform_answer` | open |
| `BGSTestSeparation` | deep | `lean/Idea38.lean:478` | `rocq/Idea38.v:469` | `∃ B, ¬ InPO B (testLangO B)` | Baker–Gill–Solovay 1975 | `bgsSeparation_of_testSeparation`, `machineRelativizing_cannot_settle` | open |
| `CookReckhow` | deep | `lean/Idea39.lean:536` | `rocq/Idea39.v:547` | `AllTautSystemsSuperpolynomial ↔ ¬ NPEqualsCoNP` | Cook–Reckhow 1979 (J. Symbolic Logic 44(1)): NP = co-NP iff some proof system for tautologies is polynomially bounded | `npNeCoNP_of_allTautSystemsSuperpolynomial`, `pNotEqualsNP_via_cookReckhow`, `allTautSystemsSuperpolynomial_of_npNeCoNP` | open |
| `CookReckhowER` | deep | `lean/Idea28.lean:819` | `rocq/Idea28.v:755` | `¬ NPEqualsCoNP → ERNotPolyBounded` | Cook–Reckhow 1979 | `erNotPolyBounded_of_npNeCoNP` | open |
| `VCHard` | deep | `lean/Idea36.lean:326` | `rocq/Idea36.v:357` | `NPHard VC` | Karp 1972; Garey–Johnson Thm 3.3 | `exactRounding_gives_pEqualsNP` | open |
| `ResNotPolyBounded` | deep | `lean/Idea28.lean:803` | `rocq/Idea28.v:741` | `NotPolyBoundedFor ResDerives` (resolution is not polynomially bounded) | Haken 1985 | none (it is the conclusion of `resNotPolyBounded_of_er`) | open |
| `PolySATDecider` | obligation | `lean/Idea01.lean:195` | `rocq/Idea01.v:195` | `InP SAT` | open problem; `ideas/Idea01.md` | `pEqualsNP_of_polySATDecider`, `polySAT_agrees_with_bruteForce`, `pNotEqualsNP_of_not_polySATDecider`, `pNotEqualsNP_of_not_polySATDecider'` | open |
| `ExactLocalSearch` | obligation | `lean/Idea06.lean:686` | `rocq/Idea06.v:673` | `LocalSearchSolves SAT` | open problem; `ideas/Idea06.md` | `inP_sat_of_exactLocalSearch`, `pEqualsNP_of_exactLocalSearch` | open |
| `SATWitnessMachine` | obligation | `lean/Idea09.lean:614` | `rocq/Idea09.v:498` | `PolyWitnessMachine satCheck` (one machine finds SAT witnesses in polynomial time) | open problem; `ideas/Idea09.md` | `inP_sat_of_witnessMachine`, `pEqualsNP_of_witnessMachine`, `levin_sat_of_witnessMachine` | open |
| `SATFormulaLowerBound` | obligation | `lean/Idea10.lean:465` | `rocq/Idea10.v:400` | SAT has no polynomial-size formulas | open problem; `ideas/Idea10.md` | `npNotInPolyFormulas_of_sat`, `npNotInPolyFormulas_of_sat'`, `pNotEqualsNP_of_satFormulaLowerBound`, `pNotEqualsNP_of_satFormulaLowerBound'` | open |
| `NPNotInPolyFormulas` | obligation | `lean/Idea10.lean:475` | `rocq/Idea10.v:410` | some `InNP` language has no polynomial-size formulas | open problem; `ideas/Idea10.md` | none (conclusion of `npNotInPolyFormulas_of_sat`) | open |
| `PSubsetPolyFormulas` | obligation | `lean/Idea10.lean:495` | `rocq/Idea10.v:429` | every `InP` language has polynomial-size formulas | open and believed false (P ⊆ NC¹-type); stated only to expose a gap; `ideas/Idea10.md` | `pNotEqualsNP_of_satFormulaLowerBound`, `pNotEqualsNP_of_satFormulaLowerBound'` | open |
| `PolyApprox` | obligation | `lean/Idea13.lean:149` | `rocq/Idea13.v:124` | `PolyApprox opt num den`: a polynomial machine approximates `opt` within ratio `num/den` | open problem; `ideas/Idea13.md` | `polyApprox_decides_gap` | open |
| `NPinRP` | obligation | `lean/Idea14.lean:316` | `rocq/Idea14.v:311` | `InRP SAT` | open problem; `ideas/Idea14.md` | `rp_sat_with_seed_compression`, `rp_route_gives_pEqualsNP` | open |
| `SeedCompression` | obligation | `lean/Idea14.lean:337` | `rocq/Idea14.v:334` | `InRP L → PolySeedRP L` | open problem; `ideas/Idea14.md` | `rp_sat_with_seed_compression`, `rp_route_gives_pEqualsNP` | open |
| `SATFormulaSizeLB` | obligation | `lean/Idea15.lean:257` | `rocq/Idea15.v:214` | SAT formulas need size `2^(c·(log₂ n + 1))` for every `c` | open problem; `ideas/Idea15.md` | `satSizeLB_implies_satDepthLB`, `npNotInLogDepth_of_satFormulaSizeLB`, `npNotInLogDepth_of_satFormulaSizeLB'` | open |
| `SATDepthLB` | obligation | `lean/Idea15.lean:265` | `rocq/Idea15.v:221` | SAT formulas need depth `c·(log₂ n + 1)` for every `c` | open problem; `ideas/Idea15.md` | `npNotInLogDepth_of_satDepthLB`, `npNotInLogDepth_of_satDepthLB'`, `pNotEqualsNP_of_satDepthLB`, `pNotEqualsNP_of_satDepthLB'` | open |
| `NPNotInLogDepth` | obligation | `lean/Idea15.lean:280` | `rocq/Idea15.v:237` | some `InNP` language needs superlogarithmic formula depth | open problem; `ideas/Idea15.md` | none (conclusion of `npNotInLogDepth_of_satDepthLB`) | open |
| `PSubsetLogDepth` | obligation | `lean/Idea15.lean:307` | `rocq/Idea15.v:265` | every `InP` language has logarithmic-depth formulas | open and believed false (P ⊆ NC¹-type); stated only to expose a gap; `ideas/Idea15.md` | `pNotEqualsNP_of_satDepthLB`, `pNotEqualsNP_of_satDepthLB'` | open |
| `SATMachinesSuperpolynomial` | obligation | `lean/Idea17.lean:466` | `rocq/Idea17.v:449` | every total SAT decider has superpolynomial worst-case `Run` time | open problem; `ideas/Idea17.md` | `pNotEqualsNP_of_satMachinesSuperpolynomial`, `pNotEqualsNP_of_satMachinesSuperpolynomial'` | open |
| `UnitReduction` | obligation | `lean/Idea18.lean:389` | `rocq/Idea18.v:363` | `ReducesInto SAT IsUnitCNF` | open problem; `ideas/Idea18.md` | `inP_sat_of_unitReduction`, `pEqualsNP_of_unitReduction` | open |
| `SATNotInPPoly` | obligation | `lean/Idea19.lean:308` | `rocq/Idea19.v:320` | `¬ InPPoly SAT` | open problem; `ideas/Idea19.md` | `npNotInPPoly_of_sat`, `npNotInPPoly_of_sat'`, `pNotEqualsNP_of_satNotInPPoly`, `pNotEqualsNP_of_satNotInPPoly'` | open |
| `NPNotInPPoly` | obligation | `lean/Idea19.lean:312` | `rocq/Idea19.v:324` | `∃ L, InNP L ∧ ¬ InPPoly L` | open problem; `ideas/Idea19.md` | `pNotEqualsNP_of_npNotInPPoly`, `nonuniform_lower_bound_separates` | open |
| `ExactPolyDecider` | obligation | `lean/Idea22.lean:592` | `rocq/Idea22.v:581` | `PolyDec SAT` | open problem; `ideas/Idea22.md` | `decision_to_search`, `inP_sat_of_exactPolyDecider`, `pEqualsNP_of_exactPolyDecider` | open |
| `NoPolyBoundedUNSATProofSystem` | obligation | `lean/Idea23.lean:604` | `rocq/Idea23.v:560` | `NoPolyBoundedMachineProofSystem (complement SAT)` | open problem (Cook's program); `ideas/Idea23.md` | `not_inP_sat_of_noPolyBounded`, `pNotEqualsNP_of_noPolyBounded`, `pNotEqualsNP_of_noPolyBounded'`, `npNeCoNP_of_noPolyBounded`, `npNeCoNP_of_noPolyBounded'`, … (7 total) | open |
| `SATComponentReduction` | obligation | `lean/Idea25.lean:347` | `rocq/Idea25.v:334` | `∃ k, ComponentReduction SAT k` | open problem; `ideas/Idea25.md` | `inP_sat_of_componentReduction`, `pEqualsNP_of_componentReduction`, `componentReduction_splits` | open |
| `SATSeparatorReduction` | obligation | `lean/Idea26.lean:421` | `rocq/Idea26.v:425` | `∃ k, SeparatorReduction SAT k` | open problem; `ideas/Idea26.md` | `inP_sat_of_separatorReduction`, `pEqualsNP_of_separatorReduction`, `separatorReduction_states` | open |
| `ERNotPolyBounded` | obligation | `lean/Idea28.lean:739` | `rocq/Idea28.v:649` | extended resolution is not polynomially bounded on unsatisfiable CNFs | open since Cook–Reckhow 1979; `ideas/Idea28.md` | `resNotPolyBounded_of_er` | open |
| `SATReducesToP` | obligation | `lean/Idea29.lean:480` | `rocq/Idea29.v:537` | `∃ L', PolyReduces SAT L' ∧ InP L'` | open problem; `ideas/Idea29.md` | `pEqualsNP_of_satReducesToP`, `pNotEqualsNP_of_not_satReducesToP`, `pNotEqualsNP_of_not_satReducesToP'` | open |
| `SATCircuitLowerBound` | obligation | `lean/Idea30.lean:95` | `rocq/Idea30.v:101` | `SuperpolyLowerBound SAT` | open problem; `ideas/Idea30.md` | `explicit_of_sat`, `explicit_of_sat'`, `sat_lower_bound_separates`, `sat_lower_bound_separates'` | open |
| `ExplicitNPLowerBound` | obligation | `lean/Idea30.lean:99` | `rocq/Idea30.v:105` | `∃ L, InNP L ∧ SuperpolyLowerBound L` | open problem; `ideas/Idea30.md` | `explicit_lower_bound_separates`, `explicit_lower_bound_not_inPPoly` | open |
| `UniformSATAdvice` | obligation | `lean/Idea31.lean:407` | `rocq/Idea31.v:415` | `UniformAdvice SAT` | open problem; `ideas/Idea31.md` | `inP_sat_of_uniformSATAdvice`, `pEqualsNP_of_uniformSATAdvice` | open |
| `IsolationObligation` | obligation | `lean/Idea32.lean:355` | `rocq/Idea32.v:350` | a deterministic polynomial machine map into the Unique-SAT promise that preserves `SAT` | open problem (Valiant–Vazirani 1986 is randomized); `ideas/Idea32.md` | `isolation_promise_inP`, `isolation_route_gives_pEqualsNP`, `promiseSolver_iff_inP`, `schema_of_isolationObligation` | open |
| `PromiseSolver` | obligation | `lean/Idea32.lean:361` | `rocq/Idea32.v:356` | a polynomial machine decides `SAT` on the Unique-SAT promise | open problem; `ideas/Idea32.md` | `isolation_promise_inP`, `isolation_route_gives_pEqualsNP` | open |
| `WorstToAverage` | obligation | `lean/Idea33.lean:325` | `rocq/Idea33.v:320` | `WorstToAverage L δ`: `AvgPolyDec L δ → InP L` (uniform distribution on words) | open problem; `ideas/Idea33.md` | `inP_sat_of_worstToAverage`, `pEqualsNP_of_worstToAverage`, `pNotEqualsNP_of_not_worstToAverage`, `pNotEqualsNP_of_not_worstToAverage'` | open |
| `CompiledSAT` | obligation | `lean/Idea35.lean:334` | `rocq/Idea35.v:302` | `Compiles SAT` | open problem; `ideas/Idea35.md` | `inP_sat_of_compiledSAT`, `pEqualsNP_of_compiledSAT` | open |
| `ExactRoundingObligation` | obligation | `lean/Idea36.lean:337` | `rocq/Idea36.v:369` | a polynomial machine map that appends an optimal vertex cover | open problem; `ideas/Idea36.md` | `exactRounding_reduces`, `exactRounding_inP`, `exactRounding_gives_pEqualsNP` | open |
| `LogParamFPTObligation` | obligation | `lean/Idea37.lean:228` | `rocq/Idea37.v:215` | `LogParamFPT SAT` | open problem; `ideas/Idea37.md` | `logParam_obligation_inP`, `logParam_route_gives_pEqualsNP` | open |
| `AllTautSystemsSuperpolynomial` | obligation | `lean/Idea39.lean:410` | `rocq/Idea39.v:392` | every Cook–Reckhow proof system for `complement SAT` has superpolynomial proofs | open problem (Cook's program); `ideas/Idea39.md` | `not_inP_sat_of_allTautSystemsSuperpolynomial`, `pNotEqualsNP_of_allTautSystemsSuperpolynomial`, `pNotEqualsNP_of_allTautSystemsSuperpolynomial'`, `npNeCoNP_of_allTautSystemsSuperpolynomial`, `pNotEqualsNP_via_cookReckhow` | open |
| `SATMachineSelfReduction` | obligation | `lean/Idea40.lean:382` | `rocq/Idea40.v:386` | `MachineSelfReductionOf SAT` | open problem; `ideas/Idea40.md` | `inP_sat_of_machineSelfReduction`, `pEqualsNP_of_machineSelfReduction` | open |
| `FastCircuitSAT` | obligation | `lean/Idea41.lean:447` | `rocq/Idea41.v:482` | for every `k`, one machine decides `(n+1)^k`-gate circuit SAT in `2^n / n^{ω(1)}` steps | open problem; Williams 2010; `ideas/Idea41.md` | `williams_method`, `williams_method_idea16`, `williams_method_lazy`, `pNotEqualsNP_of_not_fastCircuitSAT`, `npNotSubsetP_of_not_fastCircuitSAT`, … (6 total) | open |

Two rows, `ModelEquivalence` and `EncodingInvariance`, are known theorems
that are not yet named as definitions. Their lean and rocq cells say "not
defined" and their names are proposals. A PR that defines one replaces
"not defined" with the two locations.

Not in the table: the ETH and SETH statements of
[PR #639](https://github.com/konard/p-vs-np/pull/639) (draft, unmerged) are
not on `main`. Add them in the PR that merges them.

## Discharge order

1. The three blockers, in parallel:
   [#624](https://github.com/konard/p-vs-np/issues/624) (`SATHard`,
   `CookLevin`),
   [#625](https://github.com/konard/p-vs-np/issues/625) (`CircuitSATInNP`),
   [#626](https://github.com/konard/p-vs-np/issues/626) (`PSubsetPPoly`).
   Together they remove the premise from every edge of the result graph in
   [../FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md) except the Williams
   ingredients.
2. `NPClosedUnderReductions`, then `UniversalSimulation` and
   `LazyDiagonalSimulation`. The proved `nTimeHierarchy_of_lazyDiagonal`
   turns `LazyDiagonalSimulation` into the Idea 41 `NTimeHierarchy`.
3. The `P-membership` rows, one small PR each. Each needs an explicit
   `Complexity.Machine` and a polynomial `Run` bound.

`NPClosedUnderReductions` and the `P-membership` rows do not depend on each
other or on the blockers of step 1, so steps 2 and 3 can run in parallel
with step 1 and with each other. `ModelEquivalence` and
`EncodingInvariance` have no definition yet; naming them is the first step.
4. The `deep` rows only with a written plan. `VCHard` follows from #624 and
   one more reduction.

The `obligation` rows are not discharged in this order. Each one is an open
research problem.

## Known defects

- **Unpaired theorem.** `Idea18.unit_size_reduction_exists`
  (`lean/Idea18.lean:263`, classical) has no Rocq twin; `rocq/Idea18.v:28`
  says so. It is not certified. Hard rule 2 asks for a pair or for its
  removal from the Lean file (2026-11-03).
- **Two different `NTimeHierarchy`.** `Idea16.NTimeHierarchy`
  (`lean/Idea16.lean:762`) is a family of gaps for every `k ≥ 3`.
  `Idea41.NTimeHierarchy` (`lean/Idea41.lean:482`) is one gap for some `c`.
  They have the same short name and different statements. The proved
  `nTimeHierarchy_of_idea16` derives the second from the first. A reader
  who sees only the short name cannot tell which one a theorem uses.
- **Lean and Rocq differ in form for `SATMachinesSuperpolynomial`.** Lean
  writes `worstTime m n` (`lean/Idea17.lean:466`). Rocq writes
  `worstTime m (totalDecider_halts m SAT h) n` and quantifies over the proof
  `h : TotalDecider m SAT` (`rocq/Idea17.v:449`). The header comment of
  `rocq/Idea17.v` explains why. Both files prove their form equivalent to
  `¬ InP SAT` (`satMachinesSuperpolynomial_iff_not_inP`); the Rocq proof
  takes excluded middle as an explicit argument. The other rows were
  compared side by side, Lean against Rocq, and state the same proposition.
- **Missing markers.** The checker finds a hypothesis by the comment
  just above its definition: "Known theorem", "not mechanised" /
  "not mechanized", or "Open obligation" (case-sensitive). In Lean, 32 of
  the 35 `obligation` rows are found only by "Open obligation". The Lean and Rocq definitions of
  `SATInNP`, `SATHard`, `CookLevin`, `LazyDiagonalSimulation`,
  `TimeHierarchy`, `PSubsetPolyFormulas`, `PSubsetLogDepth` and
  `WorstToAverage` carry none of these markers, so a new definition like
  them would not be found. They were found by a search for `def … : Prop`
  used as a theorem argument, and are in the table by hand. The checker
  requires this list to name exactly the rows whose Lean definition has no
  marker, and each of them to have a row.
- **Believed-false premises.** `pNotEqualsNP_of_satFormulaLowerBound` and
  `pNotEqualsNP_of_satDepthLB` take `PSubsetPolyFormulas` or
  `PSubsetLogDepth`. These premises are believed false, so these theorems are
  not routes to P ≠ NP. The files say so.
- **Discharged but still a parameter.** `SATInNP` is proved, yet 23 Lean
  theorems (and 23 Rocq theorems) still take it as an argument. They are
  correct but weaker than needed. Wrappers with a prime (for example
  `inP_sat_of_pEqualsNP'`) supply `satInNP`. The checker reports this as a
  warning, and as a failure under `--strict`.

## How to update

- A PR that adds, renames, moves or discharges a named hypothesis edits this
  table in the same PR.
- A PR that proves a hypothesis changes its status to
  `discharged in PR #N (unmerged)`. After the merge, the status becomes
  `discharged on main`. Keep the row: the history is useful.
- Run `python3 -I scripts/check_formal_statement.py`. It fails if a marked
  Prop definition under `proofs/` is not in the table, if a row points to a
  line that does not declare the name as a Prop definition, if the
  dependents column differs from the signatures, or if the class disagrees
  with the marker ("Open obligation" means class `obligation`). Use
  `--write-lines` to refresh line numbers after an edit that only moves
  code. The full list of checks is in
  [../scripts/README.md](../scripts/README.md).
