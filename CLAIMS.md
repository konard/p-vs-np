# Claims ledger

Status at 2026-11-03. `main` is at `ecedd2b`.

This file lists sentences in this repository that could be false, and how
each one is checked. `scripts/check_claims.py` checks the ledger against the
sources, the result manifest, the hypothesis manifest and the literature
registry.

## Purpose and rules

1. A claim is any sentence that could be false: a theorem, a count, a
   citation, a statement about another project.
2. Every claim gets an id, a check type and a status.
3. A claim with no check is `unverified`. Do not state an `unverified` claim
   as fact in any other file. Write it as reported, claimed or conjectured,
   with a date.
4. A row is only as strong as its check. `checked` means the checker or a
   certified theorem confirms it. It does not mean the sentence is important
   or that its wording elsewhere is right.
5. `checked-conditional` means the theorem compiles in CI with each named
   premise as an explicit argument. It is certified only if it is listed in
   `scripts/proof_status.json`. `python3 -I scripts/check_claims.py --stats`
   lists which conditional rows are certified and which are compiled only.
6. CI runs `python3 -I scripts/test_check_claims.py` and
   `python3 -I scripts/check_claims.py --run-scripts` in the `detect-changes`
   job of `.github/workflows/verification.yml` (added 2026-11-03, not yet
   pushed).

## Check types

| check | what the checker does | allowed statuses |
| --- | --- | --- |
| `formal` | Each `path::Name` is declared in its file and listed in `scripts/proof_status.json`. At least one Lean and one Rocq name. The signature takes no hypothesis registered in proofs/HYPOTHESES.md as an argument. | `checked` |
| `formal-conditional` | Each `path::Name` is declared. Each name after `premises:` is a row of proofs/HYPOTHESES.md and occurs in every signature. The claim text names every premise. The Lean file is under `proofs/` and the Rocq file is in `_CoqProject`. | `checked-conditional` |
| `external-formal` | Each id after `registry:` is in `literature/registry.json`. The name after `upstream:` occurs in the `formal.declaration` field of one of them. The external proof is not re-checked here. | `external` |
| `script` | The command runs a file under `scripts/` or `experiments/`. The claim text contains the value after `expect=`. With `--run-scripts`, the command's output (or the first group of `match=`) equals that value. | `checked` |
| `source` | Each id after `registry:` is in `literature/registry.json`. Status `cited` needs an entry whose registry status is `peer-reviewed` or `formally-checked`. | `cited`, `to-formalize`, `unverified` |
| `unverified` | No check. The stated-in file must exist. Any `path::Name` given must be declared. | `unverified`, `to-formalize` |

Statuses:

- `checked`: confirmed by a certified theorem or by a script.
- `checked-conditional`: a compiled theorem with named open premises.
- `external`: a formal proof exists in another project and model. It is not
  re-checked here and is not imported (hard rule 5).
- `cited`: a published, peer-reviewed or formally checked source states it.
- `to-formalize`: listed in the formalization queue below.
- `unverified`: nothing checks it.

Every `path::Name` in any reference must be declared. A `to-formalize` row
may not name a theorem that is already certified; promote it to `formal`.

## Ledger

| id | claim | stated in (file) | check | reference | status |
| --- | --- | --- | --- | --- | --- |
| `p-subset-np` | P ⊆ NP in the shared finite-machine model. | README.md, ROADMAP.md | formal | `proofs/complexity/lean/Complexity.lean::pSubsetNP`; `proofs/complexity/rocq/Complexity.v::pSubsetNP` | checked |
| `sat-in-np` | SAT ∈ NP, by an explicit verifier machine. | README.md, ROADMAP.md | formal | `proofs/experiments/issue532/lean/SATVerifier.lean::satInNP`; `proofs/experiments/issue532/rocq/SATVerifier.v::satInNP` | checked |
| `cook-levin-iff-sat-hard` | The premises `CookLevin` and `SATHard` are equivalent. | proofs/HYPOTHESES.md | formal | `proofs/experiments/issue532/lean/SATVerifier.lean::cookLevin_iff_satHard`; `proofs/experiments/issue532/rocq/SATVerifier.v::cookLevin_iff_satHard` | checked |
| `p-eq-np-implies-sat-in-p` | P = NP implies SAT ∈ P, with no premise. | README.md | formal | `proofs/experiments/issue532/lean/SATVerifier.lean::inP_sat_of_pEqualsNP'`; `proofs/experiments/issue532/rocq/SATVerifier.v::inP_sat_of_pEqualsNP'` | checked |
| `p-vs-np-excluded-middle` | P = NP or P ≠ NP, by classical excluded middle. It decides neither side. | README.md | formal | `proofs/p_vs_np_decidable/lean/PvsNPDecidable.lean::P_vs_NP_is_decidable`; `proofs/p_vs_np_decidable/rocq/PvsNPDecidable.v::P_vs_NP_is_decidable` | checked |
| `p-neq-np-iff-hard-language` | P ≠ NP holds iff some language is in NP and not in P. | proofs/p_not_equal_np/README.md | formal | `proofs/p_not_equal_np/lean/PNotEqualNP.lean::test_existence_of_hard_problem`; `proofs/p_not_equal_np/rocq/PNotEqualNP.v::test_existence_of_hard_problem` | checked |
| `pi2-implies-p-neq-np` | If every clocked machine fails the SAT clock check on some input, then P ≠ NP. No premise. | README.md, ROADMAP.md | formal | `proofs/experiments/issue7/lean/ClockedSAT.lean::pNotEqualsNP_of_pi2`; `proofs/experiments/issue7/rocq/ClockedSAT.v::pNotEqualsNP_of_pi2` | checked |
| `clocked-sat-iff-sat-in-p` | ClockedSAT is equivalent to SAT ∈ P. | proofs/experiments/issue7/README.md | formal | `proofs/experiments/issue7/lean/ClockedSAT.lean::clockedSAT_iff_inP_sat`; `proofs/experiments/issue7/rocq/ClockedSAT.v::clockedSAT_iff_inP_sat` | checked |
| `per-machine-form-holds` | For each machine m and polynomial p, some NP language is not decided by m within time p. | proofs/experiments/issue7/README.md | formal | `proofs/experiments/issue7/lean/ClockedSAT.lean::per_machine_form_holds`; `proofs/experiments/issue7/rocq/ClockedSAT.v::per_machine_form_holds` | checked |
| `dpll-correct` | The DPLL procedure of issue 8 decides SAT on every input. | README.md | formal | `proofs/experiments/issue8/lean/NPSubsetP.lean::dpllSAT_eq_SAT`; `proofs/experiments/issue8/rocq/NPSubsetP.v::dpllSAT_eq_SAT` | checked |
| `dpll-call-bound` | On an input of length n, DPLL makes fewer than 2^(n+1) calls. | README.md, ROADMAP.md | formal | `proofs/experiments/issue8/lean/NPSubsetP.lean::dpllSAT_calls_le`; `proofs/experiments/issue8/rocq/NPSubsetP.v::dpllSAT_calls_le` | checked |
| `dpll-bound-not-polynomial` | The bound 2^(n+1) is not polynomially bounded, so the call bound gives no P algorithm. | proofs/experiments/issue8/README.md | formal | `proofs/experiments/issue8/lean/NPSubsetP.lean::calls_bound_not_polynomial`; `proofs/experiments/issue8/rocq/NPSubsetP.v::calls_bound_not_polynomial` | checked |
| `npsubsetp-iff-p-eq-np` | The issue 8 form NPSubsetP is equivalent to P = NP. | proofs/experiments/issue8/README.md | formal | `proofs/experiments/issue8/lean/NPSubsetP.lean::npSubsetP_iff_pEqualsNP`; `proofs/experiments/issue8/rocq/NPSubsetP.v::npSubsetP_iff_pEqualsNP` | checked |
| `npnotsubsetp-iff-p-neq-np` | The issue 10 form NPNotSubsetP is equivalent to P ≠ NP. | proofs/experiments/issue10/README.md | formal | `proofs/experiments/issue10/lean/NPNotSubsetP.lean::npNotSubsetP_iff_pNotEqualsNP`; `proofs/experiments/issue10/rocq/NPNotSubsetP.v::npNotSubsetP_iff_pNotEqualsNP` | checked |
| `williams-budget-not-polynomial` | For each c, the budget 2^n/(n+1)^c is not polynomially bounded. | proofs/experiments/issue10/README.md | formal | `proofs/experiments/issue10/lean/NPNotSubsetP.lean::williams_budget_not_polynomial`; `proofs/experiments/issue10/rocq/NPNotSubsetP.v::williams_budget_not_polynomial` | checked |
| `coarse-key-counterexample` | The coarse residual key maps a satisfiable and an unsatisfiable formula to the same key, for every k. | README.md, ROADMAP.md | formal | `proofs/experiments/issue567/lean/ResidualKey.lean::coarseKey_not_satisfiability_complete`; `proofs/experiments/issue567/rocq/ResidualKey.v::coarseKey_not_satisfiability_complete` | checked |
| `tableau-bounded-accept` | A bounded tableau accepts iff the machine accepts within the clock. | ROADMAP.md | formal | `proofs/experiments/issue568/lean/Tableau.lean::boundedAccept_iff_run`; `proofs/experiments/issue568/rocq/Tableau.v::boundedAccept_iff_run` | checked |
| `circuit-verifier-spec` | CircuitSAT holds on w iff some certificate passes the circuit verifier. | ROADMAP.md | formal | `proofs/experiments/issue532/lean/Idea41.lean::circuitSAT_iff_verifyCircuit`; `proofs/experiments/issue532/rocq/Idea41.v::circuitSAT_iff_verifyCircuit` | checked |
| `not-every-language-in-p` | Not every language is in P. | proofs/experiments/issue609/README.md | formal | `proofs/experiments/issue609/lean/PEqualsNPAttempt.lean::not_every_language_inP`; `proofs/experiments/issue609/rocq/PEqualsNPAttempt.v::not_every_language_inP` | checked |
| `separation-refutes-uniform` | In the abstract oracle setting, one oracle separation refutes any uniform equality proof. | proofs/experiments/issue609/README.md | formal | `proofs/experiments/issue609/lean/KnownBarriers.lean::separation_refutes_uniform`; `proofs/experiments/issue609/rocq/KnownBarriers.v::separation_refutes_uniform` | checked |
| `sat-in-p-implies-p-eq-np` | Under SATHard, SAT ∈ P implies P = NP. | README.md | formal-conditional | `proofs/experiments/issue532/lean/Machines.lean::pEqualsNP_of_inP_sat`; `proofs/experiments/issue532/rocq/Machines.v::pEqualsNP_of_inP_sat`; premises: SATHard | checked-conditional |
| `sat-in-p-iff-p-eq-np` | Under SATHard, SAT ∈ P iff P = NP. | README.md | formal-conditional | `proofs/experiments/issue532/lean/SATVerifier.lean::inP_sat_iff_of_hard`; `proofs/experiments/issue532/rocq/SATVerifier.v::inP_sat_iff_of_hard`; premises: SATHard | checked-conditional |
| `p-neq-np-implies-pi2` | Under SATHard, P ≠ NP implies the Π⁰₂ clocked form. | proofs/experiments/issue7/README.md | formal-conditional | `proofs/experiments/issue7/lean/ClockedSAT.lean::pi2_of_pNotEqualsNP`; `proofs/experiments/issue7/rocq/ClockedSAT.v::pi2_of_pNotEqualsNP`; premises: SATHard | checked-conditional |
| `npsubsetp-iff-sat-in-p` | Under SATHard, NPSubsetP iff SAT ∈ P. | proofs/experiments/issue8/README.md | formal-conditional | `proofs/experiments/issue8/lean/NPSubsetP.lean::npSubsetP_iff_inP_sat`; `proofs/experiments/issue8/rocq/NPSubsetP.v::npSubsetP_iff_inP_sat`; premises: SATHard | checked-conditional |
| `candidate-iff-p-eq-np` | Under SATHard, the issue 609 candidate holds iff P = NP. | proofs/experiments/issue609/README.md | formal-conditional | `proofs/experiments/issue609/lean/PEqualsNPAttempt.lean::candidate_iff_pEqualsNP`; `proofs/experiments/issue609/rocq/PEqualsNPAttempt.v::candidate_iff_pEqualsNP`; premises: SATHard | checked-conditional |
| `poly-sat-decider-iff` | Under SATHard, a polynomial SAT decider exists iff P = NP. | proofs/experiments/issue532/ideas/Idea01.md | formal-conditional | `proofs/experiments/issue532/lean/Idea01.lean::polySATDecider_iff_of_hard`; `proofs/experiments/issue532/rocq/Idea01.v::polySATDecider_iff_of_hard`; premises: SATHard | checked-conditional |
| `np-not-in-ppoly-implies-p-neq-np` | Under `PSubsetPPoly`: If NP ⊄ P/poly then P ≠ NP, given P ⊆ P/poly. | P_VS_NP_TASK_DESCRIPTION.md | formal-conditional | `proofs/experiments/issue10/lean/NPNotSubsetP.lean::npNotSubsetP_of_not_npSubsetPPoly`; `proofs/experiments/issue10/rocq/NPNotSubsetP.v::npNotSubsetP_of_not_npSubsetPPoly`; premises: PSubsetPPoly | checked-conditional |
| `superpoly-sat-implies-p-neq-np` | Under `SATInNP` and `PSubsetPPoly`: A superpolynomial circuit lower bound for SAT implies P ≠ NP. | proofs/experiments/issue532/RESEARCH_LOG.md | formal-conditional | `proofs/experiments/issue532/lean/Circuits.lean::pNotEqualsNP_of_superpoly_sat`; `proofs/experiments/issue532/rocq/Circuits.v::pNotEqualsNP_of_superpoly_sat`; premises: SATInNP, PSubsetPPoly | checked-conditional |
| `nexp-lower-bound-of-p-eq-np` | Under `CircuitSATInNP`, `NTimeHierarchy`, `EasyWitnessLemma` and `WilliamsSpeedup`: Given the three Williams ingredients, P = NP implies NEXP ⊄ P/poly. | proofs/experiments/issue10/README.md | formal-conditional | `proofs/experiments/issue10/lean/NPNotSubsetP.lean::nexp_lower_bound_of_pEqualsNP`; `proofs/experiments/issue10/rocq/NPNotSubsetP.v::nexp_lower_bound_of_pEqualsNP`; premises: CircuitSATInNP, NTimeHierarchy, EasyWitnessLemma, WilliamsSpeedup | checked-conditional |
| `slow-circuit-sat-implies-p-neq-np` | Under `CircuitSATInNP`: If CircuitSAT has no fast algorithm then P ≠ NP. | proofs/experiments/issue10/README.md | formal-conditional | `proofs/experiments/issue10/lean/NPNotSubsetP.lean::npNotSubsetP_of_not_fastCircuitSAT`; `proofs/experiments/issue10/rocq/NPNotSubsetP.v::npNotSubsetP_of_not_fastCircuitSAT`; premises: CircuitSATInNP | checked-conditional |
| `williams-method` | Under `NTimeHierarchy`, `EasyWitnessLemma` and `WilliamsSpeedup`: The three Williams ingredients and a fast CircuitSAT algorithm give NEXP ⊄ P/poly. | proofs/experiments/issue532/ideas/Idea41.md | formal-conditional | `proofs/experiments/issue532/lean/Idea41.lean::williams_method`; `proofs/experiments/issue532/rocq/Idea41.v::williams_method`; premises: NTimeHierarchy, EasyWitnessLemma, WilliamsSpeedup | checked-conditional |
| `lazy-diagonal-gives-ntime-hierarchy` | Under LazyDiagonalSimulation, one nondeterministic time gap holds: NTIME(2^n) is not contained in NTIME(2^n/(n+1)^c) (Idea41 `NTimeHierarchy`). | proofs/experiments/issue532/ideas/Idea41.md | formal-conditional | `proofs/experiments/issue532/lean/Idea41.lean::nTimeHierarchy_of_lazyDiagonal`; `proofs/experiments/issue532/rocq/Idea41.v::nTimeHierarchy_of_lazyDiagonal`; premises: LazyDiagonalSimulation | checked-conditional |
| `bgs-no-uniform-answer` | Under `BGSCollapse` and `BGSSeparation`: Given BGS oracles for both outcomes, no answer holds for all oracles. | proofs/experiments/issue532/ideas/Idea16.md | formal-conditional | `proofs/experiments/issue532/lean/Idea16.lean::bgs_no_uniform_answer`; `proofs/experiments/issue532/rocq/Idea16.v::bgs_no_uniform_answer`; premises: BGSCollapse, BGSSeparation | checked-conditional |
| `machine-relativizing-cannot-settle` | Under `BGSCollapse` and `BGSTestSeparation`: A machine-relativizing proof method cannot settle P versus NP, given BGS oracles. | proofs/experiments/issue532/ideas/Idea38.md | formal-conditional | `proofs/experiments/issue532/lean/Idea38.lean::machineRelativizing_cannot_settle`; `proofs/experiments/issue532/rocq/Idea38.v::machineRelativizing_cannot_settle`; premises: BGSCollapse, BGSTestSeparation | checked-conditional |
| `time-hierarchy-of-universal-simulation` | Under UniversalSimulation, no single polynomial time bound decides every language in P (Idea16 `TimeHierarchy`). This is a polynomial-level statement, not Hartmanis–Stearns and not P ⊊ EXP. | proofs/experiments/issue532/ideas/Idea16.md | formal-conditional | `proofs/experiments/issue532/lean/Idea16.lean::timeHierarchy_of_universalSimulation`; `proofs/experiments/issue532/rocq/Idea16.v::timeHierarchy_of_universalSimulation`; premises: UniversalSimulation | checked-conditional |
| `np-eq-conp-of-poly-bounded` | Under `SATHard` and `NPClosedUnderReductions`: A polynomially bounded proof system for UNSAT gives NP = coNP. | proofs/experiments/issue532/ideas/Idea23.md | formal-conditional | `proofs/experiments/issue532/lean/Idea23.lean::npEqualsCoNP_of_polyBounded`; `proofs/experiments/issue532/rocq/Idea23.v::npEqualsCoNP_of_polyBounded`; premises: SATHard, NPClosedUnderReductions | checked-conditional |
| `p-neq-np-via-conp` | Under `SATInNP`, `CookReckhowNP` and `NoPolyBoundedUNSATProofSystem`: If no proof system for UNSAT is polynomially bounded, then P ≠ NP. | proofs/experiments/issue532/ideas/Idea23.md | formal-conditional | `proofs/experiments/issue532/lean/Idea23.lean::pNotEqualsNP_via_coNP`; `proofs/experiments/issue532/rocq/Idea23.v::pNotEqualsNP_via_coNP`; premises: SATInNP, CookReckhowNP, NoPolyBoundedUNSATProofSystem | checked-conditional |
| `p-neq-np-via-cook-reckhow` | Under `CookReckhow` and `AllTautSystemsSuperpolynomial`: If every proof system for tautologies is superpolynomial, then P ≠ NP. | proofs/experiments/issue532/ideas/Idea39.md | formal-conditional | `proofs/experiments/issue532/lean/Idea39.lean::pNotEqualsNP_via_cookReckhow`; `proofs/experiments/issue532/rocq/Idea39.v::pNotEqualsNP_via_cookReckhow`; premises: CookReckhow, AllTautSystemsSuperpolynomial | checked-conditional |
| `er-lower-bound-implies-resolution` | Under `ERNotPolyBounded`: A superpolynomial Extended Resolution lower bound implies one for Resolution. | proofs/experiments/issue532/ideas/Idea28.md | formal-conditional | `proofs/experiments/issue532/lean/Idea28.lean::resNotPolyBounded_of_er`; `proofs/experiments/issue532/rocq/Idea28.v::resNotPolyBounded_of_er`; premises: ERNotPolyBounded | checked-conditional |
| `er-lower-bound-of-np-neq-conp` | Under `CookReckhowER`: NP ≠ coNP implies Extended Resolution is not polynomially bounded. | proofs/experiments/issue532/ideas/Idea28.md | formal-conditional | `proofs/experiments/issue532/lean/Idea28.lean::erNotPolyBounded_of_npNeCoNP`; `proofs/experiments/issue532/rocq/Idea28.v::erNotPolyBounded_of_npNeCoNP`; premises: CookReckhowER | checked-conditional |
| `p-eq-np-of-poly-sat-decider` | Under `SATHard` and `PolySATDecider`: A polynomial SAT decider gives P = NP. | proofs/experiments/issue532/ideas/Idea01.md | formal-conditional | `proofs/experiments/issue532/lean/Idea01.lean::pEqualsNP_of_polySATDecider`; `proofs/experiments/issue532/rocq/Idea01.v::pEqualsNP_of_polySATDecider`; premises: SATHard, PolySATDecider | checked-conditional |
| `sat-machines-superpolynomial-route` | Under `SATInNP` and `SATMachinesSuperpolynomial`: If every SAT machine is superpolynomial, then P ≠ NP. | proofs/experiments/issue532/ideas/Idea17.md | formal-conditional | `proofs/experiments/issue532/lean/Idea17.lean::pNotEqualsNP_of_satMachinesSuperpolynomial`; `proofs/experiments/issue532/rocq/Idea17.v::pNotEqualsNP_of_satMachinesSuperpolynomial`; premises: SATInNP, SATMachinesSuperpolynomial | checked-conditional |
| `sat-not-in-ppoly-route` | Under `SATInNP`, `PSubsetPPoly` and `SATNotInPPoly`: SAT ∉ P/poly implies P ≠ NP. | proofs/experiments/issue532/ideas/Idea19.md | formal-conditional | `proofs/experiments/issue532/lean/Idea19.lean::pNotEqualsNP_of_satNotInPPoly`; `proofs/experiments/issue532/rocq/Idea19.v::pNotEqualsNP_of_satNotInPPoly`; premises: SATInNP, PSubsetPPoly, SATNotInPPoly | checked-conditional |
| `formula-lower-bound-route` | Under `SATInNP`, `PSubsetPolyFormulas` and `SATFormulaLowerBound`: A SAT formula lower bound implies P ≠ NP, given P ⊆ polynomial formulas. | proofs/experiments/issue532/ideas/Idea10.md | formal-conditional | `proofs/experiments/issue532/lean/Idea10.lean::pNotEqualsNP_of_satFormulaLowerBound`; `proofs/experiments/issue532/rocq/Idea10.v::pNotEqualsNP_of_satFormulaLowerBound`; premises: SATInNP, PSubsetPolyFormulas, SATFormulaLowerBound | checked-conditional |
| `explicit-lower-bound-route` | Under `PSubsetPPoly` and `ExplicitNPLowerBound`: An explicit superpolynomial circuit lower bound for an NP language implies P ≠ NP. | proofs/experiments/issue532/ideas/Idea30.md | formal-conditional | `proofs/experiments/issue532/lean/Idea30.lean::explicit_lower_bound_separates`; `proofs/experiments/issue532/rocq/Idea30.v::explicit_lower_bound_separates`; premises: PSubsetPPoly, ExplicitNPLowerBound | checked-conditional |
| `exact-rounding-route` | Under `VCHard`, `CoverCheckInP` and `ExactRoundingObligation`: Exact rounding for Vertex Cover gives P = NP. | proofs/experiments/issue532/ideas/Idea36.md | formal-conditional | `proofs/experiments/issue532/lean/Idea36.lean::exactRounding_gives_pEqualsNP`; `proofs/experiments/issue532/rocq/Idea36.v::exactRounding_gives_pEqualsNP`; premises: VCHard, CoverCheckInP, ExactRoundingObligation | checked-conditional |
| `rp-route` | Under `NPinRP`, `SeedCompression`, `SeedEnumeration` and `SATHard`: NP ⊆ RP with seed compression and seed enumeration gives P = NP. | proofs/experiments/issue532/ideas/Idea14.md | formal-conditional | `proofs/experiments/issue532/lean/Idea14.lean::rp_route_gives_pEqualsNP`; `proofs/experiments/issue532/rocq/Idea14.v::rp_route_gives_pEqualsNP`; premises: NPinRP, SeedCompression, SeedEnumeration, SATHard | checked-conditional |
| `isolation-route` | Under `SATHard`, `IsolationObligation` and `PromiseSolver`: Isolation with a promise solver gives P = NP. | proofs/experiments/issue532/ideas/Idea32.md | formal-conditional | `proofs/experiments/issue532/lean/Idea32.lean::isolation_route_gives_pEqualsNP`; `proofs/experiments/issue532/rocq/Idea32.v::isolation_route_gives_pEqualsNP`; premises: SATHard, IsolationObligation, PromiseSolver | checked-conditional |
| `local-search-route` | Under `SATHard`, `CNFEvalInP` and `ExactLocalSearch`: Exact local search for SAT gives P = NP. | proofs/experiments/issue532/ideas/Idea06.md | formal-conditional | `proofs/experiments/issue532/lean/Idea06.lean::pEqualsNP_of_exactLocalSearch`; `proofs/experiments/issue532/rocq/Idea06.v::pEqualsNP_of_exactLocalSearch`; premises: SATHard, CNFEvalInP, ExactLocalSearch | checked-conditional |
| `witness-machine-route` | Under `WitnessCheckInP`, `SATHard` and `SATWitnessMachine`: A polynomial SAT witness machine gives P = NP. | proofs/experiments/issue532/ideas/Idea09.md | formal-conditional | `proofs/experiments/issue532/lean/Idea09.lean::pEqualsNP_of_witnessMachine`; `proofs/experiments/issue532/rocq/Idea09.v::pEqualsNP_of_witnessMachine`; premises: WitnessCheckInP, SATHard, SATWitnessMachine | checked-conditional |
| `unit-reduction-route` | Under `SATHard`, `UnitSATInP` and `UnitReduction`: A reduction of SAT to unit SAT gives P = NP. | proofs/experiments/issue532/ideas/Idea18.md | formal-conditional | `proofs/experiments/issue532/lean/Idea18.lean::pEqualsNP_of_unitReduction`; `proofs/experiments/issue532/rocq/Idea18.v::pEqualsNP_of_unitReduction`; premises: SATHard, UnitSATInP, UnitReduction | checked-conditional |
| `self-reduction-route` | Under `IterationClosure`, `SATHard` and `SATMachineSelfReduction`: A polynomial SAT machine self-reduction gives P = NP. | proofs/experiments/issue532/ideas/Idea40.md | formal-conditional | `proofs/experiments/issue532/lean/Idea40.lean::pEqualsNP_of_machineSelfReduction`; `proofs/experiments/issue532/rocq/Idea40.v::pEqualsNP_of_machineSelfReduction`; premises: IterationClosure, SATHard, SATMachineSelfReduction | checked-conditional |
| `sat-reduces-to-p-route` | Under `SATHard` and `SATReducesToP`: A reduction of SAT to a language in P gives P = NP. | proofs/experiments/issue532/ideas/Idea29.md | formal-conditional | `proofs/experiments/issue532/lean/Idea29.lean::pEqualsNP_of_satReducesToP`; `proofs/experiments/issue532/rocq/Idea29.v::pEqualsNP_of_satReducesToP`; premises: SATHard, SATReducesToP | checked-conditional |
| `certified-lean-count` | scripts/proof_status.json lists 78 certified Lean theorems. | README.md | script | `python3 -I scripts/check_claims.py --count certified-lean` expect=78 | checked |
| `certified-rocq-count` | scripts/proof_status.json lists 78 certified Rocq theorems. | README.md | script | `python3 -I scripts/check_claims.py --count certified-rocq` expect=78 | checked |
| `attempt-folders-count` | proofs/attempts/ has 116 attempt folders. | README.md, proofs/attempts/README.md | script | `python3 -I scripts/check_claims.py --count attempt-folders` expect=116 | checked |
| `attempts-p-eq-np-count` | ATTEMPTS.md marks 63 attempts as claiming P = NP. | README.md, proofs/attempts/README.md | script | `python3 -I scripts/check_claims.py --count attempts-p-eq-np` expect=63 | checked |
| `attempts-p-neq-np-count` | ATTEMPTS.md marks 50 attempts as claiming P ≠ NP. | README.md, proofs/attempts/README.md | script | `python3 -I scripts/check_claims.py --count attempts-p-neq-np` expect=50 | checked |
| `attempts-other-count` | ATTEMPTS.md marks 3 attempts with another or unclear claim. | README.md, proofs/attempts/README.md | script | `python3 -I scripts/check_claims.py --count attempts-other` expect=3 | checked |
| `coverage-concrete-count` | The attempt coverage index has 2 concrete refutations. | README.md | script | `python3 -I scripts/check_claims.py --count coverage-concrete-refutation` expect=2 | checked |
| `coverage-conditional-count` | The attempt coverage index has 2 conditional results. | README.md | script | `python3 -I scripts/check_claims.py --count coverage-conditional-result` expect=2 | checked |
| `coverage-gap-count` | The attempt coverage index has 1 identified gap. | README.md | script | `python3 -I scripts/check_claims.py --count coverage-identified-gap` expect=1 | checked |
| `coverage-informal-count` | The attempt coverage index has 111 informal or unverified analyses. | README.md | script | `python3 -I scripts/check_claims.py --count coverage-informal` expect=111 | checked |
| `idea-dossiers-count` | There are 41 idea dossiers with paired Lean and Rocq files. | README.md, CLAUDE.md | script | `python3 -I experiments/issue532/check_dossiers.py` expect=41 match=Checked\s(\d+)\sidea | checked |
| `verdict-refuted-route-count` | 15 dossiers have the verdict "Refuted as a route". | FORMAL_STATEMENT.md | script | `python3 -I scripts/check_claims.py --count verdict-refuted-route` expect=15 | checked |
| `verdict-refuted-full-count` | 6 dossiers have the verdict "Refuted in full strength". | FORMAL_STATEMENT.md | script | `python3 -I scripts/check_claims.py --count verdict-refuted-full` expect=6 | checked |
| `verdict-open-obligation-count` | 9 dossiers have the verdict "Developed to an open obligation". | FORMAL_STATEMENT.md | script | `python3 -I scripts/check_claims.py --count verdict-open-obligation` expect=9 | checked |
| `verdict-insufficient-count` | 11 dossiers have the verdict "Correct tool, insufficient alone". | FORMAL_STATEMENT.md | script | `python3 -I scripts/check_claims.py --count verdict-insufficient` expect=11 | checked |
| `strategies-count` | SOLUTION_STRATEGIES.md describes 20 strategies. | SOLUTION_STRATEGIES.md, README.md | script | `python3 -I scripts/check_claims.py --count strategies` expect=20 | checked |
| `error-families-count` | COMMON_ERRORS.md has 20 error families. | RESEARCH_VISION.md | script | `python3 -I scripts/check_claims.py --count error-families` expect=20 | checked |
| `hypotheses-rows-count` | proofs/HYPOTHESES.md has 67 rows. | proofs/HYPOTHESES.md | script | `python3 -I scripts/check_claims.py --count hypotheses-rows` expect=67 | checked |
| `registry-entries-count` | literature/registry.json has 162 valid entries. | ROADMAP.md, literature/REGISTRY.md | script | `python3 -I scripts/check_literature_registry.py` expect=162 match=:\s(\d+)\sentries\svalid | checked |
| `registry-under-review-count` | 1 registry entry is under expert review: the OpenAI ETH claim. | literature/REGISTRY.md | script | `python3 -I scripts/check_claims.py --count registry-status:under-expert-review` expect=1 | checked |
| `no-unconditional-target` | The manifest has 0 theorems whose whole statement is PEqualsNP or PNotEqualsNP. | README.md, ROADMAP.md | script | `python3 -I scripts/check_claims.py --count unconditional-target-theorems` expect=0 | checked |
| `no-eth-premise` | The manifest has 0 theorems that mention ETH or SETH. | README.md, TOOLS_AND_METHODOLOGIES.md | script | `python3 -I scripts/check_claims.py --count manifest-eth-premises` expect=0 | checked |
| `cook-levin` | SAT is NP-hard under polynomial-time reductions (Cook 1971, Levin 1973). Open here as `SATHard`. | README.md, ROADMAP.md | source | registry: cook-1971-theorem-proving, levin-1973-universal-search, karp-1972-reducibility | to-formalize |
| `np-neq-conp-implies-p-neq-np` | P = NP implies NP = coNP. So NP ≠ coNP implies P ≠ NP. Proved in Machines; not certified. | SOLUTION_STRATEGIES.md, P_VS_NP_TASK_DESCRIPTION.md | unverified | `proofs/experiments/issue532/lean/Machines.lean::pNotEqualsNP_of_npNeCoNP`; `proofs/experiments/issue532/rocq/Machines.v::pNotEqualsNP_of_npNeCoNP`; `proofs/experiments/issue532/lean/Machines.lean::npEqualsCoNP_of_pEqualsNP`; `proofs/experiments/issue532/rocq/Machines.v::npEqualsCoNP_of_pEqualsNP` | to-formalize |
| `shannon-counting` | Some language needs superpolynomial circuits (Shannon counting). Proved in Circuits; not certified. | P_VS_NP_TASK_DESCRIPTION.md, TOOLS_AND_METHODOLOGIES.md | unverified | `proofs/experiments/issue532/lean/Circuits.lean::exists_superpolyLowerBound`; `proofs/experiments/issue532/rocq/Circuits.v::exists_superpolyLowerBound` | to-formalize |
| `sat-verifier-45-states` | The SAT verifier machine has 45 states: the list `allStates` has length 45 in both the Lean and the Rocq file. | README.md | script | `python3 -I scripts/check_claims.py --count sat-verifier-states` expect=45 | checked |
| `np-closed-under-reductions` | If L reduces to L' in polynomial time and L' ∈ NP, then L ∈ NP. Open here as `NPClosedUnderReductions`. | proofs/HYPOTHESES.md, ROADMAP.md | source | registry: arora-barak-2009 | to-formalize |
| `time-hierarchy` | Deterministic time hierarchy (Hartmanis-Stearns 1965). Here only from `UniversalSimulation`. | TOOLS_AND_METHODOLOGIES.md, proofs/experiments/issue532/ideas/Idea16.md | source | registry: hartmanis-stearns-1965-time-hierarchy | to-formalize |
| `padding-exp-nexp` | P = NP implies EXP = NEXP, by padding. | TOOLS_AND_METHODOLOGIES.md | source | registry: arora-barak-2009 | to-formalize |
| `p-eq-np-collapses-ph` | P = NP implies that the polynomial hierarchy collapses to P. | TOOLS_AND_METHODOLOGIES.md, P_VS_NP_TASK_DESCRIPTION.md | source | registry: arora-barak-2009 | to-formalize |
| `multi-tape-simulation` | A k-tape machine running in time t is simulated by a one-tape machine in time O(t^2). | FORMAL_STATEMENT.md, ROADMAP.md | source | registry: arora-barak-2009 | to-formalize |
| `seth-implies-eth` | SETH implies ETH, through the sparsification lemma. | P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md, proofs/experiments/issue532/ideas/Idea37.md | source | registry: calabro-impagliazzo-paturi-2009-seth, impagliazzo-paturi-zane-2001-sparsification | to-formalize |
| `karp-lipton` | If NP ⊆ P/poly then the polynomial hierarchy collapses to its second level (Karp-Lipton 1980). | proofs/experiments/issue532/ideas/Idea19.md | source | registry: karp-lipton-1980-nonuniform | to-formalize |
| `ladner` | If P ≠ NP then some NP language is neither in P nor NP-complete (Ladner 1975). | proofs/experiments/issue532/ideas/Idea16.md | source | registry: ladner-1975-np-intermediate | to-formalize |
| `p-neq-exp` | P ⊊ EXP, by the time hierarchy theorem. | P_VS_NP_TASK_DESCRIPTION.md | source | registry: hartmanis-stearns-1965-time-hierarchy, arora-barak-2009 | cited |
| `np-neq-nexp` | NP ⊊ NEXP, by the nondeterministic time hierarchy theorem. | P_VS_NP_TASK_DESCRIPTION.md | source | registry: arora-barak-2009 | cited |
| `np-eq-conp-collapses-ph` | NP = coNP implies that the polynomial hierarchy collapses to NP. | P_VS_NP_TASK_DESCRIPTION.md | source | registry: arora-barak-2009 | cited |
| `eth-implies-p-neq-np` | ETH implies P ≠ NP. So ETH is at least as strong as P ≠ NP. Whether it is strictly stronger is not known. | TOOLS_AND_METHODOLOGIES.md, README.md | source | registry: impagliazzo-paturi-2001-eth | cited |
| `ppoly-not-subset-np` | P/poly ⊄ NP, because P/poly contains undecidable unary languages. This is a theorem. | P_VS_NP_TASK_DESCRIPTION.md | source | registry: arora-barak-2009 | cited |
| `razborov-monotone` | Clique needs superpolynomial monotone circuits, n^Ω(log n) (Razborov 1985). | TOOLS_AND_METHODOLOGIES.md, README.md | source | registry: razborov-1985-monotone-clique | cited |
| `hastad-parity-ac0` | Parity is not in AC⁰ (Furst-Saxe-Sipser, Ajtai, Håstad). | P_VS_NP_TASK_DESCRIPTION.md | source | registry: hastad-1986-small-depth-circuits, arora-barak-2009 | cited |
| `williams-nexp-acc` | NEXP ⊄ ACC⁰ (Williams 2011). Murray and Williams extended it to NQP. | README.md, P_VS_NP_TASK_DESCRIPTION.md | source | registry: williams-2014-acc, murray-williams-2018-ntime-acc | cited |
| `bgs-relativization` | There are oracles A and B with P^A = NP^A and P^B ≠ NP^B (Baker-Gill-Solovay 1975). | FORMAL_STATEMENT.md, RESEARCH_VISION.md | source | registry: bgs-1975-relativization | cited |
| `natural-proofs-barrier` | If strong pseudorandom functions exist, natural proofs cannot show NP ⊄ P/poly (Razborov-Rudich 1997). | TOOLS_AND_METHODOLOGIES.md, README.md | source | registry: razborov-rudich-1997-natural-proofs | cited |
| `algebrization-barrier` | Algebrizing techniques cannot resolve P versus NP (Aaronson-Wigderson 2009). | TOOLS_AND_METHODOLOGIES.md | source | registry: aaronson-wigderson-2009-algebrization | cited |
| `absoluteness` | P ≠ NP is an arithmetical sentence, so its truth value is the same in all models of ZFC with the standard natural numbers. | PROVING_P_VS_NP_UNDECIDABILITY.md, P_NOT_EQUAL_NP_SOLUTION_STRATEGIES.md | source | registry: shoenfield-1961-absoluteness | unverified |
| `random-oracle-hypothesis-false` | The Random Oracle Hypothesis is false (Chang et al. 1994). | P_VS_NP_INDEPENDENCE_STRATEGIES.md, PROVING_P_VS_NP_UNDECIDABILITY.md | source | registry: chang-et-al-1994-random-oracle-hypothesis | cited |
| `model-equivalence` | The finite-machine model is polynomially equivalent to standard Turing machines. | FORMAL_STATEMENT.md | unverified | open premise `ModelEquivalence` in proofs/HYPOTHESES.md; see multi-tape-simulation | unverified |
| `vacuity-25-of-30` | 25 of the 30 ideas that defined an obligation were vacuous as first stated. | RESEARCH_VISION.md | unverified | experiments/issue532_vacuity/check.py needs lake; not run by this ledger | unverified |
| `p-vs-np-open` | P versus NP is open as of 2026-11-03: no proof or refutation is accepted by the research community. The problem statement is Cook (2000); the date needs a dated source. | README.md, CLAUDE.md | source | registry: cook-2000-clay-pvsnp | unverified |
| `openai-eth-false` | OpenAI claims a k-SAT algorithm that refutes ETH. Lean checks a weaker time bound (`exact_count_and_sat`) in its own machine model; the step to "ETH is false" is informal. Under review by Impagliazzo, Paturi and Williams. Not checked here. | README.md, TOOLS_AND_METHODOLOGIES.md | external-formal | registry: openai-2026-eth-false; upstream: `exact_count_and_sat` | external |
| `anthropic-eth-false` | Anthropic claims a Lean-checked proof that 3-SAT has a 2^o(n) algorithm, and its Lean development defines ETH and proves `ethIsFalse`. Not peer reviewed; no outside review announced as of 2026-11-03. Not checked here. | README.md, TOOLS_AND_METHODOLOGIES.md | external-formal | registry: anthropic-2026-3sat-subexp; upstream: `MainResults.ethIsFalse` | external |
| `openai-eth-machine-model` | The OpenAI ETH formalization uses a custom PrimitiveMachine model on Mathlib Turing.TM0-style tapes, not Mathlib TM2. | TOOLS_AND_METHODOLOGIES.md | source | registry: openai-2026-eth-false | unverified |
| `eth-review-group` | Impagliazzo, Paturi and Williams are reviewing the OpenAI ETH claim; no outside review of the Anthropic claim is announced as of 2026-11-03. | README.md, TOOLS_AND_METHODOLOGIES.md | source | registry: ethreview-2026-working-group | unverified |
| `eth-refutation-not-p-eq-np` | A 2^o(n) algorithm can still be superpolynomial, so refuting ETH is not known to imply P = NP. | README.md, TOOLS_AND_METHODOLOGIES.md | source | registry: fortnow-2026-eth-refutation-blog | unverified |
| `alman-3sum-apsp` | Alman and Vassilevska Williams claim truly subquadratic 3SUM and truly subcubic APSP. Not reviewed. | TOOLS_AND_METHODOLOGIES.md | source | registry: alman-vw-2026-3sum-apsp | unverified |
| `openai-math-collection` | openai/math had 722 manuscripts in 372 families at its 2026-10-06 release and lists 721 in 373 families at commit 4eaee87 (2026-10-30). | README.md, RESEARCH_VISION.md | source | registry: openai-2026-math-collection | unverified |
| `openai-ugc` | openai/math claims a proof of the Unique Games Conjecture. Not reviewed. | README.md | source | registry: openai-2026-ugc | unverified |
| `openai-border-dc-permanent` | openai/math claims the border determinantal complexity of the permanent is Ω(m^3). | literature/REGISTRY.md | source | registry: openai-2026-border-dc-permanent | unverified |
| `openai-depth3-circuits` | openai/math claims a language in P that needs depth-3 OR-AND-OR circuits of size 2^ω(√n). | literature/REGISTRY.md | source | registry: openai-2026-depth3-circuits | unverified |
| `openai-psd-rank-matching` | openai/math claims the perfect matching polytope has exponential PSD rank. | literature/REGISTRY.md | source | registry: openai-2026-psd-rank-matching | unverified |
| `openai-imm-depth5` | openai/math claims a tight n^Θ(√n) bound for homogeneous depth-5 circuits for iterated matrix multiplication. | literature/REGISTRY.md | source | registry: openai-2026-imm-depth5 | unverified |
| `openai-parity-qac0` | openai/math claims parity is not in QAC⁰. | literature/REGISTRY.md | source | registry: openai-2026-parity-qac0 | unverified |
| `openai-cook-levin-tm2` | openai/math states a Cook-Levin reduction to 3-SAT over Mathlib TM2. Different model; not imported here. | FORMAL_STATEMENT.md, literature/REGISTRY.md | external-formal | registry: openai-2026-cook-levin-tm2; upstream: `threeSATReduction` | external |
| `mathlib-tm2-polytime` | Mathlib defines polynomial-time computability for TM2 machines. | TOOLS_AND_METHODOLOGIES.md | external-formal | registry: mathlib-tm2-polytime; upstream: `Turing.TM2ComputableInPolyTime` | external |
| `gaher-kunze-cook-levin` | Gäher and Kunze mechanized Cook-Levin in Coq over the weak call-by-value lambda calculus L. Different model; not imported here. | CLAUDE.md | source | registry: gaher-kunze-2021-cook-levin-coq | cited |
| `balbach-cook-levin` | Balbach mechanized Cook-Levin in Isabelle/HOL over multi-tape Turing machines. Different model; not imported here. | FORMAL_STATEMENT.md, TOOLS_AND_METHODOLOGIES.md | source | registry: balbach-2023-cook-levin-isabelle | cited |
| `williams-sqrt-space` | TIME[t] ⊆ SPACE[√(t log t)] for multitape machines (Williams 2025). | README.md | source | registry: williams-2025-sqrt-space | cited |
| `cook-mertz-tree-evaluation` | Tree Evaluation is in space O(log n log log n) (Cook-Mertz 2024). | README.md | source | registry: cook-mertz-2024-tree-evaluation | cited |
| `symmetric-exp-circuit-bound` | Symmetric exponential time needs circuits of size 2^n/n (Chen-Hirahara-Ren 2024; Li 2024). | README.md | source | registry: chen-hirahara-ren-2024-symmetric-exp, li-2024-symmetric-exp-simplified | cited |

## Formalization queue

These are the `to-formalize` rows, ordered by value and cost. Each entry
states the target in the shared model (`proofs/complexity`, with machines
from `proofs/experiments/issue532/{lean,rocq}/Machines`). No date is
promised. Sizes: small is one PR of a few hundred lines; medium is one PR
with new definitions; large needs several PRs.

### 1. `np-neq-conp-implies-p-neq-np`

- Statement: `npEqualsCoNP_of_pEqualsNP (h : PEqualsNP) : NPEqualsCoNP` and
  `pNotEqualsNP_of_npNeCoNP (h : ¬ NPEqualsCoNP) : PNotEqualsNP`. Both are
  already proved in `Machines.lean` and `Machines.v`.
- Definitions: none new. `NPEqualsCoNP` exists in Machines.
- Hypotheses: none.
- Size: small. Add both names to `scripts/proof_status.json` and pass the
  axiom audit.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 2. `shannon-counting`

- Statement: `exists_superpolyLowerBound : ∃ L : Language,
  SuperpolyLowerBound L`, already proved in `Circuits.lean` and `Circuits.v`.
- Definitions: none new.
- Hypotheses: none.
- Size: small. Certify `Circuits` and its dependencies.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 3. `cook-levin`

- Statement: `satHard : SATHard`, then `cookLevin : CookLevin` through
  `cookLevin_iff_satHard`.
- Definitions: a reduction machine with a polynomial `Run` bound; the
  tableau encoding of #568 (`Issue568.Tableau`).
- Hypotheses: none after the proof. Removes `SATHard` from the conditional
  rows above.
- Size: large. Tracked in #624 and PR #630.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 4. `np-closed-under-reductions`

- Statement: `npClosedUnderReductions : NPClosedUnderReductions`, that is,
  `PolyReduces L L' → InNP L' → InNP L`.
- Definitions: composition of a reduction machine with a verifier, and the
  polynomial bound of the composed `Run`.
- Hypotheses: none.
- Size: medium. Independent of the P-membership premises; see ROADMAP.md.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 5. `time-hierarchy`

- Statement: `universalSimulation : UniversalSimulation` (Idea 16), which
  gives `TimeHierarchy` by `timeHierarchy_of_universalSimulation`.
- Definitions: a clocked universal machine in the shared model, with its
  overhead stated.
- Hypotheses: none after the proof.
- Size: medium.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 6. `padding-exp-nexp`

- Statement: `PEqualsNP → EXPEqualsNEXP`.
- Definitions: reuse `InNEXP` (Idea41) and `InDTIME` (Idea16); add
  `InEXP`. First merge the two `InNTIME` definitions (Idea41 and Idea16).
  Then a padding map and a machine that strips padding.
- Hypotheses: none.
- Size: medium.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 7. `p-eq-np-collapses-ph`

- Statement: `PEqualsNP → ∀ k, SigmaP k = P`.
- Definitions: `SigmaP k` and `PiP k` by polynomial verifiers with k
  alternating certificate blocks.
- Hypotheses: none.
- Size: medium.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 8. `multi-tape-simulation`

- Statement: every k-tape machine running in time t is simulated by a
  shared-model `Machine` in time `O(t^2)`.
- Definitions: a k-tape machine model as a documented extension of
  `proofs/complexity`.
- Hypotheses: none.
- Size: large. Needed before any fine-grained bound (ROADMAP.md, Later).
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 9. `seth-implies-eth`

- Statement: `SETH → ETH`, with the definitions of PR #639 (unmerged).
- Definitions: ETH and SETH over the shared model; k-SAT instances;
  the sparsification lemma.
- Hypotheses: none for the implication. PR #639 must be merged first.
  Fine-grained statements depend on the machine model, so
  `multi-tape-simulation` should come first.
- Size: large.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 10. `karp-lipton`

- Statement: `NPSubsetPPoly → SigmaP 2 = PiP 2`.
- Definitions: `SigmaP 2`, `PiP 2` as in entry 8; circuit self-reduction
  for SAT using `Circuits`.
- Hypotheses: `SATHard` until `cook-levin` is done.
- Size: large.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

### 11. `ladner`

- Statement: `PNotEqualsNP → ∃ L, InNP L ∧ ¬ InP L ∧ ¬ NPComplete L`.
- Definitions: an enumeration of clocked machines and reductions; the
  delayed-diagonalization language.
- Hypotheses: `SATHard` until `cook-levin` is done.
- Size: large.
- Result class: known theorem mechanized.
- Provenance: known theorem newly mechanized.

## Claims that cannot be formalized

These rows state facts about the world, about other projects or about the
state of knowledge. No proof in this repository can check them. They are
checked by a registry entry, a dated note in the stated-in file, and the
quarterly registry review in ROADMAP.md. Each must carry a date where it is
stated.

- `p-vs-np-open`: a fact about the literature at a date.
- `absoluteness`: a metatheorem about models of set theory, outside the
  shared model. Its registry entry `shoenfield-1961-absoluteness` is not
  yet verified.
- `eth-refutation-not-p-eq-np`: a statement about what is known.
- `eth-review-group`: a report about people and a review in progress.
- `openai-eth-machine-model`: a fact about another repository at a pinned
  revision.
- `openai-math-collection`: a count in another repository at pinned
  commits.

## How to add a claim

1. Pick a kebab-case id that is not in the table.
2. Write the claim as one short sentence that could be false.
3. Put the files that state it in "stated in", comma-separated.
4. Choose the strongest check that applies:
   - a certified theorem with no registered premise: `formal`;
   - a compiled theorem with registered premises: `formal-conditional`;
   - a count or other number: `script`, with `--count` of
     `scripts/check_claims.py` or a match on an existing script's output;
   - a formal proof in another project: `external-formal`, after adding a
     registry entry with `formal.declaration`;
   - a published source: `source`, after adding a registry entry;
   - otherwise `unverified`.
5. A `to-formalize` row needs a queue entry with the fields Statement,
   Definitions, Hypotheses, Size, Result class and Provenance (one of the
   provenance labels in CLAUDE.md).
6. Escape a literal pipe in a cell as `\|`.
7. Run `python3 -I scripts/check_claims.py --run-scripts`.

When a premise is discharged or a theorem is certified, update its row: from
`checked-conditional` to `checked`, or from `to-formalize` to `formal`. The
checker fails on a `to-formalize` row whose theorem is already certified.

## How CI uses this

The CI step (`detect-changes` job of `.github/workflows/verification.yml`)
is:

```sh
python3 -I scripts/test_check_claims.py
python3 -I scripts/check_claims.py --run-scripts
```

The checker needs no Lean or Rocq build. It reads source files, so a
`formal-conditional` row confirms that the premise is an explicit argument,
not that the file compiles. Compilation is checked by `lake build` and the
Rocq jobs in `.github/workflows/verification.yml`. Axioms are audited only
for files in `scripts/proof_status.json`, by `scripts/check_proof_status.py`.

The checker exits with 1 and prints `FAIL` lines when:

- an id is duplicated or not kebab-case, or a check or status is unknown;
- a stated-in file, a source file or a declaration is missing;
- a `formal` theorem is not certified or takes a registered hypothesis;
- a premise is not in proofs/HYPOTHESES.md or not in the signature;
- a registry id or an upstream declaration name is missing;
- a script's output differs from the ledger (with `--run-scripts`);
- a `to-formalize` row has no queue entry, or its theorem is certified.

`--stats` prints the counts by status and by check type, the conditional
rows split into certified and compiled only, and the queue.
