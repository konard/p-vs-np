# Vacuity audit of Idea01–Idea40 (issue 532)

**Of the 30 ideas that define an obligation, 25 are vacuous as stated.** Each can be proved (a) or disproved (b) trivially because a time, cost or class parameter is left free. Only 01, 10, 15, 28 and 34 use a real cost measure (d), and only 34 uses `Complexity.lean`.

I wrote a compiled proof for every vacuous case except 06, 17 and 23, where the idea file already proves it. The proofs are in `experiments/issue532_vacuity/IdeaNNVacuity.lean`; they compiled against commit `76ebd01` and are kept as a regression that must fail against the current sources (`check.py`, which also runs the reviewer's four proofs in `ReviewProofs.lean`).

## Setup
- **What I checked:** commit `76ebd01` (the HEAD of `issue-532-4f371c941e18`), with Lean 4.34.1 core only.
- **Proof files:** 24 files, one per idea, in `/tmp/gh-issue-solver-1790533904797/experiments/issue532_vacuity/`. Each compiles with `lake env lean` with no errors, warnings or `sorry`.
- **No changes to protected files:** I did not modify anything under `proofs/` or `experiments/issue532/`.
- **Idea14 is being changed by someone else.** During the audit, `proofs/experiments/issue532/lean/Idea14.lean` was modified and a new file, `proofs/experiments/issue532/lean/Machines.lean`, appeared. I did not make these changes. The new Idea14 restates its definitions over `Complexity.Machine`.
  - The Idea14 row below describes the committed version.
  - `Idea14Vacuity.lean` was checked against the build of the committed version. It will probably stop compiling once Idea14 is rebuilt from the new source, which is what that rewrite is meant to do.

**Classification key:**
- (a) trivially provable, because a cost, cost model or class parameter is free.
- (b) its negation is trivially provable.
- (c) stated over a private or abstract machine or time notion instead of `proofs/complexity/lean/Complexity.lean`.
- (d) sound and non-vacuous over a real cost measure.

No conditional theorem is used outside its own Lean or Rocq file; I checked with grep over all of `proofs/`. In the Rocq column, numbers in parentheses are the lines of the dependent theorems.

## Table

| Idea | Definition (Lean line) | Class | One-line reason | Trivializing proof | Dependent conditional theorems (Lean line) | Rocq (`rocq/IdeaNN.v`) |
|---|---|---|---|---|---|---|
| 01 | `PolySATDecider` (L463) | (c)+(d) | Real TM step count and polynomial, but on a private TM copy that does not import `Complexity.lean` | none (not vacuous) | `polySAT_agrees_with_bruteForce` (L471) | L437 (L442) |
| 02, 03, 04, 05, 07, 08, 11, 21, 24, 27 | none | none | No obligation def of their own; 27 defers to Idea28 | none | none | none |
| 06 | `ExactAll` (L200) | (a) | A free neighbourhood makes every local optimum global; the file admits this | in the file: `exists_size_one_exact_neighbourhood` (L471) | `exact_local_search_decides` (L415) | L193 (L375, L429) |
| 09 | `PolyTimeWitnessProgramExists` (L526) | (a) | Free `runs`: a classical oracle finds the witness at step 0 | `Idea09Vacuity.lean`: `idea09_obligation_trivial`, `idea09_oracleRuns_monotone`, `idea09_exists_runs` | `levin_poly_of_obligation` (L537) | L422 (L429) |
| 10 | `GeneralSuperpolyLowerBound` (L381), `MonotoneSuperpolyLowerBound` (L385), `DoubleRailLowerBound` (L389) | (d) | Honest formula size; caveat: the function family `f` is never set to an NP function | none | L393, L405 | L326, L331, L336 (L341, L351) |
| 12 | `Algo` (L116), `PolyDecider` (L124), `PolyReduction` (L128) | (a); the hypothesis `¬PolyDecider` is (b) | `Algo.time` is a free field, so `time := 0` works | `Idea12Vacuity.lean`: `idea12_polyDecider_trivial`, `idea12_not_not_polyDecider`, `idea12_polyReduction_trivial` | `poly_decider_transfer` (L155), `poly_reduction_comp` (L172), `hardness_transfer` (L193, which assumes the refutable `¬PolyDecider`) | L98, L106, L109 (L141, L156, L173) |
| 13 | `Algo` (L129), `PolyApprox` (L139) | (a) | Free time: `run := opt`, `time := 0` works for any ratio ≥ 1 | `Idea13Vacuity.lean`: `idea13_polyApprox_trivial`, `idea13_exact_polyApprox` | `polyApprox_decides_gap` (L148); `fptas_poly_bounded_exact` (L85) also takes a free time bound | L89, L96 (L103, L54) |
| 14 (committed version) | `PolyDec` (L244), `RPDecider` (L248), `PolySeedRP` (L253), `NPinRP` (L265), `SeedCompression` (L272) | (a) | The existential time bound is unconstrained; a deterministic algorithm with one seed satisfies all five | `Idea14Vacuity.lean`: `idea14_polyDec_trivial`, `oneSided_trivial`, `idea14_NPinRP_trivial`, `idea14_polySeedRP_trivial`, `idea14_seedCompression_trivial` | `polySeedRP_implies_poly` (L258), `rp_sat_with_seed_compression` (L275) | L210, L214, L219, L236, L239 (L224, L243) |
| 15 | `FormulaSizeLB` (L199), `DepthLB` (L206) | (d) | Honest formula size and depth; the family `fam` is unconstrained | none | `sizeLB_implies_depthLB` (L210) | L166, L170 (L174) |
| 16 | `NonRelativizingIngredient` (L162) | (a) | Free technique: `(∃ T, NonRelativizingIngredient T real S) ↔ S real` | `Idea16Vacuity.lean`: `idea16_ingredient_iff`, `idea16_concrete` | none take it as a hypothesis (`ingredient_necessary`, L166, concludes it) | L129 (L132) |
| 17 | `AllAlgorithmsSuperpolynomial` (L286) | (a)/(b) | Free `AlgorithmModel`: a model with no correct algorithm makes it true; the file's own `twoAlgModel` makes it false | `Idea17Vacuity.lean`: `noCorrectModel`, `idea17_allSuperpoly_trivial`, `idea17_allSuperpoly_of_no_correct`, `idea17_not_allSuperpoly` | `superpolynomial_excludes_poly` (L291) | L215 (model L204; L218) |
| 18 | `PolySizeReductionInto` (L246) | (a)+(c) | No cost model: a classical map to a constant-size yes or no instance works; the file admits this (L254) | `Idea18Vacuity.lean`: `idea18_polySizeReduction_trivial`, `idea18_dcost_free` | `restriction_transfer` (L292) | L226 (L243) |
| 19 | `NPNotInPPoly` (L197) | (a)/(b) | The classes `NP` and `PPoly` are free parameters | `Idea19Vacuity.lean`: `idea19_NPNotInPPoly_trivial`, `idea19_not_NPNotInPPoly` | `nonuniform_lower_bound_separates` (L206) | L176 (L183) |
| 20 | `PhysicalResourceHonesty` (L270) | (a)/(b) | Free `Realizable`; the file's `dishonest_model_collapses` (L297) is a (b) instance | `Idea20Vacuity.lean`: `idea20_honesty_trivial`, `idea20_honesty_trivial'`, `idea20_not_honesty` | `physical_conditional` (L276) | L223 (L226) |
| 22 | `ExactPolyDecider` (L370), `PolySearch` (L375) | (a) | Free `CostModel`; the file admits this with `zero_cost_trivial` (L410) | `Idea22Vacuity.lean`: `idea22_exactPolyDecider_trivial`, `idea22_polySearch_trivial`, `idea22_exactPolyDecider_of_free` | `decision_to_search` (L381) | L364, L367 (L372, L390) |
| 23 | `NoPolyBoundedProofSystem` (L488) | (a)/(b) | Proof length is real but the `Efficient` class is free; the file proves (b) (`unrestricted_obligation_false`, L493) | `Idea23Vacuity.lean`: `idea23_noPolyBounded_trivial`, `idea23_not_noPolyBounded` | `lower_bound_excludes_efficient_decider` (L499) | L428 (L431, L437) |
| 25 | `ComponentObligation` (L245) | (a)+(c) | Free `PolyTime`: a classical map to `[]` or `[[[]]]` meets it even with width w = 0 | `Idea25Vacuity.lean`: `idea25_componentObligation_of`, `idea25_componentObligation_trivial` | `component_obligation_splits` (L252) | L224 (L231) |
| 26 | `SeparatorObligation` (L291) | (a)+(c) | Free `PolyTime`: a classical map gives an empty separator (w = 0) | `Idea26Vacuity.lean`: `idea26_separatorObligation_trivial` | `separator_obligation_states` (L300) | L279 (L289) |
| 28 | `ERSuperpolyLowerBound` (L640) | (d) | Extended-resolution proof length, a sound and complete proof system; no free cost | none | `obligation_excludes_poly_bound` (L647) | L546 (L551) |
| 29 | `PolyDecider` (L182), `InP` (L190), `ReducesToP` (L236) | (a)+(c) | `time` is a free field, so every language is in `InP` | `Idea29Vacuity.lean`: `freeDecider`, `idea29_inP_trivial`, `idea29_reducesToP_trivial` | `reducesToP_iff_inP` (L242) | L171, L185, L229 (L234) |
| 30 | `ExplicitNPLowerBound` (L409); `SuperpolyLowerBound` (L403) | the obligation is (b)+(c); `SuperpolyLowerBound` is (d) | `InNP` is a free predicate never tied to NP, so the empty class refutes it; with `InNP := True` it becomes Shannon counting (true, not formalized) | `Idea30Vacuity.lean`: `idea30_not_explicit_empty`, `idea30_explicit_mono` | `explicit_lower_bound_separates` (L435); its `simulation` hypothesis is also free | L414, L409 (L436) |
| 31 | `UniformPolyAdvice` (L331) | (a) | `decode` is unrestricted: the empty generator with `decode := fun _ x => L x` works for any L; it still works with an honest `Uniform` that contains the constant generator | `Idea31Vacuity.lean`: `idea31_uniformPolyAdvice_of`, `idea31_uniformPolyAdvice_trivial` | `uniform_advice_decides` (L339) | L335 (L341) |
| 32 | `IsolationObligation` (L223) | (a)/(b)+(c) | Free `PolyTime`: a classical SAT decider makes it true; the empty class makes it false | `Idea32Vacuity.lean`: `idea32_isolation_of`, `idea32_isolation_trivial`, `idea32_not_isolation_empty` | `isolation_solves_sat` (L229) | L225 (L230, L243) |
| 33 | `WorstToAverageObligation` (L238) | (a)/(b) | Free `Efficient`: true for the full class (take B := L), the empty class, or any class containing L; false for the file's own class (L246) | `Idea33Vacuity.lean`: `idea33_obligation_trivial`, `idea33_obligation_of_mem`, `idea33_obligation_empty`, `idea33_not_obligation` | `obligation_transfers` (L258) | L235 (L240, L251) |
| 34 | `PNotEqualsNP` (`Complexity.lean` L218); helper `PatchClosed` (L160) | (d) | The only idea over the shared model. `PatchClosed` has a free `Alg` and is never proved for `ClassP` | none | `pNotEqualsNP_iff_unfolded` (L117); `hard_inputs_unbounded` (L207) takes `PatchClosed` | L90; `PatchClosed` L136 (L184) |
| 35 | `CompactTractableCompilation` (L275) | (a)+(c) | Has no cost component; the file admits this (L288) | `Idea35Vacuity.lean`: `idea35_compilation_trivial`, `idea35_compilation_zero` | `compilation_decides` (L294) | L239 (L250, L255) |
| 36 | `ExactRoundingObligation` (L220) | (a)+(c) | Free `PolyTime` and free LP bound `lp`: take lp = the integral optimum and a classical optimal rounding; shown for vertex cover itself | `Idea36Vacuity.lean`: `exists_min`, `idea36_exactRounding_trivial`, `idea36_vertexCover_trivial` | `exact_rounding_decides` (L206) and `exact_rounding_optimal` take its components | L175 (L156, L164) |
| 37 | `LogParamFPTObligation` (L166) | (a)+(c) | Free time: `time := 0`, `param := 0` with any correct algorithm | `Idea37Vacuity.lean`: `idea37_obligation_of_correct`, `idea37_obligation_trivial` | `obligation_gives_poly_time` (L172) | L140 (L145) |
| 38 | `NonrelativizingIngredient` (L276) | (a)/(b) | Free `Proves`: "prove everything" makes it true, "prove nothing" makes it false | `Idea38Vacuity.lean`: `idea38_ingredient_trivial`, `idea38_not_ingredient`, `idea38_ingredient_of` | `nonrelativizing_needed` (L281) concludes it; `nonrelativizing_iff` (L290) | L240 (L243, L256) |
| 39 | `SuperpolyAllSystems` (L290) | (a)/(b) | Free class `C`, and systems need not be efficiently checkable: the empty class or `{weakSys}` makes it true, `{strongSys}` makes it false | `Idea39Vacuity.lean`: `idea39_superpolyAll_empty`, `idea39_superpolyAll_weak`, `idea39_not_superpolyAll_strong` | `optimal_system_reduces` (L296), `bounded_member_refutes` (L308) | L254 (L259, L270) |
| 40 | `AdditiveSelfReduction` (L253) | (a)+(c) | Free base and step functions and free costs: a classical step at cost 0; it holds for real CNF-SAT with size = number of literal occurrences | `Idea40Vacuity.lean`: `idea40_additive_trivial`, `idea40_additive_SAT` | `obligation_gives_poly_solver` (L260), `self_reduction_solver_bound` (L276) | L238 (L247, L267) |

**Free parameters are never given a real model.** No file instantiates any of these with a real machine or cost model:
- `runs`, `CostModel`, `Efficient`, `Realizable`, `AlgorithmModel`
- the technique parameter, `Proves`, `PolyTime`, class `C`, `InNP`
- `Uniform`, `NP` / `PPoly`, and the free time fields

The only instantiations are toy models or ones that make the obligation trivial: `twoAlgModel` (17), `dishonest_model_collapses` (20), `zero_cost_trivial` (22), L493 (23), L246 (33), and `weakSys` / `strongSys` (39).

## Summary: vacuous obligations
1. **06** `ExactAll`: (a); the file proves it itself.
2. **09** `PolyTimeWitnessProgramExists`: (a); free `runs`.
3. **12** `PolyDecider` and `PolyReduction`: (a); the `¬PolyDecider` hypothesis is (b).
4. **13** `PolyApprox`: (a).
5. **14** `PolyDec`, `RPDecider`, `NPinRP`, `PolySeedRP` and `SeedCompression`: (a) in the committed version; now being rewritten by someone else.
6. **16** `NonRelativizingIngredient`: (a); equivalent to `S real`.
7. **17** `AllAlgorithmsSuperpolynomial`: (a)/(b).
8. **18** `PolySizeReductionInto`: (a).
9. **19** `NPNotInPPoly`: (a)/(b).
10. **20** `PhysicalResourceHonesty`: (a)/(b).
11. **22** `ExactPolyDecider` and `PolySearch`: (a).
12. **23** `NoPolyBoundedProofSystem`: (a)/(b).
13. **25** `ComponentObligation`: (a), even with w = 0.
14. **26** `SeparatorObligation`: (a), even with w = 0.
15. **29** `InP` and `ReducesToP`: (a); true for every language.
16. **30** `ExplicitNPLowerBound`: (b); the circuit-size measure itself is honest.
17. **31** `UniformPolyAdvice`: (a).
18. **32** `IsolationObligation`: (a)/(b).
19. **33** `WorstToAverageObligation`: (a)/(b).
20. **35** `CompactTractableCompilation`: (a).
21. **36** `ExactRoundingObligation`: (a).
22. **37** `LogParamFPTObligation`: (a).
23. **38** `NonrelativizingIngredient`: (a)/(b).
24. **39** `SuperpolyAllSystems`: (a)/(b).
25. **40** `AdditiveSelfReduction`: (a); true for CNF-SAT.

**Not vacuous (d):**
- **01** `PolySATDecider` is also (c) because it uses a private TM copy.
- **10** and **15**: formula size and depth lower bounds, but the function families are never set to NP functions.
- **28** `ERSuperpolyLowerBound`.
- **30** `SuperpolyLowerBound`.
- **34** `PNotEqualsNP`, the only idea over `Complexity.lean`.

**No obligation def:** 02, 03, 04, 05, 07, 08, 11, 21, 24 and 27.
