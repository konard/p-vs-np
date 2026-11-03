# Experiments and Verification Reports

This directory holds regression checks, audit scripts, verification reports, and source material. It is not the place for the main formal results. Those live in [`proofs/experiments/`](../proofs/experiments/README.md) (certified issue experiments) and [`proofs/complexity/`](../proofs/complexity/README.md) (the shared model). Nothing here is a claimed proof of P = NP or P ≠ NP. The formal target and its status are described in [FORMAL_STATEMENT.md](../FORMAL_STATEMENT.md).

Many folders are named after the GitHub issue they reproduce or guard. CI runs several of them; see [`.github/workflows/verification.yml`](../.github/workflows/verification.yml) for the exact list. A folder without a README is described only by the table below and by its file headers.

## Regression checks and audits by issue

| Folder | Issue | Contents |
|---|---|---|
| [issue7/](issue7/) | [#7](https://github.com/konard/p-vs-np/issues/7) | Mutation test for the clocked-SAT claim checks (`check_claims_mutations.sh`) |
| [issue8/](issue8/) | [#8](https://github.com/konard/p-vs-np/issues/8) | Local replay of the Lean CI job (`local_lean_ci.sh`) |
| [issue44/](issue44/README.md) | [#44](https://github.com/konard/p-vs-np/issues/44) | Coverage check of the attempts catalog against Woeginger's list |
| [issue532/](issue532/) | [#532](https://github.com/konard/p-vs-np/issues/532) | Dossier checker and its tests; guide for rebasing ideas onto the shared machine model |
| [issue532_idea41/](issue532_idea41/) | #532 | Rocq assumption audit for the Idea 41 bridge |
| [issue532_primes/](issue532_primes/) | #532 | Lean and Rocq assumption audits for selected ideas |
| [issue532_satverifier/](issue532_satverifier/) | #532 | Lean and Rocq assumption audits for `SATVerifier` |
| [issue532_vacuity/](issue532_vacuity/REPORT.md) | #532 | Vacuity audit of the idea obligations, with Lean regressions that must fail |
| [issue567/](issue567/README.md) | [#567](https://github.com/konard/p-vs-np/issues/567) | Circuit decoder regressions and assumption audits |
| [issue568/](issue568/) | [#568](https://github.com/konard/p-vs-np/issues/568) | Lean and Rocq checks that the tableau theorems exist with the expected statements |
| [issue570/](issue570/) | [#570](https://github.com/konard/p-vs-np/issues/570) | Check that the old derivation of `False` in the legacy `p_eq_np` framework is rejected |
| [issue571/](issue571/) | [#571](https://github.com/konard/p-vs-np/issues/571) | Counterexample to the old runtime-free P definition, which must now fail |
| [issue572/](issue572/) | [#572](https://github.com/konard/p-vs-np/issues/572) | Lean, Rocq, and Agda regressions for the independence schema |
| [issue573/](issue573/README.md) | [#573](https://github.com/konard/p-vs-np/issues/573) | Reduction regression for the legacy `p_eq_np` framework |
| [issue574/](issue574/README.md) | [#574](https://github.com/konard/p-vs-np/issues/574) | Polynomial-bound regressions for the shared `PolynomiallyBounded` predicate |
| [issue575/](issue575/) | [#575](https://github.com/konard/p-vs-np/issues/575) | Pinned-toolchain Lean check |
| [issue576/](issue576/README.md) | [#576](https://github.com/konard/p-vs-np/issues/576) | Initial assumption-audit probe |
| [issue577/](issue577/README.md) | [#577](https://github.com/konard/p-vs-np/issues/577) | Plotnikov 2007 refutation consistency check |
| [issue578/](issue578/README.md) | [#578](https://github.com/konard/p-vs-np/issues/578) | Gubin 2010 LP reproduction and checks |
| [issue579/](issue579/) | [#579](https://github.com/konard/p-vs-np/issues/579) | Check against unsupported independence claims |
| [issue580/](issue580/README.md) | [#580](https://github.com/konard/p-vs-np/issues/580) | Zhu 2007 projector witness and semantic coverage test |
| [issue584/](issue584/) | [#584](https://github.com/konard/p-vs-np/issues/584) | Tests for the verification workflow's event and result handling |
| [issue585/](issue585/README.md) | [#585](https://github.com/konard/p-vs-np/issues/585) | Contributor-guide Lean example regression |
| [issue586/](issue586/README.md) | [#586](https://github.com/konard/p-vs-np/issues/586) | Weiss growth regression |
| [issue587/](issue587/README.md) | [#587](https://github.com/konard/p-vs-np/issues/587) | Kardash 2-SAT regression |
| [issue588/](issue588/README.md) | [#588](https://github.com/konard/p-vs-np/issues/588) | Repository audit closure and the admission inventory script |
| [issue611/](issue611/) | [#611](https://github.com/konard/p-vs-np/issues/611) | Test that `_CoqProject` stays in sync with the Rocq sources |
| [issue614/](issue614/) | [#614](https://github.com/konard/p-vs-np/issues/614) | Regression checks for the Williams framework files |

## Other material

| Path | Contents |
|---|---|
| [sat_solvers/](sat_solvers/) | A basic Python DPLL solver and its tests |
| [barron-romero-analysis/](barron-romero-analysis/), [frederic-gillet-2013/](frederic-gillet-2013/), [nicholas-argall-2003/](nicholas-argall-2003/), [panyukov-analysis/](panyukov-analysis/), [sanchez-guinea-research/](sanchez-guinea-research/), [louis-coder-2012.pdf](louis-coder-2012.pdf) | Source papers and notes for individual attempts in [`proofs/attempts/`](../proofs/attempts/README.md) |
| [issue28_verification.md](issue28_verification.md), [issue31_verification.md](issue31_verification.md), [implementation_plan.md](implementation_plan.md) | Historical verification reports for external critiques (issues #28 and #31) and the resulting plan |
| [issue7_undecidability_attempt.md](issue7_undecidability_attempt.md), [issue7_shoenfield_absoluteness.lean](issue7_shoenfield_absoluteness.lean), [issue7_undecidability_formalization.lean](issue7_undecidability_formalization.lean) | Earlier issue #7 write-up and Lean illustrations, corrected in #579. The current formal work is [`proofs/experiments/issue7/`](../proofs/experiments/issue7/README.md) |

## Related write-ups in `proofs/experiments/`

The corrected [Williams experiment](../proofs/experiments/p_not_equal_np_proof_attempt.md) explains the algorithm-to-lower-bound implication and its open premises. Its paired [Lean](../proofs/experiments/WilliamsFramework.lean) and [Rocq](../proofs/experiments/WilliamsFramework.v) regression checks import the shared Idea 41 model; `issue614/test_framework.py` reproduces the original compile failure. The issue #10 target `NP ⊈ P` is in [proofs/experiments/issue10](../proofs/experiments/issue10/README.md). The issue #8 target `NP ⊆ P`, a verified DPLL solver with its call bound, and the [corrected write-up](../proofs/experiments/np_subset_p_proof_attempt.md) are in [proofs/experiments/issue8](../proofs/experiments/issue8/README.md).
