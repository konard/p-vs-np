# Full Cook–Levin continuation

The latest review requires the complete issue #624 result and reuse of checked
Lean/Rocq infrastructure. No impossibility of Cook–Levin in this model has been
established; missing proofs must not be described as a formal obstruction.

1. [x] Read issue #624, its complete comments, the edited PR #630 description,
   conversation comments, inline comments, reviews, and contributor guidance.
2. [x] Verify branch `issue-624-0b9b9b6c5d75`, clean initial status, recent CI
   timestamps/head SHAs, and inclusion of `origin/main`.
3. [x] Trace the shared machine, `Run`, `Reaches`, `Computes`, variable-length
   certificate fragment, finite windows, local CNF, and existing circuit model.
4. [ ] Build missing formula components with paired regressions first. The
   shared NAND-to-CNF and instruction-selection compilers are proved, but
   complete tableau transitions remain open. Reuse
   shared circuit/encoding/trace definitions; avoid certificate enumeration.
5. [ ] Prove both full tableau model directions and all negative examples.
6. [ ] Prove the full output-size bound, counting unary variable identifiers.
7. [ ] Construct one finite reduction machine for all inputs and prove its
   charged `Computes` bound; per-input fixed emitters are insufficient.
8. [ ] Assemble paired `satHard` and `cookLevin`, remove hardness arguments,
   register conclusions, and update all dependent documentation.
9. [x] Run complete local workflow checks and assumption audits. Preserve
   large outputs in `ci-logs/`; inspect logs after every background job ends.
10. [ ] Review the complete PR diff, commit atomic verified changes, push only
    the prepared branch, update the PR title/body, and check fresh CI SHA/time.
11. [ ] Download and inspect any failed CI logs, fix their specific errors,
    verify a clean working tree, and mark PR #630 ready on completion.

Experiments are finite. Any deliberate memory/stack probe must use resource
limits. All experiment files stay here. No unproved axiom, admission, freely
charged operation, or restricted verifier class may replace the endpoint.

## Verified compiler checkpoint

The paired `CircuitCNF` modules prove the three-clause NAND contract,
assignment agreement with the shared wire evaluator, acceptance
equisatisfiability including zero wires, and a polynomial bound on the
actual unary encoding when the total wire count is polynomially bounded.
Seven conclusions are registered in each prover. Existing circuit and
encoding proofs now use shared lemmas, with old public names retained.

All local Python, Lean, Rocq, and pinned Agda workflow checks pass. Lean
built 251 jobs; both whole-manifest audits passed for 126 registered
conclusions, including all 48 for #624 in each prover. The new Lean
compiler conclusions use only `propext` and `Quot.sound`; Rocq has no
global assumptions. Initial regression failures and full check logs
are preserved under `ci-logs/`.

The full tableau, full size bound, input-dependent reduction machine,
`satHard`, and `cookLevin` remain unproved. No formal impossibility has
been established, and this checkpoint does not supply one.

## Instruction selection checkpoint

The next continuation adds paired `MachineCNF` modules, reusing `LocalCNF`
implications and one-hot clauses. They compile the actual shared machine's
state/symbol lookup, prove model extraction and constructive representation,
reject an incorrect output instruction, and bound the actual unary encoded
length. Fourteen further conclusions per prover bring the #624 registration
count to 62 and the whole manifest to 140 per prover. Tape/head wiring and
successor configurations remain open. See [CI_CONTINUATION.md](CI_CONTINUATION.md)
for fresh failure diagnostics and this checkpoint's validation record.

## Finite-row successor checkpoint

`SuccessorCNF` now compiles one move between well-formed rows, extracts
configurations constructively, and proves equivalence to the original
charged `step`, including rejection at both window edges. Its clause,
variable, width, and actual unary encoded-size bounds are checked.
Thirty-eight further paired conclusions bring the #624 registration count
to 100 and the whole manifest to 178 per prover. Initial/certificate wiring,
active-prefix rows, accepting termination, the full encoded-size polynomial,
and the input-dependent reduction machine remain open.
[RESTART_PLAN.md](RESTART_PLAN.md) records this continuation and its validation.
