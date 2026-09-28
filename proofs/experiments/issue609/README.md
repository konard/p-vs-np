# Issue #609: correcting the incoming P = NP proof sketches

Incoming PR #41's `PEqualsNPAttempt.lean` and `KnownBarriers.lean` are not in
`main`. This directory supplies paired Lean/Rocq replacements against the
current shared model. They do not import the old files or assert their global
axioms. The old PR must not be merged alongside its original proof files.

## Reproducing the defects in PR #41

1. Its global `axiom contradiction_from_separation : False` lets `False.elim`
   prove any proposition. Its `no_known_proof : RealPEqualsNPProof → False`
   also asserts nonexistence, which does not follow from lack of a known proof.
2. `SAT_Problem := fun _ => True` accepts an unsatisfiable CNF. In the shared
   model, `sat_has_no_instance` proves that the encoding of `[[]]` is rejected,
   while `sat_has_yes_instance` proves that the empty CNF is accepted. These
   two executable proof obligations would fail for the old constant predicate.
3. Its `ProofTechniqueRelativizes` reduces to `∀ A, True`. The claimed barrier
   theorem instantiated at `technique := False` then denies the valid
   implication `False → PEqualsNP`. The paired
   `false_technique_counterexample` theorem proves this counterexample.
4. The old circuit and oracle placeholders erase the data needed for their
   claimed results. A fixed `n^10` bound is not a superpolynomial lower bound.
   No natural-proof or algebrization result is claimed in these replacements.

## Verified scope

| Claim | Lean | Rocq |
| --- | --- | --- |
| A candidate machine has a polynomial `Run` bound and agrees with encoded SAT | `candidate_decides`, `candidate_on_encodings` | same names |
| A candidate implies P = NP **if `SATHard` is supplied** | `pEqualsNP_of_candidate` | same name |
| A candidate exists iff P = NP, given `SATHard` and the proved SAT verifier | `candidate_iff_pEqualsNP` | same name |
| SAT has both yes and no instances | `sat_has_yes_instance`, `sat_has_no_instance` | same names |
| The class P obligation is nontrivial | `not_every_language_inP` | same name |
| A separating world refutes a uniform equality proof, and an equality world refutes a uniform separation proof, when the technique applies there | `separation_refutes_uniform`, `equality_refutes_uniform` | same names |
| The constant-true and false-technique barrier claims fail in countermodels | `constant_true_not_uniform`, `constant_true_not_uniform_separation`, `false_technique_counterexample` | same names |

`Candidate` uses `Complexity.Machine`, `Complexity.Run`, and
`Issue532.Machines.SAT`. The latter decodes actual CNF formulas. The reverse
direction of `candidate_iff_pEqualsNP` uses `SATVerifier.satInNP`, and the
forward direction keeps `SATHard` (the
unproved hardness half of Cook–Levin in this repository) as an explicit
premise. No candidate SAT machine is constructed here.

The barrier file is an **abstract schema**: `P` and `NP` are parameters for
classes of languages in oracle worlds. The Boolean two-world model checks
non-vacuity; it is not an oracle-machine construction or a proof of a historical
barrier theorem. Formalizing the historical relativization, natural-proofs,
and algebrization results requires suitable oracle and circuit models.

## Verification

Run from the repository root:

```sh
lake build proofs.experiments.issue609.lean.PEqualsNPAttempt proofs.experiments.issue609.lean.KnownBarriers
rocq compile -Q . '' proofs/experiments/issue609/rocq/PEqualsNPAttempt.v
rocq compile -Q . '' proofs/experiments/issue609/rocq/KnownBarriers.v
python3 scripts/check_proof_status.py --lean
python3 scripts/check_proof_status.py --rocq
```

The paired conclusions and counterexamples are in `scripts/proof_status.json`.
The source audit rejects admissions and unapproved global assumptions in their
local import closures, while the prover queries report their transitive
assumptions. A clean global assumption report does not discharge the explicit
`SATHard` premise. PR #41's separate DPLL defect (issue #610) was fixed in
PR #616.
