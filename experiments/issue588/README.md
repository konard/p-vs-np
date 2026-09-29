# Issue #588 audit closure

Issue #588 audited `main` at `c4a7803d3f5f589b30a6ff2affba3ec087384c30` and
filed 18 defect reports (#570–#587). Each has been fixed by a merged pull
request that added a regression check. This directory contains the closure
record and tools to re-run the checks locally.

- `verify_audit.sh` runs every regression check for the 18 defects, grouped as
  `python`, `lean`, `rocq`, and `agda`. It runs all groups when called without
  arguments. A requested group fails if its tool is missing. Without a local
  `agda` binary, the Agda group uses the Docker image pinned by CI. The Lean
  group includes the contributor guide check, which requires `lake`. The Rocq
  group builds the root `_CoqProject` in dependency order, as CI does.
- `admission_inventory.py` recomputes the audit's admission counts, excluding
  comments and string literals. `test_admission_inventory.py` tests it.

```bash
bash experiments/issue588/verify_audit.sh                # all groups
bash experiments/issue588/verify_audit.sh python lean    # selected groups
python3 experiments/issue588/admission_inventory.py
```

## Defect status

| Issue | Severity | Defect | Fixed by | Regression check |
|-------|----------|--------|----------|------------------|
| #570 | Critical | Core P=NP framework derives `False` from `empty_in_P` | #592 | `experiments/issue570/check_contradiction.py` (Lean, Rocq) |
| #571 | Critical | Runtime-free definitions put every Boolean language in P | #591 | `experiments/issue571/check.sh`; shared Agda modules |
| #572 | High | Independence was impossible in Lean/Agda but `True` in Rocq | #601 | `experiments/issue572/Independent.{lean,v,agda}` |
| #573 | High | `PolyTimeReduction` ignored its function and required equal languages | #600 | `experiments/issue573/check.sh` (Lean, Rocq) |
| #574 | High | Polynomial predicates rejected `n + 1` | #599 | `experiments/issue574/PolynomialRegression.{lean,v}` |
| #575 | High | Lean verification failed; toolchain unpinned | #598 | `experiments/issue575/check.sh`, `lean-toolchain` = 4.34.1 |
| #576 | High | Status did not separate proved results from admissions | #597 | `scripts/check_proof_status.py`, `scripts/test_check_proof_status.py` |
| #577 | Critical | Plotnikov 2007 refutation asserted contradictions | #590 | `experiments/issue577/test_refutation_consistency.py` |
| #578 | Critical | Gubin 2010 refutation contradicted its own definitions | #589 | `scripts/check_gubin_audit.py`, `experiments/issue578/check_paper_lp.py` |
| #579 | High | Issue 7 research misapplied Shoenfield absoluteness | #596 | `experiments/issue579/check_claims.py`; issue 7 Lean experiments |
| #580 | High | Named refutations proved tautologies | #595 | `experiments/issue580/test_semantic_coverage.py` |
| #581 | Medium | Index hid legacy Lean/Rocq formalizations | #606 | `scripts/test_check_attempt_structure.py` |
| #582 | Medium | Checker marked empty directories complete | #605 | `scripts/test_check_attempt_structure.py` |
| #583 | High | Strict Woeginger check passed without its source | #594 | `scripts/test_check_attempt_structure.py` |
| #584 | High | Manual verification could skip both provers | #593 | `experiments/issue584/test_verification_workflow.py` |
| #585 | Medium | Guidance banned core Lean tactics and recommended `sorry` | #604 | `experiments/issue585/check_guidance.py` |
| #586 | Medium | Weiss growth proof used a false witness | #603 | `experiments/issue586/check.sh` |
| #587 | Medium | Kardash refutation said propagation decides 2-SAT | #602 | `experiments/issue587/test_kardash_2sat.py`, `check.sh` (Lean, Rocq) |

All checks except the local convenience runner were already in
`.github/workflows/verification.yml`. On `main` at `653b2f0`, run
[36338870065](https://github.com/konard/p-vs-np/actions/runs/36338870065)
passed them all.

## Local verification

On 2026-09-27, `verify_audit.sh` passed all four groups at `653b2f0` with
Lean 4.34.1, Rocq 9.2 (CI uses 9.0), and the CI Agda image. `lake build` completed all 193
jobs. The Rocq group compiled every `.v` file in the repository.

## Admission inventory

`admission_inventory.py --root` reproduces the audit's counts at `c4a7803`.

| Measure | Audit (`c4a7803`) | Now (`653b2f0`) |
|---------|-------------------|-----------------|
| Lean `sorry` | 393 in 115/189 files | 384 in 111/191 files |
| Rocq `Admitted`/`admit` | 480 in 119/188 files | 464 in 115/190 files |
| Lean `refutation/` files with admissions | 40/61 | 37/62 |
| Rocq `refutation/` files with admissions | 39/61 | 36/62 |

These admissions are in historical attempt material. The certified conclusions
listed in `scripts/proof_status.json` contain no admissions, and CI rejects any
axioms outside each theorem's allowance. With the offline checker, 39 of 116
attempts are complete under the stricter #582 rule. Completeness is still a
structural measure, not evidence of correctness.

## Remaining work outside the 18 reports

The audit noted that other per-attempt defects may remain. After these fixes,
the historical attempts still contain 38 Lean `axiom … : True` declarations in
21 files and 35 Rocq `Axiom … : True.` declarations in 18 files. For example,
`proofs/attempts/renjit-2006-conpeqnp/refutation/lean/RenjitRefutation.lean`
declares `axiom paper_withdrawn : True`. These declarations are logically
harmless, but a reader can mistake them for formalized claims. Like the
historical `sorry` admissions, they are outside the certified boundary.
Fixing them requires source-by-source reconstruction work like #580. This
repository does not resolve P vs NP.
