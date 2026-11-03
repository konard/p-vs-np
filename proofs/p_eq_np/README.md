# Legacy P = NP toy framework

**Status: legacy, axiomatized, not certified.** This directory is a historical
toy model for hypothetical P = NP claims. It is **not** the repository's shared
complexity model, and nothing proved here is a statement about the Clay
problem. Issue [#627](https://github.com/konard/p-vs-np/issues/627) proposes
archiving it under `archive/`, as was done for Isabelle.

The repository's formal P and NP live in
[`proofs/complexity/`](../complexity/README.md). The formal target
`Complexity.PEqualsNP` and the list of named premises are described in
[FORMAL_STATEMENT.md](../../FORMAL_STATEMENT.md) and
[proofs/HYPOTHESES.md](../HYPOTHESES.md).

## What is here

| File | Checked by CI | Unproved content |
| --- | --- | --- |
| [`lean/PvsNP.lean`](lean/PvsNP.lean) | Compiled by `lake build` | 4 axioms: `P_subseteq_NP` (line 139), `P_eq_or_neq_NP` (150), `P_closed_under_complement` (432), `P_eq_NP_implies_NP_closed_complement` (436) |
| [`rocq/PvsNP.v`](rocq/PvsNP.v) | Compiled via `_CoqProject` | 3 `Admitted` (lines 81, 192, 524) and `Axiom P_eq_or_neq_NP` (205) |
| [`agda/PvsNP.agda`](agda/PvsNP.agda) | Not checked | 14 `postulate` blocks |

Compilation accepts axioms and admissions, so it does not certify these files.
None of their theorems is listed in
[`scripts/proof_status.json`](../../scripts/proof_status.json).

## Why it must not be read as the problem statement

- It defines its own `TuringMachine`, `InP`, `InNP`, `PEqualsNP`, and
  reduction notions. They compete with the shared definitions in
  `proofs/complexity/`.
- Its `InNP` verifier is a Boolean function with no machine runtime
  condition, so `P_subseteq_NP` is assumed rather than proved. In the shared
  model the corresponding facts are theorems: `Complexity.pSubsetNP` and
  `PvsNPDecidable.P_vs_NP_is_decidable`.
- A file that imports this framework can obtain such facts for free from the
  axioms. See error families 11 (incompatible formal definitions) and 12
  (smuggling the conclusion into an axiom) in
  [`proofs/attempts/COMMON_ERRORS.md`](../attempts/COMMON_ERRORS.md).

[ASSUMPTIONS.md](ASSUMPTIONS.md) records the assumption audit from issue
[#570](https://github.com/konard/p-vs-np/issues/570) and the remaining modeling
gaps. The regression checks in
[`experiments/issue570/`](../../experiments/issue570/) and
[`experiments/issue573/`](../../experiments/issue573/README.md) still use
these files.
