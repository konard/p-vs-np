# Issue 573 reduction regression

Status at 2026-11-03: a passing regression for issue #573 (closed). CI runs
`check.sh --lean` in the Lean job and `check.sh --rocq` in the Rocq job.

At `17e3305`, both `AuditBefore.lean` and `AuditBefore.v.in` prove that an
arbitrary Boolean function is a reduction to the singleton language `{[true]}`.
The old definition requires only a one-bit output-size bound; it does not
require a program that computes the Boolean function.

After the fix, run `bash experiments/issue573/check.sh --lean` and
`bash experiments/issue573/check.sh --rocq`. Each command checks that its
previously valid proof is rejected at the missing computation certificate.
The positive identity, composition, and bitwise-NOT examples are proved in
`proofs/p_eq_np/lean/PvsNP.lean` and `proofs/p_eq_np/rocq/PvsNP.v`. Those two
files are a legacy framework with its own P and NP. They carry axioms (and
the Rocq file carries `Admitted`), are not certified, and are slated for
archiving in [#627](https://github.com/konard/p-vs-np/issues/627).

The Rocq source has a `.v.in` suffix so the normal full-project scan does not
try to compile an intentionally failing proof.
