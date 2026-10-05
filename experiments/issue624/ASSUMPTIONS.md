# Assumption reports for the #624 prerequisites

Captured on 2026-10-05 with Lean 4.34.1 and Rocq 9.2. These reports apply to
certificate CNF and the semantic verifier interface, not to `satHard`,
`tableauCNF`, or a reduction machine. Those results remain unimplemented.

## Direct Lean reports

Command: `lake env lean experiments/issue624/CertificateRegression.lean`.
The regression runs these `#print axioms` queries after its examples.

```text
'Issue624.CertificateCNF.certificateCNF_models' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.encodeCertificate_models' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.decode_encodeCertificate' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.certificateCNF_polynomial_size' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.encode_certificateCNF_length' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.certificateCNF_variables' depends on axioms: [propext, Quot.sound]
'Issue624.CertificateCNF.overlong_rejected' depends on axioms: [propext, Quot.sound]
'Issue624.VerifierTableau.verifierTableau_iff_language' depends on axioms: [propext, Quot.sound]
'Issue624.VerifierTableau.maxClock_polynomial' depends on axioms: [propext, Quot.sound]
'Issue624.VerifierTableau.verifierTableau_span' depends on axioms: [propext, Quot.sound]
'Issue624.VerifierTableau.wrong_successor_not_model' depends on axioms: [propext, Quot.sound]
```

## Direct Rocq reports

Command: `rocq compile -Q proofs proofs -Q experiments experiments experiments/issue624/CertificateRegression.v`.
The regression runs each of the following `Print Assumptions` queries. Query
labels below associate the otherwise identical prover responses with their
statements, in source order.

```text
Print Assumptions certificateCNF_models.
Closed under the global context
Print Assumptions encodeCertificate_models.
Closed under the global context
Print Assumptions decode_encodeCertificate.
Closed under the global context
Print Assumptions certificateCNF_polynomial_size.
Closed under the global context
Print Assumptions encode_certificateCNF_length.
Closed under the global context
Print Assumptions certificateCNF_variables.
Closed under the global context
Print Assumptions CertificateCNF.overlong_rejected.
Closed under the global context
Print Assumptions VerifierTableau.verifierTableau_iff_language.
Closed under the global context
Print Assumptions VerifierTableau.maxClock_polynomial.
Closed under the global context
Print Assumptions VerifierTableau.verifierTableau_span.
Closed under the global context
Print Assumptions VerifierTableau.wrong_successor_not_model.
Closed under the global context
```

## Enforced manifest audit

Commands: `python3 scripts/check_proof_status.py --lean` and
`python3 scripts/check_proof_status.py --rocq`.
Both whole-manifest audits passed. Below are their actual output lines for
all 20 new public conclusions in each prover. Lean's allowed axioms are
`propext` and `Quot.sound`; the Rocq entries permit no assumptions. The checker
also scans the transitive source closure for admissions and new axioms.

```text
lean Issue624.CertificateCNF.certificateCNF_models: Quot.sound, propext
lean Issue624.CertificateCNF.decodeCertificate_length: Quot.sound, propext
lean Issue624.CertificateCNF.represents_length: Quot.sound, propext
lean Issue624.CertificateCNF.represents_decode: propext
lean Issue624.CertificateCNF.encodeCertificate_models: Quot.sound, propext
lean Issue624.CertificateCNF.decode_encodeCertificate: Quot.sound, propext
lean Issue624.CertificateCNF.certificateCNF_variables: Quot.sound, propext
lean Issue624.CertificateCNF.represents_sentinel: Quot.sound, propext
lean Issue624.CertificateCNF.overlong_rejected: Quot.sound, propext
lean Issue624.CertificateCNF.encode_certificateCNF_length: Quot.sound, propext
lean Issue624.CertificateCNF.certificateCNF_polynomial_size: Quot.sound, propext
lean Issue624.VerifierTableau.verifierRun_iff: propext
lean Issue624.VerifierTableau.verifierTableau_iff_language: Quot.sound, propext
lean Issue624.VerifierTableau.verifierTimeLimit_le: Quot.sound, propext
lean Issue624.VerifierTableau.maxClock_polynomial: Quot.sound, propext
lean Issue624.VerifierTableau.verifierInitial_span: Quot.sound, propext
lean Issue624.VerifierTableau.verifierTableau_span: Quot.sound, propext
lean Issue624.VerifierTableau.overlong_not_representable: Quot.sound, propext
lean Issue624.VerifierTableau.rejecting_verifier_no_tableau: Quot.sound, propext
lean Issue624.VerifierTableau.wrong_successor_not_model: Quot.sound, propext
rocq CertificateCNF.certificateCNF_models: (none)
rocq CertificateCNF.decodeCertificate_length: (none)
rocq CertificateCNF.represents_length: (none)
rocq CertificateCNF.represents_decode: (none)
rocq CertificateCNF.encodeCertificate_models: (none)
rocq CertificateCNF.decode_encodeCertificate: (none)
rocq CertificateCNF.certificateCNF_variables: (none)
rocq CertificateCNF.represents_sentinel: (none)
rocq CertificateCNF.overlong_rejected: (none)
rocq CertificateCNF.encode_certificateCNF_length: (none)
rocq CertificateCNF.certificateCNF_polynomial_size: (none)
rocq VerifierTableau.verifierRun_iff: (none)
rocq VerifierTableau.verifierTableau_iff_language: (none)
rocq VerifierTableau.verifierTimeLimit_le: (none)
rocq VerifierTableau.maxClock_polynomial: (none)
rocq VerifierTableau.verifierInitial_span: (none)
rocq VerifierTableau.verifierTableau_span: (none)
rocq VerifierTableau.overlong_not_representable: (none)
rocq VerifierTableau.rejecting_verifier_no_tableau: (none)
rocq VerifierTableau.wrong_successor_not_model: (none)
```
