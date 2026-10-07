# Assumption reports for the #624 construction

Initial reports captured on 2026-10-05 with Lean 4.34.1 and Rocq 9.2.
The successor and accepting-trace compiler updates below were captured on
2026-10-06. These reports cover
certificate CNF, exact-clock recovery, fixed-window verifier semantics,
local CNF combinators, shared NAND-circuit, finite-row successor and bounded
accepting-trace compilers, and a finite fixed-output machine. The full tableau
and its unary size bound are covered by the continuation reports below.
`satHard` and the input-independent reduction machine remain
unimplemented.

## Direct Lean reports

The five paired regressions are `CertificateRegression`, `WindowRegression`,
`CNFRegression`, `EmitterRegression`, and `CircuitCNFRegression`. After `lake build`, run each with
`lake env lean experiments/issue624/<name>.lean`. Each prints the following
queries, in source order.

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
'Issue624.VerifierTableau.acceptingRun_timeLimit' depends on axioms: [propext]
'Issue624.VerifierTableau.envelopeTableau_iff_exact' depends on axioms: [propext, Quot.sound]
'Issue624.VerifierTableau.envelopeTableau_iff_language' depends on axioms: [propext, Quot.sound]
'Issue624.FixedWindow.windowVerifierTableau_iff_language' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.FixedWindow.run_fitWindow_iff' depends on axioms: [propext]
'Issue624.FixedWindow.trace_window_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.FixedWindow.windowWidth_polynomial' depends on axioms: [propext, Quot.sound]
'Issue624.LocalCNF.oneHot_models' depends on axioms: [propext, Quot.sound]
'Issue624.LocalCNF.implies_models' depends on axioms: [propext, Quot.sound]
'Issue624.LocalCNF.oneHot_encoded_size' depends on axioms: [propext, Quot.sound]
'Issue624.ConstantEmitter.emitter_computes' depends on axioms: [propext, Quot.sound]
'Issue624.CircuitCNF.acceptingCNF_iff' depends on axioms: [propext, Quot.sound]
'Issue624.CircuitCNF.circuitCNF_models' depends on axioms: [propext, Quot.sound]
'Issue624.CircuitCNF.acceptingCNF_encoded_size' depends on axioms: [propext, Quot.sound]
'Issue624.CircuitCNF.acceptingCNF_polynomial_size' depends on axioms: [propext, Quot.sound]
```

## Direct Rocq reports

Run `rocq compile -Q . '' experiments/issue624/<name>.v` after building the
imports, or use the complete `_CoqProject` build. Query labels associate each
prover response with its statement, in source order.

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
Print Assumptions VerifierTableau.acceptingRun_timeLimit.
Closed under the global context
Print Assumptions VerifierTableau.envelopeTableau_iff_exact.
Closed under the global context
Print Assumptions VerifierTableau.envelopeTableau_iff_language.
Closed under the global context
Print Assumptions windowVerifierTableau_iff_language.
Closed under the global context
Print Assumptions run_fitWindow_iff.
Closed under the global context
Print Assumptions trace_window_of_run.
Closed under the global context
Print Assumptions windowWidth_polynomial.
Closed under the global context
Print Assumptions oneHot_models.
Closed under the global context
Print Assumptions implies_models.
Closed under the global context
Print Assumptions oneHot_encoded_size.
Closed under the global context
Print Assumptions emitter_computes.
Closed under the global context
Print Assumptions acceptingCNF_iff.
Closed under the global context
Print Assumptions circuitCNF_models.
Closed under the global context
Print Assumptions acceptingCNF_encoded_size.
Closed under the global context
Print Assumptions acceptingCNF_polynomial_size.
Closed under the global context
```

## Enforced manifest audit

`python3 scripts/check_proof_status.py --lean` and `--rocq` both pass across
the whole manifest. The following are the actual audit lines for all 48
registered #624 conclusions in each prover. Lean uses only `propext`,
`Classical.choice`, and `Quot.sound`; Rocq entries permit no assumptions.
The checker also scans the transitive source closure for admissions and new
axioms. Only completed conclusions are registered.

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
lean Issue624.VerifierTableau.acceptingRun_timeLimit: propext
lean Issue624.VerifierTableau.envelopeTableau_iff_exact: Quot.sound, propext
lean Issue624.VerifierTableau.envelopeTableau_iff_language: Quot.sound, propext
lean Issue624.FixedWindow.tapeEquivalent_moveHead: propext
lean Issue624.FixedWindow.run_of_tapeEquivalent: propext
lean Issue624.FixedWindow.fitWindow_equivalent: propext
lean Issue624.FixedWindow.run_fitWindow_iff: propext
lean Issue624.FixedWindow.fitWindow_span: Quot.sound, propext
lean Issue624.FixedWindow.fitWindow_reserve: Classical.choice, Quot.sound, propext
lean Issue624.FixedWindow.trace_window_of_run: Classical.choice, Quot.sound, propext
lean Issue624.FixedWindow.accepting_trace_state_lt: propext
lean Issue624.FixedWindow.windowWidth_polynomial: Quot.sound, propext
lean Issue624.FixedWindow.windowVerifierTableau_iff_language: Classical.choice, Quot.sound, propext
lean Issue624.LocalCNF.implies_models: Quot.sound, propext
lean Issue624.LocalCNF.oneHot_models: Quot.sound, propext
lean Issue624.LocalCNF.cnf_encoded_size: Quot.sound, propext
lean Issue624.LocalCNF.oneHot_encoded_size: Quot.sound, propext
lean Issue624.CircuitCNF.gateCNF_models: Quot.sound, propext
lean Issue624.CircuitCNF.agrees_prefix: Quot.sound, propext
lean Issue624.CircuitCNF.agrees_append: Quot.sound, propext
lean Issue624.CircuitCNF.circuitCNF_models: Quot.sound, propext
lean Issue624.CircuitCNF.acceptingCNF_iff: Quot.sound, propext
lean Issue624.CircuitCNF.acceptingCNF_encoded_size: Quot.sound, propext
lean Issue624.CircuitCNF.acceptingCNF_polynomial_size: Quot.sound, propext
lean Issue624.ConstantEmitter.emitter_states: Quot.sound, propext
lean Issue624.ConstantEmitter.write_block: Quot.sound, propext
lean Issue624.ConstantEmitter.return_block: Quot.sound, propext
lean Issue624.ConstantEmitter.emitter_computes: Quot.sound, propext
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
rocq VerifierTableau.acceptingRun_timeLimit: (none)
rocq VerifierTableau.envelopeTableau_iff_exact: (none)
rocq VerifierTableau.envelopeTableau_iff_language: (none)
rocq FixedWindow.tapeEquivalent_moveHead: (none)
rocq FixedWindow.run_of_tapeEquivalent: (none)
rocq FixedWindow.fitWindow_equivalent: (none)
rocq FixedWindow.run_fitWindow_iff: (none)
rocq FixedWindow.fitWindow_span: (none)
rocq FixedWindow.fitWindow_reserve: (none)
rocq FixedWindow.trace_window_of_run: (none)
rocq FixedWindow.accepting_trace_state_lt: (none)
rocq FixedWindow.windowWidth_polynomial: (none)
rocq FixedWindow.windowVerifierTableau_iff_language: (none)
rocq LocalCNF.implies_models: (none)
rocq LocalCNF.oneHot_models: (none)
rocq LocalCNF.cnf_encoded_size: (none)
rocq LocalCNF.oneHot_encoded_size: (none)
rocq CircuitCNF.gateCNF_models: (none)
rocq CircuitCNF.agrees_prefix: (none)
rocq CircuitCNF.agrees_append: (none)
rocq CircuitCNF.circuitCNF_models: (none)
rocq CircuitCNF.acceptingCNF_iff: (none)
rocq CircuitCNF.acceptingCNF_encoded_size: (none)
rocq CircuitCNF.acceptingCNF_polynomial_size: (none)
rocq ConstantEmitter.emitter_states: (none)
rocq ConstantEmitter.write_block: (none)
rocq ConstantEmitter.return_block: (none)
rocq ConstantEmitter.emitter_computes: (none)
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

## Finite machine instruction compiler (2026-10-06)

The paired `MachineCNFRegression` files query the instruction compiler
against the original shared finite table and `step`. The 14 new manifest
entries per prover also audit the generic bounded lookup compiler and
negative case. These do not certify the outstanding Cook–Levin endpoint.

Lean 4.34.1 direct reports:

```text
'Issue624.MachineCNF.dispatchCNF_models' depends on axioms: [propext, Quot.sound]
'Issue624.MachineCNF.dispatchAssignment_models' depends on axioms: [propext, Quot.sound]
'Issue624.MachineCNF.instructionCode_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.MachineCNF.dispatchCNF_encoded_size' depends on axioms: [propext, Quot.sound]
'Issue624.MachineCNF.dispatchCNF_instruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.MachineCNF.dispatchCNF_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.MachineCNF.dispatchCNF_wrong_instruction' depends on axioms: [propext, Quot.sound]
'Issue624.MachineCNF.dispatchCNF_polynomial_size' depends on axioms: [propext, Quot.sound]
```

Rocq 9.2 reports `Closed under the global context` for each of the eight
corresponding direct queries. Both full manifest audits enforce the allowed
assumptions independently. No admissions or new axioms are introduced.

## Finite-row successor compiler (2026-10-06)

`SuccessorRegression.lean` and `SuccessorRegression.v` print these nine
main conclusions after checking the concrete positive and negative cases.
The Lean decoder uses bounded list search. Its proof reports and those of
the original-step correspondence use only the standard permitted assumptions.

```text
'Issue624.SuccessorCNF.rowAssignment_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.rowCNF_models' depends on axioms: [propext, Quot.sound]
'Issue624.SuccessorCNF.decodeRow_represents' depends on axioms: [propext, Quot.sound]
'Issue624.SuccessorCNF.moveHead_matches' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.transitionCNF_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.successorCNF_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.successorCNF_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.successorCNF_decoded_wrong_successor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Issue624.SuccessorCNF.successorCNF_encoded_size' depends on axioms: [propext, Quot.sound]
```

The matching Rocq queries, in the same order, are:

```text
Print Assumptions rowAssignment_represents.
Closed under the global context
Print Assumptions rowCNF_models.
Closed under the global context
Print Assumptions decodeRow_represents.
Closed under the global context
Print Assumptions moveHead_matches.
Closed under the global context
Print Assumptions transitionCNF_step.
Closed under the global context
Print Assumptions successorCNF_models.
Closed under the global context
Print Assumptions successorCNF_sound.
Closed under the global context
Print Assumptions successorCNF_decoded_wrong_successor.
Closed under the global context
Print Assumptions successorCNF_encoded_size.
Closed under the global context
```

The full local verification suites pass with 178 registered conclusions in
each prover, including 100 for #624. The following are the actual audit
lines for all 38 new successor conclusions in each prover. Each new Lean
manifest policy is restricted to its reported assumptions; all new Rocq
policies are empty. Existing policies remain unchanged.

```text
lean Issue624.SuccessorCNF.flatten_length: Quot.sound, propext
lean Issue624.SuccessorCNF.cell_head: Quot.sound, propext
lean Issue624.SuccessorCNF.decodeConfig_flatten: Quot.sound, propext
lean Issue624.SuccessorCNF.flatten_injective: Quot.sound, propext
lean Issue624.SuccessorCNF.moveHead_flatten: Quot.sound, propext
lean Issue624.SuccessorCNF.rowAssignment_state: Quot.sound, propext
lean Issue624.SuccessorCNF.rowAssignment_head: Quot.sound, propext
lean Issue624.SuccessorCNF.rowAssignment_cell: Quot.sound, propext
lean Issue624.SuccessorCNF.rowAssignment_represents: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.rowRepresents_models: Quot.sound, propext
lean Issue624.SuccessorCNF.selectedIndex_selected: Quot.sound, propext
lean Issue624.SuccessorCNF.decodeConfig_shape: Quot.sound, propext
lean Issue624.SuccessorCNF.rowCNF_models: Quot.sound, propext
lean Issue624.SuccessorCNF.selected_true_iff: (none)
lean Issue624.SuccessorCNF.guard_models: Quot.sound, propext
lean Issue624.SuccessorCNF.inside_of_moveHead_span: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.moveHead_cells: Quot.sound, propext
lean Issue624.SuccessorCNF.config_eq_of_cells: Quot.sound, propext
lean Issue624.SuccessorCNF.decodeRow_represents: Quot.sound, propext
lean Issue624.SuccessorCNF.moveHead_matches: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.copyRules_models: Quot.sound, propext
lean Issue624.SuccessorCNF.copyRules_cells: propext
lean Issue624.SuccessorCNF.instructionRules_models: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.nextHead_lt: Quot.sound, propext
lean Issue624.SuccessorCNF.instructionRules_step: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.transitionCNF_step: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_step: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_models: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_sound: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_decoded_wrong_successor: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_wrong_successor: Classical.choice, Quot.sound, propext
lean Issue624.SuccessorCNF.rowCNF_length: Quot.sound, propext
lean Issue624.SuccessorCNF.rowCNF_bounds: Quot.sound, propext
lean Issue624.SuccessorCNF.instructionRules_length: Quot.sound, propext
lean Issue624.SuccessorCNF.instructionRules_bounds: Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_length: Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_bounds: Quot.sound, propext
lean Issue624.SuccessorCNF.successorCNF_encoded_size: Quot.sound, propext
rocq SuccessorCNF.flatten_length: (none)
rocq SuccessorCNF.cell_head: (none)
rocq SuccessorCNF.decodeConfig_flatten: (none)
rocq SuccessorCNF.flatten_injective: (none)
rocq SuccessorCNF.moveHead_flatten: (none)
rocq SuccessorCNF.rowAssignment_state: (none)
rocq SuccessorCNF.rowAssignment_head: (none)
rocq SuccessorCNF.rowAssignment_cell: (none)
rocq SuccessorCNF.rowAssignment_represents: (none)
rocq SuccessorCNF.rowRepresents_models: (none)
rocq SuccessorCNF.selectedIndex_selected: (none)
rocq SuccessorCNF.decodeConfig_shape: (none)
rocq SuccessorCNF.rowCNF_models: (none)
rocq SuccessorCNF.selected_true_iff: (none)
rocq SuccessorCNF.guard_models: (none)
rocq SuccessorCNF.inside_of_moveHead_span: (none)
rocq SuccessorCNF.moveHead_cells: (none)
rocq SuccessorCNF.config_eq_of_cells: (none)
rocq SuccessorCNF.decodeRow_represents: (none)
rocq SuccessorCNF.moveHead_matches: (none)
rocq SuccessorCNF.copyRules_models: (none)
rocq SuccessorCNF.copyRules_cells: (none)
rocq SuccessorCNF.instructionRules_models: (none)
rocq SuccessorCNF.nextHead_lt: (none)
rocq SuccessorCNF.instructionRules_step: (none)
rocq SuccessorCNF.transitionCNF_step: (none)
rocq SuccessorCNF.successorCNF_step: (none)
rocq SuccessorCNF.successorCNF_models: (none)
rocq SuccessorCNF.successorCNF_sound: (none)
rocq SuccessorCNF.successorCNF_decoded_wrong_successor: (none)
rocq SuccessorCNF.successorCNF_wrong_successor: (none)
rocq SuccessorCNF.rowCNF_length: (none)
rocq SuccessorCNF.rowCNF_bounds: (none)
rocq SuccessorCNF.instructionRules_length: (none)
rocq SuccessorCNF.instructionRules_bounds: (none)
rocq SuccessorCNF.successorCNF_length: (none)
rocq SuccessorCNF.successorCNF_bounds: (none)
rocq SuccessorCNF.successorCNF_encoded_size: (none)
```

## Accepting-trace compiler and shared polynomial arithmetic

Captured on 2026-10-06 with `python3 experiments/issue624/run_assumptions.py`.
The script checks paired public names and reuses the kernel-query code from
`scripts/check_proof_status.py`. All entries below are registered with exactly
the reported assumptions. These trace results do not supply initial
input/certificate wiring or the charged reduction machine.

```text
lean Issue624.RunCNF.guarded_models: Quot.sound, propext
lean Issue624.RunCNF.haltRule_models: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.haltCNF_step: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.runCNF_unfold: Quot.sound, propext
lean Issue624.RunCNF.decodeTrace_length: Quot.sound, propext
lean Issue624.RunCNF.runCNF_sound: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.runCNF_complete: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.runCNF_models: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.runCNF_wrong_successor_rejected: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.rowRepresents_congr: Quot.sound, propext
lean Issue624.RunCNF.traceRepresents_congr: Quot.sound, propext
lean Issue624.RunCNF.traceAssignment_represents: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.decodeTrace_represents: Quot.sound, propext
lean Issue624.RunCNF.runCNF_traceAssignment: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.traceRepresents_width: propext
lean Issue624.RunCNF.runCNF_iff: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.runCNF_rejecting_unsatisfiable: Classical.choice, Quot.sound, propext
lean Issue624.RunCNF.haltCNF_length: Quot.sound, propext
lean Issue624.RunCNF.haltCNF_bounds: Quot.sound, propext
lean Issue624.RunCNF.runCNF_length: Quot.sound, propext
lean Issue624.RunCNF.guarded_bounds: Quot.sound, propext
lean Issue624.RunCNF.runCNF_bounds: Quot.sound, propext
lean Issue624.RunCNF.runCNF_encoded_size: Quot.sound, propext
lean Issue624.RunCNF.runCNF_polynomial_size: Quot.sound, propext
lean Complexity.polyAdd_eval: propext
lean Complexity.polyMul_eval: Quot.sound, propext
rocq RunCNF.guarded_models: (none)
rocq RunCNF.haltRule_models: (none)
rocq RunCNF.haltCNF_step: (none)
rocq RunCNF.runCNF_unfold: (none)
rocq RunCNF.decodeTrace_length: (none)
rocq RunCNF.runCNF_sound: (none)
rocq RunCNF.runCNF_complete: (none)
rocq RunCNF.runCNF_models: (none)
rocq RunCNF.runCNF_wrong_successor_rejected: (none)
rocq RunCNF.rowRepresents_congr: (none)
rocq RunCNF.traceRepresents_congr: (none)
rocq RunCNF.traceAssignment_represents: (none)
rocq RunCNF.decodeTrace_represents: (none)
rocq RunCNF.runCNF_traceAssignment: (none)
rocq RunCNF.traceRepresents_width: (none)
rocq RunCNF.runCNF_iff: (none)
rocq RunCNF.runCNF_rejecting_unsatisfiable: (none)
rocq RunCNF.haltCNF_length: (none)
rocq RunCNF.haltCNF_bounds: (none)
rocq RunCNF.runCNF_length: (none)
rocq RunCNF.guarded_bounds: (none)
rocq RunCNF.runCNF_bounds: (none)
rocq RunCNF.runCNF_encoded_size: (none)
rocq RunCNF.runCNF_polynomial_size: (none)
rocq Complexity.polyAdd_eval: (none)
rocq Complexity.polyMul_eval: (none)
```

## Initial row and full tableau

Captured on 2026-10-06 with the extended `run_assumptions.py`. The 30 new
paired public conclusions are registered with exactly their kernel-reported
assumptions. The seven full-tableau endpoint types also match the unchanged
completion contracts; the reduction and hardness endpoints are still absent.

```text
lean Issue624.InitialCNF.sourceCNF_models: Quot.sound, propext
lean Issue624.InitialCNF.tapeCNF_models: Quot.sound, propext
lean Issue624.InitialCNF.tapeSelected_iff: Quot.sound, propext
lean Issue624.InitialCNF.certificateSources_length: propext
lean Issue624.InitialCNF.certificateSources_eval: Quot.sound, propext
lean Issue624.InitialCNF.windowSources_length: Quot.sound, propext
lean Issue624.InitialCNF.windowSources_eval: Quot.sound, propext
lean Issue624.InitialCNF.initialCNF_models: Quot.sound, propext
lean Issue624.InitialCNF.sourceCNF_length: Quot.sound, propext
lean Issue624.InitialCNF.sourceCNF_bounds: Classical.choice, Quot.sound, propext
lean Issue624.InitialCNF.tapeCNF_length: Quot.sound, propext
lean Issue624.InitialCNF.tapeCNF_bounds: Classical.choice, Quot.sound, propext
lean Issue624.InitialCNF.certificateSources_bound: Quot.sound, propext
lean Issue624.InitialCNF.windowSources_bound: Quot.sound, propext
lean Issue624.InitialCNF.initialCNF_length: Quot.sound, propext
lean Issue624.InitialCNF.initialCNF_bounds: Classical.choice, Quot.sound, propext
lean Issue624.InitialCNF.initialCNF_polynomial_size: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.sources_length: Quot.sound, propext
lean Issue624.CookLevin.initialRow_span: Quot.sound, propext
lean Issue624.CookLevin.initialCNF_row: Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_unfold: propext
lean Issue624.CookLevin.tableauCNF_sound: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.decodeCertificate_congr: Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_complete: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_iff: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_rejecting_unsatisfiable: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_overlong_rejected: Quot.sound, propext
lean Issue624.CookLevin.tableauCNF_wrong_successor_rejected: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.encodeCNF_length_append: propext
lean Issue624.CookLevin.tableauCNF_encoded_size: Classical.choice, Quot.sound, propext
rocq InitialCNF.sourceCNF_models: (none)
rocq InitialCNF.tapeCNF_models: (none)
rocq InitialCNF.tapeSelected_iff: (none)
rocq InitialCNF.certificateSources_length: (none)
rocq InitialCNF.certificateSources_eval: (none)
rocq InitialCNF.windowSources_length: (none)
rocq InitialCNF.windowSources_eval: (none)
rocq InitialCNF.initialCNF_models: (none)
rocq InitialCNF.sourceCNF_length: (none)
rocq InitialCNF.sourceCNF_bounds: (none)
rocq InitialCNF.tapeCNF_length: (none)
rocq InitialCNF.tapeCNF_bounds: (none)
rocq InitialCNF.certificateSources_bound: (none)
rocq InitialCNF.windowSources_bound: (none)
rocq InitialCNF.initialCNF_length: (none)
rocq InitialCNF.initialCNF_bounds: (none)
rocq InitialCNF.initialCNF_polynomial_size: (none)
rocq CookLevin.sources_length: (none)
rocq CookLevin.initialRow_span: (none)
rocq CookLevin.initialCNF_row: (none)
rocq CookLevin.tableauCNF_unfold: (none)
rocq CookLevin.tableauCNF_sound: (none)
rocq CookLevin.decodeCertificate_congr: (none)
rocq CookLevin.tableauCNF_complete: (none)
rocq CookLevin.tableauCNF_iff: (none)
rocq CookLevin.tableauCNF_rejecting_unsatisfiable: (none)
rocq CookLevin.tableauCNF_overlong_rejected: (none)
rocq CookLevin.tableauCNF_wrong_successor_rejected: (none)
rocq CookLevin.encodeCNF_length_append: (none)
rocq CookLevin.tableauCNF_encoded_size: (none)
```

## Existing Idea 36 bridge

The bridge's required type already has no SAT-hardness premise. The paired
registration retains its separate vertex-cover hardness and rounding premises,
as required by the original completion contract. `existing_bridge_probe.py`
checks that unapplied type and its kernel-reported assumptions:

```text
lean Issue532.Idea36.exactRounding_gives_pEqualsNP: Classical.choice, Quot.sound, propext
rocq Idea36.exactRounding_gives_pEqualsNP: (none)
```

## Charged counter and shared tape scans (2026-10-06)

Run `python3 experiments/issue624/counter_assumptions.py` after building
the paired modules to reproduce these 11 reports per prover. They cover
the fixed counter table, actual-input setup, composed 16-state block,
exact charged times, polynomial bounds, and shared scan/composition lemmas.
The manifest allows only each entry’s kernel-reported assumptions.

```text
lean Issue624.UnaryCounter.counter_cycle: Quot.sound, propext
lean Issue624.UnaryCounter.counter_reaches: Quot.sound, propext
lean Issue624.UnaryCounter.countTime_polynomial: Quot.sound, propext
lean Issue624.UnaryCounter.counter_append: Quot.sound, propext
lean Issue624.UnaryCounter.prepare_reaches: Quot.sound, propext
lean Issue624.UnaryCounter.countedInput_reaches: Quot.sound, propext
lean Issue624.UnaryCounter.inputTime_polynomial: Quot.sound, propext
lean Issue532.Machines.Reaches.trans: propext
lean Issue532.Machines.scan_right: propext
lean Issue532.Machines.scan_left: propext
lean Issue532.Machines.reaches_append_right: Quot.sound, propext
rocq UnaryCounter.counter_cycle: (none)
rocq UnaryCounter.counter_reaches: (none)
rocq UnaryCounter.countTime_polynomial: (none)
rocq UnaryCounter.counter_append: (none)
rocq UnaryCounter.prepare_reaches: (none)
rocq UnaryCounter.countedInput_reaches: (none)
rocq UnaryCounter.inputTime_polynomial: (none)
rocq Machines.reaches_trans: (none)
rocq Machines.scan_right: (none)
rocq Machines.scan_left: (none)
rocq Machines.reaches_append_right: (none)
```

The paired `CounterRegression` files also query the main block contracts
directly. This audit does not establish the missing formula reduction,
`satHard`, or `cookLevin`; the full completion gate remains required.

## Finite tableau schema (2026-10-07)

The schema continuation registers 42 additional conclusions per prover:
39 paired schema lemmas, `tableauSchema`, and the two consuming `CookLevin`
equations. Their exact assumption sets are recorded in
`scripts/proof_status.json` and reproduced by
`python3 scripts/check_proof_status.py --lean --rocq` after building both
projects. The manifest now contains 288 conclusions per prover.

Every new Rocq conclusion is closed under the global context. New Lean
conclusions use only their individual kernel-reported subsets of `propext`,
`Quot.sound`, and `Classical.choice`. In particular:

```text
lean Issue624.Schema.tableauSchema: propext
lean Issue624.Schema.tableauSchema_fragments: Classical.choice, Quot.sound, propext
lean Issue624.CookLevin.tableauSchema_eq: propext
lean Issue624.CookLevin.tableauCNF_fragments: Classical.choice, Quot.sound, propext
rocq Schema.tableauSchema: (none)
rocq Schema.tableauSchema_fragments: (none)
rocq CookLevin.tableauSchema_eq: (none)
rocq CookLevin.tableauCNF_fragments: (none)
```

Two existing consuming proofs, `CookLevin.tableauCNF_unfold` and
`CookLevin.tableauCNF_overlong_rejected`, now also report `Classical.choice`,
`Quot.sound`, and `propext` in Lean because they use the schema equality.
Their individual manifest entries are refreshed to those exact reports.
The permitted assumptions of the completion gate remain unchanged.

These equations preserve the original tableau contracts through exact list
equality. They do not discharge `red_computes`, `satHard`, or `cookLevin`;
the completion preflight still reports the same 42 diagnostics.

## Charged register program reports (2026-10-07)

`python3 experiments/issue624/register_assumptions.py` queries all 33 paired
conclusions. `RegisterRegression` independently prints the eight main contracts.
The generated finite tables use the shared charged machine semantics and
`appendMachine`; no additional assumptions or counter semantics are introduced.

```text
lean Issue624.RegisterMachine.tape_append: propext
lean Issue624.RegisterMachine.tape_cons: propext
lean Issue624.RegisterMachine.tape_nonblank: Quot.sound, propext
lean Issue624.RegisterMachine.seekRows_length: propext
lean Issue624.RegisterMachine.seek_states: propext
lean Issue624.RegisterMachine.push_states: propext
lean Issue624.RegisterMachine.seekRows_get: Quot.sound, propext
lean Issue624.RegisterMachine.seek_instruction: Quot.sound, propext
lean Issue624.RegisterMachine.seek_scan: Quot.sound, propext
lean Issue624.RegisterMachine.seek_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.grow_carry_instruction: propext
lean Issue624.RegisterMachine.shift_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.grow_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.push_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.pushWord_states: propext
lean Issue624.RegisterMachine.wordTime_succ: Quot.sound, propext
lean Issue624.RegisterMachine.pushWord_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.wordTime_polynomial: Quot.sound, propext
lean Issue624.RegisterMachine.incr_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.emitConst_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.incrementRegs_length: propext
lean Issue624.RegisterMachine.incrementRegs_split: propext
lean Issue624.RegisterMachine.register_decomposition: propext
lean Issue624.RegisterMachine.runProg_regs_length: propext
lean Issue624.RegisterMachine.increment_state_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.compile_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.tape_regWords_length: Quot.sound, propext
lean Issue624.RegisterMachine.blocks_length: Quot.sound, propext
lean Issue624.RegisterMachine.incrementRegs_sum: propext
lean Issue624.RegisterMachine.runProg_tape_length: Quot.sound, propext
lean Issue624.RegisterMachine.wordTime_add: Quot.sound, propext
lean Issue624.RegisterMachine.cost_eq_wordTime: Quot.sound, propext
lean Issue624.RegisterMachine.cost_polynomial: Quot.sound, propext
rocq RegisterMachine.tape_append: (none)
rocq RegisterMachine.tape_cons: (none)
rocq RegisterMachine.tape_nonblank: (none)
rocq RegisterMachine.seekRows_length: (none)
rocq RegisterMachine.seek_states: (none)
rocq RegisterMachine.push_states: (none)
rocq RegisterMachine.seekRows_get: (none)
rocq RegisterMachine.seek_instruction: (none)
rocq RegisterMachine.seek_scan: (none)
rocq RegisterMachine.seek_reaches: (none)
rocq RegisterMachine.grow_carry_instruction: (none)
rocq RegisterMachine.shift_reaches: (none)
rocq RegisterMachine.grow_reaches: (none)
rocq RegisterMachine.push_reaches: (none)
rocq RegisterMachine.pushWord_states: (none)
rocq RegisterMachine.wordTime_succ: (none)
rocq RegisterMachine.pushWord_reaches: (none)
rocq RegisterMachine.wordTime_polynomial: (none)
rocq RegisterMachine.incr_reaches: (none)
rocq RegisterMachine.emitConst_reaches: (none)
rocq RegisterMachine.incrementRegs_length: (none)
rocq RegisterMachine.incrementRegs_split: (none)
rocq RegisterMachine.register_decomposition: (none)
rocq RegisterMachine.runProg_regs_length: (none)
rocq RegisterMachine.increment_state_reaches: (none)
rocq RegisterMachine.compile_reaches: (none)
rocq RegisterMachine.tape_regWords_length: (none)
rocq RegisterMachine.blocks_length: (none)
rocq RegisterMachine.incrementRegs_sum: (none)
rocq RegisterMachine.runProg_tape_length: (none)
rocq RegisterMachine.wordTime_add: (none)
rocq RegisterMachine.cost_eq_wordTime: (none)
rocq RegisterMachine.cost_polynomial: (none)
```

These contracts establish insertion into any delimited block, fixed-count
unary register increment, constant output append, and the straight-line `Prog`
compiler. `compile_reaches` checks pure `runProg` and exact `cost` semantics.
The compiler preserves input and register count and returns the head to home;
`cost_eq_wordTime` accounts for tape growth between instructions. Dynamic
arithmetic, loops, the final reduction machine and charged `Computes` proof,
and hardness remain outstanding.

## Dynamic register continuation (2026-10-07)

Both kernels checked 21 additional conclusions, bringing the manifest to
342 results per prover. The generated unary decrement/clear tables preserve
surrounding blocks. Their consuming compiler composition and its polynomial
cost bound are included below. Lean permits only the exact reported subsets
of its existing three logical axioms; all new Rocq conclusions are closed
under the global context. No reduction or hardness endpoint is registered.

Reproduce these reports with
`python3 experiments/issue624/dynamic_assumptions.py`.

```text
lean Issue624.RegisterMachine.pop_states: propext
lean Issue624.RegisterMachine.clear_states: propext
lean Issue624.RegisterMachine.delete_shift: propext
lean Issue624.RegisterMachine.delete_positive: Quot.sound, propext
lean Issue624.RegisterMachine.delete_empty: Quot.sound, propext
lean Issue624.RegisterMachine.pop_positive: Quot.sound, propext
lean Issue624.RegisterMachine.pop_empty: Quot.sound, propext
lean Issue624.RegisterMachine.clearTime_succ: Quot.sound, propext
lean Issue624.RegisterMachine.clearTarget_inside: (none)
lean Issue624.RegisterMachine.clearTarget_positive: propext
lean Issue624.RegisterMachine.clearTarget_empty: Classical.choice, Quot.sound, propext
lean Issue624.RegisterMachine.clear_reaches: Classical.choice, Quot.sound, propext
lean Issue624.RegisterMachine.clearTime_polynomial: Quot.sound, propext
lean Issue624.RegisterMachine.clear_then_compile_reaches: Classical.choice, Quot.sound, propext
lean Issue624.RegisterMachine.clear_then_cost_polynomial: Quot.sound, propext
lean Issue532.Machines.reaches_of_similar: propext
lean Issue532.Machines.BlankPad.trans: Quot.sound, propext
lean Issue532.Machines.Similar.trans: Quot.sound, propext
lean Issue532.Machines.retarget_instruction: propext
lean Issue532.Machines.retarget_moveHead: (none)
lean Issue532.Machines.retarget_reaches: Quot.sound, propext
rocq RegisterMachine.pop_states: (none)
rocq RegisterMachine.clear_states: (none)
rocq RegisterMachine.delete_shift: (none)
rocq RegisterMachine.delete_positive: (none)
rocq RegisterMachine.delete_empty: (none)
rocq RegisterMachine.pop_positive: (none)
rocq RegisterMachine.pop_empty: (none)
rocq RegisterMachine.clearTime_succ: (none)
rocq RegisterMachine.clearTarget_inside: (none)
rocq RegisterMachine.clearTarget_positive: (none)
rocq RegisterMachine.clearTarget_empty: (none)
rocq RegisterMachine.clear_reaches: (none)
rocq RegisterMachine.clearTime_polynomial: (none)
rocq RegisterMachine.clear_then_compile_reaches: (none)
rocq RegisterMachine.clear_then_cost_polynomial: (none)
rocq Machines.reaches_of_similar: (none)
rocq Machines.blankPad_trans: (none)
rocq Machines.similar_trans: (none)
rocq Machines.retarget_instruction: (none)
rocq Machines.retarget_moveHead: (none)
rocq Machines.retarget_reaches: (none)
```


## Charged unary loop and literal continuation (2026-10-07)

Both kernels checked 31 additional conclusions, bringing the manifest to
373 results per prover. The loop's exact cost includes the backward jump and
final empty-counter test. Its body must preserve the counter; all other
register/output writes come from the existing well-formed straight-line
compiler. The dynamic tick emitter and its consuming `encodeLit` emitter
preserve surrounding blocks and have explicit quadratic charged bounds.

Reproduce these reports with
`python3 experiments/issue624/loop_assumptions.py`. All new Rocq conclusions
are closed under the global context. No reduction or hardness endpoint is
registered; copying, nested schema loops, input reads and final assembly are
still outstanding.

```text
lean Issue624.RegisterMachine.repeatHead_states: propext
lean Issue624.RegisterMachine.repeatBase_states: propext
lean Issue624.RegisterMachine.repeatMachine_states: propext
lean Issue624.RegisterMachine.repeatHeadTarget_inside: Quot.sound, propext
lean Issue624.RegisterMachine.repeatTarget_inside: (none)
lean Issue624.RegisterMachine.repeatHeadTarget_positive: Quot.sound, propext
lean Issue624.RegisterMachine.repeatHeadTarget_empty: propext
lean Issue624.RegisterMachine.repeatTarget_back: propext
lean Issue624.RegisterMachine.repeatTarget_exit: Quot.sound, propext
lean Issue624.RegisterMachine.repeat_empty: Quot.sound, propext
lean Issue624.RegisterMachine.repeat_positive: Quot.sound, propext
lean Issue624.RegisterMachine.similar_shiftConfig: (none)
lean Issue624.RegisterMachine.similar_retargetConfig: (none)
lean Issue624.RegisterMachine.repeat_body_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.registerAt_split: Quot.sound, propext
lean Issue624.RegisterMachine.putRegister_split: Quot.sound, propext
lean Issue624.RegisterMachine.putRegister_length: propext
lean Issue624.RegisterMachine.registerAt_putRegister: propext
lean Issue624.RegisterMachine.incrementRegs_readOnly: propext
lean Issue624.RegisterMachine.runProg_readOnly: propext
lean Issue624.RegisterMachine.repeatPrefix_split: propext
lean Issue624.RegisterMachine.repeatSuffix_split: Quot.sound, propext
lean Issue624.RegisterMachine.repeat_compile_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.repeatRun_ticks: Quot.sound, propext
lean Issue624.RegisterMachine.repeatCost_ticks: Quot.sound, propext
lean Issue624.RegisterMachine.ticksTime_polynomial: Quot.sound, propext
lean Issue624.RegisterMachine.emitTicks_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.compose_home_reaches: Quot.sound, propext
lean Issue624.RegisterMachine.ticks_eq_replicate: Quot.sound, propext
lean Issue624.RegisterMachine.literalTime_polynomial: Quot.sound, propext
lean Issue624.RegisterMachine.emitLiteral_reaches: Quot.sound, propext
rocq RegisterMachine.repeatHead_states: (none)
rocq RegisterMachine.repeatBase_states: (none)
rocq RegisterMachine.repeatMachine_states: (none)
rocq RegisterMachine.repeatHeadTarget_inside: (none)
rocq RegisterMachine.repeatTarget_inside: (none)
rocq RegisterMachine.repeatHeadTarget_positive: (none)
rocq RegisterMachine.repeatHeadTarget_empty: (none)
rocq RegisterMachine.repeatTarget_back: (none)
rocq RegisterMachine.repeatTarget_exit: (none)
rocq RegisterMachine.repeat_empty: (none)
rocq RegisterMachine.repeat_positive: (none)
rocq RegisterMachine.similar_shiftConfig: (none)
rocq RegisterMachine.similar_retargetConfig: (none)
rocq RegisterMachine.repeat_body_reaches: (none)
rocq RegisterMachine.registerAt_split: (none)
rocq RegisterMachine.putRegister_split: (none)
rocq RegisterMachine.putRegister_length: (none)
rocq RegisterMachine.registerAt_putRegister: (none)
rocq RegisterMachine.incrementRegs_readOnly: (none)
rocq RegisterMachine.runProg_readOnly: (none)
rocq RegisterMachine.repeatPrefix_split: (none)
rocq RegisterMachine.repeatSuffix_split: (none)
rocq RegisterMachine.repeat_compile_reaches: (none)
rocq RegisterMachine.repeatRun_ticks: (none)
rocq RegisterMachine.repeatCost_ticks: (none)
rocq RegisterMachine.ticksTime_polynomial: (none)
rocq RegisterMachine.emitTicks_reaches: (none)
rocq RegisterMachine.compose_home_reaches: (none)
rocq RegisterMachine.ticks_eq_replicate: (none)
rocq RegisterMachine.literalTime_polynomial: (none)
rocq RegisterMachine.emitLiteral_reaches: (none)
```
