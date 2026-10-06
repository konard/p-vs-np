From Stdlib Require Import List Lia.
Import ListNotations.
From proofs.experiments.issue567.rocq Require Import CircuitSyntax.
From proofs.experiments.issue532.rocq Require Import Idea41.
From proofs.experiments.issue10.rocq Require Import NPNotSubsetP.
Import Complexity Machines Circuits CircuitSyntax.

Example finite_table : length (program circuitSyntaxMachine) = 6.
Proof. reflexivity. Qed.
Example multi_gate_syntax : circuitSyntax (encCircuit 2 [(0, 1); (2, 1)]) = true.
Proof. reflexivity. Qed.
Example zero_input_syntax : circuitSyntax (encCircuit 0 []) = true.
Proof. reflexivity. Qed.
Example empty_rejected : circuitSyntax [] = false.
Proof. reflexivity. Qed.
Example truncated_header : circuitSyntax [true] = false.
Proof. reflexivity. Qed.
Example trailing_rejected : circuitSyntax (encCircuit 1 [(0, 0)] ++ [true]) = false.
Proof. reflexivity. Qed.
Example truncated_first_wire : circuitSyntax [true; false; true; false] = false.
Proof. reflexivity. Qed.
Example truncated_second_wire : circuitSyntax [true; false; true; false; true] = false.
Proof. reflexivity. Qed.

Example charged_accept : Run circuitSyntaxMachine
  (pairedInput (encCircuit 1 [(0, 0)]) [false]) (length (encCircuit 1 [(0, 0)]) + 1) true.
Proof. apply circuitSyntaxMachine_run. Qed.
Example charged_reject : Run circuitSyntaxMachine (pairedInput [true] [false]) 2 false.
Proof. apply circuitSyntaxMachine_run. Qed.
Example zero_step_rejected : forall m x cert b, ~ Run m (pairedInput x cert) 0 b.
Proof. intros m x cert b hr. pose proof (run_pos _ _ _ _ hr). lia. Qed.

Example forward_wire_has_syntax : circuitSyntax (encCircuit 1 [(0, 1)]) = true.
Proof. reflexivity. Qed.
Example forward_wire_rejected : verifyCircuit (encCircuit 1 [(0, 1)]) [false] = false.
Proof. reflexivity. Qed.
Example short_cert_rejected : verifyCircuit (encCircuit 1 [(0, 0)]) [] = false.
Proof. reflexivity. Qed.
Example long_cert_rejected : verifyCircuit (encCircuit 1 [(0, 0)]) [false; true] = false.
Proof. reflexivity. Qed.
Example true_cert_accepted : verifyCircuit (encCircuit 1 []) [true] = true.
Proof. reflexivity. Qed.
Example false_cert_rejected : verifyCircuit (encCircuit 1 []) [false] = false.
Proof. reflexivity. Qed.

Example fixed_certificate_breaks_language : ~ (CircuitSAT (encCircuit 1 []) = true <->
  exists cert : Word, verifyCircuit (encCircuit 1 []) [false] = true).
Proof.
  intro he. assert (hs : CircuitSAT (encCircuit 1 []) = true) by reflexivity.
  destruct (proj1 he hs) as [cert hc]. discriminate.
Qed.

Example certificate_blind_incorrect : forall (v : Word -> Word -> bool),
  (forall x cert, v x cert = verifyCircuit x cert) ->
  (forall x a b, v x a = v x b) -> False.
Proof.
  intros v hv blind. pose proof (blind (encCircuit 1 []) [true] [false]) as he.
  rewrite !hv in he. discriminate.
Qed.
