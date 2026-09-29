From Stdlib Require Import List.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Idea41.

Example decoder_roundtrip : decCircuit (encCircuit 1 [(0, 0)]) = Some (1, [(0, 0)]).
Proof. reflexivity. Qed.
Example decoder_trailing : decCircuit (encCircuit 1 [(0, 0)] ++ [true]) = None.
Proof. reflexivity. Qed.
Example decoder_truncated : decCircuit [true] = None.
Proof. reflexivity. Qed.
Example forward_wire_rejected : checkCircuit (encCircuit 1 [(0, 1)]) = false.
Proof. reflexivity. Qed.
Example zero_input_gate_rejected : checkCircuit (encCircuit 0 [(0, 0)]) = false.
Proof. reflexivity. Qed.
Example nand_accepts : verifyCircuit (encCircuit 1 [(0, 0)]) [false] = true.
Proof. reflexivity. Qed.
Example nand_rejects : verifyCircuit (encCircuit 1 [(0, 0)]) [true] = false.
Proof. reflexivity. Qed.
Example short_cert_rejected : verifyCircuit (encCircuit 1 [(0, 0)]) [] = false.
Proof. reflexivity. Qed.
Example trailing_bits_rejected :
  verifyCircuit (encCircuit 1 [(0, 0)] ++ [true]) [false] = false.
Proof. reflexivity. Qed.
Example zero_input_empty_rejected : verifyCircuit (encCircuit 0 []) [] = false.
Proof. reflexivity. Qed.
Example no_gate_reads_input : verifyCircuit (encCircuit 1 []) [true] = true.
Proof. reflexivity. Qed.
