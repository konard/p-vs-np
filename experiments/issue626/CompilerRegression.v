From Stdlib Require Import List.
From proofs.experiments.issue532.rocq Require Import CircuitModel.
From proofs.experiments.issue626.rocq Require Import NandCompiler Window Simulation.
Import ListNotations Complexity Simulation.
Definition readBit : Machine := {|program := [[halt false; halt false; halt true]]|}.
Example reads_false : output [false] (simCircuit readBit {|coefficient:=1;degree:=0|} 1) = false.
Proof. vm_compute. reflexivity. Qed.
Example reads_true : output [true] (simCircuit readBit {|coefficient:=1;degree:=0|} 1) = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions simCircuit_WF.
Print Assumptions simCircuit_polynomial_size.
