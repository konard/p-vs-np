From Stdlib Require Import List Bool Arith Lia.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines Circuits.
From proofs.experiments.issue624.rocq Require Import CircuitCNF.
Import ListNotations Complexity Machines Circuits CircuitCNF.

Example existing_semantics : forall n C, WF n C ->
  Satisfiable (acceptingCNF n C) <->
    exists x : Word, length x = n /\ output x C = true.
Proof. exact acceptingCNF_iff. Qed.

Example zero_input_rejected : ~ Satisfiable (acceptingCNF 0 []).
Proof.
  rewrite acceptingCNF_iff by exact I.
  intros [x [hx ho]]. destruct x; [discriminate|simpl in hx; lia].
Qed.

Example nand_has_model : Satisfiable (acceptingCNF 1 [(0, 0)]).
Proof.
  apply acceptingCNF_iff; [cbn; auto|].
  exists [false]. split; reflexivity.
Qed.

Example contradiction_has_no_model :
  ~ Satisfiable (acceptingCNF 1 [(0, 0); (0, 1); (2, 2)]).
Proof.
  rewrite acceptingCNF_iff by (cbn; repeat split; lia).
  intros [x [hx ho]]. destruct x as [|b tail]; [simpl in hx; lia|].
  assert (ht : tail = []) by (apply length_zero_iff_nil; simpl in hx; lia).
  subst tail. destruct b; discriminate.
Qed.

Example wrong_true_output : evalCNF (fun _ => true) (gateCNF 2 0 1) = false.
Proof. reflexivity. Qed.
Example wrong_false_output : evalCNF (fun _ => false) (gateCNF 2 0 1) = false.
Proof. reflexivity. Qed.
Example gate_contract : forall a,
  evalCNF a (gateCNF 2 0 1) = true <-> a 2 = negb (andb (a 0) (a 1)).
Proof. intros. apply gateCNF_models. Qed.

Example unary_encoded_size : forall n C, WF n C ->
  length (encodeCNF (acceptingCNF n C)) <=
    8 * (3 * length C + 1) * (n + length C + 1).
Proof. exact acceptingCNF_encoded_size. Qed.

Print Assumptions acceptingCNF_iff.
Print Assumptions circuitCNF_models.
Print Assumptions acceptingCNF_encoded_size.

Example polynomial_unary_bound : forall p inputLength n C,
  WF n C -> n + length C <= evalPoly p inputLength ->
  length (encodeCNF (acceptingCNF n C)) <=
    evalPoly (circuitPolynomial p) inputLength.
Proof. exact acceptingCNF_polynomial_size. Qed.

Print Assumptions acceptingCNF_polynomial_size.
