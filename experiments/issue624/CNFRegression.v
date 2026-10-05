From Stdlib Require Import List Bool Arith Lia.
From proofs.experiments.issue624.rocq Require Import LocalCNF.
Import ListNotations Complexity.Complexity Machines LocalCNF.

Example empty_domain : evalCNF (fun _ => false) (oneHot 7 0) = false.
Proof. reflexivity. Qed.
Example no_value : evalCNF (fun _ => false) (oneHot 7 3) = false.
Proof. reflexivity. Qed.
Example multiple_values : evalCNF (fun _ => true) (oneHot 7 3) = false.
Proof. reflexivity. Qed.
Example singleton_value : evalCNF (fun i => Nat.eqb i 8) (oneHot 7 3) = true.
Proof. reflexivity. Qed.
Example all_models : forall a base size,
  evalCNF a (oneHot base size) = true <->
    exists v, v < size /\ a (base + v) = true /\
      forall w, w < size -> a (base + w) = true -> w = v.
Proof. apply oneHot_models. Qed.

Example invalid_edge : evalClause (fun _ => true)
  (implies [mkLit 0 true; mkLit 1 true] []) = false.
Proof. reflexivity. Qed.
Example inactive_edge : evalClause (fun i => negb (Nat.eqb i 1))
  (implies [mkLit 0 true; mkLit 1 true] []) = true.
Proof. reflexivity. Qed.
Example empty_contradiction : evalClause (fun _ => true) (implies [] []) = false.
Proof. reflexivity. Qed.
Example empty_premise : evalClause (fun _ => true) (implies [] [mkLit 5 true]) = true.
Proof. reflexivity. Qed.

Print Assumptions oneHot_models.
Print Assumptions implies_models.
Print Assumptions oneHot_encoded_size.
