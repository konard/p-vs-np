From Stdlib Require Import List Bool Arith.
From proofs.complexity.rocq Require Import Complexity.
From proofs.experiments.issue532.rocq Require Import Machines.
From proofs.experiments.issue624.rocq Require Import
  Schema CookLevin CertificateCNF InitialCNF RunCNF FixedWindow VerifierTableau.
Import ListNotations Complexity Machines Schema CookLevin VerifierTableau.

Example schema_finite_description : ClassNP -> Schema := tableauSchema.

Example schema_full_contract : forall np x,
  evalSchema (tableauSchema np) (tableauParams np (length x)) x (fun _ => 0) =
    tableauCNF np x.
Proof. exact tableauSchema_eq. Qed.

Example schema_original_fragments : forall np x env,
  evalSchema (tableauSchema np) (tableauParams np (length x)) x env =
    (CertificateCNF.certificateCNF 0 (evalPoly (np_certBound np) (length x)) ++
      InitialCNF.initialCNF (rowBase np x) (length (program (verifierMachine (np_verifier np))))
        (VerifierTableau.maxClock np (length x)) (sources np x)) ++
    RunCNF.runCNF (verifierMachine (np_verifier np)) (rowBase np x)
      (FixedWindow.windowWidth np (length x)) (VerifierTableau.maxClock np (length x)).
Proof. exact tableauSchema_fragments. Qed.

Example subtract_truncates : evalExpr (ESub (EConst 2) (EConst 5)) [] [] (fun _ => 0) = 0.
Proof. reflexivity. Qed.

Example nested_loop_slots :
  evalSchema (SForRange 0 (EConst 2)
    (SForRange 1 (EAdd (EIdx 0) (EConst 1))
      (SClause (LList [(EAdd (EMul (EConst 10) (EIdx 0)) (EIdx 1), true)]))))
      [] [] (fun _ => 99) = [[mkLit 0 true]; [mkLit 10 true]; [mkLit 11 true]].
Proof. reflexivity. Qed.
Example input_bit : evalExpr (EBit (EConst 1)) [] [false; true] (fun _ => 0) = 1.
Proof. reflexivity. Qed.
Example missing_bit : evalExpr (EBit (EConst 3)) [] [true] (fun _ => 0) = 0.
Proof. reflexivity. Qed.
Example missing_param : evalExpr (EParam 3) [7] [] (fun _ => 0) = 0.
Proof. reflexivity. Qed.
Example one_hot_order :
  evalSchema (oneHotSchema 0 (EConst 4) (EConst 3)) [] [] (fun _ => 0) =
    [[mkLit 4 true; mkLit 5 true; mkLit 6 true];
     [mkLit 4 false; mkLit 5 false]; [mkLit 4 false; mkLit 6 false];
     [mkLit 5 false; mkLit 6 false]].
Proof. reflexivity. Qed.
Example zero_certificate :
  evalSchema (certificateSchema 0 (EConst 0) (EConst 0)) [] [] (fun _ => 0) =
    [[mkLit 0 false]].
Proof. reflexivity. Qed.
