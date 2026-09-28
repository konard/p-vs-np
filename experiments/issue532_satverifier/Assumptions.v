(* Scratch check: the Rocq SAT-in-NP theorems are closed. *)
From proofs.experiments.issue532.rocq Require Import SATVerifier.
Print Assumptions satInNP.
Print Assumptions satNP.
Print Assumptions verifier_run.
Print Assumptions cookLevin_iff_satHard.
Print Assumptions inP_sat_iff_of_hard.
Print Assumptions inP_sat_of_pEqualsNP'.
