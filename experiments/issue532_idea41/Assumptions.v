(* Axiom audit for the Idea 41 bridge to Idea 16 (issue #532).
   From the repository root, after compiling Complexity.v, Machines.v,
   Circuits.v, Idea16.v and Idea41.v:
     rocq compile -Q . '' experiments/issue532_idea41/Assumptions.v
   Every line must print "Closed under the global context". *)
From proofs.experiments.issue532.rocq Require Idea41.
Print Assumptions Idea41.inNTIME_iff_idea16.
Print Assumptions Idea41.nTimeHierarchy_of_idea16.
Print Assumptions Idea41.williams_method_idea16.
Print Assumptions Idea41.idea16_nTimeHierarchy_of_lazyDiagonal.
Print Assumptions Idea41.inNEXP_of_inNTIME_two_pow.
Print Assumptions Idea41.not_forall_inNTIME.
