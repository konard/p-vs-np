From Stdlib Require Import List.
From proofs.experiments.issue568.rocq Require Import Tableau.

Check Tableau.localTrace_iff_run.
Check Tableau.boundedAccept_iff_run.
Check Tableau.bounded_initial_span.

Import ListNotations.

Example one_step_accepts :
  Tableau.boundedTableau Tableau.acceptMachine (Complexity.Complexity.initial []) 1 true :=
  Tableau.one_clock_accepts.

Example no_early_halt :
  ~ Tableau.localTrace Tableau.acceptMachine true
      [Complexity.Complexity.initial []; Complexity.Complexity.initial []] :=
  Tableau.premature_halt_rejected.

Example wrong_successor_still_halts :
  Complexity.Complexity.step Tableau.moveThenAccept Tableau.wrongSuccessor =
    inl true := Tableau.wrong_successor_halts.

Example good_two_step_trace :
  Tableau.localTrace Tableau.moveThenAccept true
      [Complexity.Complexity.initial []; Tableau.goodSuccessor] :=
  Tableau.two_step_accepts.

Example wrong_successor_has_bad_edge :
  ~ Tableau.localTrace Tableau.moveThenAccept true
      [Complexity.Complexity.initial []; Tableau.wrongSuccessor] :=
  Tableau.wrong_successor_rejected.

Example no_zero_clock :
  ~ Tableau.boundedTableau Tableau.acceptMachine (Complexity.Complexity.initial []) 0 true :=
  Tableau.zero_clock_rejected _ _.
