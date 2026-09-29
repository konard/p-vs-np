import proofs.experiments.issue568.lean.Tableau

#check Issue568.Tableau.localTrace_iff_run
#check Issue568.Tableau.boundedAccept_iff_run
#check Issue568.Tableau.bounded_initial_span

open Complexity Issue568.Tableau

example : BoundedTableau acceptMachine (initial []) 1 true :=
  one_clock_accepts

example : ¬ LocalTrace acceptMachine true [initial [], initial []] :=
  premature_halt_rejected

example : step moveThenAccept wrongSuccessor = .inl true :=
  wrong_successor_halts

example : LocalTrace moveThenAccept true [initial [], goodSuccessor] :=
  two_step_accepts

example : ¬ LocalTrace moveThenAccept true [initial [], wrongSuccessor] :=
  wrong_successor_rejected

example : ¬ BoundedTableau acceptMachine (initial []) 0 true :=
  zero_clock_rejected _ _
