From proofs.p_vs_np_undecidable.rocq Require Import PvsNPUndecidable.
From proofs.complexity.rocq Require Import Complexity.
Import Complexity.Complexity.

Definition emptyTheory : Theory := {| proves := fun _ => False |}.

Example empty_theory_independent : PvsNPIsIndependent emptyTheory.
Proof. split; intro h; exact h. Qed.

Example negation_denotes_p_not_equals_np :
  denotes (neg pEqualsNP) = PNotEqualsNP.
Proof. reflexivity. Qed.

Example independent_cannot_prove_negation : forall theory,
  PvsNPIsIndependent theory -> ~ Provable theory (neg pEqualsNP).
Proof. intros theory h. exact (proj2 h). Qed.
