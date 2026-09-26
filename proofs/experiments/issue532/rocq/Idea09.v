(* Issue #532: 09_length_vs_runtime. Finite model only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Inductive program := short | long.
Definition codeLength (p : program) : nat := match p with short => 1 | long => 2 end.
Definition steps (p : program) : nat := match p with short => 10 | long => 1 end.
Theorem tested : codeLength short < codeLength long /\ steps long < steps short.
Proof. compute; lia. Qed.
