(* Issue #532: 34_algorithm_quantifiers. General lemma or countermodel only; see RESEARCH_LOG.md. *)
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List Lia.
Theorem tested :
  exists fails : bool -> bool -> Prop,
    (forall algorithm, exists input, fails algorithm input) /\
    ~ (exists input, forall algorithm, fails algorithm input).
Proof.
  exists (fun algorithm input => algorithm = input); split.
  - intro algorithm; exists algorithm; reflexivity.
  - intros [input H]; specialize (H (negb input)); destruct input; discriminate.
Qed.
