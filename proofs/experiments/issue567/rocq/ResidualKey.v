(** Issue 567: a scoped residual-state key counterexample.
    The challenged key is [(variable count, clause count, encoded bit length)].
    This says nothing about full canonical keys or unrestricted algorithms. *)

From Stdlib Require Import List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

Definition posUnit : Clause := [mkLit 0 true].
Definition negUnit : Clause := [mkLit 0 false].

Definition satFamily (k : nat) : CNF := posUnit :: posUnit :: repeat posUnit k.
Definition unsatFamily (k : nat) : CNF := negUnit :: posUnit :: repeat posUnit k.

Definition coarseKey (phi : CNF) : nat * nat * nat :=
  (numVars phi, length phi, length (encodeCNF phi)).

Theorem coarseKey_collision : forall k,
  coarseKey (satFamily k) = coarseKey (unsatFamily k).
Proof.
  intro k. unfold coarseKey, satFamily, unsatFamily, posUnit, negUnit.
  simpl. reflexivity.
Qed.

Theorem satFamily_satisfiable : forall k, Satisfiable (satFamily k).
Proof.
  assert (H : forall j,
    evalCNF (fun _ => true) (repeat posUnit j) = true).
  { intro j. induction j as [| j IH]; [reflexivity |].
    simpl. unfold posUnit. simpl. exact IH. }
  intro k. exists (fun _ => true). unfold satFamily.
  simpl. exact (H k).
Qed.

Theorem unsatFamily_unsatisfiable : forall k, ~ Satisfiable (unsatFamily k).
Proof.
  intros k [a H]. unfold unsatFamily, negUnit, posUnit in H.
  simpl in H. unfold evalLit in H.
  destruct (a 0) eqn:E; simpl in H.
  all: rewrite E in H; simpl in H; discriminate.
Qed.

Theorem length_replicate_posUnit : forall k,
  length (encodeCNF (repeat posUnit k)) = 4 * k.
Proof.
  induction k as [| k IH]; [reflexivity |].
  change (length (encodeClause posUnit ++ encodeCNF (repeat posUnit k)) = 4 * S k).
  rewrite length_app, IH.
  change (length (encodeClause posUnit)) with 4. lia.
Qed.

Theorem family_encoded_lengths : forall k,
  length (encodeCNF (satFamily k)) = 4 * (k + 2) /\
  length (encodeCNF (unsatFamily k)) = 4 * (k + 2).
Proof.
  intro k. unfold satFamily, unsatFamily.
  change (length (encodeClause posUnit ++ encodeClause posUnit ++
            encodeCNF (repeat posUnit k)) = 4 * (k + 2) /\
          length (encodeClause negUnit ++ encodeClause posUnit ++
            encodeCNF (repeat posUnit k)) = 4 * (k + 2)).
  rewrite !length_app, length_replicate_posUnit.
  change (length (encodeClause posUnit)) with 4.
  change (length (encodeClause negUnit)) with 4. lia.
Qed.

(** For every [k], the key merges opposite SAT answers at encoded length
    [4 * (k + 2)]. Reusing answers solely by this key is unsound. *)
Theorem coarseKey_not_satisfiability_complete : forall k,
  coarseKey (satFamily k) = coarseKey (unsatFamily k) /\
  Satisfiable (satFamily k) /\ ~ Satisfiable (unsatFamily k).
Proof.
  intro k. repeat split; auto using coarseKey_collision,
    satFamily_satisfiable, unsatFamily_unsatisfiable.
Qed.
