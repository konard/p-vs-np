(* Concrete counterexample to Gubin, cs/0610042v3, Theorem 1.2.
   Zero-based indices. The graph is two disjoint directed 3-cycles. *)
From Stdlib Require Import Arith.PeanoNat Bool.Bool QArith.QArith Lia.
Local Open Scope nat_scope.

Module GubinPaperAudit.

Definition next (i j : nat) : bool := Nat.eqb j ((i + 1) mod 6).

Definition edge (a b : nat) : bool :=
  ((Nat.eqb a 0 && Nat.eqb b 1) ||
   (Nat.eqb a 1 && Nat.eqb b 2) ||
   (Nat.eqb a 2 && Nat.eqb b 0) ||
   (Nat.eqb a 3 && Nat.eqb b 4) ||
   (Nat.eqb a 4 && Nat.eqb b 5) ||
   (Nat.eqb a 5 && Nat.eqb b 3))%bool.

Definition group (a : nat) : bool := a <? 3.

Definition compatible (i j a b : nat) : bool :=
  (negb (next i j) || edge a b) &&
  (negb (next j i) || edge b a).

Definition sum6 (f : nat -> Q) : Q :=
  (f 0%nat + f 1%nat + f 2%nat + f 3%nat + f 4%nat + f 5%nat)%Q.

(* Equations (1.8) and (1.9), including nonnegativity. *)
Definition PaperFeasible (x : nat -> nat -> nat -> nat -> Q)
    (y : nat -> nat -> Q) : Prop :=
  (forall i j a b, i < 6 -> j < 6 -> a < 6 -> b < 6 ->
    i <> j -> a <> b ->
    Qeq (x i j a b) (x j i b a) /\ Qle 0 (x i j a b)) /\
  (forall i j b, i < 6 -> j < 6 -> b < 6 -> i <> j ->
    Qeq (sum6 (fun a => if Nat.eqb a b then 0%Q else x i j a b)) (y j b)) /\
  (forall j a b, j < 6 -> a < 6 -> b < 6 -> a <> b ->
    Qeq (sum6 (fun i => if Nat.eqb i j then 0%Q else x i j a b)) (y j b)) /\
  (forall j, j < 6 ->
    Qeq (sum6 (y j)) 1 /\ forall b, b < 6 -> Qle 0 (y j b)) /\
  (forall i j a b, i < 6 -> j < 6 -> a < 6 -> b < 6 ->
    i <> j -> a <> b -> compatible i j a b = false ->
    Qeq (x i j a b) 0).

Definition y (_ _ : nat) : Q := 1 # 6.

Definition x (i j a b : nat) : Q :=
  if (Nat.eqb i j || Nat.eqb a b)%bool then 0%Q
  else if next i j then (if edge a b then 1 # 6 else 0%Q)
  else if next j i then (if edge b a then 1 # 6 else 0%Q)
  else if xorb (group a) (group b) then 1 # 18 else 0%Q.

Lemma lt6_cases : forall n, n < 6 ->
  n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5.
Proof. intros; lia. Qed.

Ltac cases6 n H :=
  let h := fresh "hcases" in
  pose proof (lt6_cases n H) as h;
  destruct h as [h|[h|[h|[h|[h|h]]]]]; subst n.

Theorem witness_feasible : PaperFeasible x y.
Proof.
  unfold PaperFeasible.
  repeat (apply conj).
  - intros i j a b hi hj ha hb hij hab.
    cases6 i hi; cases6 j hj; cases6 a ha; cases6 b hb;
      try congruence; split; vm_compute; congruence.
  - intros i j b hi hj hb hij.
    cases6 i hi; cases6 j hj; cases6 b hb;
      try congruence; vm_compute; congruence.
  - intros j a b hj ha hb hab.
    cases6 j hj; cases6 a ha; cases6 b hb;
      try congruence; vm_compute; congruence.
  - intros j hj.
    cases6 j hj; split; try (vm_compute; congruence);
      intros b hb; cases6 b hb; vm_compute; congruence.
  - intros i j a b hi hj ha hb hij hab hbad.
    cases6 i hi; cases6 j hj; cases6 a ha; cases6 b hb;
      try congruence; vm_compute in *; congruence.
Qed.

Definition HasTour : Prop :=
  exists p : nat -> nat,
    (forall i, i < 6 -> p i < 6) /\
    (forall i j, i < 6 -> j < 6 -> p i = p j -> i = j) /\
    (forall a, a < 6 -> exists i, i < 6 /\ p i = a) /\
    (forall i, i < 6 -> edge (p i) (p ((i + 1) mod 6)) = true).

Lemma edge_same_group : forall a b,
    a < 6 -> b < 6 -> edge a b = true -> group a = group b.
Proof.
  intros a b ha hb he.
  cases6 a ha; cases6 b hb; vm_compute in *; congruence.
Qed.

Theorem no_hamiltonian_tour : ~ HasTour.
Proof.
  intros [p [hrange [_ [hsurj hcycle]]]].
  assert (h01 : group (p 0) = group (p 1)).
  { apply edge_same_group; try (apply hrange; lia).
    exact (hcycle 0 ltac:(lia)). }
  assert (h12 : group (p 1) = group (p 2)).
  { apply edge_same_group; try (apply hrange; lia).
    exact (hcycle 1 ltac:(lia)). }
  assert (h23 : group (p 2) = group (p 3)).
  { apply edge_same_group; try (apply hrange; lia).
    exact (hcycle 2 ltac:(lia)). }
  assert (h34 : group (p 3) = group (p 4)).
  { apply edge_same_group; try (apply hrange; lia).
    exact (hcycle 3 ltac:(lia)). }
  assert (h45 : group (p 4) = group (p 5)).
  { apply edge_same_group; try (apply hrange; lia).
    exact (hcycle 4 ltac:(lia)). }
  assert (hall : forall i, i < 6 -> group (p i) = group (p 0)).
  { intros i hi; cases6 i hi; try reflexivity; congruence. }
  destruct (hsurj 0 ltac:(lia)) as [i0 [hi0 hp0]].
  destruct (hsurj 3 ltac:(lia)) as [i3 [hi3 hp3]].
  pose proof (hall i0 hi0) as hg0.
  pose proof (hall i3 hi3) as hg3.
  rewrite hp0 in hg0; rewrite hp3 in hg3.
  unfold group in hg0, hg3.
  replace (0 <? 3) with true in hg0 by reflexivity.
  replace (3 <? 3) with false in hg3 by reflexivity.
  congruence.
Qed.

Theorem paper_correspondence_fails : PaperFeasible x y /\ ~ HasTour.
Proof. split; [exact witness_feasible|exact no_hamiltonian_tour]. Qed.

Theorem claimed_soundness_false :
  ~ (forall x y, PaperFeasible x y -> HasTour).
Proof.
  intro h; exact (no_hamiltonian_tour (h x y witness_feasible)).
Qed.

End GubinPaperAudit.
