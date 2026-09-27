(* Issue #532, Idea 25: decomposable constraints (component splitting).

   Verdict: correct tool, insufficient alone (general theorem proved).

   Same content as ../lean/Idea25.lean:
   - eval_congr: evaluation of a CNF depends only on its variables;
   - split_sat_iff: variable-disjoint parts are satisfiable together iff
     separately (merged witness);
   - joinAll_sat_iff: the same for a list of pairwise disjoint components;
   - chain_not_splittable: for every n the chain (x0 \/ x1) /\ ... /\
     (x_{n-1} \/ x_n) has no non-trivial variable-disjoint clause split;
   - split_cost: 2^a + 2^b <= 2 * 2^(max a b) and 2^(max a b) <= 2^a + 2^b.
   See ../ideas/Idea25.md. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

Record Lit := mkLit { var : nat; pos : bool }.

Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition evalLit (a : Assignment) (l : Lit) : bool :=
  if pos l then a (var l) else negb (a (var l)).

Fixpoint evalClause (a : Assignment) (c : Clause) : bool :=
  match c with
  | [] => false
  | l :: c' => evalLit a l || evalClause a c'
  end.

Fixpoint evalCNF (a : Assignment) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | c :: phi' => evalClause a c && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a, evalCNF a phi = true.

Definition clauseVars (c : Clause) : list nat := map var c.

Fixpoint vars (phi : CNF) : list nat :=
  match phi with
  | [] => []
  | c :: phi' => clauseVars c ++ vars phi'
  end.

Lemma evalCNF_append : forall a (phi psi : CNF),
  evalCNF a (phi ++ psi) = evalCNF a phi && evalCNF a psi.
Proof.
  intros a phi psi; induction phi as [|c phi IH]; simpl.
  - reflexivity.
  - rewrite IH, andb_assoc; reflexivity.
Qed.

Lemma vars_append : forall phi psi : CNF, vars (phi ++ psi) = vars phi ++ vars psi.
Proof.
  intros phi psi; induction phi as [|c phi IH]; simpl.
  - reflexivity.
  - rewrite IH, app_assoc; reflexivity.
Qed.

Lemma evalClause_congr : forall (a b : Assignment) (c : Clause),
  (forall v, In v (clauseVars c) -> a v = b v) -> evalClause a c = evalClause b c.
Proof.
  intros a b c; induction c as [|l c IH]; intros H; simpl.
  - reflexivity.
  - assert (Hl : a (var l) = b (var l)) by (apply H; simpl; left; reflexivity).
    rewrite IH.
    + unfold evalLit; rewrite Hl; reflexivity.
    + intros v Hv; apply H; simpl; right; exact Hv.
Qed.

(* Locality of evaluation. *)
Theorem eval_congr : forall (a b : Assignment) (phi : CNF),
  (forall v, In v (vars phi) -> a v = b v) -> evalCNF a phi = evalCNF b phi.
Proof.
  intros a b phi; induction phi as [|c phi IH]; intros H; simpl.
  - reflexivity.
  - rewrite (evalClause_congr a b c), IH.
    + reflexivity.
    + intros v Hv; apply H; simpl; apply in_or_app; right; exact Hv.
    + intros v Hv; apply H; simpl; apply in_or_app; left; exact Hv.
Qed.

Definition Disjoint (phi psi : CNF) : Prop :=
  forall v, In v (vars phi) -> ~ In v (vars psi).

Definition merge (phi1 : CNF) (a1 a2 : Assignment) : Assignment :=
  fun v => if in_dec Nat.eq_dec v (vars phi1) then a1 v else a2 v.

Lemma merge_left : forall phi1 a1 a2,
  evalCNF (merge phi1 a1 a2) phi1 = evalCNF a1 phi1.
Proof.
  intros phi1 a1 a2; apply eval_congr; intros v Hv; unfold merge.
  destruct (in_dec Nat.eq_dec v (vars phi1)) as [_|Hn]; [reflexivity | contradiction].
Qed.

Lemma merge_right : forall phi1 phi2 a1 a2, Disjoint phi1 phi2 ->
  evalCNF (merge phi1 a1 a2) phi2 = evalCNF a2 phi2.
Proof.
  intros phi1 phi2 a1 a2 Hd; apply eval_congr; intros v Hv; unfold merge.
  destruct (in_dec Nat.eq_dec v (vars phi1)) as [H1|_].
  - exfalso; exact (Hd v H1 Hv).
  - reflexivity.
Qed.

(* Component splitting theorem. *)
Theorem split_sat_iff : forall phi1 phi2, Disjoint phi1 phi2 ->
  (Satisfiable (phi1 ++ phi2) <-> Satisfiable phi1 /\ Satisfiable phi2).
Proof.
  intros phi1 phi2 Hd; split.
  - intros [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
    destruct Ha as [H1 H2]; split; exists a; assumption.
  - intros [[a1 H1] [a2 H2]]; exists (merge phi1 a1 a2).
    rewrite evalCNF_append, merge_left, (merge_right phi1 phi2 a1 a2 Hd), H1, H2.
    reflexivity.
Qed.

Theorem sat_append_left : forall phi1 phi2,
  Satisfiable (phi1 ++ phi2) -> Satisfiable phi1 /\ Satisfiable phi2.
Proof.
  intros phi1 phi2 [a Ha]; rewrite evalCNF_append in Ha; apply andb_prop in Ha.
  destruct Ha as [H1 H2]; split; exists a; assumption.
Qed.

Fixpoint joinAll (phis : list CNF) : CNF :=
  match phis with
  | [] => []
  | phi :: rest => phi ++ joinAll rest
  end.

Fixpoint DisjointChain (phis : list CNF) : Prop :=
  match phis with
  | [] => True
  | phi :: rest => Disjoint phi (joinAll rest) /\ DisjointChain rest
  end.

(* Many components. *)
Theorem joinAll_sat_iff : forall phis, DisjointChain phis ->
  (Satisfiable (joinAll phis) <-> forall phi, In phi phis -> Satisfiable phi).
Proof.
  intros phis; induction phis as [|phi rest IH]; intros Hd; simpl.
  - split.
    + intros _ phi [].
    + intros _; exists (fun _ => false); reflexivity.
  - destruct Hd as [Hphi Hrest].
    rewrite (split_sat_iff phi (joinAll rest) Hphi), (IH Hrest).
    split.
    + intros [H1 H2] psi [Heq | Hin].
      * subst psi; exact H1.
      * apply H2; exact Hin.
    + intros H; split.
      * apply H; left; reflexivity.
      * intros psi Hpsi; apply H; right; exact Hpsi.
Qed.

Definition chainClause (i : nat) : Clause := [mkLit i true; mkLit (S i) true].

Definition chain (n : nat) : CNF := map chainClause (seq 0 n).

Theorem chain_satisfiable : forall n, Satisfiable (chain n).
Proof.
  intros n; exists (fun _ => true); unfold chain.
  induction (seq 0 n) as [|i l IH]; simpl.
  - reflexivity.
  - unfold evalLit; simpl; exact IH.
Qed.

Theorem chain_length : forall n, length (chain n) = n.
Proof. intros n; unfold chain; rewrite length_map, length_seq; reflexivity. Qed.

(* Discrete intermediate value theorem. *)
Lemma adjacent_change : forall (p : nat -> bool) i d, p i <> p (i + d) ->
  exists k, i <= k /\ k + 1 <= i + d /\ p k <> p (k + 1).
Proof.
  intros p i d; induction d as [|d IH]; intros H.
  - exfalso; apply H; rewrite Nat.add_0_r; reflexivity.
  - destruct (bool_dec (p i) (p (i + d))) as [Heq | Hne].
    + exists (i + d); split; [lia | split; [lia |]].
      rewrite <- Heq. replace (i + d + 1) with (i + S d) by lia. exact H.
    + destruct (IH Hne) as [k [Hk1 [Hk2 Hk3]]].
      exists k; split; [exact Hk1 | split; [lia | exact Hk3]].
Qed.

(* The chain is connected for every n. *)
Theorem chain_not_splittable : forall n (p : nat -> bool) i j,
  i < n -> j < n -> p i = true -> p j = false ->
  exists k, k + 1 < n /\ p k <> p (k + 1) /\
    In (k + 1) (clauseVars (chainClause k)) /\
    In (k + 1) (clauseVars (chainClause (k + 1))).
Proof.
  intros n p i j Hi Hj Hpi Hpj.
  assert (shared : forall k, In (k + 1) (clauseVars (chainClause k)) /\
                             In (k + 1) (clauseVars (chainClause (k + 1)))).
  { intros k; unfold clauseVars, chainClause; simpl; split.
    - right; left; lia.
    - left; reflexivity. }
  destruct (Nat.lt_ge_cases i j) as [Hij | Hij].
  - destruct (adjacent_change p i (j - i)) as [k [Hk1 [Hk2 Hk3]]].
    + replace (i + (j - i)) with j by lia; rewrite Hpi, Hpj; discriminate.
    + exists k; split; [lia | split; [exact Hk3 | apply shared]].
  - destruct (adjacent_change p j (i - j)) as [k [Hk1 [Hk2 Hk3]]].
    + replace (j + (i - j)) with i by lia; rewrite Hpi, Hpj; discriminate.
    + exists k; split; [lia | split; [exact Hk3 | apply shared]].
Qed.

Theorem split_cost : forall a b,
  2 ^ a + 2 ^ b <= 2 * 2 ^ (Nat.max a b) /\ 2 ^ (Nat.max a b) <= 2 ^ a + 2 ^ b.
Proof.
  intros a b.
  assert (Ha : 2 ^ a <= 2 ^ Nat.max a b) by (apply Nat.pow_le_mono_r; lia).
  assert (Hb : 2 ^ b <= 2 ^ Nat.max a b) by (apply Nat.pow_le_mono_r; lia).
  split; [lia |].
  destruct (Nat.le_ge_cases a b) as [H | H].
  - rewrite (Nat.max_r a b H); lia.
  - rewrite (Nat.max_l a b H); lia.
Qed.

(* The open obligation (FS): a map in the class PolyTime sending every CNF to
   pairwise variable-disjoint components whose union is equisatisfiable, each
   component having at most w |phi| variable occurrences. *)
Definition ComponentObligation (PolyTime : (CNF -> list CNF) -> Prop) (w : nat -> nat) : Prop :=
  exists f : CNF -> list CNF, PolyTime f /\ forall phi, DisjointChain (f phi) /\
    (forall psi, In psi (f phi) -> length (vars psi) <= w (length phi)) /\
    (Satisfiable phi <-> Satisfiable (joinAll (f phi))).

(* Conditional theorem: under the obligation, satisfiability of every CNF is the
   conjunction of the satisfiability of its small components. *)
Theorem component_obligation_splits (PolyTime : (CNF -> list CNF) -> Prop) (w : nat -> nat) :
  ComponentObligation PolyTime w ->
  exists f : CNF -> list CNF, PolyTime f /\ forall phi,
    (forall psi, In psi (f phi) -> length (vars psi) <= w (length phi)) /\
    (Satisfiable phi <-> forall psi, In psi (f phi) -> Satisfiable psi).
Proof.
  intros (f & hf & hall). exists f. split; [exact hf|]. intro phi.
  destruct (hall phi) as (hd & hw & hp). split; [exact hw|].
  rewrite hp. apply joinAll_sat_iff. exact hd.
Qed.
