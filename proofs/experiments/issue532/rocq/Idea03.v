(** * Issue #532, Idea 03 -- A verifier for CNF-SAT (the NP side)

    Rocq counterpart of [lean/Idea03.lean]; theorem names are aligned.

    - [verify_sound], [verify_complete], [sat_iff_exists_cert]: the verifier
      characterizes satisfiability with certificates of length [numVars phi];
    - [cert_length_le_encoding]: certificates are no longer than the input;
    - [verifyRun_result], [verify_cost_eq]: the instrumented verifier computes
      [verify] with exactly [size phi] literal evaluations;
    - [verifyRunSC_result], [verifyRunSC_cost_le]: the short-circuit verifier
      computes [verify] with at most [size phi] literal evaluations;
    - [size_le_encodingLength], [verify_cost_le_encoding]: linear in the input;
    - [unsat_iff_all_rejected], [total_verification_cost]: unsatisfiability is
      a statement about all [2^n] certificates, whose exhaustive check costs
      exactly [2^n * size phi].

    Verdict: correct tool, insufficient alone.  The NP side is easy; the
    difficulty is the quantifier over certificates (Idea 01's obligation). *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.

(** ** CNF syntax and semantics *)

Record Lit := mkLit { var : nat; pos : bool }.
Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition evalLit (a : Assignment) (l : Lit) : bool := Bool.eqb (a (var l)) (pos l).

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

Definition Satisfiable (phi : CNF) : Prop := exists a : Assignment, evalCNF a phi = true.

Definition VarsBelow (n : nat) (phi : CNF) : Prop :=
  forall c, In c phi -> forall l, In l c -> var l < n.

Lemma evalClause_congr (a b : Assignment) (n : nat) (c : Clause) :
  (forall i, i < n -> a i = b i) -> (forall l, In l c -> var l < n) ->
  evalClause a c = evalClause b c.
Proof.
  intros hab; induction c as [|l c IH]; intros hc; simpl; auto.
  unfold evalLit. rewrite (hab (var l) (hc l (or_introl eq_refl))).
  rewrite IH; auto. intros l' hl'; apply hc; simpl; auto.
Qed.

Lemma evalCNF_congr (a b : Assignment) (n : nat) (phi : CNF) :
  (forall i, i < n -> a i = b i) -> VarsBelow n phi -> evalCNF a phi = evalCNF b phi.
Proof.
  intros hab; induction phi as [|c phi IH]; intros hphi; simpl; auto.
  rewrite (evalClause_congr a b n c hab (hphi c (or_introl eq_refl))).
  rewrite IH; auto. intros c' hc'; apply hphi; simpl; auto.
Qed.

(** ** Enumerating all assignments *)

Fixpoint allAssignments (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => map (cons false) (allAssignments n') ++ map (cons true) (allAssignments n')
  end.

Fixpoint toAssign (v : list bool) (i : nat) : bool :=
  match v, i with
  | [], _ => false
  | b :: _, 0 => b
  | _ :: v', S i' => toAssign v' i'
  end.

Fixpoint prefixOf (a : Assignment) (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => a 0 :: prefixOf (fun i => a (S i)) n'
  end.

Theorem length_allAssignments (n : nat) : length (allAssignments n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite length_app, !length_map, IH. lia.
Qed.

Theorem mem_allAssignments_iff (n : nat) (v : list bool) :
  In v (allAssignments n) <-> length v = n.
Proof.
  revert v; induction n as [|n IH]; intros v.
  - destruct v as [|b v]; simpl; split; intros H; auto; try discriminate.
    destruct H as [H|H]; [discriminate|contradiction].
  - destruct v as [|b v]; simpl; rewrite in_app_iff, !in_map_iff; split.
    + intros [[w [Hw _]]|[w [Hw _]]]; discriminate.
    + intros H; discriminate.
    + intros [[w [Hw Hin]]|[w [Hw Hin]]]; injection Hw; intros; subst;
        f_equal; apply IH; auto.
    + intros H; injection H; intros H'; destruct b.
      * right; exists v; split; auto; apply IH; auto.
      * left; exists v; split; auto; apply IH; auto.
Qed.

Lemma nodup_app_intro {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 H; simpl; auto.
  inversion H1; subst. constructor.
  - intros Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + contradiction.
    + apply (H x); simpl; auto.
  - apply IH; auto. intros y Hy; apply H; simpl; auto.
Qed.

Lemma nodup_map_cons (b : bool) (L : list (list bool)) :
  NoDup L -> NoDup (map (cons b) L).
Proof.
  induction L as [|x L IH]; intros H; simpl; constructor.
  - inversion H; subst. intros Hin; apply in_map_iff in Hin.
    destruct Hin as [y [Hy Hin]]; injection Hy; intros; subst; contradiction.
  - inversion H; subst; auto.
Qed.

Theorem nodup_allAssignments (n : nat) : NoDup (allAssignments n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [simpl; auto | constructor].
  - apply nodup_app_intro; try apply nodup_map_cons; auto.
    intros x Hx Hy; apply in_map_iff in Hx; apply in_map_iff in Hy.
    destruct Hx as [u [Hu _]]; destruct Hy as [w [Hw _]]; subst.
    discriminate.
Qed.

Lemma length_prefixOf (a : Assignment) (n : nat) : length (prefixOf a n) = n.
Proof. revert a; induction n; intros a; simpl; auto. Qed.

Lemma toAssign_prefixOf (a : Assignment) (n i : nat) :
  i < n -> toAssign (prefixOf a n) i = a i.
Proof.
  revert a i; induction n as [|n IH]; intros a i H; [lia|].
  destruct i as [|i]; simpl; auto.
  apply (IH (fun j => a (S j))); lia.
Qed.

(** ** Number of variables *)

Fixpoint clauseBound (c : Clause) : nat :=
  match c with
  | [] => 0
  | l :: c' => Nat.max (S (var l)) (clauseBound c')
  end.

Fixpoint numVars (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => Nat.max (clauseBound c) (numVars phi')
  end.

Lemma clauseBound_cons (l : Lit) (c : Clause) :
  clauseBound (l :: c) = Nat.max (S (var l)) (clauseBound c).
Proof. reflexivity. Qed.

Lemma numVars_cons (c : Clause) (phi : CNF) :
  numVars (c :: phi) = Nat.max (clauseBound c) (numVars phi).
Proof. reflexivity. Qed.

Lemma lt_clauseBound (c : Clause) : forall l, In l c -> var l < clauseBound c.
Proof.
  induction c as [|l c IH]; intros l' Hl'; [contradiction|].
  change (clauseBound (l :: c)) with (Nat.max (S (var l)) (clauseBound c)).
  destruct Hl' as [H|H]; [subst; lia|]. specialize (IH l' H); lia.
Qed.

Lemma varsBelow_numVars (phi : CNF) : VarsBelow (numVars phi) phi.
Proof.
  induction phi as [|c phi IH]; intros c' Hc' l Hl; [contradiction|].
  change (numVars (c :: phi)) with (Nat.max (clauseBound c) (numVars phi)).
  destruct Hc' as [H|H].
  - subst; pose proof (lt_clauseBound c' l Hl); lia.
  - pose proof (IH c' H l Hl); lia.
Qed.

(** ** A lossless binary encoding of CNFs (same token scheme as the Lean file) *)

Fixpoint ticks (k : nat) : list bool :=
  match k with
  | 0 => []
  | S k' => true :: true :: ticks k'
  end.

Definition encodeLit (l : Lit) : list bool := ticks (var l) ++ [false; pos l].

Fixpoint encodeClause (c : Clause) : list bool :=
  match c with
  | [] => [true; false]
  | l :: c' => encodeLit l ++ encodeClause c'
  end.

Fixpoint encodeCNF (phi : CNF) : list bool :=
  match phi with
  | [] => []
  | c :: phi' => encodeClause c ++ encodeCNF phi'
  end.

Fixpoint decodeAux (w : list bool) (k : nat) (cur : Clause) : CNF :=
  match w with
  | true :: true :: rest => decodeAux rest (S k) cur
  | false :: p :: rest => decodeAux rest 0 (cur ++ [mkLit k p])
  | true :: false :: rest => cur :: decodeAux rest 0 []
  | _ => []
  end.

Definition decode (w : list bool) : CNF := decodeAux w 0 [].

Lemma decodeAux_ticks (v : nat) (r : list bool) (k : nat) (cur : Clause) :
  decodeAux (ticks v ++ r) k cur = decodeAux r (k + v) cur.
Proof.
  revert k; induction v as [|v IH]; intros k; simpl.
  - rewrite Nat.add_0_r; auto.
  - rewrite IH; f_equal; lia.
Qed.

Lemma decodeAux_clause (c : Clause) (r : list bool) (cur : Clause) :
  decodeAux (encodeClause c ++ r) 0 cur = (cur ++ c) :: decodeAux r 0 [].
Proof.
  revert cur; induction c as [|[v p] c IH]; intros cur; simpl.
  - rewrite app_nil_r; auto.
  - unfold encodeLit; simpl. rewrite <- !app_assoc, decodeAux_ticks. simpl.
    rewrite IH, <- app_assoc; auto.
Qed.

Theorem decode_encode (phi : CNF) : decode (encodeCNF phi) = phi.
Proof.
  unfold decode; induction phi as [|c phi IH]; simpl; auto.
  rewrite decodeAux_clause, IH; auto.
Qed.

Theorem encode_injective (phi psi : CNF) : encodeCNF phi = encodeCNF psi -> phi = psi.
Proof.
  intros H; rewrite <- (decode_encode phi), H; apply decode_encode.
Qed.

Lemma length_ticks (v : nat) : length (ticks v) = 2 * v.
Proof. induction v as [|v IH]; simpl; auto. rewrite IH; lia. Qed.

Lemma clauseBound_le_length (c : Clause) : clauseBound c <= length (encodeClause c).
Proof.
  induction c as [|l c IH]; [simpl; auto|].
  rewrite clauseBound_cons; simpl encodeClause.
  unfold encodeLit; rewrite !length_app, length_ticks; simpl length; lia.
Qed.

Theorem numVars_le_encodingLength (phi : CNF) : numVars phi <= length (encodeCNF phi).
Proof.
  induction phi as [|c phi IH]; auto.
  rewrite numVars_cons; simpl encodeCNF.
  rewrite length_app; pose proof (clauseBound_le_length c); lia.
Qed.


(** ** Size *)

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | c :: phi' => length c + size phi'
  end.

Lemma two_size_le_encodeClause (c : Clause) : 2 * length c <= length (encodeClause c).
Proof.
  induction c as [|l c IH]; [simpl; lia|].
  simpl encodeClause. unfold encodeLit. rewrite !length_app, length_ticks.
  simpl length. lia.
Qed.

Theorem size_le_encodingLength (phi : CNF) : 2 * size phi <= length (encodeCNF phi).
Proof.
  induction phi as [|c phi IH]; [simpl; lia|].
  simpl size; simpl encodeCNF. rewrite length_app.
  pose proof (two_size_le_encodeClause c); lia.
Qed.

(** ** The verifier *)

Definition verify (phi : CNF) (cert : list bool) : bool := evalCNF (toAssign cert) phi.

Theorem verify_sound (phi : CNF) (cert : list bool) :
  verify phi cert = true -> Satisfiable phi.
Proof. intros H; exists (toAssign cert); exact H. Qed.

Theorem verify_complete (n : nat) (phi : CNF) :
  VarsBelow n phi -> Satisfiable phi -> exists cert, length cert = n /\ verify phi cert = true.
Proof.
  intros Hphi [a Ha]. exists (prefixOf a n); split; [apply length_prefixOf|].
  unfold verify.
  rewrite (evalCNF_congr (toAssign (prefixOf a n)) a n phi); auto.
  intros i Hi; apply toAssign_prefixOf; auto.
Qed.

Theorem sat_iff_exists_cert (phi : CNF) :
  Satisfiable phi <-> exists cert, length cert = numVars phi /\ verify phi cert = true.
Proof.
  split.
  - apply verify_complete, varsBelow_numVars.
  - intros [cert [_ H]]; exact (verify_sound phi cert H).
Qed.

Theorem cert_length_le_encoding (phi : CNF) (cert : list bool) :
  length cert = numVars phi -> length cert <= length (encodeCNF phi).
Proof. intros H; rewrite H; apply numVars_le_encodingLength. Qed.

(** ** Cost of verification, counted in literal evaluations *)

Fixpoint clauseRun (a : Assignment) (c : Clause) : bool * nat :=
  match c with
  | [] => (false, 0)
  | l :: c' => (evalLit a l || fst (clauseRun a c'), S (snd (clauseRun a c')))
  end.

Fixpoint cnfRun (a : Assignment) (phi : CNF) : bool * nat :=
  match phi with
  | [] => (true, 0)
  | c :: phi' => (fst (clauseRun a c) && fst (cnfRun a phi'),
                  snd (clauseRun a c) + snd (cnfRun a phi'))
  end.

Definition verifyRun (phi : CNF) (cert : list bool) : bool * nat :=
  cnfRun (toAssign cert) phi.

Lemma clauseRun_fst (a : Assignment) (c : Clause) : fst (clauseRun a c) = evalClause a c.
Proof. induction c as [|l c IH]; simpl; auto. rewrite IH; auto. Qed.

Lemma clauseRun_snd (a : Assignment) (c : Clause) : snd (clauseRun a c) = length c.
Proof. induction c as [|l c IH]; simpl; auto. Qed.

Lemma cnfRun_fst (a : Assignment) (phi : CNF) : fst (cnfRun a phi) = evalCNF a phi.
Proof. induction phi as [|c phi IH]; simpl; auto. rewrite IH, clauseRun_fst; auto. Qed.

Lemma cnfRun_snd (a : Assignment) (phi : CNF) : snd (cnfRun a phi) = size phi.
Proof. induction phi as [|c phi IH]; simpl; auto. rewrite IH, clauseRun_snd; auto. Qed.

Theorem verifyRun_result (phi : CNF) (cert : list bool) :
  fst (verifyRun phi cert) = verify phi cert.
Proof. apply cnfRun_fst. Qed.

Theorem verify_cost_eq (phi : CNF) (cert : list bool) : snd (verifyRun phi cert) = size phi.
Proof. apply cnfRun_snd. Qed.

Theorem verify_cost_le_encoding (phi : CNF) (cert : list bool) :
  2 * snd (verifyRun phi cert) <= length (encodeCNF phi).
Proof. rewrite verify_cost_eq; apply size_le_encodingLength. Qed.

Fixpoint clauseRunSC (a : Assignment) (c : Clause) : bool * nat :=
  match c with
  | [] => (false, 0)
  | l :: c' => if evalLit a l then (true, 1)
               else (fst (clauseRunSC a c'), S (snd (clauseRunSC a c')))
  end.

Fixpoint cnfRunSC (a : Assignment) (phi : CNF) : bool * nat :=
  match phi with
  | [] => (true, 0)
  | c :: phi' =>
      if fst (clauseRunSC a c)
      then (fst (cnfRunSC a phi'), snd (clauseRunSC a c) + snd (cnfRunSC a phi'))
      else (false, snd (clauseRunSC a c))
  end.

Definition verifyRunSC (phi : CNF) (cert : list bool) : bool * nat :=
  cnfRunSC (toAssign cert) phi.

Lemma clauseRunSC_fst (a : Assignment) (c : Clause) : fst (clauseRunSC a c) = evalClause a c.
Proof.
  induction c as [|l c IH]; simpl; auto.
  destruct (evalLit a l); simpl; auto.
Qed.

Lemma clauseRunSC_snd (a : Assignment) (c : Clause) : snd (clauseRunSC a c) <= length c.
Proof.
  induction c as [|l c IH]; simpl; auto.
  destruct (evalLit a l); simpl; lia.
Qed.

Lemma cnfRunSC_fst (a : Assignment) (phi : CNF) : fst (cnfRunSC a phi) = evalCNF a phi.
Proof.
  induction phi as [|c phi IH]; simpl; auto.
  rewrite <- (clauseRunSC_fst a c).
  destruct (fst (clauseRunSC a c)); simpl; auto.
Qed.

Lemma cnfRunSC_snd (a : Assignment) (phi : CNF) : snd (cnfRunSC a phi) <= size phi.
Proof.
  induction phi as [|c phi IH]; simpl; auto.
  pose proof (clauseRunSC_snd a c).
  destruct (fst (clauseRunSC a c)); simpl; lia.
Qed.

Theorem verifyRunSC_result (phi : CNF) (cert : list bool) :
  fst (verifyRunSC phi cert) = verify phi cert.
Proof. apply cnfRunSC_fst. Qed.

Theorem verifyRunSC_cost_le (phi : CNF) (cert : list bool) :
  snd (verifyRunSC phi cert) <= size phi.
Proof. apply cnfRunSC_snd. Qed.

(** ** Where the difficulty lies: the quantifier over certificates *)

Theorem unsat_iff_all_rejected (n : nat) (phi : CNF) :
  VarsBelow n phi ->
  (~ Satisfiable phi <-> forall cert, In cert (allAssignments n) -> verify phi cert = false).
Proof.
  intros Hphi; split.
  - intros H cert _. destruct (verify phi cert) eqn:Hv; auto.
    exfalso; apply H; exact (verify_sound phi cert Hv).
  - intros H Hs. destruct (verify_complete n phi Hphi Hs) as [cert [Hlen Hv]].
    rewrite (H cert (proj2 (mem_allAssignments_iff n cert) Hlen)) in Hv; discriminate.
Qed.

Fixpoint totalCost (phi : CNF) (L : list (list bool)) : nat :=
  match L with
  | [] => 0
  | v :: L' => snd (verifyRun phi v) + totalCost phi L'
  end.

Lemma totalCost_eq (phi : CNF) (L : list (list bool)) : totalCost phi L = length L * size phi.
Proof.
  induction L as [|v L IH]; simpl; auto.
  rewrite IH, verify_cost_eq; auto.
Qed.

Theorem total_verification_cost (n : nat) (phi : CNF) :
  totalCost phi (allAssignments n) = 2 ^ n * size phi.
Proof. rewrite totalCost_eq, length_allAssignments; auto. Qed.
