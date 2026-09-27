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

   Machine model (Machines.v): SmallComponents k w says that the CNF encoded
   by w is a disjoint union of components with at most k * log2 (|w|+1)
   variable occurrences each.  The named known theorem SmallComponentSATInP
   (componentwise brute force is polynomial on that promise) is used only as
   an explicit premise.  The open obligation SATComponentReduction asks for a
   Machine that maps every SAT instance, within a polynomial number of steps,
   to an equisatisfiable instance with small components;
   inP_sat_of_componentReduction and pEqualsNP_of_componentReduction derive
   InP SAT and PEqualsNP from it, and not_forall_componentReduction shows that
   the reduction notion is not satisfied by every language.

   Difference from Lean: the Lean viaMachine M m is noncomputable.  Here
   viaMachine M (m, p) is computable (it runs m for p(|x|) steps with the
   interpreter runOut and reads the output off the tape), viaMachine_eq holds
   pointwise, and exists_not_reducible diagonalises pointwise against
   (machine, polynomial) pairs, without function extensionality or excluded
   middle.  No axioms are used.
   See ../ideas/Idea25.md. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

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

(** Schema for (FS) over a caller-supplied class PolyTime of maps and a width
    bound w: a map in PolyTime sending every CNF to pairwise variable-disjoint
    components whose union is equisatisfiable, each component having at most
    w |phi| variable occurrences.  PolyTime is a free parameter, so the schema
    is not itself a statement about running time; the machine version is
    SATComponentReduction below. *)
Definition ComponentObligationFor (PolyTime : (CNF -> list CNF) -> Prop) (w : nat -> nat) : Prop :=
  exists f : CNF -> list CNF, PolyTime f /\ forall phi, DisjointChain (f phi) /\
    (forall psi, In psi (f phi) -> length (vars psi) <= w (length phi)) /\
    (Satisfiable phi <-> Satisfiable (joinAll (f phi))).

(* Conditional theorem: under the schema, satisfiability of every CNF is the
   conjunction of the satisfiability of its small components. *)
Theorem component_obligation_splits (PolyTime : (CNF -> list CNF) -> Prop) (w : nat -> nat) :
  ComponentObligationFor PolyTime w ->
  exists f : CNF -> list CNF, PolyTime f /\ forall phi,
    (forall psi, In psi (f phi) -> length (vars psi) <= w (length phi)) /\
    (Satisfiable phi <-> forall psi, In psi (f phi) -> Satisfiable psi).
Proof.
  intros (f & hf & hall). exists f. split; [exact hf|]. intro phi.
  destruct (hall phi) as (hd & hw & hp). split; [exact hw|].
  rewrite hp. apply joinAll_sat_iff. exact hd.
Qed.

(** ** The machine model *)

(** A CNF of the shared machine model, read in this file's syntax. *)
Definition ofM (phi : Machines.CNF) : CNF :=
  map (map (fun l => mkLit (Machines.var l) (Machines.pos l))) phi.

Theorem evalClause_ofM : forall (a : Assignment) (C : Machines.Clause),
  evalClause a (map (fun l => mkLit (Machines.var l) (Machines.pos l)) C) =
  Machines.evalClause a C.
Proof.
  intros a C. induction C as [| l C IH]; simpl; [reflexivity |].
  rewrite IH. unfold evalLit, Machines.evalLit. simpl.
  destruct (Machines.pos l), (a (Machines.var l)); reflexivity.
Qed.

Theorem evalCNF_ofM : forall (a : Assignment) (phi : Machines.CNF),
  evalCNF a (ofM phi) = Machines.evalCNF a phi.
Proof.
  intros a phi. unfold ofM. induction phi as [| C phi IH]; simpl; [reflexivity |].
  rewrite evalClause_ofM, IH. reflexivity.
Qed.

(** The machine-model language SAT is satisfiability in this file's syntax. *)
Theorem sat_ofM : forall w : Word, SAT w = true <-> Satisfiable (ofM (decode w)).
Proof.
  intro w. rewrite sat_iff. split; intros [a ha]; exists a.
  - rewrite evalCNF_ofM. exact ha.
  - rewrite <- evalCNF_ofM. exact ha.
Qed.

(** The word [w] encodes a CNF that is a disjoint union of components with at
    most [k * log2 (|w|+1)] variable occurrences each. *)
Definition SmallComponents (k : nat) (w : Word) : Prop :=
  exists phis : list CNF, ofM (decode w) = joinAll phis /\ DisjointChain phis /\
    forall psi, In psi phis -> length (vars psi) <= k * Nat.log2 (length w + 1).

(** On the promise [SmallComponents k], SAT is the conjunction of the
    satisfiability of the small components (the exact splitting lemma). *)
Theorem sat_of_smallComponents : forall k w, SmallComponents k w ->
  exists phis : list CNF,
    (forall psi, In psi phis -> length (vars psi) <= k * Nat.log2 (length w + 1)) /\
    (SAT w = true <-> forall psi, In psi phis -> Satisfiable psi).
Proof.
  intros k w [phis [he [hd hs]]]. exists phis. split; [exact hs |].
  rewrite sat_ofM, he. apply joinAll_sat_iff. exact hd.
Qed.

(** Known theorem, not mechanised here.  For each fixed k, SAT is decided in
    polynomial time on the promise SmallComponents k.  Algorithm: compute the
    connected components of the primal graph (graph search, e.g.
    Hopcroft-Tarjan, CACM 16(6), 1973); each of them lies inside one of the
    promised components, so it has at most k * log2 (|w|+1) distinct
    variables, and brute force over its assignments costs at most (|w|+1)^k
    evaluations; by joinAll_sat_iff the answer is the conjunction.  This is
    the folklore base case of treewidth dynamic programming (Samer-Szeider,
    J. Discrete Algorithms 8(1), 2010).  What is not mechanised is the Machine
    carrying it out.  Used only as an explicit premise. *)
Definition SmallComponentSATInP : Prop :=
  forall k, exists (d : Machine) (p : Polynomial), DecidesOn d p (SmallComponents k) SAT.

(** A polynomial-time machine reduction of [L] to SAT instances with small
    components. *)
Definition ComponentReduction (L : Language) (k : nat) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, SmallComponents k (f x) /\ L x = SAT (f x).

(** Open obligation (FS in the machine model).  For some k, a Machine maps
    every word x, within a polynomial number of Run steps, to a word f x with
    SAT x = SAT (f x) whose CNF splits into variable-disjoint components of at
    most k * log2 (|f x|+1) variable occurrences. *)
Definition SATComponentReduction : Prop := exists k, ComponentReduction SAT k.

(** Transfer: a component reduction and the componentwise decider put [L] in
    P. *)
Theorem inP_of_componentReduction : forall (L : Language) (k : nat),
  SmallComponentSATInP -> ComponentReduction L k -> InP L.
Proof.
  intros L k hK [m [f [p [hm hf]]]].
  destruct (hK k) as [d [p' hd]].
  exact (inP_of_promise_reduction L SAT (SmallComponents k) m d f p p' hm
    (fun x => proj1 (hf x)) (fun x => proj2 (hf x)) hd).
Qed.

(** Conditional theorem.  The open obligation and the known componentwise
    decider put SAT in P. *)
Theorem inP_sat_of_componentReduction :
  SmallComponentSATInP -> SATComponentReduction -> InP SAT.
Proof.
  intros hK [k hk]. exact (inP_of_componentReduction SAT k hK hk).
Qed.

(** Conditional theorem.  With the hardness half of Cook-Levin, the open
    obligation gives P = NP. *)
Theorem pEqualsNP_of_componentReduction :
  SATHard -> SmallComponentSATInP -> SATComponentReduction -> PEqualsNP.
Proof.
  intros hard hK h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_componentReduction hK h)).
Qed.

(** Machine analogue of component_obligation_splits: under the obligation,
    SAT x holds iff every small component of the reduced instance is
    satisfiable. *)
Theorem componentReduction_splits : SATComponentReduction ->
  exists (k : nat) (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, exists phis : list CNF,
      (forall psi, In psi phis -> length (vars psi) <= k * Nat.log2 (length (f x) + 1)) /\
      (SAT x = true <-> forall psi, In psi phis -> Satisfiable psi).
Proof.
  intros [k [m [f [p [hm hf]]]]].
  exists k, m, f, p. split; [exact hm |]. intro x.
  destruct (sat_of_smallComponents k (f x) (proj1 (hf x))) as [phis [hs hsat]].
  exists phis. split; [exact hs |]. rewrite (proj2 (hf x)). exact hsat.
Qed.

(** ** Reading a machine's output (computable) *)

(** Run [m] from [c] for at most [fuel] steps until it reaches the exit state
    [length (program m)]; return that configuration. *)
Fixpoint runOut (m : Machine) (c : Config) (fuel : nat) : option Config :=
  if Nat.eqb (state c) (length (program m)) then Some c else
  match fuel with
  | 0 => None
  | S f => match step m c with
           | inl _ => None
           | inr c' => runOut m c' f
           end
  end.

Lemma runOut_of_reaches : forall m c t d, Reaches m c t d ->
  state d = length (program m) -> forall fuel, t <= fuel -> runOut m c fuel = Some d.
Proof.
  intros m c t d h. induction h as [c | c c' d t hs hr IH]; intros hd fuel hf.
  - destruct fuel; simpl; rewrite hd, Nat.eqb_refl; reflexivity.
  - pose proof (state_lt_of_step _ _ _ hs) as hlt.
    destruct fuel as [| fuel]; [lia |]. simpl.
    destruct (Nat.eqb_spec (state c) (length (program m))) as [e | _]; [lia |].
    rewrite hs. apply IH; [exact hd | lia].
Qed.

(** The bits at the head and to its right, up to the first non-bit symbol. *)
Fixpoint readBits (l : list Symbol) : Word :=
  match l with
  | one :: r => true :: readBits r
  | zero :: r => false :: readBits r
  | _ => []
  end.

Lemma readBits_output : forall w k, readBits (map ofBool w ++ blanks k) = w.
Proof.
  intros w k. induction w as [| b w IH]; simpl.
  - destruct k; reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

(** The language obtained by running the machine [m] for [p(|x|)] steps as a
    reduction into [M] (computable). *)
Definition viaMachine (M : Language) (x : Machine * Polynomial) : Language := fun w =>
  match runOut (fst x) (initial w) (evalPoly (snd x) (length w)) with
  | Some c => M (readBits (tapeHead c :: tapeRight c))
  | None => false
  end.

Theorem viaMachine_eq : forall (M : Language) m f p, Computes m f p ->
  forall x, viaMachine M (m, p) x = M (f x).
Proof.
  intros M m f p hm x. destruct (hm x) as [t [c [ht [hr [hs [_ [k hk]]]]]]].
  unfold viaMachine. cbn [fst snd].
  rewrite (runOut_of_reaches _ _ _ _ hr hs _ ht), hk, readBits_output.
  reflexivity.
Qed.

(** Cantor over machines.  For every target language [M] some language has no
    machine map [f] with [L x = M (f x)] (pointwise diagonal over
    machine-polynomial pairs). *)
Theorem exists_not_reducible : forall M : Language,
  exists L : Language, forall m f p, Computes m f p -> exists x, L x <> M (f x).
Proof.
  intro M.
  exists (fun w => match decMachinePoly w with
                   | Some a => negb (viaMachine M a w)
                   | None => true
                   end).
  intros m f p hm. exists (encMachinePoly (m, p)).
  rewrite decMachinePoly_encMachinePoly, (viaMachine_eq M m f p hm).
  destruct (M (f (encMachinePoly (m, p)))); discriminate.
Qed.


(** Non-vacuity.  For every k, some language has no component reduction, so
    [ComponentReduction SAT k] is a statement about SAT. *)
Theorem not_forall_componentReduction : forall k : nat,
  ~ (forall L : Language, ComponentReduction L k).
Proof.
  intros k h.
  destruct (exists_not_reducible SAT) as [L hL].
  destruct (h L) as [m [f [p [hm hf]]]].
  destruct (hL m f p hm) as [x hx].
  exact (hx (proj2 (hf x))).
Qed.
