(* Issue #532, Idea 18: structural restrictions and easy subclasses of SAT.

   Rocq counterpart of lean/Idea18.lean.  General theorems: 1-valid / 0-valid
   CNFs are satisfied by the all-true / all-false assignment; unit CNFs are
   satisfiable iff they have no empty clause and no complementary unit pair
   (with a correct Boolean decider); no satisfiability-preserving map of any
   kind lands in a trivially satisfiable class; and a polynomial-size
   reduction into a decidable restricted class transfers correctness and a
   composed polynomial cost bound.  The size-only schema
   PolySizeReductionIntoFor is only defined.

   Machine model (Machines.v): ReducesInto L R asks for a Machine that
   computes the map within a polynomial (Computes), with every output decoding
   into R; SATInPOn R is a polynomial-time machine decider correct on the
   promise "decodes into R" (DecidesOn).  inP_of_reducesInto composes them into
   InP; pEqualsNP_of_unitReduction turns the open obligation UnitReduction
   (SAT reduces into unit CNF) into PEqualsNP, given the named known theorem
   UnitSATInP and SATHard.  The trivial classes are refuted again
   (reducesInto_positive_const, not_reducesInto_positive), and
   not_forall_reducesInto shows that no class makes the reduction statement
   hold for every language.

   Difference from Lean: the Lean viaMachine M m is noncomputable.  Here
   viaMachine M (m, p) is computable (it runs m for p(|x|) steps with the
   interpreter runOut and reads the output off the tape), viaMachine_eq holds
   pointwise, and exists_not_reducible diagonalises pointwise against
   (machine, polynomial) pairs, without function extensionality or excluded
   middle.  unit_size_reduction_exists (classical in Lean) is not in this
   file.  No axioms are used. *)

From Stdlib Require Import Bool Arith PeanoNat List Lia.
Import ListNotations.
From proofs.experiments.issue532.rocq Require Import Machines.

(* ---------- SAT core ---------- *)

Record Lit := mkLit { var : nat; pos : bool }.

Definition lit_eq_dec : forall l1 l2 : Lit, {l1 = l2} + {l1 <> l2}.
Proof. decide equality; [apply bool_dec | apply Nat.eq_dec]. Defined.

Definition Clause := list Lit.
Definition CNF := list Clause.
Definition Assignment := nat -> bool.

Definition clause_eq_dec : forall C1 C2 : Clause, {C1 = C2} + {C1 <> C2} :=
  list_eq_dec lit_eq_dec.

Definition evalLit (a : Assignment) (l : Lit) : bool :=
  if pos l then a (var l) else negb (a (var l)).

Fixpoint evalClause (a : Assignment) (C : Clause) : bool :=
  match C with
  | [] => false
  | l :: C' => evalLit a l || evalClause a C'
  end.

Fixpoint evalCNF (a : Assignment) (phi : CNF) : bool :=
  match phi with
  | [] => true
  | C :: phi' => evalClause a C && evalCNF a phi'
  end.

Definition Satisfiable (phi : CNF) : Prop := exists a, evalCNF a phi = true.

Lemma evalClause_true_iff : forall a C,
  evalClause a C = true <-> exists l, In l C /\ evalLit a l = true.
Proof.
  intros a C. induction C as [|l C IH]; simpl.
  - split; [discriminate | intros [l [[] _]]].
  - rewrite orb_true_iff, IH. split.
    + intros [H|[l' [Hin H]]]; [exists l | exists l']; auto.
    + intros [l' [[Heq|Hin] H]]; [subst; left | right; exists l']; auto.
Qed.

Lemma evalCNF_true_iff : forall a phi,
  evalCNF a phi = true <-> forall C, In C phi -> evalClause a C = true.
Proof.
  intros a phi. induction phi as [|C phi IH]; simpl.
  - split; [intros _ C Hin; destruct Hin | auto].
  - rewrite andb_true_iff, IH. split.
    + intros [H1 H2] C' [Heq|Hin]; [subst|]; auto.
    + intros H. split; auto.
Qed.

Fixpoint size (phi : CNF) : nat :=
  match phi with
  | [] => 0
  | C :: phi' => length C + 1 + size phi'
  end.

(* ---------- (a) 1-valid and 0-valid classes ---------- *)

Definition PositiveClauses (phi : CNF) : Prop :=
  forall C, In C phi -> exists l, In l C /\ pos l = true.

Definition NegativeClauses (phi : CNF) : Prop :=
  forall C, In C phi -> exists l, In l C /\ pos l = false.

Theorem allTrue_satisfies : forall phi,
  PositiveClauses phi -> evalCNF (fun _ => true) phi = true.
Proof.
  intros phi H. apply evalCNF_true_iff. intros C HC.
  destruct (H C HC) as [l [Hl Hp]]. apply evalClause_true_iff.
  exists l. split; auto. unfold evalLit. rewrite Hp. reflexivity.
Qed.

Theorem allFalse_satisfies : forall phi,
  NegativeClauses phi -> evalCNF (fun _ => false) phi = true.
Proof.
  intros phi H. apply evalCNF_true_iff. intros C HC.
  destruct (H C HC) as [l [Hl Hp]]. apply evalClause_true_iff.
  exists l. split; auto. unfold evalLit. rewrite Hp. reflexivity.
Qed.

Theorem positive_satisfiable : forall phi, PositiveClauses phi -> Satisfiable phi.
Proof. intros phi H. exists (fun _ => true). apply allTrue_satisfies; auto. Qed.

Theorem negative_satisfiable : forall phi, NegativeClauses phi -> Satisfiable phi.
Proof. intros phi H. exists (fun _ => false). apply allFalse_satisfies; auto. Qed.

(* ---------- (b) Unit CNFs ---------- *)

Definition IsUnitCNF (phi : CNF) : Prop := forall C, In C phi -> length C <= 1.

Definition UnitClash (phi : CNF) : Prop :=
  exists l1 l2, In [l1] phi /\ In [l2] phi /\ var l1 = var l2 /\ pos l1 <> pos l2.

Lemma clause_of_length_le_one : forall C : Clause,
  length C <= 1 -> C <> [] -> exists l, C = [l].
Proof.
  intros [|l [|l' C]] H Hne; simpl in *.
  - contradiction.
  - exists l. reflexivity.
  - lia.
Qed.

Theorem unitCNF_sat_iff : forall phi, IsUnitCNF phi ->
  (Satisfiable phi <-> (~ In [] phi /\ ~ UnitClash phi)).
Proof.
  intros phi Hu. split.
  - intros [a Ha]. rewrite evalCNF_true_iff in Ha. split.
    + intros Hin. specialize (Ha [] Hin). discriminate.
    + intros [l1 [l2 [H1 [H2 [Hv Hp]]]]].
      pose proof (Ha _ H1) as E1. pose proof (Ha _ H2) as E2.
      simpl in E1, E2. rewrite orb_false_r in E1, E2.
      unfold evalLit in E1, E2. rewrite Hv in E1.
      destruct (pos l1), (pos l2); try (apply Hp; reflexivity);
        destruct (a (var l2)); discriminate.
  - intros [Hne Hclash].
    exists (fun v => if in_dec clause_eq_dec [mkLit v true] phi then true else false).
    apply evalCNF_true_iff. intros C HC.
    assert (HCne : C <> []) by (intros E; subst; contradiction).
    destruct (clause_of_length_le_one C (Hu C HC) HCne) as [l E]. subst C.
    simpl. rewrite orb_false_r. unfold evalLit.
    destruct l as [v p]; simpl. destruct p.
    + destruct (in_dec clause_eq_dec [mkLit v true] phi) as [H|H]; auto.
    + destruct (in_dec clause_eq_dec [mkLit v true] phi) as [H|H]; auto.
      exfalso. apply Hclash. exists (mkLit v true), (mkLit v false).
      repeat split; auto. simpl. discriminate.
Qed.

Definition isEmptyClause (C : Clause) : bool :=
  match C with [] => true | _ => false end.

Definition unitDecide (phi : CNF) : bool :=
  negb (existsb isEmptyClause phi) &&
  forallb (fun C1 => forallb (fun C2 =>
    match C1, C2 with
    | [l1], [l2] => negb (Nat.eqb (var l1) (var l2) && negb (Bool.eqb (pos l1) (pos l2)))
    | _, _ => true
    end) phi) phi.

Lemma existsb_isEmpty : forall phi, existsb isEmptyClause phi = true <-> In [] phi.
Proof.
  intros phi. rewrite existsb_exists. split.
  - intros [C [HC HE]]. destruct C; [auto | discriminate].
  - intros H. exists []. auto.
Qed.

Theorem unitDecide_correct : forall phi, IsUnitCNF phi ->
  (unitDecide phi = true <-> Satisfiable phi).
Proof.
  intros phi Hu. rewrite (unitCNF_sat_iff phi Hu). unfold unitDecide.
  rewrite andb_true_iff, negb_true_iff. split.
  - intros [Hne Hall]. split.
    + intros Hin. apply existsb_isEmpty in Hin. congruence.
    + intros [l1 [l2 [H1 [H2 [Hv Hp]]]]].
      rewrite forallb_forall in Hall. specialize (Hall _ H1).
      rewrite forallb_forall in Hall. specialize (Hall _ H2).
      simpl in Hall. rewrite Hv, Nat.eqb_refl in Hall.
      destruct (pos l1), (pos l2); simpl in Hall; try discriminate; apply Hp; reflexivity.
  - intros [Hne Hclash]. split.
    + destruct (existsb isEmptyClause phi) eqn:E; auto.
      apply existsb_isEmpty in E. contradiction.
    + apply forallb_forall. intros C1 H1. apply forallb_forall. intros C2 H2.
      destruct C1 as [|l1 [|l1' C1]]; auto.
      destruct C2 as [|l2 [|l2' C2]]; auto.
      destruct (Nat.eqb (var l1) (var l2)) eqn:Ev; simpl; auto.
      apply Nat.eqb_eq in Ev.
      destruct (Bool.eqb (pos l1) (pos l2)) eqn:Ep; simpl; auto.
      exfalso. apply Hclash. exists l1, l2. repeat split; auto.
      intros Heq. rewrite Heq, eqb_reflx in Ep. discriminate.
Qed.

(* ---------- (c) Reductions into trivial classes ---------- *)

Theorem reduction_into_trivial_class : forall (A B : Type) (L : A -> Prop) (M : B -> Prop)
  (f : A -> B), (forall x, L x <-> M (f x)) -> (forall y, M y) -> forall x, L x.
Proof. intros A B L M f Hred Hc x. apply Hred. apply Hc. Qed.

Theorem no_reduction_of_nontrivial : forall (A B : Type) (L : A -> Prop) (M : B -> Prop),
  (exists x, ~ L x) -> (forall y, M y) -> ~ exists f : A -> B, forall x, L x <-> M (f x).
Proof.
  intros A B L M [x Hx] Hc [f Hf]. apply Hx.
  apply (reduction_into_trivial_class A B L M f Hf Hc).
Qed.

Theorem empty_clause_unsat : ~ Satisfiable [[]].
Proof. intros [a Ha]. discriminate. Qed.

Theorem no_sat_reduction_into_positive :
  ~ exists f : CNF -> CNF, (forall phi, PositiveClauses (f phi)) /\
                           (forall phi, Satisfiable phi <-> Satisfiable (f phi)).
Proof.
  intros [f [Hpos Hpres]]. apply empty_clause_unsat.
  apply Hpres. apply positive_satisfiable. apply Hpos.
Qed.

Theorem no_sat_reduction_into_negative :
  ~ exists f : CNF -> CNF, (forall phi, NegativeClauses (f phi)) /\
                           (forall phi, Satisfiable phi <-> Satisfiable (f phi)).
Proof.
  intros [f [Hneg Hpres]]. apply empty_clause_unsat.
  apply Hpres. apply negative_satisfiable. apply Hneg.
Qed.

(* ---------- The useful direction: hardness-preserving restriction ---------- *)

Definition polyEval (c k n : nat) : nat := c * (n + 1) ^ k.

(** Size-only schema for a restricted class R: SAT reduces into R by a
    satisfiability-preserving map with polynomial size blow-up.  The map is an
    arbitrary function, so this schema records no running time: for the
    1-valid and 0-valid classes it is false (no_sat_reduction_into_positive,
    no_sat_reduction_into_negative).  The machine version, with the map
    computed by a Machine, is ReducesInto below. *)
Definition PolySizeReductionIntoFor (R : CNF -> Prop) : Prop :=
  exists (f : CNF -> CNF) (c k : nat),
    (forall phi, R (f phi)) /\ (forall phi, Satisfiable phi <-> Satisfiable (f phi)) /\
    (forall phi, size (f phi) <= polyEval c k (size phi)).

Theorem poly_comp_bound : forall c k c' k' n,
  polyEval c' k' (polyEval c k n) <= polyEval (c' * (c + 1) ^ k') (k * k') n.
Proof.
  intros c k c' k' n. unfold polyEval.
  assert (H1 : 1 <= (n + 1) ^ k).
  { pose proof (Nat.pow_le_mono_l 1 (n + 1) k ltac:(lia)). rewrite Nat.pow_1_l in H. lia. }
  assert (H2 : c * (n + 1) ^ k + 1 <= (c + 1) * (n + 1) ^ k) by nia.
  pose proof (Nat.pow_le_mono_l _ _ k' H2) as H3.
  rewrite Nat.pow_mul_l, <- Nat.pow_mul_r in H3.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. exact H3.
Qed.

Theorem restriction_transfer : forall (R : CNF -> Prop),
  PolySizeReductionIntoFor R ->
  forall (d : CNF -> bool), (forall psi, R psi -> (d psi = true <-> Satisfiable psi)) ->
  forall (dcost : CNF -> nat) (c' k' : nat),
    (forall psi, dcost psi <= polyEval c' k' (size psi)) ->
    exists (f : CNF -> CNF) (C K : nat),
      (forall phi, d (f phi) = true <-> Satisfiable phi) /\
      (forall phi, dcost (f phi) <= polyEval C K (size phi)).
Proof.
  intros R [f [c [k [HfR [Hfsat Hfsize]]]]] d Hd dcost c' k' Hcost.
  exists f, (c' * (c + 1) ^ k'), (k * k'). split.
  - intros phi. rewrite (Hd _ (HfR phi)). symmetry. apply Hfsat.
  - intros phi. eapply Nat.le_trans; [apply Hcost|].
    eapply Nat.le_trans; [|apply poly_comp_bound].
    unfold polyEval. apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l.
    specialize (Hfsize phi). unfold polyEval in Hfsize. lia.
Qed.

(* ---------- The machine model: a polynomial-time reduction into a restricted class ---------- *)

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

(** A polynomial-time machine reduction of L into the class R: a Machine
    computes f within a polynomial, every output decodes to a CNF in R, and
    L x = SAT (f x). *)
Definition ReducesInto (L : Language) (R : CNF -> Prop) : Prop :=
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall x, R (ofM (decode (f x))) /\ L x = SAT (f x).

(** SAT restricted to R is decided by a polynomial-time machine that is
    correct on every word decoding to a CNF in R (a promise problem). *)
Definition SATInPOn (R : CNF -> Prop) : Prop :=
  exists (d : Machine) (p : Polynomial),
    DecidesOn d p (fun w => R (ofM (decode w))) SAT.

(** Transfer in the machine model.  A polynomial-time reduction into R
    followed by a polynomial-time decider correct on R puts L in P. *)
Theorem inP_of_reducesInto : forall (L : Language) (R : CNF -> Prop),
  ReducesInto L R -> SATInPOn R -> InP L.
Proof.
  intros L R [m [f [p [hm hf]]]] [d [p' hd]].
  exact (inP_of_promise_reduction L SAT (fun w => R (ofM (decode w))) m d f p p' hm
    (fun x => proj1 (hf x)) (fun x => proj2 (hf x)) hd).
Qed.

(** The machine-model version of the size schema's correctness half: a machine
    reduction into R is a satisfiability-preserving map of CNFs into R. *)
Theorem reducesInto_preserves : forall R : CNF -> Prop, ReducesInto SAT R ->
  exists (m : Machine) (f : Word -> Word) (p : Polynomial), Computes m f p /\
    forall phi : Machines.CNF, R (ofM (decode (f (encodeCNF phi)))) /\
      (Satisfiable (ofM phi) <-> Satisfiable (ofM (decode (f (encodeCNF phi))))).
Proof.
  intros R [m [f [p [hm hf]]]].
  exists m, f, p. split; [exact hm |]. intro phi.
  split; [exact (proj1 (hf _)) |].
  pose proof (proj2 (hf (encodeCNF phi))) as e.
  rewrite <- sat_ofM, <- e, sat_ofM, decode_encode. reflexivity.
Qed.

(** Known theorem, not mechanised here.  Satisfiability of unit CNFs (every
    clause has at most one literal) is decided in polynomial time: check for
    an empty clause and for a complementary pair of unit clauses (a quadratic
    scan; its correctness is unitCNF_sat_iff / unitDecide_correct above, and
    it is a special case of Horn-SAT, Dowling-Gallier 1984, and of 2-SAT,
    Aspvall-Plass-Tarjan 1979).  What is not mechanised is a Machine
    implementing the scan on encoded formulas.  Used only as an explicit
    premise. *)
Definition UnitSATInP : Prop := SATInPOn IsUnitCNF.

(** Open obligation.  SAT reduces into unit CNF by a polynomial-time machine:
    a Machine computes, within a polynomial number of Run steps, a map f such
    that every f x decodes to a unit CNF and SAT x = SAT (f x). *)
Definition UnitReduction : Prop := ReducesInto SAT IsUnitCNF.

(** Conditional theorem.  The open obligation and the known unit-CNF decider
    put SAT in P. *)
Theorem inP_sat_of_unitReduction : UnitSATInP -> UnitReduction -> InP SAT.
Proof. intros hU h. exact (inP_of_reducesInto SAT IsUnitCNF h hU). Qed.

(** Conditional theorem.  With the hardness half of Cook-Levin, the open
    obligation gives P = NP. *)
Theorem pEqualsNP_of_unitReduction : SATHard -> UnitSATInP -> UnitReduction -> PEqualsNP.
Proof.
  intros hard hU h. exact (pEqualsNP_of_inP_sat hard (inP_sat_of_unitReduction hU h)).
Qed.

(** The same route for any class R with a polynomial-time promise decider. *)
Theorem pEqualsNP_of_reducesInto : SATHard -> forall R : CNF -> Prop,
  SATInPOn R -> ReducesInto SAT R -> PEqualsNP.
Proof.
  intros hard R hR h. exact (pEqualsNP_of_inP_sat hard (inP_of_reducesInto SAT R h hR)).
Qed.

(** A machine reduction into the 1-valid class forces a constant answer. *)
Theorem reducesInto_positive_const : forall L : Language,
  ReducesInto L PositiveClauses -> forall x, L x = true.
Proof.
  intros L [m [f [p [_ hf]]]] x.
  rewrite (proj2 (hf x)).
  apply sat_ofM. apply positive_satisfiable. exact (proj1 (hf x)).
Qed.

Theorem machine_empty_clause_unsat : SAT (encodeCNF [[]]) = false.
Proof.
  destruct (SAT (encodeCNF [[]])) eqn:h; [| reflexivity].
  apply sat_encode in h. destruct h as [a ha]. discriminate ha.
Qed.

(** Refutation in the machine model.  SAT has no polynomial-time (indeed no)
    machine reduction into the 1-valid class. *)
Theorem not_reducesInto_positive : ~ ReducesInto SAT PositiveClauses.
Proof.
  intro h.
  pose proof (reducesInto_positive_const SAT h (encodeCNF [[]])) as e.
  rewrite machine_empty_clause_unsat in e. discriminate e.
Qed.

(* ---------- Reading a machine's output (computable) ---------- *)

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

(** Non-vacuity.  For every class [R], some language has no polynomial-time
    machine reduction into [R]; so [ReducesInto SAT R] is a statement about
    SAT and not a consequence of the definitions. *)
Theorem not_forall_reducesInto : forall R : CNF -> Prop,
  ~ (forall L : Language, ReducesInto L R).
Proof.
  intros R h.
  destruct (exists_not_reducible SAT) as [L hL].
  destruct (h L) as [m [f [p [hm hf]]]].
  destruct (hL m f p hm) as [x hx].
  exact (hx (proj2 (hf x))).
Qed.
